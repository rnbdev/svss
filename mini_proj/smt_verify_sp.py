#!/usr/bin/python3

import pycparser as pycp
import z3
import sys

t_qe = z3.Tactic('qe')
t = z3.Repeat(z3.Then("simplify", "propagate-ineqs",
                      "propagate-values", "unit-subsume-simplify",
                      z3.OrElse("split-clause", "skip")))
t_qe_ = z3.Then(t_qe, t)


def gen_smt_expr(ast):
    if isinstance(ast, pycp.c_ast.Constant):
        return z3.IntVal(ast.value)
    elif isinstance(ast, pycp.c_ast.ID):
        return vars[ast.name]
    elif isinstance(ast, pycp.c_ast.UnaryOp):
        if ast.op == "-":
            return "-" + gen_smt_expr(ast.expr)
        if ast.op == "!":
            return z3.Not(gen_smt_expr(ast.expr))
    elif isinstance(ast, pycp.c_ast.BinaryOp):
        lexp = gen_smt_expr(ast.left)
        rexp = gen_smt_expr(ast.right)
        if ast.op == "+":
            return lexp + rexp
        if ast.op == "-":
            return lexp - rexp
        elif ast.op == "*":
            return lexp * rexp
        elif ast.op == "%":
            return lexp % rexp
        elif ast.op == "<":
            return lexp < rexp
        elif ast.op == ">":
            return lexp > rexp
        elif ast.op == "<=":
            return lexp <= rexp
        elif ast.op == ">=":
            return lexp >= rexp
        elif ast.op == "==":
            return lexp == rexp
        if ast.op == "&&":
            return z3.And(lexp, rexp)
        if ast.op == "||":
            return z3.Or(lexp, rexp)
        elif ast.op == "!=":
            return lexp != rexp


def walk_block(node, prev_g=None, cond=True):
    g = z3.Goal()
    g.add(cond)
    if prev_g is not None:
        for e in prev_g:
            if isinstance(e, z3.Goal):
                g.add(e.as_expr())
            else:
                g.add(e)

    if isinstance(node, pycp.c_ast.Compound):
        if node.block_items is not None:
            for e in node.block_items:
                g_next = walk_block(e, g)
                g = g_next
    elif isinstance(node, pycp.c_ast.Decl):
        if "int" in node.type.type.names:
            vars[node.name] = z3.Int(node.name)
        if "float" in node.type.type.names:
            vars[node.name] = z3.Real(node.name)
    elif isinstance(node, pycp.c_ast.FuncCall):
        if node.name.name == "__ASSUME":
            for e_exp in node.args.exprs:
                g.add(gen_smt_expr(e_exp))
        elif node.name.name == "__ASSERT":
            assertions = z3.Goal()
            for e_exp in node.args.exprs:
                assertions.add(gen_smt_expr(e_exp))
            print("solving..")
            print("SP:", g.as_expr())
            print("assert:", assertions)

            seen = set()

            def bv_length(e):
                li = [-1]
                if e in seen:
                    return -1
                if (z3.is_bv(e) and
                        z3.is_const(e) and
                        e.decl().kind() == z3.Z3_OP_UNINTERPRETED):
                    li.append(e.size())
                seen.add(e)
                if z3.is_app(e):
                    for ch in e.children():
                        li.append(bv_length(ch))
                elif z3.is_quantifier(e):
                    for ch in e.body().children():
                        li.append(bv_length(ch))
                return max(li)

            t = z3.Tactic('nla2bv')
            s = z3.Then(t, 'default').solver()
            fml = z3.And(g.as_expr(), z3.Not(assertions.as_expr()))
            print("solving using bitvector underapproximation..")
            s.add(fml)
            status = s.check()

            if status == z3.unknown:
                print("returned 'unknown'! trying again with bigger bit length..")
                print("getting highest bit length used in formula..")
                bv_l = bv_length(t(fml).as_expr())
                print("highest bit length used:", bv_l)

                while True:
                    bv_l += 1
                    print("trying with bit length:", bv_l)
                    s = z3.Then(z3.With('nla2bv', nla2bv_bv_size=bv_l),
                                'default').solver()
                    s.add(fml)
                    status = s.check()

                    if status != z3.unknown or bv_l >= 64:
                        break

            if status == z3.sat:
                model = s.model()
                print("program is unsafe.\nlisting an unsafe assignments..")
                for e in vars:
                    print(e, ':', model[vars[e]])
            elif status == z3.unsat:
                print("program is safe.")
            elif status == z3.unknown:
                print("unknown")

            s.reset()
        else:
            print("found a func call")
    elif isinstance(node, pycp.c_ast.Assignment):
        rexp = gen_smt_expr(node.rvalue)
        if z3.is_int(vars[node.lvalue.name]):
            hand_ = z3.Int('__hand__')
        elif z3.is_real(vars[node.lvalue.name]):
            hand_ = z3.Real('__hand__')
        if node.op == "=":
            g.add(hand_ == rexp)
        elif node.op == "+=":
            g.add(hand_ == (vars[node.lvalue.name] + rexp))
        elif node.op == "-=":
            g.add(hand_ == (vars[node.lvalue.name] - rexp))
        elif node.op == "*=":
            g.add(hand_ == (vars[node.lvalue.name] * rexp))
        elif node.op == "%=":
            g.add(hand_ == (vars[node.lvalue.name] % rexp))
        g_ = z3.Goal()
        g_.add(z3.Exists(vars[node.lvalue.name], g.as_expr()))
        g_ = t_qe_(g_)
        g = z3.Goal()
        g.add(z3.substitute(g_.as_expr(), (hand_, vars[node.lvalue.name])))
        # g = g.simplify()
    elif isinstance(node, pycp.c_ast.If):
        cond_exp = gen_smt_expr(node.cond)
        if node.iftrue is not None:
            true_expr = walk_block(node.iftrue, g, cond_exp).as_expr()
        else:
            true_expr = z3.And(cond_exp, g.as_expr())
        if node.iffalse is not None:
            false_expr = walk_block(
                node.iffalse, g, z3.Not(cond_exp)).as_expr()
        else:
            false_expr = z3.And(z3.Not(cond_exp), g.as_expr())
        g = z3.Goal()
        g.add(z3.Or(true_expr, false_expr))
        g = t(g)  # g.simplify()
    else:
        return prev_g
    # print(g.as_expr(), "\n")
    return g


if __name__ == "__main__":
    c_fname = sys.argv[1]

    ast = pycp.parse_file(c_fname, use_cpp=True,
                          cpp_path='gcc',
                          cpp_args=['-E', r'-Iutils/fake_libc_include'])

    # ast.show()

    vars = {}

    main_func = None

    for e in ast.ext:
        if isinstance(e, pycp.c_ast.FuncDef) and e.decl.name == "main":
            main_func = e
            break

    if main_func is None:
        raise("no main function")

    s = z3.Solver()

    g = walk_block(main_func.body)

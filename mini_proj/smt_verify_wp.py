#!/usr/bin/python3

import pycparser as pycp
import z3
import sys

t_qe = z3.Tactic('qe')
t = z3.Repeat(z3.Then("simplify", "propagate-ineqs", "propagate-values",
                      "unit-subsume-simplify"))
t_qe_ = z3.Then(t_qe, t)


def gen_smt_expr(ast):
    if isinstance(ast, pycp.c_ast.Constant):
        return z3.BitVecVal(ast.value, 32)
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


def walk_block(node, prev_g=None):
    g = z3.Goal()
    if prev_g is not None:
        for e in prev_g:
            if isinstance(e, z3.Goal):
                g.add(e.as_expr())
            else:
                g.add(e)

    if isinstance(node, pycp.c_ast.Compound):
        if node.block_items is not None:
            for e in node.block_items:
                if isinstance(e, pycp.c_ast.Decl):
                    if "int" in e.type.type.names:
                        vars[e.name] = z3.BitVec(e.name, 32)
            for e in reversed(node.block_items):
                g_next = walk_block(e, g)
                g = g_next
    elif isinstance(node, pycp.c_ast.FuncCall):
        if node.name.name == "__ASSERT":
            li = []
            for e_exp in node.args.exprs:
                li.append(gen_smt_expr(e_exp))
            g.add(z3.Not(z3.And(li)))
        elif node.name.name == "__ASSUME":
            assumptions = z3.Goal()
            for e_exp in node.args.exprs:
                assumptions.add(gen_smt_expr(e_exp))
            print("solving..")
            print("WP:", g.as_expr())
            print("assume:", assumptions)
            s.add(assumptions.as_expr())
            s.add(g.as_expr())
            status = s.check()
            print(s)

            if status == z3.sat:
                model = s.model()
                print("program is unsafe.\nlisting an unsafe assignments..")
                for e in vars:
                    print(e, ':', model[vars[e]].as_signed_long())
            elif status == z3.unsat:
                print("program is safe.")
            elif status == z3.unknown:
                print("unknown")

            s.reset()
        else:
            print("found a func call")
    elif isinstance(node, pycp.c_ast.Assignment):
        rexp = gen_smt_expr(node.rvalue)
        g_ = z3.Goal()
        if node.op == "=":
            g_.add(z3.substitute(g.as_expr(), (vars[node.lvalue.name], rexp)))
        elif node.op == "+=":
            g_.add(z3.substitute(g.as_expr(),
                                 (vars[node.lvalue.name],
                                  vars[node.lvalue.name] + rexp)))
        elif node.op == "-=":
            g_.add(z3.substitute(g.as_expr(),
                                 (vars[node.lvalue.name],
                                  vars[node.lvalue.name] - rexp)))
        elif node.op == "*=":
            g_.add(z3.substitute(g.as_expr(),
                                 (vars[node.lvalue.name],
                                  vars[node.lvalue.name] * rexp)))
        elif node.op == "%=":
            g_.add(z3.substitute(g.as_expr(),
                                 (vars[node.lvalue.name],
                                  vars[node.lvalue.name] % rexp)))
        g = t(g_)
        # g = g.simplify()
    elif isinstance(node, pycp.c_ast.If):
        cond_exp = gen_smt_expr(node.cond)
        true_expr, false_expr = None, None
        if node.iftrue is not None:
            true_ = walk_block(node.iftrue, g)
            true_expr = true_.as_expr()
        else:
            true_expr = g.as_expr()
        if node.iffalse is not None:
            false_ = walk_block(node.iffalse, g)
            false_expr = false_.as_expr()
        else:
            false_expr = g.as_expr()
        true_expr = z3.And(cond_exp, true_expr)
        false_expr = z3.And(z3.Not(cond_exp), false_expr)
        g = z3.Goal()
        g.add(z3.Or(true_expr, false_expr))
        g = t(g)  # g.simplify()
    else:
        g = prev_g
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

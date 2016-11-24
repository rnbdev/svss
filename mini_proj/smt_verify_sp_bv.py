#!/usr/bin/python3

import pycparser as pycp
import z3
import sys
import random

t = z3.Repeat(z3.Then("propagate-values", "propagate-ineqs",
                      "unit-subsume-simplify", "propagate-bv-bounds",
                      "simplify"))
t_qe_ = z3.OrElse(z3.Then(z3.TryFor('qe', 1000),
                          z3.TryFor('qe2', 1000)), 'skip')


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
            ts[node.name] = 0
            vars[node.name] = z3.BitVec("%s!!%d" % (node.name, ts[node.name]),
                                        32)
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

            fml = z3.And(g.as_expr(), z3.Not(assertions.as_expr()))

            s = z3.SolverFor('bv')
            s.add(fml)

            under_approx_info = {}
            for e in vars:
                under_approx_info[e] = [1, z3.Bool('%s!!switch' % e)]

            while(1):
                s.push()
                switches = []
                for e in vars:
                    if under_approx_info[e][0] <= 30:
                        s.add(z3.Implies(under_approx_info[e][1],
                                         z3.Extract(30,
                                                    under_approx_info[e][0],
                                                    vars[e]) == 0))
                        switches.append(under_approx_info[e][1])

                if len(switches) == 0:
                    status = s.check()
                    break

                # print(s)
                status = s.check(switches)
                s.pop()
                if status == z3.unsat:
                    u_core = s.unsat_core()
                    # print(u_core)
                    if len(u_core) == 0:
                        break
                    e_bool = random.choice(u_core)
                    var_st = str(e_bool).split('!!')[0]
                    # print(var_st)
                    under_approx_info[var_st][0] += 1
                elif status == z3.sat:
                    break
                else:
                    break

            if status == z3.sat:
                # print(s)
                model = s.model()
                print("program is unsafe.\nlisting an unsafe assignments..")
                for e in vars:
                    print(e, ':', model[vars[e]].as_signed_long())
            elif status == z3.unsat:
                print("program is safe.")
            elif status == z3.unknown:
                print("unknown")
        else:
            print("found a func call")
    elif isinstance(node, pycp.c_ast.Assignment):
        rexp = gen_smt_expr(node.rvalue)
        ts[node.lvalue.name] += 1
        old_ = vars[node.lvalue.name]
        if z3.is_bv(vars[node.lvalue.name]):
            curr_ = z3.BitVec('%s!!%d' %
                              (node.lvalue.name, ts[node.lvalue.name]), 32)
        vars[node.lvalue.name] = curr_
        if node.op == "=":
            g.add(curr_ == rexp)
        elif node.op == "+=":
            g.add(curr_ == (old_ + rexp))
        elif node.op == "-=":
            g.add(curr_ == (old_ - rexp))
        elif node.op == "*=":
            g.add(curr_ == (old_ * rexp))
        elif node.op == "%=":
            g.add(curr_ == (old_ % rexp))
        g_ = z3.Goal()
        g_.add(z3.Exists(old_, g.as_expr()))
        g_ = t_qe_(g_)
        if not z3.is_quantifier(g_.as_expr()):
            print("q eliminated: %s" % old_)
            g = g_
        # g = z3.Goal()
        # g = g.simplify()
    elif isinstance(node, pycp.c_ast.If):
        cond_exp = gen_smt_expr(node.cond)
        vars_ = {}
        for e in vars:
            vars_[e] = vars[e]
        if node.iftrue is not None:
            true_expr = walk_block(node.iftrue, g, cond_exp).as_expr()
        else:
            true_expr = z3.And(cond_exp, g.as_expr())
        vars_t = {}
        for e in vars:
            vars_t[e] = vars[e]
            vars[e] = vars_[e]
        if node.iffalse is not None:
            false_expr = walk_block(
                node.iffalse, g, z3.Not(cond_exp)).as_expr()
        else:
            false_expr = z3.And(z3.Not(cond_exp), g.as_expr())
        g_t = z3.Goal()
        g_f = z3.Goal()
        g_t.add(true_expr)
        g_f.add(false_expr)
        for e in vars:
            if not vars[e].eq(vars_t[e]):
                ts[e] += 1
                new_ = z3.BitVec('%s!!%s' % (e, ts[e]), 32)
                g_t.add(new_ == vars_t[e])
                g_f.add(new_ == vars[e])
                vars[e] = new_
        g = z3.Goal()
        g.add(z3.Or(g_t.as_expr(), g_f.as_expr()))
        # print(g)
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
    ts = {}

    main_func = None

    for e in ast.ext:
        if isinstance(e, pycp.c_ast.FuncDef) and e.decl.name == "main":
            main_func = e
            break

    if main_func is None:
        raise("no main function")

    g = walk_block(main_func.body)

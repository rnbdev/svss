#!/usr/bin/python3

import z3
import sys

import clang.cindex as cl
cl.Config.set_library_file("/usr/lib/llvm-3.8/lib/libclang.so.1")


def gen_smt_expr(ast):
    if isinstance(ast, pycp.c_ast.Constant):
        return ast.value
    elif isinstance(ast, pycp.c_ast.ID):
        return vars[ast.name][1][-1]
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
        elif ast.op == "!=":
            return lexp != rexp


def walk_block(c):
    assumptions = []
    prog_path = []
    assertions = []
    assert c.kind == cl.CursorKind.COMPOUND_STMT  # debugging
    for e in c.get_children():
        if e.kind == cl.CursorKind.COMPOUND_STMT:
            prog_path.append(walk_block(e))
        elif e.kind == cl.CursorKind.DECL_STMT:
            for e_v in e.get_children():
                assert e_v.kind == cl.CursorKind.VAR_DECL
                vars[e.spelling] = [e.type.spelling, []]
                if e.type.spelling == "int":
                    vars[e.spelling][1].append(z3.Int("%s__0_" % e.spelling))
                    vars[e.spelling].append(vars[e.spelling][1][-1])
                elif e.type.spelling == "float":
                    vars[e.spelling][1].append(z3.Real("%s__0_" % e.spelling))
                    vars[e.spelling].append(vars[e.spelling][1][-1])
        elif e.kind == cl.CursorKind.CALL_EXPR:
            if e.spelling == "__ASSUME":
                for e_exp in e.args.exprs:
                    assumptions.append(gen_smt_expr(e_exp))
            elif e.spelling == "__ASSERT":
                for e_exp in e.args.exprs:
                    assertions.append(gen_smt_expr(e_exp))
            else:
                print("found a func call")
        elif isinstance(e, pycp.c_ast.Assignment):
            rexp = gen_smt_expr(e.rvalue)
            if "int" in vars[e.lvalue.name][0]:
                vars[e.lvalue.name][1].append(
                    z3.Int("%s__%i_" % (e.lvalue.name, len(vars[e.lvalue.name][1]))))
            elif "float" in vars[e.lvalue.name][0]:
                vars[e.lvalue.name][1].append(
                    z3.Real("%s__%i_" % (e.lvalue.name, len(vars[e.lvalue.name][1]))))
            if e.op == "=":
                prog_path.append(vars[e.lvalue.name][1][-1] == rexp)
            elif e.op == "+=":
                prog_path.append(vars[e.lvalue.name][1][-1]
                                 == (vars[e.lvalue.name][1][-2] + rexp))
            elif e.op == "-=":
                prog_path.append(vars[e.lvalue.name][1][-1]
                                 == (vars[e.lvalue.name][1][-2] - rexp))
            elif e.op == "*=":
                prog_path.append(vars[e.lvalue.name][1][-1]
                                 == (vars[e.lvalue.name][1][-2] * rexp))
            elif e.op == "%=":
                prog_path.append(vars[e.lvalue.name][1][-1]
                                 == (vars[e.lvalue.name][1][-2] % rexp))
        elif isinstance(e, pycp.c_ast.If):
            cond_exp = gen_smt_expr(e.cond)
            curr_ix = {key: len(vars[key][1]) - 1 for key in vars}
            bool_exp_true, bool_exp_false = [], []
            if e.iftrue is not None and e.iftrue.block_items is not None:
                bool_exp_true = walk_block(e.iftrue)
                for key in curr_ix:
                    vars[key][1][curr_ix[key]], vars[key][
                        1][-1] = vars[key][1][-1], vars[key][1][curr_ix[key]]
            if e.iffalse is not None and e.iffalse.block_items is not None:
                bool_exp_false = walk_block(e.iffalse)
            for key in vars:
                if curr_ix[key] + 1 == len(vars[key][1]):
                    continue
                if "int" in vars[key][0]:
                    vars[key][1].append(z3.Int("%s__%i_" %
                                               (key, len(vars[key][1]))))
                elif "float" in vars[key][0]:
                    vars[key][1].append(z3.Real("%s__%i_" %
                                                (key, len(vars[key][1]))))
                bool_exp_true.append(
                    vars[key][1][-1] == vars[key][1][curr_ix[key]])
                bool_exp_false.append(vars[key][1][-1] == vars[key][1][-2])
            prog_path.append(z3.If(cond_exp, z3.And(
                bool_exp_true), z3.And(bool_exp_false)))

    li = assumptions + prog_path
    if assertions:
        if len(assertions) > 1:
            assertions = z3.And(assertions)
        else:
            assertions = assertions[0]
        li.append(z3.Not(assertions))
    return li


if __name__ == "__main__":
    c_fname = sys.argv[1]

    index = cl.Index.create()

    tu = index.parse(sys.argv[1])

    cursor = tu.cursor

    vars = {}

    main_func = None

    for e in cursor.get_children():
        if e.kind == cl.CursorKind.FUNCTION_DECL:
            if e.spelling == "main":
                main_func = e
                break

    if main_func is None:
        raise("no main function")

    bool_exp = walk_block(main_func)
    s = z3.Solver()
    s.add(bool_exp)

    print(s)

    status = s.check()

    if status == z3.sat:
        print("program is unsafe.\nlisting an unsafe execution..")
        model = s.model()
        print("initial values:")
        for e in vars:
            print(e, ':', model[vars[e][-1]])
    elif status == z3.unsat:
        print("program is safe.")
    elif status == z3.unknown:
        print("unknown")

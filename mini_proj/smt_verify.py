#!/usr/bin/python3

import pycparser as pycp
import z3
import sys

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

def walk_block(body):
    assumptions = []
    prog_path = []
    assertions = []
    for e in body.block_items:
        if isinstance(e, pycp.c_ast.Decl):
            vars[e.type.declname] = [e.type.type.names, []]
            if "int" in e.type.type.names:
                vars[e.type.declname][1].append(z3.Int("%s__0_" % e.type.declname))
                vars[e.type.declname].append(vars[e.type.declname][1][-1])
            if "float" in e.type.type.names:
                vars[e.type.declname][1].append(z3.Real("%s__0_" % e.type.declname))
                vars[e.type.declname].append(vars[e.type.declname][1][-1])
        elif isinstance(e, pycp.c_ast.FuncCall):
            if e.name.name == "__ASSUME":
                for e_exp in e.args.exprs:
                    assumptions.append(gen_smt_expr(e_exp))
            elif e.name.name == "__ASSERT":
                for e_exp in e.args.exprs:
                    assertions.append(gen_smt_expr(e_exp))
            else:
                print("found a func call")
        elif isinstance(e, pycp.c_ast.Assignment):
            rexp = gen_smt_expr(e.rvalue)
            if "int" in vars[e.lvalue.name][0]:
                vars[e.lvalue.name][1].append(z3.Int("%s__%i_" % (e.lvalue.name, len(vars[e.lvalue.name][1]))))
            elif "float" in vars[e.lvalue.name][0]:
                vars[e.lvalue.name][1].append(z3.Real("%s__%i_" % (e.lvalue.name, len(vars[e.lvalue.name][1]))))
            if e.op == "=":
                prog_path.append(vars[e.lvalue.name][1][-1] == rexp)
            elif e.op == "+=":
                prog_path.append(vars[e.lvalue.name][1][-1] == (vars[e.lvalue.name][1][-2] + rexp))
            elif e.op == "-=":
                prog_path.append(vars[e.lvalue.name][1][-1] == (vars[e.lvalue.name][1][-2] - rexp))
            elif e.op == "*=":
                prog_path.append(vars[e.lvalue.name][1][-1] == (vars[e.lvalue.name][1][-2] * rexp))
            elif e.op == "%=":
                prog_path.append(vars[e.lvalue.name][1][-1] == (vars[e.lvalue.name][1][-2] % rexp))
        elif isinstance(e, pycp.c_ast.If):
            cond_exp = gen_smt_expr(e.cond)
            curr_ix = {key: len(vars[key][1])-1 for key in vars}
            bool_exp_true, bool_exp_false = [], []
            if e.iftrue is not None and e.iftrue.block_items is not None:
                bool_exp_true = walk_block(e.iftrue)
                for key in curr_ix:
                    vars[key][1][curr_ix[key]], vars[key][1][-1] = vars[key][1][-1], vars[key][1][curr_ix[key]]
            if e.iffalse is not None and e.iffalse.block_items is not None:
                bool_exp_false = walk_block(e.iffalse)
            for key in vars:
                if curr_ix[key] + 1 == len(vars[key][1]):
                    continue
                if "int" in vars[key][0]:
                    vars[key][1].append(z3.Int("%s__%i_" % (key, len(vars[key][1]))))
                elif "float" in vars[key][0]:
                    vars[key][1].append(z3.Real("%s__%i_" % (key, len(vars[key][1]))))
                bool_exp_true.append(vars[key][1][-1] == vars[key][1][curr_ix[key]])
                bool_exp_false.append(vars[key][1][-1] == vars[key][1][-2])
            prog_path.append(z3.If(cond_exp, z3.And(bool_exp_true), z3.And(bool_exp_false)))

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

    ast = pycp.parse_file(c_fname)

    # ast.show()

    vars = {}

    main_func = None

    for e in ast.ext:
        if isinstance(e, pycp.c_ast.FuncDef) and e.decl.name == "main":
            main_func = e
            break

    if main_func == None:
        raise("no main function")

    bool_exp = walk_block(main_func.body)
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
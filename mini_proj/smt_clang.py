#!/usr/bin/env python3

import clang.cindex as cl
import sys

cl.Config.set_library_file("/usr/lib/llvm-3.8/lib/libclang.so.1")

index = cl.Index.create()

tu = index.parse(sys.argv[1])

cursor = tu.cursor

def rec(c, k, flag=False):
    print((k<<1)*' ', end="")
    if flag:
        print(c.kind, c.spelling)
    elif c.kind == cl.CursorKind.VAR_DECL:
        print(c.kind, c.type.spelling, c.spelling)
    elif c.kind == cl.CursorKind.FUNCTION_DECL:
        print(c.kind, c.spelling)
    elif c.kind == cl.CursorKind.CALL_EXPR:
        print(c.kind, c.spelling)
    elif c.kind == cl.CursorKind.BINARY_OPERATOR or c.kind == cl.CursorKind.UNARY_OPERATOR:
        print(c.kind, "op", c.displayname, c.spelling, dir(c), [e.spelling for e in c.get_tokens()])
    elif c.kind == cl.CursorKind.UNEXPOSED_EXPR:
        print(c.kind, "unexp", c.spelling,[e.spelling for e in c.get_tokens()])
    elif c.kind == cl.CursorKind.DECL_REF_EXPR:
        print(c.kind, "ref -exp", c.spelling, [e.spelling for e in c.get_tokens()])
    else:
        print(c.kind)
    for e in c.get_children():
        rec(e, k+1, flag)

rec(cursor, 0)
#!/usr/bin/env python3

import z3

x, y = z3.Ints('x y')
x_g = x > 10
x_l = x < 10
y_g = y > 10
y_l = y < 10
li_p = list(z3.Bools('x_g x_l y_g y_l'))

s = z3.Solver()
s.add(z3.Implies(li_p[0], x_g))
s.add(z3.Implies(li_p[1], x_l))
s.add(z3.Implies(li_p[2], y_g))
s.add(z3.Implies(li_p[3], y_l))

cores = [e for e in li_p]

status = s.check(cores)
print(s)
unsat_cores = s.unsat_core()
print(unsat_cores)

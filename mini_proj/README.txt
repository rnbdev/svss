		Property verification of C code using SMT Solver
			 Chennai Mathematical Institute
			    Ranadeep Biswas, MSc II

      A tool to verify property of very simple C codes using SMT solver Z3

Requirements:
	* python3
	* z3
	* python3 module
		- z3-solver
		- pycparser

Installation on Ubuntu:
	sudo apt update
	sudo apt install python3 z3 virtualenv
	virtualenv venv -p python3
	source venv/bin/activate
	pip install -r requirements.txt
	# done, now to verify simple.c
	python3 smt_verify.py simple.c

Usage:
	python3 smt_verify.py <code.c>

Restriction on C code:
	* No outside function call.
	* Every declaration and code should be inside `main` function.
	* No loop - code must be straight line program.
	* Variables are modified only at assignment statement.
		i.e. no use of `++`.
	* Use `__ASSUME` and `__ASSERT` function to assume or assert properties.
		e.g. __ASSUME(0 < x, x <= 10); __ASSERT(x != 100, x != 200)

import Mathlib.Order.PiLex

/- Exercise 5.11. A faithful statement requires upstream owners for program `(5.27)`, its
full associated basic solution and independently defined lexicographically optimal bases, and
an output-bearing simplex computation with termination and correctness specifications. The
verified reusable APIs currently available without those upstream owners are finite
lexicographic order and the canonical greatest-element predicate checked below. -/
#check toLex
#check IsGreatest

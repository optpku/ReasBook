/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Example_9_1.Objectives

public section

/-! Exercise 9.1. Statement-stage canonical reuse.

The Chapter 9 likelihood objective `(9.5)` and its displayed gradient and
Hessian formulas `(9.6)`-`(9.8)` are already formalized in the item-local
foundation module `Book.Ch9.Example_9_1.Objectives`. This file stays thin and
source-facing by reusing those existing Chapter 9 anchors directly.
-/

/- Exercise 9.1 (1).

The gradient formula `(9.6)` for the Chapter 9 likelihood objective `J_lhd`
from `(9.5)` is formalized by
`gradient_example91LikelihoodFunctional`.
-/
#check gradient_example91LikelihoodFunctional

/- Exercise 9.1 (2).

The diagonal matrix formula `(9.8)` occurring in the Hessian representation is
formalized by `example91LikelihoodDiagonal_def`.
-/
#check example91LikelihoodDiagonal_def

/- Exercise 9.1 (3).

The Hessian formula `(9.7)` using the diagonal matrix from `(9.8)` is
formalized by `hessian_example91LikelihoodFunctional`.
-/
#check hessian_example91LikelihoodFunctional

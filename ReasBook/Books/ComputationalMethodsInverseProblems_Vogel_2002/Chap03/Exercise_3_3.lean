/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional

public section

/- Exercise 3.3. The source asks for the explicit solution of the positive-step
line-search subproblem for steepest descent on a quadratic functional with
positive-definite Hessian. The canonical Chapter 3 formalization already exists
as `QuadraticOptimization.exactLineSearchStep_quadraticFunctional`, so this
item records direct reuse of that theorem owner. -/

#check QuadraticOptimization.exactLineSearchStep_quadraticFunctional

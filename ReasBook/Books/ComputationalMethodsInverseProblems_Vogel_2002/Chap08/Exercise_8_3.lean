/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Algorithm_8_2_2.Clauses

public section

/-!
Exercise 8.3.

The source exercise concerns the displayed two-dimensional discrete formula
`(8.29)` for `L' (f) f`. The current repository snapshot still does not expose
a chapter-specific owner for the discrete penalty operator `L(f)` or for its
derivative, so this item must not replace that concrete source statement by a
generic public predicate on arbitrary `L'`, `Dx`, `Dy`, and `ψ''`.

Accordingly this file remains a labeled blocker/check-only surface. The checks
below record the existing Chapter 8 Newton owners that a future faithful
formalization of `(8.29)` should connect to directly.
-/

/- Exercise 8.3. Main labeled source-facing blocker entry for the discrete
two-dimensional formula `(8.29)` for `L' (f) f`.

The existing Chapter 8 Newton API already records the penalty-Hessian clause
`H_J := L(f_v) + L' (f_v) (f_v)`, but the book's concrete two-dimensional
discrete operator `L(f)` and its derivative still do not have a source-faithful
owner in the repository. This file therefore keeps the exercise as a
blocker/check-only surface instead of weakening it to an arbitrary matrix
wrapper API.
-/
#check TVNewton.HasPenaltyHessianFormula

/- Exercise 8.3. Once the discrete `(8.29)` owner exists, its main downstream
use should be through the Newton penalty-Hessian accessor below rather than a
parallel exercise-local wrapper. -/
#check TVNewton.HasGradientAndPenaltyHessian.penaltyHessian_eq

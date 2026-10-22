/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5_1.Iteration

public section

/-! Exercise 9.18. Canonical bridge surface.

This exercise is a source-facing bridge/view item. The Richardson-Lucy step
`(9.42)` itself is already owned by `RichardsonLucy.update`, and the
transpose/backprojection rewrite obtained from the split-gradient hint is
already formalized by `RichardsonLucy.update_eq_transpose_mulVec`. The exercise
therefore reuses that existing Chapter 9 theorem directly instead of introducing
a duplicate wrapper.
-/

/- Exercise 9.18.

Using the hint's rewriting of the negative Poisson log-likelihood
`J f = ⟪Matrix.mulVec K f, 1⟫ - ⟪d, log (Matrix.mulVec K f)⟫`, the split-gradient
decomposition identifies the Richardson-Lucy step with its
transpose/backprojection form. The faithful source-facing anchor for that
exercise conclusion is `RichardsonLucy.update_eq_transpose_mulVec`.
-/
#check RichardsonLucy.update_eq_transpose_mulVec

/- Companion owner for the Richardson-Lucy step `(9.42)`. -/
#check RichardsonLucy.update

/- Companion bridge identifying the split-gradient positive term with `Kᵀ *ᵥ 1`. -/
#check RichardsonLucy.columnSum_eq_mulVec_transpose_one

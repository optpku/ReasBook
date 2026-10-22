/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_6_2

/- Chapter03 Assumption 3.6-extra-1: the nonlinear equation `F x = 0` on a real normed
space has a solution `xStar` such that `F` is continuously differentiable on a neighborhood of
`xStar` and `fderiv ℝ F xStar` is invertible.

Source/core/bridge triage:
* source-facing: existence of a regular zero for `F`
* core/canonical: the Chapter 3.6 owner `IsRegularZero`
* bridge/view: none; this assumption is exactly the existential reuse of `IsRegularZero`

The previous public predicate `HasInexactNewtonAssumptions` and its `_iff` theorem duplicated
the already adequate Chapter 3.6 owner surface and had no downstream users. This file therefore
stays at the recall layer and records the source-facing proposition anonymously. -/

section InexactNewtonMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (F : E → E)

/-- Chapter03 Assumption 3.6-extra-1: the source-facing hypotheses `(A1)`-`(A3)` for the
nonlinear equation `F x = 0` are exactly the existence of a regular zero in the canonical
Chapter 3.6 sense. -/
theorem exists_regularZero_iff_exists_textbook_assumptions :
    (∃ xStar : E, IsRegularZero F xStar) ↔
      ∃ xStar : E,
        F xStar = 0 ∧
          (∃ s ∈ nhds xStar, ContDiffOn ℝ 1 F s) ∧
          (fderiv ℝ F xStar).IsInvertible := by
  constructor
  · rintro ⟨xStar, hxStar⟩
    -- The controlled object is the candidate zero `xStar`; now unpack `IsRegularZero` into A1--A3.
    exact ⟨xStar, (isRegularZero_iff F xStar).mp hxStar⟩
  · rintro ⟨xStar, hxStar⟩
    -- Route correction: repackage the textbook assumptions back into the canonical owner.
    exact ⟨xStar, (isRegularZero_iff F xStar).mpr hxStar⟩

end InexactNewtonMethod

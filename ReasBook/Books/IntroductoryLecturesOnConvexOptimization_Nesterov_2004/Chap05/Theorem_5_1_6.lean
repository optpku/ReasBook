/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/-
Theorem 5.1.6 belongs to the Chapter 5 self-concordance / closed-convex domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOn` from `Definition_5_1_1`, the source-facing qualitative owner when the
  value of the self-concordance constant is not part of the statement;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for pointwise
  Hessian positivity together with strict Hessian quadratic-form positivity on a domain;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative owner used only after
  unpacking a witness from `IsSelfConcordantOn`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` shell;
* `hessianLocalNorm` and `hessianLocalNorm_def` from `Definition_5_1_1`, the canonical bridge
  from the Hessian owner to the local norm;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the source epigraph
  over a feasible domain, whose closedness supplies the missing hypothesis from the source
  theorem.

Source/core/bridge triage:
* source-facing: strict positivity of the Hessian quadratic form in every nonzero direction under
  qualitative self-concordance and the source no-affine-line hypothesis;
* core/canonical: `HasPositiveDefiniteHessianOn dom f`, the Hessian owner `hessian f x`, and the
  Chapter 3 constrained-epigraph owner on `dom`;
* bridge/view: pointwise positivity and strict local-norm positivity read canonically via
  `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
  `HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def`.

Primitive data:
* the ambient complete real inner-product space `E`;
* a domain `dom`, objective `f`, and the closed constrained epigraph
  `constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))`;
* the no-affine-line hypothesis on `dom`.

Derived API:
* the chapter owner `HasPositiveDefiniteHessianOn dom f`.

This file keeps the numbered theorem source-facing, but its core output is now the chapter owner
`HasPositiveDefiniteHessianOn dom f`. Downstream pointwise Hessian and local-norm positivity are
read from that owner through `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
`HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def` instead of new local wrapper
theorems. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOn

variable {dom : Set E} {f : E → ℝ}

/-- Helper for Theorem 5.1.6: every self-concordant function admits a strictly positive
self-concordance constant after enlarging the original witness by `1`. -/
theorem exists_positive_selfconcordant_constant
    {Mf0 : NNReal} (h0 : IsSelfConcordantOnWith dom Mf0 f) :
    ∃ Mf : NNReal, 0 < (Mf : ℝ) ∧ IsSelfConcordantOnWith dom Mf f := by
  -- Enlarge the original witness by `1` so the inverse Dikin radius is strictly positive.
  refine ⟨Mf0 + 1, ?_, ?_⟩
  · exact_mod_cast show (0 : NNReal) < Mf0 + 1 by simp
  · exact h0.of_le (by simp)

/-- Helper for Theorem 5.1.6: if the Hessian quadratic form vanishes in direction `h`, then the
entire affine line through `x` in direction `h` lies in the open Dikin ellipsoid centered at `x`
with radius `1 / Mf`. -/
theorem line_point_mem_openDikinEllipsoid_of_zero_quadratic_form
    {Mf : NNReal} {x h : E} (hq : inner ℝ h (hessian f x h) = 0) (hMf_pos : 0 < (Mf : ℝ)) :
    ∀ τ : ℝ, x + τ • h ∈ openDikinEllipsoid f x (1 / (Mf : ℝ)) := by
  intro τ
  -- Rewriting the Dikin quadratic form for the displacement `τ • h` collapses it to `0`.
  have hquad :
      inner ℝ ((x + τ • h) - x) (hessian f x ((x + τ • h) - x)) = 0 := by
    simp [inner_smul_left, inner_smul_right, hq]
  have hquad_nonneg :
      0 ≤ inner ℝ ((x + τ • h) - x) (hessian f x ((x + τ • h) - x)) := by
    rw [hquad]
  -- A zero quadratic form is strictly below the positive inverse-square radius.
  refine
    (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq f x (x + τ • h) hquad_nonneg
      (le_of_lt (one_div_pos.mpr hMf_pos))).2 ?_
  rw [hquad]
  positivity

/-- Helper for Theorem 5.1.6: a zero Hessian quadratic form along `h` forces the whole affine
line through `x` in direction `h` to stay inside `dom`. -/
theorem affine_line_mem_dom_of_zero_quadratic_form
    {Mf : NNReal} (hself : IsSelfConcordantOnWith dom Mf f) {x h : E}
    (hMf_pos : 0 < (Mf : ℝ)) (hx : x ∈ dom)
    (hq : inner ℝ h (hessian f x h) = 0) :
    ∀ τ : ℝ, x + τ • h ∈ dom := by
  intro τ
  -- First place each line point in the Dikin ellipsoid, then use the standard inclusion theorem.
  have hτ_mem :
      x + τ • h ∈ openDikinEllipsoid f x (1 / (Mf : ℝ)) :=
    line_point_mem_openDikinEllipsoid_of_zero_quadratic_form (f := f) hq hMf_pos τ
  exact hself.openDikinEllipsoid_inv_constant_subset hx hτ_mem

-- Proof sketch: if the Hessian quadratic form vanished at some `x ∈ dom` in a nonzero direction
-- `h`, then the restriction of `f` to the affine line `x + ℝ • h` would be locally affine at
-- `x`. Closedness of the constrained epigraph upgrades this local zero-curvature behavior to an
-- entire affine line in `dom`, contradicting the source hypothesis.
/-- Theorem 5.1.6: if `f` is self-concordant on `dom`, the constrained epigraph of `f` over
`dom` is closed, and `dom` contains no affine line, then the Hessian of `f` is positive definite
on `dom`. -/
theorem hasPositiveDefiniteHessianOn_of_no_affine_line
    (hself : IsSelfConcordantOn dom f)
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom) :
    HasPositiveDefiniteHessianOn dom f := by
  rcases hself with ⟨Mf0, hMf0⟩
  obtain ⟨Mf, hMf_pos, hMf⟩ := exists_positive_selfconcordant_constant (f := f) hMf0
  refine ⟨?_, ?_⟩
  · intro x hx
    -- The qualitative owner already supplies pointwise Hessian positivity on the domain.
    exact hMf.hessian_isPositive hx
  · intro x hx h hh
    -- Route correction: use the Chapter 5 Dikin inclusion theorem directly rather than the old
    -- epigraph sketch. A vanishing quadratic form would force an affine line inside `dom`.
    by_contra hnotlt
    have hnonneg : 0 ≤ inner ℝ h (hessian f x h) := hMf.hessian_posSemidef hx h
    have hq : inner ℝ h (hessian f x h) = 0 := by
      exact le_antisymm (not_lt.mp hnotlt) hnonneg
    have hline : ∀ τ : ℝ, x + τ • h ∈ dom :=
      affine_line_mem_dom_of_zero_quadratic_form (f := f) hMf hMf_pos hx hq
    exact (hnoAffineLine hh) hline

end IsSelfConcordantOn

end

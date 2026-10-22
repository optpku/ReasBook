/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal} {f : E → ℝ}

/-
Definition 2.7 lies in the second-order smooth-convex domain on finite-dimensional real
inner-product spaces.

Sampled owner-style declarations:
* `ConvexC1SeminormSmooth` / `f ∈ 𝓕[L, p]¹¹` in `Theorem_2_5`, the chapter owner for `C¹` convex
  objectives with `L`-Lipschitz gradient measured by `p`
* `ConvexC1SeminormSmooth.contDiff`, the canonical `C¹` regularity projection from that owner
* `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` in `Theorem_2_6`, the bridge from
  the first-order owner plus `ContDiff ℝ 2` to the textbook Hessian inequalities
* `HasLipschitzContinuousHessian` / `f ∈ C22[L₃]` in `Chap04/Definition_4_2_7`, a nearby chapter
  pattern where a source-facing smoothness class is kept as a named owner and reuses canonical
  projections instead of duplicating its downstream API

Best owner abstraction:
* source-facing: `ConvexC2SeminormSmooth p L f`, written on theorem surfaces as `f ∈ 𝓕[L, p]²¹`
* core/canonical: `f ∈ 𝓕[L, p]¹¹ ∧ ContDiff ℝ 2 f`
* bridge/view: Theorem 2.6's Hessian quadratic-form characterization

Primitive data:
* the smooth-convex owner hypothesis `f ∈ 𝓕[L, p]¹¹`
* the second-order regularity hypothesis `ContDiff ℝ 2 f`

Derived API:
* the inherited convexity and gradient-Lipschitz consequences from `f ∈ 𝓕[L, p]¹¹`
* the `C²` projection
* the source-text Hessian inequalities recovered through Theorem 2.6

This file therefore restores the textbook class surface `𝓕_L^{2,1}` as a thin source-facing owner,
but it does not duplicate the first-order smooth-convex machinery or repackage the Hessian
characterization as new primitive data. The canonical pair remains the core definition, and
Theorem 2.6 supplies the bridge back to the textbook Hessian condition.
-/

/-- Definition 2.7: a function belongs to the source-facing class `𝓕_L^{2,1}` when it already
lies in the chapter smooth-convex class `𝓕[L, p]¹¹` and is twice continuously differentiable. The
textbook Euclidean class `𝓕_L^{2,1}(ℝⁿ)` is the specialization `p = normSeminorm ℝ E`. -/
abbrev ConvexC2SeminormSmooth
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  f ∈ 𝓕[L, p]¹¹ ∧ ContDiff ℝ 2 f

scoped[SmoothConvex] notation "𝓕[" L ", " p "]²¹" =>
  setOf (ConvexC2SeminormSmooth p L)

/-- The notation `f ∈ 𝓕[L, p]²¹` is the source-facing set view of the owner predicate
`ConvexC2SeminormSmooth p L f`. -/
theorem mem_F21_iff :
    f ∈ 𝓕[L, p]²¹ ↔ ConvexC2SeminormSmooth p L f :=
  Iff.rfl

namespace ConvexC2SeminormSmooth

/-- Membership in `𝓕[L, p]²¹` includes the canonical Chapter 2 smooth-convex owner
`f ∈ 𝓕[L, p]¹¹`. -/
theorem objective_mem
    (hf : ConvexC2SeminormSmooth p L f) :
    f ∈ 𝓕[L, p]¹¹ :=
  hf.1

/-- Membership in `𝓕[L, p]²¹` includes twice continuous differentiability. -/
theorem contDiff
    (hf : ConvexC2SeminormSmooth p L f) :
    ContDiff ℝ 2 f :=
  hf.2

/-- Theorem 2.6 re-expresses `𝓕[L, p]²¹` by the displayed Hessian quadratic-form inequalities.
-/
theorem iff_contDiff_and_hessian_quadratic_form_bounded :
    ConvexC2SeminormSmooth p L f ↔
      ContDiff ℝ 2 f ∧
        ∀ x h : E,
          0 ≤ inner ℝ (hessian f x h) h ∧
            inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 := by
  constructor
  · rintro ⟨hf11, hfC2⟩
    exact
      ⟨hfC2,
        (convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded hfC2).mp hf11⟩
  · rintro ⟨hfC2, hquad⟩
    exact
      ⟨(convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded hfC2).mpr hquad, hfC2⟩

/-- Membership in `𝓕[L, p]²¹` yields the textbook Hessian quadratic-form inequalities. -/
theorem hessian_quadratic_form_bounded
    (hf : ConvexC2SeminormSmooth p L f) (x h : E) :
    0 ≤ inner ℝ (hessian f x h) h ∧
      inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 :=
  (iff_contDiff_and_hessian_quadratic_form_bounded.mp hf).2 x h

end ConvexC2SeminormSmooth

/-- Definition 2.7 restated on theorem surfaces: the source-facing class `𝓕[L, p]²¹` is exactly
the canonical pair `f ∈ 𝓕[L, p]¹¹ ∧ ContDiff ℝ 2 f`, and therefore equivalently the Chapter 2
Hessian inequalities of Theorem 2.6. -/
theorem mem_F21_iff_contDiff_and_hessian_quadratic_form_bounded :
    f ∈ 𝓕[L, p]²¹ ↔
      ContDiff ℝ 2 f ∧
        ∀ x h : E,
          0 ≤ inner ℝ (hessian f x h) h ∧
            inner ℝ (hessian f x h) h ≤ (L : ℝ) * (p h) ^ 2 :=
  ConvexC2SeminormSmooth.iff_contDiff_and_hessian_quadratic_form_bounded

end

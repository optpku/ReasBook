/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : ℕ) (f : E → ℝ) (s : Set E) (L : NNReal)

local notation "TaylorSeries" => E → FormalMultilinearSeries ℝ E ℝ

/- Definition 4.2.10 lies in the on-set higher-order Taylor-coefficient Lipschitz domain.

Sampled owner-style declarations:
* `taylorCoeffLipschitzClass`
* `HasFTaylorSeriesUpToOn`
* `HasFTaylorSeriesUpToOn.contDiffOn`
* `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`

Owner abstraction:
* the Chapter 1 source-facing owner `taylorCoeffLipschitzClass`
* this item is the self-order specialization `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)`

Source/core/bridge triage:
* source-facing: `f ∈ 𝒞^{p - 1,p - 1}_{L}(s)`
* core/canonical: `HasFTaylorSeriesUpToOn (p - 1) f P s`
* bridge/view: the `iteratedFDerivWithin` formula recovered on `UniqueDiffOn ℝ s`

Primitive data:
* a Taylor witness `P`
* `HasFTaylorSeriesUpToOn (p - 1) f P s`
* `LipschitzOnWith L (fun x ↦ P x (p - 1)) s`

Derived API:
* `ContDiffOn ℝ (p - 1) f s`
* the source-style `iteratedFDerivWithin` norm estimate on `UniqueDiffOn ℝ s`

This file does not introduce a second owner around `iteratedFDerivWithin`; it reuses the
Chapter 1 owner and keeps the iterated-derivative formula only as a bridge.
-/

/- Definition 4.2.10: a nonnegative constant `L` is a Lipschitz constant for the `(p - 1)`-st
derivative of `f` on `s` exactly when `f` belongs to the Chapter 1 owner
`𝒞^{p - 1,p - 1}_{L}(s)`. The `iteratedFDerivWithin` presentation is a bridge view recovered
under `UniqueDiffOn ℝ s`, not the primitive owner.
-/
#check (f ∈ 𝒞^{p - 1,p - 1}_{L}(s))

namespace taylorCoeffLipschitzClass

theorem contDiffOn
    {p : ℕ} {f : E → ℝ} {s : Set E} {L : NNReal}
    (hf : f ∈ 𝒞^{p - 1,p - 1}_{L}(s)) :
    ContDiffOn ℝ (p - 1) f s := by
  rcases hf.2 with ⟨P, hP, _⟩
  exact hP.contDiffOn

/-- On a set with unique differentiability, membership in `𝒞^{p - 1,p - 1}_{L}(s)` recovers the
source-style pointwise Lipschitz estimate for `iteratedFDerivWithin ℝ (p - 1) f s`. -/
theorem norm_sub_le_iteratedFDerivWithin
    {p : ℕ} {f : E → ℝ} {s : Set E} {L : NNReal}
    (hf : f ∈ 𝒞^{p - 1,p - 1}_{L}(s)) (hs : UniqueDiffOn ℝ s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖iteratedFDerivWithin ℝ (p - 1) f s x - iteratedFDerivWithin ℝ (p - 1) f s y‖ ≤
      (L : ℝ) * ‖x - y‖ := by
  rcases hf.2 with ⟨P, hP, hLip⟩
  simpa [hP.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx,
    hP.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hy] using hLip.norm_sub_le hx hy

end taylorCoeffLipschitzClass

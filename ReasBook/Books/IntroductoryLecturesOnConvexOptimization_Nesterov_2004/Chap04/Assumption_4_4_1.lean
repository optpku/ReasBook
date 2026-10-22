/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Assumption 4.4.1 lies in the local first-order smoothness domain for real-valued functions on
feasible subsets of real normed spaces.

Sampled owner-style declarations:
* mathlib `DifferentiableOn ℝ f 𝓕`
* mathlib `UniqueDiffOn ℝ 𝓕`
* mathlib `LipschitzOnWith L g 𝓕`
* mathlib `contDiffOn_succ_iff_fderivWithin`
* Chapter 1's whole-space owner pair `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` in
  `Nesterov.Chap01.Definition_1_5_2`

Best owner abstraction:
* source-facing: `HasLipschitzDerivativeOnWith L 𝓕 f`
* core/canonical: the primitive triple `DifferentiableOn ℝ f 𝓕`, `UniqueDiffOn ℝ 𝓕`, and
  `LipschitzOnWith L (fun x ↦ fderivWithin ℝ f 𝓕 x) 𝓕`
* bridge/view: on open sets, the ambient-derivative reformulation through `fderiv`; on
  `Set.univ`,
  the whole-space `ContDiff ℝ 1 f`

Primitive data:
* the feasible set `𝓕`
* the objective `f`
* differentiability of `f` on `𝓕`
* unique differentiability of `𝓕`, making the within derivative intrinsic
* the Lipschitz bound for the derivative map `x ↦ fderivWithin ℝ f 𝓕 x` on `𝓕`

Derived API:
* continuity of the within derivative map on `𝓕`
* `ContDiffOn ℝ 1 f 𝓕` on the feasible set
* on open feasible sets, continuity and Lipschitz control for the ambient derivative map
* the whole-space specialization `ContDiff ℝ 1 f` on `Set.univ`

The source statement is genuinely local and on-set, so it should remain a source-facing owner
instead of being collapsed into the Chapter 1 whole-space Hilbert-space owner pair. The refine
work here is therefore to keep that local owner thin on the canonical within-derivative layer,
with the ambient `fderiv` view only as an open-set bridge, not to introduce a parallel wrapper
around already existing global owners.
-/

/-- Assumption 4.4.1: a real-valued function on a subset `𝓕` of a real normed space has a
Lipschitz-continuous derivative with constant `L` when it is differentiable on the uniquely
differentiable feasible set `𝓕` and its canonical within-derivative map
`x ↦ fderivWithin ℝ f 𝓕 x` is `L`-Lipschitz on `𝓕`. On open feasible sets this agrees with the
ambient derivative formulation. -/
class HasLipschitzDerivativeOnWith (L : NNReal) {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (𝓕 : Set E) (f : E → ℝ) : Prop where
  /-- The function is differentiable on the feasible set. -/
  differentiableOn : DifferentiableOn ℝ f 𝓕
  /-- The feasible set is uniquely differentiable, so the within derivative is intrinsic. -/
  uniqueDiffOn : UniqueDiffOn ℝ 𝓕
  /-- The derivative map is `L`-Lipschitz on the feasible set. -/
  lipschitz : LipschitzOnWith L (fun x ↦ fderivWithin ℝ f 𝓕 x) 𝓕

namespace HasLipschitzDerivativeOnWith

variable {L : NNReal} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝓕 : Set E} {f : E → ℝ}

/-- The canonical within-derivative map in Assumption 4.4.1 is continuous on the feasible set
because every Lipschitz map is continuous on its domain. -/
theorem continuousOn_fderivWithin
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) :
    ContinuousOn (fderivWithin ℝ f 𝓕) 𝓕 :=
  hf.lipschitz.continuousOn

/-- Assumption 4.4.1 upgrades the objective to a `C¹` function on the feasible set in the
canonical mathlib within-set sense. -/
theorem contDiffOn
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) :
    ContDiffOn ℝ 1 f 𝓕 := by
  simpa [contDiffOn_zero] using
    (contDiffOn_succ_iff_fderivWithin hf.uniqueDiffOn).2
      ⟨hf.differentiableOn, by simp, contDiffOn_zero.mpr hf.continuousOn_fderivWithin⟩

/-- On an open feasible set, the within-derivative control from Assumption 4.4.1 is exactly the
ambient derivative control. -/
theorem lipschitz_fderiv_of_isOpen
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) (h𝓕 : IsOpen 𝓕) :
    LipschitzOnWith L (fun x ↦ fderiv ℝ f x) 𝓕 := by
  intro x hx y hy
  simpa [fderivWithin_of_isOpen h𝓕 hx, fderivWithin_of_isOpen h𝓕 hy] using hf.lipschitz hx hy

/-- On an open feasible set, Assumption 4.4.1 also gives continuity of the ambient derivative
map. -/
theorem continuousOn_fderiv_of_isOpen
    (hf : HasLipschitzDerivativeOnWith L 𝓕 f) (h𝓕 : IsOpen 𝓕) :
    ContinuousOn (fderiv ℝ f) 𝓕 :=
  (hf.lipschitz_fderiv_of_isOpen h𝓕).continuousOn

/-- The whole-space specialization of Assumption 4.4.1 yields global `C¹` regularity. -/
theorem contDiff
    (hf : HasLipschitzDerivativeOnWith L Set.univ f) :
    ContDiff ℝ 1 f := by
  simpa [contDiffOn_univ] using hf.contDiffOn

/-- The whole-space specialization of Assumption 4.4.1 yields ordinary differentiability on the
ambient normed space. -/
theorem differentiable
    (hf : HasLipschitzDerivativeOnWith L Set.univ f) :
    Differentiable ℝ f :=
  differentiableOn_univ.mp hf.differentiableOn

end HasLipschitzDerivativeOnWith

/-- Constant real-valued functions have Lipschitz-continuous derivative on any uniquely
differentiable feasible set for every Lipschitz constant. -/
instance {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : NNReal) (𝓕 : Set E) (h𝓕 : UniqueDiffOn ℝ 𝓕) (c : ℝ) :
    HasLipschitzDerivativeOnWith L 𝓕 (fun _ : E ↦ c) where
  differentiableOn := differentiableOn_const c
  uniqueDiffOn := h𝓕
  lipschitz := by
    simpa [fderivWithin_const] using
      (LipschitzWith.const' (0 : E →L[ℝ] ℝ)).lipschitzOnWith

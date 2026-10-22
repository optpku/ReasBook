/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.1.2 lies in the local Hessian-Lipschitz smooth-optimization domain on complete
real inner-product spaces.

Sampled owner declarations:
* `hessian f x` in `Definition_1_4_16`
* `HasLipschitzContinuousHessian L f` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.lipschitz` in `Definition_4_2_7`
* `HasLipschitzContinuousHessian.norm_sub_le` in `Definition_4_2_7`
* `ContDiffOn ℝ 2 f 𝓕`
* `LipschitzOnWith L (hessian f) 𝓕`

Source/core/bridge triage:
* source-facing: `HessianLipschitzOn L 𝓕 f`
* core/canonical: `HasLipschitzContinuousHessian L f`
* bridge/view: restriction from the global owner to an open convex set

Owner abstraction:
* the local owner `HessianLipschitzOn L 𝓕 f`, built from the canonical global owner when `𝓕` is
  an open convex region

Primitive data:
* a Lipschitz constant `L`
* a domain `𝓕`
* a function `f`
* openness and convexity of `𝓕`
* `C²` regularity and Hessian-Lipschitz control on `𝓕`

Derived API:
* the `Fact` instance for the on-set Hessian Lipschitz bound
* continuity of the Hessian map on the domain
* the pointwise `C²` bridge `HessianLipschitzOn.contDiffAt`
* the pointwise operator-norm estimate `HessianLipschitzOn.norm_sub_le`
* the bridge `HasLipschitzContinuousHessian.toHessianLipschitzOn`

This keeps the source-facing local owner while connecting it to the existing project-level global
owner instead of leaving two parallel root Hessian-Lipschitz APIs. -/

/-- Definition 4.1.2: on an open convex set `𝓕`, a twice continuously differentiable
real-valued function has `L`-Lipschitz Hessian when the Hessian map is `L`-Lipschitz with
respect to the ambient norm and the induced operator norm. The source Euclidean case `𝓕 ⊆ ℝⁿ`
is recovered by specializing `E` to `EuclideanSpace ℝ (Fin n)`. -/
class HessianLipschitzOn (L : NNReal) (𝓕 : Set E) (f : E → ℝ) : Prop where
  /-- The domain `𝓕` is open. -/
  isOpen : IsOpen 𝓕
  /-- The domain `𝓕` is convex. -/
  convex : Convex ℝ 𝓕
  /-- The function is twice continuously differentiable on `𝓕`. -/
  contDiffOn : ContDiffOn ℝ 2 f 𝓕
  /-- The Hessian map `x ↦ ∇² f(x)` is `L`-Lipschitz on `𝓕`. -/
  lipschitz : LipschitzOnWith L (hessian f) 𝓕

/-- Restricting a globally Hessian-Lipschitz `C²` function to an open convex set produces the
source-facing local owner `HessianLipschitzOn`. -/
theorem HasLipschitzContinuousHessian.toHessianLipschitzOn
    {L : NNReal} {𝓕 : Set E} {f : E → ℝ} (hf : HasLipschitzContinuousHessian L f)
    (h_open : IsOpen 𝓕) (h_convex : Convex ℝ 𝓕) :
    HessianLipschitzOn L 𝓕 f :=
  { isOpen := h_open
    convex := h_convex
    contDiffOn := hf.contDiff.contDiffOn
    lipschitz := (HasLipschitzContinuousHessian.lipschitz hf).lipschitzOnWith }

/-- A `HessianLipschitzOn` hypothesis canonically supplies the underlying Hessian Lipschitz bound
on the domain. -/
instance {L : NNReal} {𝓕 : Set E} {f : E → ℝ} [hf : HessianLipschitzOn L 𝓕 f] :
    Fact (LipschitzOnWith L (hessian f) 𝓕) where
  out := hf.lipschitz

/-- The global owner restricts to the local owner on the whole space. -/
instance {L : NNReal} {f : E → ℝ} [hf : HasLipschitzContinuousHessian L f] :
    HessianLipschitzOn L Set.univ f :=
  hf.toHessianLipschitzOn isOpen_univ convex_univ

namespace HessianLipschitzOn

/-- The Hessian map of a `HessianLipschitzOn` function is continuous on the domain. -/
theorem continuousOn_hessian
    {L : NNReal} {𝓕 : Set E} {f : E → ℝ} (hf : HessianLipschitzOn L 𝓕 f) :
    ContinuousOn (hessian f) 𝓕 :=
  hf.lipschitz.continuousOn

/-- A `HessianLipschitzOn` hypothesis supplies the pointwise `C²` regularity needed at every
point of the domain. -/
theorem contDiffAt
    {L : NNReal} {𝓕 : Set E} {f : E → ℝ} (hf : HessianLipschitzOn L 𝓕 f)
    {x : E} (hx : x ∈ 𝓕) :
    ContDiffAt ℝ 2 f x :=
  hf.contDiffOn.contDiffAt (hf.isOpen.mem_nhds hx)

/-- The defining pointwise Hessian-Lipschitz estimate of `HessianLipschitzOn L 𝓕 f` is the
operator-norm inequality `‖∇² f(x) - ∇² f(y)‖ ≤ L ‖x - y‖` for points of `𝓕`. -/
theorem norm_sub_le
    {L : NNReal} {𝓕 : Set E} {f : E → ℝ} (hf : HessianLipschitzOn L 𝓕 f)
    {x y : E} (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖hessian f x - hessian f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  simpa [dist_eq_norm] using hf.lipschitz.dist_le_mul x hx y hy

end HessianLipschitzOn

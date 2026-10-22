/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped HessianLocalNorm

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

namespace IsSelfConcordantOnWith

/- Theorem 5.1.2 lies in the Chapter 5 self-concordance affine-pullback calculus.

Primary domain:
- self-concordant functions on open convex domains and affine precomposition

Sampled owner-style declarations in this domain:
- `IsSelfConcordantOnWith`
- `ConvexC1On.comp_continuousAffineMap`
- `ClosedConvexOn.comp_continuousAffineMap`
- mathlib `HasFTaylorSeriesUpToOn.comp_continuousAffineMap`

Best owner abstraction:
- `IsSelfConcordantOnWith.comp_continuousAffineMap`

Primitive data:
- the owner witness `hf : IsSelfConcordantOnWith dom Mf f`
- the continuous affine map `g : E →ᴬ[ℝ] E₁`

Derived API:
- the finite-dimensional affine-map specialization `comp_affineMap`
- the linear-plus-translation source presentation `x ↦ A x + b`

Source/core/bridge triage:
- source-facing: affine pullback closure of self-concordance
- core/canonical: `IsSelfConcordantOnWith.comp_continuousAffineMap`
- bridge/view: finite-dimensional affine maps, then the textbook `A x + b` presentation

The old statement used a plain `LinearMap` together with finite-dimensional hypotheses only to
recover continuity. The canonical owner surface is the continuous-affine-map pullback theorem;
finite-dimensional affine-map presentations should be derived from it rather than kept as the main
API. -/

-- Proof sketch: openness and convexity pull back along a continuous affine map, `ContDiffOn`
-- composes with continuous affine maps, and the affine bridge identities for the Hessian local
-- norm and third directional derivative transfer the cubic bound with the same constant `Mf`.
/-- Theorem 5.1.2: precomposing a self-concordant function with a continuous affine map preserves
self-concordance on the affine preimage with the same self-concordance constant. This is the
canonical owner-level affine-pullback theorem. -/
theorem comp_continuousAffineMap
    {dom : Set E₁} {Mf : NNReal} {f : E₁ → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f) (g : E →ᴬ[ℝ] E₁) :
    IsSelfConcordantOnWith (g ⁻¹' dom) Mf (f ∘ g) := by
  refine
    { isOpen_domain := hf.isOpen_domain.preimage g.continuous
      contDiffOn := hf.contDiffOn.comp g.contDiff.contDiffOn (fun _ hx ↦ hx)
      convexOn := by
        simpa using hf.convexOn.comp_affineMap (g : E →ᵃ[ℝ] E₁)
      third_deriv_bound := ?_ }
  intro x hx u
  have hx_dom : g x ∈ dom := hx
  have hcont :
      ContDiffAt ℝ 2 f (g x) := by
    exact (hf.contDiffOn.of_le (by norm_num)).contDiffAt (hf.isOpen_domain.mem_nhds hx_dom)
  simpa [thirdDirectionalDerivative_comp_affine, hessianLocalNorm_comp_affine f g x u hcont] using
    hf.third_deriv_bound hx_dom (g.contLinear u)

-- Proof sketch: regard an affine map on a finite-dimensional domain as a continuous affine map and
-- apply `comp_continuousAffineMap`.
/-- Theorem 5.1.2, finite-dimensional specialization: affine precomposition preserves
self-concordance on the affine preimage. -/
theorem comp_affineMap
    [FiniteDimensional ℝ E]
    {dom : Set E₁} {Mf : NNReal} {f : E₁ → ℝ}
    (hf : IsSelfConcordantOnWith dom Mf f) (g : E →ᵃ[ℝ] E₁) :
    IsSelfConcordantOnWith (g ⁻¹' dom) Mf (f ∘ g) := by
  simpa using hf.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

end IsSelfConcordantOnWith

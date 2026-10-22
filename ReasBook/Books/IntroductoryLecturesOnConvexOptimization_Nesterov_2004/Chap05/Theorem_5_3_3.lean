/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Gradient HessianLocalNorm

variable {E : Type u} {E₁ : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/- Theorem 5.3.3 lies in the Chapter 5 self-concordant-barrier affine-pullback calculus.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers;
* `IsSelfConcordantOnWith.comp_continuousAffineMap` from `Theorem_5_1_2`, the owner-level
  affine-pullback theorem for standard self-concordance;
* `IsSelfConcordantOnWith.comp_affineMap` from `Theorem_5_1_2`, the finite-dimensional
  specialization derived from the continuous-affine owner theorem;
* `IsSelfConcordantBarrierOnWith.isBarrierFunctionOn` from `Definition_5_3_2`, the canonical
  bridge from a self-concordant barrier to the Chapter 1 barrier owner.

Best owner abstraction:
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`.

Primitive data:
* the owner witness `h : IsSelfConcordantBarrierOnWith dom ν F`;
* the continuous affine map `g : E →ᴬ[ℝ] E₁`.

Derived API:
* the owner-level pullback barrier `F ∘ g` on `g ⁻¹' dom`;
* the finite-dimensional specialization `comp_affineMap`;
* the coordinate presentation `x ↦ F (A x + b)` when `g x = A x + b`.

Source/core/bridge triage:
* source-facing: affine pullback closure of self-concordant barriers;
* core/canonical: `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`;
* bridge/view: the finite-dimensional `comp_affineMap` specialization, then the textbook
  linear-plus-translation form `x ↦ F (A x + b)`.

The barrier owner is defined over complete real inner-product spaces, and the surrounding chapter
already organizes affine pullback calculus around continuous affine maps. This refinement therefore
keeps the numbered content in the barrier owner namespace at the `ContinuousAffineMap` level, with
`comp_affineMap` retained only as the finite-dimensional bridge. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: apply `IsSelfConcordantOnWith.comp_continuousAffineMap` to the standard
-- self-concordance field of the barrier owner. For the barrier parameter, fix `x ∈ g ⁻¹' dom`
-- and rewrite the gradient and Hessian quadratic form of `F ∘ g` in the direction `u` through
-- the image direction `g.toAffineMap.linear u`; then apply the owner bound for `F` at `g x`.
/-- Theorem 5.3.3: if `F` is a `ν`-self-concordant barrier on `dom ⊆ E₁`, then its precomposition
with a continuous affine map `g : E →ᴬ[ℝ] E₁` is a `ν`-self-concordant barrier on the affine
preimage `g ⁻¹' dom`. This is the owner-level affine-pullback theorem. -/
theorem comp_continuousAffineMap
    {dom : Set E₁} {ν : NNReal} {F : E₁ → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (g : E →ᴬ[ℝ] E₁) :
    IsSelfConcordantBarrierOnWith (g ⁻¹' dom) ν (F ∘ g) := by
  let hstd : IsStandardSelfConcordantOn dom F := h.toIsStandardSelfConcordantOn
  refine
    { toIsStandardSelfConcordantOn := hstd.comp_continuousAffineMap g
      barrier_parameter_bound := ?_ }
  intro x hx u
  have hpull : IsStandardSelfConcordantOn (g ⁻¹' dom) (F ∘ g) :=
    hstd.comp_continuousAffineMap g
  have hPos : (hessian (F ∘ g) x).IsPositive := hpull.hessian_isPositive hx
  refine ((_root_.barrier_parameter_bound_iff_gradient_inner_sq_le hPos).2 ?_) u
  intro u
  have hx_dom : g x ∈ dom := hx
  have hcont :
      ContDiffAt ℝ 2 F (g x) := by
    exact (hstd.contDiffOn.of_le (by norm_num)).contDiffAt (hstd.isOpen_domain.mem_nhds hx_dom)
  have hdiff : DifferentiableAt ℝ F (g x) := hcont.differentiableAt (by norm_num)
  have hdiff_comp : DifferentiableAt ℝ (F ∘ g) x :=
    (hcont.comp x g.contDiff.contDiffAt).differentiableAt (by norm_num)
  have hsq :=
      (_root_.barrier_parameter_bound_iff_gradient_inner_sq_le
          (hstd.hessian_isPositive hx_dom)).mp
        (h.barrier_parameter_bound hx_dom)
  calc
    (inner ℝ (∇ (F ∘ g) x) u) ^ (2 : ℕ) = (fderiv ℝ (F ∘ g) x u) ^ (2 : ℕ) := by
      rw [inner_gradient_left hdiff_comp]
    _ = (fderiv ℝ F (g x) (g.contLinear u)) ^ (2 : ℕ) := by
      congr 1
      simpa using congrArg (fun A : E →L[ℝ] ℝ ↦ A u) (fderiv_comp x hdiff g.differentiableAt)
    _ = (inner ℝ (∇ F (g x)) (g.contLinear u)) ^ (2 : ℕ) := by
      rw [← inner_gradient_left hdiff]
    _ ≤ (ν : ℝ) * ‖g.contLinear u‖[F; g x] ^ (2 : ℕ) :=
      hsq (g.contLinear u)
    _ = (ν : ℝ) * ‖u‖[F ∘ g; x] ^ (2 : ℕ) := by
      rw [← hessianLocalNorm_comp_affine F g x u hcont]

/-- Theorem 5.3.3, finite-dimensional specialization: affine precomposition preserves the barrier
property on the affine preimage with the same barrier parameter. -/
theorem comp_affineMap
    [FiniteDimensional ℝ E]
    {dom : Set E₁} {ν : NNReal} {F : E₁ → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν F) (g : E →ᵃ[ℝ] E₁) :
    IsSelfConcordantBarrierOnWith (g ⁻¹' dom) ν (F ∘ g) := by
  simpa using h.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

end IsSelfConcordantBarrierOnWith

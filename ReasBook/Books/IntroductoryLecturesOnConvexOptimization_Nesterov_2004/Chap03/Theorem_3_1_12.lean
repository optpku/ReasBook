/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Filter Set
open scoped Topology WithTopConvexAnalysis

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-
Theorem 3.1.12 lies in the chapter's convex directional-derivative bridge domain.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real representative of an `ℝ ∪ {+∞}`-valued function;
- `ConvexOn.comp_affineMap`, the canonical way to pass convexity to the one-variable directional
  slice;
- `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior` in mathlib
  `Analysis/Convex/Deriv.lean`, the owner theorem for one-sided derivatives of convex real-valued
  functions on an interval-like interior domain.

Best owner abstraction:
- core/canonical: the one-variable convex derivative theorem
  `ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior` applied to the affine slice
  `α ↦ x + α • p`;
- bridge/view: the source-facing secant-slope limit statement below, together with eventual
  finiteness of the ray in `dom f`.

Primitive data:
- a convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- an interior point `hx : x ∈ interior (dom f)`.

Derived API:
- eventual finiteness of `x + α • p` for `α ↓ 0`;
- convergence of the finite real secant slopes.

Source/core/bridge triage:
- source-facing: the secant-slope limit theorem below;
- core/canonical: the mathlib one-variable derivative theorem on the directional slice;
- bridge/view: the affine-line reduction from `E` to `ℝ`.
-/
/-- Theorem 3 1 12: a convex `ℝ ∪ {+∞}`-valued function has a finite one-sided directional
derivative in every direction at every interior point of its effective domain. -/
-- Proof sketch: apply the monotonicity argument for the positive secant slopes
-- `α ↦ (withTopRealPart f (x + α • p) - withTopRealPart f x) / α` of a convex function. The
-- interior-point hypothesis gives a backward point on the same affine line, which yields a
-- uniform lower bound on these slopes; hence they admit a finite right limit in `ℝ`.
theorem exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    ∃ d : ℝ,
      (∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
        Tendsto
          (fun α : ℝ ↦
            (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
          (𝓝[>] (0 : ℝ)) (𝓝 d) := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + p)
  let S : Set ℝ := g ⁻¹' dom f
  let φ : ℝ → ℝ := withTopRealPart f ∘ g
  have hg_apply (α : ℝ) : g α = x + α • p := by
    simpa [g, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x (x + p) α)
  have hphi : φ = fun α : ℝ ↦ withTopRealPart f (x + α • p) := by
    funext α
    simp [φ, hg_apply]
  have hconv : ConvexOn ℝ S φ := by
    -- Restrict convexity to the affine line through `x` in direction `p`.
    simpa [S, φ, g] using
      hf.comp_affineMap (AffineMap.lineMap x (x + p))
  have hcont : Continuous g := by
    simpa [g] using
      (AffineMap.lineMap_continuous : Continuous (AffineMap.lineMap x (x + p) : ℝ →ᵃ[ℝ] E))
  have h0dom : ∀ᶠ α : ℝ in 𝓝 (0 : ℝ), g α ∈ dom f :=
    hcont.continuousAt.eventually_mem
      (by simpa [g] using
        (mem_interior_iff_mem_nhds.mp hx))
  have hS_nhds : S ∈ 𝓝 (0 : ℝ) := by
    simpa [S] using h0dom
  have hS0 : (0 : ℝ) ∈ interior S := mem_interior_iff_mem_nhds.mpr hS_nhds
  let d : ℝ := sInf (slope φ 0 '' {α : ℝ | α ∈ S ∧ 0 < α})
  have hderiv_Ioi :
      HasDerivWithinAt
        (fun α : ℝ ↦ withTopRealPart f (x + α • p))
        d (Set.Ioi (0 : ℝ)) 0 := by
    -- Rewrite the one-variable slice first, then apply the convex derivative theorem.
    rw [← hphi]
    simpa [d, Set.setOf_and, and_left_comm, and_assoc] using
      hconv.hasDerivWithinAt_sInf_slope_of_mem_interior hS0
  have hIoi : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), g α ∈ dom f :=
    h0dom.filter_mono nhdsWithin_le_nhds
  have hdom_eventually : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
    filter_upwards [hIoi] with α hα
    simpa [hg_apply α] using hα
  have htendsto :
      Tendsto
        (fun α : ℝ ↦
          (withTopRealPart f (x + α • p) - withTopRealPart f x) / α)
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    -- Convert the right derivative on `Ioi` into a slope limit on the same one-variable slice.
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)] at hderiv_Ioi
    simpa [slope_fun_def_field] using hderiv_Ioi
  exact ⟨d, hdom_eventually, htendsto⟩

end

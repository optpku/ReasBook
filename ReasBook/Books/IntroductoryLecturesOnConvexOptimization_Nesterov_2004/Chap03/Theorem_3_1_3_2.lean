/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis Topology WithTopConvexAnalysis

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-
Theorem 3.1.3.2 lies in the chapter's convex directional-differentiability domain.

Primary domain:
- finite one-sided directional differentiability of convex `WithTop ℝ`-valued functions at
  interior points of the effective domain.

Relevant owner-style declarations sampled before refinement:
- `DirectionallyDifferentiableAt` and `HasDirectionalDerivAt` in
  `Nesterov.Chap03.Definition_3_1_3_1`, the source-facing directional-derivative owners;
- `dom f`, `withTopRealPart f`, and `withTopToEReal ∘ f` in `Definition_3_3`, the chapter's
  canonical bridge from `WithTop ℝ`-valued convex functions to the `EReal` directional-derivative
  owner surface;
- `exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain` in
  `Nesterov.Chap03.Theorem_3_1_12`, the upstream finite-real secant-slope limit theorem that
  supplies the bridge data.

Best owner abstraction:
- `DirectionallyDifferentiableAt (withTopToEReal ∘ f) x p`

Primitive data:
- the convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior-point assumption `hx : x ∈ interior (dom f)`.

Derived API:
- the source-facing directional differentiability statement below;
- the explicit `∃ d, HasDirectionalDerivAt ... d` companion.

Source/core/bridge triage:
- source-facing: directional differentiability of a convex `WithTop ℝ`-valued function at an
  interior point of `dom f`;
- core/canonical: `DirectionallyDifferentiableAt` and `HasDirectionalDerivAt`;
- bridge/view: the secant-slope existence theorem `Theorem_3_1_12`.

The previous version moved the numbered item to the weaker `EReal` secant-limit bridge layer by
recalling `Theorem_3_14`. This file now returns to the source-facing directional-derivative API,
uses `Theorem_3_1_12` only as internal bridge data, and keeps the ambient space at the weaker
topological real-module owner level already used by `HasDirectionalDerivAt`, rather than freezing
the older normed-space proof route into the public theorem surface.
-/
namespace ConvexOn

/-- Theorem 3.1.3.2: a convex `ℝ ∪ {+∞}`-valued function is directionally differentiable in every
direction at every interior point of its effective domain. -/
-- Proof sketch: `Theorem_3_1_12` already yields a finite real right limit of the secant slopes
-- together with eventual finiteness of the ray. Interpreting that limit as a derivative of the
-- scalar slice gives `HasDirectionalDerivAt` for the canonical `EReal` bridge `withTopToEReal ∘
-- f`, and hence `DirectionallyDifferentiableAt`.
theorem directionallyDifferentiableAt_of_mem_interior_dom
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    DirectionallyDifferentiableAt (withTopToEReal ∘ f) x p := by
  have hmem_dom_toEReal {y : E} (hy : y ∈ dom f) :
      y ∈ dom (withTopToEReal ∘ f) := by
    change withTopToEReal (f y) ≠ ⊤ ∧ withTopToEReal (f y) ≠ ⊥
    constructor
    · intro htop
      exact (ne_of_lt hy) (WithBot.coe_eq_top.mp htop)
    · exact WithBot.coe_ne_bot
  rcases exists_tendsto_right_directionalSlope_of_convexOn_of_mem_interior_effectiveDomain
      hf hx with ⟨d, hd_dom, hd_tendsto⟩
  refine ⟨d, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hmem_dom_toEReal (interior_subset hx)
  · filter_upwards [hd_dom] with α hα
    exact hmem_dom_toEReal hα
  · have hderiv :
        HasDerivWithinAt
          (fun α ↦ extendedRealRealPart (withTopToEReal ∘ f) (x + α • p))
          d (Set.Ioi (0 : ℝ)) 0 := by
        have hslice :
            (fun α : ℝ ↦ extendedRealRealPart (withTopToEReal ∘ f) (x + α • p)) =
              fun α : ℝ ↦ withTopRealPart f (x + α • p) := by
          funext α
          cases hfx : f (x + α • p) with
          | top =>
              simp [extendedRealRealPart, withTopRealPart, withTopToEReal, Function.comp, hfx]
              rfl
          | coe a =>
              simp [extendedRealRealPart, withTopRealPart, withTopToEReal, Function.comp, hfx]
              rfl
        rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi (0 : ℝ) by simp)]
        rw [hslice]
        simpa [slope_fun_def_field] using hd_tendsto
    exact hderiv.Ici_of_Ioi

/-- A convex `ℝ ∪ {+∞}`-valued function admits a finite directional derivative in every direction
at every interior point of its effective domain. -/
theorem exists_hasDirectionalDerivAt_of_mem_interior_dom
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x p : E} (hx : x ∈ interior (dom f)) :
    ∃ d : ℝ, HasDirectionalDerivAt (withTopToEReal ∘ f) x p d := by
  simpa [DirectionallyDifferentiableAt] using
    hf.directionallyDifferentiableAt_of_mem_interior_dom hx

end ConvexOn

end

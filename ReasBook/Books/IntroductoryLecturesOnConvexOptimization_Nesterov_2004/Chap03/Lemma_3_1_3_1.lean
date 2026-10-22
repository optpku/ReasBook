/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis Topology WithTopConvexAnalysis

universe u

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/- Lemma 3.1.3.1 is source-facing in the chapter's convex directional-derivative domain.

Primary domain:
- finite directional derivatives of convex `ℝ ∪ {+∞}`-valued functions at interior points.

Sampled owner-style declarations:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative at a finite base point;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the owner
  convexity theorem for the theorem-level finite directional-derivative view on all directions;
- `withTopEffectiveDomain`, `withTopRealPart`, and
  `ConvexOn ℝ (dom f) (withTopRealPart f)` in `Definition_3_3`;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity.

Best owner abstraction:
- the theorem-level finite `toReal` view of the chapter owner
  `convexDirectionalDerivative f x (interior_subset hx)`, identified upstream with
  `HasDirectionalDerivAt`.

Primitive data:
- none in this file; the secant-slope and `EReal` infimum construction are already owned upstream
  by `Theorem_3_21`.

Derived API:
- the owner-level convexity recall on all directions;
- the positive-homogeneity theorem for the finite directional-derivative owner;
- the affine-support inequality in real form on the same topological-module owner layer.

Source/core/bridge triage:
- source-facing: the real-valued directional derivative at an interior point, together with its
  convexity, degree-one positive homogeneity, and affine support inequality;
- core/canonical: `convexDirectionalDerivative` and `HasDirectionalDerivAt`;
- bridge/view: the upstream direct `toReal` expansion against
  `convexDirectionalDerivative f x (interior_subset hx)`.

This file therefore stops re-owning the directional derivative as a global real-valued definition.
The `EReal` infimum-of-slopes object remains the upstream core owner, while the public surface
here uses only the explicit theorem-level finite view supplied by the chapter
directional-derivative API. The convexity, positive-homogeneity, and affine-support surface all
live in the same topological-module layer.
-/

section Core

variable {f : E → WithTop ℝ}

/- Lemma 3.1.3.1 (1): for a convex `ℝ ∪ {+∞}`-valued function and an interior point `x` of its
effective domain, the finite directional derivative given by the explicit `toReal` view of
`convexDirectionalDerivative` is convex on all directions. -/
recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

/-- Helper for Lemma 3.1.3.1: a finite `WithTop ℝ` value stays finite after coercion to `EReal`.
-/
theorem mem_dom_withTopToEReal_comp_of_mem_dom
    {y : E} (hy : y ∈ dom f) :
    y ∈ dom (withTopToEReal ∘ f) := by
  change withTopToEReal (f y) ≠ ⊤ ∧ withTopToEReal (f y) ≠ ⊥
  constructor
  · intro htop
    exact (ne_of_lt hy) (WithBot.coe_eq_top.mp htop)
  · exact WithBot.coe_ne_bot

/-- Helper for Lemma 3.1.3.1: reading a `WithTop ℝ` value through `EReal.toReal` gives the same
finite real part as `withTopRealPart`. -/
theorem withTopToEReal_toReal_eq_withTopRealPart
    {z : E} :
    (withTopToEReal (f z)).toReal = withTopRealPart f z := by
  cases hfz : f z with
  | top =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_top
  | coe a =>
      rw [withTopRealPart, Function.comp_apply, hfz]
      exact EReal.toReal_coe a

/-- Helper for Lemma 3.1.3.1: the finite directional derivative at an interior point vanishes in
the zero direction. -/
theorem convexDirectionalDerivativeReal_zero_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) :
    f′[hx] (0 : E) = 0 := by
  -- Compare the owner directional derivative with the constant-ray zero-direction derivative.
  have howner :
      HasDirectionalDerivAt (withTopToEReal ∘ f) x (0 : E) (f′[hx] (0 : E)) :=
    convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx 0
  have hzero :
      HasDirectionalDerivAt (withTopToEReal ∘ f) x (0 : E) 0 :=
    HasDirectionalDerivAt.zero (f := withTopToEReal ∘ f) (x := x)
      (mem_dom_withTopToEReal_comp_of_mem_dom (f := f) (interior_subset hx))
  exact HasDirectionalDerivAt.unique howner hzero

/-- Helper for Lemma 3.1.3.1: the finite directional derivative scales linearly under positive
real dilation of the direction variable. -/
theorem convexDirectionalDerivativeReal_smul_of_pos
    {x p : E} (_hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) {τ : ℝ} (hτ : 0 < τ) :
    f′[hx] (τ • p) = τ * f′[hx] p := by
  -- Pass the extended-valued positive-scaling law through the finite `toReal` owner surface.
  rw [convexDirectionalDerivativeReal_apply, convexDirectionalDerivativeReal_apply]
  rw [convexDirectionalDerivative_smul (f := f) (hx := interior_subset hx) hτ p]
  simp [EReal.toReal_mul]

/-- Lemma 3.1.3.1 (1): for a convex `ℝ ∪ {+∞}`-valued function and an interior point `x` of its
effective domain, the finite directional derivative is positively homogeneous of degree one on all
directions. Its canonical pointwise rescaling API is the owner projection `map_smul` with bundled
nonnegative scalars `τ : NNReal`. -/
-- Proof sketch: the interior-point directional derivative is the finite theorem-surface view of
-- the canonical owner `convexDirectionalDerivative`; positive homogeneity is obtained by passing
-- the extended-valued positive-scaling law to this finite owner.
theorem convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f)) :
    IsPositivelyHomogeneousOn 1 Set.univ (f′[hx]) := by
  refine ⟨?_, ?_⟩
  · -- The domain is all of `E`, so nonnegative rescaling stays in the domain automatically.
    intro p _ τ
    simp
  · intro p _ τ
    by_cases hτ : τ = 0
    · -- The zero scalar branch reduces to the zero-direction value.
      rw [hτ, zero_smul]
      simpa [Real.rpow_one] using
        convexDirectionalDerivativeReal_zero_of_mem_interior (f := f) hf hx
    · -- For positive scalars, transfer the owner scaling identity to the real-valued view.
      have hτ_pos : 0 < (τ : ℝ) := by
        exact_mod_cast (show 0 < τ from pos_iff_ne_zero.mpr hτ)
      simpa [Real.rpow_one, smul_eq_mul] using
        convexDirectionalDerivativeReal_smul_of_pos (f := f) (x := x) (p := p) hf hx hτ_pos

/-- Every point `y` in the effective domain lies above the affine lower support determined by the
finite directional derivative at an interior point `x`. -/
-- Proof sketch: rewrite the supporting inequality for the directional derivative in the finite
-- real-valued owner surface `convexDirectionalDerivativeReal`, without reintroducing an
-- inner-product-only subgradient detour.
theorem convexDirectionalDerivativeReal_affine_support_of_mem_interior
    {x : E} (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx : x ∈ interior (dom f))
    {y : E} (hy : y ∈ dom f) :
    withTopRealPart f y ≥
      withTopRealPart f x + f′[hx] (y - x) := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let S : Set ℝ := line ⁻¹' dom f
  let g : ℝ → ℝ := withTopRealPart f ∘ line
  have hline_apply (α : ℝ) : line α = x + α • (y - x) := by
    simpa [line, sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm] using
      (AffineMap.lineMap_apply_module x y α)
  have hconv : ConvexOn ℝ S g := by
    -- Restrict the convex function to the affine line through `x` and `y`.
    simpa [S, g] using hf.comp_affineMap line
  have hzero_mem : (0 : ℝ) ∈ S := by
    simpa [S, hline_apply] using interior_subset hx
  have hone_mem : (1 : ℝ) ∈ S := by
    simpa [S, hline_apply] using hy
  have hslice :
      (fun α : ℝ ↦ (withTopToEReal (f (x + α • (y - x)))).toReal) = g := by
    -- The `EReal.toReal` slice is exactly the `withTopRealPart` slice on the same affine line.
    funext α
    change (withTopToEReal (f (x + α • (y - x)))).toReal = withTopRealPart f (line α)
    rw [hline_apply]
    simpa using
      (withTopToEReal_toReal_eq_withTopRealPart (f := f) (z := x + α • (y - x)))
  have hderiv_Ici : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ici (0 : ℝ)) 0 := by
    -- The directional-derivative owner theorem gives the right derivative of the scalar slice.
    simpa [extendedRealRealPart_eq_toReal, Function.comp, hslice] using
      (convexDirectionalDerivative_toReal_hasDirectionalDerivAt hf hx (y - x)).hasDerivWithinAt
  have hderiv_Ioi : HasDerivWithinAt g (f′[hx] (y - x)) (Set.Ioi (0 : ℝ)) 0 :=
    hderiv_Ici.Ioi_of_Ici
  have hslope :
      f′[hx] (y - x) ≤ withTopRealPart f y - withTopRealPart f x := by
    -- A convex scalar slice lies above its right derivative at the left endpoint.
    simpa [g, slope_def_field, hline_apply] using
      hconv.le_slope_of_hasDerivWithinAt_Ioi hzero_mem hone_mem zero_lt_one hderiv_Ioi
  linarith

end Core

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.1 lies in the Chapter 5 self-concordance calculus domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for self-concordance on an
  open convex domain;
* mathlib `ContDiffOn.add` and `ConvexOn.add`, the canonical additive calculus owners reused by
  self-concordance proofs;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  zero-self-concordance perturbation owner used downstream in Corollary 5.1.2;
* `IsSelfConcordantOnWith.comp_continuousAffineMap` from `Theorem_5_1_2`, the nearby owner-level
  closure theorem showing the same namespace pattern for derived self-concordance calculus.

Source/core/bridge triage:
* source-facing: the weighted-sum closure theorem for self-concordant functions;
* core/canonical: the owner predicate `IsSelfConcordantOnWith`;
* bridge/view: the unweighted additive specialization `add`.

Primitive data:
* two owner witnesses `h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁` and
  `h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂`;
* positive weights `α` and `β`, carried canonically by `NNRealˣ`.

Derived API:
* the weighted-sum closure theorem itself;
* the additive specialization obtained by setting `α = β = 1`.

The refined file keeps the source-facing weighted theorem as the primary declaration and treats the
plain sum as its thin specialization, rather than as a second independent calculus theorem. -/

namespace IsSelfConcordantOnWith

/-- Helper for Theorem 5.1.1: squaring the Hessian local norm recovers the underlying Hessian
quadratic form once that quadratic form is known to be nonnegative. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {g : E → ℝ} {x u : E} (hquad : 0 ≤ inner ℝ u (hessian g x u)) :
    ‖u‖[g; x] ^ (2 : ℕ) = inner ℝ u (hessian g x u) := by
  -- Expand the local norm and use the standard `sqrt(x)^2 = x` identity.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.1.1: positive rescaling preserves self-concordance while dividing the
constant by the square root of the scaling factor. -/
private theorem pos_smul_with_div_sqrt
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantOnWith dom Mf f) (α : NNRealˣ) :
    IsSelfConcordantOnWith dom (Mf / NNReal.sqrt α) ((α : ℝ) • f) := by
  have hα : 0 < (α : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα_nonneg : 0 ≤ (α : ℝ) := le_of_lt hα
  refine
    { isOpen_domain := h.isOpen_domain
      contDiffOn := by
        -- `C³` regularity is stable under multiplication by a constant.
        simpa using h.contDiffOn.const_smul (α : ℝ)
      convexOn := by
        -- Convexity is stable under multiplication by a nonnegative constant.
        simpa using ConvexOn.smul hα_nonneg h.convexOn
      third_deriv_bound := ?_ }
  intro x hx u
  have hthird :
      thirdDirectionalDerivative ((α : ℝ) • f) x u =
        (α : ℝ) * thirdDirectionalDerivative f x u := by
    -- Rewrite the directional slice of the scaled function as a scaled univariate slice.
    rw [thirdDirectionalDerivative]
    have hs : directionalSlice ((α : ℝ) • f) x u = (α : ℝ) • directionalSlice f x u := by
      funext t
      simp [directionalSlice]
    rw [hs, iteratedDeriv_const_smul_field]
    simp [thirdDirectionalDerivative, smul_eq_mul]
  have hnorm :
      hessianLocalNorm ((α : ℝ) • f) x u = Real.sqrt α * ‖u‖[f; x] := by
    -- Pull the scalar through the Hessian, then evaluate the resulting square root.
    have hhess : hessian ((α : ℝ) • f) = (α : ℝ) • hessian f := by
      funext y
      unfold hessian
      rw [show ∇ ((α : ℝ) • f) = (α : ℝ) • ∇ f by
        funext z
        unfold gradient
        rw [fderiv_const_smul_field]
        exact (InnerProductSpace.toDual ℝ E).symm.map_smul (α : ℝ) (fderiv ℝ f z)]
      rw [fderiv_const_smul_field]
    rw [hessianLocalNorm_def, hessianLocalNorm_def, hhess]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_right]
    rw [Real.sqrt_mul hα_nonneg]
  calc
    |thirdDirectionalDerivative ((α : ℝ) • f) x u|
        = (α : ℝ) * |thirdDirectionalDerivative f x u| := by
            rw [hthird, abs_mul, abs_of_nonneg hα_nonneg]
    _ ≤ (α : ℝ) * (2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)) := by
      gcongr
      exact h.third_deriv_bound hx u
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) * (Real.sqrt α * ‖u‖[f; x]) ^ (3 : ℕ) := by
      rw [NNReal.coe_div, Real.coe_sqrt]
      have hsqrt_ne : Real.sqrt (α : ℝ) ≠ 0 := by
        exact Real.sqrt_ne_zero'.2 hα
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt hα_nonneg]
      ring
    _ = 2 * ((Mf / NNReal.sqrt α : NNReal) : ℝ) *
          hessianLocalNorm ((α : ℝ) • f) x u ^ (3 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 5.1.1: a `C²` scalar field has a differentiable gradient at the base
point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x) :
    DifferentiableAt ℝ (∇ g) x := by
  -- Rewrite the gradient through the Riesz isomorphism so differentiability follows from the
  -- differentiability of the Fréchet derivative field.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ g) x := by
    exact
      (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ g y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.1.1: on open domains where both summands are `C²`, the Hessian of the
sum is the sum of the Hessians at the given point. -/
private theorem hessian_add_at
    {dom₁ dom₂ : Set E} {g₁ g₂ : E → ℝ} {x : E}
    (hg₁ : ContDiffOn ℝ 2 g₁ dom₁) (hopen₁ : IsOpen dom₁) (hx₁ : x ∈ dom₁)
    (hg₂ : ContDiffOn ℝ 2 g₂ dom₂) (hopen₂ : IsOpen dom₂) (hx₂ : x ∈ dom₂) :
    hessian (g₁ + g₂) x = hessian g₁ x + hessian g₂ x := by
  have hgrad_nhds :
      (fun y ↦ ∇ (g₁ + g₂) y) =ᶠ[nhds x] fun y ↦ ∇ g₁ y + ∇ g₂ y := by
    -- Near `x`, both summands are differentiable, so the gradient of the sum is the sum of
    -- the gradients pointwise.
    filter_upwards [hopen₁.mem_nhds hx₁, hopen₂.mem_nhds hx₂] with y hy₁ hy₂
    have hg₁y : DifferentiableAt ℝ g₁ y := by
      exact (hg₁.contDiffAt (hopen₁.mem_nhds hy₁)).differentiableAt (by norm_num)
    have hg₂y : DifferentiableAt ℝ g₂ y := by
      exact (hg₂.contDiffAt (hopen₂.mem_nhds hy₂)).differentiableAt (by norm_num)
    rw [gradient, fderiv_add hg₁y hg₂y]
    simp [gradient]
  have hgrad₁ : DifferentiableAt ℝ (∇ g₁) x := by
    exact differentiableAt_gradient_of_contDiffAt_two (hg₁.contDiffAt (hopen₁.mem_nhds hx₁))
  have hgrad₂ : DifferentiableAt ℝ (∇ g₂) x := by
    exact differentiableAt_gradient_of_contDiffAt_two (hg₂.contDiffAt (hopen₂.mem_nhds hx₂))
  -- Differentiate the neighborhood identity for the gradient at the base point.
  rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgrad₁ hgrad₂]

/-- Helper for Theorem 5.1.1: the sum of two nonnegative cubes is bounded by the cubic power of
their Euclidean norm. -/
private theorem pow_three_sum_le_hypot_cube
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (3 : Nat) + b ^ (3 : Nat) ≤
      (a ^ (2 : Nat) + b ^ (2 : Nat)) * Real.sqrt (a ^ (2 : Nat) + b ^ (2 : Nat)) := by
  have ha_le :
      a ≤ Real.sqrt (a ^ (2 : Nat) + b ^ (2 : Nat)) := by
    have hsquare : a ^ (2 : Nat) ≤ a ^ (2 : Nat) + b ^ (2 : Nat) := by
      nlinarith [sq_nonneg b]
    have hsqrt :
        Real.sqrt (a ^ (2 : Nat)) ≤ Real.sqrt (a ^ (2 : Nat) + b ^ (2 : Nat)) :=
      Real.sqrt_le_sqrt hsquare
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg ha] using hsqrt
  have hb_le :
      b ≤ Real.sqrt (a ^ (2 : Nat) + b ^ (2 : Nat)) := by
    have hsquare : b ^ (2 : Nat) ≤ a ^ (2 : Nat) + b ^ (2 : Nat) := by
      nlinarith [sq_nonneg a]
    have hsqrt :
        Real.sqrt (b ^ (2 : Nat)) ≤ Real.sqrt (a ^ (2 : Nat) + b ^ (2 : Nat)) :=
      Real.sqrt_le_sqrt hsquare
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hb] using hsqrt
  -- Each cube is at most its square times the common hypotenuse factor.
  nlinarith [sq_nonneg a, sq_nonneg b, ha, hb, ha_le, hb_le]

/-- Helper for Theorem 5.1.1: adding two self-concordant functions on the intersection domain
preserves self-concordance with the maximum of the two constants. -/
private theorem add_inter_max
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {g₁ g₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ g₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ g₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂) (max M₁ M₂) (g₁ + g₂) := by
  refine
    { isOpen_domain := h₁.isOpen_domain.inter h₂.isOpen_domain
      contDiffOn := ?_
      convexOn := ?_
      third_deriv_bound := ?_ }
  · -- Restrict both `C³` owners to the intersection domain and add them there.
    have hcont₁ : ContDiffOn ℝ 3 g₁ (dom₁ ∩ dom₂) :=
      h₁.contDiffOn.mono (by intro x hx; exact hx.1)
    have hcont₂ : ContDiffOn ℝ 3 g₂ (dom₁ ∩ dom₂) :=
      h₂.contDiffOn.mono (by intro x hx; exact hx.2)
    simpa using hcont₁.add hcont₂
  · -- First view each summand as convex on the intersection, then add the convexity inequalities.
    have hconv₁ : ConvexOn ℝ (dom₁ ∩ dom₂) g₁ := by
      refine ⟨h₁.convexOn.1.inter h₂.convexOn.1, ?_⟩
      intro x hx y hy a b ha hb hab
      exact h₁.convexOn.2 hx.1 hy.1 ha hb hab
    have hconv₂ : ConvexOn ℝ (dom₁ ∩ dom₂) g₂ := by
      refine ⟨h₁.convexOn.1.inter h₂.convexOn.1, ?_⟩
      intro x hx y hy a b ha hb hab
      exact h₂.convexOn.2 hx.2 hy.2 ha hb hab
    simpa using hconv₁.add hconv₂
  · intro x hx u
    have hcont₁x : ContDiffAt ℝ 3 g₁ x := by
      exact h₁.contDiffOn.contDiffAt (h₁.isOpen_domain.mem_nhds hx.1)
    have hcont₂x : ContDiffAt ℝ 3 g₂ x := by
      exact h₂.contDiffOn.contDiffAt (h₂.isOpen_domain.mem_nhds hx.2)
    have hline3 : ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0 := by
      simpa using (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const) :
        ContDiffAt ℝ 3 (fun a : ℝ ↦ x + a • u) 0)
    have hslice₁ : ContDiffAt ℝ 3 (directionalSlice g₁ x u) 0 := by
      -- Restrict the ambient `C³` regularity of `g₁` to the affine line through `x`.
      have hcont_line : ContDiffAt ℝ 3 g₁ ((fun a : ℝ ↦ x + a • u) 0) := by
        simpa using hcont₁x
      simpa [directionalSlice] using hcont_line.comp 0 hline3
    have hslice₂ : ContDiffAt ℝ 3 (directionalSlice g₂ x u) 0 := by
      -- The same line restriction gives the univariate `C³` regularity for `g₂`.
      have hcont_line : ContDiffAt ℝ 3 g₂ ((fun a : ℝ ↦ x + a • u) 0) := by
        simpa using hcont₂x
      simpa [directionalSlice] using hcont_line.comp 0 hline3
    have hthird :
        thirdDirectionalDerivative (g₁ + g₂) x u =
          thirdDirectionalDerivative g₁ x u + thirdDirectionalDerivative g₂ x u := by
      -- The cubic directional derivative is additive because the slice is additive.
      rw [thirdDirectionalDerivative]
      have hs :
          directionalSlice (g₁ + g₂) x u =
            directionalSlice g₁ x u + directionalSlice g₂ x u := by
        funext t
        simp [directionalSlice]
      rw [hs, iteratedDeriv_add hslice₁ hslice₂]
      simp [thirdDirectionalDerivative]
    have hquad₁ : 0 ≤ inner ℝ u (hessian g₁ x u) := h₁.hessian_posSemidef hx.1 u
    have hquad₂ : 0 ≤ inner ℝ u (hessian g₂ x u) := h₂.hessian_posSemidef hx.2 u
    have hhess :
        hessian (g₁ + g₂) x = hessian g₁ x + hessian g₂ x := by
      exact hessian_add_at (h₁.contDiffOn.of_le (by norm_num)) h₁.isOpen_domain hx.1
        (h₂.contDiffOn.of_le (by norm_num)) h₂.isOpen_domain hx.2
    have hquad_sum : 0 ≤ inner ℝ u (hessian (g₁ + g₂) x u) := by
      rw [hhess, ContinuousLinearMap.add_apply, inner_add_right]
      linarith
    have hnorm_sq :
        ‖u‖[g₁ + g₂; x] ^ (2 : ℕ) =
          ‖u‖[g₁; x] ^ (2 : ℕ) + ‖u‖[g₂; x] ^ (2 : ℕ) := by
      -- Rewrite the Hessian quadratic form of the sum and then square the local norms.
      calc
        ‖u‖[g₁ + g₂; x] ^ (2 : ℕ) = inner ℝ u (hessian (g₁ + g₂) x u) := by
          exact sq_hessianLocalNorm_eq_inner_of_nonneg hquad_sum
        _ = inner ℝ u (hessian g₁ x u) + inner ℝ u (hessian g₂ x u) := by
          rw [hhess, ContinuousLinearMap.add_apply, inner_add_right]
        _ = ‖u‖[g₁; x] ^ (2 : ℕ) + ‖u‖[g₂; x] ^ (2 : ℕ) := by
          rw [← sq_hessianLocalNorm_eq_inner_of_nonneg hquad₁,
            ← sq_hessianLocalNorm_eq_inner_of_nonneg hquad₂]
    have hnorm₁_nonneg : 0 ≤ ‖u‖[g₁; x] := hessianLocalNorm_nonneg g₁ x u
    have hnorm₂_nonneg : 0 ≤ ‖u‖[g₂; x] := hessianLocalNorm_nonneg g₂ x u
    have hnorm_sum_nonneg : 0 ≤ ‖u‖[g₁ + g₂; x] := hessianLocalNorm_nonneg (g₁ + g₂) x u
    have hM₁_le : (M₁ : ℝ) ≤ ((max M₁ M₂ : NNReal) : ℝ) := by
      exact_mod_cast le_max_left M₁ M₂
    have hM₂_le : (M₂ : ℝ) ≤ ((max M₁ M₂ : NNReal) : ℝ) := by
      exact_mod_cast le_max_right M₁ M₂
    have hbound₁ :
        |thirdDirectionalDerivative g₁ x u| ≤
          2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₁; x] ^ (3 : ℕ) := by
      have hpow : 0 ≤ ‖u‖[g₁; x] ^ (3 : ℕ) := by
        exact pow_nonneg hnorm₁_nonneg _
      calc
        |thirdDirectionalDerivative g₁ x u| ≤
            2 * (M₁ : ℝ) * ‖u‖[g₁; x] ^ (3 : ℕ) :=
          h₁.third_deriv_bound hx.1 u
        _ ≤ 2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₁; x] ^ (3 : ℕ) := by
          nlinarith
    have hbound₂ :
        |thirdDirectionalDerivative g₂ x u| ≤
          2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₂; x] ^ (3 : ℕ) := by
      have hpow : 0 ≤ ‖u‖[g₂; x] ^ (3 : ℕ) := by
        exact pow_nonneg hnorm₂_nonneg _
      calc
        |thirdDirectionalDerivative g₂ x u| ≤
            2 * (M₂ : ℝ) * ‖u‖[g₂; x] ^ (3 : ℕ) :=
          h₂.third_deriv_bound hx.2 u
        _ ≤ 2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₂; x] ^ (3 : ℕ) := by
          nlinarith
    -- Combine the additive cubic bound with the quadratic-form identity for the Hessian local norm.
    calc
      |thirdDirectionalDerivative (g₁ + g₂) x u|
          ≤ |thirdDirectionalDerivative g₁ x u| + |thirdDirectionalDerivative g₂ x u| := by
            simpa [hthird] using
              (abs_add_le (thirdDirectionalDerivative g₁ x u) (thirdDirectionalDerivative g₂ x u))
      _ ≤ 2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₁; x] ^ (3 : ℕ) +
            2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₂; x] ^ (3 : ℕ) := by
          exact add_le_add hbound₁ hbound₂
      _ = 2 * ((max M₁ M₂ : NNReal) : ℝ) *
            (‖u‖[g₁; x] ^ (3 : ℕ) + ‖u‖[g₂; x] ^ (3 : ℕ)) := by
          ring
      _ ≤ 2 * ((max M₁ M₂ : NNReal) : ℝ) *
            ((‖u‖[g₁; x] ^ (2 : ℕ) + ‖u‖[g₂; x] ^ (2 : ℕ)) *
              Real.sqrt (‖u‖[g₁; x] ^ (2 : ℕ) + ‖u‖[g₂; x] ^ (2 : ℕ))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact pow_three_sum_le_hypot_cube hnorm₁_nonneg hnorm₂_nonneg
          · positivity
      _ = 2 * ((max M₁ M₂ : NNReal) : ℝ) *
            (‖u‖[g₁ + g₂; x] ^ (2 : ℕ) * ‖u‖[g₁ + g₂; x]) := by
          rw [← hnorm_sq]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_sum_nonneg]
      _ = 2 * ((max M₁ M₂ : NNReal) : ℝ) * ‖u‖[g₁ + g₂; x] ^ (3 : ℕ) := by
          simp [pow_succ, mul_assoc]

/-- Theorem 5.1.1: if `f₁` and `f₂` are self-concordant on `dom₁` and `dom₂` with constants
`M₁` and `M₂`, then for positive weights `α` and `β` the weighted sum
`(α : ℝ) • f₁ + (β : ℝ) • f₂` is self-concordant on the intersection domain `dom₁ ∩ dom₂` with
self-concordance constant `max (M₁ / √α) (M₂ / √β)`. -/
theorem weightedSum
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {α β : NNRealˣ} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂)
      (max (M₁ / NNReal.sqrt α) (M₂ / NNReal.sqrt β))
      ((α : ℝ) • f₁ + (β : ℝ) • f₂) := by
  -- Route correction: the public `add` theorem is defined below as a specialization of this
  -- weighted theorem, so the proof must first build the private additive closure helper.
  have h₁scaled :
      IsSelfConcordantOnWith dom₁ (M₁ / NNReal.sqrt α) ((α : ℝ) • f₁) :=
    pos_smul_with_div_sqrt h₁ α
  have h₂scaled :
      IsSelfConcordantOnWith dom₂ (M₂ / NNReal.sqrt β) ((β : ℝ) • f₂) :=
    pos_smul_with_div_sqrt h₂ β
  -- After rescaling each summand, the weighted theorem is just the unweighted additive closure.
  simpa using add_inter_max h₁scaled h₂scaled

-- Proof sketch: specialize `weightedSum` to `α = β = 1`, then simplify the weights, the square
-- roots, and the resulting self-concordance constants.
/-- The owner-level additive specialization of Theorem 5.1.1: if `f₁` and `f₂` are
self-concordant on `dom₁` and `dom₂` with constants `M₁` and `M₂`, then their pointwise sum is
self-concordant on the intersection domain `dom₁ ∩ dom₂` with constant `max M₁ M₂`. -/
theorem add
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂) (max M₁ M₂) (f₁ + f₂) := by
  have hsum :
      IsSelfConcordantOnWith (dom₁ ∩ dom₂)
        (max (M₁ / NNReal.sqrt (1 : NNRealˣ)) (M₂ / NNReal.sqrt (1 : NNRealˣ)))
        (((1 : NNRealˣ) : ℝ) • f₁ + ((1 : NNRealˣ) : ℝ) • f₂) :=
    h₁.weightedSum h₂
  simpa using hsum

end IsSelfConcordantOnWith

end

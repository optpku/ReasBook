/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Classical

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [BorelSpace H]

/-- The extended-real integral functional induced by a pointwise `]-∞,+∞]`-valued integrand on an
`L²` space, with value `⊤` outside the a.e.-finite integrable locus. -/
noncomputable def pointwiseIntegralFunctional (φ : H → Set.Ioi (⊥ : EReal))
    (x : Ω →₂[μ] H) : EReal :=
  if Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ then
    ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal)
  else
    ⊤

/-- The domain of the extended-real integral functional, defined as the set of `L²` fields where
its value is finite above. -/
def pointwiseIntegralFunctionalDomain (φ : H → Set.Ioi (⊥ : EReal)) : Set (Ω →₂[μ] H) :=
  {x | pointwiseIntegralFunctional φ x < ⊤}

-- Proof sketch: split on whether the defining integrability-and-finiteness condition holds. In the
-- integrable branch the value is a real number viewed in `EReal`, while in the fallback branch the
-- value is `⊤`; neither branch can equal `⊥`.
/-- Proposition 8.24 (1): the integral functional defined from `φ` is well defined as an
`]-∞,+∞]`-valued map on `L²`, in the sense that it never takes the value `-∞`. -/
theorem pointwiseIntegralFunctional_ne_bot (φ : H → Set.Ioi (⊥ : EReal))
    (x : Ω →₂[μ] H) :
    pointwiseIntegralFunctional φ x ≠ ⊥ := by
  -- Split along the definition: the integral branch is a real coercion, and the fallback branch is `⊤`.
  by_cases h :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤
  · simp [pointwiseIntegralFunctional, h]
  · simp [pointwiseIntegralFunctional, h]

-- Proof sketch: unfold `pointwiseIntegralFunctionalDomain` and the definition of
-- `pointwiseIntegralFunctional`. The only way the value is strictly below `⊤` is when the
-- integrability-and-a.e.-finiteness condition selecting the integral branch holds.
/-- Proposition 8.24 (2): the domain of the integral functional consists exactly of those `L²`
fields whose pointwise composition with `φ` is integrable after `EReal.toReal` and is finite
`μ`-almost everywhere. -/
theorem pointwiseIntegralFunctionalDomain_eq
    (φ : H → Set.Ioi (⊥ : EReal)) :
    (pointwiseIntegralFunctionalDomain φ : Set (Ω →₂[μ] H)) =
      {x : Ω →₂[μ] H | Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤} := by
  ext x
  -- The strict finiteness test is exactly the branch condition selecting the integral value.
  by_cases h :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤
  · simp [pointwiseIntegralFunctionalDomain, pointwiseIntegralFunctional, h]
  · simp [pointwiseIntegralFunctionalDomain, pointwiseIntegralFunctional, h]

/-- Helper for Proposition 8.24: the real-valued integrand obtained by composing `φ` with an
`L²` field is almost everywhere strongly measurable. -/
lemma pointwise_integrand_aestronglyMeasurable
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ_meas : Measurable φ)
    (x : Ω →₂[μ] H) :
    AEStronglyMeasurable (fun ω ↦ EReal.toReal (φ (x ω))) μ := by
  -- Compose the measurable subtype-valued map with the `L²` field, then pass to `EReal.toReal`.
  have hφx : AEMeasurable (fun ω ↦ (φ (x ω) : EReal)) μ := by
    exact measurable_subtype_coe.comp_aemeasurable <|
      hφ_meas.comp_aemeasurable (Lp.aestronglyMeasurable x).aemeasurable
  exact hφx.ereal_toReal.aestronglyMeasurable

/-- Helper for Proposition 8.24: evaluating an `L²` convex combination agrees almost everywhere
with the pointwise convex combination. -/
lemma convex_combo_apply_ae
    {x y : Ω →₂[μ] H} {α : ℝ} :
    ∀ᵐ ω ∂μ, (α • x + (1 - α) • y) ω = α • x ω + (1 - α) • y ω := by
  -- The `Lp` addition and scalar actions are represented pointwise almost everywhere.
  filter_upwards [Lp.coeFn_add (α • x) ((1 - α) • y), Lp.coeFn_smul α x, Lp.coeFn_smul (1 - α) y]
    with ω hadd hsx hsy
  calc
    (α • x + (1 - α) • y) ω = (((α • x : Ω →₂[μ] H) : Ω → H) + (((1 - α) • y : Ω →₂[μ] H) : Ω → H)) ω :=
      hadd
    _ = (((α • x : Ω →₂[μ] H) : Ω → H) ω) + ((((1 - α) • y : Ω →₂[μ] H) : Ω → H) ω) := rfl
    _ = α • x ω + (1 - α) • y ω := by
      simpa [Pi.smul_apply] using congrArg₂ HAdd.hAdd hsx hsy

/-- Helper for Proposition 8.24: under a.e. finiteness of the endpoint integrands, the convex
combination integrand is also a.e. finite. -/
lemma convex_combo_finite_ae
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ_convex : ∀ ⦃u v : H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (φ (α • u + (1 - α) • v) : EReal) ≤
        (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal))
    {x y : Ω →₂[μ] H} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hx_fin : ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤)
    (hy_fin : ∀ᵐ ω ∂μ, (φ (y ω) : EReal) < ⊤) :
    ∀ᵐ ω ∂μ, (φ ((α • x + (1 - α) • y) ω) : EReal) < ⊤ := by
  -- Pointwise convexity places the middle value below a finite convex combination.
  filter_upwards [hx_fin, hy_fin, convex_combo_apply_ae (x := x) (y := y) (α := α)]
    with ω hxω hyω hxyω
  have hx_ne_top : (φ (x ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hxω
  have hy_ne_top : (φ (y ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hyω
  have hconv :
      (φ ((α • x + (1 - α) • y) ω) : EReal) ≤
        (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) := by
    calc
      (φ ((α • x + (1 - α) • y) ω) : EReal) =
          (φ (α • x ω + (1 - α) • y ω) : EReal) := by rw [hxyω]
      _ ≤ (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) :=
          hφ_convex hα0 hα1
  have hrhs_ne_top :
      (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) ≠ ⊤ := by
    let xv : ℝ := EReal.toReal (φ (x ω))
    let yv : ℝ := EReal.toReal (φ (y ω))
    have hx_eq : ((xv : ℝ) : EReal) = (φ (x ω) : EReal) := by
      dsimp [xv]
      exact EReal.coe_toReal hx_ne_top (ne_of_gt (show (⊥ : EReal) < (φ (x ω) : EReal) from (φ (x ω)).2))
    have hy_eq : ((yv : ℝ) : EReal) = (φ (y ω) : EReal) := by
      dsimp [yv]
      exact EReal.coe_toReal hy_ne_top (ne_of_gt (show (⊥ : EReal) < (φ (y ω) : EReal) from (φ (y ω)).2))
    have hexpr :
        (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) =
          (((α * xv + (1 - α) * yv : ℝ)) : EReal) := by
      rw [← hx_eq, ← hy_eq]
      norm_num
    rw [hexpr]
    exact EReal.coe_ne_top _
  exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top hrhs_ne_top hconv)

/-- Helper for Proposition 8.24: the pointwise convexity inequality for `φ` becomes an a.e.
real-valued inequality on the finite branch. -/
lemma toReal_convex_bound_ae
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ_convex : ∀ ⦃u v : H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (φ (α • u + (1 - α) • v) : EReal) ≤
        (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal))
    {x y : Ω →₂[μ] H} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hx_fin : ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤)
    (hy_fin : ∀ᵐ ω ∂μ, (φ (y ω) : EReal) < ⊤) :
    ∀ᵐ ω ∂μ,
      EReal.toReal (φ ((α • x + (1 - α) • y) ω)) ≤
        α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω)) := by
  -- Route correction: first prove a.e. finiteness of the convex-combination branch, then lift all
  -- three extended-real values to `ℝ` and read the inequality there.
  have hz_fin :
      ∀ᵐ ω ∂μ, (φ ((α • x + (1 - α) • y) ω) : EReal) < ⊤ :=
    convex_combo_finite_ae φ hφ_convex hα0 hα1 hx_fin hy_fin
  filter_upwards [hx_fin, hy_fin, hz_fin, convex_combo_apply_ae (x := x) (y := y) (α := α)]
    with ω hxω hyω hzω hxyω
  have hx_ne_top : (φ (x ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hxω
  have hy_ne_top : (φ (y ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hyω
  have hz_ne_top :
      (φ ((α • x + (1 - α) • y) ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hzω
  have hconv :
      (φ ((α • x + (1 - α) • y) ω) : EReal) ≤
        (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) := by
    calc
      (φ ((α • x + (1 - α) • y) ω) : EReal) =
          (φ (α • x ω + (1 - α) • y ω) : EReal) := by rw [hxyω]
      _ ≤ (α : EReal) * (φ (x ω) : EReal) + (1 - α : EReal) * (φ (y ω) : EReal) :=
          hφ_convex hα0 hα1
  let xv : ℝ := EReal.toReal (φ (x ω))
  let yv : ℝ := EReal.toReal (φ (y ω))
  let zv : ℝ := EReal.toReal (φ ((α • x + (1 - α) • y) ω))
  have hx_eq : ((xv : ℝ) : EReal) = (φ (x ω) : EReal) := by
    dsimp [xv]
    exact EReal.coe_toReal hx_ne_top (ne_of_gt (show (⊥ : EReal) < (φ (x ω) : EReal) from (φ (x ω)).2))
  have hy_eq : ((yv : ℝ) : EReal) = (φ (y ω) : EReal) := by
    dsimp [yv]
    exact EReal.coe_toReal hy_ne_top (ne_of_gt (show (⊥ : EReal) < (φ (y ω) : EReal) from (φ (y ω)).2))
  have hz_eq : ((zv : ℝ) : EReal) = (φ ((α • x + (1 - α) • y) ω) : EReal) := by
    dsimp [zv]
    exact EReal.coe_toReal hz_ne_top (ne_of_gt (show (⊥ : EReal) < (φ ((α • x + (1 - α) • y) ω) : EReal) from
      (φ ((α • x + (1 - α) • y) ω)).2))
  -- After the lifts, the convexity statement is an inequality between ordinary real numbers.
  have hconv' : zv ≤ α * xv + (1 - α) * yv := by
    have hconvEReal :
        ((zv : ℝ) : EReal) ≤
          (α : EReal) * ((xv : ℝ) : EReal) + (1 - α : EReal) * ((yv : ℝ) : EReal) := by
      rw [hz_eq, hx_eq, hy_eq]
      exact hconv
    have hconvEReal' :
        ((zv : ℝ) : EReal) ≤ (((α * xv + (1 - α) * yv : ℝ)) : EReal) := by
      simpa using hconvEReal
    exact_mod_cast hconvEReal'
  simpa using hconv'

/-- Helper for Proposition 8.24: in the finite branch, the convex-combination integrand satisfies
the same branch condition as the endpoints. -/
lemma convex_combo_branch_condition
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ_meas : Measurable φ)
    (hφ_convex : ∀ ⦃u v : H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (φ (α • u + (1 - α) • v) : EReal) ≤
        (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal))
    (hφ_lower : ∀ x : Ω →₂[μ] H, ∃ θ : Ω → ℝ,
      Integrable θ μ ∧ ∀ᵐ ω ∂μ, (θ ω : EReal) ≤ φ (x ω))
    {x y : Ω →₂[μ] H} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hx : Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤)
    (hy : Integrable (fun ω ↦ EReal.toReal (φ (y ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (y ω) : EReal) < ⊤) :
    let z := α • x + (1 - α) • y
    Integrable (fun ω ↦ EReal.toReal (φ (z ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (z ω) : EReal) < ⊤ := by
  let z : Ω →₂[μ] H := α • x + (1 - α) • y
  -- The lower bound comes from the hypothesis, while convexity supplies an integrable upper bound.
  rcases hφ_lower z with ⟨θ, hθ_int, hθ_le⟩
  have hz_fin :
      ∀ᵐ ω ∂μ, (φ (z ω) : EReal) < ⊤ :=
    convex_combo_finite_ae φ hφ_convex hα0 hα1 hx.2 hy.2
  have hupper_ae :
      ∀ᵐ ω ∂μ,
        EReal.toReal (φ (z ω)) ≤
          α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω)) :=
    toReal_convex_bound_ae φ hφ_convex hα0 hα1 hx.2 hy.2
  have hθ_real_le :
      ∀ᵐ ω ∂μ, θ ω ≤ EReal.toReal (φ (z ω)) := by
    -- Convert the lower `EReal` bound back to a real inequality once finiteness is known.
    filter_upwards [hθ_le, hz_fin] with ω hθω hzω
    have hz_ne_top : (φ (z ω) : EReal) ≠ ⊤ := lt_top_iff_ne_top.mp hzω
    simpa using EReal.toReal_le_toReal hθω (EReal.coe_ne_bot _) hz_ne_top
  have hupper_int :
      Integrable
        (fun ω ↦ α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω))) μ := by
    exact (hx.1.const_mul α).add (hy.1.const_mul (1 - α))
  have hz_int :
      Integrable (fun ω ↦ EReal.toReal (φ (z ω))) μ := by
    -- The integrand is squeezed between two integrable real-valued functions.
    refine integrable_of_le_of_le (pointwise_integrand_aestronglyMeasurable φ hφ_meas z)
      hθ_real_le hupper_ae hθ_int hupper_int
  exact ⟨hz_int, hz_fin⟩

/-- Helper for Proposition 8.24: after all three points lie in the integral branch, integrating the
pointwise convexity estimate yields the global convexity estimate. -/
lemma integral_convex_bound
    (φ : H → Set.Ioi (⊥ : EReal))
    {x y z : Ω →₂[μ] H} {α : ℝ}
    (hx : Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤)
    (hy : Integrable (fun ω ↦ EReal.toReal (φ (y ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (y ω) : EReal) < ⊤)
    (hz : Integrable (fun ω ↦ EReal.toReal (φ (z ω))) μ ∧
      ∀ᵐ ω ∂μ, (φ (z ω) : EReal) < ⊤)
    (hbound :
      ∀ᵐ ω ∂μ,
        EReal.toReal (φ (z ω)) ≤
          α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω))) :
    ((∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) : EReal) ≤
      (α : EReal) * ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) +
        (1 - α : EReal) * ((∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : EReal) := by
  -- First integrate the real-valued pointwise estimate.
  have hreal :
      (∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) ≤
        α * (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
          (1 - α) * (∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) := by
    calc
      (∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) ≤
          ∫ ω, (α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω))) ∂μ := by
            exact integral_mono_ae hz.1 ((hx.1.const_mul α).add (hy.1.const_mul (1 - α))) hbound
      _ = (∫ ω, α * EReal.toReal (φ (x ω)) ∂μ : ℝ) +
          (∫ ω, (1 - α) * EReal.toReal (φ (y ω)) ∂μ : ℝ) := by
            rw [integral_add]
            · exact (hx.1.const_mul α)
            · exact (hy.1.const_mul (1 - α))
      _ = α * (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
          (1 - α) * (∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) := by
            rw [integral_const_mul, integral_const_mul]
  -- Then view the resulting real inequality inside `EReal`.
  have hEReal :
      ((∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) : EReal) ≤
        (((α * (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
          (1 - α) * (∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : ℝ)) : EReal) := by
    exact_mod_cast hreal
  have hEq :
      (((α * (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) +
        (1 - α) * (∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : ℝ)) : EReal) =
        (α : EReal) * ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) +
          (1 - α : EReal) * ((∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : EReal) := by
    norm_num
  exact hEReal.trans_eq hEq

-- Proof sketch: use measurability of `φ ∘ x` to make the integral branch meaningful, apply the
-- pointwise convexity inequality coming from `hφ_convex`, and then integrate the resulting
-- inequality using the lower integrable bound supplied by `hφ_lower` to rule out the `-∞` case.
/-- Proposition 8.24 (3): if `φ` is measurable, convex, and admits an integrable lower bound along
every `L²` field, then the induced integral functional is convex on the whole `L²` space. -/
theorem pointwiseIntegralFunctional_convex
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ_meas : Measurable φ)
    (hφ_convex : ∀ ⦃u v : H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (φ (α • u + (1 - α) • v) : EReal) ≤
        (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal))
    (hφ_lower : ∀ x : Ω →₂[μ] H, ∃ θ : Ω → ℝ,
      Integrable θ μ ∧ ∀ᵐ ω ∂μ, (θ ω : EReal) ≤ φ (x ω)) :
    ∀ ⦃x y : Ω →₂[μ] H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      pointwiseIntegralFunctional φ (α • x + (1 - α) • y) ≤
        (α : EReal) * pointwiseIntegralFunctional φ x +
          (1 - α : EReal) * pointwiseIntegralFunctional φ y := by
  intro x y α hα0 hα1
  by_cases hx :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤
  · by_cases hy :
        Integrable (fun ω ↦ EReal.toReal (φ (y ω))) μ ∧
          ∀ᵐ ω ∂μ, (φ (y ω) : EReal) < ⊤
    · -- In the genuine integral branch, prove the convex estimate by integrating the pointwise bound.
      let z : Ω →₂[μ] H := α • x + (1 - α) • y
      have hz :
          Integrable (fun ω ↦ EReal.toReal (φ (z ω))) μ ∧
            ∀ᵐ ω ∂μ, (φ (z ω) : EReal) < ⊤ := by
        simpa [z] using
          convex_combo_branch_condition φ hφ_meas hφ_convex hφ_lower hα0 hα1 hx hy
      have hbound :
          ∀ᵐ ω ∂μ,
            EReal.toReal (φ (z ω)) ≤
              α * EReal.toReal (φ (x ω)) + (1 - α) * EReal.toReal (φ (y ω)) :=
        by
          simpa [z] using toReal_convex_bound_ae φ hφ_convex hα0 hα1 hx.2 hy.2
      have hmain :
          ((∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) : EReal) ≤
            (α : EReal) * ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) +
              (1 - α : EReal) * ((∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : EReal) :=
        integral_convex_bound φ (z := z) hx hy hz hbound
      have hz_val :
          pointwiseIntegralFunctional φ z =
            ((∫ ω, EReal.toReal (φ (z ω)) ∂μ : ℝ) : EReal) := by
        simp [pointwiseIntegralFunctional, hz]
      have hx_val :
          pointwiseIntegralFunctional φ x =
            ((∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ) : EReal) := by
        simp [pointwiseIntegralFunctional, hx]
      have hy_val :
          pointwiseIntegralFunctional φ y =
            ((∫ ω, EReal.toReal (φ (y ω)) ∂μ : ℝ) : EReal) := by
        simp [pointwiseIntegralFunctional, hy]
      have hcombo :
          pointwiseIntegralFunctional φ z ≤
            (α : EReal) * pointwiseIntegralFunctional φ x +
              (1 - α : EReal) * pointwiseIntegralFunctional φ y := by
        rw [hz_val, hx_val, hy_val]
        exact hmain
      simpa [z] using hcombo
    · -- If `y` is outside the integral branch, the right-hand side is already `⊤`.
      have hy_top : pointwiseIntegralFunctional φ y = ⊤ := by
        simp [pointwiseIntegralFunctional, hy]
      have hmul_top :
          (1 - α : EReal) * pointwiseIntegralFunctional φ y = ⊤ := by
        rw [hy_top]
        exact EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr hα1)
      have hleft_ne_bot :
          (α : EReal) * pointwiseIntegralFunctional φ x ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (pointwiseIntegralFunctional_ne_bot φ x),
          Or.inl (EReal.coe_ne_top _), Or.inl ?_⟩
        exact le_of_lt (by exact_mod_cast hα0)
      calc
        pointwiseIntegralFunctional φ (α • x + (1 - α) • y) ≤ ⊤ := le_top
        _ = (α : EReal) * pointwiseIntegralFunctional φ x +
              (1 - α : EReal) * pointwiseIntegralFunctional φ y := by
            have hrhs_top :
                (α : EReal) * pointwiseIntegralFunctional φ x +
                  (1 - α : EReal) * pointwiseIntegralFunctional φ y = ⊤ := by
              rw [hmul_top]
              exact EReal.add_top_of_ne_bot hleft_ne_bot
            exact hrhs_top.symm
  · -- If `x` is outside the integral branch, the right-hand side is already `⊤`.
    have hx_top : pointwiseIntegralFunctional φ x = ⊤ := by
      simp [pointwiseIntegralFunctional, hx]
    have hmul_top :
        (α : EReal) * pointwiseIntegralFunctional φ x = ⊤ := by
      rw [hx_top]
      exact EReal.mul_top_of_pos (by exact_mod_cast hα0)
    have hright_ne_bot :
        (1 - α : EReal) * pointwiseIntegralFunctional φ y ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (pointwiseIntegralFunctional_ne_bot φ y),
        Or.inl (EReal.coe_ne_top _), Or.inl ?_⟩
      exact le_of_lt (by exact_mod_cast sub_pos.mpr hα1)
    calc
      pointwiseIntegralFunctional φ (α • x + (1 - α) • y) ≤ ⊤ := le_top
      _ = (α : EReal) * pointwiseIntegralFunctional φ x +
            (1 - α : EReal) * pointwiseIntegralFunctional φ y := by
          have hrhs_top :
              (α : EReal) * pointwiseIntegralFunctional φ x +
                (1 - α : EReal) * pointwiseIntegralFunctional φ y = ⊤ := by
            rw [hmul_top]
            exact EReal.top_add_of_ne_bot hright_ne_bot
          exact hrhs_top.symm

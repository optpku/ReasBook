/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_completeSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: Proposition 8.24 shows that `pointwiseIntegralFunctional φ x` is never `⊥`.
-- Rewrite membership in `Set.Ioi (⊥ : EReal)` as strict inequality above `⊥`.
/-- The Chapter 8 pointwise integral functional takes values in `]-∞,+∞]`. -/
theorem pointwiseIntegralFunctional_mem_Ioi_bot (φ : H → Set.Ioi (⊥ : EReal))
    (x : Ω →₂[μ] H) :
    pointwiseIntegralFunctional φ x ∈ Set.Ioi (⊥ : EReal) := by
  -- Proposition 8.24 already rules out the value `⊥`, so the order on `EReal` forces strict
  -- inequality above `⊥`.
  exact lt_of_le_of_ne bot_le (Ne.symm (pointwiseIntegralFunctional_ne_bot φ x))

/-- The `]-∞,+∞]`-valued integral functional on `L²((Ω,\mathcal F,\mu); H)` induced by `φ`. -/
noncomputable def integralFunctional (μ : Measure Ω) (φ : H → Set.Ioi (⊥ : EReal)) :
    (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨pointwiseIntegralFunctional φ x, pointwiseIntegralFunctional_mem_Ioi_bot φ x⟩

-- Proof sketch: unfold `integralFunctional`; it is defined by coercing
-- `pointwiseIntegralFunctional φ x` into `Set.Ioi (⊥ : EReal)`.
/-- Coercing `integralFunctional μ φ x` back to `EReal` recovers the Chapter 8 integral
functional. -/
@[simp] theorem integralFunctional_coe (μ : Measure Ω) (φ : H → Set.Ioi (⊥ : EReal))
    (x : Ω →₂[μ] H) :
    (integralFunctional μ φ x : EReal) = pointwiseIntegralFunctional φ x := by
  -- `integralFunctional` is defined by the subtype constructor around
  -- `pointwiseIntegralFunctional`.
  rfl

/-- Helper for Proposition 9.40: outside the effective domain of an `]-∞,+∞]`-valued function,
the value is necessarily `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {K : Type*} {f : K → Set.Ioi (⊥ : EReal)} {x : K} (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- A finite-above value would put the point back in the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

/-- Helper for Proposition 9.40: a real-height epigraph point has a base point in the effective
domain. -/
private theorem mem_effectiveDomain_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hxξ : (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal))) :
    x ∈ effectiveDomain f := by
  -- Epigraph membership bounds `f x` by a finite real height, so `x` lies in the effective domain.
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (mem_epigraph_iff _ _ _ |>.mp hxξ) (EReal.coe_lt_top _)

/-- Helper for Proposition 9.40: the projection inequality from Proposition 9.18 normalizes to an
affine lower support inequality on the effective domain. -/
private theorem affine_minorant_on_effectiveDomain_of_projection
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal)
    (hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)) :
    let u : H := ((π - ξ)⁻¹) • (x - p)
    ∀ y ∈ effectiveDomain f,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  have hproj_data :
      max (ξ : EReal) (f p : EReal) ≤ (π : EReal) ∧
        ∀ y ∈ effectiveDomain f,
          ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
      hproj
  rcases hproj_data with ⟨hmax, hvar⟩
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point itself belongs to the epigraph.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  have hξ_le_pi : ξ ≤ π := by
    -- The max-majorization from Proposition 9.18 already places `π` above `ξ`.
    have hξ_le_pi' : (ξ : EReal) ≤ (π : EReal) := by
      exact le_trans
        (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _)
        hmax
    exact_mod_cast hξ_le_pi'
  have hfp_top : (f p : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hfp_bot : (f p : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f p : EReal) > ⊥ from (f p).2)
  have hfp_le_pi : (f p : EReal).toReal ≤ π := by
    -- The projection height is a real upper bound for the finite value `f p`.
    have hfp_le_pi' : (f p : EReal) ≤ (π : EReal) :=
      mem_epigraph_iff _ _ _ |>.mp hp_mem_epigraph
    have hcast :
        (((f p : EReal).toReal : ℝ) : EReal) ≤ (π : EReal) := by
      simpa [EReal.coe_toReal hfp_top hfp_bot] using hfp_le_pi'
    exact_mod_cast hcast
  have hξ_lt_pi : ξ < π := by
    -- Equality `π = ξ` would force the projection point back to `x`, contradicting `ξ < f x`.
    by_cases hπξ : π = ξ
    · have hvarx :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπξ, sub_self, mul_zero, add_zero] at hvarx
      have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
        simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
      have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
        nlinarith [hinner_nonneg, hvarx]
      have hxp : x = p := by
        have hsub : x - p = 0 := by
          simpa using inner_self_eq_zero.mp hinner_eq_zero
        exact sub_eq_zero.mp hsub
      have hfp_le_xi : (f p : EReal) ≤ (ξ : EReal) := by
        have hmax_to_xi : max (ξ : EReal) (f p : EReal) ≤ (ξ : EReal) := by
          simpa [hπξ] using hmax
        exact le_trans
          (show (f p : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_right _ _)
          hmax_to_xi
      have hfx_le_xi : (f x : EReal).toReal ≤ ξ := by
        have hfx_top : (f x : EReal) ≠ ⊤ :=
          ne_of_lt (mem_effectiveDomain_iff.mp hx)
        have hfx_bot : (f x : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (f x : EReal) > ⊥ from (f x).2)
        have hfx_le_xi' : (f x : EReal) ≤ (ξ : EReal) := by
          simpa [hxp] using hfp_le_xi
        have hcast :
            (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
          simpa [EReal.coe_toReal hfx_top hfx_bot] using hfx_le_xi'
        exact_mod_cast hcast
      linarith
    · exact lt_of_le_of_ne hξ_le_pi (by
        intro hξπ
        exact hπξ hξπ.symm)
  dsimp
  intro y hy
  have hvar' :
      ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 :=
    hvar y hy
  have hgap_pos : 0 < π - ξ := by
    -- The projection height strictly exceeds the point chosen below the epigraph.
    exact sub_pos.mpr hξ_lt_pi
  have hinner_le :
      ⟪y - p, x - p⟫_ℝ ≤
        ((f y : EReal).toReal - π) * (π - ξ) := by
    -- Rewrite the variational inequality using the positive gap `π - ξ`.
    nlinarith
  have hscaled :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ ≤
        (f y : EReal).toReal - π := by
    -- Divide by the positive gap to isolate the affine slope.
    have hdiv : ⟪y - p, x - p⟫_ℝ / (π - ξ) ≤ (f y : EReal).toReal - π := by
      refine (div_le_iff₀ hgap_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
    simpa [div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hreal :
      ⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal ≤
        (f y : EReal).toReal := by
    -- Replace the intercept `π` by the smaller finite value `(f p).toReal`.
    linarith
  have hfy_top : (f y : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (f y : EReal) > ⊥ from (f y).2)
  have hcast :
      ((⟪y - p, (π - ξ)⁻¹ • (x - p)⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤
        (((f y : EReal).toReal : ℝ) : EReal) := by
    exact_mod_cast hreal
  -- Replace the finite right-hand side by the original `EReal` value of `f y`.
  simpa [EReal.coe_toReal hfy_top hfy_bot] using hcast

/-- Helper for Proposition 9.40: every `Γ₀(H)` integrand admits a global continuous affine
minorant of the form used in the textbook proof. -/
private theorem exists_affine_minorant_of_mem_gammaZero_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ p ∈ effectiveDomain f, ∃ u : H, ∀ y : H,
      ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (f y : EReal) := by
  -- Route correction: instead of importing the later Chapter 9 affine-minorant file, rebuild the
  -- textbook support inequality directly from Proposition 9.18's projection characterization.
  rcases hf.2.nonempty with ⟨x, hx⟩
  let ξ : ℝ := (f x : EReal).toReal - 1
  have hξ : ξ < (f x : EReal).toReal := by
    -- The chosen ordinate sits one unit below the finite value of `f x`.
    dsimp [ξ]
    linarith
  let z : H × ℝ :=
    projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
      (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  let p : H := z.1
  let π : ℝ := z.2
  have hproj :
      (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) := by
    -- The chosen coordinates are exactly the components of the projection point.
    simp [p, π, z]
  have hp_mem_epigraph :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point belongs to the epigraph by construction.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  have hp : p ∈ effectiveDomain f :=
    mem_effectiveDomain_of_mem_real_epigraph hp_mem_epigraph
  let u : H := ((π - ξ)⁻¹) • (x - p)
  refine ⟨p, hp, u, ?_⟩
  intro y
  by_cases hy : y ∈ effectiveDomain f
  · -- On the effective domain, Proposition 9.18 gives the normalized affine support inequality.
    simpa [u] using
      affine_minorant_on_effectiveDomain_of_projection hf hx hξ hproj y hy
  · -- Off the effective domain, the right-hand side is `⊤`, so the lower support bound is trivial.
    simpa [value_eq_top_of_not_mem_effectiveDomain hy] using
      (le_top :
        ((⟪y - p, u⟫_ℝ + (f p : EReal).toReal : ℝ) : EReal) ≤ (⊤ : EReal))

/-- Helper for Proposition 9.40: a `Γ₀` function satisfies the global Jensen inequality, with the
off-domain cases absorbed by the value `⊤`. -/
private theorem convex_ineq_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    {u v : H} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (φ (α • u + (1 - α) • v) : EReal) ≤
      (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal) := by
  by_cases hu : u ∈ effectiveDomain φ
  · by_cases hv : v ∈ effectiveDomain φ
    · -- On the effective domain, the stored `ConvexOn` inequality is exactly the desired estimate.
      exact hφ.2.ineq hu hv hα0 hα1
    · -- If `v` is off-domain, the right-hand side already contains a positive multiple of `⊤`.
      have hv_top : (φ v : EReal) = ⊤ :=
        value_eq_top_of_not_mem_effectiveDomain hv
      have hmul_top :
          (1 - α : EReal) * (φ v : EReal) = ⊤ := by
        rw [hv_top]
        exact EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr hα1)
      have hleft_ne_bot :
          (α : EReal) * (φ u : EReal) ≠ ⊥ := by
        rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (φ u).2.ne', Or.inl (EReal.coe_ne_top _), Or.inl ?_⟩
        exact le_of_lt (by exact_mod_cast hα0)
      calc
        (φ (α • u + (1 - α) • v) : EReal) ≤ ⊤ := le_top
        _ = (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal) := by
          rw [hmul_top]
          exact (EReal.add_top_of_ne_bot hleft_ne_bot).symm
  · -- Symmetrically, if `u` is off-domain then the first term forces the whole right-hand side
    -- to be `⊤`.
    have hu_top : (φ u : EReal) = ⊤ :=
      value_eq_top_of_not_mem_effectiveDomain hu
    have hmul_top :
        (α : EReal) * (φ u : EReal) = ⊤ := by
      rw [hu_top]
      exact EReal.mul_top_of_pos (by exact_mod_cast hα0)
    have hright_ne_bot :
        (1 - α : EReal) * (φ v : EReal) ≠ ⊥ := by
      rw [EReal.mul_ne_bot]
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (φ v).2.ne', Or.inl (EReal.coe_ne_top _), Or.inl ?_⟩
      exact le_of_lt (by exact_mod_cast sub_pos.mpr hα1)
    calc
      (φ (α • u + (1 - α) • v) : EReal) ≤ ⊤ := le_top
      _ = (α : EReal) * (φ u : EReal) + (1 - α : EReal) * (φ v : EReal) := by
        rw [hmul_top]
        exact (EReal.top_add_of_ne_bot hright_ne_bot).symm

/-- Helper for Proposition 9.40: lower semicontinuity of the `EReal` coercion makes the
subtype-valued integrand measurable. -/
private theorem measurable_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) :
    Measurable φ := by
  -- The coercion to `EReal` is measurable, and the subtype map just records the range proof.
  exact hφ.1.measurable.subtype_mk

/-- Helper for Proposition 9.40: the Chapter 8 convexity theorem needs an integrable lower bound
along each `L²` field; finite measure gives one from an affine minorant, while the nonnegative
branch uses the zero function. -/
private theorem integrable_lower_bound_of_finite_or_nonneg
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    ∀ x : Ω →₂[μ] H, ∃ θ : Ω → ℝ,
      Integrable θ μ ∧ ∀ᵐ ω ∂μ, (θ ω : EReal) ≤ φ (x ω) := by
  intro x
  rcases hfinite_or_nonneg with hfinite | ⟨hzero, hnonneg⟩
  · letI : IsFiniteMeasure μ := ⟨hfinite⟩
    rcases exists_affine_minorant_of_mem_gammaZero_local hφ with ⟨p, hp, u, hminorant⟩
    let θ : Ω → ℝ := fun ω ↦ ⟪x ω - p, u⟫_ℝ + (φ p : EReal).toReal
    have hx_int : Integrable (fun ω : Ω ↦ x ω) μ := by
      -- On a finite measure space, every `L²` field is integrable as an `H`-valued map.
      exact
        integrableOn_univ.mp
          (integrableOn_Lp_of_measure_ne_top x fact_one_le_two_ennreal.elim
            (measure_ne_top μ Set.univ))
    have hθ_int : Integrable θ μ := by
      -- The affine lower bound is integrable because it is an inner product against an `L¹` map
      -- plus a constant.
      have hsub_int : Integrable (fun ω : Ω ↦ x ω - p) μ :=
        hx_int.sub (integrable_const p)
      have hinner_int : Integrable (fun ω : Ω ↦ ⟪x ω - p, u⟫_ℝ) μ :=
        hsub_int.inner_const u
      simpa [θ] using hinner_int.add (integrable_const ((φ p : EReal).toReal : ℝ))
    refine ⟨θ, hθ_int, ?_⟩
    -- The affine minorant holds pointwise after evaluating the global support inequality at `x ω`.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [θ] using hminorant (x ω)
  · have hzero_int : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
      simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
    refine ⟨fun _ ↦ 0, hzero_int, ?_⟩
    -- In the nonnegative branch, the zero function is a global lower bound.
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [hzero] using hnonneg (x ω)

/-- Helper for Proposition 9.40: the effective domain of the induced integral functional is
nonempty under either hypothesis of Proposition 9.40. -/
private theorem integralFunctional_effectiveDomain_nonempty_of_finite_or_nonneg
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    Set.Nonempty (effectiveDomain
      (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal))) := by
  rcases hfinite_or_nonneg with hfinite | ⟨hzero, hnonneg⟩
  · letI : IsFiniteMeasure μ := ⟨hfinite⟩
    rcases hφ.2.nonempty with ⟨z, hz⟩
    let x : Ω →₂[μ] H := Lp.const 2 μ z
    refine ⟨x, ?_⟩
    rw [mem_effectiveDomain_iff, integralFunctional_coe μ, pointwiseIntegralFunctional]
    have hx_int : Integrable (fun ω : Ω ↦ EReal.toReal (φ (x ω))) μ := by
      have hconst :
          (fun ω : Ω ↦ EReal.toReal (φ (x ω))) =ᵐ[μ] fun _ : Ω ↦ EReal.toReal (φ z) := by
        filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) z] with ω hω
        simpa [Function.const] using congrArg (fun y : H ↦ EReal.toReal (φ y)) hω
      exact (integrable_const (EReal.toReal (φ z) : ℝ)).congr hconst.symm
    have hx_fin : ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := by
      filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) z] with ω hω
      have hxω : x ω = z := by
        simpa [x, Function.const] using hω
      simpa [hxω] using (mem_effectiveDomain_iff.mp hz)
    have hbranch :
        Integrable (fun ω : Ω ↦ EReal.toReal (φ (x ω))) μ ∧
          ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := ⟨hx_int, hx_fin⟩
    -- The constant field stays inside the integral branch because both the value and the measure
    -- are finite.
    simpa [pointwiseIntegralFunctional, hbranch] using
      (EReal.coe_lt_top (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ))
  · refine ⟨0, ?_⟩
    rw [mem_effectiveDomain_iff, integralFunctional_coe μ]
    have hx_int : Integrable (fun ω : Ω ↦ EReal.toReal (φ ((0 : Ω →₂[μ] H) ω))) μ := by
      have hφ0_real : EReal.toReal (φ 0 : EReal) = 0 := by
        simpa [hzero]
      have hzero_ae :
          (fun ω : Ω ↦ EReal.toReal (φ ((0 : Ω →₂[μ] H) ω))) =ᵐ[μ] fun _ : Ω ↦ (0 : ℝ) := by
        filter_upwards [Lp.coeFn_zero H 2 μ] with ω hω
        have hzero_apply : ((0 : Ω →₂[μ] H) ω) = 0 := by
          simpa using hω
        have hφ_apply : EReal.toReal (φ ((0 : Ω →₂[μ] H) ω) : EReal) = EReal.toReal (φ 0 : EReal) := by
          rw [hzero_apply]
        simpa [hφ0_real] using hφ_apply
      have hzero_int : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
        simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
      exact hzero_int.congr hzero_ae.symm
    have hx_fin : ∀ᵐ ω ∂μ, (φ ((0 : Ω →₂[μ] H) ω) : EReal) < ⊤ := by
      have hφ0_lt_top : (φ 0 : EReal) < ⊤ := by
        simpa [hzero] using (EReal.coe_lt_top (0 : ℝ))
      filter_upwards [Lp.coeFn_zero H 2 μ] with ω hω
      have hzero_apply : ((0 : Ω →₂[μ] H) ω) = 0 := by
        simpa using hω
      have hφ_apply : (φ ((0 : Ω →₂[μ] H) ω) : EReal) = (φ 0 : EReal) := by
        rw [hzero_apply]
      exact hφ_apply ▸ hφ0_lt_top
    have hbranch :
        Integrable (fun ω : Ω ↦ EReal.toReal (φ ((0 : Ω →₂[μ] H) ω))) μ ∧
          ∀ᵐ ω ∂μ, (φ ((0 : Ω →₂[μ] H) ω) : EReal) < ⊤ := ⟨hx_int, hx_fin⟩
    have hzero_integral :
        (∫ ω, EReal.toReal (φ ((0 : Ω →₂[μ] H) ω)) ∂μ : ℝ) = 0 := by
      have hφ0_real : EReal.toReal (φ 0 : EReal) = 0 := by
        simpa [hzero]
      have hzero_ae :
          (fun ω : Ω ↦ EReal.toReal (φ ((0 : Ω →₂[μ] H) ω))) =ᵐ[μ] fun _ : Ω ↦ (0 : ℝ) := by
        filter_upwards [Lp.coeFn_zero H 2 μ] with ω hω
        have hzero_apply : ((0 : Ω →₂[μ] H) ω) = 0 := by
          simpa using hω
        have hφ_apply : EReal.toReal (φ ((0 : Ω →₂[μ] H) ω) : EReal) = EReal.toReal (φ 0 : EReal) := by
          rw [hzero_apply]
        simpa [hφ0_real] using hφ_apply
      rw [integral_congr_ae hzero_ae]
      simp
    have hbranch0 :
        Integrable (fun ω : Ω ↦ EReal.toReal (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)))) μ ∧
          ∀ᵐ ω ∂μ, (φ ((((0 : Ω →₂[μ] H) : Ω → H) ω)) : EReal) < ⊤ := ⟨hx_int, hx_fin⟩
    -- In the nonnegative branch, the zero field gives `f(0) = 0`.
    rw [pointwiseIntegralFunctional, if_pos hbranch0, hzero_integral]
    exact EReal.coe_lt_top (0 : ℝ)

/-- Helper for Proposition 9.40: the projection-based support inequality can be rewritten as the
textbook affine minorant `y ↦ ⟪y,u⟫ + η`. -/
private theorem exists_real_affine_minorant_of_mem_gammaZero_local
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) :
    ∃ u : H, ∃ η : ℝ, ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ (φ y : EReal)) := by
  rcases exists_affine_minorant_of_mem_gammaZero_local hφ with ⟨p, hp, u, hminorant⟩
  let η : ℝ := (φ p : EReal).toReal - ⟪p, u⟫_ℝ
  refine ⟨u, η, ?_⟩
  intro y
  -- Expanding `⟪y - p, u⟫` turns the stored support inequality into the textbook affine form.
  have hrepack : ⟪y - p, u⟫_ℝ + (φ p : EReal).toReal = ⟪y, u⟫_ℝ + η := by
    rw [inner_sub_left]
    dsimp [η]
    ring
  simpa [hrepack] using hminorant y

/-- Helper for Proposition 9.40: norm convergence in `L²` admits an almost-everywhere convergent
subsequence. -/
private theorem ae_convergent_subsequence_of_tendsto_L2
    {xs : ℕ → Ω →₂[μ] H} {x : Ω →₂[μ] H} (hx : Filter.Tendsto xs Filter.atTop (nhds x)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun k ↦ xs (ns k) ω) Filter.atTop (nhds (x ω)) := by
  -- Route correction: isolate the standard `L² -> in measure -> a.e. subsequence` bridge so the
  -- main lower-level-set argument can stay flat.
  have hmeasure :
      TendstoInMeasure μ (fun n ↦ (xs n : Ω → H)) Filter.atTop (x : Ω → H) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hx
  simpa using hmeasure.exists_seq_tendsto_ae

/-- Helper for Proposition 9.40: on the effective domain, subtracting an integrable real lower
bound produces an integrable nonnegative shifted integrand. -/
private theorem shifted_integrand_integrable_nonneg_of_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} {ρ : H → ℝ}
    (hρ_le : ∀ y : H, (((ρ y : ℝ) : EReal) ≤ (φ y : EReal)))
    {x : Ω →₂[μ] H} (hρx_int : Integrable (fun ω ↦ ρ (x ω)) μ)
    (hx : x ∈ effectiveDomain
      (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal))) :
    Integrable (fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω)) μ ∧
      0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω) := by
  have hx_lt : (integralFunctional μ φ x : EReal) < ⊤ :=
    mem_effectiveDomain_iff.mp hx
  have hx_domain : x ∈ pointwiseIntegralFunctionalDomain φ := by
    simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using hx_lt
  rw [pointwiseIntegralFunctionalDomain_eq] at hx_domain
  have hshift_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω) := by
    -- The affine minorant gives `ρ(x ω) ≤ φ(x ω)`; finiteness on the integral branch lets us move
    -- that inequality to `ℝ`.
    filter_upwards [hx_domain.2] with ω hω
    have hreal_le : ρ (x ω) ≤ EReal.toReal (φ (x ω)) := by
      exact EReal.toReal_le_toReal (hρ_le (x ω)) (EReal.coe_ne_bot _)
        (lt_top_iff_ne_top.mp hω)
    exact sub_nonneg.mpr hreal_le
  refine ⟨hx_domain.1.sub hρx_int, hshift_nonneg⟩

/-- Helper for Proposition 9.40: after shifting by a continuous affine minorant, pointwise
lower semicontinuity yields the expected `EReal` liminf inequality along an a.e.-convergent
subsequence. -/
private theorem shifted_ereal_liminf_ae_of_subsequence
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) {ρ : H → ℝ}
    (hρ_cont : Continuous ρ) {x : Ω →₂[μ] H} {xs : ℕ → Ω →₂[μ] H} {ns : ℕ → ℕ}
    (hae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k ↦ xs (ns k) ω) Filter.atTop (nhds (x ω))) :
    ∀ᵐ ω ∂μ,
      ((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))) ≤
        Filter.liminf
          (fun k ↦ (φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal))) Filter.atTop := by
  have hshift_lsc :
      LowerSemicontinuous
        (fun y : H ↦ (φ y : EReal) + (((-ρ y : ℝ) : EReal))) := by
    have hcorr :
        LowerSemicontinuous (fun y : H ↦ (((-ρ y : ℝ) : EReal))) := by
      exact (continuous_coe_real_ereal.comp hρ_cont.neg).lowerSemicontinuous
    exact hφ.1.add' hcorr fun y ↦
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  filter_upwards [hae] with ω hω
  -- The shifted integrand is lower semicontinuous on `H`, so its value at the limit is below the
  -- liminf along the convergent subsequence.
  calc
    ((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))) ≤
        Filter.liminf (fun y : H ↦ (φ y : EReal) + (((-ρ y : ℝ) : EReal))) (nhds (x ω)) := by
          exact (hshift_lsc.lowerSemicontinuousAt (x ω)).le_liminf
    _ ≤
        Filter.liminf
          (fun k ↦ (φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal))) Filter.atTop := by
          simpa [Filter.liminf_comp] using Filter.liminf_le_liminf_of_le hω

/-- Helper for Proposition 9.40: on the a.e.-finite branch, the shifted `EReal` integrand agrees
with the `ENNReal` integrand used in Fatou's lemma. -/
private theorem shifted_toENNReal_eq_ofReal_shifted_toReal
    {φ : H → Set.Ioi (⊥ : EReal)} {ρ : H → ℝ} {y : H}
    (hy_top : (φ y : EReal) ≠ ⊤) :
    (((φ y : EReal) + (((-ρ y : ℝ) : EReal))).toENNReal) =
      ENNReal.ofReal (EReal.toReal (φ y) - ρ y) := by
  have hy_bot : (φ y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (φ y : EReal) from (φ y).2)
  -- Rewriting the finite `EReal` value of `φ y` as a real cast makes the shifted term explicit.
  have hsum_eq :
      (φ y : EReal) + (((-ρ y : ℝ) : EReal)) =
        (((EReal.toReal (φ y) - ρ y : ℝ)) : EReal) := by
    calc
      (φ y : EReal) + (((-ρ y : ℝ) : EReal)) =
          (((EReal.toReal (φ y) : ℝ) : EReal)) + (((-ρ y : ℝ) : EReal)) := by
            rw [EReal.coe_toReal hy_top hy_bot]
      _ = (((EReal.toReal (φ y) - ρ y : ℝ)) : EReal) := by
            simpa [sub_eq_add_neg]
  rw [hsum_eq]
  simpa using EReal.real_coe_toENNReal ((φ y : EReal).toReal - ρ y)

/-- Helper for Proposition 9.40: applying `EReal.toENNReal` to the shifted lower-semicontinuity
estimate gives the Fatou-ready `ENNReal` liminf inequality. -/
private theorem shifted_integrand_liminf_ae_of_subsequence
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H)) {ρ : H → ℝ}
    (hρ_cont : Continuous ρ) {x : Ω →₂[μ] H} {xs : ℕ → Ω →₂[μ] H} {ns : ℕ → ℕ}
    (hae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k ↦ xs (ns k) ω) Filter.atTop (nhds (x ω))) :
    ∀ᵐ ω ∂μ,
      (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal) ≤
        Filter.liminf
          (fun k ↦ (((φ (xs (ns k) ω) : EReal) +
            (((-ρ (xs (ns k) ω) : ℝ) : EReal))).toENNReal)) Filter.atTop := by
  let τ : EReal → ℝ≥0∞ := EReal.toENNReal
  have hτ_mono : Monotone τ := fun _ _ hab ↦ EReal.toENNReal_le_toENNReal hab
  filter_upwards [shifted_ereal_liminf_ae_of_subsequence hφ hρ_cont hae] with ω hω
  -- The monotone continuous map `EReal.toENNReal` transports the liminf identity along the
  -- shifted sequence.
  have hmap :
      τ (Filter.liminf
        (fun k ↦ (φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal)))
        Filter.atTop) =
        Filter.liminf
          (fun k ↦ τ ((φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal))))
          Filter.atTop := by
    simpa [τ, Function.comp] using
      (Monotone.map_liminf_of_continuousAt (F := Filter.atTop) hτ_mono
        (a := fun k ↦ (φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal)))
        EReal.continuous_toENNReal.continuousAt)
  calc
    (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal) ≤
        τ (Filter.liminf
          (fun k ↦ (φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal)))
          Filter.atTop) := by
            exact EReal.toENNReal_le_toENNReal hω
    _ =
        Filter.liminf
          (fun k ↦ (((φ (xs (ns k) ω) : EReal) +
            (((-ρ (xs (ns k) ω) : ℝ) : EReal))).toENNReal)) Filter.atTop := by
              simpa [τ] using hmap

/-- Helper for Proposition 9.40: integrating the affine minorant `y ↦ ⟪y, u⟫ + η` yields the
continuous correction term from the textbook proof. -/
private theorem integral_affine_correction_eq_inner_const_add
    [IsFiniteMeasure μ] {u : H} {η : ℝ} (x : Ω →₂[μ] H) :
    ∫ ω, (⟪x ω, u⟫_ℝ + η) ∂μ =
      ⟪x, Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal := by
  have hx_int : Integrable (fun ω : Ω ↦ x ω) μ := by
    -- On a finite measure space, every `L²` field is integrable as an `H`-valued map.
    exact
      integrableOn_univ.mp
        (integrableOn_Lp_of_measure_ne_top x fact_one_le_two_ennreal.elim
          (measure_ne_top μ Set.univ))
  have hinner :
      ∫ ω, ⟪x ω, u⟫_ℝ ∂μ = ⟪x, Lp.const 2 μ u⟫_ℝ := by
    -- The `L²` inner product with the constant field is the integral of the pointwise inner
    -- products.
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) u] with ω hω
    have hconst : (Lp.const 2 μ u : Ω →₂[μ] H) ω = u := by
      simpa [Function.const] using hω
    have hinnerω :
        ⟪x ω, (Lp.const 2 μ u : Ω →₂[μ] H) ω⟫_ℝ = ⟪x ω, u⟫_ℝ := by
      exact congrArg (fun v : H ↦ ⟪x ω, v⟫_ℝ) hconst
    simpa using hinnerω.symm
  calc
    ∫ ω, (⟪x ω, u⟫_ℝ + η) ∂μ =
        ∫ ω, ⟪x ω, u⟫_ℝ ∂μ + ∫ ω, η ∂μ := by
          rw [integral_add (hx_int.inner_const u) (integrable_const η)]
    _ = ⟪x, Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal := by
      rw [hinner, integral_const]
      simpa [Measure.real, smul_eq_mul, mul_comm]

/-- Helper for Proposition 9.40: on the effective domain, the integral functional splits into the
nonnegative shifted integral plus the affine correction term. -/
private theorem integralFunctional_eq_shifted_integral_add_correction
    {φ : H → Set.Ioi (⊥ : EReal)} {ρ : H → ℝ}
    (hρ_le : ∀ y : H, (((ρ y : ℝ) : EReal) ≤ (φ y : EReal)))
    {x : Ω →₂[μ] H}
    (hρx_int : Integrable (fun ω ↦ ρ (x ω)) μ)
    (hx : x ∈ effectiveDomain
      (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal))) :
    (integralFunctional μ φ x : EReal) =
      (((∫ ω, (EReal.toReal (φ (x ω)) - ρ (x ω)) ∂μ) +
        ∫ ω, ρ (x ω) ∂μ : ℝ) : EReal) := by
  have hx_lt : (integralFunctional μ φ x : EReal) < ⊤ :=
    mem_effectiveDomain_iff.mp hx
  have hx_domain : x ∈ pointwiseIntegralFunctionalDomain φ := by
    simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using hx_lt
  rw [pointwiseIntegralFunctionalDomain_eq] at hx_domain
  have hshift_int :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω)) μ :=
    (shifted_integrand_integrable_nonneg_of_effectiveDomain hρ_le hρx_int hx).1
  have hsplit :
      ∫ ω, EReal.toReal (φ (x ω)) ∂μ =
        ∫ ω, (EReal.toReal (φ (x ω)) - ρ (x ω)) ∂μ + ∫ ω, ρ (x ω) ∂μ := by
    -- Integrate the pointwise identity `φ = (φ - ρ) + ρ`.
    rw [← integral_add hshift_int hρx_int]
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun ω ↦ by ring
  have hx_branch :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := by
    simpa using hx_domain
  rw [integralFunctional_coe μ, pointwiseIntegralFunctional]
  rw [if_pos hx_branch]
  simpa [hsplit]

/-- Helper for Proposition 9.40: if the shifted nonnegative `ENNReal` integral is finite, then the
limit field lies back in the effective domain of the integral functional. -/
private theorem effectiveDomain_of_shifted_lintegral_ne_top
    {φ : H → Set.Ioi (⊥ : EReal)} {ρ : H → ℝ}
    (hρ_le : ∀ y : H, (((ρ y : ℝ) : EReal) ≤ (φ y : EReal)))
    {x : Ω →₂[μ] H}
    (hρx_int : Integrable (fun ω ↦ ρ (x ω)) μ)
    (hshift_sm : AEStronglyMeasurable (fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω)) μ)
    (hshift_meas :
      AEMeasurable
        (fun ω ↦ (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal)) μ)
    (hshift_ne_top :
      ∫⁻ ω, (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal) ∂μ ≠ ∞) :
    x ∈ effectiveDomain (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal)) := by
  have hshift_finite :
      ∀ᵐ ω ∂μ,
        (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal) < ∞ :=
    ae_lt_top' hshift_meas hshift_ne_top
  have hφ_finite : ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := by
    filter_upwards [hshift_finite] with ω hω
    by_contra htop
    have hsum_top :
        (φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal)) = ⊤ := by
      have hφ_top : (φ (x ω) : EReal) = ⊤ := by
        exact top_unique (not_lt.mp htop)
      rw [hφ_top]
      exact EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    have : (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal) = ∞ := by
      simpa [hsum_top]
    exact hω.ne this
  have hshift_eq :
      (fun ω ↦ (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal)) =ᵐ[μ]
        fun ω ↦ ENNReal.ofReal (EReal.toReal (φ (x ω)) - ρ (x ω)) := by
    filter_upwards [hφ_finite] with ω hω
    exact shifted_toENNReal_eq_ofReal_shifted_toReal (lt_top_iff_ne_top.mp hω)
  have hshift_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω) := by
    filter_upwards [hφ_finite] with ω hω
    have hreal_le : ρ (x ω) ≤ EReal.toReal (φ (x ω)) := by
      exact EReal.toReal_le_toReal (hρ_le (x ω)) (EReal.coe_ne_bot _)
        (lt_top_iff_ne_top.mp hω)
    exact sub_nonneg.mpr hreal_le
  have hshift_ofReal_ne_top :
      ∫⁻ ω, ENNReal.ofReal (EReal.toReal (φ (x ω)) - ρ (x ω)) ∂μ ≠ ∞ := by
    rw [← lintegral_congr_ae hshift_eq]
    exact hshift_ne_top
  have hshift_int :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hshift_sm hshift_nonneg).mp hshift_ofReal_ne_top
  have hφ_int : Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ := by
    have hadd_int : Integrable (fun ω ↦
        (EReal.toReal (φ (x ω)) - ρ (x ω)) + ρ (x ω)) μ :=
      hshift_int.add hρx_int
    have hsum_eq :
        (fun ω ↦ (EReal.toReal (φ (x ω)) - ρ (x ω)) + ρ (x ω)) =ᵐ[μ]
          fun ω ↦ EReal.toReal (φ (x ω)) := by
      exact Filter.Eventually.of_forall fun ω ↦ by ring
    exact hadd_int.congr hsum_eq
  have hbranch :
      Integrable (fun ω ↦ EReal.toReal (φ (x ω))) μ ∧
        ∀ᵐ ω ∂μ, (φ (x ω) : EReal) < ⊤ := ⟨hφ_int, hφ_finite⟩
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ, pointwiseIntegralFunctional]
  simpa [hbranch] using
    (EReal.coe_lt_top (∫ ω, EReal.toReal (φ (x ω)) ∂μ : ℝ))

/-- Helper for Proposition 9.40: the induced integral functional is lower semicontinuous. -/
private theorem integralFunctional_lowerSemicontinuous_of_finite_or_nonneg
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    LowerSemicontinuous (fun x : Ω →₂[μ] H ↦ (integralFunctional μ φ x : EReal)) := by
  -- Route correction: the missing analytic bridge is now isolated in
  -- `shifted_integrand_liminf_ae_of_subsequence`, and the affine correction term is packaged by
  -- `integral_affine_correction_eq_inner_const_add`. The remaining work is the final assembly of
  -- the closed-lower-level-set argument using these two helpers.
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro ξ
  apply IsSeqClosed.isClosed
  intro xs x hxs_level hx_tendsto
  let F : (Ω →₂[μ] H) → EReal := fun z ↦ (integralFunctional μ φ z : EReal)
  have hxs_le : ∀ n : ℕ, F (xs n) ≤ (ξ : EReal) := by
    intro n
    simpa [F] using (mem_lowerLevelSet_iff F ξ (xs n)).mp (hxs_level n)
  have hxs_dom : ∀ n : ℕ,
      xs n ∈ effectiveDomain (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal)) := by
    intro n
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt (hxs_le n) (EReal.coe_lt_top ξ)
  rcases ae_convergent_subsequence_of_tendsto_L2 hx_tendsto with ⟨ns, hns, hae⟩
  have hsubseq_tendsto : Filter.Tendsto (fun k ↦ xs (ns k)) Filter.atTop (nhds x) :=
    hx_tendsto.comp hns.tendsto_atTop
  have hfinish_of_shift :
      ∀ {ρ : H → ℝ},
        Continuous ρ →
        (∀ y : H, (((ρ y : ℝ) : EReal) ≤ (φ y : EReal))) →
        (∀ n : ℕ, Integrable (fun ω ↦ ρ (xs n ω)) μ) →
        Integrable (fun ω ↦ ρ (x ω)) μ →
        Filter.Tendsto (fun k ↦ ∫ ω, ρ (xs (ns k) ω) ∂μ) Filter.atTop
          (nhds (∫ ω, ρ (x ω) ∂μ)) →
        x ∈ lowerLevelSet F ξ := by
    intro ρ hρ_cont hρ_le hρxs_int hρx_int hcorr_tendsto
    let s : Ω → ℝ≥0∞ := fun ω ↦
      (((φ (x ω) : EReal) + (((-ρ (x ω) : ℝ) : EReal))).toENNReal)
    let sSeq : ℕ → Ω → ℝ≥0∞ := fun k ω ↦
      (((φ (xs (ns k) ω) : EReal) + (((-ρ (xs (ns k) ω) : ℝ) : EReal))).toENNReal)
    let gₓ : Ω → ℝ := fun ω ↦ EReal.toReal (φ (x ω)) - ρ (x ω)
    let gSeq : ℕ → Ω → ℝ := fun k ω ↦ EReal.toReal (φ (xs (ns k) ω)) - ρ (xs (ns k) ω)
    let corrSeq : ℕ → ℝ := fun k ↦ ∫ ω, ρ (xs (ns k) ω) ∂μ
    let corrₓ : ℝ := ∫ ω, ρ (x ω) ∂μ
    have hsSeq_meas : ∀ k : ℕ, AEMeasurable (sSeq k) μ := by
      intro k
      have hφ_meas_k :
          AEMeasurable (fun ω ↦ (φ (xs (ns k) ω) : EReal)) μ := by
        exact measurable_subtype_coe.comp_aemeasurable <|
          (measurable_of_mem_gammaZero hφ).comp_aemeasurable
            (Lp.aestronglyMeasurable (xs (ns k))).aemeasurable
      have hρ_meas_k :
          AEMeasurable (fun ω ↦ (((-ρ (xs (ns k) ω) : ℝ) : EReal))) μ := by
        exact (continuous_coe_real_ereal.comp hρ_cont.neg).measurable.comp_aemeasurable
          (Lp.aestronglyMeasurable (xs (ns k))).aemeasurable
      exact (hφ_meas_k.add hρ_meas_k).ereal_toENNReal
    have hs_meas : AEMeasurable s μ := by
      have hφ_meas_x :
          AEMeasurable (fun ω ↦ (φ (x ω) : EReal)) μ := by
        exact measurable_subtype_coe.comp_aemeasurable <|
          (measurable_of_mem_gammaZero hφ).comp_aemeasurable
            (Lp.aestronglyMeasurable x).aemeasurable
      have hρ_meas_x :
          AEMeasurable (fun ω ↦ (((-ρ (x ω) : ℝ) : EReal))) μ := by
        exact (continuous_coe_real_ereal.comp hρ_cont.neg).measurable.comp_aemeasurable
          (Lp.aestronglyMeasurable x).aemeasurable
      exact (hφ_meas_x.add hρ_meas_x).ereal_toENNReal
    have hsSeq_eq : ∀ k : ℕ, sSeq k =ᵐ[μ] fun ω ↦ ENNReal.ofReal (gSeq k ω) := by
      intro k
      have hdom : xs (ns k) ∈ pointwiseIntegralFunctionalDomain φ := by
        simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using
          (mem_effectiveDomain_iff.mp (hxs_dom (ns k)))
      rw [pointwiseIntegralFunctionalDomain_eq] at hdom
      filter_upwards [hdom.2] with ω hω
      exact shifted_toENNReal_eq_ofReal_shifted_toReal (lt_top_iff_ne_top.mp hω)
    have hgSeq_int : ∀ k : ℕ, Integrable (gSeq k) μ := by
      intro k
      exact
        (shifted_integrand_integrable_nonneg_of_effectiveDomain hρ_le
          (hρxs_int (ns k)) (hxs_dom (ns k))).1
    have hgSeq_nonneg : ∀ k : ℕ, 0 ≤ᵐ[μ] gSeq k := by
      intro k
      exact
        (shifted_integrand_integrable_nonneg_of_effectiveDomain hρ_le
          (hρxs_int (ns k)) (hxs_dom (ns k))).2
    have hsSeq_lintegral_eq : ∀ k : ℕ, ∫⁻ ω, sSeq k ω ∂μ = ENNReal.ofReal (∫ ω, gSeq k ω ∂μ) := by
      intro k
      rw [lintegral_congr_ae (hsSeq_eq k)]
      exact (ofReal_integral_eq_lintegral_ofReal (hgSeq_int k) (hgSeq_nonneg k)).symm
    have hshift_liminf :
        ∫⁻ ω, s ω ∂μ ≤ Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop := by
      -- The pointwise liminf estimate feeds directly into Fatou's lemma.
      have hpointwise :
          ∀ᵐ ω ∂μ, s ω ≤ Filter.liminf (fun k ↦ sSeq k ω) Filter.atTop := by
        simpa [s, sSeq] using shifted_integrand_liminf_ae_of_subsequence hφ hρ_cont hae
      have hmono :
          ∫⁻ ω, s ω ∂μ ≤ ∫⁻ ω, Filter.liminf (fun k ↦ sSeq k ω) Filter.atTop ∂μ :=
        lintegral_mono_ae hpointwise
      exact hmono.trans (lintegral_liminf_le' hsSeq_meas)
    have hcorr_ge :
        ∀ᶠ k : ℕ in Filter.atTop, corrₓ - 1 ≤ corrSeq k := by
      have hIcc : Set.Icc (corrₓ - 1) (corrₓ + 1) ∈ nhds corrₓ := by
        exact Icc_mem_nhds (by linarith) (by linarith)
      exact hcorr_tendsto.eventually hIcc |>.mono fun _ hk ↦ hk.1
    have hcorr_le :
        ∀ᶠ k : ℕ in Filter.atTop, corrSeq k ≤ corrₓ + 1 := by
      have hIcc : Set.Icc (corrₓ - 1) (corrₓ + 1) ∈ nhds corrₓ := by
        exact Icc_mem_nhds (by linarith) (by linarith)
      exact hcorr_tendsto.eventually hIcc |>.mono fun _ hk ↦ hk.2
    let B : ℝ := max 0 (ξ + 1 - corrₓ)
    have hgSeq_bound :
        ∀ᶠ k : ℕ in Filter.atTop, ∫ ω, gSeq k ω ∂μ ≤ B := by
      filter_upwards [hcorr_ge] with k hk
      have hcombo_eq :
          (integralFunctional μ φ (xs (ns k)) : EReal) =
            (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) := by
        simpa [gSeq, corrSeq] using
          integralFunctional_eq_shifted_integral_add_correction hρ_le (hρxs_int (ns k))
            (hxs_dom (ns k))
      have hcombo_eq' :
          pointwiseIntegralFunctional φ (xs (ns k)) =
            (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) := by
        simpa [integralFunctional_coe μ] using hcombo_eq
      have hcombo_leE :
          (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) ≤ (ξ : EReal) := by
        simpa [F, integralFunctional_coe μ, hcombo_eq'] using hxs_le (ns k)
      have hcombo_le : (∫ ω, gSeq k ω ∂μ) + corrSeq k ≤ ξ := by
        exact_mod_cast hcombo_leE
      have htmp : ∫ ω, gSeq k ω ∂μ ≤ ξ + 1 - corrₓ := by
        linarith
      exact le_trans htmp (le_max_right 0 _)
    have hsSeq_bound :
        ∀ᶠ k : ℕ in Filter.atTop, ∫⁻ ω, sSeq k ω ∂μ ≤ ENNReal.ofReal B := by
      filter_upwards [hgSeq_bound] with k hk
      calc
        ∫⁻ ω, sSeq k ω ∂μ = ENNReal.ofReal (∫ ω, gSeq k ω ∂μ) := hsSeq_lintegral_eq k
        _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hk
    have hliminf_ne_top :
        Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop ≠ ∞ := by
      have hliminf_le_B :
          Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop ≤ ENNReal.ofReal B := by
        refine Filter.liminf_le_of_le ?_ ?_
        · exact by isBoundedDefault
        · intro b hb
          let ⟨k, hk₁, hk₂⟩ := (hb.and hsSeq_bound).exists
          exact hk₁.trans hk₂
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hliminf_le_B
    have hshift_sm_x : AEStronglyMeasurable gₓ μ := by
      have hφ_toReal :
          AEStronglyMeasurable (fun ω ↦ EReal.toReal (φ (x ω))) μ :=
        pointwise_integrand_aestronglyMeasurable φ (measurable_of_mem_gammaZero hφ) x
      have hρ_meas_x :
          AEMeasurable (fun ω ↦ ρ (x ω)) μ :=
        hρ_cont.measurable.comp_aemeasurable (Lp.aestronglyMeasurable x).aemeasurable
      exact hφ_toReal.sub hρ_meas_x.aestronglyMeasurable
    have hx_dom :
        x ∈ effectiveDomain (integralFunctional μ φ : (Ω →₂[μ] H) → Set.Ioi (⊥ : EReal)) :=
      effectiveDomain_of_shifted_lintegral_ne_top hρ_le hρx_int hshift_sm_x hs_meas
        (ne_top_of_le_ne_top hliminf_ne_top hshift_liminf)
    have hgₓ_int : Integrable gₓ μ :=
      (shifted_integrand_integrable_nonneg_of_effectiveDomain hρ_le hρx_int hx_dom).1
    have hgₓ_nonneg : 0 ≤ᵐ[μ] gₓ :=
      (shifted_integrand_integrable_nonneg_of_effectiveDomain hρ_le hρx_int hx_dom).2
    have hs_eq :
        s =ᵐ[μ] fun ω ↦ ENNReal.ofReal (gₓ ω) := by
      have hdom : x ∈ pointwiseIntegralFunctionalDomain φ := by
        simpa [pointwiseIntegralFunctionalDomain, integralFunctional_coe μ] using
          (mem_effectiveDomain_iff.mp hx_dom)
      rw [pointwiseIntegralFunctionalDomain_eq] at hdom
      filter_upwards [hdom.2] with ω hω
      exact shifted_toENNReal_eq_ofReal_shifted_toReal (lt_top_iff_ne_top.mp hω)
    have hs_lintegral_eq : ∫⁻ ω, s ω ∂μ = ENNReal.ofReal (∫ ω, gₓ ω ∂μ) := by
      rw [lintegral_congr_ae hs_eq]
      exact (ofReal_integral_eq_lintegral_ofReal hgₓ_int hgₓ_nonneg).symm
    have hright_toReal :
        (Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop).toReal =
          Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop := by
      calc
        (Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop).toReal =
            Filter.liminf (fun k ↦ (∫⁻ ω, sSeq k ω ∂μ).toReal) Filter.atTop := by
              simpa using
                (ENNReal.liminf_toReal_eq (f := Filter.atTop)
                  (u := fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) ENNReal.ofReal_ne_top hsSeq_bound).symm
        _ = Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop := by
              refine Filter.liminf_congr ?_
              exact Filter.Eventually.of_forall fun k ↦ by
                have hk_nonneg : 0 ≤ ∫ ω, gSeq k ω ∂μ := integral_nonneg_of_ae (hgSeq_nonneg k)
                rw [hsSeq_lintegral_eq k, ENNReal.toReal_ofReal hk_nonneg]
    have hshift_real :
        ∫ ω, gₓ ω ∂μ ≤ Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop := by
      have htoReal_le :
          (∫⁻ ω, s ω ∂μ).toReal ≤
            (Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop).toReal :=
        (ENNReal.toReal_le_toReal (by rw [hs_lintegral_eq]; exact ENNReal.ofReal_ne_top)
          hliminf_ne_top).2 hshift_liminf
      calc
        ∫ ω, gₓ ω ∂μ = (∫⁻ ω, s ω ∂μ).toReal := by
          have hx_nonneg : 0 ≤ ∫ ω, gₓ ω ∂μ := integral_nonneg_of_ae hgₓ_nonneg
          rw [hs_lintegral_eq, ENNReal.toReal_ofReal hx_nonneg]
        _ ≤ (Filter.liminf (fun k ↦ ∫⁻ ω, sSeq k ω ∂μ) Filter.atTop).toReal := htoReal_le
        _ = Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop := hright_toReal
    have hcorr_liminf : Filter.liminf corrSeq Filter.atTop = corrₓ := hcorr_tendsto.liminf_eq
    have hsum_le_liminf :
        (∫ ω, gₓ ω ∂μ) + corrₓ ≤ Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ + corrSeq k) Filter.atTop := by
      have hu_ge :
          Filter.IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) Filter.atTop
            (fun k ↦ ∫ ω, gSeq k ω ∂μ) :=
        Filter.isBoundedUnder_of_eventually_ge (a := 0)
          (Filter.Eventually.of_forall fun k ↦ integral_nonneg_of_ae (hgSeq_nonneg k))
      have hu_le :
          Filter.IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) Filter.atTop
            (fun k ↦ ∫ ω, gSeq k ω ∂μ) :=
        Filter.isBoundedUnder_of_eventually_le (a := B) hgSeq_bound
      have hv_ge :
          Filter.IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) Filter.atTop corrSeq :=
        Filter.isBoundedUnder_of_eventually_ge (a := corrₓ - 1) hcorr_ge
      have hv_co :
          Filter.IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) Filter.atTop corrSeq :=
        Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop hcorr_le
      calc
        (∫ ω, gₓ ω ∂μ) + corrₓ ≤
            Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop +
              Filter.liminf corrSeq Filter.atTop := by
                rw [hcorr_liminf]
                gcongr
        _ ≤ Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ + corrSeq k) Filter.atTop := by
              simpa [corrSeq] using
                (le_liminf_add (h₁ := hu_ge) (h₂ := hu_le) (h₃ := hv_ge) (h₄ := hv_co) :
                  Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ) Filter.atTop +
                    Filter.liminf corrSeq Filter.atTop ≤
                      Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ + corrSeq k) Filter.atTop)
    have hcombo_le_xi :
        Filter.liminf (fun k ↦ ∫ ω, gSeq k ω ∂μ + corrSeq k) Filter.atTop ≤ ξ := by
      have hcombo_ge :
          ∀ᶠ k : ℕ in Filter.atTop, corrₓ - 1 ≤ ∫ ω, gSeq k ω ∂μ + corrSeq k := by
        filter_upwards [hcorr_ge] with k hk
        have hk_nonneg : 0 ≤ ∫ ω, gSeq k ω ∂μ := integral_nonneg_of_ae (hgSeq_nonneg k)
        linarith
      refine Filter.liminf_le_of_le ?_ ?_
      · exact Filter.isBoundedUnder_of_eventually_ge (a := corrₓ - 1) hcombo_ge
      · intro b hb
        have hupper :
            ∀ᶠ k : ℕ in Filter.atTop, ∫ ω, gSeq k ω ∂μ + corrSeq k ≤ ξ := by
          refine Filter.Eventually.of_forall ?_
          intro k
          have hcombo_eq :
              (integralFunctional μ φ (xs (ns k)) : EReal) =
                (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) := by
            simpa [gSeq, corrSeq] using
              integralFunctional_eq_shifted_integral_add_correction hρ_le (hρxs_int (ns k))
                (hxs_dom (ns k))
          have hcombo_eq' :
              pointwiseIntegralFunctional φ (xs (ns k)) =
                (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) := by
            simpa [integralFunctional_coe μ] using hcombo_eq
          have hcombo_leE :
              (((∫ ω, gSeq k ω ∂μ) + corrSeq k : ℝ) : EReal) ≤ (ξ : EReal) := by
            simpa [F, integralFunctional_coe μ, hcombo_eq'] using hxs_le (ns k)
          exact_mod_cast hcombo_leE
        let ⟨k, hk₁, hk₂⟩ := (hb.and hupper).exists
        exact hk₁.trans hk₂
    have hx_eq :
        (integralFunctional μ φ x : EReal) = (((∫ ω, gₓ ω ∂μ) + corrₓ : ℝ) : EReal) := by
      simpa [gₓ, corrₓ] using
        integralFunctional_eq_shifted_integral_add_correction hρ_le hρx_int hx_dom
    have hx_le_real : (∫ ω, gₓ ω ∂μ) + corrₓ ≤ ξ :=
      hsum_le_liminf.trans hcombo_le_xi
    rw [mem_lowerLevelSet_iff]
    have hx_leE : (((∫ ω, gₓ ω ∂μ) + corrₓ : ℝ) : EReal) ≤ (ξ : EReal) := by
      exact_mod_cast hx_le_real
    have hx_eq' : pointwiseIntegralFunctional φ x = (((∫ ω, gₓ ω ∂μ) + corrₓ : ℝ) : EReal) := by
      simpa [integralFunctional_coe μ] using hx_eq
    simpa [F, integralFunctional_coe μ, hx_eq'] using hx_leE
  rcases hfinite_or_nonneg with hfinite | ⟨hzero, hnonneg⟩
  · letI : IsFiniteMeasure μ := ⟨hfinite⟩
    rcases exists_real_affine_minorant_of_mem_gammaZero_local hφ with ⟨u, η, hminorant⟩
    let ρ : H → ℝ := fun y ↦ ⟪y, u⟫_ℝ + η
    have hρ_cont : Continuous ρ := by
      simpa [ρ] using (continuous_id.inner continuous_const).add continuous_const
    have hρ_int_all : ∀ z : Ω →₂[μ] H, Integrable (fun ω ↦ ρ (z ω)) μ := by
      intro z
      have hz_int : Integrable (fun ω : Ω ↦ z ω) μ := by
        exact
          integrableOn_univ.mp
            (integrableOn_Lp_of_measure_ne_top z fact_one_le_two_ennreal.elim
              (measure_ne_top μ Set.univ))
      simpa [ρ] using (hz_int.inner_const u).add (integrable_const η)
    have hcorr_tendsto :
        Filter.Tendsto (fun k ↦ ∫ ω, ρ (xs (ns k) ω) ∂μ) Filter.atTop
          (nhds (∫ ω, ρ (x ω) ∂μ)) := by
      have hinner_tendsto :
          Filter.Tendsto
            (fun k ↦ ⟪xs (ns k), Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal)
            Filter.atTop
            (nhds (⟪x, Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal)) := by
        have hcont :
            Continuous
              (fun z : Ω →₂[μ] H ↦ ⟪z, Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal) := by
          simpa using (continuous_id.inner continuous_const).add continuous_const
        exact hcont.tendsto x |>.comp hsubseq_tendsto
      have hseq_eq :
          (fun k ↦ ∫ ω, ρ (xs (ns k) ω) ∂μ) =
            fun k ↦ ⟪xs (ns k), Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal := by
        funext k
        simpa [ρ] using
          integral_affine_correction_eq_inner_const_add (u := u) (η := η) (xs (ns k))
      have hx_eq :
          (∫ ω, ρ (x ω) ∂μ) = ⟪x, Lp.const 2 μ u⟫_ℝ + η * (μ Set.univ).toReal := by
        simpa [ρ] using integral_affine_correction_eq_inner_const_add (u := u) (η := η) x
      rw [hseq_eq, hx_eq]
      exact hinner_tendsto
    exact hfinish_of_shift hρ_cont hminorant (fun n ↦ hρ_int_all (xs n)) (hρ_int_all x) hcorr_tendsto
  · have hρ_cont : Continuous (fun _ : H ↦ (0 : ℝ)) := continuous_const
    have hρ_le : ∀ y : H, ((((0 : ℝ) : ℝ) : EReal) ≤ (φ y : EReal)) := by
      intro y
      simpa [hzero] using hnonneg y
    have hρxs_int : ∀ n : ℕ, Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
      intro n
      simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
    have hρx_int : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ := by
      simpa using (integrable_zero : Integrable (fun _ : Ω ↦ (0 : ℝ)) μ)
    have hcorr_tendsto :
        Filter.Tendsto (fun k : ℕ ↦ ∫ ω, (0 : ℝ) ∂μ) Filter.atTop
          (nhds (∫ ω, (0 : ℝ) ∂μ)) := by
      simpa using tendsto_const_nhds
    exact hfinish_of_shift hρ_cont hρ_le
      (fun n ↦ by simpa using hρxs_int n) hρx_int hcorr_tendsto

-- Proof sketch: use the Chapter 8 convexity theorem for the integral functional. For lower
-- semicontinuity, follow the textbook Fatou argument on almost-everywhere convergent subsequences.
-- Properness comes either from the finite-measure constant field built from a point in `dom φ`, via
-- an affine minorant of `φ`, or from the zero field when `φ` is bounded below by `φ(0) = 0`.
/-- Proposition 9.40: if `φ ∈ Γ₀(H)` and either (i) `μ(Ω) < +∞` or (ii) `φ ≥ φ(0) = 0`, then the
integral functional induced by `φ` belongs to `Γ₀(L²((Ω,\mathcal F,\mu); H))`. -/
theorem integralFunctional_mem_gammaZero
    (μ : Measure Ω)
    (φ : H → Set.Ioi (⊥ : EReal))
    (hφ : φ ∈ Γ₀(H))
    (hfinite_or_nonneg :
      μ Set.univ < ∞ ∨ ((φ 0 : EReal) = 0 ∧ ∀ z : H, (φ 0 : EReal) ≤ (φ z : EReal))) :
    integralFunctional μ φ ∈ Γ₀(Ω →₂[μ] H) := by
  -- The Chapter 8 result gives the Jensen inequality once we provide measurability, the global
  -- convex bridge, and an integrable lower bound along each `L²` field.
  have hconv_global :
      ∀ ⦃x y : Ω →₂[μ] H⦄, ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        (integralFunctional μ φ (α • x + (1 - α) • y) : EReal) ≤
          (α : EReal) * (integralFunctional μ φ x : EReal) +
            (1 - α : EReal) * (integralFunctional μ φ y : EReal) := by
    intro x y α hα0 hα1
    simpa [integralFunctional_coe μ] using
      pointwiseIntegralFunctional_convex φ
        (measurable_of_mem_gammaZero hφ)
        (fun {u v} {β} hβ0 hβ1 ↦ convex_ineq_of_mem_gammaZero hφ hβ0 hβ1)
        (integrable_lower_bound_of_finite_or_nonneg φ hφ hfinite_or_nonneg)
        hα0 hα1
  refine ⟨integralFunctional_lowerSemicontinuous_of_finite_or_nonneg φ hφ hfinite_or_nonneg, ?_⟩
  refine ⟨integralFunctional_effectiveDomain_nonempty_of_finite_or_nonneg φ hφ hfinite_or_nonneg,
    fun x hx ↦ hx, ?_⟩
  -- Global convexity immediately restricts to convexity on the effective domain.
  intro x hx y hy α hα0 hα1
  exact hconv_global hα0 hα1

end

end ERealFunction

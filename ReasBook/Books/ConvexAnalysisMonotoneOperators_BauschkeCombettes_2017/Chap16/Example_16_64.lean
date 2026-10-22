/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_63

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [μ.IsComplete] [SigmaFinite μ]

/-- Classical decidability of equality on `H`, used to state the normalized pointwise field. -/
local instance instDecidableEqIntegralFunctionalNorm : DecidableEq H := Classical.decEq H

/- Source/core/bridge triage:
- `source-facing`: Example 16.64 is the integral-functional subgradient formula for the norm.
- `core/canonical`: the owner objects are `Γ₀(H)`, `∂`, and `integralFunctional μ`.
- `bridge/view`: Example 16.32 provides the pointwise norm subdifferential formula, and
  Proposition 16.63 upgrades almost-everywhere pointwise subdifferential membership to membership
  in the subdifferential of the integral functional.
-/

-- Proof sketch: the norm is a proper lower-semicontinuous convex function on a real Hilbert space,
-- hence its `]-∞,+∞]`-valued version belongs to `Γ₀(H)`.
omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The `]-∞,+∞]`-valued norm function belongs to `Γ₀(H)`. -/
theorem norm_mem_gammaZero :
    norm.toEReal ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha hb
    have hnorm :
        ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
      (((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ)) : EReal)
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact_mod_cast hnorm
  · simpa using (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous

-- Proof sketch: use Example 16.32 pointwise. If `x ω = 0`, then the chosen value is `0`, which
-- belongs to the closed unit ball branch of the norm subdifferential. If `x ω ≠ 0`, then the
-- chosen value is exactly the normalized vector appearing in the singleton branch.
omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [μ.IsComplete] [SigmaFinite μ] in
/-- A field agreeing almost everywhere with the normalized pointwise formula belongs almost
everywhere to the pointwise subdifferential of the norm. -/
theorem ae_mem_subdifferential_norm_of_ae_eq_normalized
    {x u : Ω →₂[μ] H}
    (hu :
      ∀ᵐ ω ∂μ, u ω = if x ω = 0 then 0 else ‖x ω‖⁻¹ • x ω) :
    ∀ᵐ ω ∂μ, u ω ∈ (∂ ((norm : H → ℝ).toEReal)) (x ω) := by
  filter_upwards [hu] with ω huω
  by_cases hxω : x ω = 0
  · simp [subdifferential_norm_eq_singleton_or_closedBall, Metric.mem_closedBall, huω, hxω]
  · simp [subdifferential_norm_eq_singleton_or_closedBall, huω, hxω]

-- Proof sketch: on the set where `x ω ≠ 0`, the normalized field has norm `1`, and it vanishes
-- elsewhere. Since `u` is an `L²` field, that indicator of `{ω | x ω ≠ 0}` also lies in `L²`,
-- hence the support set has finite measure. The ambient `L²` field `x` therefore belongs to `L¹`
-- on that finite-measure support, so the integral norm functional is finite at `x`.
omit [μ.IsComplete] [SigmaFinite μ] in
/-- If an `L²` field agrees almost everywhere with the normalized pointwise formula associated to
`x`, then `x` automatically belongs to the effective domain of the integral norm functional. -/
theorem mem_effectiveDomain_integralFunctional_norm_of_ae_eq_normalized
    {x u : Ω →₂[μ] H}
    (hu :
      ∀ᵐ ω ∂μ, u ω = if x ω = 0 then 0 else ‖x ω‖⁻¹ • x ω) :
    x ∈ effectiveDomain (integralFunctional μ norm.toEReal) := by
  let s : Set Ω := {ω | x ω ≠ 0}
  have hs : MeasurableSet s := by
    rw [show s = x ⁻¹' ({0}ᶜ : Set H) by
      ext ω
      simp [s]]
    exact measurableSet_preimage (Lp.stronglyMeasurable x).measurable
      isClosed_singleton.isOpen_compl.measurableSet
  have hu_norm :
      ∀ᵐ ω ∂μ, ‖u ω‖ = Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω := by
    filter_upwards [hu] with ω huω
    by_cases hxω : x ω = 0
    · simp [s, hxω, huω]
    · simp [s, hxω, huω, norm_smul]
  have hs_fin : μ s < ⊤ := by
    have hmem_indicator :
        MemLp (Set.piecewise s (Function.const Ω (1 : ℝ)) (Function.const Ω 0)) 2 μ := by
      refine ((Lp.memLp u).norm).congr_norm ?_ ?_
      · exact (measurable_const.piecewise hs measurable_const).aestronglyMeasurable
      · filter_upwards [hu_norm] with ω hω
        simpa [Set.piecewise_eq_indicator] using congrArg (fun t : ℝ ↦ ‖t‖) hω
    have hmem_simple_indicator :
        MemLp (⇑(SimpleFunc.piecewise s hs (SimpleFunc.const Ω (1 : ℝ)) (SimpleFunc.const Ω 0))) 2 μ := by
      simpa [SimpleFunc.coe_piecewise, Set.piecewise_eq_indicator] using hmem_indicator
    simpa using
      (SimpleFunc.measure_lt_top_of_memLp_indicator two_ne_zero ENNReal.ofNat_ne_top
        one_ne_zero hs hmem_simple_indicator : μ s < ⊤)
  have hx_memLp : MemLp x 1 μ := by
    have hx_zero_off_s : ∀ ω, ω ∉ s → x ω = 0 := by
      intro ω hω
      simpa [s] using hω
    refine (Lp.memLp x).mono_exponent_of_measure_support_ne_top hx_zero_off_s hs_fin.ne ?_
    · norm_num
  have hx_int : Integrable (fun ω ↦ x ω) μ := memLp_one_iff_integrable.mp hx_memLp
  rw [mem_effectiveDomain_iff, integralFunctional_coe μ, pointwiseIntegralFunctional]
  have hbranch :
      Integrable (fun ω ↦ EReal.toReal (norm.toEReal (x ω))) μ ∧
        ∀ᵐ ω ∂μ, ((norm.toEReal (x ω) : Set.Ioi (⊥ : EReal)) : EReal) < ⊤ := by
    constructor
    · simpa using hx_int.norm
    · filter_upwards with ω
      simp
  rw [if_pos hbranch]
  simp [Function.toEReal_apply]

-- Proof sketch: apply the membership bridge from Proposition 16.63 to
-- `φ = norm.toEReal`. The required `Γ₀` hypothesis is `norm_mem_gammaZero`, and the
-- nonnegativity branch holds because the norm vanishes at `0` and is everywhere nonnegative. Then
-- use `mem_effectiveDomain_integralFunctional_norm_of_ae_eq_normalized` to derive the effective
-- domain hypothesis internally, and `ae_mem_subdifferential_norm_of_ae_eq_normalized` to verify
-- the pointwise subdifferential condition almost everywhere.
/-- Example 16.64: every `L²` field that agrees almost everywhere with the normalized pointwise
formula `ω ↦ if x ω = 0 then 0 else ‖x ω‖⁻¹ • x ω` is a subgradient of the integral norm
functional at `x`. The normalized-field hypothesis already forces `x` into the effective domain of
the integral functional. -/
theorem normalizedField_mem_subdifferential_integralFunctional_norm
    {x u : Ω →₂[μ] H}
    (hu :
      ∀ᵐ ω ∂μ, u ω = if x ω = 0 then 0 else ‖x ω‖⁻¹ • x ω) :
    u ∈
      (∂ integralFunctional μ ((norm : H → ℝ).toEReal)) x := by
  have hx : x ∈ effectiveDomain (integralFunctional μ norm.toEReal) :=
    mem_effectiveDomain_integralFunctional_norm_of_ae_eq_normalized hu
  refine
    (mem_subdifferential_integralFunctional_iff_ae_mem_subdifferential
      norm.toEReal norm_mem_gammaZero
      (Or.inr ⟨by simp, fun z ↦ by simp⟩) hx).2 ?_
  exact ae_mem_subdifferential_norm_of_ae_eq_normalized hu

end SubdifferentialCalculus

end

end ERealFunction

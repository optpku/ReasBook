/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Set

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {H : Type v} [NormedAddCommGroup H]

-- Proof sketch: rewrite the textbook left- and right-hand sides as the corresponding
-- `MeasureTheory.eLpNorm` expressions for exponents `ENNReal.ofReal p` and `ENNReal.ofReal q`,
-- then apply `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` to `x`. The hypothesis
-- `hpq : p < q` supplies the required exponent monotonicity.
/-- Example 9.25 (1): on a finite measure space, every `H`-valued `L^q` function with
`0 < p < q` satisfies the standard comparison estimate between its `L^p` and `L^q` norms. -/
theorem lp_norm_le_measure_univ_rpow_mul_lq_norm
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) {x : Ω → H}
    (hx : MemLp x (ENNReal.ofReal q) μ) :
    (∫ ω, ‖x ω‖ ^ p ∂μ) ^ (1 / p) ≤
      ((μ Set.univ).toReal) ^ (1 / p - 1 / q) * (∫ ω, ‖x ω‖ ^ q ∂μ) ^ (1 / q) := by
  let p' : ENNReal := ENNReal.ofReal p
  let q' : ENNReal := ENNReal.ofReal q
  have hq : 0 < q := lt_trans hp hpq
  have hp'_ne_zero : p' ≠ 0 := by
    simpa [p'] using hp
  have hq'_ne_zero : q' ≠ 0 := by
    simpa [q'] using hq
  have hx' : MemLp x p' μ := hx.mono_exponent <| by
    simpa [p', q'] using ENNReal.ofReal_le_ofReal hpq.le
  have h_exp_nonneg : 0 ≤ 1 / p'.toReal - 1 / q'.toReal := by
    have h_inv : q⁻¹ ≤ p⁻¹ := by
      exact (inv_le_inv₀ hq hp).2 hpq.le
    simpa [p', q', hp.le, hq.le, sub_nonneg, one_div] using h_inv
  have h_compare :
      eLpNorm x p' μ ≤ eLpNorm x q' μ * μ Set.univ ^ (1 / p'.toReal - 1 / q'.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by simpa [p', q'] using ENNReal.ofReal_le_ofReal hpq.le)
      hx.aestronglyMeasurable
  have h_rhs_ne_top :
      eLpNorm x q' μ * μ Set.univ ^ (1 / p'.toReal - 1 / q'.toReal) ≠ ⊤ := by
    refine ENNReal.mul_ne_top hx.eLpNorm_ne_top ?_
    exact (ENNReal.rpow_lt_top_of_nonneg h_exp_nonneg (measure_lt_top μ Set.univ).ne).ne
  have h_real :
      (eLpNorm x p' μ).toReal ≤
        (eLpNorm x q' μ * μ Set.univ ^ (1 / p'.toReal - 1 / q'.toReal)).toReal :=
    (ENNReal.toReal_le_toReal hx'.eLpNorm_ne_top h_rhs_ne_top).2 h_compare
  rw [ENNReal.toReal_mul, toReal_eLpNorm hx'.aestronglyMeasurable,
    toReal_eLpNorm hx.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp'_ne_zero ENNReal.ofReal_ne_top hx'.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hq'_ne_zero ENNReal.ofReal_ne_top hx.aestronglyMeasurable,
    ← ENNReal.toReal_rpow] at h_real
  simpa [p', q', hp.le, hq.le, one_div, mul_comm] using h_real

-- Proof sketch: keep the textbook domain `0 < p < q`, convert the exponent inequality to
-- `ENNReal.ofReal p ≤ ENNReal.ofReal q`, and apply the canonical antitonicity
-- `MeasureTheory.Lp.antitone` on finite measure spaces.
/-- Example 9.25 (2): on a finite measure space, every `H`-valued `L^q` function with
`0 < p < q` also belongs to `L^p(μ; H)`. -/
theorem lp_antitone_of_lt_exponent
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    MeasureTheory.Lp H (ENNReal.ofReal q) μ ≤ MeasureTheory.Lp H (ENNReal.ofReal p) μ := by
  have hq : 0 < q := lt_trans hp hpq
  have hpq' : ENNReal.ofReal p < ENNReal.ofReal q :=
    (ENNReal.ofReal_lt_ofReal_iff hq).2 hpq
  exact MeasureTheory.Lp.antitone hpq'.le

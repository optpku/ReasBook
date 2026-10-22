/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
variable (hμ :
  ∃ a : NNReal,
    0 < a ∧ ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A ≠ 0 → (a : ENNReal) ≤ μ A)

include hμ

omit hμ in
/-- Helper for Exercise 4.1.1: a measurable set with measure strictly below the uniform lower
bound must be null. -/
lemma measure_eq_zero_of_lt_uniformLowerBound
    {a : NNReal}
    (ha_lower :
      ∀ ⦃A : Set Ω⦄, MeasurableSet A → μ A ≠ 0 → (a : ENNReal) ≤ μ A)
    {S : Set Ω} (hS_meas : MeasurableSet S) (hS_lt : μ S < (a : ENNReal)) :
    μ S = 0 := by
  -- A nonnull set would contradict the lower bound immediately.
  by_contra hS_nonzero
  exact (not_lt_of_ge (ha_lower hS_meas hS_nonzero)) hS_lt

omit hμ in
/-- Helper for Exercise 4.1.1: if a superlevel set of `‖f‖` is null, then `f` is almost
everywhere bounded by that threshold. -/
lemma ae_norm_le_of_superlevel_null
    {f : Ω →ₘ[μ] ℝ} {ε : ENNReal} (hε_ne_top : ε ≠ ∞)
    (hS_zero : μ {x | ε ≤ ‖f x‖₊} = 0) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ε.toReal := by
  -- First move the null-set statement into an a.e. complement statement.
  have hS_ae : ∀ᵐ x ∂μ, x ∉ {x | ε ≤ ‖f x‖₊} :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hS_zero
  filter_upwards [hS_ae] with x hx
  -- Then convert the strict `ENNReal` inequality back to a real-valued norm bound.
  have hx_lt : (‖f x‖₊ : ENNReal) < ε := lt_of_not_ge hx
  have hx_real_lt : ((‖f x‖₊ : ENNReal).toReal) < ε.toReal :=
    (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hε_ne_top).2 hx_lt
  simpa using hx_real_lt.le

/-- Helper for Exercise 4.1.1: under the uniform lower bound on nonnull measurable sets, every
`L^p` class with `1 ≤ p` is essentially bounded. -/
lemma aeBoundOfMemLpOfMeasureLowerBound
    {p : ENNReal} (hp : 1 ≤ p) {f : Ω →ₘ[μ] ℝ} (hf : f ∈ Lp ℝ p μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  by_cases hp_top : p = ∞
  · -- In the `L^∞` case, the standard essential-supremum bound gives the required constant.
    have hf_top : MemLp f ∞ μ := by
      simpa [hp_top] using (Lp.mem_Lp_iff_memLp (f := f)).1 hf
    refine ⟨lpNorm f ∞ μ, lpNorm_nonneg, ?_⟩
    simpa using ae_le_lpNorm_exponent_top hf_top
  -- Route correction: work directly with the native superlevel set `{x | ε ≤ ‖f x‖₊}` so the
  -- Markov estimate and the final a.e. bound use the same spelling throughout.
  rcases hμ with ⟨a, ha_pos, ha_lower⟩
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  let F : Lp ℝ p μ := ⟨f, hf⟩
  let K : ENNReal := ENNReal.ofReal ‖F‖ ^ p.toReal
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K.toReal / (a : ℝ) < n + 1 := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, K.toReal / (a : ℝ) < m := exists_nat_gt (K.toReal / (a : ℝ))
    have hm_succ : (m : ℝ) < m + 1 := by
      exact_mod_cast Nat.lt_succ_self m
    exact ⟨m, lt_trans hm hm_succ⟩
  have hK_lt : K.toReal < (a : ℝ) * (n + 1) := by
    have ha_real_pos : 0 < (a : ℝ) := ha_pos
    have : K.toReal < (n + 1 : ℝ) * a := by
      exact (div_lt_iff₀ ha_real_pos).1 <| by simpa using hn
    simpa [mul_comm] using this
  let ε : ENNReal := (n + 1 : ENNReal) ^ (1 / p.toReal)
  let S : Set Ω := {x | ε ≤ ‖f x‖₊}
  have hS_meas : MeasurableSet S := by
    -- The superlevel set is measurable because the representative is strongly measurable.
    refine measurableSet_le measurable_const ?_
    simpa [S] using f.stronglyMeasurable.nnnorm.measurable
  have hε_pow : ε ^ p.toReal = n + 1 := by
    -- The threshold was chosen so that its `p`th power is exactly `n + 1`.
    dsimp [ε]
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp_toReal_pos.ne', ENNReal.rpow_one]
  have hmarkovPow : ε ^ p.toReal * μ S ≤ K := by
    -- This is the direct Markov estimate on the native superlevel set.
    simpa [F, K, S] using Lp.mul_meas_ge_le_pow_enorm' F hp_ne_zero hp_top ε
  have hmarkov : (n + 1 : ENNReal) * μ S ≤ K := by
    -- Rewrite the powered threshold to the integer level chosen above.
    calc
      (n + 1 : ENNReal) * μ S = ε ^ p.toReal * μ S := by rw [hε_pow]
      _ ≤ K := hmarkovPow
  have hK_ne_top : K ≠ ∞ := by
    simp [K]
  have hS_lt : μ S < (a : ENNReal) := by
    -- Otherwise `μ S ≥ a`, and the Markov inequality contradicts the choice of `n`.
    by_contra hS_not_lt
    have ha_le : (a : ENNReal) ≤ μ S := le_of_not_gt hS_not_lt
    have hna_le_K : (n + 1 : ENNReal) * (a : ENNReal) ≤ K := by
      exact le_trans (mul_le_mul_right ha_le (n + 1 : ENNReal)) hmarkov
    have hna_le_real : (n + 1 : ℝ) * a ≤ K.toReal := by
      simpa [ENNReal.toReal_mul, mul_comm, mul_left_comm, mul_assoc] using
        ENNReal.toReal_mono hK_ne_top hna_le_K
    have hna_le_real' : (a : ℝ) * (n + 1) ≤ K.toReal := by
      simpa [mul_comm] using hna_le_real
    exact (not_lt_of_ge hna_le_real') hK_lt
  have hS_zero : μ S = 0 := measure_eq_zero_of_lt_uniformLowerBound ha_lower hS_meas hS_lt
  have hε_ne_top : ε ≠ ∞ := by
    simp [ε]
  refine ⟨ε.toReal, ENNReal.toReal_nonneg, ?_⟩
  -- The nullity of the superlevel set gives the required a.e. real-valued bound.
  simpa [S] using ae_norm_le_of_superlevel_null (μ := μ) (f := f) hε_ne_top hS_zero

omit hμ in
/-- Helper for Exercise 4.1.1: an almost-everywhere bound upgrades `MemLp f p' μ` to
`MemLp f p μ` when `1 ≤ p' ≤ p < ∞`. -/
lemma memLpOfMemLpOfAEBound
    {f : Ω → ℝ} {p' p : ENNReal}
    (hp' : 1 ≤ p') (hp'le : p' ≤ p) (hp_top : p ≠ ∞)
    (hf : MemLp f p' μ) {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    MemLp f p μ := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_trans hp' hp'le))
  have hp'_ne_zero : p' ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp')
  have hp'_top : p' ≠ ∞ := by
    intro hp'_top
    have hp_le_top : ∞ ≤ p := by
      simpa [hp'_top] using hp'le
    exact hp_top (top_le_iff.mp hp_le_top)
  have htoReal_mono : p'.toReal ≤ p.toReal := ENNReal.toReal_mono hp_top hp'le
  have hdiff_nonneg : 0 ≤ p.toReal - p'.toReal := sub_nonneg.mpr htoReal_mono
  let B : ℝ := max C 0
  have hfB : ∀ᵐ x ∂μ, ‖f x‖ ≤ B := by
    -- Replace the a.e. bound by a nonnegative one so that `Real.rpow_le_rpow` applies directly.
    filter_upwards [hfC] with x hx
    exact hx.trans (le_max_left _ _)
  have hpow_mem : MemLp (fun x ↦ ‖f x‖ ^ p'.toReal) 1 μ := hf.norm_rpow hp'_ne_zero hp'_top
  have hpow_p : MemLp (fun x ↦ ‖f x‖ ^ p.toReal) 1 μ := by
    -- Compare the `p`-power directly with the `p'`-power using the essential bound `‖f‖ ≤ B`.
    refine hpow_mem.of_le_mul (c := B ^ (p.toReal - p'.toReal))
      ((hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable) ?_
    filter_upwards [hfB] with x hx
    have hnorm_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      exact le_max_right _ _
    have hpow'_nonneg : 0 ≤ ‖f x‖ ^ p'.toReal := Real.rpow_nonneg hnorm_nonneg _
    have hpow_nonneg : 0 ≤ ‖f x‖ ^ p.toReal := Real.rpow_nonneg hnorm_nonneg _
    have hfactor_le : ‖f x‖ ^ (p.toReal - p'.toReal) ≤ B ^ (p.toReal - p'.toReal) := by
      exact Real.rpow_le_rpow hnorm_nonneg hx hdiff_nonneg
    have hsplit : (p.toReal - p'.toReal) + p'.toReal = p.toReal := sub_add_cancel _ _
    have hsplit_pow :
        ‖f x‖ ^ p.toReal = ‖f x‖ ^ (p.toReal - p'.toReal) * ‖f x‖ ^ p'.toReal := by
      simpa [hsplit] using
        (Real.rpow_add_of_nonneg hnorm_nonneg hdiff_nonneg ENNReal.toReal_nonneg :
          ‖f x‖ ^ ((p.toReal - p'.toReal) + p'.toReal) =
            ‖f x‖ ^ (p.toReal - p'.toReal) * ‖f x‖ ^ p'.toReal)
    have hpow'_norm : ‖‖f x‖ ^ p'.toReal‖ = ‖f x‖ ^ p'.toReal := by
      rw [Real.norm_eq_abs, abs_of_nonneg hpow'_nonneg]
    calc
      ‖‖f x‖ ^ p.toReal‖ = ‖f x‖ ^ p.toReal := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      _ = ‖f x‖ ^ (p.toReal - p'.toReal) * ‖f x‖ ^ p'.toReal := hsplit_pow
      _ ≤ B ^ (p.toReal - p'.toReal) * ‖f x‖ ^ p'.toReal :=
        mul_le_mul_of_nonneg_right hfactor_le hpow'_nonneg
      _ = B ^ (p.toReal - p'.toReal) * ‖‖f x‖ ^ p'.toReal‖ := by
        rw [hpow'_norm]
  have hpow_div : MemLp (fun x ↦ ‖f x‖ ^ p.toReal) (p / p) μ := by
    simpa [ENNReal.div_self hp_ne_zero hp_top] using hpow_p
  exact
    (memLp_norm_rpow_iff (p := p) (q := p) hf.aestronglyMeasurable hp_ne_zero hp_top).mp
      hpow_div

-- Proof sketch: use the hypothesis that every nonnull measurable set has measure bounded below by
-- a fixed positive constant to control the size of the level sets of `|f|`; this turns the
-- `ℒ^{p'}` summability condition into the stronger `ℒ^p` summability condition, as for sequence
-- spaces with counting measure.
/-- Exercise 4.1.1, canonical `Lp`-space form: if every measurable set has either zero measure or
measure at least some positive constant, then `L^{p'}(μ)` is a subspace of `L^p(μ)` for
`1 ≤ p' ≤ p ≤ ∞`. -/
theorem Lp_le_Lp_of_measure_lower_bound
    {p' p : ENNReal} (hp' : 1 ≤ p') (hp'le : p' ≤ p) :
    Lp ℝ p' μ ≤ Lp ℝ p μ := by
  intro f hf
  -- First upgrade the `L^{p'}` control to an essential bound using the measure hypothesis.
  rcases aeBoundOfMemLpOfMeasureLowerBound hμ hp' hf with ⟨C, _, hfC⟩
  by_cases hp_top : p = ∞
  · -- Once we know `f` is essentially bounded, the `p = ∞` case is immediate.
    refine (Lp.mem_Lp_iff_memLp).2 ?_
    simpa [hp_top] using memLp_top_of_bound f.stronglyMeasurable.aestronglyMeasurable C hfC
  -- For finite `p`, compare `‖f‖^p` with a bounded factor times `‖f‖^{p'}`.
  refine (Lp.mem_Lp_iff_memLp).2 ?_
  exact memLpOfMemLpOfAEBound hp' hp'le hp_top (Lp.mem_Lp_iff_memLp.1 hf) hfC

/-- Exercise 4.1.1 in textbook representative form: if every measurable set has either zero
measure or measure at least some positive constant, then `ℒ^{p'}(μ) ⊆ ℒ^p(μ)` for
`1 ≤ p' ≤ p ≤ ∞`. -/
theorem memLp_of_memLp_of_measure_lower_bound
    {f : Ω → ℝ} {p' p : ENNReal}
    (hp' : 1 ≤ p') (hp'le : p' ≤ p) (hf : MemLp f p' μ) :
    MemLp f p μ := by
  let f' : Lp ℝ p' μ := hf.toLp f
  have hf' : ((f' : Ω →ₘ[μ] ℝ) ∈ Lp ℝ p μ) :=
    Lp_le_Lp_of_measure_lower_bound hμ hp' hp'le f'.2
  exact MemLp.ae_eq hf.coeFn_toLp <| (Lp.mem_Lp_iff_memLp.1 hf')

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_17

open MeasureTheory ProbabilityTheory MeasureTheory.FiniteMeasure
open scoped MeasureTheory ENNReal Topology

noncomputable section

universe u v

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Corollary 24.18: Lebesgue measure on `[0, ∞)` transported to `NNReal`. -/
def nnrealLebesgue : Measure NNReal :=
  Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Helper for Corollary 24.18: the standard Poisson-exponential kernel is bounded by the
truncation kernel `x ↦ min (1, x)` on `[0, ∞)`. -/
lemma one_sub_expNeg_le_min_one (x : ℝ) :
    1 - Real.exp (-x) ≤ min 1 x := by
  -- Proof comment: the tangent-line bound gives the `≤ x` half.
  have hx_le : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  -- Proof comment: positivity of the exponential gives the uniform `≤ 1` half.
  have h_one : 1 - Real.exp (-x) ≤ 1 := by
    have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
    linarith
  exact le_min h_one hx_le

/-- Helper for Corollary 24.18: the small scales `s_n = (n + 1)⁻¹` used in the Laplace limit
argument. -/
def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Corollary 24.18: `ennrealExpNeg` is measurable on `ℝ≥0∞`. -/
lemma measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) := by
    fun_prop
  -- Proof comment: rewrite the definition as a singleton-piecewise function.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (∞ : ℝ≥0∞)) hcore)

/-- Helper for Corollary 24.18: `ennrealExpNeg` is nonnegative. -/
lemma ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ∞
  · -- Proof comment: at `∞` the kernel is exactly `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: away from `∞`, the kernel is an ordinary exponential.
    simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Corollary 24.18: `ennrealExpNeg` is bounded above by `1`. -/
lemma ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ∞
  · -- Proof comment: the `∞` value is `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: on finite inputs the exponent is nonpositive.
    have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Corollary 24.18: small Laplace scales converge pointwise to the finiteness
indicator on `ℝ≥0∞`. -/
lemma ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ∞ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ∞
  · -- Proof comment: positive scales keep `∞` at `∞`, so the sequence is constantly `0`.
    have hconst :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          fun _ ↦ (0 : ℝ) := by
      funext n
      have hn : 0 < (n : ℝ) + 1 := by
        positivity
      have hs_pos : 0 < invSuccScaleReal n := by
        simpa [invSuccScaleReal] using one_div_pos.mpr hn
      have hs_pos' : 0 < ENNReal.ofReal (invSuccScaleReal n) := ENNReal.ofReal_pos.mpr hs_pos
      simp [hy, ennrealExpNeg, ne_of_gt hs_pos']
    rw [hconst]
    simp [hy]
  · -- Proof comment: on finite inputs, continuity of the exponential at `0` gives the limit.
    have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
      change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * y.toReal) Filter.atTop
          (nhds (0 * y.toReal)) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    have hexp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) Filter.atTop
          (nhds (Real.exp (-(0 * y.toReal)))) := by
      exact hcont.continuousAt.tendsto.comp hmul
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) := by
      funext n
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ∞ :=
        ENNReal.mul_ne_top (by simp [invSuccScaleReal]) hy
      have hs_nonneg : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
      change Real.exp (-((ENNReal.ofReal (invSuccScaleReal n)).toReal * y.toReal)) = _
      rw [ENNReal.toReal_ofReal hs_nonneg]
    rw [hrewrite]
    simpa [hy] using hexp

/-- Helper for Corollary 24.18: small-scale Laplace expectations converge to the probability of
the finiteness event. -/
lemma laplaceInvSucc_tendsto_measureFinite
    {β : Type v} [MeasurableSpace β] {μ : Measure β} [IsFiniteMeasure μ] {Y : β → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ∞}).toReal) := by
  let A : Set β := {a | Y a < ∞}
  let G : β → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    -- Proof comment: compose the measurable kernel with the measurable extended-valued variable.
    exact (measurable_ennrealExpNeg.comp (measurable_const.mul hY)).aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ a ∂μ, ‖ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with a
    have hnonneg : 0 ≤ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) :=
      ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ≤ 1 :=
      ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ a ∂μ, Filter.Tendsto
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a))
        Filter.atTop (nhds (G a)) := by
    filter_upwards with a
    by_cases ha : Y a = ∞
    · -- Proof comment: at `∞` the pointwise limit is the zero branch of the indicator.
      simpa [G, A, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · -- Proof comment: on the finite branch, the same limit is `1`.
      have ha' : Y a < ∞ := lt_top_iff_ne_top.mpr ha
      simpa [G, A, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : β ↦ (1 : ℝ)) hF_meas (integrable_const 1) h_bound h_lim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hG_integral : ∫ a, G a ∂μ = (μ A).toReal := by
    -- Proof comment: integrating the indicator of the finiteness event recovers its mass.
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hG_integral] using hDCT

/-- Helper for Corollary 24.18: scaling the Poisson-exponential kernel by `s ≤ 1` preserves the
domination by `x ↦ min (1, x)`. -/
lemma poissonExpKernel_scale_le_minOne
    (s : ℝ) (hs1 : s ≤ 1) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) := by
  -- Proof comment: monotonicity of `min 1 ·` and the bound `s * x ≤ x` do all the work.
  have hmul_le : s * (x : ℝ) ≤ (x : ℝ) := by
    nlinarith [x.2, hs1]
  calc
    1 - Real.exp (-(s * (x : ℝ))) ≤ min 1 (s * (x : ℝ)) := one_sub_expNeg_le_min_one _
    _ ≤ min 1 (x : ℝ) := min_le_min le_rfl hmul_le

/-- Helper for Corollary 24.18: the scaled Poisson-exponential kernel is the `ENNReal` lift of
the ordinary real kernel. -/
lemma poissonLaplaceKernel_scale_eq_ofReal (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (s * (x : ℝ)))) =
      ENNReal.ofReal (1 - Real.exp (-(s * (x : ℝ)))) := by
  have hmul_nonneg : 0 ≤ s * (x : ℝ) := by
    nlinarith [hs, x.2]
  have hExpNonneg : 0 ≤ Real.exp (-(s * (x : ℝ))) := Real.exp_nonneg _
  -- Proof comment: once the `ENNReal` argument is finite, this is only `ofReal_sub`.
  simp [ennrealExpNeg, hmul_nonneg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Corollary 24.18: under truncated first-moment integrability, the small Laplace
exponents converge to `0`. -/
lemma poissonLaplaceExponent_invSucc_tendstoZero
    (ν : Measure NNReal)
    (hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν)
      Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h_meas :
      ∀ n, AEStronglyMeasurable
        (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
    intro n
    have h : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
      fun_prop
    exact h.aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ x : NNReal ∂ν,
        ‖1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))‖ ≤ min (1 : ℝ) (x : ℝ) := by
    intro n
    filter_upwards with x
    have hs1 : invSuccScaleReal n ≤ 1 := by
      have hn : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      have hs0 : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [x.2, hs0]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hle : 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_minOne (invSuccScaleReal n) hs1 x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ x : NNReal ∂ν,
        Filter.Tendsto
          (fun n : ℕ ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) Filter.atTop
          (nhds 0) := by
    filter_upwards with x
    -- Proof comment: for each fixed `x`, the scale tends to `0`, so the kernel tends to `0`.
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * (x : ℝ)) Filter.atTop
          (nhds (0 * (x : ℝ))) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ 1 - Real.exp (-r)) := by
      simpa using continuous_const.sub (Real.continuous_exp.comp continuous_neg)
    simpa using hcont.continuousAt.tendsto.comp hmul
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) h_meas hInt h_bound h_lim

/-- Helper for Corollary 24.18: for `s ≥ 0`, the scaled Bernstein kernel is dominated by
`max (1, s) * min (1, x)`. -/
lemma poissonExpKernel_scale_le_maxMulMinOne
    (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
  by_cases hx1 : (x : ℝ) ≤ 1
  · calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ s * (x : ℝ) := by
        refine le_trans (one_sub_expNeg_le_min_one (s * (x : ℝ))) ?_
        exact min_le_right _ _
      _ ≤ max 1 s * (x : ℝ) := by
        nlinarith [le_max_right 1 s, x.2]
      _ = max 1 s * min (1 : ℝ) (x : ℝ) := by
        rw [min_eq_right hx1]
  · have hx1' : 1 ≤ (x : ℝ) := le_of_not_ge hx1
    calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ 1 := by
        have hpos : 0 < Real.exp (-(s * (x : ℝ))) := Real.exp_pos _
        linarith
      _ ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
        simpa [min_eq_left hx1'] using (le_max_left (1 : ℝ) s)

end MeasureTheory.ProbabilityMeasure

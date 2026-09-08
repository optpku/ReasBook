module

public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped Topology

/-! Stability of nonsummability under a sufficiently small perturbation. -/

/-- A nonnegative, nonsummable sequence stays nonsummable after an asymptotically smaller
perturbation whenever the perturbed sequence is eventually nonnegative. -/
theorem not_summable_of_nonneg_add_isLittleO
    {v r : ℕ → ℝ}
    (hv : ∀ n, 0 ≤ v n)
    (hvr : ∀ᶠ n in atTop, 0 ≤ v n + r n)
    (hsmall : r =o[atTop] v)
    (hdiv : ¬ Summable v) :
    ¬ Summable (fun n ↦ v n + r n) := by
  intro hsum
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have herr : ∀ᶠ n in atTop, |r n| ≤ (1 / 2 : ℝ) * v n := by
    have hbound := hsmall.bound hhalf
    filter_upwards [hbound] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hv n)] using hn
  have hdom : ∀ᶠ n in atTop, ‖v n‖ ≤ (2 : ℝ) * ‖v n + r n‖ := by
    filter_upwards [herr, hvr] with n hn hnonneg
    have hlower : -(1 / 2 : ℝ) * v n ≤ r n := by
      have hbound := neg_le_of_abs_le hn
      linarith
    have hvalue : v n ≤ (2 : ℝ) * (v n + r n) := by
      linarith
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hv n), abs_of_nonneg hnonneg] using hvalue
  have hbig : (fun n ↦ v n) =O[atTop] (fun n ↦ v n + r n) :=
    Asymptotics.IsBigO.of_bound 2 hdom
  exact hdiv (summable_of_isBigO_nat hsum hbig)

/-- A nonnegative sequence remains nonsummable when another sequence eventually
dominates it by a fixed positive factor. -/
theorem not_summable_of_eventually_le_mul
    {v w : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hv : ∀ n, 0 ≤ v n)
    (hvw : ∀ᶠ n in atTop, c * v n ≤ w n)
    (hdiv : ¬ Summable v) :
    ¬ Summable w := by
  intro hsum
  have hnorm : ∀ᶠ n in atTop, ‖v n‖ ≤ c⁻¹ * ‖w n‖ := by
    filter_upwards [hvw] with n hn
    have hscaled_nonneg : 0 ≤ c * v n := mul_nonneg hc.le (hv n)
    have hw_nonneg : 0 ≤ w n := le_trans hscaled_nonneg hn
    have hvalue : v n ≤ c⁻¹ * w n := by
      calc
        v n = c⁻¹ * (c * v n) := by simp [hc.ne']
        _ ≤ c⁻¹ * w n := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hv n), abs_of_nonneg hw_nonneg,
      abs_mul, abs_inv, abs_of_pos hc] using hvalue
  have hbig : (fun n ↦ v n) =O[atTop] (fun n ↦ w n) :=
    Asymptotics.IsBigO.of_bound c⁻¹ hnorm
  exact hdiv (summable_of_isBigO_nat hsum hbig)

/-- A fixed positive lower bound on the terms of a sequence in a complete normed additive
group transfers nonsummability to a real control sequence, without requiring the control
sequence to be pointwise nonnegative. -/
theorem not_summable_of_eventually_norm_mul_le
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {v : ℕ → E} {w : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hvw : ∀ᶠ n in atTop, c * ‖v n‖ ≤ ‖w n‖)
    (hdiv : ¬ Summable v) :
    ¬ Summable w := by
  intro hsum
  have hnorm : ∀ᶠ n in atTop, ‖v n‖ ≤ c⁻¹ * ‖w n‖ := by
    filter_upwards [hvw] with n hn
    calc
      ‖v n‖ = c⁻¹ * (c * ‖v n‖) := by simp [hc.ne']
      _ ≤ c⁻¹ * ‖w n‖ := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)
  have hnorm' : ∀ᶠ n in atTop, ‖v n‖ ≤ c⁻¹ * ‖‖w n‖‖ := by
    simpa only [norm_norm] using hnorm
  have hbig : (fun n ↦ v n) =O[atTop] (fun n ↦ ‖w n‖) :=
    Asymptotics.IsBigO.of_bound c⁻¹ hnorm'
  have hsumNorm : Summable (fun n ↦ ‖w n‖) := by
    simpa only [Real.norm_eq_abs] using hsum.abs
  exact hdiv (summable_of_isBigO_nat hsumNorm hbig)

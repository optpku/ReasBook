/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.PowerMoments
public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace TikhonovEstimation
namespace PowerRisk
lemma moment_scaling {p s c x : ℝ} {j : ℕ} (hc : 0 < c) (hp : 0 < p) (hx : 0 < x) :
    moment p j s (x / c) =
      c ^ ((s + 1) / p) * x ^ (-((s + 1) / p)) *
        KernelMoment.quadratureSeries p j s ((x / c) ^ (1 / p)) := by
  have hxc := div_pos hx hc
  have hh : 0 < (x / c) ^ (1 / p) := Real.rpow_pos_of_pos hxc _
  have hpow : ((x / c) ^ (1 / p)) ^ p = x / c := by
    rw [← Real.rpow_mul hxc.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  rw [← hpow, moment_eq_quadrature hh]
  rw [hpow]
  congr 1
  rw [← Real.rpow_mul hxc.le,
    show (1 / p) * (-s - 1) = -((s + 1) / p) by ring,
    Real.div_rpow hx.le hc.le, Real.rpow_neg hc.le ((s + 1) / p), div_inv_eq_mul]
  ring

lemma normalized_moment_tendsto {α : ℕ → ℝ} {p s c : ℝ} {j : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hs : -1 < s)
    (hd : 0 < (j : ℝ) * p - s - 1)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ (α n) ^ ((s + 1) / p) * moment p j s (α n / c)) atTop
      (𝓝 (c ^ ((s + 1) / p) * KernelMoment.integral p j s)) := by
  have ht := (quadrature_tendsto hs hd (step_tendsto hc hp hα hαpos)).const_mul
    (c ^ ((s + 1) / p))
  apply ht.congr'
  filter_upwards [hαpos] with n hn
  rw [moment_scaling hc hp hn]
  have hcancel : α n ^ ((s + 1) / p) * α n ^ (-((s + 1) / p)) = 1 := by
    rw [← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero]
  symm
  calc
    _ = (α n ^ ((s + 1) / p) * α n ^ (-((s + 1) / p))) *
        (c ^ ((s + 1) / p) * KernelMoment.quadratureSeries p j s ((α n / c) ^ (1 / p))) := by ring
    _ = _ := by rw [hcancel, one_mul]

lemma negLog_tendsto {α : ℕ → ℝ} (hα : Tendsto α atTop (𝓝 0))
    (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ -Real.log (α n)) atTop atTop := by
  exact tendsto_neg_atBot_atTop.comp
    (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hα, hαpos⟩))

lemma critical_moment_tendsto {α : ℕ → ℝ} {c p : ℝ} {j : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hj : 0 < (j : ℝ) * p)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ moment p j (-1) (α n / c) / (-Real.log (α n)))
      atTop (𝓝 (1 / p)) := by
  let h : ℕ → ℝ := fun n ↦ (α n / c) ^ (1 / p)
  let l : Filter (ℕ × ℝ) := map (fun n ↦ (0, h n)) atTop
  have hh : Tendsto Prod.snd l (𝓝[>] 0) := by
    simpa [l, h, Filter.tendsto_map'_iff, Function.comp_def] using! step_tendsto hc hp hα hαpos
  have hb := (KernelMoment.quadratureSeriesLogGap_isBigO hj hh).comp_tendsto
    (tendsto_map : Tendsto (fun n ↦ (0, h n)) atTop l)
  have hlog := negLog_tendsto hα hαpos
  have ho : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] (fun n ↦ -Real.log (α n)) := by
    exact isLittleO_one_left_iff ℝ |>.2 (tendsto_norm_atTop_atTop.comp hlog)
  have hrem : Tendsto (fun n ↦ (KernelMoment.quadratureSeries p j (-1) (h n) +
      Real.log (h n)) / (-Real.log (α n))) atTop (𝓝 0) := by
    exact (hb.trans_isLittleO ho).tendsto_div_nhds_zero
  have hinv : Tendsto (fun n ↦ (1 : ℝ) / (-Real.log (α n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using! (tendsto_inv_atTop_zero.comp hlog)
  have ht := hrem.add ((hinv.const_mul ((1 / p) * Real.log c)).add_const (1 / p))
  simp only [mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [hαpos, hlog.eventually (eventually_gt_atTop 0)] with n hn hln
  have hm : moment p j (-1) (α n / c) = KernelMoment.quadratureSeries p j (-1) (h n) := by
    rw [moment_scaling hc hp hn]
    simp only [neg_add_cancel, zero_div, neg_zero, Real.rpow_zero, one_mul]
    rfl
  have hl : Real.log (h n) = (1 / p) * (Real.log (α n) - Real.log c) := by
    dsimp [h]
    rw [Real.log_rpow (div_pos hn hc), Real.log_div hn.ne' hc.ne']
  rw [hm, hl]
  field_simp [hp.ne', ne_of_lt (neg_pos.1 hln)]
  ring

lemma source_pos {b c p q : ℝ} (hb : 0 < b) (hc : 0 < c) (hs : 2 * p - q < -1) :
    0 < source b c p q := by
  have hsum : Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ (2 * p - q)) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Real.summable_nat_rpow.2 hs).comp_injective Nat.succ_injective
  apply mul_pos (div_pos hb (sq_pos_of_pos hc))
  exact hsum.tsum_pos (fun k ↦ Real.rpow_nonneg (by positivity) _) 0 (by simp)
@[expose] def biasFactor (b c p q : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (b / c ^ 2) * moment p j (2 * p - q) (x / c)

@[expose] def biasConstant (b c p q : ℝ) (j : ℕ) : ℝ :=
  b * c ^ (-(q - 1) / p) * KernelMoment.integral p j (2 * p - q)

@[expose] def varianceConstant (c p : ℝ) (j : ℕ) : ℝ :=
  c ^ (1 / p) * KernelMoment.integral p j (((j : ℝ) - 1) * p)

lemma variance_scale {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (j : ℕ) :
    c / c ^ j * c ^ ((((j : ℝ) - 1) * p + 1) / p) = c ^ (1 / p) := by
  have heq : c / c ^ j = c ^ (1 - (j : ℝ)) := by
    rw [Real.rpow_sub hc, Real.rpow_one, Real.rpow_natCast]
  rw [heq, ← Real.rpow_add hc]
  congr 1
  field_simp
  ring

lemma bias_scale {b c p q : ℝ} (hc : 0 < c) (hp : 0 < p) :
    (b / c ^ 2) * c ^ ((2 * p - q + 1) / p) = b * c ^ (-(q - 1) / p) := by
  have heq : (c ^ 2)⁻¹ = c ^ (-2 : ℝ) := by rw [Real.rpow_neg hc.le, Real.rpow_two]
  rw [div_eq_mul_inv, mul_assoc, heq, ← Real.rpow_add hc]
  congr 2
  field_simp
  ring

lemma bias_normalized_tendsto {α : ℕ → ℝ} {b c p q : ℝ} {j : ℕ}
    (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hj : j = 2 ∨ j = 3)
    (hs : -1 < 2 * p - q)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ (α n) ^ ((2 * p - q + 1) / p) * biasFactor b c p q j (α n))
      atTop (𝓝 (biasConstant b c p q j)) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < (j : ℝ) * p - (2 * p - q) - 1 := by
    rcases hj with rfl | rfl <;> norm_num <;> linarith
  have ht := (normalized_moment_tendsto hc hp0 hs hd hα hαpos).const_mul (b / c ^ 2)
  rw [← mul_assoc, bias_scale hc hp0] at ht
  simpa only [biasFactor, biasConstant, mul_left_comm (b / c ^ 2)] using ht

lemma variance_normalized_tendsto {α : ℕ → ℝ} {c p : ℝ} {j : ℕ}
    (hc : 0 < c) (hp : 1 < p) (hj : j = 2 ∨ j = 3)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ (α n) ^ ((((j : ℝ) - 1) * p + 1) / p) *
      SeriesRisk.varianceMoment (eigenvalue c p) j (α n)) atTop
      (𝓝 (varianceConstant c p j)) := by
  have hp0 : 0 < p := by linarith
  have hs : -1 < ((j : ℝ) - 1) * p := by
    rcases hj with rfl | rfl <;> norm_num <;> linarith
  have hd : 0 < (j : ℝ) * p - (((j : ℝ) - 1) * p) - 1 := by nlinarith
  have ht := (normalized_moment_tendsto hc hp0 hs hd hα hαpos).const_mul (c / c ^ j)
  rw [← mul_assoc, variance_scale hc hp0] at ht
  simpa only [varianceMoment_eq hc j hj, varianceConstant, mul_left_comm (c / c ^ j)] using ht

lemma bias_critical_tendsto {α : ℕ → ℝ} {b c p q : ℝ} {j : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hj : 0 < (j : ℝ) * p) (hs : 2 * p - q = -1)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ biasFactor b c p q j (α n) / (-Real.log (α n)))
      atTop (𝓝 (b / (c ^ 2 * p))) := by
  have ht := (critical_moment_tendsto hc hp hj hα hαpos).const_mul (b / c ^ 2)
  simpa only [biasFactor, hs, mul_div_assoc, div_mul_eq_div_div, mul_one, mul_one_div] using ht

lemma bias_saturated_tendsto {α : ℕ → ℝ} {b c p q : ℝ} {j : ℕ}
    (hc : 0 < c) (hs : 2 * p - q < -1) (hα : Tendsto α atTop (𝓝 0))
    (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ biasFactor b c p q j (α n)) atTop (𝓝 (source b c p q)) := by
  have hρ : Tendsto (fun n ↦ α n / c) atTop (𝓝 0) := by simpa using hα.div_const c
  have hρpos : ∀ᶠ n in atTop, 0 ≤ α n / c :=
    hαpos.mono fun n hn ↦ (div_pos hn hc).le
  exact (moment_saturated_tendsto hs hρ hρpos).const_mul (b / c ^ 2)

end PowerRisk
end TikhonovEstimation

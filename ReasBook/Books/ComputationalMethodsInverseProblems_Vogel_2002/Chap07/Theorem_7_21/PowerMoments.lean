/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_19
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.SeriesRisk
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace TikhonovEstimation
namespace PowerRisk

@[expose] def coeff (b q : ℝ) (k : ℕ) : ℝ := b * ((k : ℝ) + 1) ^ (-q)
@[expose] def eigenvalue (c p : ℝ) (k : ℕ) : ℝ := c * ((k : ℝ) + 1) ^ (-p)
@[expose] def moment (p : ℝ) (j : ℕ) (s ρ : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 1) ^ s / (1 + ρ * ((k : ℝ) + 1) ^ p) ^ j

@[expose] def source (b c p q : ℝ) : ℝ :=
  (b / c ^ 2) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (2 * p - q)

lemma coeff_summable {b q : ℝ} (hq : 1 < q) : Summable (coeff b q) := by
  exact ((Real.summable_nat_rpow.2 (by linarith : -q < -1)).comp_injective
    Nat.succ_injective |>.congr (fun k ↦ by simp [Nat.cast_add, Nat.cast_one])).mul_left b

lemma eigenvalue_summable {c p : ℝ} (hp : 1 < p) : Summable (eigenvalue c p) :=
  coeff_summable hp

lemma eigenvalue_le {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (k : ℕ) :
    eigenvalue c p k ≤ c := by
  dsimp [eigenvalue]
  have ht : ((k : ℝ) + 1) ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)
  nlinarith

lemma moment_eq_quadrature {p s h : ℝ} {j : ℕ} (hh : 0 < h) :
    moment p j s (h ^ p) = h ^ (-s - 1) * KernelMoment.quadratureSeries p j s h := by
  unfold moment KernelMoment.quadratureSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hr : h ^ (-s - 1) * (h * h ^ s) = 1 := by
    calc
      _ = h ^ (-s - 1) * (h ^ (1 : ℝ) * h ^ s) := by rw [Real.rpow_one]
      _ = h ^ ((-s - 1) + (1 + s)) := by rw [Real.rpow_add hh, Real.rpow_add hh]
      _ = 1 := by rw [show (-s - 1) + (1 + s) = 0 by ring, Real.rpow_zero]
  simp only [KernelMoment.integrand_def, Nat.cast_add, Nat.cast_one]
  rw [Real.mul_rpow hk.le hh.le, Real.mul_rpow hk.le hh.le]
  rw [show h ^ p * ((k : ℝ) + 1) ^ p = ((k : ℝ) + 1) ^ p * h ^ p by ring]
  symm
  calc
    _ = (h ^ (-s - 1) * (h * h ^ s)) *
        (((k : ℝ) + 1) ^ s / (1 + ((k : ℝ) + 1) ^ p * h ^ p) ^ j) := by ring
    _ = _ := by rw [hr, one_mul]

lemma step_tendsto {α : ℕ → ℝ} {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ (α n / c) ^ (1 / p)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have hdiv : Tendsto (fun n ↦ α n / c) atTop (𝓝 0) := by simpa using hα.div_const c
    have ht := hdiv.rpow_const (p := 1 / p) (Or.inr (one_div_pos.2 hp).le)
    simpa only [Real.zero_rpow (ne_of_gt (one_div_pos.2 hp))] using ht
  · exact hαpos.mono fun n hn ↦ Real.rpow_pos_of_pos (div_pos hn hc) _

lemma quadrature_tendsto {α : ℕ → ℝ} {p s : ℝ} {j : ℕ}
    (hs : -1 < s) (hd : 0 < (j : ℝ) * p - s - 1)
    (hα : Tendsto α atTop (𝓝[>] 0)) :
    Tendsto (fun n ↦ KernelMoment.quadratureSeries p j s (α n)) atTop
      (𝓝 (KernelMoment.integral p j s)) := by
  let l : Filter (ℕ × ℝ) := Filter.map (fun n ↦ (0, α n)) atTop
  have hh : Tendsto Prod.snd l (𝓝[>] 0) := by simpa [l, Filter.tendsto_map'_iff, Function.comp_def] using! hα
  have ht : Tendsto (fun n ↦ KernelMoment.quadratureSeries p j s (α n) -
      KernelMoment.integral p j s) atTop (𝓝 0) := by
    by_cases hs0 : 0 < s
    · have hb := (KernelMoment.quadratureSeriesGap_pos_isBigO hd hs0 hh).comp_tendsto
        (tendsto_map : Tendsto (fun n ↦ (0, α n)) atTop l)
      exact hb.trans_tendsto (tendsto_nhds_of_tendsto_nhdsWithin hα)
    · have hb := (KernelMoment.quadratureSeriesGap_nonpos_isBigO hd hs (le_of_not_gt hs0) hh).comp_tendsto
        (tendsto_map : Tendsto (fun n ↦ (0, α n)) atTop l)
      have hpow := (tendsto_nhds_of_tendsto_nhdsWithin hα).rpow_const
        (p := s + 1) (Or.inr (by linarith))
      apply hb.trans_tendsto
      simpa [Function.comp_def, Real.zero_rpow (by linarith : s + 1 ≠ 0)] using! hpow
  simpa using ht.add_const (KernelMoment.integral p j s)

lemma moment_saturated_tendsto {α : ℕ → ℝ} {p s : ℝ} {j : ℕ}
    (hs : s < -1) (hα : Tendsto α atTop (𝓝 0))
    (hαpos : ∀ᶠ n in atTop, 0 ≤ α n) :
    Tendsto (fun n ↦ moment p j s (α n)) atTop
      (𝓝 (∑' k : ℕ, ((k : ℝ) + 1) ^ s)) := by
  have hsum : Summable (fun k : ℕ ↦ ((k : ℝ) + 1) ^ s) := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Real.summable_nat_rpow.2 hs).comp_injective Nat.succ_injective
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro k
    have ht := (tendsto_const_nhds (x := ((k : ℝ) + 1) ^ s) (f := atTop)).div (((hα.mul_const (((k : ℝ) + 1) ^ p)).const_add 1).pow j)
      (by simp)
    simpa using! ht
  · filter_upwards [hαpos] with n hn k
    have hk : 0 < (k : ℝ) + 1 := by positivity
    have hden : 1 ≤ 1 + α n * ((k : ℝ) + 1) ^ p := by
      linarith [mul_nonneg hn (Real.rpow_nonneg hk.le p)]
    have hpow : 1 ≤ (1 + α n * ((k : ℝ) + 1) ^ p) ^ j := one_le_pow₀ hden
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (Real.rpow_nonneg hk.le s) hpow
lemma biasMoment_eq {b c p q x : ℝ} (hc : 0 < c) :
    SeriesRisk.biasMoment (coeff b q) (eigenvalue c p) x =
      (b / c ^ 2) * moment p 3 (2 * p - q) (x / c) := by
  unfold SeriesRisk.biasMoment moment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hi : 0 < (k : ℝ) + 1 := by positivity
  have hz : ((k : ℝ) + 1) ^ p ≠ 0 := (Real.rpow_pos_of_pos hi _).ne'
  have hpw : ((k : ℝ) + 1) ^ (2 * p - q) =
      ((k : ℝ) + 1) ^ (-q) * (((k : ℝ) + 1) ^ p) ^ 2 := by
    rw [← Real.rpow_mul_natCast hi.le, ← Real.rpow_add hi]
    congr 1
    ring
  dsimp [coeff, eigenvalue]
  rw [Real.rpow_neg hi.le p, hpw]
  field_simp

lemma varianceMoment_eq {c p x : ℝ} (hc : 0 < c) (j : ℕ) (hj : j = 2 ∨ j = 3) :
    SeriesRisk.varianceMoment (eigenvalue c p) j x =
      (c / c ^ j) * moment p j (((j : ℝ) - 1) * p) (x / c) := by
  unfold SeriesRisk.varianceMoment moment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hi : 0 < (k : ℝ) + 1 := by positivity
  have hz : ((k : ℝ) + 1) ^ p ≠ 0 := (Real.rpow_pos_of_pos hi _).ne'
  have hpw : ((k : ℝ) + 1) ^ (((j : ℝ) - 1) * p) =
      (((k : ℝ) + 1) ^ p) ^ j / ((k : ℝ) + 1) ^ p := by
    rw [sub_mul, one_mul, Real.rpow_sub hi, mul_comm (j : ℝ) p,
      Real.rpow_mul hi.le, Real.rpow_natCast]
  dsimp [eigenvalue]
  rw [Real.rpow_neg hi.le p, hpw]
  rcases hj with rfl | rfl <;> field_simp

lemma risk_eq {b c p q δ x : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hp : 1 < p) (hq : 1 < q) (hx : 0 < x) :
    SeriesRisk.risk (coeff b q) (eigenvalue c p) δ x =
      x ^ 2 * (b / c ^ 2) * moment p 2 (2 * p - q) (x / c) +
        δ * SeriesRisk.varianceMoment (eigenvalue c p) 2 x := by
  have ha : ∀ k, 0 ≤ coeff b q k := fun k ↦ by dsimp [coeff]; positivity
  have hd : ∀ k, 0 ≤ eigenvalue c p k := fun k ↦ by dsimp [eigenvalue]; positivity
  have hsa := coeff_summable (b := b) hq
  have hsd := eigenvalue_summable (c := c) hp
  have hba : Summable (fun k ↦ coeff b q k / (eigenvalue c p k + x) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k ↦ div_nonneg (ha k) (sq_nonneg _))
      (fun k ↦ ?_) (hsa.div_const (x ^ 2))
    exact div_le_div_of_nonneg_left (ha k) (sq_pos_of_pos hx)
      (pow_le_pow_left₀ hx.le (by linarith [hd k]) 2)
  have hbeq : (∑' k, coeff b q k / (eigenvalue c p k + x) ^ 2) =
      (b / c ^ 2) * moment p 2 (2 * p - q) (x / c) := by
    unfold moment
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hi : 0 < (k : ℝ) + 1 := by positivity
    have hpw : ((k : ℝ) + 1) ^ (2 * p - q) =
        ((k : ℝ) + 1) ^ (-q) * (((k : ℝ) + 1) ^ p) ^ 2 := by
      rw [← Real.rpow_mul_natCast hi.le, ← Real.rpow_add hi]
      congr 1
      ring
    dsimp [coeff, eigenvalue]
    rw [Real.rpow_neg hi.le p, hpw]
    field_simp
  unfold SeriesRisk.risk
  simp_rw [add_div, mul_div_assoc]
  rw [(hba.mul_left (x ^ 2)).tsum_add
    ((SeriesRisk.summable_varianceMoment hd hsd hx 2).mul_left δ),
    tsum_mul_left, tsum_mul_left, hbeq]
  simp only [SeriesRisk.varianceMoment, mul_assoc]

lemma integral_pos {p s : ℝ} {j : ℕ} (hp : 0 < p)
    (hs : -1 < s) (hd : 0 < (j : ℝ) * p - s - 1) :
    0 < KernelMoment.integral p j s := by
  rw [KernelMoment.integral_eq_gamma_mul_gamma_div_gamma (by linarith) hd]
  have hj : 0 < (j : ℝ) := by nlinarith
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (div_pos hd hp))
    (Real.Gamma_pos_of_pos (div_pos (by linarith) hp)))
    (mul_pos hp (Real.Gamma_pos_of_pos hj))

end PowerRisk
end TikhonovEstimation

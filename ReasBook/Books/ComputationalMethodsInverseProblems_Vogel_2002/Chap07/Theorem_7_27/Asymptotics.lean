/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.RateCalculus
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.Minimizer
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_27.Benchmark
public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace TikhonovDiscrepancy
namespace SequenceModel
open TikhonovEstimation TikhonovEstimation.PowerRisk

/-- Signal contribution to the squared residual after the noise baseline is removed. -/
@[expose] def bias (b c p q x : ℝ) : ℝ :=
  ∑' k, coeff b q k * eigenvalue c p k / (eigenvalue c p k + x) ^ 2

/-- Noise removed by the Tikhonov filter, relative to the unfiltered baseline. -/
@[expose] def noise (c p x : ℝ) : ℝ :=
  ∑' k, eigenvalue c p k * (2 * x + eigenvalue c p k) /
    (eigenvalue c p k + x) ^ 2

/-- Exact renormalized discrepancy balance for the power-law sequence model.
This hypothesis concerns convergent scalar series; it does not posit an
infinite Hilbert-space white-noise vector. Only positive tail indices matter. -/
@[expose] def HasBalance (b c p q σ : ℝ) (α : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, 0 < α n ∧
    α n ^ 2 * bias b c p q (α n) = noiseLevel σ n * noise c p (α n)

lemma summable_bias {b c p q x : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hp : 1 < p) (hq : 1 < q) (hx : 0 < x) :
    Summable (fun k ↦ coeff b q k * eigenvalue c p k /
      (eigenvalue c p k + x) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k ↦ by dsimp [coeff, eigenvalue]; positivity)
    (fun k ↦ ?_) ((coeff_summable (b := b) hq).mul_left (c / x ^ 2))
  have ha : 0 ≤ coeff b q k := by dsimp [coeff]; positivity
  have hd : 0 ≤ eigenvalue c p k := by dsimp [eigenvalue]; positivity
  have hdc := eigenvalue_le hc (by linarith : 0 < p) k
  calc
    _ ≤ coeff b q k * c / x ^ 2 := by gcongr; linarith
    _ = _ := by ring

lemma noise_term_bound {d x : ℝ} (hd : 0 ≤ d) (hx : 0 < x) :
    d * (2 * x + d) / (d + x) ^ 2 ≤ (2 / x) * d := by
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < d + x))).2
  have hm : d * (2 * x + d) * x ≤ 2 * d * (d + x) ^ 2 := by
    nlinarith [mul_nonneg hd (sq_nonneg d), mul_nonneg (sq_nonneg d) hx.le]
  apply (mul_le_mul_iff_left₀ hx).1
  convert! hm using 1
  field_simp

lemma summable_noise {c p x : ℝ} (hc : 0 < c) (hp : 1 < p) (hx : 0 < x) :
    Summable (fun k ↦ eigenvalue c p k * (2 * x + eigenvalue c p k) /
      (eigenvalue c p k + x) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k ↦ by dsimp [eigenvalue]; positivity)
    (fun k ↦ noise_term_bound (by dsimp [eigenvalue]; positivity) hx)
    ((eigenvalue_summable (c := c) hp).mul_left (2 / x))

lemma balance_tendsto_zero {b c p q σ : ℝ} {α : ℕ → ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q)
    (hbal : HasBalance b c p q σ α) : Tendsto α atTop (𝓝 0) := by
  have hα := hbal.mono fun _ h ↦ h.1
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact hα.mono fun _ hn ↦ hε.trans hn
  · intro ε hε
    let L := ε * b * c * (ε / (c + ε)) ^ 2
    have hL : 0 < L := by dsimp [L]; positivity
    have hsmall : ∀ᶠ n in atTop,
        2 * noiseLevel σ n * (∑' k, eigenvalue c p k) < L := by
      have ht := (noiseLevel_tendsto σ).const_mul 2 |>.mul_const
        (∑' k, eigenvalue c p k)
      simp only [mul_zero, zero_mul] at ht
      exact ht.eventually (gt_mem_nhds hL)
    filter_upwards [hbal, hsmall] with n hn hsmalln
    obtain ⟨hn, hbn⟩ := hn
    by_contra hnlt
    have hεn : ε ≤ α n := le_of_not_gt hnlt
    have hB : b * c / (c + α n) ^ 2 ≤ bias b c p q (α n) := by
      simpa only [coeff, eigenvalue, bias, Nat.cast_zero, zero_add, Real.one_rpow, mul_one] using
        (summable_bias hb hc hp hq hn).le_tsum 0
          (fun k _ ↦ by dsimp [coeff, eigenvalue]; positivity)
    have hV : noise c p (α n) ≤ (2 / α n) * (∑' k, eigenvalue c p k) := by
      rw [noise, ← tsum_mul_left]
      exact (summable_noise hc hp hn).tsum_le_tsum
        (fun k ↦ noise_term_bound (by dsimp [eigenvalue]; positivity) hn)
        ((eigenvalue_summable (c := c) hp).mul_left _)
    have hbound : α n ^ 2 * (b * c / (c + α n) ^ 2) ≤
        noiseLevel σ n * ((2 / α n) * (∑' k, eigenvalue c p k)) := by
      calc
        _ ≤ α n ^ 2 * bias b c p q (α n) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
        _ = noiseLevel σ n * noise c p (α n) := hbn
        _ ≤ _ := mul_le_mul_of_nonneg_left hV (noiseLevel_nonneg σ n)
    have hr : ε / (c + ε) ≤ α n / (c + α n) := by
      apply (div_le_div_iff₀ (by positivity : 0 < c + ε)
        (by positivity : 0 < c + α n)).2
      nlinarith
    have hLbound : L ≤ α n * b * c * (α n / (c + α n)) ^ 2 := by
      dsimp [L]
      gcongr
    have hbound' : α n * b * c * (α n / (c + α n)) ^ 2 ≤
        2 * noiseLevel σ n * (∑' k, eigenvalue c p k) := by
      have hm := mul_le_mul_of_nonneg_right hbound hn.le
      convert! hm using 1 <;> field_simp
    exact (not_lt_of_ge (hLbound.trans hbound')) hsmalln

lemma bias_eq {b c p q x : ℝ} (hc : 0 < c) :
    bias b c p q x = (b / c) * moment p 2 (p - q) (x / c) := by
  unfold bias moment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hi : 0 < (k : ℝ) + 1 := by positivity
  have hz : ((k : ℝ) + 1) ^ p ≠ 0 := (Real.rpow_pos_of_pos hi _).ne'
  have hpw : ((k : ℝ) + 1) ^ (p - q) =
      ((k : ℝ) + 1) ^ (-q) * ((k : ℝ) + 1) ^ p := by
    rw [← Real.rpow_add hi]
    congr 1
    ring
  dsimp [coeff, eigenvalue]
  rw [Real.rpow_neg hi.le p, hpw]
  field_simp

lemma noise_eq {c p x : ℝ} (hc : 0 < c) (hp : 1 < p) (hx : 0 < x) :
    noise c p x = 2 * (x / c) * moment p 2 p (x / c) + moment p 2 0 (x / c) := by
  have hd : ∀ k, 0 ≤ eigenvalue c p k := fun k ↦ by dsimp [eigenvalue]; positivity
  have hsd := eigenvalue_summable (c := c) hp
  have hs₁ := SeriesRisk.summable_varianceMoment hd hsd hx 2
  have hs₂ : Summable (fun k ↦ eigenvalue c p k ^ 2 / (eigenvalue c p k + x) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
      (hs₁.mul_left c)
    have hk := hd k
    have hkc := eigenvalue_le hc (by linarith : 0 < p) k
    have hden : 0 < (eigenvalue c p k + x) ^ 2 := by positivity
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hden).2 (by nlinarith)
  have hsplit : noise c p x = 2 * x * SeriesRisk.varianceMoment (eigenvalue c p) 2 x +
      ∑' k, eigenvalue c p k ^ 2 / (eigenvalue c p k + x) ^ 2 := by
    unfold noise SeriesRisk.varianceMoment
    simp_rw [show ∀ k, eigenvalue c p k * (2 * x + eigenvalue c p k) /
      (eigenvalue c p k + x) ^ 2 = 2 * x *
      (eigenvalue c p k / (eigenvalue c p k + x) ^ 2) +
      eigenvalue c p k ^ 2 / (eigenvalue c p k + x) ^ 2 by intro k; ring]
    rw [((hs₁.mul_left _).tsum_add hs₂), tsum_mul_left]
  rw [hsplit, varianceMoment_eq hc 2 (Or.inl rfl)]
  have h₂ : (∑' k, eigenvalue c p k ^ 2 / (eigenvalue c p k + x) ^ 2) =
      moment p 2 0 (x / c) := by
    apply tsum_congr
    intro k
    have hi : 0 < (k : ℝ) + 1 := by positivity
    have hz : ((k : ℝ) + 1) ^ p ≠ 0 := (Real.rpow_pos_of_pos hi _).ne'
    dsimp [eigenvalue]
    rw [Real.rpow_neg hi.le p, Real.rpow_zero]
    field_simp
  rw [h₂]
  norm_num
  field_simp

@[expose] def noiseConstant (c p : ℝ) : ℝ :=
  c ^ (1 / p) * (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)

lemma noiseConstant_pos {c p : ℝ} (hc : 0 < c) (hp : 1 < p) :
    0 < noiseConstant c p := by
  have h₁ := integral_pos (p := p) (s := p) (j := 2) (by linarith : 0 < p)
    (by linarith) (by norm_num; linarith)
  have h₀ := integral_pos (p := p) (s := 0) (j := 2) (by linarith : 0 < p)
    (by norm_num) (by norm_num; linarith)
  change 0 < c ^ (1 / p) * (2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0)
  exact mul_pos (Real.rpow_pos_of_pos hc _) (by linarith)

lemma noise_normalized_tendsto {c p : ℝ} {α : ℕ → ℝ}
    (hc : 0 < c) (hp : 1 < p)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ α n ^ (1 / p) * noise c p (α n)) atTop
      (𝓝 (noiseConstant c p)) := by
  have hp0 : 0 < p := by linarith
  have h₁ := normalized_moment_tendsto (j := 2) (s := p) hc hp0
    (by linarith) (by norm_num; linarith) hα hαpos
  have h₀ := normalized_moment_tendsto (j := 2) (s := 0) hc hp0
    (by norm_num) (by norm_num; linarith) hα hαpos
  have hscale : (2 / c) * c ^ ((p + 1) / p) = 2 * c ^ (1 / p) := by
    rw [show (p + 1) / p = 1 + 1 / p by field_simp, Real.rpow_add hc, Real.rpow_one]
    field_simp
  have ht := (h₁.const_mul (2 / c)).add h₀
  rw [← mul_assoc, hscale] at ht
  have hconst : 2 * c ^ (1 / p) * KernelMoment.integral p 2 p +
      c ^ ((0 + 1) / p) * KernelMoment.integral p 2 0 = noiseConstant c p := by
    dsimp [noiseConstant]
    norm_num
    ring
  rw [hconst] at ht
  apply ht.congr'
  filter_upwards [hαpos] with n hn
  rw [noise_eq hc hp hn]
  have hpow : α n ^ ((p + 1) / p) = α n ^ (1 / p) * α n := by
    rw [show (p + 1) / p = 1 / p + 1 by field_simp; ring,
      Real.rpow_add hn, Real.rpow_one]
  rw [hpow]
  norm_num
  ring

/-- The noise side divided by one parameter factor, matching the generic balance calculus. -/
lemma divided_noise_tendsto {c p : ℝ} {α : ℕ → ℝ}
    (hc : 0 < c) (hp : 1 < p)
    (hα : Tendsto α atTop (𝓝 0)) (hαpos : ∀ᶠ n in atTop, 0 < α n) :
    Tendsto (fun n ↦ α n ^ (1 + 1 / p) * (noise c p (α n) / α n)) atTop
      (𝓝 (noiseConstant c p)) := by
  apply (noise_normalized_tendsto hc hp hα hαpos).congr'
  filter_upwards [hαpos] with n hn
  rw [Real.rpow_add hn, Real.rpow_one]
  field_simp

lemma divided_balance {b c p q σ : ℝ} {α : ℕ → ℝ}
    (hbal : HasBalance b c p q σ α) :
    ∀ᶠ n in atTop, α n * bias b c p q (α n) =
      noiseLevel σ n * (noise c p (α n) / α n) := by
  filter_upwards [hbal] with n hn
  rw [← mul_div_assoc]
  apply (eq_div_iff hn.1.ne').2
  nlinarith [hn.2]

lemma nonsaturated {b c p q σ : ℝ} {α : ℕ → ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hs : -1 < p - q) (hbal : HasBalance b c p q σ α) :
    α ~[atTop] nonsaturatedParameterBenchmark b c p q σ := by
  have hp0 : 0 < p := by linarith
  have hα := balance_tendsto_zero hb hc hp hq hbal
  have hαpos := hbal.mono fun _ h ↦ h.1
  let u := (p - q + 1) / p
  let D := (b / c) * c ^ u * KernelMoment.integral p 2 (p - q)
  have hI : 0 < KernelMoment.integral p 2 (p - q) :=
    integral_pos hp0 hs (by norm_num; linarith)
  have hD : 0 < D := mul_pos (mul_pos (div_pos hb hc) (Real.rpow_pos_of_pos hc _)) hI
  have hB : Tendsto (fun n ↦ α n ^ u * bias b c p q (α n)) atTop (𝓝 D) := by
    have ht := (normalized_moment_tendsto (j := 2) hc hp0 hs
      (by norm_num; linarith) hα hαpos).const_mul (b / c)
    simpa only [bias_eq hc, u, D, mul_assoc, mul_left_comm (b / c)] using ht
  have he : 1 + (1 + 1 / p) - u = (p + q) / p := by dsimp [u]; field_simp; ring
  have hexp : 1 / ((p + q) / p) = p / (p + q) := by field_simp
  have ht := rate_of_balance (u := u) (v := 1 + 1 / p)
    (by rw [he]; exact (div_pos (by linarith) hp0).ne')
    (noiseConstant_pos hc hp) hD (noiseLevel_nonneg σ) (noiseLevel_eventuallyPos hσ)
    hαpos hB (divided_noise_tendsto hc hp hα hαpos) (divided_balance hbal)
  rw [he, hexp] at ht
  have hbase : noiseConstant c p / D =
      ((2 * KernelMoment.integral p 2 p + KernelMoment.integral p 2 0) /
        KernelMoment.integral p 2 (p - q)) * (c ^ (q / p) / b) := by
    have hpow : c ^ (q / p) * c ^ u = c * c ^ (1 / p) := by
      calc
        _ = c ^ (q / p + u) := (Real.rpow_add hc _ _).symm
        _ = c ^ (1 + 1 / p) := by
          congr 1
          dsimp [u]
          field_simp
          ring
        _ = c * c ^ (1 / p) := by rw [Real.rpow_add hc, Real.rpow_one]
    change (c ^ (1 / p) * (2 * KernelMoment.integral p 2 p +
      KernelMoment.integral p 2 0)) / ((b / c) * c ^ u * KernelMoment.integral p 2 (p - q)) = _
    field_simp [hI.ne', hb.ne', hc.ne', (Real.rpow_pos_of_pos hc u).ne']
    nlinarith [congrArg (fun t : ℝ ↦ t * (2 * KernelMoment.integral p 2 p +
      KernelMoment.integral p 2 0)) hpow]
  rw [hbase] at ht
  change α ~[atTop] (fun n ↦ parameterConstant1 b c p q * (σ ^ 2 / (n : ℝ)) ^ (p / (p + q)))
  rw [parameterConstant1_def]
  exact ht

lemma critical {b c p q σ : ℝ} {α : ℕ → ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hs : p - q = -1) (hbal : HasBalance b c p q σ α) :
    α ~[atTop] betaDiscrep b c p σ := by
  have hp0 : 0 < p := by linarith
  have hα := balance_tendsto_zero hb hc hp hq hbal
  have hαpos := hbal.mono fun _ h ↦ h.1
  have hB : Tendsto (fun n ↦ bias b c p q (α n) / (-Real.log (α n))) atTop
      (𝓝 (b / (c * p))) := by
    have ht := (critical_moment_tendsto (j := 2) hc hp0 (by norm_num; linarith)
      hα hαpos).const_mul (b / c)
    simpa only [bias_eq hc, hs, mul_div_assoc, mul_one_div, div_div] using ht
  have he : 1 + (1 + 1 / p) = (2 * p + 1) / p := by field_simp; ring
  have hroot : ∀ᶠ n in atTop,
      logPower (1 + (1 + 1 / p)) (betaDiscrep b c p σ n) =
        (noiseConstant c p / (b / (c * p))) * noiseLevel σ n := by
    obtain ⟨N, hN⟩ := betaDiscrep_spec_largeIndex b c p σ hb hc hp hσ
    filter_upwards [Ici_mem_atTop (max N 1)] with n hn
    have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hn)
    have h := (hN ⟨n, hn0⟩ (by simpa using le_of_max_le_left hn)).2.2
    rw [BetaDiscrepRootEquation] at h
    change -(betaDiscrep b c p σ n ^ ((2 * p + 1) / p)) * Real.log (betaDiscrep b c p σ n) = _ at h
    rw [he]
    change _ * (-Real.log _) = _
    rw [mul_neg, ← neg_mul, h]
    have hpow : c ^ ((p + 1) / p) = c * c ^ (1 / p) := by
      rw [show (p + 1) / p = 1 + 1 / p by field_simp, Real.rpow_add hc, Real.rpow_one]
    rw [hpow]
    dsimp [noiseConstant, noiseLevel]
    field_simp
  exact critical_rate_of_balance (by positivity : 0 < 1 + (1 + 1 / p))
    (noiseConstant_pos hc hp) (div_pos hb (mul_pos hc hp0)) (noiseLevel_eventuallyPos hσ)
    hα hαpos (betaDiscrep_tendsto_zero b c p σ hb hc hp hσ)
    (betaDiscrep_eventually_pos b c p σ hb hc hp hσ) hB
    (divided_noise_tendsto hc hp hα hαpos) (divided_balance hbal) hroot

/-- Source scalar for the saturated residual, which uses one inverse eigenvalue. -/
@[expose] def source (b c p q : ℝ) : ℝ :=
  (b / c) * ∑' k : ℕ, ((k : ℝ) + 1) ^ (p - q)

lemma saturated {b c p q σ T : ℝ} {α : ℕ → ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hs : p - q < -1) (hbal : HasBalance b c p q σ α)
    (hT : source b c p q = T) (hTpos : 0 < T) :
    α ~[atTop] saturatedParameterBenchmark c p σ T := by
  have hp0 : 0 < p := by linarith
  have hα := balance_tendsto_zero hb hc hp hq hbal
  have hαpos := hbal.mono fun _ h ↦ h.1
  have hρ : Tendsto (fun n ↦ α n / c) atTop (𝓝 0) := by simpa using hα.div_const c
  have hρpos : ∀ᶠ n in atTop, 0 ≤ α n / c :=
    hαpos.mono fun n hn ↦ (div_pos hn hc).le
  have hB : Tendsto (fun n ↦ α n ^ (0 : ℝ) * bias b c p q (α n)) atTop (𝓝 T) := by
    have ht := (moment_saturated_tendsto (p := p) (j := 2) hs hρ hρpos).const_mul (b / c)
    change Tendsto _ _ (𝓝 (source b c p q)) at ht
    simpa only [Real.rpow_zero, one_mul, bias_eq hc, hT] using ht
  have he : 1 + (1 + 1 / p) - 0 = (2 * p + 1) / p := by field_simp; ring
  have hexp : 1 / ((2 * p + 1) / p) = p / (2 * p + 1) := by field_simp
  have ht := rate_of_balance (u := 0) (v := 1 + 1 / p)
    (by rw [he]; exact (div_pos (by linarith) hp0).ne')
    (noiseConstant_pos hc hp) hTpos (noiseLevel_nonneg σ) (noiseLevel_eventuallyPos hσ)
    hαpos hB (divided_noise_tendsto hc hp hα hαpos) (divided_balance hbal)
  rw [he, hexp] at ht
  change α ~[atTop] (fun n ↦ parameterConstant2 c p T * (σ ^ 2 / (n : ℝ)) ^ (p / (2 * p + 1)))
  rw [parameterConstant2_def]
  exact ht

end SequenceModel
end TikhonovDiscrepancy

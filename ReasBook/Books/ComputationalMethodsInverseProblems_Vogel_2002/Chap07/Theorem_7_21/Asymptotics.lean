/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.RateCalculus
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.Minimizer
public section
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
namespace TikhonovEstimation
namespace PowerRisk

lemma biasConstant_pos {b c p q : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hp : 1 < p) (hq : 1 < q) (hs : -1 < 2 * p - q)
    (j : ℕ) (hj : j = 2 ∨ j = 3) : 0 < biasConstant b c p q j := by
  apply mul_pos (mul_pos hb (Real.rpow_pos_of_pos hc _))
  apply integral_pos (by linarith) hs
  rcases hj with rfl | rfl <;> norm_num <;> linarith

lemma varianceConstant_pos {c p : ℝ} (hc : 0 < c) (hp : 1 < p)
    (j : ℕ) (hj : j = 2 ∨ j = 3) : 0 < varianceConstant c p j := by
  apply mul_pos (Real.rpow_pos_of_pos hc _)
  apply integral_pos (by linarith)
  · rcases hj with rfl | rfl <;> norm_num <;> linarith
  · nlinarith

lemma nonsaturated_constant_eq {b c p q : ℝ} (hc : 0 < c) :
    varianceConstant c p 3 / biasConstant b c p q 3 =
      c ^ (q / p) * KernelMoment.integral p 3 (2 * p) /
        (b * KernelMoment.integral p 3 (2 * p - q)) := by
  have hpw : c ^ (1 / p) / c ^ (-(q - 1) / p) = c ^ (q / p) := by
    rw [← Real.rpow_sub hc]
    congr 1
    ring
  simp only [varianceConstant, biasConstant, Nat.cast_ofNat]
  norm_num only
  calc
    _ = (c ^ (1 / p) / c ^ (-(q - 1) / p)) *
        KernelMoment.integral p 3 (2 * p) /
          (b * KernelMoment.integral p 3 (2 * p - q)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
    _ = _ := by rw [hpw]

lemma risk_equivalent_of_normalized {R α β δ : ℕ → ℝ} {r C : ℝ}
    (hC : 0 < C) (hβ : ∀ n, 0 ≤ β n)
    (hparam : α ~[atTop] β)
    (hlim : Tendsto (fun n ↦ R n / (δ n * (α n) ^ (-r))) atTop (𝓝 C)) :
    R ~[atTop] (fun n ↦ C * δ n * (β n) ^ (-r)) := by
  have h₁ := equivalent_const_mul_of_div_tendsto hC.ne' hlim
  have h₂ := (IsEquivalent.refl (u := fun n ↦ C * δ n) (l := atTop)).mul
    (hparam.rpow (r := -r) hβ)
  exact (h₁.congr_right (Eventually.of_forall fun n ↦ by dsimp; ring)).trans h₂

lemma noise_power_normalForm {C A δ k r : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    C * δ * (A * δ ^ k) ^ (-r) = C * A ^ (-r) * δ ^ (1 - k * r) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hδ.le k), ← Real.rpow_mul hδ.le]
  have hpw : δ * δ ^ (k * -r) = δ ^ (1 - k * r) := by
    calc
      _ = δ ^ (1 : ℝ) * δ ^ (k * -r) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  calc
    _ = C * A ^ (-r) * (δ * δ ^ (k * -r)) := by ring
    _ = _ := by rw [hpw]

section Nonsaturated
variable {objective : ℕ → ℝ → ℝ} {floor α : ℕ → ℝ} {b c p q σ : ℝ}
variable (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
variable (hmodel : HasPowerRiskModel objective floor b c p q σ)
variable (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
variable (hpos : ∀ᶠ n in atTop, 0 < α n) (hs : -1 < 2 * p - q)
include hb hc hp hq hσ hmodel hmin hpos hs

lemma parameter_nonsaturated : α ~[atTop] nonsaturatedParameterBenchmark b c p q σ := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  have hB := bias_normalized_tendsto (b := b) hc hp hq (j := 3) (Or.inr rfl) hs hz hpos
  have hV := variance_normalized_tendsto hc hp (j := 3) (Or.inr rfl) hz hpos
  simp only [Nat.cast_ofNat, show ((3 : ℝ) - 1) * p = 2 * p by ring] at hV
  have ha : 1 + (2 * p + 1) / p - (2 * p - q + 1) / p ≠ 0 := by
    have heq : 1 + (2 * p + 1) / p - (2 * p - q + 1) / p = (p + q) / p := by field_simp; ring
    rw [heq]
    exact (div_pos (by linarith) (by linarith)).ne'
  have heq : 1 / (1 + (2 * p + 1) / p - (2 * p - q + 1) / p) = p / (p + q) := by
    rw [show 1 + (2 * p + 1) / p - (2 * p - q + 1) / p = (p + q) / p by
      field_simp; ring, one_div_div]
  have ht := rate_of_balance ha (varianceConstant_pos hc hp 3 (Or.inr rfl))
    (biasConstant_pos hb hc hp hq hs 3 (Or.inr rfl)) (noiseLevel_nonneg σ)
    (noiseLevel_eventuallyPos hσ) hpos hB hV hstat
  change α ~[atTop] (fun n ↦ parameterConstantC1 b c p q *
    (noiseLevel σ n) ^ (p / (p + q)))
  simpa only [heq, nonsaturated_constant_eq hc, parameterConstantC1] using ht

lemma risk_nonsaturated :
    (fun n ↦ SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n)) ~[atTop]
      nonsaturatedErrorBenchmark b c p q σ := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  have hB₂ := bias_normalized_tendsto (b := b) hc hp hq (j := 2) (Or.inl rfl) hs hz hpos
  have hB₃ := bias_normalized_tendsto (b := b) hc hp hq (j := 3) (Or.inr rfl) hs hz hpos
  have hD₃ := biasConstant_pos hb hc hp hq hs 3 (Or.inr rfl)
  have hV₂ := variance_normalized_tendsto hc hp (j := 2) (Or.inl rfl) hz hpos
  have hV₃ := variance_normalized_tendsto hc hp (j := 3) (Or.inr rfl) hz hpos
  simp only [Nat.cast_ofNat, show ((2 : ℝ) - 1) * p = p by ring,
    show ((3 : ℝ) - 1) * p = 2 * p by ring] at hV₂ hV₃
  have hV₃' : Tendsto (fun n ↦ (α n) ^ ((p + 1) / p + 1) *
      SeriesRisk.varianceMoment (eigenvalue c p) 3 (α n)) atTop (𝓝 (varianceConstant c p 3)) := by
    have hexp : (p + 1) / p + 1 = (2 * p + 1) / p := by field_simp; ring
    simpa only [hexp] using hV₃
  have hratio := bias_ratio_of_scaled_limits hpos hD₃.ne' hB₂ hB₃
  have hBn : ∀ᶠ n in atTop, biasFactor b c p q 3 (α n) ≠ 0 := by
    filter_upwards [hB₃.eventually (lt_mem_nhds hD₃)] with n hn
    intro heq
    simp [heq] at hn
  have hT : biasConstant b c p q 2 / biasConstant b c p q 3 =
      KernelMoment.integral p 2 (2 * p - q) / KernelMoment.integral p 3 (2 * p - q) := by
    exact mul_div_mul_left _ _ (mul_pos hb (Real.rpow_pos_of_pos hc _)).ne'
  let T := KernelMoment.integral p 2 (2 * p - q) / KernelMoment.integral p 3 (2 * p - q)
  have hTp : 0 < T := div_pos (integral_pos (by linarith) hs (by norm_num; linarith))
    (integral_pos (by linarith) hs (by norm_num; linarith))
  have hC : 0 < varianceConstant c p 2 + varianceConstant c p 3 * T :=
    add_pos (varianceConstant_pos hc hp 2 (Or.inl rfl))
      (mul_pos (varianceConstant_pos hc hp 3 (Or.inr rfl)) hTp)
  have hlim := risk_normalized_tendsto hpos (noiseLevel_eventuallyPos hσ) hBn hstat
    (hT ▸ hratio) hV₂ hV₃'
  have hrisk : Tendsto (fun n ↦
      SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n) /
        (noiseLevel σ n * (α n) ^ (-((p + 1) / p)))) atTop
        (𝓝 (varianceConstant c p 2 + varianceConstant c p 3 * T)) := by
    apply hlim.congr'
    filter_upwards [hpos] with n hn
    rw [risk_eq hb hc hp hq hn]
    simp only [biasFactor, mul_assoc]
  have hA : 0 < parameterConstantC1 b c p q := by
    rw [parameterConstantC1, ← nonsaturated_constant_eq hc]
    exact Real.rpow_pos_of_pos (div_pos (varianceConstant_pos hc hp 3 (Or.inr rfl)) hD₃) _
  have hβ : ∀ n, 0 ≤ nonsaturatedParameterBenchmark b c p q σ n := fun n ↦
    mul_nonneg hA.le (Real.rpow_nonneg (noiseLevel_nonneg σ n) _)
  have heq := risk_equivalent_of_normalized hC hβ
    (parameter_nonsaturated hb hc hp hq hσ hmodel hmin hpos hs) hrisk
  apply heq.congr_right
  filter_upwards [noiseLevel_eventuallyPos hσ] with n hn
  rw [nonsaturatedParameterBenchmark]
  dsimp only [noiseLevel] at hn ⊢
  rw [noise_power_normalForm hA hn]
  have hexp : 1 - p / (p + q) * ((p + 1) / p) = (q - 1) / (p + q) := by
    field_simp [ne_of_gt (show 0 < p by linarith),
      ne_of_gt (show 0 < p + q by linarith), ne_of_gt (show 0 < 3 * p + 1 by linarith)]
    ring
  rw [hexp]
  simp only [nonsaturatedErrorBenchmark, errorConstantC3, varianceConstant, Nat.cast_ofNat]
  norm_num only
  dsimp [T, noiseLevel]
  ring
end Nonsaturated
lemma risk_equivalent_of_bias_ratio {objective : ℕ → ℝ → ℝ} {floor α β : ℕ → ℝ}
    {b c p q σ T : ℝ} (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (hmodel : HasPowerRiskModel objective floor b c p q σ)
    (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
    (hpos : ∀ᶠ n in atTop, 0 < α n) (hβ : ∀ n, 0 ≤ β n)
    (hparam : α ~[atTop] β) (hT : 0 ≤ T)
    (hBn : ∀ᶠ n in atTop, biasFactor b c p q 3 (α n) ≠ 0)
    (hBratio : Tendsto (fun n ↦ biasFactor b c p q 2 (α n) /
      biasFactor b c p q 3 (α n)) atTop (𝓝 T)) :
    (fun n ↦ SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n)) ~[atTop]
      (fun n ↦ (varianceConstant c p 2 + varianceConstant c p 3 * T) * noiseLevel σ n *
        (β n) ^ (-((p + 1) / p))) := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  have hV₂ := variance_normalized_tendsto hc hp (j := 2) (Or.inl rfl) hz hpos
  have hV₃ := variance_normalized_tendsto hc hp (j := 3) (Or.inr rfl) hz hpos
  simp only [Nat.cast_ofNat, show ((2 : ℝ) - 1) * p = p by ring,
    show ((3 : ℝ) - 1) * p = 2 * p by ring] at hV₂ hV₃
  have hV₃' : Tendsto (fun n ↦ (α n) ^ ((p + 1) / p + 1) *
      SeriesRisk.varianceMoment (eigenvalue c p) 3 (α n)) atTop (𝓝 (varianceConstant c p 3)) := by
    have hexp : (p + 1) / p + 1 = (2 * p + 1) / p := by field_simp; ring
    simpa only [hexp] using hV₃
  have hlim := risk_normalized_tendsto hpos (noiseLevel_eventuallyPos hσ) hBn hstat
    hBratio hV₂ hV₃'
  have hrisk : Tendsto (fun n ↦
      SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n) /
        (noiseLevel σ n * (α n) ^ (-((p + 1) / p)))) atTop
        (𝓝 (varianceConstant c p 2 + varianceConstant c p 3 * T)) := by
    apply hlim.congr'
    filter_upwards [hpos] with n hn
    rw [risk_eq hb hc hp hq hn]
    simp only [biasFactor, mul_assoc]
  exact risk_equivalent_of_normalized
    (add_pos_of_pos_of_nonneg (varianceConstant_pos hc hp 2 (Or.inl rfl))
      (mul_nonneg (varianceConstant_pos hc hp 3 (Or.inr rfl)).le hT)) hβ hparam hrisk

section Saturated
variable {objective : ℕ → ℝ → ℝ} {floor α : ℕ → ℝ} {b c p q σ : ℝ}
variable (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
variable (hmodel : HasPowerRiskModel objective floor b c p q σ)
variable (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
variable (hpos : ∀ᶠ n in atTop, 0 < α n) (hs : 2 * p - q < -1)
include hb hc hp hq hσ hmodel hmin hpos hs

lemma parameter_saturated :
    α ~[atTop] saturatedParameterBenchmark c p σ (source b c p q) := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  have hB₃ := bias_saturated_tendsto (b := b) hc (j := 3) hs hz hpos
  have hB : Tendsto (fun n ↦ (α n) ^ (0 : ℝ) * biasFactor b c p q 3 (α n)) atTop
      (𝓝 (source b c p q)) := by simpa using hB₃
  have hV := variance_normalized_tendsto hc hp (j := 3) (Or.inr rfl) hz hpos
  simp only [Nat.cast_ofNat, show ((3 : ℝ) - 1) * p = 2 * p by ring] at hV
  have ha : 1 + (2 * p + 1) / p - 0 ≠ 0 := by
    have : 0 < (2 * p + 1) / p := div_pos (by linarith) (by linarith)
    linarith
  have hexp : 1 / (1 + (2 * p + 1) / p - 0) = p / (3 * p + 1) := by
    rw [show 1 + (2 * p + 1) / p - 0 = (3 * p + 1) / p by
      field_simp; ring, one_div_div]
  have ht := rate_of_balance ha (varianceConstant_pos hc hp 3 (Or.inr rfl))
    (source_pos hb hc hs) (noiseLevel_nonneg σ) (noiseLevel_eventuallyPos hσ) hpos hB hV hstat
  change α ~[atTop] (fun n ↦ parameterConstantC2 c p (source b c p q) *
    (noiseLevel σ n) ^ (p / (3 * p + 1)))
  simpa only [hexp, parameterConstantC2, varianceConstant, Nat.cast_ofNat,
    show ((3 : ℝ) - 1) * p = 2 * p by ring] using ht

lemma risk_saturated :
    (fun n ↦ SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n)) ~[atTop]
      saturatedErrorBenchmark b c p q σ := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hA := source_pos hb hc hs
  have hB₂ := bias_saturated_tendsto (b := b) hc (j := 2) hs hz hpos
  have hB₃ := bias_saturated_tendsto (b := b) hc (j := 3) hs hz hpos
  have hBn : ∀ᶠ n in atTop, biasFactor b c p q 3 (α n) ≠ 0 :=
    (hB₃.eventually (lt_mem_nhds hA)).mono fun n hn ↦ hn.ne'
  have hratio : Tendsto (fun n ↦ biasFactor b c p q 2 (α n) /
      biasFactor b c p q 3 (α n)) atTop (𝓝 1) := by
    have ht := hB₂.div hB₃ hA.ne'
    simp only [div_self hA.ne'] at ht
    exact ht
  have hAp : 0 < parameterConstantC2 c p (source b c p q) := by
    apply Real.rpow_pos_of_pos
    exact div_pos (by simpa only [varianceConstant, Nat.cast_ofNat,
      show ((3 : ℝ) - 1) * p = 2 * p by ring] using varianceConstant_pos hc hp 3 (Or.inr rfl)) hA
  have hβ : ∀ n, 0 ≤ saturatedParameterBenchmark c p σ (source b c p q) n := fun n ↦
    mul_nonneg hAp.le (Real.rpow_nonneg (noiseLevel_nonneg σ n) _)
  have heq := risk_equivalent_of_bias_ratio hb hc hp hq hσ hmodel hmin hpos hβ
    (parameter_saturated hb hc hp hq hσ hmodel hmin hpos hs) zero_le_one hBn hratio
  apply heq.congr_right
  filter_upwards [noiseLevel_eventuallyPos hσ] with n hn
  rw [saturatedParameterBenchmark]
  dsimp only [noiseLevel] at hn ⊢
  rw [noise_power_normalForm hAp hn]
  have hexp : 1 - p / (3 * p + 1) * ((p + 1) / p) = 2 * p / (3 * p + 1) := by
    field_simp [ne_of_gt (show 0 < p by linarith),
      ne_of_gt (show 0 < p + q by linarith), ne_of_gt (show 0 < 3 * p + 1 by linarith)]
    ring
  rw [hexp]
  simp only [saturatedErrorBenchmark, errorConstantC5, varianceConstant, Nat.cast_ofNat,
    source, scalarSourceNormSq]
  norm_num only
  dsimp [noiseLevel]
  ring
end Saturated

section Critical
variable {objective : ℕ → ℝ → ℝ} {floor α β : ℕ → ℝ} {b c p q σ : ℝ}
variable (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
variable (hmodel : HasPowerRiskModel objective floor b c p q σ)
variable (hmin : ParameterChoice.IsOptimalParameterFamily objective admissibleParameters α)
variable (hpos : ∀ᶠ n in atTop, 0 < α n) (hs : 2 * p - q = -1)
variable (hroot : IsCriticalBenchmark b c p σ β) (hβpos : ∀ n, 0 < β n)
variable (hβzero : Tendsto β atTop (𝓝 0))
include hb hc hp hq hσ hmodel hmin hpos hs hroot hβpos hβzero

lemma parameter_critical : α ~[atTop] β := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hstat := stationary_of_optimality hb hc hp hq hmodel hmin hpos
  have hp0 : 0 < p := by linarith
  have hB := bias_critical_tendsto (b := b) hc hp0 (j := 3) (by norm_num; linarith) hs hz hpos
  have hV := variance_normalized_tendsto hc hp (j := 3) (Or.inr rfl) hz hpos
  simp only [Nat.cast_ofNat, show ((3 : ℝ) - 1) * p = 2 * p by ring] at hV
  apply critical_rate_of_balance (by positivity : 0 < 1 + (2 * p + 1) / p)
    (varianceConstant_pos hc hp 3 (Or.inr rfl)) (div_pos hb (mul_pos (sq_pos_of_pos hc) hp0))
    (noiseLevel_eventuallyPos hσ) hz hpos hβzero (Eventually.of_forall hβpos) hB hV hstat
  have hexp : 1 + (2 * p + 1) / p = (3 * p + 1) / p := by field_simp; ring
  filter_upwards [hroot] with n hn
  change -(β n ^ ((3 * p + 1) / p)) * Real.log (β n) = criticalRootRhs b c p σ n at hn
  rw [logPower, hexp]
  calc
    _ = -(β n ^ ((3 * p + 1) / p)) * Real.log (β n) := by ring
    _ = _ := hn
    _ = _ := by
      simp only [criticalRootRhs, varianceConstant, Nat.cast_ofNat, Real.rpow_neg_one, noiseLevel]
      norm_num only
      field_simp

lemma risk_critical :
    (fun n ↦ SeriesRisk.risk (coeff b q) (eigenvalue c p) (noiseLevel σ n) (α n)) ~[atTop]
      criticalErrorBenchmark c p σ β := by
  have hz := optimality_tendsto_zero hb hc hp hq hmodel hmin hpos
  have hp0 : 0 < p := by linarith
  have hD : 0 < b / (c ^ 2 * p) := div_pos hb (mul_pos (sq_pos_of_pos hc) hp0)
  have hB₂ := bias_critical_tendsto (b := b) hc hp0 (j := 2) (by norm_num; linarith) hs hz hpos
  have hB₃ := bias_critical_tendsto (b := b) hc hp0 (j := 3) (by norm_num; linarith) hs hz hpos
  have hlog := negLog_tendsto hz hpos
  have hBn : ∀ᶠ n in atTop, biasFactor b c p q 3 (α n) ≠ 0 := by
    filter_upwards [hB₃.eventually (lt_mem_nhds hD)] with n hn
    intro heq
    simp [heq] at hn
  have hratio : Tendsto (fun n ↦ biasFactor b c p q 2 (α n) /
      biasFactor b c p q 3 (α n)) atTop (𝓝 1) := by
    have ht := hB₂.div hB₃ hD.ne'
    simp only [div_self hD.ne'] at ht
    apply ht.congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with n hn
    change (biasFactor b c p q 2 (α n) / (-Real.log (α n))) /
      (biasFactor b c p q 3 (α n) / (-Real.log (α n))) = _
    field_simp [ne_of_lt (neg_pos.1 hn)]
  have heq := risk_equivalent_of_bias_ratio hb hc hp hq hσ hmodel hmin hpos (fun n ↦ (hβpos n).le)
    (parameter_critical hb hc hp hq hσ hmodel hmin hpos hs hroot hβpos hβzero) zero_le_one hBn hratio
  apply heq.congr_right
  apply Eventually.of_forall
  intro n
  simp only [criticalErrorBenchmark, errorConstantC4, varianceConstant, Nat.cast_ofNat, noiseLevel]
  norm_num only
  ring
end Critical
end PowerRisk
end TikhonovEstimation

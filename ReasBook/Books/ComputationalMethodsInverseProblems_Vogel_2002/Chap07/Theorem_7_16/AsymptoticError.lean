/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.PowerSums
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalIndexProfile
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.ErrorConstant
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.SpectralError
/-!
# The asymptotic TSVD estimation error in equation (7.64)

The two indices in the optimality window are asymptotically equivalent to
the real-valued profile in equation (7.63). Transporting the power-sum and
power-tail estimates along either index gives the same leading error term.
The algebraic profile identities identify its coefficient with
`errorConstant`, and nonnegativity permits adding any nullspace floor.

The spectral theorem at the end only requires noise moments for the modes
actually retained along the chosen truncation family.
-/

public section

noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators
namespace TsvdEstimation

lemma powerSum_isEquivalent {p : ℝ} (hp : 0 < p) :
    IsEquivalent atTop (fun m : ℕ ↦ ∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p)
      (fun m ↦ (m : ℝ) ^ (p + 1) / (p + 1)) := by
  apply isEquivalent_of_tendsto_one
  have ht : Tendsto (fun m : ℕ ↦
      ((∑ k ∈ Finset.range m, ((k : ℝ) + 1) ^ p) / (m : ℝ) ^ (p + 1)) * (p + 1))
      atTop (𝓝 1) := by
    simpa only [one_div_mul_cancel (by linarith : p + 1 ≠ 0)] using
      (powerSum_normalized_tendsto hp).mul_const (p + 1)
  convert ht using 1
  funext m
  dsimp
  rw [div_div_eq_mul_div]
  ring

lemma powerTail_isEquivalent {q : ℝ} (hq : 1 < q) :
    IsEquivalent atTop (fun m : ℕ ↦ ∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q))
      (fun m ↦ (m : ℝ) ^ (1 - q) / (q - 1)) := by
  apply isEquivalent_of_tendsto_one
  have ht : Tendsto (fun m : ℕ ↦
      ((∑' k : ℕ, ((k + m + 1 : ℕ) : ℝ) ^ (-q)) / (m : ℝ) ^ (1 - q)) * (q - 1))
      atTop (𝓝 1) := by
    simpa only [one_div_mul_cancel (by linarith : q - 1 ≠ 0)] using
      (powerTail_normalized_tendsto hq).mul_const (q - 1)
  convert ht using 1
  funext m
  dsimp
  rw [div_div_eq_mul_div]
  ring

lemma scalar_error_isEquivalent {b p q : ℝ} (hb : 0 < b) (hp : 0 < p) (hq : 1 < q)
    {M : ℕ → ℝ} (hMnonneg : ∀ n, 0 ≤ M n) (hMtop : Tendsto M atTop atTop)
    {m : ℕ → ℕ} (hmeq : IsEquivalent atTop (fun n ↦ (m n : ℝ)) M) :
    IsEquivalent atTop
      (fun n ↦ b * (∑' k : ℕ, ((k + m n + 1 : ℕ) : ℝ) ^ (-q)) +
        (b / (M n) ^ (p + q)) * ∑ k ∈ Finset.range (m n), ((k : ℝ) + 1) ^ p)
      (fun n ↦ b * (1 / (q - 1) + 1 / (p + 1)) * (M n) ^ (1 - q)) := by
  have hmtop : Tendsto m atTop atTop :=
    tendsto_natCast_atTop_iff.1 (hmeq.tendsto_atTop_iff.2 hMtop)
  have htail : IsEquivalent atTop
      (fun n ↦ ∑' k : ℕ, ((k + m n + 1 : ℕ) : ℝ) ^ (-q))
      (fun n ↦ (M n) ^ (1 - q) / (q - 1)) :=
    ((powerTail_isEquivalent hq).comp_tendsto hmtop).trans
      ((hmeq.rpow hMnonneg).div IsEquivalent.refl)
  have hsum : IsEquivalent atTop
      (fun n ↦ ∑ k ∈ Finset.range (m n), ((k : ℝ) + 1) ^ p)
      (fun n ↦ (M n) ^ (p + 1) / (p + 1)) :=
    ((powerSum_isEquivalent hp).comp_tendsto hmtop).trans
      ((hmeq.rpow hMnonneg).div IsEquivalent.refl)
  have hnoise : IsEquivalent atTop
      (fun n ↦ (b / (M n) ^ (p + q)) * ∑ k ∈ Finset.range (m n), ((k : ℝ) + 1) ^ p)
      (fun n ↦ b * (M n) ^ (1 - q) / (p + 1)) := by
    apply (IsEquivalent.refl.mul hsum).trans_eventuallyEq
    filter_upwards [hMtop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    dsimp only [Pi.mul_apply]
    have heq : (M n) ^ (p + 1) / (M n) ^ (p + q) = (M n) ^ (1 - q) := by
      rw [← Real.rpow_sub hn]
      congr 1
      ring
    calc
      _ = b * ((M n) ^ (p + 1) / (M n) ^ (p + q)) / (p + 1) := by ring
      _ = _ := by rw [heq]
  have hbias := (IsEquivalent.refl (u := fun _ : ℕ ↦ b)).mul htail
  have hall := IsEquivalent.add_add_of_nonneg
    (fun n ↦ mul_nonneg hb.le (div_nonneg (Real.rpow_nonneg (hMnonneg n) _) (by linarith)))
    (fun n ↦ div_nonneg (mul_nonneg hb.le (Real.rpow_nonneg (hMnonneg n) _)) (by linarith))
    hbias hnoise
  apply hall.trans_eventuallyEq
  exact Eventually.of_forall (fun n ↦ by dsimp; ring)

lemma optimalIndexWindow_isEquivalent_profile {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    {m : ℕ → ℕ} (hwindow : ∀ᶠ n in atTop,
      m n = optimalIndex b c p q σ n ∨ m n + 1 = optimalIndex b c p q σ n) :
    IsEquivalent atTop (fun n ↦ (m n : ℝ)) (optimalIndexProfile b c p q σ) := by
  let M := optimalIndexProfile b c p q σ
  let β := optimalIndex b c p q σ
  have hMtop : Tendsto M atTop atTop := optimalIndexProfile_tendstoAtTop b c p q σ hb hc hp hq hσ
  have hMpos : ∀ᶠ n in atTop, 0 < M n := hMtop.eventually (eventually_gt_atTop 0)
  have hβratio : Tendsto (fun n ↦ (β n : ℝ) / M n) atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one (hMpos.mono fun n hn ↦ hn.ne')).1
      (optimalIndexCast_isEquivalent_profile b c p q σ hb hc hp hq hσ)
  have hInv : Tendsto (fun n ↦ 1 / M n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using! tendsto_inv_atTop_zero.comp hMtop
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun n ↦ (m n : ℝ) / M n) atTop (𝓝 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n ↦ (β n : ℝ) / M n - 1 / M n)
    (h := fun n ↦ (β n : ℝ) / M n)
    (by simpa using hβratio.sub hInv) hβratio
  · filter_upwards [hwindow, hMpos] with n hn hMn
    have hbound : (β n : ℝ) - 1 ≤ (m n : ℝ) := by
      rcases hn with h | h
      · change m n = β n at h
        rw [h]
        linarith
      · have hcast : (m n : ℝ) + 1 = (β n : ℝ) := by exact_mod_cast h
        linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hbound hMn.le
  · filter_upwards [hwindow, hMpos] with n hn hMn
    have hbound : m n ≤ β n := by
      change m n = β n ∨ m n + 1 = β n at hn
      omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast hbound) hMn.le

lemma optimalIndexProfile_noiseScale {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hpq : 0 < p + q) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) :
    b / (optimalIndexProfile b c p q σ n) ^ (p + q) = σ ^ 2 / ((n : ℝ) * c) := by
  have hX : 0 < σ ^ 2 / (n : ℝ) := by positivity
  rw [optimalIndexProfile_def, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (mul_pos hb hc).le, ← Real.rpow_mul hX.le,
    show (1 / (p + q)) * (p + q) = 1 by field_simp,
    show -(1 / (p + q)) * (p + q) = -1 by field_simp,
    Real.rpow_one, Real.rpow_neg_one]
  field_simp

lemma optimalIndexProfile_errorConstant {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    {n : ℕ} (hn : 0 < n) :
    b * (1 / (q - 1) + 1 / (p + 1)) * (optimalIndexProfile b c p q σ n) ^ (1 - q) =
      errorConstant b c p q * (σ ^ 2 / (n : ℝ)) ^ ((q - 1) / (p + q)) := by
  have hpq : p + q ≠ 0 := by linarith
  have hX : 0 < σ ^ 2 / (n : ℝ) := by positivity
  have hpow : (optimalIndexProfile b c p q σ n) ^ (1 - q) =
      b ^ ((1 - q) / (p + q)) * c ^ ((1 - q) / (p + q)) *
        (σ ^ 2 / (n : ℝ)) ^ ((q - 1) / (p + q)) := by
    rw [optimalIndexProfile_def, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (mul_pos hb hc).le, ← Real.rpow_mul hX.le,
      show (1 / (p + q)) * (1 - q) = (1 - q) / (p + q) by ring,
      show -(1 / (p + q)) * (1 - q) = (q - 1) / (p + q) by ring,
      Real.mul_rpow hb.le hc.le]
  have hcPow : (c ^ (q - 1)) ^ (1 / (p + q)) = (c ^ ((1 - q) / (p + q)))⁻¹ := by
    rw [← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]
    congr 1
    ring
  have hbPow : b * b ^ ((1 - q) / (p + q)) = (b ^ (p + 1)) ^ (1 / (p + q)) := by
    calc
      _ = b ^ (1 + (1 - q) / (p + q)) := by rw [Real.rpow_add hb, Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_mul hb.le]
        congr 1
        field_simp
        ring
  have hconstant : (b ^ (p + 1) / c ^ (q - 1)) ^ (1 / (p + q)) =
      (b * b ^ ((1 - q) / (p + q))) * c ^ ((1 - q) / (p + q)) := by
    rw [Real.div_rpow (by positivity) (by positivity), hcPow, div_inv_eq_mul, ← hbPow]
  rw [hpow, errorConstant_def, hconstant]
  have hcoef : 1 / (q - 1) + 1 / (p + 1) = (p + q) / ((p + 1) * (q - 1)) := by
    field_simp [show q - 1 ≠ 0 by linarith, show p + 1 ≠ 0 by linarith]
    ring
  rw [hcoef]
  ring

lemma scalar_error_at_optimalIndexWindow_isEquivalent {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    {m : ℕ → ℕ} (hwindow : ∀ᶠ n in atTop,
      m n = optimalIndex b c p q σ n ∨ m n + 1 = optimalIndex b c p q σ n) :
    IsEquivalent atTop
      (fun n ↦ b * (∑' k : ℕ, ((k + m n + 1 : ℕ) : ℝ) ^ (-q)) +
        (σ ^ 2 / ((n : ℝ) * c)) * ∑ k ∈ Finset.range (m n), ((k : ℝ) + 1) ^ p)
      (fun n ↦ errorConstant b c p q * (σ ^ 2 / (n : ℝ)) ^ ((q - 1) / (p + q))) := by
  have h := scalar_error_isEquivalent hb (by linarith : 0 < p) hq
    (M := optimalIndexProfile b c p q σ) (by intro n; rw [optimalIndexProfile_def]; positivity)
    (optimalIndexProfile_tendstoAtTop b c p q σ hb hc hp hq hσ)
    (optimalIndexWindow_isEquivalent_profile hb hc hp hq hσ hwindow)
  apply (h.congr_left ?_).trans_eventuallyEq ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [optimalIndexProfile_noiseScale hb hc (by linarith : 0 < p + q) hσ hn]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact optimalIndexProfile_errorConstant hb hc hp hq hσ hn

theorem expectedSqErrorAlong_isEquivalent_of_optimalIndexWindow
    {H F Ω : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (hlen : ∀ n, (S n).length = ⊤) (f : H) {b c p q σ : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hp : 1 < p) (hq : 1 < q) (hσ : 0 < σ)
    (η : ℕ → Ω → F) (R : ℕ → ℕ → F →L[ℝ] H)
    (hR : IsTsvdReconstructionFamily K S hlen R)
    (hLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (hs : ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (hlen n) c p)
    (hf : ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (hlen n) f b q)
    {m : ℕ → ℕ}
    (hvar : ∀ᶠ n in atTop, ∀ i < m n, ∫ ω,
      (inner ℝ ((S n).leftBasis ((S n).natIndex (hlen n) i) : F) (η n ω)) ^ 2 ∂μ =
        σ ^ 2 / (n : ℝ))
    (hwindow : ∀ᶠ n in atTop,
      m n = optimalIndex b c p q σ n ∨ m n + 1 = optimalIndex b c p q σ n) :
    IsEquivalent atTop (expectedSqErrorAlong μ K R f η m)
      (optimalErrorBenchmark K f b c p q σ) := by
  have hcpos : 0 < errorConstant b c p q := by
    rw [errorConstant_def]
    apply mul_pos (div_pos (by linarith) (mul_pos (by linarith) (by linarith)))
    exact Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos hc _)) _
  have herr := scalar_error_at_optimalIndexWindow_isEquivalent hb hc hp hq hσ hwindow
  have h := IsEquivalent.add_add_of_nonneg
    (fun n ↦ sq_nonneg ‖FilterRegularization.nullspaceComponent (K n) f‖)
    (fun n ↦ mul_nonneg hcpos.le (Real.rpow_nonneg (by positivity) _))
    (IsEquivalent.refl (u := fun n ↦ ‖FilterRegularization.nullspaceComponent (K n) f‖ ^ 2)) herr
  apply (h.congr_left ?_).trans_eventuallyEq ?_
  · filter_upwards [hvar] with n hn
    rw [expectedSqErrorAlong_apply,
      expectedSqErrorObjective_eq_nullspace_add_tail_add_sum μ K S hlen f hq η R hR hLp hs hf hn]
    rfl
  · exact Eventually.of_forall (fun n ↦ (optimalErrorBenchmark_apply K f b c p q σ n).symm)

end TsvdEstimation

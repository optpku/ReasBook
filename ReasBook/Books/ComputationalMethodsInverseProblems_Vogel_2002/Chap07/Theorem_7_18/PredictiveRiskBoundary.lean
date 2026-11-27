/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_18.PredictiveRiskStep

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section Profile

variable (b c p q σ : ℝ)

/-- Helper for Theorem 7.18: the two benchmark spellings `(7.63)` and `(7.61)`
agree. -/
theorem benchmark_rpow_profile_eq (b c p q σ : ℝ) {n : ℕ} (hn : 0 < n)
    (hb : 0 < b) (hc : 0 < c) :
    (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) =
      ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
  calc
    (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q))))
        = (1 / (b * c) : ℝ) ^ (-(1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
          rw [Real.mul_rpow (div_pos one_pos (mul_pos hb hc)).le
            (div_nonneg (sq_nonneg σ) (Nat.cast_nonneg n))]
    _ = (((1 / (b * c) : ℝ)⁻¹) ^ (1 / (p + q))) *
          (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
          rw [Real.rpow_neg_eq_inv_rpow]
    _ = ((b * c) ^ (1 / (p + q))) *
          (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
          rw [one_div, inv_inv]

end Profile

section PredictiveRiskBoundary

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
variable (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
variable
  (h_noise_modeVariance :
    ∀ n i,
      ∫ ω,
        (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
          σ ^ 2 / (n : ℝ))
variable (h_singularDecay :
  ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
variable (h_fourierDecay :
  ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

/-- Helper for Theorem 7.18: the predictive-risk backward step is the
estimation-error backward step multiplied by the positive factor
`(c / n) * m ^ (-p)`, so the two objectives have the same one-step signs (and
hence the same minimizer set). -/
theorem expectedPredictiveRiskObjective_step_eq_smul_stepExpr
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (m : ℝ) ^ (-(p + q)) =
      ((c / (n : ℝ)) * (m : ℝ) ^ (-p)) *
        (-b * (m : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : (m : ℝ) ^ (-(p + q)) = (m : ℝ) ^ (-p) * (m : ℝ) ^ (-q) := by
    rw [show -(p + q) = -p + -q by ring, Real.rpow_add hm0]
  have hcancel : (m : ℝ) ^ (-p) * (m : ℝ) ^ p = 1 := by
    rw [← Real.rpow_add hm0, show -p + p = 0 by ring, Real.rpow_zero]
  rw [hsplit]
  field_simp
  nlinarith [hcancel]

/-- Helper for Theorem 7.18: the predictive-risk backward step is monotone in
the truncation index. -/
theorem expectedPredictiveRiskObjective_step_mono
    {n j₁ j₂ : ℕ} (h1 : 0 < j₁) (h12 : j₁ ≤ j₂) :
    (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (j₁ : ℝ) ^ (-(p + q)) ≤
      (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (j₂ : ℝ) ^ (-(p + q)) := by
  have hj1 : (0 : ℝ) < (j₁ : ℝ) := by exact_mod_cast h1
  have hj12 : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h12
  have hdecay : (j₂ : ℝ) ^ (-(p + q)) ≤ (j₁ : ℝ) ^ (-(p + q)) :=
    Real.rpow_le_rpow_of_nonpos hj1 hj12 (by linarith : -(p + q) ≤ 0)
  have hcoef : (0 : ℝ) ≤ (b * c) / (n : ℝ) := by positivity
  nlinarith

/-- Helper for Theorem 7.18: at the diagonal index `m = n` the predictive-risk
backward step is eventually positive, because for `p + q > 2` the signal cross
term `(b * c / n) * n ^ (-(p + q))` is dominated by `b * c / n ^ 3`, which in
turn is smaller than the noise term `σ ^ 2 / n ^ 2` once `n > b * c / σ ^ 2`. -/
theorem expectedPredictiveRiskObjective_step_self_pos_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (n : ℝ) ^ (-(p + q)) := by
  have hpq : (2 : ℝ) < p + q := by linarith
  have hthr : ∀ᶠ n : ℕ in Filter.atTop, (b * c) / σ ^ 2 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_gt_atTop ((b * c) / σ ^ 2))
  filter_upwards [hthr, Filter.eventually_ge_atTop (2 : ℕ)] with n hn hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hbc : (0 : ℝ) < b * c := mul_pos h_b h_c
  have hσ2 : (0 : ℝ) < σ ^ 2 := pow_pos h_σ 2
  -- Since `p + q > 2`, the decaying power is dominated by `n ^ (-2)`.
  have hle : (n : ℝ) ^ (-(p + q)) ≤ (n : ℝ) ^ (-2 : ℝ) := by
    rw [Real.rpow_le_rpow_left_iff (x := (n : ℝ)) (y := -(p + q)) (z := -2) hn1]
    linarith
  have hcoef : (0 : ℝ) ≤ (b * c) / (n : ℝ) := by positivity
  have hterm_le :
      (b * c) / (n : ℝ) * (n : ℝ) ^ (-(p + q)) ≤ (b * c) / (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
    mul_le_mul_of_nonneg_left hle hcoef
  -- The bound `(b * c / n) * n ^ (-2) = b * c / n ^ 3` beats the noise term.
  have hterm_eq : (b * c) / (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) = (b * c) / (n : ℝ) ^ 3 := by
    rw [Real.rpow_neg (x := (n : ℝ)) (le_of_lt hn0)]
    field_simp
    norm_num
  have hsmall : (b * c) / (n : ℝ) * (n : ℝ) ^ (-2 : ℝ) < (σ ^ 2) / (n : ℝ) ^ 2 := by
    rw [hterm_eq, div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)]
    have hsq : (σ ^ 2) / (n : ℝ) ^ 2 * (n : ℝ) ^ 3 = σ ^ 2 * (n : ℝ) := by
      field_simp
    rw [hsq]
    have hmul := mul_lt_mul_of_pos_right hn hσ2
    have hcancel : (b * c) / σ ^ 2 * σ ^ 2 = b * c := by
      field_simp
    linarith [hmul, hcancel]
  linarith [hterm_le, hsmall]

/-- Helper for Theorem 7.18: eventually the predictive-risk objective at
truncation index `1` is strictly smaller than at the boundary index `0`. -/
theorem expectedPredictiveRiskObjective_one_lt_zero_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n 1 <
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n 0 := by
  have hthr : ∀ᶠ n : ℕ in Filter.atTop, σ ^ 2 / (b * c) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_gt_atTop (σ ^ 2 / (b * c)))
  filter_upwards [hthr, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < n := hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hbc : (0 : ℝ) < b * c := mul_pos h_b h_c
  have hstep := expectedPredictiveRiskObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := 1) hnpos (by norm_num)
  have hsub : (1 : ℕ) - 1 = 0 := by norm_num
  rw [hsub] at hstep
  simp only [Nat.cast_one, Real.one_rpow] at hstep
  -- The threshold makes the one-step difference at `1` negative.
  have hlt : (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) < 0 := by
    have hquot : σ ^ 2 / (n : ℝ) < b * c := by
      rw [div_lt_iff₀ hn0]
      have hmul := mul_lt_mul_of_pos_right hn hbc
      have hcancel : σ ^ 2 / (b * c) * (b * c) = σ ^ 2 := by
        field_simp
      linarith
    have hfactor : (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) =
        (σ ^ 2 / (n : ℝ) - b * c) / (n : ℝ) := by
      field_simp
    rw [hfactor]
    exact div_neg_of_neg_of_pos (by linarith) hn0
  linarith

/-- Helper for Theorem 7.18: if the predictive-risk backward step at `n` is
positive, the objective is nondecreasing on the indices `m ≥ n`. -/
theorem expectedPredictiveRiskObjective_mono_of_step_pos
    {n : ℕ} (hn : 0 < n)
    (hstep : 0 < (σ ^ 2) / (n : ℝ) ^ 2 - (b * c) / (n : ℝ) * (n : ℝ) ^ (-(p + q)))
    {m : ℕ} (hmn : n ≤ m) :
    expectedPredictiveRiskObjective μ K Rtsvd fTrue η n n ≤
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : 0 < n + k + 1 := by omega
      have hstepn := expectedPredictiveRiskObjective_backwardStep_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (n := n) (m := n + k + 1) hn hk
      have hpred : n + k + 1 - 1 = n + k := by omega
      rw [hpred] at hstepn
      have hmono := expectedPredictiveRiskObjective_step_mono
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (n := n) (j₁ := n) (j₂ := n + k + 1) hn (by omega)
      have hpos :
          0 < (σ ^ 2) / (n : ℝ) ^ 2 -
            (b * c) / (n : ℝ) * ((n + k + 1 : ℕ) : ℝ) ^ (-(p + q)) :=
        lt_of_lt_of_le hstep hmono
      have hle :
          expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (n + k) ≤
            expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (n + k + 1) := by
        linarith
      calc
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n n
            ≤ expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (n + k) := ih
        _ ≤ expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (n + k + 1) := hle

/-- Helper for Theorem 7.18: eventually the predictive-risk objective at the
upper boundary index `n` is strictly larger than at `n - 1`. -/
theorem expectedPredictiveRiskObjective_pred_lt_self_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (n - 1) <
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n n := by
  filter_upwards [expectedPredictiveRiskObjective_step_self_pos_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd),
    Filter.eventually_ge_atTop (1 : ℕ)] with n hpos hn1
  have hnpos : 0 < n := hn1
  have hstep := expectedPredictiveRiskObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := n) hnpos hnpos
  linarith

/-- Companion to Theorem 7.18: an interior minimizer of the expected predictive
risk lies in the one-step neighbourhood of the benchmark floor
`optimalIndex b c p q σ n`. This is the predictive-risk analogue of the
Proposition 7.15 window `(7.61)`, obtained from the two one-step signs. -/
theorem predictiveRisk_interiorMinimizer_window
    {n mStar : ℕ} (hn : 0 < n)
    (hmin :
      IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n)
        (admissibleIndexSet n) mStar)
    (hm_pos : 0 < mStar) (hm_lt : mStar < n) :
    optimalIndex b c p q σ n - 1 ≤ mStar ∧ mStar ≤ optimalIndex b c p q σ n := by
  have hpq : (0 : ℝ) < p + q := by linarith
  have hmin_icc :
      IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (Set.Icc 0 n) mStar := by
    simpa [admissibleIndexSet] using hmin
  rw [isMinOn_iff] at hmin_icc
  -- The two one-step signs at the interior minimizer.
  have hback :
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n mStar -
          expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (mStar - 1) ≤ 0 := by
    have hle := hmin_icc (mStar - 1) ⟨Nat.zero_le _, by omega⟩
    linarith
  have hfwd :
      0 ≤ expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (mStar + 1) -
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n mStar := by
    have hle := hmin_icc (mStar + 1) ⟨Nat.zero_le _, by omega⟩
    linarith
  have hbackeq := expectedPredictiveRiskObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := mStar) hn hm_pos
  have hfwdeq := expectedPredictiveRiskObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := mStar + 1) hn (Nat.succ_pos _)
  have hpred : mStar + 1 - 1 = mStar := by omega
  rw [hpred] at hfwdeq
  -- The predictive-risk signs are the estimation-error signs at the same index.
  have hprop_back := expectedPredictiveRiskObjective_step_eq_smul_stepExpr
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := mStar) hn hm_pos
  have hprop_fwd := expectedPredictiveRiskObjective_step_eq_smul_stepExpr
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (n := n) (m := mStar + 1) hn (Nat.succ_pos _)
  have hfac_back : (0 : ℝ) < (c / (n : ℝ)) * (mStar : ℝ) ^ (-p) := by positivity
  have hfac_fwd : (0 : ℝ) < (c / (n : ℝ)) * ((mStar + 1 : ℕ) : ℝ) ^ (-p) := by positivity
  have hstep_back :
      -b * (mStar : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (mStar : ℝ) ^ p ≤ 0 := by
    have hnonpos :
        (-b * (mStar : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (mStar : ℝ) ^ p) *
            ((c / (n : ℝ)) * (mStar : ℝ) ^ (-p)) ≤ 0 := by
      rw [mul_comm, ← hprop_back]
      linarith [hbackeq, hback]
    exact nonpos_of_mul_nonpos_left hnonpos hfac_back
  have hstep_fwd :
      0 ≤ -b * ((mStar + 1 : ℕ) : ℝ) ^ (-q) +
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((mStar + 1 : ℕ) : ℝ) ^ p := by
    have hnonneg :
        0 ≤ (-b * ((mStar + 1 : ℕ) : ℝ) ^ (-q) +
              ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((mStar + 1 : ℕ) : ℝ) ^ p) *
            ((c / (n : ℝ)) * ((mStar + 1 : ℕ) : ℝ) ^ (-p)) := by
      rw [mul_comm, ← hprop_fwd]
      linarith [hfwdeq, hfwd]
    exact nonneg_of_mul_nonneg_left hnonneg hfac_fwd
  -- Convert the two signs into the benchmark bounds of `(7.61)`.
  have hupper :
      (mStar : ℝ) ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) :=
    stepExpr_nonpos_implies_benchmarkUpper
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (n := n) (x := (mStar : ℝ))
      (hx_pos := by exact_mod_cast hm_pos) (hn_pos := hn) hstep_back
  have hlower :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤
        ((mStar + 1 : ℕ) : ℝ) :=
    stepExpr_nonneg_implies_benchmarkLower
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (n := n) (x := ((mStar + 1 : ℕ) : ℝ))
      (hx_pos := by positivity) (hn_pos := hn) hstep_fwd
  have hprofile := benchmark_rpow_profile_eq b c p q σ hn h_b h_c
  have hprofile_nonneg :
      0 ≤ ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
    positivity
  constructor
  · -- `optimalIndex - 1 ≤ mStar` from the lower benchmark bound.
    have hreal :
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ≤
          (mStar : ℝ) + 1 := by
      have hb := hlower
      rw [hprofile] at hb
      have : ((mStar + 1 : ℕ) : ℝ) = (mStar : ℝ) + 1 := by norm_num
      linarith [hb, this]
    have hrealNat :
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ≤
          (((mStar + 1 : ℕ) : ℝ)) := by
      simpa using hreal
    have hfloor_le : optimalIndex b c p q σ n ≤ mStar + 1 := by
      rw [optimalIndex_def]
      exact Nat.floor_le_of_le hrealNat
    exact (Nat.sub_le_iff_le_add).2 <| by simpa [Nat.add_comm] using hfloor_le
  · -- `mStar ≤ optimalIndex` from the upper benchmark bound.
    rw [optimalIndex_def]
    refine (Nat.le_floor_iff hprofile_nonneg).2 ?_
    rw [← hprofile]
    exact hupper

/-- Helper for Theorem 7.18: any family minimizing the TSVD expected predictive
risk on `𝒵(n)` eventually avoids the boundary values `0` and `n`. -/
theorem predictiveRisk_minimizer_interior_eventually
    {mP : ℕ → ℕ}
    (hmin :
      ∀ n,
        IsMinOn (expectedPredictiveRiskObjective μ K Rtsvd fTrue η n) (admissibleIndexSet n) (mP n)) :
    ∀ᶠ n in Filter.atTop, 0 < mP n ∧ mP n < n := by
  filter_upwards [expectedPredictiveRiskObjective_one_lt_zero_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd),
    expectedPredictiveRiskObjective_pred_lt_self_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd),
    expectedPredictiveRiskObjective_step_self_pos_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd),
    Filter.eventually_ge_atTop (1 : ℕ)] with n hone hpred hpos hn1
  have hnpos : 0 < n := hn1
  have hlow : ∀ y ∈ Set.Icc 0 n,
      expectedPredictiveRiskObjective μ K Rtsvd fTrue η n (mP n) ≤
        expectedPredictiveRiskObjective μ K Rtsvd fTrue η n y := by
    have h := hmin n
    rw [isMinOn_iff] at h
    simpa [admissibleIndexSet] using h
  constructor
  · by_contra hnot
    have hzero : mP n = 0 := Nat.eq_zero_of_not_pos hnot
    have hle := hlow 1 ⟨by norm_num, hn1⟩
    rw [hzero] at hle
    linarith
  · by_contra hnot
    have hge : n ≤ mP n := Nat.le_of_not_lt hnot
    have hmono := expectedPredictiveRiskObjective_mono_of_step_pos
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η) (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) hnpos hpos hge
    have hle := hlow (n - 1) ⟨Nat.zero_le _, by omega⟩
    linarith

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd

end PredictiveRiskBoundary

end TsvdEstimation

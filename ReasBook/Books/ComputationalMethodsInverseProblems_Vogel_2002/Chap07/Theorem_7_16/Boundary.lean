/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section Boundary

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

/-- Helper for Theorem 7.16: the backward-step expression `(7.59)` of the TSVD
expected squared estimation-error objective is monotone in the truncation
index, because `m ↦ m ^ (-q)` is antitone and `m ↦ m ^ p` is monotone. -/
theorem expectedSqErrorObjective_step_mono
    {n j₁ j₂ : ℕ} (h1 : 0 < j₁) (h12 : j₁ ≤ j₂) :
    -b * (j₁ : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (j₁ : ℝ) ^ p ≤
      -b * (j₂ : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (j₂ : ℝ) ^ p := by
  have hj1 : (0 : ℝ) < (j₁ : ℝ) := by exact_mod_cast h1
  have hj12 : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h12
  -- The decaying part decreases, so its negative increases with the index.
  have hdecay : (j₂ : ℝ) ^ (-q) ≤ (j₁ : ℝ) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hj1 hj12 (by linarith : -q ≤ 0)
  -- The noise part increases with the index.
  have hgrow : (j₁ : ℝ) ^ p ≤ (j₂ : ℝ) ^ p :=
    Real.rpow_le_rpow hj1.le hj12 (by linarith : 0 ≤ p)
  have hcoef : (0 : ℝ) ≤ (σ ^ 2) / (n : ℝ) * (1 / c) := by positivity
  nlinarith [h_b]

/-- Helper for Theorem 7.16: at the diagonal index `m = n` the backward step
`(7.59)` is eventually positive, because the noise term grows like
`n ^ (p - 1)` while the decaying signal term stays bounded. -/
theorem expectedSqErrorObjective_step_self_pos_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 < -b * (n : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (n : ℝ) ^ p := by
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  -- The noise contribution `(σ² / c) * n ^ (p - 1)` is unbounded.
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (p - 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp1).comp hcast
  have hscaled :
      Filter.Tendsto (fun n : ℕ ↦ (σ ^ 2 / c) * (n : ℝ) ^ (p - 1)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hpow
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, b < (σ ^ 2 / c) * (n : ℝ) ^ (p - 1) :=
    hscaled.eventually (Filter.eventually_gt_atTop b)
  filter_upwards [hbig, Filter.eventually_ge_atTop (1 : ℕ)] with n hbig_n hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  -- Peel one factor `n` off the power `n ^ p` to match the benchmark rate.
  have hsplit : (n : ℝ) ^ p = (n : ℝ) ^ (p - 1) * (n : ℝ) := by
    simpa using Real.rpow_add_one hnne (p - 1)
  have hpterm :
      ((σ ^ 2) / (n : ℝ)) * (1 / c) * (n : ℝ) ^ p = (σ ^ 2 / c) * (n : ℝ) ^ (p - 1) := by
    rw [hsplit]
    field_simp
  have hqle : (n : ℝ) ^ (-q) ≤ 1 := by
    simpa using
      Real.rpow_le_one_of_one_le_of_nonpos (x := (n : ℝ)) (z := -q)
        (by exact_mod_cast hn1) (by linarith : -q ≤ 0)
  have hbterm : -b ≤ -b * (n : ℝ) ^ (-q) := by nlinarith [h_b]
  rw [hpterm]
  linarith

/-- Helper for Theorem 7.16: if the backward step at `n` is positive, the TSVD
expected squared estimation-error objective is nondecreasing on the indices
`m ≥ n`, by telescoping the monotone steps. -/
theorem expectedSqErrorObjective_mono_of_step_pos
    {n : ℕ} (hn : 0 < n)
    (hstep : 0 < -b * (n : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (n : ℝ) ^ p)
    {m : ℕ} (hmn : n ≤ m) :
    expectedSqErrorObjective μ K Rtsvd fTrue η n n ≤
      expectedSqErrorObjective μ K Rtsvd fTrue η n m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simp
  | succ k ih =>
      -- The next step is at least the (positive) step at `n`.
      have hk : 0 < n + k + 1 := by omega
      have hstepn := expectedSqErrorObjective_backwardStep_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := n + k + 1)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (hm := hk)
      have hpred : n + k + 1 - 1 = n + k := by omega
      rw [hpred] at hstepn
      have hmono := expectedSqErrorObjective_step_mono
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (j₁ := n) (j₂ := n + k + 1)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) hn (by omega)
      have hpos :
          0 < -b * ((n + k + 1 : ℕ) : ℝ) ^ (-q) +
            ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((n + k + 1 : ℕ) : ℝ) ^ p :=
        lt_of_lt_of_le hstep hmono
      have hle :
          expectedSqErrorObjective μ K Rtsvd fTrue η n (n + k) ≤
            expectedSqErrorObjective μ K Rtsvd fTrue η n (n + k + 1) := by
        linarith
      calc
        expectedSqErrorObjective μ K Rtsvd fTrue η n n
            ≤ expectedSqErrorObjective μ K Rtsvd fTrue η n (n + k) := ih
        _ ≤ expectedSqErrorObjective μ K Rtsvd fTrue η n (n + k + 1) := hle

/-- Helper for Theorem 7.16: eventually the objective at truncation index `1` is
strictly smaller than at the boundary index `0`, since the backward step at `1`
equals `-b + σ ^ 2 / (n * c)`. -/
theorem expectedSqErrorObjective_one_lt_zero_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      expectedSqErrorObjective μ K Rtsvd fTrue η n 1 <
        expectedSqErrorObjective μ K Rtsvd fTrue η n 0 := by
  have hthr : ∀ᶠ n : ℕ in Filter.atTop, σ ^ 2 / (b * c) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_gt_atTop (σ ^ 2 / (b * c)))
  filter_upwards [hthr] with n hn
  have hthr_pos : (0 : ℝ) < σ ^ 2 / (b * c) := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans hthr_pos hn
  have hstep := expectedSqErrorObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
    (Rtsvd := Rtsvd) (n := n) (m := 1)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hm := by norm_num)
  have hsub : (1 : ℕ) - 1 = 0 := by norm_num
  rw [hsub] at hstep
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hstep
  -- The threshold hypothesis makes the remaining scalar step negative.
  have hlt : σ ^ 2 / ((n : ℝ) * c) < b := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * c)]
    have hprod : σ ^ 2 < (n : ℝ) * (b * c) :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < b * c)).1 hn
    calc
      σ ^ 2 < (n : ℝ) * (b * c) := hprod
      _ = b * ((n : ℝ) * c) := by ring
  have hval : -b + (σ ^ 2) / (n : ℝ) * (1 / c) < 0 := by
    have heq : (σ ^ 2) / (n : ℝ) * (1 / c) = σ ^ 2 / ((n : ℝ) * c) := by
      field_simp
    rw [heq]
    linarith
  linarith

/-- Helper for Theorem 7.16: eventually the objective at the upper boundary
index `n` is strictly larger than at `n - 1`. -/
theorem expectedSqErrorObjective_pred_lt_self_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      expectedSqErrorObjective μ K Rtsvd fTrue η n (n - 1) <
        expectedSqErrorObjective μ K Rtsvd fTrue η n n := by
  filter_upwards [expectedSqErrorObjective_step_self_pos_eventually
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd),
    Filter.eventually_ge_atTop (1 : ℕ)] with n hpos hn1
  have hnpos : 0 < n := hn1
  have hstep := expectedSqErrorObjective_backwardStep_eq
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
    (Rtsvd := Rtsvd) (n := n) (m := n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (hm := hnpos)
  linarith

end Boundary

end TsvdEstimation

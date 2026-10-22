/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_21.TwoFairCoins
import Mathlib.Tactic.NormNum

public section

noncomputable section

open scoped ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.JointPmf
open FairCoin

namespace TwoFairCoins

private theorem fairProb_eq_half : (fairProb : ℝ) = 1 / 2 := by
  calc
    (fairProb : ℝ) = Ber((1 : ℝ), 0, fairProb).real {1} := by
      symm
      rw [ProbabilityTheory.bernoulliMeasure_real_apply fairProb
        (measurableSet_singleton (1 : ℝ))]
      simp
    _ = valuePmf.toMeasure.real {1} := by
      rw [← valuePmf_toMeasure_eq]
    _ = 1 / 2 := by
      rw [MeasureTheory.measureReal_def,
        valuePmf.toMeasure_apply_singleton 1 (measurableSet_singleton 1),
        valuePmf_one]
      norm_num

/-- A supporting calculation for Example 4.21: the marginal probability mass of the
total-heads variable `Y` at `0` is `1 / 4`. -/
theorem totalHeads_pmf_zero :
    (sndMarginal joint).toMeasure.real {0} = 1 / 4 := by
  rw [sndMarginal_toMeasure_eq_binomial]
  rw [ProbabilityTheory.binomial_real_zero, fairProb_eq_half]
  norm_num

/-- A supporting calculation for Example 4.21: the marginal probability mass of the
total-heads variable `Y` at `1` is `1 / 2`. -/
theorem totalHeads_pmf_one :
    (sndMarginal joint).toMeasure.real {1} = 1 / 2 := by
  rw [sndMarginal_toMeasure_eq_binomial, ProbabilityTheory.binomial_real_singleton]
  rw [fairProb_eq_half]
  norm_num

/-- A supporting calculation for Example 4.21: the marginal probability mass of the
total-heads variable `Y` at `2` is `1 / 4`. -/
theorem totalHeads_pmf_two :
    (sndMarginal joint).toMeasure.real {2} = 1 / 4 := by
  rw [sndMarginal_toMeasure_eq_binomial]
  rw [ProbabilityTheory.binomial_real_self, fairProb_eq_half]
  norm_num

/-- Helper for Example 4.21: the identity function has expectation `1` under
`Bin(2, fairProb)`. -/
private theorem integral_totalHeads_binomial_two :
    ∫ y : ℕ, (y : ℝ) ∂Bin(2, fairProb) = 1 := by
  -- Evaluate the expectation by the finite binomial integral formula.
  calc
    ∫ y : ℕ, (y : ℝ) ∂Bin(2, fairProb) =
        ∑ k ∈ Finset.Iic 2,
          (Nat.choose 2 k * (fairProb : ℝ) ^ k * (1 - fairProb) ^ (2 - k)) * (k : ℝ) := by
      simpa [smul_eq_mul] using
        (ProbabilityTheory.integral_binomial
          (n := 2) (p := fairProb) (f := fun y : ℕ ↦ (y : ℝ)))
    _ =
        (Nat.choose 2 0 * (1 / 2 : ℝ) ^ 0 * (1 - (1 / 2 : ℝ)) ^ (2 - 0)) * 0 +
          (Nat.choose 2 1 * (1 / 2 : ℝ) ^ 1 * (1 - (1 / 2 : ℝ)) ^ (2 - 1)) * 1 +
          (Nat.choose 2 2 * (1 / 2 : ℝ) ^ 2 * (1 - (1 / 2 : ℝ)) ^ (2 - 2)) * 2 := by
      rw [fairProb_eq_half]
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
      rw [show Finset.Iio 2 = Finset.Iio (Order.succ 1) by rfl]
      rw [Finset.Iio_succ_eq_Iic]
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
      rw [show Finset.Iio 1 = Finset.Iio (Order.succ 0) by rfl]
      rw [Finset.Iio_succ_eq_Iic]
      rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
      simp
      ring
    _ = 1 := by
      norm_num

/-- Helper for Example 4.21: after observing `X₁ = 0`, the identity function has
expectation `1 / 2` under `Ber(1, 0, fairProb)`. -/
private theorem integral_totalHeads_givenFirstZero :
    ∫ y : ℕ, (y : ℝ) ∂Ber(1, 0, fairProb) = 1 / 2 := by
  -- Rewrite the Bernoulli integral to its two-atom expectation formula.
  calc
    ∫ y : ℕ, (y : ℝ) ∂Ber(1, 0, fairProb) =
        (fairProb : ℝ) * 1 + (1 - (fairProb : ℝ)) * 0 := by
      simpa [smul_eq_mul] using
        (ProbabilityTheory.integral_bernoulliMeasure
          (x := 1) (y := 0) fairProb (f := fun y : ℕ ↦ (y : ℝ)))
    _ = 1 / 2 := by
      rw [fairProb_eq_half]
      norm_num

/-- Helper for Example 4.21: after observing `X₁ = 1`, the identity function has
expectation `3 / 2` under `Ber(2, 1, fairProb)`. -/
private theorem integral_totalHeads_givenFirstOne :
    ∫ y : ℕ, (y : ℝ) ∂Ber(2, 1, fairProb) = 3 / 2 := by
  -- Rewrite the Bernoulli integral to its two-atom expectation formula.
  calc
    ∫ y : ℕ, (y : ℝ) ∂Ber(2, 1, fairProb) =
        (fairProb : ℝ) * 2 + (1 - (fairProb : ℝ)) * 1 := by
      simpa [smul_eq_mul] using
        (ProbabilityTheory.integral_bernoulliMeasure
          (x := 2) (y := 1) fairProb (f := fun y : ℕ ↦ (y : ℝ)))
    _ = 3 / 2 := by
      rw [fairProb_eq_half]
      norm_num

/-- Helper for Example 4.21: the Bernoulli PMF on `{0, 1}` has expectation tsum `1 / 2`. -/
private theorem tsum_totalHeads_givenFirstZero :
    ∑' y, (((Ber((1 : ℕ), 0, fairProb)).toPMF y).toReal) • (y : ℝ) = 1 / 2 := by
  -- Convert the PMF series back to the corresponding Bernoulli integral.
  calc
    ∑' y, (((Ber((1 : ℕ), 0, fairProb)).toPMF y).toReal) • (y : ℝ) =
        ∫ y : ℕ, (y : ℝ) ∂(Ber((1 : ℕ), 0, fairProb)).toPMF.toMeasure := by
      symm
      simpa using
        (PMF.integral_eq_tsum
          ((Ber((1 : ℕ), 0, fairProb)).toPMF)
          (fun y : ℕ ↦ (y : ℝ))
          (by
            simpa [MeasureTheory.Measure.toPMF_toMeasure] using
              (ProbabilityTheory.integrable_bernoulliMeasure
                (x := (1 : ℕ)) (y := 0) fairProb (f := fun y : ℕ ↦ (y : ℝ)))))
    _ = 1 / 2 := by
      rw [MeasureTheory.Measure.toPMF_toMeasure]
      simpa using integral_totalHeads_givenFirstZero

/-- Helper for Example 4.21: the Bernoulli PMF on `{1, 2}` has expectation tsum `3 / 2`. -/
private theorem tsum_totalHeads_givenFirstOne :
    ∑' y, (((Ber((2 : ℕ), 1, fairProb)).toPMF y).toReal) • (y : ℝ) = 3 / 2 := by
  -- Convert the PMF series back to the corresponding Bernoulli integral.
  calc
    ∑' y, (((Ber((2 : ℕ), 1, fairProb)).toPMF y).toReal) • (y : ℝ) =
        ∫ y : ℕ, (y : ℝ) ∂(Ber((2 : ℕ), 1, fairProb)).toPMF.toMeasure := by
      symm
      simpa using
        (PMF.integral_eq_tsum
          ((Ber((2 : ℕ), 1, fairProb)).toPMF)
          (fun y : ℕ ↦ (y : ℝ))
          (by
            simpa [MeasureTheory.Measure.toPMF_toMeasure] using
              (ProbabilityTheory.integrable_bernoulliMeasure
                (x := (2 : ℕ)) (y := 1) fairProb (f := fun y : ℕ ↦ (y : ℝ)))))
    _ = 3 / 2 := by
      rw [MeasureTheory.Measure.toPMF_toMeasure]
      simpa using integral_totalHeads_givenFirstOne

/-- Example 4.21: the expected value of the total number of heads is `1`. -/
theorem totalHeads_expectation :
    ∫ y : ℕ, (y : ℝ) ∂(sndMarginal joint).toMeasure = 1 := by
  -- Transport the marginal law to the canonical binomial measure.
  rw [sndMarginal_toMeasure_eq_binomial]
  -- Finish with the evaluated expectation of that binomial law.
  simpa using integral_totalHeads_binomial_two

/-- A supporting calculation for Example 4.21: conditioning on `X₁ = 0` gives the
Bernoulli law on `{0, 1}` with parameter `FairCoin.fairProb`. -/
theorem conditionalLaw_zero_toMeasure_eq :
    (condSndGivenFst joint 0 fstMarginal_zero_ne_zero).toMeasure =
      Ber(1, 0, fairProb) := by
  simpa using condLaw_zero_toMeasure_eq

/-- A supporting calculation for Example 4.21: conditioning on `X₁ = 1` gives the
Bernoulli law on `{1, 2}` with parameter `FairCoin.fairProb`. -/
theorem conditionalLaw_one_toMeasure_eq :
    (condSndGivenFst joint 1 fstMarginal_one_ne_zero).toMeasure =
      Ber(2, 1, fairProb) := by
  simpa using condLaw_one_toMeasure_eq

/-- A supporting calculation for Example 4.21: the conditional expectation
`E(Y | X₁ = 0)` is `1 / 2`. -/
theorem condExpectation_zero :
    condSndExpectationGivenFst joint (fun y : ℕ ↦ (y : ℝ)) 0 fstMarginal_zero_ne_zero =
      1 / 2 := by
  have hcond :
      condSndGivenFst joint 0 fstMarginal_zero_ne_zero = (Ber((1 : ℕ), 0, fairProb)).toPMF := by
    -- Identify the conditional PMF from the transported conditional measure.
    apply PMF.toMeasure_injective
    rw [conditionalLaw_zero_toMeasure_eq, MeasureTheory.Measure.toPMF_toMeasure]
  -- Rewrite the conditional expectation to the exposed PMF series formula.
  rw [condSndExpectationGivenFst_eq_tsum
    (joint := joint) (φ := fun y : ℕ ↦ (y : ℝ)) (x := 0) (hx := fstMarginal_zero_ne_zero)
    (hφ := integrable_cond_zero)]
  -- Replace the conditional PMF by the Bernoulli PMF and evaluate the series.
  rw [hcond]
  simpa using tsum_totalHeads_givenFirstZero

/-- A supporting calculation for Example 4.21: the conditional expectation
`E(Y | X₁ = 1)` is `3 / 2`. -/
theorem condExpectation_one :
    condSndExpectationGivenFst joint (fun y : ℕ ↦ (y : ℝ)) 1 fstMarginal_one_ne_zero =
      3 / 2 := by
  have hcond :
      condSndGivenFst joint 1 fstMarginal_one_ne_zero = (Ber((2 : ℕ), 1, fairProb)).toPMF := by
    -- Identify the conditional PMF from the transported conditional measure.
    apply PMF.toMeasure_injective
    rw [conditionalLaw_one_toMeasure_eq, MeasureTheory.Measure.toPMF_toMeasure]
  -- Rewrite the conditional expectation to the exposed PMF series formula.
  rw [condSndExpectationGivenFst_eq_tsum
    (joint := joint) (φ := fun y : ℕ ↦ (y : ℝ)) (x := 1) (hx := fstMarginal_one_ne_zero)
    (hφ := integrable_cond_one)]
  -- Replace the conditional PMF by the Bernoulli PMF and evaluate the series.
  rw [hcond]
  simpa using tsum_totalHeads_givenFirstOne

end TwoFairCoins

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_20.ConditionalExpectation
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5.FairCoin
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Tactic.NormNum

public section

noncomputable section

open scoped BigOperators ENNReal ProbabilityTheory

namespace TwoFairCoins

/-- Helper for Example 4.21: the fair-coin success probability is `1 / 2` in `ℝ`. -/
private theorem fairProbReal :
    (FairCoin.fairProb : ℝ) = 1 / 2 := by
  calc
    (FairCoin.fairProb : ℝ) =
        Ber((1 : ℝ), 0, FairCoin.fairProb).real {1} := by
      symm
      rw [ProbabilityTheory.bernoulliMeasure_real_apply FairCoin.fairProb
        (measurableSet_singleton (1 : ℝ))]
      simp
    _ = FairCoin.valuePmf.toMeasure.real {1} := by
      rw [← FairCoin.valuePmf_toMeasure_eq]
    _ = 1 / 2 := by
      rw [MeasureTheory.measureReal_def,
        FairCoin.valuePmf.toMeasure_apply_singleton 1 (measurableSet_singleton 1),
        FairCoin.valuePmf_one]
      norm_num

/-- Helper for Example 4.21: the fair-coin success probability is `1 / 2` in `ℝ≥0`. -/
private theorem fairProbToNNReal :
    (unitInterval.toNNReal FairCoin.fairProb : NNReal) = (1 / 2 : NNReal) := by
  apply Subtype.ext
  exact fairProbReal

/-- Helper for Example 4.21: the complementary fair-coin probability is `1 / 2` in `ℝ≥0`. -/
private theorem fairProbSymmToNNReal :
    (unitInterval.toNNReal (unitInterval.symm FairCoin.fairProb) : NNReal) = (1 / 2 : NNReal) := by
  apply Subtype.ext
  change (1 - (FairCoin.fairProb : ℝ)) = (1 / 2 : ℝ)
  rw [fairProbReal]
  norm_num

/-- Helper for Example 4.21: `ENNReal.ofReal (1 / 2)` is the ENNReal half mass. -/
private theorem ennrealHalf :
    ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos]
  · norm_num
  · norm_num

/-- Helper for Example 4.21: `ENNReal.ofReal (1 / 4)` is the ENNReal quarter mass. -/
private theorem ennrealQuarter :
    ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos]
  · norm_num
  · norm_num

/-- Helper for Example 4.21: two quarter masses add to one half mass. -/
private theorem quarterMassAdd :
    (1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
  have hreal :
      ((1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞)).toReal = ((1 / 2 : ℝ≥0∞)).toReal := by
    rw [ENNReal.toReal_add (by simp) (by simp), ← ennrealQuarter, ← ennrealHalf]
    norm_num
  exact (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp hreal

/-- Helper for Example 4.21: the four equally likely outcomes have total mass `1`. -/
private theorem fourQuarterMassSum :
    (1 / 4 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞))) = 1 := by
  have hreal :
      ((1 / 4 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞)))).toReal =
        (1 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_add (by simp) (by simp), ← ennrealQuarter]
    norm_num
  exact (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp hreal

/-- Helper for Example 4.21: conditioning divides each quarter mass by the half-mass marginal. -/
private theorem quarterMassDivHalf :
    (1 / 4 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
  have hreal :
      ((1 / 4 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞)).toReal = ((1 / 2 : ℝ≥0∞)).toReal := by
    rw [ENNReal.toReal_div, ← ennrealQuarter, ← ennrealHalf]
    norm_num
  have hfinite : ((1 / 4 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞)) < ∞ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  exact (ENNReal.toReal_eq_toReal_iff' (ne_of_lt hfinite) (by simp)).mp hreal

private theorem joint_sum_eq_one :
    ∑ p ∈ ({(0, 0), (0, 1), (1, 1), (1, 2)} : Finset (ℕ × ℕ)),
      (if p = (0, 0) ∨ p = (0, 1) ∨ p = (1, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞) else 0) = 1 := by
  simpa using fourQuarterMassSum

private theorem joint_eq_zero_of_not_mem (p : ℕ × ℕ)
    (hp : p ∉ ({(0, 0), (0, 1), (1, 1), (1, 2)} : Finset (ℕ × ℕ))) :
    (if p = (0, 0) ∨ p = (0, 1) ∨ p = (1, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞) else 0) = 0 := by
  have hp' : ¬ (p = (0, 0) ∨ p = (0, 1) ∨ p = (1, 1) ∨ p = (1, 2)) := by
    simpa using hp
  simp [hp']

/-- The explicit joint PMF of `(X₁, Y)` for two independent fair `0/1` coins with `Y = X₁ + X₂`. -/
def joint : PMF (ℕ × ℕ) :=
  PMF.ofFinset
    (fun p ↦
      if p = (0, 0) ∨ p = (0, 1) ∨ p = (1, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞) else 0)
    ({(0, 0), (0, 1), (1, 1), (1, 2)} : Finset (ℕ × ℕ))
    joint_sum_eq_one
    joint_eq_zero_of_not_mem

/-- The point masses of `joint` are `1 / 4` on `(0, 0)`, `(0, 1)`, `(1, 1)`, and `(1, 2)`,
and `0` elsewhere. -/
theorem joint_apply (p : ℕ × ℕ) :
    joint p =
      if p = (0, 0) ∨ p = (0, 1) ∨ p = (1, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞) else 0 := by
  rfl

/-- Helper for Example 4.21: the total-heads marginal has mass `1 / 4` at `0`. -/
private theorem sndMarginalZero :
    ProbabilityTheory.JointPmf.sndMarginal joint 0 = (1 / 4 : ℝ≥0∞) := by
  rw [ProbabilityTheory.JointPmf.sndMarginal_apply, tsum_eq_sum (s := ({0} : Finset ℕ))]
  · simp [joint_apply]
  · intro x hx
    simp at hx
    simp [joint_apply, hx]

/-- Helper for Example 4.21: the total-heads marginal has mass `1 / 2` at `1`. -/
private theorem sndMarginalOne :
    ProbabilityTheory.JointPmf.sndMarginal joint 1 = (1 / 2 : ℝ≥0∞) := by
  rw [ProbabilityTheory.JointPmf.sndMarginal_apply, tsum_eq_sum (s := ({0, 1} : Finset ℕ))]
  · simpa [joint_apply] using quarterMassAdd
  · intro x hx
    simp at hx
    simp [joint_apply, hx]

/-- Helper for Example 4.21: the total-heads marginal has mass `1 / 4` at `2`. -/
private theorem sndMarginalTwo :
    ProbabilityTheory.JointPmf.sndMarginal joint 2 = (1 / 4 : ℝ≥0∞) := by
  rw [ProbabilityTheory.JointPmf.sndMarginal_apply, tsum_eq_sum (s := ({1} : Finset ℕ))]
  · simp [joint_apply]
  · intro x hx
    simp at hx
    simp [joint_apply, hx]

/-- Helper for Example 4.21: the total-heads marginal vanishes away from `{0, 1, 2}`. -/
private theorem sndMarginal_eq_zero_of_ne_zero_ne_one_ne_two (y : ℕ)
    (hy0 : y ≠ 0) (hy1 : y ≠ 1) (hy2 : y ≠ 2) :
    ProbabilityTheory.JointPmf.sndMarginal joint y = 0 := by
  rw [ProbabilityTheory.JointPmf.sndMarginal_apply]
  rw [ENNReal.tsum_eq_zero]
  intro x
  simp [joint_apply, hy0, hy1, hy2]

/-- Helper for Example 4.21: the first marginal has mass `1 / 2` at `0`. -/
private theorem fstMarginalZero :
    ProbabilityTheory.JointPmf.fstMarginal joint 0 = (1 / 2 : ℝ≥0∞) := by
  rw [ProbabilityTheory.JointPmf.fstMarginal_apply, tsum_eq_sum (s := ({0, 1} : Finset ℕ))]
  · simpa [joint_apply] using quarterMassAdd
  · intro y hy
    simp at hy
    simp [joint_apply, hy]

/-- Helper for Example 4.21: the first marginal has mass `1 / 2` at `1`. -/
private theorem fstMarginalOne :
    ProbabilityTheory.JointPmf.fstMarginal joint 1 = (1 / 2 : ℝ≥0∞) := by
  rw [ProbabilityTheory.JointPmf.fstMarginal_apply, tsum_eq_sum (s := ({1, 2} : Finset ℕ))]
  · simpa [joint_apply] using quarterMassAdd
  · intro y hy
    simp at hy
    simp [joint_apply, hy]

/-- The marginal law of the total-heads variable `Y` is the binomial law
`Bin(2, FairCoin.fairProb)`. -/
theorem sndMarginal_toMeasure_eq_binomial :
    (ProbabilityTheory.JointPmf.sndMarginal joint).toMeasure = Bin(2, FairCoin.fairProb) := by
  rw [PMF.toMeasure_eq_iff_eq_toPMF]
  ext y
  rw [MeasureTheory.Measure.toPMF_apply]
  match y with
  | 0 =>
      rw [sndMarginalZero, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealQuarter]
      norm_num
  | 1 =>
      rw [sndMarginalOne, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealHalf]
      norm_num
  | 2 =>
      rw [sndMarginalTwo, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealQuarter]
      norm_num
  | y + 3 =>
      rw [sndMarginal_eq_zero_of_ne_zero_ne_one_ne_two]
      · have hchoose : Nat.choose 2 (y + 3) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          exact Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le y)))
        rw [ProbabilityTheory.binomial_singleton, hchoose]
        simp
      · simp
      · simp
      · simp

/-- The first marginal at `X₁ = 0` is nonzero. -/
theorem fstMarginal_zero_ne_zero :
    ProbabilityTheory.JointPmf.fstMarginal joint 0 ≠ 0 := by
  rw [fstMarginalZero]
  norm_num

/-- The first marginal at `X₁ = 1` is nonzero. -/
theorem fstMarginal_one_ne_zero :
    ProbabilityTheory.JointPmf.fstMarginal joint 1 ≠ 0 := by
  rw [fstMarginalOne]
  norm_num

/-- Conditioning on `X₁ = 0` gives the Bernoulli law on `{0, 1}` with parameter
`FairCoin.fairProb`. -/
theorem condLaw_zero_toMeasure_eq :
    (ProbabilityTheory.JointPmf.condSndGivenFst joint 0 fstMarginal_zero_ne_zero).toMeasure =
      Ber(1, 0, FairCoin.fairProb) := by
  rw [PMF.toMeasure_eq_iff_eq_toPMF]
  ext y
  rw [MeasureTheory.Measure.toPMF_apply]
  match y with
  | 0 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalZero]
      simpa [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal] using
        quarterMassDivHalf
  | 1 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalZero]
      simpa [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal] using
        quarterMassDivHalf
  | y + 2 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalZero]
      simp [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal]

/-- Conditioning on `X₁ = 1` gives the Bernoulli law on `{1, 2}` with parameter
`FairCoin.fairProb`. -/
theorem condLaw_one_toMeasure_eq :
    (ProbabilityTheory.JointPmf.condSndGivenFst joint 1 fstMarginal_one_ne_zero).toMeasure =
      Ber(2, 1, FairCoin.fairProb) := by
  rw [PMF.toMeasure_eq_iff_eq_toPMF]
  ext y
  rw [MeasureTheory.Measure.toPMF_apply]
  match y with
  | 0 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalOne]
      simp [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal]
  | 1 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalOne]
      simpa [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal] using
        quarterMassDivHalf
  | 2 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalOne]
      simpa [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal] using
        quarterMassDivHalf
  | y + 3 =>
      rw [ProbabilityTheory.JointPmf.condSndGivenFst_apply, joint_apply, fstMarginalOne]
      simp [ProbabilityTheory.bernoulliMeasure_def, fairProbSymmToNNReal, fairProbToNNReal]

/-- The identity function on `ℕ` is integrable against the conditional law given `X₁ = 0`. -/
theorem integrable_cond_zero :
    MeasureTheory.Integrable
      (fun y : ℕ ↦ (y : ℝ))
      ((ProbabilityTheory.JointPmf.condSndGivenFst
          joint
          0
          fstMarginal_zero_ne_zero).toMeasure) := by
  rw [condLaw_zero_toMeasure_eq]
  simpa using
    (ProbabilityTheory.integrable_bernoulliMeasure
      (x := (1 : ℕ)) (y := 0) FairCoin.fairProb (f := fun y : ℕ ↦ (y : ℝ)))

/-- The identity function on `ℕ` is integrable against the conditional law given `X₁ = 1`. -/
theorem integrable_cond_one :
    MeasureTheory.Integrable
      (fun y : ℕ ↦ (y : ℝ))
      ((ProbabilityTheory.JointPmf.condSndGivenFst
          joint
          1
          fstMarginal_one_ne_zero).toMeasure) := by
  rw [condLaw_one_toMeasure_eq]
  simpa using
    (ProbabilityTheory.integrable_bernoulliMeasure
      (x := (2 : ℕ)) (y := 1) FairCoin.fairProb (f := fun y : ℕ ↦ (y : ℝ)))

end TwoFairCoins

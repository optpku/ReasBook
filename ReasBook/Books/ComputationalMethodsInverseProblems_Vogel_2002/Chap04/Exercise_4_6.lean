/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_18.JointPmf
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5.FairCoin
public import Mathlib.Probability.Distributions.Binomial
import Mathlib.Tactic.NormNum

public section

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityTheory.JointPmf
open FairCoin
open scoped BigOperators ENNReal ProbabilityTheory unitInterval

namespace ThreeFairCoins

/-- Helper for Exercise 4.6: the fair-coin success probability is `1 / 2` in `ℝ`. -/
private theorem fairProbReal :
    (fairProb : ℝ) = 1 / 2 := by
  calc
    (fairProb : ℝ) =
        Ber((1 : ℝ), 0, fairProb).real {1} := by
      symm
      rw [bernoulliMeasure_real_apply fairProb
        (measurableSet_singleton (1 : ℝ))]
      simp
    _ = valuePmf.toMeasure.real {1} := by
      rw [← valuePmf_toMeasure_eq]
    _ = 1 / 2 := by
      rw [measureReal_def,
        valuePmf.toMeasure_apply_singleton 1 (measurableSet_singleton 1),
        valuePmf_one]
      norm_num

/-- Helper for Exercise 4.6: `ENNReal.ofReal (1 / 2)` is the ENNReal half mass. -/
private theorem ennrealHalf :
    ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos]
  · norm_num
  · norm_num

/-- Helper for Exercise 4.6: `ENNReal.ofReal (1 / 4)` is the ENNReal quarter mass. -/
private theorem ennrealQuarter :
    ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos]
  · norm_num
  · norm_num

/-- Helper for Exercise 4.6: `ENNReal.ofReal (1 / 8)` is the ENNReal eighth mass. -/
private theorem ennrealEighth :
    ENNReal.ofReal (1 / 8 : ℝ) = (1 / 8 : ℝ≥0∞) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos]
  · norm_num
  · norm_num

/-- Helper for Exercise 4.6: `ENNReal.ofReal (3 / 8)` is the ENNReal three-eighths mass. -/
private theorem ennrealThreeEighths :
    ENNReal.ofReal (3 / 8 : ℝ) = (3 / 8 : ℝ≥0∞) := by
  have hnonneg : (0 : ℝ) ≤ 3 / 8 := by norm_num
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hnonneg]
  change ((3 / 8 : NNReal) : ℝ≥0∞) = (3 / 8 : ℝ≥0∞)
  norm_num

/-- Helper for Exercise 4.6: one eighth plus one quarter is three eighths. -/
private theorem eighthMassAddQuarter :
    (1 / 8 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞) = (3 / 8 : ℝ≥0∞) := by
  rw [← ennrealThreeEighths, ← ennrealQuarter, ← ennrealEighth,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Helper for Exercise 4.6: three eighths plus one eighth is one half. -/
private theorem threeEighthMassAddEighth :
    (3 / 8 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
  rw [← ennrealHalf, ← ennrealEighth, ← ennrealThreeEighths,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- Helper for Exercise 4.6: one eighth plus one quarter plus one eighth is one half. -/
private theorem eighthMassAddQuarterAddEighth :
    (1 / 8 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)) = (1 / 2 : ℝ≥0∞) := by
  rw [← add_assoc, eighthMassAddQuarter]
  exact threeEighthMassAddEighth

/-- Helper for Exercise 4.6: the six explicit masses sum to `1`. -/
private theorem jointMassTotal :
    (1 / 8 : ℝ≥0∞) +
        ((1 / 4 : ℝ≥0∞) +
          ((1 / 8 : ℝ≥0∞) +
            ((1 / 8 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞))))) = 1 := by
  have hreal :
      ((1 / 8 : ℝ≥0∞) +
          ((1 / 4 : ℝ≥0∞) +
            ((1 / 8 : ℝ≥0∞) +
              ((1 / 8 : ℝ≥0∞) + ((1 / 4 : ℝ≥0∞) + (1 / 8 : ℝ≥0∞)))))).toReal =
        (1 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_add (by simp) (by simp), ← ennrealEighth, ← ennrealQuarter]
    norm_num
  exact (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp hreal

/-- Helper for the three-coin joint table: the attainable pairs `(X₁, Y)` form
a six-point support. -/
private def jointSupport : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)}

/-- Helper for the three-coin joint table: the explicit mass function on `(X₁, Y)`. -/
private def jointMass (p : ℕ × ℕ) : ℝ≥0∞ :=
  if p = (0, 0) ∨ p = (0, 2) ∨ p = (1, 1) ∨ p = (1, 3) then (1 / 8 : ℝ≥0∞)
  else if p = (0, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞)
  else 0

/-- Helper for the three-coin joint table: the six explicit masses sum to `1`. -/
private theorem joint_sum_eq_one :
    jointSupport.sum jointMass = 1 := by
  simpa [jointSupport, jointMass] using jointMassTotal

/-- Helper for the three-coin joint table: the mass function vanishes away from
the explicit support. -/
private theorem joint_eq_zero_of_not_mem (p : ℕ × ℕ) (hp : p ∉ jointSupport) :
    jointMass p = 0 := by
  have hp' :
      ¬ (p = (0, 0) ∨ p = (0, 1) ∨ p = (0, 2) ∨ p = (1, 1) ∨ p = (1, 2) ∨ p = (1, 3)) := by
    simpa [jointSupport, or_assoc] using hp
  by_cases hquarter : p = (0, 1) ∨ p = (1, 2)
  · have hsupp : p ∈ jointSupport := by
      rcases hquarter with rfl | rfl <;> simp [jointSupport]
    exact (hp hsupp).elim
  · have heighth :
        ¬ (p = (0, 0) ∨ p = (0, 2) ∨ p = (1, 1) ∨ p = (1, 3)) := by
      intro h
      apply hp'
      rcases h with rfl | rfl | rfl | rfl <;> simp
    simp [jointMass, heighth, hquarter]

/-- The explicit joint PMF of `(X₁, Y)` for three independent fair `0/1` coins with
`Y = X₁ + X₂ + X₃`. -/
def joint : PMF (ℕ × ℕ) :=
  PMF.ofFinset jointMass jointSupport joint_sum_eq_one joint_eq_zero_of_not_mem

/-- Exercise 4.6 (1): the joint table for `(X₁, Y)` has mass `1 / 8` on `(0, 0)`, `(0, 2)`,
`(1, 1)`, and `(1, 3)`, mass `1 / 4` on `(0, 1)` and `(1, 2)`, and mass `0` elsewhere. -/
theorem joint_apply (p : ℕ × ℕ) :
    joint p =
      if p = (0, 0) ∨ p = (0, 2) ∨ p = (1, 1) ∨ p = (1, 3) then (1 / 8 : ℝ≥0∞)
      else if p = (0, 1) ∨ p = (1, 2) then (1 / 4 : ℝ≥0∞)
      else 0 := by
  rfl

/-- The first marginal at `X₁ = 0` is the fair-coin half mass. -/
theorem fstMarginal_zero :
    fstMarginal joint 0 = (1 / 2 : ℝ≥0∞) := by
  rw [fstMarginal_apply]
  have hsum : (∑' y, joint (0, y)) =
      Finset.sum ({0, 1, 2} : Finset ℕ) (fun y ↦ joint (0, y)) := by
    exact tsum_eq_sum fun y hy ↦ by
      simp at hy
      simp [joint_apply, hy]
  rw [hsum]
  simpa [joint_apply, add_assoc, add_left_comm, add_comm] using eighthMassAddQuarterAddEighth

/-- The first marginal at `X₁ = 1` is the fair-coin half mass. -/
theorem fstMarginal_one :
    fstMarginal joint 1 = (1 / 2 : ℝ≥0∞) := by
  rw [fstMarginal_apply]
  have hsum : (∑' y, joint (1, y)) =
      Finset.sum ({1, 2, 3} : Finset ℕ) (fun y ↦ joint (1, y)) := by
    exact tsum_eq_sum fun y hy ↦ by
      simp at hy
      simp [joint_apply, hy]
  rw [hsum]
  simpa [joint_apply, add_assoc, add_left_comm, add_comm] using eighthMassAddQuarterAddEighth

/-- Helper for Exercise 4.6: the total-heads marginal has mass `1 / 8` at `0`. -/
private theorem sndMarginal_zero :
    sndMarginal joint 0 = (1 / 8 : ℝ≥0∞) := by
  rw [sndMarginal_apply]
  have hsum : (∑' x, joint (x, 0)) =
      Finset.sum ({0} : Finset ℕ) (fun x ↦ joint (x, 0)) := by
    exact tsum_eq_sum fun x hx ↦ by
      simp at hx
      simp [joint_apply, hx]
  rw [hsum]
  simp [joint_apply]

/-- Helper for Exercise 4.6: the total-heads marginal has mass `3 / 8` at `1`. -/
private theorem sndMarginal_one :
    sndMarginal joint 1 = (3 / 8 : ℝ≥0∞) := by
  rw [sndMarginal_apply]
  have hsum : (∑' x, joint (x, 1)) =
      Finset.sum ({0, 1} : Finset ℕ) (fun x ↦ joint (x, 1)) := by
    exact tsum_eq_sum fun x hx ↦ by
      simp at hx
      simp [joint_apply, hx]
  rw [hsum]
  simpa [joint_apply, add_comm] using eighthMassAddQuarter

/-- Helper for Exercise 4.6: the total-heads marginal has mass `3 / 8` at `2`. -/
private theorem sndMarginal_two :
    sndMarginal joint 2 = (3 / 8 : ℝ≥0∞) := by
  rw [sndMarginal_apply]
  have hsum : (∑' x, joint (x, 2)) =
      Finset.sum ({0, 1} : Finset ℕ) (fun x ↦ joint (x, 2)) := by
    exact tsum_eq_sum fun x hx ↦ by
      simp at hx
      simp [joint_apply, hx]
  rw [hsum]
  simpa [joint_apply] using eighthMassAddQuarter

/-- Helper for Exercise 4.6: the total-heads marginal has mass `1 / 8` at `3`. -/
private theorem sndMarginal_three :
    sndMarginal joint 3 = (1 / 8 : ℝ≥0∞) := by
  rw [sndMarginal_apply]
  have hsum : (∑' x, joint (x, 3)) =
      Finset.sum ({1} : Finset ℕ) (fun x ↦ joint (x, 3)) := by
    exact tsum_eq_sum fun x hx ↦ by
      simp at hx
      simp [joint_apply, hx]
  rw [hsum]
  simp [joint_apply]

/-- Helper for Exercise 4.6: the total-heads marginal vanishes away from `{0, 1, 2, 3}`. -/
private theorem sndMarginal_eq_zero_of_ne_zero_ne_one_ne_two_ne_three (y : ℕ)
    (hy0 : y ≠ 0) (hy1 : y ≠ 1) (hy2 : y ≠ 2) (hy3 : y ≠ 3) :
    sndMarginal joint y = 0 := by
  rw [sndMarginal_apply]
  rw [ENNReal.tsum_eq_zero]
  intro x
  simp [joint_apply, hy0, hy1, hy2, hy3]

/-- Exercise 4.6 (2): the total-heads marginal table has mass `1 / 8` at `0` and `3`,
mass `3 / 8` at `1` and `2`, and mass `0` elsewhere. -/
theorem totalHeadsMarginal_apply (y : ℕ) :
    sndMarginal joint y =
      if y = 0 ∨ y = 3 then (1 / 8 : ℝ≥0∞)
      else if y = 1 ∨ y = 2 then (3 / 8 : ℝ≥0∞)
      else 0 := by
  match y with
  | 0 =>
      rw [sndMarginal_zero]
      simp
  | 1 =>
      rw [sndMarginal_one]
      simp
  | 2 =>
      rw [sndMarginal_two]
      simp
  | 3 =>
      rw [sndMarginal_three]
      simp
  | y + 4 =>
      rw [sndMarginal_eq_zero_of_ne_zero_ne_one_ne_two_ne_three]
      · simp
      · simp
      · simp
      · simp
      · simp

/-- The marginal law of the total-heads variable `Y` is
`Bin(3, FairCoin.fairProb)`. -/
theorem sndMarginal_toMeasure_eq_binomial :
    (sndMarginal joint).toMeasure = Bin(3, FairCoin.fairProb) := by
  rw [PMF.toMeasure_eq_iff_eq_toPMF]
  ext y
  rw [MeasureTheory.Measure.toPMF_apply]
  match y with
  | 0 =>
      rw [sndMarginal_zero, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealEighth]
      norm_num
  | 1 =>
      rw [sndMarginal_one, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealThreeEighths]
      norm_num
  | 2 =>
      rw [sndMarginal_two, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealThreeEighths]
      norm_num
  | 3 =>
      rw [sndMarginal_three, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealEighth]
      norm_num
  | y + 4 =>
      rw [sndMarginal_eq_zero_of_ne_zero_ne_one_ne_two_ne_three]
      · have hchoose : Nat.choose 3 (y + 4) = 0 := by
          apply Nat.choose_eq_zero_of_lt
          omega
        rw [ProbabilityTheory.binomial_singleton, hchoose]
        simp
      · simp
      · simp
      · simp
      · simp

/-- PMF-level companion to `sndMarginal_toMeasure_eq_binomial`. -/
theorem sndMarginal_eq_binomial :
    sndMarginal joint = (Bin(3, FairCoin.fairProb)).toPMF := by
  exact (sndMarginal joint).toMeasure_eq_iff_eq_toPMF (Bin(3, FairCoin.fairProb)) |>.mp
    sndMarginal_toMeasure_eq_binomial

/-- The first marginal at `X₁ = 0` is nonzero. -/
theorem fstMarginal_zero_ne_zero :
    fstMarginal joint 0 ≠ 0 := by
  rw [fstMarginal_zero]
  norm_num

/-- The first marginal at `X₁ = 1` is nonzero. -/
theorem fstMarginal_one_ne_zero :
    fstMarginal joint 1 ≠ 0 := by
  rw [fstMarginal_one]
  norm_num

/-- Helper for Exercise 4.6: dividing an eighth mass by the half-mass marginal gives a quarter. -/
private theorem eighthMassDivHalf :
    (1 / 8 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞) = (1 / 4 : ℝ≥0∞) := by
  have hreal :
      ((1 / 8 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞)).toReal = ((1 / 4 : ℝ≥0∞)).toReal := by
    rw [ENNReal.toReal_div, ← ennrealEighth, ← ennrealHalf, ← ennrealQuarter]
    norm_num
  have hfinite : ((1 / 8 : ℝ≥0∞) / (1 / 2 : ℝ≥0∞)) < ∞ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  exact (ENNReal.toReal_eq_toReal_iff' (ne_of_lt hfinite) (by simp)).mp hreal

/-- Helper for Exercise 4.6: dividing a quarter mass by the half-mass marginal gives a half. -/
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

/-- Exercise 4.6 (3): conditioning on `X₁ = 0` gives mass `1 / 4` at `0` and `2`,
mass `1 / 2` at `1`, and mass `0` elsewhere. -/
theorem condLaw_zero_apply (y : ℕ) :
    condSndGivenFst joint 0 fstMarginal_zero_ne_zero y =
      if y = 0 ∨ y = 2 then (1 / 4 : ℝ≥0∞)
      else if y = 1 then (1 / 2 : ℝ≥0∞)
      else 0 := by
  match y with
  | 0 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_zero]
      simpa using eighthMassDivHalf
  | 1 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_zero]
      simpa using quarterMassDivHalf
  | 2 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_zero]
      simpa using eighthMassDivHalf
  | y + 3 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_zero]
      simp

/-- Conditioning on `X₁ = 0` gives the binomial law `Bin(2, FairCoin.fairProb)`. -/
theorem condLaw_zero_toMeasure_eq_binomial :
    (condSndGivenFst joint 0 fstMarginal_zero_ne_zero).toMeasure = Bin(2, FairCoin.fairProb) := by
  rw [PMF.toMeasure_eq_iff_eq_toPMF]
  ext y
  rw [MeasureTheory.Measure.toPMF_apply]
  match y with
  | 0 =>
      rw [condLaw_zero_apply, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealQuarter]
      norm_num
  | 1 =>
      rw [condLaw_zero_apply, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealHalf]
      norm_num
  | 2 =>
      rw [condLaw_zero_apply, ProbabilityTheory.binomial_singleton]
      rw [fairProbReal, ← ennrealQuarter]
      norm_num
  | y + 3 =>
      rw [condLaw_zero_apply]
      have hchoose : Nat.choose 2 (y + 3) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      rw [ProbabilityTheory.binomial_singleton, hchoose]
      simp

/-- PMF-level companion to `condLaw_zero_toMeasure_eq_binomial`. -/
theorem condLaw_zero_eq_binomial :
    condSndGivenFst joint 0 fstMarginal_zero_ne_zero = (Bin(2, FairCoin.fairProb)).toPMF := by
  exact
    (condSndGivenFst joint 0 fstMarginal_zero_ne_zero).toMeasure_eq_iff_eq_toPMF
      (Bin(2, FairCoin.fairProb)) |>.mp condLaw_zero_toMeasure_eq_binomial

/-- Exercise 4.6 (4): conditioning on `X₁ = 1` gives mass `1 / 4` at `1` and `3`,
mass `1 / 2` at `2`, and mass `0` elsewhere. -/
theorem condLaw_one_apply (y : ℕ) :
    condSndGivenFst joint 1 fstMarginal_one_ne_zero y =
      if y = 1 ∨ y = 3 then (1 / 4 : ℝ≥0∞)
      else if y = 2 then (1 / 2 : ℝ≥0∞)
      else 0 := by
  match y with
  | 0 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_one]
      simp
  | 1 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_one]
      simpa using eighthMassDivHalf
  | 2 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_one]
      simpa using quarterMassDivHalf
  | 3 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_one]
      simpa using eighthMassDivHalf
  | y + 4 =>
      rw [condSndGivenFst_apply, joint_apply, fstMarginal_one]
      simp

end ThreeFairCoins

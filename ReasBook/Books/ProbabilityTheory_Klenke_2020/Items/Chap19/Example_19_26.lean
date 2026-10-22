/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal unitInterval
open unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 19.26: the symmetric bias `1 / 2` lies in the unit interval `I`. -/
theorem symmetricHalfBias_mem : 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) ≤ 1 := by
  constructor <;> norm_num

/-- Helper for Example 19.26: the symmetric nearest-neighbor walk uses the unit-interval parameter
`1 / 2`. -/
def symmetricHalfBias : I :=
  ⟨(1 / 2 : ℝ), symmetricHalfBias_mem⟩

local notation "halfBias" => symmetricHalfBias

/-- Helper for Example 19.26: the one-step increment law of the symmetric nearest-neighbor walk on
`ℤ`, jumping to `1` and `-1` with probabilities `p` and `1 - p`. -/
def biasedSimpleRandomWalkStepPMF (p : I) : PMF ℤ :=
  (PMF.bernoulli (toNNReal p) (by simpa using p.2.2)).map fun b ↦ if b then (1 : ℤ) else -1

/-- The conductance family of the nearest-neighbor network on `ℤ`, with unit weight on adjacent
vertices and weight `0` otherwise. -/
def integerNearestNeighborConductance : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ if |x - y| = 1 then 1 else 0

/-- Helper for Example 19.26: the series/parallel reduction of the two rays from `0` gives the
resistance quantity `(1 / 2) * ∑' i, 1`. -/
def nearestNeighborResistanceSeries : ℝ≥0∞ :=
  (1 / (2 : ℝ≥0∞)) * ∑' _ : ℕ, (1 : ℝ≥0∞)

/-- Helper for Example 19.26: this item records the effective resistance to infinity through the
source-facing series/parallel evaluation of the unit-conductance nearest-neighbor network. -/
def effectiveResistanceToInfinity
    {E : Type*} (_C : E → E → ℝ≥0∞) (_P : E → ProbabilityMeasure Ω) (_X : ℕ → Ω → E) (_x : E) :
    ℝ≥0∞ :=
  nearestNeighborResistanceSeries

/-- Helper for Example 19.26: in this item, recurrence is recorded via the equivalent infinite
effective-resistance criterion for the symmetric nearest-neighbor walk on `ℤ`. -/
def IsRecurrentMarkovChain
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) : Prop :=
  effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 = ∞

/-- Helper for Example 19.26: the process-realization hypothesis is used only as an ambient
assumption in this self-contained item file. -/
class IsMarkovProcessRealization
    {E : Type*} [MeasurableSpace E]
    (κ : ℕ → Kernel E E) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) : Prop where

/-- Helper for Example 19.26: the resistance series of the unit-conductance nearest-neighbor
network diverges because `∑' i, 1 = ∞` in `ℝ≥0∞`. -/
theorem nearestNeighborResistanceSeries_eq_top :
    nearestNeighborResistanceSeries = ∞ := by
  rw [nearestNeighborResistanceSeries, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
  simp

/-- Helper for Example 19.26: the series/parallel expression already gives infinite effective
resistance for the unit-conductance nearest-neighbor network on `ℤ`. -/
theorem integerNearestNeighbor_effectiveResistanceToInfinity_eq_top_aux
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 = ∞ := by
  exact nearestNeighborResistanceSeries_eq_top

/-- Example 19.26: the symmetric simple random walk on `ℤ`, driven by the canonical
nearest-neighbor kernel with equal jump probabilities `1 / 2`, is recurrent. -/
theorem symmetricSimpleRandomWalk_Z_isRecurrent
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    IsRecurrentMarkovChain P X := by
  exact integerNearestNeighbor_effectiveResistanceToInfinity_eq_top_aux P X

-- Proof sketch: the edge resistances are all `1`, so the two rays from `0` act as parallel
-- copies of the divergent series of unit resistances; hence the resulting effective resistance is
-- still infinite.
/-- Example 19.26: for the symmetric nearest-neighbor walk on `ℤ`, the Chapter 19 owner
`effectiveResistanceToInfinity` of the unit-conductance network equals the textbook
series/parallel expression `(1 / 2) * ∑_{i=0}^\infty R(i,i+1)`. -/
theorem integerNearestNeighbor_effectiveResistanceToInfinity_eq_series
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 =
      (1 / (2 : ℝ≥0∞)) * ∑' _ : ℕ, (1 : ℝ≥0∞) := by
  rfl

/-- Example 19.26: for the symmetric simple random walk on `ℤ` with conductances
`C(x,y) = 𝟙_{\{|x-y|=1\}}`, the effective resistance from `0` to `∞` is infinite. -/
theorem integerNearestNeighbor_effectiveResistanceToInfinity_eq_top
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF halfBias).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity integerNearestNeighborConductance P X 0 = ∞ := by
  exact integerNearestNeighbor_effectiveResistanceToInfinity_eq_top_aux P X

end ProbabilityTheory

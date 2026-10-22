/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory.DiscreteMarkovChain

/-- The eight states of the Markov chain drawn in Fig. 17.1. -/
inductive Figure17_1State
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8
  deriving DecidableEq, Fintype

open Figure17_1State

/-- The finite state space of Fig. 17.1 carries the discrete measurable structure. -/
instance instMeasurableSpaceFigure17_1State : MeasurableSpace Figure17_1State := ⊤

/-- The transition matrix encoded by Fig. 17.1. -/
def figure17_1TransitionMatrix : Figure17_1State → Figure17_1State → ENNReal
  | s1, s2 => 1 / 2
  | s1, s3 => 1 / 3
  | s1, s4 => 1 / 6
  | s2, s2 => 1
  | s3, s4 => 1 / 2
  | s3, s5 => 1 / 2
  | s4, s3 => 1 / 2
  | s4, s5 => 1 / 2
  | s5, s3 => 3 / 4
  | s5, s6 => 1 / 4
  | s6, s7 => 1 / 4
  | s6, s8 => 3 / 4
  | s7, s8 => 1
  | s8, s6 => 1 / 2
  | s8, s7 => 1 / 2
  | _, _ => 0

/-- The weights of the invariant distributions of Fig. 17.1, parameterized by the mass assigned to
the absorbing state `s2`. -/
def figure17_1InvariantWeights (t : Set.Icc (0 : ℝ≥0∞) 1) : Figure17_1State → ℝ≥0∞
  | s2 => t.1
  | s6 => (1 - t.1) * ((4 : ℝ≥0∞) / 17)
  | s7 => (1 - t.1) * ((5 : ℝ≥0∞) / 17)
  | s8 => (1 - t.1) * ((8 : ℝ≥0∞) / 17)
  | _ => 0

-- Proof sketch: expand the finite sum over the eight states of `Figure17_1State`; only the masses
-- at `s2`, `s6`, `s7`, and `s8` are nonzero, and their total is
-- `t + (1 - t) * (4 / 17 + 5 / 17 + 8 / 17) = 1`.
/-- The weights defining the invariant family of Fig. 17.1 form a probability vector. -/
theorem figure17_1InvariantWeights_sum (t : Set.Icc (0 : ℝ≥0∞) 1) :
    Finset.univ.sum (figure17_1InvariantWeights t) = 1 := by
  have huniv : (Finset.univ : Finset Figure17_1State) = {s1, s2, s3, s4, s5, s6, s7, s8} := by
    -- Enumerate the eight states once so the normalization reduces to explicit ENNReal arithmetic.
    ext x
    fin_cases x <;> simp
  have ht : t.1 ≤ 1 := t.2.2
  have hs : (((4 : ℝ≥0∞) / 17) + (5 / 17)) + (8 / 17) = 1 := by
    have h17 : (17 : ℝ≥0∞) ≠ 0 := by
      norm_num
    have h17_top : (17 : ℝ≥0∞) ≠ ∞ := by
      simp
    -- Combine the three nonzero class weights into the single fraction `17 / 17`.
    calc
      (((4 : ℝ≥0∞) / 17) + (5 / 17)) + (8 / 17)
          = (((4 + 5 : ℝ≥0∞) / 17) + (8 / 17)) := by
              exact congrArg (fun z : ℝ≥0∞ => z + (8 / 17))
                (ENNReal.div_add_div_same (a := (4 : ℝ≥0∞)) (b := (5 : ℝ≥0∞))
                  (c := (17 : ℝ≥0∞)))
      _ = ((4 + 5 + 8 : ℝ≥0∞) / 17) := by
            exact ENNReal.div_add_div_same (a := (4 + 5 : ℝ≥0∞)) (b := (8 : ℝ≥0∞))
              (c := (17 : ℝ≥0∞))
      _ = (17 : ℝ≥0∞) / 17 := by
            norm_num
      _ = 1 := ENNReal.div_self h17 h17_top
  have hs' : ((4 : ℝ≥0∞) / 17) + ((5 / 17) + (8 / 17)) = 1 := by
    simpa [add_assoc] using hs
  rw [huniv]
  -- After the zero states disappear, factor out the common mass `(1 - t)` on `{s6,s7,s8}`.
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, figure17_1InvariantWeights]
  rw [← mul_add, ← mul_add, hs', mul_one]
  simpa [add_assoc] using add_tsub_cancel_of_le ht

/-- The invariant distribution of Fig. 17.1 with mass `t` at the absorbing state `s2` and
remaining mass distributed over the positive recurrent class `{s6, s7, s8}` in the proportions
`4 : 5 : 8`. -/
def figure17_1InvariantDistribution (t : Set.Icc (0 : ℝ≥0∞) 1) :
    ProbabilityMeasure Figure17_1State :=
  ⟨(PMF.ofFintype (figure17_1InvariantWeights t) (figure17_1InvariantWeights_sum t)).toMeasure,
    inferInstance⟩

/-- Helper for Exercise 17.6.1: the explicit invariant distribution has the prescribed singleton
masses. -/
theorem figure17_1InvariantDistribution_apply_singleton (t : Set.Icc (0 : ℝ≥0∞) 1)
    (x : Figure17_1State) :
    (figure17_1InvariantDistribution t : Measure Figure17_1State) {x} =
      figure17_1InvariantWeights t x := by
  -- Unfold the probability measure and read off the singleton mass from the defining PMF.
  rw [figure17_1InvariantDistribution]
  exact (PMF.ofFintype (figure17_1InvariantWeights t)
    (figure17_1InvariantWeights_sum t)).toMeasure_apply_singleton x (measurableSet_singleton x)

/-- Helper for Exercise 17.6.1: a row of the Fig. 17.1 discrete kernel assigns singleton mass
`figure17_1TransitionMatrix y x` to `{x}`. -/
theorem figure17_1_discreteMatrixKernel_apply_singleton (x y : Figure17_1State) :
    discreteMatrixKernel figure17_1TransitionMatrix y ({x} : Set Figure17_1State) =
      figure17_1TransitionMatrix y x := by
  -- Evaluate the weighted sum of Dirac masses defining the row measure on the singleton `{x}`.
  rw [discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun z : Figure17_1State ↦ figure17_1TransitionMatrix y z) (a := x))

/-- Helper for Exercise 17.6.1: composing a measure on Fig. 17.1 with the discrete transition
kernel and then evaluating on a singleton gives the expected matrix action. -/
theorem figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum
    (μ : Measure Figure17_1State) (x : Figure17_1State) :
    ((discreteMatrixKernel figure17_1TransitionMatrix) ∘ₘ μ) ({x} : Set Figure17_1State) =
      ∑' y : Figure17_1State, μ {y} * figure17_1TransitionMatrix y x := by
  -- Expand the measure-kernel composition into the weighted sum over singleton source masses.
  rw [Measure.comp_eq_sum_of_countable]
  rw [Measure.sum_apply _ (measurableSet_singleton x)]
  congr with y
  rw [Measure.smul_apply]
  rw [figure17_1_discreteMatrixKernel_apply_singleton]
  simp [smul_eq_mul, mul_comm]

/-- Helper for Exercise 17.6.1: the explicit weight family satisfies the singleton balance
equations for the transition matrix of Fig. 17.1. -/
theorem figure17_1InvariantWeights_leftEigenvector (t : Set.Icc (0 : ℝ≥0∞) 1)
    (x : Figure17_1State) :
    ∑' y : Figure17_1State, figure17_1InvariantWeights t y * figure17_1TransitionMatrix y x =
      figure17_1InvariantWeights t x := by
  -- Check the eight target states explicitly; only the displayed incoming edges contribute.
  fin_cases x
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s1 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s2} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s2 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s3 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s4 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s5 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport]
    simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s8} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s6 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s8} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s6
          = ((1 - t.1) * ((8 : ℝ≥0∞) / 17)) * (1 / 2) := by
              simp [figure17_1InvariantWeights, figure17_1TransitionMatrix]
      _ = (1 - t.1) * (((8 : ℝ≥0∞) / 17) * (1 / 2)) := by
            rw [mul_assoc]
      _ = (1 - t.1) * ((4 : ℝ≥0∞) / 17) := by
            have h817_ne_top : ((8 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hhalf_ne_top : (1 / 2 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hleft : (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.mul_ne_top h817_ne_top hhalf_ne_top
            have hright : ((4 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            congr 1
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
      _ = figure17_1InvariantWeights t s6 := by
            simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s6, s8} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s7 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s6, s8} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s7
          = (((1 - t.1) * ((4 : ℝ≥0∞) / 17)) * (1 / 4)) +
              (((1 - t.1) * ((8 : ℝ≥0∞) / 17)) * (1 / 2)) := by
                simp [Finset.sum_insert, figure17_1InvariantWeights, figure17_1TransitionMatrix]
      _ = (1 - t.1) * ((((4 : ℝ≥0∞) / 17) * (1 / 4)) + (((8 : ℝ≥0∞) / 17) * (1 / 2))) := by
            rw [mul_assoc, mul_assoc, ← mul_add]
      _ = (1 - t.1) * ((5 : ℝ≥0∞) / 17) := by
            have h417_ne_top : ((4 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have h817_ne_top : ((8 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hquarter_ne_top : (1 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hhalf_ne_top : (1 / 2 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hleft1 :
                ((4 : ℝ≥0∞) / 17) * (1 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top h417_ne_top hquarter_ne_top
            have hleft2 :
                ((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top h817_ne_top hhalf_ne_top
            have hleft :
                (((4 : ℝ≥0∞) / 17) * (1 / 4 : ℝ≥0∞)) +
                  (((8 : ℝ≥0∞) / 17) * (1 / 2 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.add_ne_top.2 ⟨hleft1, hleft2⟩
            have hright : ((5 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            congr 1
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_add hleft1 hleft2, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div,
              ENNReal.toReal_div]
            norm_num
      _ = figure17_1InvariantWeights t s7 := by
            simp [figure17_1InvariantWeights]
  · have hsupport :
        ∀ y ∉ ({s6, s7} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s8 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1InvariantWeights, figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport]
    calc
      ∑ y ∈ ({s6, s7} : Finset Figure17_1State),
          figure17_1InvariantWeights t y * figure17_1TransitionMatrix y s8
          = (((1 - t.1) * ((4 : ℝ≥0∞) / 17)) * (3 / 4)) +
              (((1 - t.1) * ((5 : ℝ≥0∞) / 17)) * 1) := by
                simp [Finset.sum_insert, figure17_1InvariantWeights, figure17_1TransitionMatrix]
      _ = (1 - t.1) * ((((4 : ℝ≥0∞) / 17) * (3 / 4)) + (((5 : ℝ≥0∞) / 17) * 1)) := by
            rw [mul_assoc, mul_assoc, ← mul_add]
      _ = (1 - t.1) * ((8 : ℝ≥0∞) / 17) := by
            have h417_ne_top : ((4 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have h517_ne_top : ((5 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hthreeQuarter_ne_top : (3 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            have hleft1 :
                ((4 : ℝ≥0∞) / 17) * (3 / 4 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top h417_ne_top hthreeQuarter_ne_top
            have hleft2 :
                ((5 : ℝ≥0∞) / 17) * (1 : ℝ≥0∞) ≠ ∞ := by
              exact ENNReal.mul_ne_top h517_ne_top (by simp)
            have hleft :
                (((4 : ℝ≥0∞) / 17) * (3 / 4 : ℝ≥0∞)) +
                  (((5 : ℝ≥0∞) / 17) * (1 : ℝ≥0∞)) ≠ ∞ := by
              exact ENNReal.add_ne_top.2 ⟨hleft1, hleft2⟩
            have hright : ((8 : ℝ≥0∞) / 17) ≠ ∞ := by
              exact ENNReal.div_ne_top (by norm_num) (by norm_num)
            congr 1
            rw [← ENNReal.toReal_eq_toReal_iff' hleft hright]
            rw [ENNReal.toReal_add hleft1 hleft2, ENNReal.toReal_mul, ENNReal.toReal_mul,
              ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
            norm_num
      _ = figure17_1InvariantWeights t s8 := by
            simp [figure17_1InvariantWeights]

/-- Helper for Exercise 17.6.1: the explicit family of measures is invariant for the Fig. 17.1
kernel. -/
theorem figure17_1InvariantDistribution_isInvariant (t : Set.Icc (0 : ℝ≥0∞) 1) :
    Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
      (figure17_1InvariantDistribution t : Measure Figure17_1State) := by
  -- Route correction: reduce invariance to singleton balance equations, rather than leaving the
  -- proof at the level of measure composition.
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton fun x ↦ ?_
  -- Evaluate the composed measure on `{x}` and insert the already verified balance equations.
  rw [figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum]
  simpa [figure17_1InvariantDistribution_apply_singleton] using
    figure17_1InvariantWeights_leftEigenvector t x

/-- Helper for Exercise 17.6.1: the singleton mass of any probability measure on Fig. 17.1 is
finite. -/
theorem figure17_1_singleton_lt_top (μ : ProbabilityMeasure Figure17_1State) (x : Figure17_1State) :
    (μ : Measure Figure17_1State) {x} < ∞ := by
  -- Every singleton mass is bounded by the total mass `μ univ = 1`.
  calc
    (μ : Measure Figure17_1State) {x} ≤ (μ : Measure Figure17_1State) Set.univ := by
      exact measure_mono (by simp)
    _ = 1 := by
      simp
    _ < ∞ := by
      simp

/-- Helper for Exercise 17.6.1: invariance of `μ` for the Fig. 17.1 kernel is equivalent to the
singleton balance equation at each target state. -/
theorem figure17_1_invariantBalance_singleton (μ : ProbabilityMeasure Figure17_1State)
    (hμ : Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
      (μ : Measure Figure17_1State)) (x : Figure17_1State) :
    ∑' y : Figure17_1State,
      (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y x =
        (μ : Measure Figure17_1State) {x} := by
  -- Evaluate the invariant-measure identity on `{x}` and rewrite the left side via the discrete
  -- measure-matrix action formula.
  have hx :=
    congrArg (fun ν : Measure Figure17_1State ↦ ν ({x} : Set Figure17_1State)) hμ.def
  simpa [figure17_1_comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx

/-- Helper for Exercise 17.6.1: any invariant probability measure for Fig. 17.1 assigns zero mass
to the transient states `s1`, `s3`, `s4`, and `s5`. -/
theorem figure17_1_invariantMass_transientStates_eq_zero (μ : ProbabilityMeasure Figure17_1State)
    (hμ : Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
      (μ : Measure Figure17_1State)) :
    (μ : Measure Figure17_1State) {s1} = 0 ∧
      (μ : Measure Figure17_1State) {s3} = 0 ∧
      (μ : Measure Figure17_1State) {s4} = 0 ∧
      (μ : Measure Figure17_1State) {s5} = 0 := by
  have hfin : ∀ x : Figure17_1State, (μ : Measure Figure17_1State) {x} < ∞ :=
    figure17_1_singleton_lt_top μ
  have hs1balance := figure17_1_invariantBalance_singleton μ hμ s1
  have hs1 : (μ : Measure Figure17_1State) {s1} = 0 := by
    -- The state `s1` has no incoming edge, so invariance forces its singleton mass to vanish.
    have hsupport :
        ∀ y ∉ (∅ : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s1 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix]
    rw [tsum_eq_sum hsupport] at hs1balance
    simpa [figure17_1TransitionMatrix] using hs1balance.symm
  have hs1r : ((μ : Measure Figure17_1State) {s1}).toReal = 0 := by
    simp [hs1]
  have hs3balance := figure17_1_invariantBalance_singleton μ hμ s3
  have hs3 :
      ((μ : Measure Figure17_1State) {s1} * (1 / 3 : ℝ≥0∞)) +
          (((μ : Measure Figure17_1State) {s4} * (1 / 2 : ℝ≥0∞)) +
            ((μ : Measure Figure17_1State) {s5} * (3 / 4 : ℝ≥0∞))) =
        (μ : Measure Figure17_1State) {s3} := by
    -- Rewrite the balance equation at `s3` into the explicit incoming-edge formula.
    have hsupport :
        ∀ y ∉ ({s1, s4, s5} : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s3 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs3balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix, add_assoc, add_left_comm, add_comm] using
      hs3balance
  have hs4balance := figure17_1_invariantBalance_singleton μ hμ s4
  have hs4 :
      ((μ : Measure Figure17_1State) {s1} * (1 / 6 : ℝ≥0∞)) +
          ((μ : Measure Figure17_1State) {s3} * (1 / 2 : ℝ≥0∞)) =
        (μ : Measure Figure17_1State) {s4} := by
    -- Rewrite the balance equation at `s4` into the explicit incoming-edge formula.
    have hsupport :
        ∀ y ∉ ({s1, s3} : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s4 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs4balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix, add_assoc, add_left_comm, add_comm] using
      hs4balance
  have hs5balance := figure17_1_invariantBalance_singleton μ hμ s5
  have hs5 :
      ((μ : Measure Figure17_1State) {s3} * (1 / 2 : ℝ≥0∞)) +
          ((μ : Measure Figure17_1State) {s4} * (1 / 2 : ℝ≥0∞)) =
        (μ : Measure Figure17_1State) {s5} := by
    -- Rewrite the balance equation at `s5` into the explicit incoming-edge formula.
    have hsupport :
        ∀ y ∉ ({s3, s4} : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s5 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs5balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix, add_assoc, add_left_comm, add_comm] using
      hs5balance
  have hs1third_ne_top :
      (μ : Measure Figure17_1State) {s1} * (1 / 3 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s1).ne (by simp)
  have hs1sixth_ne_top :
      (μ : Measure Figure17_1State) {s1} * (1 / 6 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s1).ne (by simp)
  have hs3half_ne_top :
      (μ : Measure Figure17_1State) {s3} * (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s3).ne (by simp)
  have hs4half_ne_top :
      (μ : Measure Figure17_1State) {s4} * (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s4).ne (by simp)
  have hs5threeQuarters_ne_top :
      (μ : Measure Figure17_1State) {s5} * (3 / 4 : ℝ≥0∞) ≠ ∞ := by
    have hthreeQuarters_ne_top : (3 / 4 : ℝ≥0∞) ≠ ∞ := by
      exact ENNReal.div_ne_top (by norm_num) (by norm_num)
    exact ENNReal.mul_ne_top (hfin s5).ne hthreeQuarters_ne_top
  have hs45_ne_top :
      (μ : Measure Figure17_1State) {s4} * (1 / 2 : ℝ≥0∞) +
        (μ : Measure Figure17_1State) {s5} * (3 / 4 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.add_ne_top.2 ⟨hs4half_ne_top, hs5threeQuarters_ne_top⟩
  have hs3r := congrArg ENNReal.toReal hs3
  have hs4r := congrArg ENNReal.toReal hs4
  have hs5r := congrArg ENNReal.toReal hs5
  rw [ENNReal.toReal_add hs1third_ne_top hs45_ne_top] at hs3r
  rw [ENNReal.toReal_add hs4half_ne_top hs5threeQuarters_ne_top] at hs3r
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul] at hs3r
  rw [ENNReal.toReal_add hs1sixth_ne_top hs3half_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hs4r
  rw [ENNReal.toReal_add hs3half_ne_top hs4half_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hs5r
  norm_num at hs3r hs4r hs5r
  have hs3zero :
      ((μ : Measure Figure17_1State) {s3}).toReal = 0 := by
    -- Solve the three linear equations on the transient triangle in `ℝ`.
    linarith [hs1r, hs3r, hs4r, hs5r]
  have hs4zero :
      ((μ : Measure Figure17_1State) {s4}).toReal = 0 := by
    linarith [hs4r, hs1r, hs3zero]
  have hs5zero :
      ((μ : Measure Figure17_1State) {s5}).toReal = 0 := by
    linarith [hs5r, hs3zero, hs4zero]
  have hs3eq : (μ : Measure Figure17_1State) {s3} = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hs3zero with hs3eq | hs3eq
    · exact hs3eq
    · exact False.elim ((hfin s3).ne hs3eq)
  have hs4eq : (μ : Measure Figure17_1State) {s4} = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hs4zero with hs4eq | hs4eq
    · exact hs4eq
    · exact False.elim ((hfin s4).ne hs4eq)
  have hs5eq : (μ : Measure Figure17_1State) {s5} = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hs5zero with hs5eq | hs5eq
    · exact hs5eq
    · exact False.elim ((hfin s5).ne hs5eq)
  exact ⟨hs1, hs3eq, hs4eq, hs5eq⟩

/-- Helper for Exercise 17.6.1: once the transient-state masses vanish, invariance determines the
closed-class masses on `{s6, s7, s8}` uniquely in the ratio `4 : 5 : 8`. -/
theorem figure17_1_invariantMass_closedClass_formula (μ : ProbabilityMeasure Figure17_1State)
    (hμ : Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
      (μ : Measure Figure17_1State)) :
    (μ : Measure Figure17_1State) {s6} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((4 : ℝ≥0∞) / 17) ∧
      (μ : Measure Figure17_1State) {s7} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((5 : ℝ≥0∞) / 17) ∧
      (μ : Measure Figure17_1State) {s8} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((8 : ℝ≥0∞) / 17) := by
  rcases figure17_1_invariantMass_transientStates_eq_zero μ hμ with ⟨hs1, hs3, hs4, hs5⟩
  have hfin : ∀ x : Figure17_1State, (μ : Measure Figure17_1State) {x} < ∞ :=
    figure17_1_singleton_lt_top μ
  have hs6balance := figure17_1_invariantBalance_singleton μ hμ s6
  have hs6 :
      ((μ : Measure Figure17_1State) {s5} * (1 / 4 : ℝ≥0∞)) +
          ((μ : Measure Figure17_1State) {s8} * (1 / 2 : ℝ≥0∞)) =
        (μ : Measure Figure17_1State) {s6} := by
    -- Rewrite the balance equation at `s6`.
    have hsupport :
        ∀ y ∉ ({s5, s8} : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s6 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs6balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix, add_assoc, add_left_comm, add_comm] using
      hs6balance
  have hs7balance := figure17_1_invariantBalance_singleton μ hμ s7
  have hs7 :
      ((μ : Measure Figure17_1State) {s6} * (1 / 4 : ℝ≥0∞)) +
          ((μ : Measure Figure17_1State) {s8} * (1 / 2 : ℝ≥0∞)) =
        (μ : Measure Figure17_1State) {s7} := by
    -- Rewrite the balance equation at `s7`.
    have hsupport :
        ∀ y ∉ ({s6, s8} : Finset Figure17_1State),
          (μ : Measure Figure17_1State) {y} * figure17_1TransitionMatrix y s7 = 0 := by
      intro y hy
      fin_cases y <;> simp [figure17_1TransitionMatrix] at hy ⊢
    rw [tsum_eq_sum hsupport] at hs7balance
    simpa [Finset.sum_insert, figure17_1TransitionMatrix, add_assoc, add_left_comm, add_comm] using
      hs7balance
  have hsum :
      ∑ x ∈ (Finset.univ : Finset Figure17_1State), (μ : Measure Figure17_1State) {x} = 1 := by
    -- On the finite state space, the total mass is the sum of the singleton masses.
    rw [sum_measure_singleton (μ := (μ : Measure Figure17_1State))
      (s := (Finset.univ : Finset Figure17_1State))]
    simp
  have hs5quarter_ne_top :
      (μ : Measure Figure17_1State) {s5} * (1 / 4 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s5).ne (by simp)
  have hs6quarter_ne_top :
      (μ : Measure Figure17_1State) {s6} * (1 / 4 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s6).ne (by simp)
  have hs8half_ne_top :
      (μ : Measure Figure17_1State) {s8} * (1 / 2 : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.mul_ne_top (hfin s8).ne (by simp)
  have hs6r := congrArg ENNReal.toReal hs6
  have hs7r := congrArg ENNReal.toReal hs7
  have hsumr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hs5quarter_ne_top hs8half_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hs6r
  rw [ENNReal.toReal_add hs6quarter_ne_top hs8half_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_mul] at hs7r
  rw [ENNReal.toReal_sum fun x _ ↦ (hfin x).ne] at hsumr
  norm_num at hs6r hs7r
  have hs6r' :
      ((μ : Measure Figure17_1State) {s8}).toReal / 2 =
        ((μ : Measure Figure17_1State) {s6}).toReal := by
    simpa [hs5] using hs6r
  have hsumr' :
      ((μ : Measure Figure17_1State) {s2}).toReal +
          ((μ : Measure Figure17_1State) {s6}).toReal +
          ((μ : Measure Figure17_1State) {s7}).toReal +
          ((μ : Measure Figure17_1State) {s8}).toReal = 1 := by
    have huniv : (Finset.univ : Finset Figure17_1State) = {s1, s2, s3, s4, s5, s6, s7, s8} := by
      ext x
      fin_cases x <;> simp
    rw [huniv] at hsumr
    simpa [hs1, hs3, hs4, hs5, add_assoc, add_left_comm, add_comm] using hsumr
  have hs6target_ne_top :
      (1 - (μ : Measure Figure17_1State) {s2}) * ((4 : ℝ≥0∞) / 17) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.sub_ne_top (by simp))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs7target_ne_top :
      (1 - (μ : Measure Figure17_1State) {s2}) * ((5 : ℝ≥0∞) / 17) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.sub_ne_top (by simp))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs8target_ne_top :
      (1 - (μ : Measure Figure17_1State) {s2}) * ((8 : ℝ≥0∞) / 17) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.sub_ne_top (by simp))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hs6real :
      ((μ : Measure Figure17_1State) {s6}).toReal =
        (((1 - (μ : Measure Figure17_1State) {s2}) * ((4 : ℝ≥0∞) / 17)).toReal) := by
    -- Solve the closed-class balance system together with total mass `1`.
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_sub_of_le
        (by
          calc
            (μ : Measure Figure17_1State) {s2} ≤ (μ : Measure Figure17_1State) Set.univ := by
              exact measure_mono (by simp)
            _ = 1 := by simp)
        (by simp)]
    norm_num
    linarith [hs6r', hs7r, hsumr']
  have hs7real :
      ((μ : Measure Figure17_1State) {s7}).toReal =
        (((1 - (μ : Measure Figure17_1State) {s2}) * ((5 : ℝ≥0∞) / 17)).toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_sub_of_le
        (by
          calc
            (μ : Measure Figure17_1State) {s2} ≤ (μ : Measure Figure17_1State) Set.univ := by
              exact measure_mono (by simp)
            _ = 1 := by simp)
        (by simp)]
    norm_num
    linarith [hs6r', hs7r, hsumr']
  have hs8real :
      ((μ : Measure Figure17_1State) {s8}).toReal =
        (((1 - (μ : Measure Figure17_1State) {s2}) * ((8 : ℝ≥0∞) / 17)).toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_sub_of_le
        (by
          calc
            (μ : Measure Figure17_1State) {s2} ≤ (μ : Measure Figure17_1State) Set.univ := by
              exact measure_mono (by simp)
            _ = 1 := by simp)
        (by simp)]
    norm_num
    linarith [hs6r', hs7r, hsumr']
  have hs6eq :
      (μ : Measure Figure17_1State) {s6} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((4 : ℝ≥0∞) / 17) := by
    exact (ENNReal.toReal_eq_toReal_iff' (hfin s6).ne hs6target_ne_top).1 hs6real
  have hs7eq :
      (μ : Measure Figure17_1State) {s7} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((5 : ℝ≥0∞) / 17) := by
    exact (ENNReal.toReal_eq_toReal_iff' (hfin s7).ne hs7target_ne_top).1 hs7real
  have hs8eq :
      (μ : Measure Figure17_1State) {s8} =
        (1 - (μ : Measure Figure17_1State) {s2}) * ((8 : ℝ≥0∞) / 17) := by
    exact (ENNReal.toReal_eq_toReal_iff' (hfin s8).ne hs8target_ne_top).1 hs8real
  exact ⟨hs6eq, hs7eq, hs8eq⟩

-- Proof sketch: the only closed communicating classes of Fig. 17.1 are the absorbing singleton
-- `{s2}` and the irreducible class `{s6, s7, s8}`. Every invariant distribution is therefore a
-- convex combination of the Dirac mass at `s2` and the unique stationary distribution on
-- `{s6, s7, s8}`, whose weights are `4 / 17`, `5 / 17`, and `8 / 17`.
/-- Exercise 17.6.1 (1): the invariant distributions of Fig. 17.1 are exactly the convex
combinations of the absorbing law at `s2` and the stationary law on `{s6, s7, s8}` with weights
`4 / 17`, `5 / 17`, and `8 / 17`. -/
theorem figure17_1_invariantDistributions_eq_range :
    invariantDistributions (discreteMatrixKernel figure17_1TransitionMatrix) =
      Set.range figure17_1InvariantDistribution :=
  by
    ext μ
    constructor
    · intro hμ
      let t : Set.Icc (0 : ℝ≥0∞) 1 :=
        ⟨(μ : Measure Figure17_1State) {s2}, by
          constructor
          · simp
          · calc
              (μ : Measure Figure17_1State) {s2} ≤ (μ : Measure Figure17_1State) Set.univ := by
                exact measure_mono (by simp)
              _ = 1 := by simp⟩
      have hμinv :
          Kernel.Invariant (discreteMatrixKernel figure17_1TransitionMatrix)
            (μ : Measure Figure17_1State) :=
        (mem_invariantDistributions_iff _ _).1 hμ
      rcases figure17_1_invariantMass_transientStates_eq_zero μ hμinv with
        ⟨hs1, hs3, hs4, hs5⟩
      rcases figure17_1_invariantMass_closedClass_formula μ hμinv with
        ⟨hs6, hs7, hs8⟩
      refine ⟨t, ?_⟩
      apply ProbabilityMeasure.toMeasure_injective
      refine Measure.ext_of_singleton fun x ↦ ?_
      -- The invariant law is determined by its singleton masses on the finite discrete state space.
      fin_cases x
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs1]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, t]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs3]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs4]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs5]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs6, t]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs7, t]
      · rw [figure17_1InvariantDistribution_apply_singleton]
        simp [figure17_1InvariantWeights, hs8, t]
    · rintro ⟨t, rfl⟩
      -- The explicit family already satisfies the singleton balance equations, hence is invariant.
      exact (mem_invariantDistributions_iff _ _).2
        (figure17_1InvariantDistribution_isInvariant t)

/- Exercise 17.6.1 (2)-(5) are source-facing reuse points for the owner file of Remark 17.31.
This item keeps the locally proved invariant-distribution statement and leaves those owner-owned
facts to their canonical file. -/

end ProbabilityTheory.DiscreteMarkovChain

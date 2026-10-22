/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_1

-- Chapter 2 already provides the source-facing shifted Fibonacci owner and the canonical
-- interval data, and records the underdetermined Fibonacci clause as a recall-only block
-- against that existing chapter owner.

noncomputable section

open Set

/-- The objective function `t ↦ Real.exp (-t) + Real.exp t` from the line-search exercise. -/
def chapter02Exercise23Objective (t : ℝ) : ℝ :=
  Real.exp (-t) + Real.exp t

/-- The derivative `t ↦ Real.exp t - Real.exp (-t)` of `chapter02Exercise23Objective`. -/
def chapter02Exercise23ObjectiveDeriv (t : ℝ) : ℝ :=
  Real.exp t - Real.exp (-t)

/-- The left `0.618`-method trial point on `[-1, 1]`. -/
def chapter02Exercise23LeftTrialPoint : ℝ :=
  2 - Real.sqrt 5

/-- The right `0.618`-method trial point on `[-1, 1]`. -/
def chapter02Exercise23RightTrialPoint : ℝ :=
  Real.sqrt 5 - 2

/-- The left admissible retained interval after the first `0.618` step on `[-1, 1]`. -/
def chapter02Exercise23LeftRetainedInterval : Set ℝ :=
  Icc (-1 : ℝ) chapter02Exercise23RightTrialPoint

/-- The right admissible retained interval after the first `0.618` step on `[-1, 1]`. -/
def chapter02Exercise23RightRetainedInterval : Set ℝ :=
  Icc chapter02Exercise23LeftTrialPoint (1 : ℝ)

/-- Chapter02 Exercise 2.3 (1): under the explicit tie convention that equal `φ`-values allow
either candidate subinterval to be kept, a retained interval after the first `0.618` step for
`φ(t) = Real.exp (-t) + Real.exp t` on `[-1, 1]` is exactly one of the two explicit subintervals
determined by the trial points `2 - Real.sqrt 5` and `Real.sqrt 5 - 2`. -/
theorem chapter02Exercise23ZeroPointSixOneEightRetainedInterval_iff (I : Set ℝ) :
    ((chapter02Exercise23Objective chapter02Exercise23LeftTrialPoint ≤
          chapter02Exercise23Objective chapter02Exercise23RightTrialPoint ∧
        I = chapter02Exercise23LeftRetainedInterval) ∨
      (chapter02Exercise23Objective chapter02Exercise23RightTrialPoint ≤
          chapter02Exercise23Objective chapter02Exercise23LeftTrialPoint ∧
        I = chapter02Exercise23RightRetainedInterval)) ↔
      I = chapter02Exercise23LeftRetainedInterval ∨
        I = chapter02Exercise23RightRetainedInterval := by
  constructor
  · rintro (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp
  · rintro (rfl | rfl)
    · left
      refine ⟨?_, rfl⟩
      have htrial :
          chapter02Exercise23LeftTrialPoint = -chapter02Exercise23RightTrialPoint := by
        dsimp [chapter02Exercise23LeftTrialPoint, chapter02Exercise23RightTrialPoint]
        rw [neg_sub]
      rw [htrial]
      simp [chapter02Exercise23Objective, add_comm]
    · right
      refine ⟨?_, rfl⟩
      have htrial :
          chapter02Exercise23LeftTrialPoint = -chapter02Exercise23RightTrialPoint := by
        dsimp [chapter02Exercise23LeftTrialPoint, chapter02Exercise23RightTrialPoint]
        rw [neg_sub]
      rw [htrial]
      simp [chapter02Exercise23Objective, add_comm]

/-- The `0.618`-method trial points are negatives of one another. -/
theorem chapter02Exercise23LeftTrialPoint_eq_neg_rightTrialPoint :
    chapter02Exercise23LeftTrialPoint = -chapter02Exercise23RightTrialPoint := by
  dsimp [chapter02Exercise23LeftTrialPoint, chapter02Exercise23RightTrialPoint]
  rw [neg_sub]

/-- The right `0.618`-method trial point lies in the nonnegative ray. -/
theorem chapter02Exercise23RightTrialPoint_nonneg :
    0 ≤ chapter02Exercise23RightTrialPoint := by
  dsimp [chapter02Exercise23RightTrialPoint]
  refine sub_nonneg.mpr ?_
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- The right `0.618`-method trial point lies to the left of `1`. -/
theorem chapter02Exercise23RightTrialPoint_le_one :
    chapter02Exercise23RightTrialPoint ≤ 1 := by
  dsimp [chapter02Exercise23RightTrialPoint]
  have hs : Real.sqrt 5 ≤ (3 : ℝ) := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hs' : Real.sqrt 5 - 2 ≤ (1 : ℝ) := by
    linarith
  exact hs'

/-- The left `0.618`-method trial point lies to the right of `-1`. -/
theorem chapter02Exercise23NegOne_le_leftTrialPoint :
    (-1 : ℝ) ≤ chapter02Exercise23LeftTrialPoint := by
  rw [chapter02Exercise23LeftTrialPoint_eq_neg_rightTrialPoint]
  simpa using neg_le_neg chapter02Exercise23RightTrialPoint_le_one

/-- The left `0.618`-method trial point lies in the nonpositive ray. -/
theorem chapter02Exercise23LeftTrialPoint_nonpos :
    chapter02Exercise23LeftTrialPoint ≤ 0 := by
  rw [chapter02Exercise23LeftTrialPoint_eq_neg_rightTrialPoint]
  exact neg_nonpos.mpr chapter02Exercise23RightTrialPoint_nonneg

/-- The first `0.618` comparison points on `[-1, 1]` give equal objective values for
`chapter02Exercise23Objective`. -/
theorem chapter02Exercise23ZeroPointSixOneEightTrialValues_eq :
    chapter02Exercise23Objective chapter02Exercise23LeftTrialPoint =
      chapter02Exercise23Objective chapter02Exercise23RightTrialPoint := by
  rw [chapter02Exercise23LeftTrialPoint_eq_neg_rightTrialPoint]
  simp [chapter02Exercise23Objective, add_comm]

/-- `0` belongs to the left retained `0.618` interval. -/
theorem chapter02Exercise23Zero_mem_leftRetainedInterval :
    (0 : ℝ) ∈ chapter02Exercise23LeftRetainedInterval := by
  exact ⟨by norm_num, chapter02Exercise23RightTrialPoint_nonneg⟩

/-- `0` belongs to the right retained `0.618` interval. -/
theorem chapter02Exercise23Zero_mem_rightRetainedInterval :
    (0 : ℝ) ∈ chapter02Exercise23RightRetainedInterval := by
  exact ⟨chapter02Exercise23LeftTrialPoint_nonpos, by norm_num⟩

/-- The left retained `0.618` interval remains inside the initial interval `[-1, 1]`. -/
theorem chapter02Exercise23LeftRetainedInterval_subset_initialInterval :
    chapter02Exercise23LeftRetainedInterval ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  exact ⟨hx.1, le_trans hx.2 chapter02Exercise23RightTrialPoint_le_one⟩

/-- The right retained `0.618` interval remains inside the initial interval `[-1, 1]`. -/
theorem chapter02Exercise23RightRetainedInterval_subset_initialInterval :
    chapter02Exercise23RightRetainedInterval ⊆ Icc (-1 : ℝ) 1 := by
  intro x hx
  exact ⟨le_trans chapter02Exercise23NegOne_le_leftTrialPoint hx.1, hx.2⟩

/-- Helper for Chapter02 Exercise 2.3: the objective is bounded below by `2` on all real inputs.
-/
lemma chapter02Exercise23Objective_two_le (t : ℝ) :
    2 ≤ chapter02Exercise23Objective t := by
  -- Unfold the objective so the standard exponential lower bounds apply directly.
  dsimp [chapter02Exercise23Objective]
  -- Adding the estimates at `t` and `-t` cancels the linear terms and leaves `2`.
  linarith [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]

/-- Helper for Chapter02 Exercise 2.3: the objective takes the value `2` at the origin. -/
lemma chapter02Exercise23Objective_zero_eq_two :
    chapter02Exercise23Objective 0 = 2 := by
  -- Evaluate both exponential terms at `0` to identify the minimum value candidate.
  norm_num [chapter02Exercise23Objective]

/-- `chapter02Exercise23Objective` attains its minimum on the initial interval `[-1, 1]` at `0`.
-/
theorem chapter02Exercise23Objective_isMinOn_initialInterval :
    IsMinOn chapter02Exercise23Objective (Icc (-1 : ℝ) 1) 0 := by
  -- Rewrite `IsMinOn` as the pointwise lower-bound property on the interval.
  refine isMinOn_iff.mpr ?_
  intro x hx
  -- The interval hypothesis is unused because the lower bound holds globally on `ℝ`.
  simpa [chapter02Exercise23Objective_zero_eq_two] using chapter02Exercise23Objective_two_le x

/-- `chapter02Exercise23Objective` attains its minimum on the left retained `0.618` interval at
`0`. -/
theorem chapter02Exercise23Objective_isMinOn_leftRetainedInterval :
    IsMinOn chapter02Exercise23Objective chapter02Exercise23LeftRetainedInterval 0 := by
  exact chapter02Exercise23Objective_isMinOn_initialInterval.on_subset
    chapter02Exercise23LeftRetainedInterval_subset_initialInterval

/-- `chapter02Exercise23Objective` attains its minimum on the right retained `0.618` interval at
`0`. -/
theorem chapter02Exercise23Objective_isMinOn_rightRetainedInterval :
    IsMinOn chapter02Exercise23Objective chapter02Exercise23RightRetainedInterval 0 := by
  exact chapter02Exercise23Objective_isMinOn_initialInterval.on_subset
    chapter02Exercise23RightRetainedInterval_subset_initialInterval

/- Chapter02 Exercise 2.3 (2): the Fibonacci method on `[-1, 1]` requires a prescribed stage
budget or final interval tolerance, and the source exercise does not specify either quantity.
This clause is therefore recorded as a recall-only block around the chapter's source-facing
Fibonacci owner `fibonacciSequence`, and the intended minimizer surface remains
`IsMinOn chapter02Exercise23Objective (Icc (-1 : ℝ) 1) 0`.
-/
#check fibonacciSequence
#check fibonacciSequence_recurrence
#check IsMinOn chapter02Exercise23Objective (Icc (-1 : ℝ) 1) 0

/-- Chapter02 Exercise 2.3 (3): for a starting point `t0` and Armijo parameters `β`, `ρ`, `τ`,
the Chapter 2 Armijo owner specializes to the one-dimensional sufficient-decrease inequality for
`chapter02Exercise23Objective` at the geometric trial point `t0 + (β ^ m) * τ`. -/
theorem chapter02Exercise23ArmijoAcceptsAtExponent_iff
    {t0 β ρ τ : ℝ} {m : ℕ} :
    armijoAcceptsAtExponent chapter02Exercise23Objective t0 (1 : ℝ)
        (chapter02Exercise23ObjectiveDeriv t0) β ρ τ m ↔
      chapter02Exercise23Objective t0 -
        chapter02Exercise23Objective (t0 + (β ^ m) * τ) ≥
          -(ρ * (β ^ m) * τ * chapter02Exercise23ObjectiveDeriv t0) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (armijoAcceptsAtExponent_iff :
      armijoAcceptsAtExponent chapter02Exercise23Objective t0 (1 : ℝ)
          (chapter02Exercise23ObjectiveDeriv t0) β ρ τ m ↔
        chapter02Exercise23Objective t0 -
          chapter02Exercise23Objective (t0 + ((β ^ m) * τ) • (1 : ℝ)) ≥
            -(ρ * (β ^ m) * τ * inner ℝ (chapter02Exercise23ObjectiveDeriv t0) (1 : ℝ)))

/-- The canonical least-index Armijo owner for `chapter02Exercise23Objective` is equivalent to
the parameter bounds together with the least accepted exponent for the one-dimensional
sufficient-decrease inequality from `chapter02Exercise23ArmijoAcceptsAtExponent_iff`. -/
theorem chapter02Exercise23IsArmijoIndex_iff_isLeastAcceptedExponent
    {t0 β ρ τ : ℝ} {mk : ℕ} :
    IsArmijoIndex chapter02Exercise23Objective t0 (1 : ℝ)
      (chapter02Exercise23ObjectiveDeriv t0) β ρ τ mk ↔
      ArmijoParameters β ρ τ ∧
        IsLeast
          {m : ℕ |
            chapter02Exercise23Objective t0 -
              chapter02Exercise23Objective (t0 + (β ^ m) * τ) ≥
                -(ρ * (β ^ m) * τ * chapter02Exercise23ObjectiveDeriv t0)} mk := by
  rw [isArmijoIndex_iff_isLeastAcceptedExponent]
  simp [chapter02Exercise23ArmijoAcceptsAtExponent_iff]

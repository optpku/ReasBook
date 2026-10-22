/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_3_extra_1
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter

noncomputable section

section Chapter10Exercise103

-- Source-facing layer: the concrete `ℝ²` objective, nonnegativity constraints, logarithmic
-- barrier, and explicit initial point and minimizers from Exercise 10.3.
-- Core/canonical layer: `InteriorPointPenaltyProblem` for the barrier problem data and `IsMinOn`
-- for minimizer statements. This file therefore keeps only the primitive exercise data local and
-- derives the feasible-set and barrier-subproblem surfaces from that chapter owner.

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The objective in this exercise is `x ↦ x 0 - x 1 + (x 1)^2`. -/
def chapter10Exercise103Objective (x : Point) : ℝ :=
  x 0 - x 1 + (x 1) ^ (2 : ℕ)

/-- The two inequality constraints are the coordinate functions `x 0` and `x 1`. -/
def chapter10Exercise103Constraint (i : Fin 2) (x : Point) : ℝ :=
  x i

/-- The logarithmic barrier attached to the nonnegativity constraints is `c ↦ log (1 / c)`. -/
def chapter10Exercise103Barrier (c : ℝ) : ℝ :=
  Real.log (1 / c)

/-- The source initial point is `(1, 1)ᵀ`. -/
def chapter10Exercise103InitialPoint : Point :=
  EuclideanSpace.single 0 (1 : ℝ) +
    EuclideanSpace.single 1 (1 : ℝ)

/-- The log barrier `c ↦ log (1 / c)` diverges to `+∞` as `c → 0+`. -/
theorem chapter10Exercise103_logBarrier_large_near_zero :
    ∀ R : ℝ, ∃ δ > 0, ∀ ⦃c : ℝ⦄, 0 < c → c < δ → R < chapter10Exercise103Barrier c := by
  intro R
  refine ⟨Real.exp (-R), Real.exp_pos _, ?_⟩
  intro c hc hcδ
  -- Compare `1 / c` with `exp R`, then transfer the estimate through `log`.
  have hInv : Real.exp R < 1 / c := by
    simpa [Real.exp_neg] using (one_div_lt_one_div_of_lt hc hcδ)
  rw [chapter10Exercise103Barrier]
  exact (Real.lt_log_iff_exp_lt (one_div_pos.mpr hc)).2 hInv

/-- The log barrier `c ↦ log (1 / c)` is antitone on the positive half-line. -/
theorem chapter10Exercise103_logBarrier_antitone :
    ∀ ⦃c₁ c₂ : ℝ⦄, 0 < c₁ → c₁ < c₂ →
      chapter10Exercise103Barrier c₂ ≤ chapter10Exercise103Barrier c₁ := by
  intro c₁ c₂ hc₁ hc₁₂
  have hc₂ : 0 < c₂ := lt_trans hc₁ hc₁₂
  -- The reciprocal reverses the order, and `log` is monotone on positive reals.
  rw [chapter10Exercise103Barrier]
  exact Real.log_le_log (one_div_pos.mpr hc₂) (one_div_le_one_div_of_le hc₁ hc₁₂.le)

/-- Exercise 10.3 as a chapter-level `InteriorPointPenaltyProblem` with the objective
`x 0 - x 1 + (x 1)^2`, the two nonnegativity constraints, and the logarithmic barrier
`c ↦ log (1 / c)`. -/
def chapter10Exercise103Problem : InteriorPointPenaltyProblem Point (Fin 2) where
  objective := chapter10Exercise103Objective
  constraint := chapter10Exercise103Constraint
  strictFeasibleSet_nonempty := by
    refine ⟨chapter10Exercise103InitialPoint, ?_⟩
    simp [chapter10Exercise103InitialPoint, chapter10Exercise103Constraint]
  barrier := chapter10Exercise103Barrier
  barrier_large_near_zero := chapter10Exercise103_logBarrier_large_near_zero
  barrier_antitone := chapter10Exercise103_logBarrier_antitone

/-- Evaluating `chapter10Exercise103Problem.penaltyFunction σ x` gives the source log-barrier
objective
`x 0 - x 1 + (x 1)^2 + (1 / σ) * (log (1 / x 0) + log (1 / x 1))`. -/
theorem chapter10Exercise103_penaltyFunction_apply (σ : ℝ) (x : Point) :
    chapter10Exercise103Problem.penaltyFunction σ x =
      chapter10Exercise103Objective x +
        (1 / σ) *
          (chapter10Exercise103Barrier (chapter10Exercise103Constraint 0 x) +
            chapter10Exercise103Barrier (chapter10Exercise103Constraint 1 x)) := by
  simpa [chapter10Exercise103Problem, Fin.sum_univ_two] using
    InteriorPointPenaltyProblem.penaltyFunction_apply chapter10Exercise103Problem σ x

/-- Feasibility for `chapter10Exercise103Problem.feasibleSet` is exactly `x 0 ≥ 0` and
`x 1 ≥ 0`. -/
theorem chapter10Exercise103_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter10Exercise103Problem.feasibleSet ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  simp [chapter10Exercise103Problem, InteriorPointPenaltyProblem.feasibleSet,
    chapter10Exercise103Constraint]

/-- Strict feasibility for `chapter10Exercise103Problem.strictFeasibleSet` is exactly `x 0 > 0`
and `x 1 > 0`. -/
theorem chapter10Exercise103_mem_strictFeasibleSet_iff (x : Point) :
    x ∈ chapter10Exercise103Problem.strictFeasibleSet ↔ 0 < x 0 ∧ 0 < x 1 := by
  simp [chapter10Exercise103Problem, InteriorPointPenaltyProblem.strictFeasibleSet,
    chapter10Exercise103Constraint]

/-- The source initial point `(1, 1)ᵀ` belongs to the strict feasible set. -/
theorem chapter10Exercise103_initialPoint_mem_strictFeasibleSet :
    chapter10Exercise103InitialPoint ∈ chapter10Exercise103Problem.strictFeasibleSet := by
  rw [chapter10Exercise103_mem_strictFeasibleSet_iff]
  simp [chapter10Exercise103InitialPoint]

/-- For barrier parameter `σ`, the log-barrier subproblem has the explicit minimizer
`(1 / σ, (1 + √(1 + 8 / σ)) / 4)`. -/
def chapter10Exercise103BarrierMinimizer (σ : ℝ) : Point :=
  EuclideanSpace.single 0 (1 / σ) +
    EuclideanSpace.single 1 ((1 + Real.sqrt (1 + 8 / σ)) / 4)

/-- The constrained optimizer is `(0, 1 / 2)ᵀ`. -/
def chapter10Exercise103Optimizer : Point :=
  EuclideanSpace.single 1 ((1 : ℝ) / 2)

/-- Helper for Chapter10 Exercise 10.3: the explicit second-coordinate candidate is positive and
satisfies the quadratic stationarity identity `2 y^2 - y = 1 / σ`. -/
lemma chapter10Exercise103_second_coordinate_quadratic {σ : ℝ} (hσ : 0 < σ) :
    let y : ℝ := (1 + Real.sqrt (1 + 8 / σ)) / 4
    0 < y ∧ 2 * y ^ (2 : ℕ) - y = 1 / σ := by
  let y : ℝ := (1 + Real.sqrt (1 + 8 / σ)) / 4
  have hy_def : y = (1 + Real.sqrt (1 + 8 / σ)) / 4 := rfl
  have hy_pos : 0 < y := by
    -- The explicit formula has positive numerator and denominator.
    rw [hy_def]
    positivity
  refine ⟨hy_pos, ?_⟩
  let s : ℝ := Real.sqrt (1 + 8 / σ)
  have hs : s ^ (2 : ℕ) = 1 + 8 / σ := by
    -- Replace `s^2` by the radicand.
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  -- Expand the quadratic expression and then collapse the square root term.
  calc
    2 * y ^ (2 : ℕ) - y = (s ^ (2 : ℕ) - 1) / 8 := by
      rw [hy_def, show Real.sqrt (1 + 8 / σ) = s by rfl]
      ring
    _ = ((1 + 8 / σ) - 1) / 8 := by rw [hs]
    _ = 1 / σ := by
      field_simp [hσ.ne']
      ring

/-- Helper for Chapter10 Exercise 10.3: the first-coordinate scalar term of the log-barrier
objective is minimized at `t = 1 / σ`. -/
lemma chapter10Exercise103_first_coordinate_term_minimized
    {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    (1 / σ) + (1 / σ) * Real.log σ ≤ t + (1 / σ) * Real.log (1 / t) := by
  have hcore : 0 ≤ σ * t - 1 - Real.log (σ * t) := by
    -- Use the standard inequality `log u ≤ u - 1` at `u = σ t`.
    linarith [Real.log_le_sub_one_of_pos (mul_pos hσ ht)]
  have hscaled : 0 ≤ t - 1 / σ - (1 / σ) * Real.log (σ * t) := by
    -- Divide the nonnegative gap by the positive parameter `σ`.
    have hcore' : 0 ≤ (σ * t - 1 - Real.log (σ * t)) / σ := by
      exact div_nonneg hcore hσ.le
    convert hcore' using 1
    field_simp [hσ.ne']
  have hlog_mul : Real.log (σ * t) = Real.log σ + Real.log t := by
    rw [Real.log_mul (ne_of_gt hσ) (ne_of_gt ht)]
  have hbound : (1 / σ) + (1 / σ) * Real.log σ ≤ t - (1 / σ) * Real.log t := by
    -- Rewrite the logarithm of the product and rearrange.
    rw [hlog_mul] at hscaled
    linarith
  have hlog_inv : Real.log (1 / t) = -Real.log t := by
    simp [one_div]
  rw [hlog_inv]
  simpa [sub_eq_add_neg] using hbound

/-- Helper for Chapter10 Exercise 10.3: the second-coordinate scalar term of the log-barrier
objective is minimized at `y = (1 + √(1 + 8 / σ)) / 4`. -/
lemma chapter10Exercise103_second_coordinate_term_minimized
    {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    let y : ℝ := (1 + Real.sqrt (1 + 8 / σ)) / 4
    y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y) ≤
      t ^ (2 : ℕ) - t + (1 / σ) * Real.log (1 / t) := by
  let y : ℝ := (1 + Real.sqrt (1 + 8 / σ)) / 4
  have hy_data : 0 < y ∧ 2 * y ^ (2 : ℕ) - y = 1 / σ := by
    simpa [y] using (chapter10Exercise103_second_coordinate_quadratic hσ)
  rcases hy_data with ⟨hy_pos, hquad⟩
  let u : ℝ := t / y
  have hu_pos : 0 < u := by
    -- The comparison variable `u = t / y` stays positive on the strict feasible set.
    dsimp [u]
    exact div_pos ht hy_pos
  have hcore : 0 ≤ u - 1 - Real.log u := by
    -- Apply the same scalar log inequality to `u`.
    linarith [Real.log_le_sub_one_of_pos hu_pos]
  have hscaled : 0 ≤ (1 / σ) * (u - 1 - Real.log u) := by
    exact mul_nonneg (by positivity) hcore
  have hsquare : 0 ≤ (t - y) ^ (2 : ℕ) := sq_nonneg (t - y)
  have hidentity :
      t ^ (2 : ℕ) - t + (1 / σ) * Real.log (1 / t) -
        (y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y)) =
      (t - y) ^ (2 : ℕ) + (1 / σ) * (u - 1 - Real.log u) := by
    have hlog_inv_t : Real.log (1 / t) = -Real.log t := by
      simp [one_div]
    have hlog_inv_y : Real.log (1 / y) = -Real.log y := by
      simp [one_div]
    have hlog_div : Real.log u = Real.log t - Real.log y := by
      rw [show u = t / y by rfl, Real.log_div (ne_of_gt ht) (ne_of_gt hy_pos)]
    -- Rewrite the gap as a square plus a scalar log gap.
    rw [hlog_inv_t, hlog_inv_y, hlog_div, show u = t / y by rfl, hquad.symm]
    field_simp [hy_pos.ne']
    ring
  have hgap_nonneg :
      0 ≤
        t ^ (2 : ℕ) - t + (1 / σ) * Real.log (1 / t) -
          (y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y)) := by
    rw [hidentity]
    exact add_nonneg hsquare hscaled
  have hbound :
      y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y) ≤
        t ^ (2 : ℕ) - t + (1 / σ) * Real.log (1 / t) := by
    linarith
  simpa [y] using hbound

/-- Helper for Chapter10 Exercise 10.3: the explicit barrier minimizer lies in the strict
feasible set for every positive barrier parameter. -/
lemma chapter10Exercise103_barrierMinimizer_mem_strictFeasibleSet
    {σ : ℝ} (hσ : 0 < σ) :
    chapter10Exercise103BarrierMinimizer σ ∈ chapter10Exercise103Problem.strictFeasibleSet := by
  have hy_data :
      0 < ((1 + Real.sqrt (1 + 8 / σ)) / 4 : ℝ) ∧
        2 * (((1 + Real.sqrt (1 + 8 / σ)) / 4 : ℝ) ^ (2 : ℕ)) -
          ((1 + Real.sqrt (1 + 8 / σ)) / 4 : ℝ) = 1 / σ := by
    simpa using (chapter10Exercise103_second_coordinate_quadratic hσ)
  rcases hy_data with ⟨hy_pos, -⟩
  -- Both coordinates of the explicit point are positive.
  rw [chapter10Exercise103_mem_strictFeasibleSet_iff]
  constructor
  · simpa [chapter10Exercise103BarrierMinimizer] using (one_div_pos.mpr hσ)
  · simpa [chapter10Exercise103BarrierMinimizer] using hy_pos

/-- Helper for Chapter10 Exercise 10.3: the explicit barrier minimizer is the constrained
optimizer plus a horizontal `1 / σ` shift and a vertical barrier shift. -/
lemma chapter10Exercise103_barrierMinimizer_eq_optimizer_add_shifts (σ : ℝ) :
    chapter10Exercise103BarrierMinimizer σ =
      chapter10Exercise103Optimizer +
        (1 / σ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
        (((Real.sqrt (1 + 8 / σ) - 1) / 4 : ℝ)) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
  -- Compare the explicit points coordinatewise.
  ext i
  fin_cases i <;>
    simp [chapter10Exercise103BarrierMinimizer, chapter10Exercise103Optimizer, add_assoc, add_comm]
  ring

/-- Chapter10 Exercise 10.3: for every positive barrier parameter `σ`, the logarithmic barrier
subproblem for minimizing `x 0 - x 1 + (x 1)^2` under `x 0 ≥ 0` and `x 1 ≥ 0` is minimized on
the strict feasible region at
`chapter10Exercise103BarrierMinimizer σ = (1 / σ, (1 + √(1 + 8 / σ)) / 4)`. -/
theorem chapter10Exercise103_logBarrier_isMinOn
    (σ : ℝ) (hσ : 0 < σ) :
    IsMinOn
      (chapter10Exercise103Problem.penaltyFunction σ)
      chapter10Exercise103Problem.strictFeasibleSet
      (chapter10Exercise103BarrierMinimizer σ) := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  rcases (chapter10Exercise103_mem_strictFeasibleSet_iff x).1 hx with ⟨hx0, hx1⟩
  let y : ℝ := (1 + Real.sqrt (1 + 8 / σ)) / 4
  have hFirst :
      (1 / σ) + (1 / σ) * Real.log σ ≤ x 0 + (1 / σ) * Real.log (1 / x 0) :=
    chapter10Exercise103_first_coordinate_term_minimized hσ hx0
  have hSecond :
      y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y) ≤
        x 1 ^ (2 : ℕ) - x 1 + (1 / σ) * Real.log (1 / x 1) := by
    simpa [y] using (chapter10Exercise103_second_coordinate_term_minimized hσ hx1)
  have hMinEval :
      chapter10Exercise103Problem.penaltyFunction σ (chapter10Exercise103BarrierMinimizer σ) =
        ((1 / σ) + (1 / σ) * Real.log σ) +
          (y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y)) := by
    -- Split the barrier objective at the explicit minimizer into the two scalar pieces.
    simp [chapter10Exercise103_penaltyFunction_apply, chapter10Exercise103Objective,
      chapter10Exercise103BarrierMinimizer, chapter10Exercise103Barrier,
      chapter10Exercise103Constraint, y]
    ring
  have hXEval :
      chapter10Exercise103Problem.penaltyFunction σ x =
        (x 0 + (1 / σ) * Real.log (1 / x 0)) +
          (x 1 ^ (2 : ℕ) - x 1 + (1 / σ) * Real.log (1 / x 1)) := by
    -- On a strict-feasible point, the barrier objective also separates by coordinates.
    simp [chapter10Exercise103_penaltyFunction_apply, chapter10Exercise103Objective,
      chapter10Exercise103Barrier, chapter10Exercise103Constraint]
    ring
  calc
    chapter10Exercise103Problem.penaltyFunction σ (chapter10Exercise103BarrierMinimizer σ)
        = ((1 / σ) + (1 / σ) * Real.log σ) +
            (y ^ (2 : ℕ) - y + (1 / σ) * Real.log (1 / y)) := hMinEval
    _ ≤ (x 0 + (1 / σ) * Real.log (1 / x 0)) +
          (x 1 ^ (2 : ℕ) - x 1 + (1 / σ) * Real.log (1 / x 1)) :=
        add_le_add hFirst hSecond
    _ = chapter10Exercise103Problem.penaltyFunction σ x := hXEval.symm

/-- At `σ = 1`, the explicit barrier minimizer is the source initial point `(1, 1)ᵀ`. -/
theorem chapter10Exercise103_barrierMinimizer_one_eq_initialPoint :
    chapter10Exercise103BarrierMinimizer 1 = chapter10Exercise103InitialPoint := by
  have hsqrt : Real.sqrt 9 = 3 := by
    -- Identify the square root in the explicit second coordinate.
    have hsq : (Real.sqrt 9) ^ (2 : ℕ) = 9 := by
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (9 : ℝ))]
    have hnonneg : 0 ≤ Real.sqrt 9 := Real.sqrt_nonneg 9
    nlinarith
  have hsqrt1 : Real.sqrt (1 + 8 : ℝ) = 3 := by
    norm_num
    exact hsqrt
  -- Compare the two points coordinatewise.
  ext i
  fin_cases i
  · norm_num [chapter10Exercise103BarrierMinimizer, chapter10Exercise103InitialPoint]
  · calc
      chapter10Exercise103BarrierMinimizer 1 1 = ((1 + Real.sqrt (1 + 8 : ℝ)) / 4 : ℝ) := by
        simp [chapter10Exercise103BarrierMinimizer]
      _ = 1 := by
        rw [hsqrt1]
        norm_num
      _ = chapter10Exercise103InitialPoint 1 := by
        simp [chapter10Exercise103InitialPoint]

/-- The original constrained problem is minimized at `(0, 1 / 2)ᵀ`. -/
theorem chapter10Exercise103_isMinOn :
    IsMinOn
      chapter10Exercise103Problem.objective
      chapter10Exercise103Problem.feasibleSet
      chapter10Exercise103Optimizer := by
  rw [isMinOn_iff]
  intro x hx
  rcases (chapter10Exercise103_mem_feasibleSet_iff x).1 hx with ⟨hx0, hx1⟩
  calc
    chapter10Exercise103Problem.objective chapter10Exercise103Optimizer = -((1 : ℝ) / 4) := by
      -- Evaluate the source objective at the explicit optimizer.
      simp [chapter10Exercise103Problem, chapter10Exercise103Objective,
        chapter10Exercise103Optimizer]
      norm_num
    _ ≤ x 0 + (x 1 - (1 : ℝ) / 2) ^ (2 : ℕ) - (1 : ℝ) / 4 := by
      -- The feasible objective is a nonnegative square plus the nonnegative term `x 0`.
      have hxSquare : 0 ≤ (x 1 - (1 : ℝ) / 2) ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    _ = chapter10Exercise103Problem.objective x := by
      -- Complete the square in the second coordinate.
      simp [chapter10Exercise103Problem, chapter10Exercise103Objective]
      ring

/-- The explicit log-barrier minimizers converge to the constrained optimizer as `σ → +∞`. -/
theorem chapter10Exercise103_barrierMinimizer_tendsto :
    Tendsto chapter10Exercise103BarrierMinimizer atTop (nhds chapter10Exercise103Optimizer) :=
  by
  have hInv : Tendsto (fun σ : ℝ ↦ 1 / σ) atTop (nhds 0) := by
    -- The horizontal shift is the usual reciprocal decay.
    simpa [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ ↦ r⁻¹) atTop (nhds 0))
  have hFirstVec :
      Tendsto (fun σ : ℝ ↦ (1 / σ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) atTop
        (nhds ((0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) :=
    hInv.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  have hEightInv : Tendsto (fun σ : ℝ ↦ 8 / σ) atTop (nhds 0) := by
    -- The square-root radicand approaches `1`.
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (hInv.const_mul (8 : ℝ))
  have hInside : Tendsto (fun σ : ℝ ↦ (1 : ℝ) + 8 / σ) atTop (nhds (1 : ℝ)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds (1 : ℝ))).add hEightInv)
  have hSqrt : Tendsto (fun σ : ℝ ↦ Real.sqrt (1 + 8 / σ)) atTop (nhds (Real.sqrt 1)) :=
    Filter.Tendsto.sqrt hInside
  have hSecondScalar :
      Tendsto (fun σ : ℝ ↦ ((Real.sqrt (1 + 8 / σ) - 1) / 4 : ℝ)) atTop (nhds 0) := by
    -- The vertical barrier shift is a continuous transform of the same reciprocal decay.
    have hShift :
        Tendsto (fun σ : ℝ ↦ Real.sqrt (1 + 8 / σ) - 1) atTop (nhds (Real.sqrt 1 - 1)) :=
      hSqrt.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (nhds (1 : ℝ)))
    simpa [Real.sqrt_one, div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      (hShift.const_mul ((1 : ℝ) / 4))
  have hSecondVec :
      Tendsto
        (fun σ : ℝ ↦
          (((Real.sqrt (1 + 8 / σ) - 1) / 4 : ℝ)) •
            EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        atTop
        (nhds ((0 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :=
    hSecondScalar.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  have hShifts :
      Tendsto
        (fun σ : ℝ ↦
          (1 / σ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
            (((Real.sqrt (1 + 8 / σ) - 1) / 4 : ℝ)) •
              EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        atTop
        (nhds
          ((0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
            (0 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) :=
    hFirstVec.add hSecondVec
  have hTotal :
      Tendsto
        (fun σ : ℝ ↦
          chapter10Exercise103Optimizer +
            ((1 / σ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
              (((Real.sqrt (1 + 8 / σ) - 1) / 4 : ℝ)) •
                EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
        atTop
        (nhds
          (chapter10Exercise103Optimizer +
            ((0 : ℝ) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
              (0 : ℝ) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ ↦ chapter10Exercise103Optimizer) atTop
        (nhds chapter10Exercise103Optimizer)).add hShifts
  convert hTotal using 1
  · ext σ i
    fin_cases i <;> simp [chapter10Exercise103_barrierMinimizer_eq_optimizer_add_shifts, add_assoc]
  · simp

#print axioms chapter10Exercise103Problem
#print axioms chapter10Exercise103BarrierMinimizer

end Chapter10Exercise103

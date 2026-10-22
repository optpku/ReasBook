/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_5_1

open Matrix

noncomputable section

section

local notation "Point" => EuclideanSpace ℝ (Fin 3)
local notation "Multiplier" => EuclideanSpace ℝ (Fin 2)
local notation "Matrix3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "ConstraintMatrix" => Matrix (Fin 2) (Fin 3) ℝ

/-- The canonical bridge from coordinate functions on `Fin 3` to points of `ℝ³`. -/
private abbrev point (x : Fin 3 → ℝ) : Point :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm x

/-- The canonical bridge from coordinate functions on `Fin 2` to multiplier vectors in `ℝ²`. -/
private abbrev multiplierPoint (x : Fin 2 → ℝ) : Multiplier :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm x

/-- The Hessian matrix `I₃` of the displayed quadratic objective. -/
def chapter09Example952Hessian : Matrix3 :=
  1

/-- The inverse Hessian `I₃` used in the dual-method initialization. -/
def chapter09Example952InverseHessian : Matrix3 :=
  1

/-- The linear term `(0, -3, -1)ᵀ` in the displayed objective
`(1 / 2) x 0^2 + (1 / 2) x 1^2 + (1 / 2) x 2^2 - 3 * x 1 - x 2`. -/
def chapter09Example952LinearTerm : Point :=
  point ![(0 : ℝ), -3, -1]

/-- The inequality matrix encoding
`-x 0 - x 1 - x 2 ≥ -1` and `x 2 - x 1 ≥ -1`. -/
def chapter09Example952ConstraintMatrix : ConstraintMatrix :=
  !![(-1 : ℝ), -1, -1; 0, -1, 1]

/-- The right-hand side vector `(-1, -1)ᵀ` of the displayed inequality system. -/
def chapter09Example952ConstraintBound : Multiplier :=
  multiplierPoint ![(-1 : ℝ), -1]

/-- The concrete inequality-constrained quadratic program used below. -/
def chapter09Example952Problem : DualMethodProblem 3 2 where
  G := chapter09Example952Hessian
  hG_symm := by
    simp [chapter09Example952Hessian]
  Ginv := chapter09Example952InverseHessian
  G_mul_Ginv := by
    simp [chapter09Example952Hessian, chapter09Example952InverseHessian]
  Ginv_mul_G := by
    simp [chapter09Example952Hessian, chapter09Example952InverseHessian]
  g := chapter09Example952LinearTerm
  Aeq := 0
  beq := 0
  Aineq := chapter09Example952ConstraintMatrix
  bineq := chapter09Example952ConstraintBound

#print axioms chapter09Example952Problem

/-- Evaluating the inherited quadratic-program objective of `chapter09Example952Problem`
recovers the displayed source objective formula. -/
@[simp] theorem chapter09Example952_objective_apply (x : Point) :
    chapter09Example952Problem.toQuadraticProgram.objective x =
      (1 / 2 : ℝ) * x 0 ^ (2 : ℕ) +
        (1 / 2 : ℝ) * x 1 ^ (2 : ℕ) +
        (1 / 2 : ℝ) * x 2 ^ (2 : ℕ) -
        3 * x 1 - x 2 := by
  rw [QuadraticProgram.objective_eq]
  simp [chapter09Example952Problem, chapter09Example952Hessian, chapter09Example952LinearTerm,
    point, dotProduct, Fin.sum_univ_three]
  ring_nf

/-- Membership in `chapter09Example952Problem.feasibleSet` is exactly the pair of source
inequalities. -/
@[simp] theorem chapter09Example952_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Example952Problem.feasibleSet ↔
      -x 0 - x 1 - x 2 ≥ (-1 : ℝ) ∧ x 2 - x 1 ≥ (-1 : ℝ) := by
  rw [QuadraticProgram.mem_feasibleSet_iff]
  constructor
  · rintro ⟨_, hIneq⟩
    have hRow0 : x 0 + -1 + x 2 ≤ -x 1 := by
      simpa [chapter09Example952Problem, chapter09Example952ConstraintMatrix,
        chapter09Example952ConstraintBound, multiplierPoint, Fin.sum_univ_three,
        Fin.sum_univ_two, vecHead, vecTail] using hIneq 0
    have h0 : (-1 : ℝ) ≤ -x 0 - x 1 - x 2 := by
      linarith
    have h1 : (-1 : ℝ) ≤ x 2 - x 1 := by
      simpa [chapter09Example952Problem, chapter09Example952ConstraintMatrix,
        chapter09Example952ConstraintBound, multiplierPoint, Fin.sum_univ_three,
        Fin.sum_univ_two, vecHead, vecTail] using hIneq 1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨by ext i; exact Fin.elim0 i, ?_⟩
    intro i
    fin_cases i
    · simpa [chapter09Example952Problem, chapter09Example952ConstraintMatrix,
        chapter09Example952ConstraintBound, multiplierPoint, Fin.sum_univ_three,
        Fin.sum_univ_two, vecHead, vecTail] using (by linarith [h0] :
          x 0 + -1 + x 2 ≤ -x 1)
    · simpa [chapter09Example952Problem, chapter09Example952ConstraintMatrix,
        chapter09Example952ConstraintBound, multiplierPoint, Fin.sum_univ_three,
        Fin.sum_univ_two, vecHead, vecTail] using h1

/-- The unconstrained start point `x₁ = -G⁻¹ g = (0, 3, 1)ᵀ`. -/
def chapter09Example952InitialPoint : Point :=
  point ![(0 : ℝ), 3, 1]

/-- The first full-step iterate `x₂ = (-1, 2, 0)ᵀ`. -/
def chapter09Example952FirstIterate : Point :=
  point ![(-1 : ℝ), 2, 0]

/-- The intended second full-step iterate `x₃ = (-1, 3 / 2, 1 / 2)ᵀ`, which is the stated
solution after correcting the sign inconsistency in the displayed source line. -/
def chapter09Example952Solution : Point :=
  point ![(-1 : ℝ), 3 / 2, 1 / 2]

/-- The first dual-method search direction `d₁ = (-1, -1, -1)ᵀ`. -/
def chapter09Example952FirstDirection : Point :=
  point ![(-1 : ℝ), -1, -1]

/-- The second dual-method search direction `d₂ = (0, -1, 1)ᵀ`. -/
def chapter09Example952SecondDirection : Point :=
  point ![(0 : ℝ), -1, 1]

/-- The multiplier vector `barLambda₂ = (1, 0)ᵀ` after the first full step. -/
def chapter09Example952FirstMultiplier : Multiplier :=
  multiplierPoint ![(1 : ℝ), 0]

/-- The first full-step dual search `y₁ = A₁^* a₁ = 0` because the initial active-set inverse
vanishes. -/
def chapter09Example952FirstDualSearch : Multiplier :=
  0

/-- The multiplier vector `barLambda₃ = (1, 1 / 2)ᵀ` corresponding to the final iterate. -/
def chapter09Example952FinalMultiplier : Multiplier :=
  multiplierPoint ![(1 : ℝ), 1 / 2]

/-- The second full-step dual search `y₂ = A₂^* a₂ = 0`, so the source blocking test is in the
nonblocking branch. -/
def chapter09Example952SecondDualSearch : Multiplier :=
  0

/-- The first full-step size `α₁ = 1`. -/
def chapter09Example952FirstStepSize : ℝ :=
  1

/-- The second full-step size `α₂ = 1 / 2`. -/
def chapter09Example952SecondStepSize : ℝ :=
  1 / 2

/-- A full-size active-set inverse for the working set `{0}` after the first full step. -/
def chapter09Example952FirstAStar : ConstraintMatrix :=
  !![(-1 / 3 : ℝ), -1 / 3, -1 / 3; 0, 0, 0]

/-- The projected inverse Hessian `Ĝ₂ = I - (1, 1, 1)ᵀ (1 / 3) (1, 1, 1)` after the first
constraint becomes active. -/
def chapter09Example952FirstHatG : Matrix3 :=
  !![(2 / 3 : ℝ), -1 / 3, -1 / 3;
    -1 / 3, 2 / 3, -1 / 3;
    -1 / 3, -1 / 3, 2 / 3]

/-- A full-size active-set inverse for the working set `{0, 1}` at the final iterate. -/
def chapter09Example952SecondAStar : ConstraintMatrix :=
  !![(-1 / 3 : ℝ), -1 / 3, -1 / 3;
    0, -1 / 2, 1 / 2]

/-- The projected inverse Hessian after both constraints are active at the final iterate. -/
def chapter09Example952SecondHatG : Matrix3 :=
  !![(2 / 3 : ℝ), -1 / 3, -1 / 3;
    -1 / 3, 1 / 6, 1 / 6;
    -1 / 3, 1 / 6, 1 / 6]

/-- The Step-1 stage data for the displayed dual-method run. -/
def chapter09Example952InitialStage : DualMethodState 3 2 where
  x := chapter09Example952InitialPoint
  objectiveValue := -5
  workingSet := ∅
  multiplier := 0
  hatG := 1
  aStar := 0

/-- The Step-2 control state before choosing the first entering constraint. -/
def chapter09Example952InitialControlState : DualMethodControlState 3 2 where
  stage := chapter09Example952InitialStage
  entering := none

/-- The control state after Step 2 chooses the first inequality. -/
def chapter09Example952SelectedFirstConstraintState : DualMethodControlState 3 2 where
  stage := chapter09Example952InitialStage
  entering := some 0

/-- The stage data after the first full step. -/
def chapter09Example952AfterFirstFullStepStage : DualMethodState 3 2 where
  x := chapter09Example952FirstIterate
  objectiveValue := -7 / 2
  workingSet := {0}
  multiplier := chapter09Example952FirstMultiplier
  hatG := chapter09Example952FirstHatG
  aStar := chapter09Example952FirstAStar

/-- The control state returned to Step 2 after the first full step. -/
def chapter09Example952AfterFirstFullStepControlState : DualMethodControlState 3 2 where
  stage := chapter09Example952AfterFirstFullStepStage
  entering := none

/-- The control state after Step 2 chooses the second inequality. -/
def chapter09Example952SelectedSecondConstraintState : DualMethodControlState 3 2 where
  stage := chapter09Example952AfterFirstFullStepStage
  entering := some 1

/-- The stage data after the second full step reaches the stated solution. -/
def chapter09Example952AfterSecondFullStepStage : DualMethodState 3 2 where
  x := chapter09Example952Solution
  objectiveValue := -13 / 4
  workingSet := insert 0 ({1} : Finset (Fin 2))
  multiplier := chapter09Example952FinalMultiplier
  hatG := chapter09Example952SecondHatG
  aStar := chapter09Example952SecondAStar

/-- The control state at the terminal Step-2 check after the second full step. -/
def chapter09Example952AfterSecondFullStepControlState : DualMethodControlState 3 2 where
  stage := chapter09Example952AfterSecondFullStepStage
  entering := none

/-- Helper for Chapter09 Example 9.5.2: the initial Step-2 control state is consistent with
Algorithm 9.5.1. -/
lemma chapter09Example952_initialControlConsistent :
    IsDualMethodConsistentControlState
      chapter09Example952Problem
      chapter09Example952InitialControlState := by
  refine ⟨?_, ?_⟩
  · change IsDualMethodConsistentState chapter09Example952Problem chapter09Example952InitialStage
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- The initial projected inverse Hessian is `G⁻¹ = I`, since the active-set inverse is zero.
      simp [chapter09Example952InitialStage, chapter09Example952Problem,
        chapter09Example952InverseHessian, DualMethodProblem.constraintTranspose]
    · -- The empty active set makes both the support and identity clauses vacuous.
      rw [isDualMethodActiveSetInverse_iff]
      constructor
      · intro i hi
        ext j
        fin_cases i <;> fin_cases j <;> simp [chapter09Example952InitialStage]
      · intro i j hi hj
        exfalso
        simpa [chapter09Example952InitialStage] using hi
    · -- Evaluating the stored objective at `(0, 3, 1)` gives `-5`.
      rw [chapter09Example952_objective_apply]
      simp [chapter09Example952InitialStage, chapter09Example952InitialPoint]
      norm_num
    · -- No constraint lies in the empty working set.
      intro i hi
      simpa [chapter09Example952InitialStage] using hi
    · -- The active-row annihilation condition is vacuous for the empty working set.
      intro entering i hi
      simpa [chapter09Example952InitialStage] using hi
  · -- The zero multiplier is supported on the empty working set.
    rw [dualMethodMultiplierSupported_iff]
    intro i hi
    simpa [chapter09Example952InitialControlState, chapter09Example952InitialStage]

/-- Helper for Chapter09 Example 9.5.2: selecting the first constraint only changes the
remembered entering index, so the initial stage remains consistent. -/
lemma chapter09Example952_selectedFirstConstraintControlConsistent :
    IsDualMethodConsistentControlState
      chapter09Example952Problem
      chapter09Example952SelectedFirstConstraintState := by
  refine ⟨chapter09Example952_initialControlConsistent.stage_consistent, ?_⟩
  -- The multiplier is still zero, so it is supported on `{0}`.
  rw [dualMethodMultiplierSupported_iff]
  intro i hi
  simp [chapter09Example952SelectedFirstConstraintState, chapter09Example952InitialStage]

/-- Helper for Chapter09 Example 9.5.2: the Step-2 control state after the first full step is
consistent with the stored matrices, iterate, and multiplier. -/
lemma chapter09Example952_afterFirstFullStepControlConsistent :
    IsDualMethodConsistentControlState
      chapter09Example952Problem
      chapter09Example952AfterFirstFullStepControlState := by
  refine ⟨?_, ?_⟩
  · change
      IsDualMethodConsistentState
        chapter09Example952Problem
        chapter09Example952AfterFirstFullStepStage
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- The stored `Ĝ₂` is exactly `G⁻¹ (I - Aᵀ A₂^*)`.
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
          chapter09Example952InverseHessian, chapter09Example952FirstHatG,
          chapter09Example952ConstraintMatrix, chapter09Example952FirstAStar,
          DualMethodProblem.constraintTranspose, Matrix.mul_apply, Matrix.one_apply,
          Fin.sum_univ_two, Fin.sum_univ_three]
    · -- The full-size active-set inverse vanishes off `{0}` and is the identity on the active row.
      rw [isDualMethodActiveSetInverse_iff]
      constructor
      · intro i hi
        fin_cases i
        · exfalso
          simpa [chapter09Example952AfterFirstFullStepStage] using hi
        · ext j
          fin_cases j <;>
            norm_num [chapter09Example952AfterFirstFullStepStage, chapter09Example952FirstAStar]
      · intro i j hi hj
        fin_cases i
        · fin_cases j
          · simp [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
              chapter09Example952FirstAStar, chapter09Example952ConstraintMatrix,
              DualMethodProblem.constraintTranspose, Matrix.mul_apply, Fin.sum_univ_three,
              vecHead, vecTail]
            norm_num
          · exfalso
            simpa [chapter09Example952AfterFirstFullStepStage] using hj
        · exfalso
          simpa [chapter09Example952AfterFirstFullStepStage] using hi
    · -- Evaluating the objective at `x₂ = (-1, 2, 0)` gives the stored value `-7 / 2`.
      rw [chapter09Example952_objective_apply]
      simp [chapter09Example952AfterFirstFullStepStage, chapter09Example952FirstIterate]
      norm_num
    · -- The only active constraint after the first full step is the first residual, which is zero.
      intro i hi
      fin_cases i
      · norm_num [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
          DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
          chapter09Example952ConstraintMatrix, chapter09Example952FirstIterate]
      · exfalso
        simpa [chapter09Example952AfterFirstFullStepStage] using hi
    · -- Every direction `Ĝ₂ a_i` is annihilated by the active first row.
      intro entering i hi
      fin_cases i
      · fin_cases entering <;>
          simp [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
            chapter09Example952ConstraintMatrix, chapter09Example952FirstHatG,
            DualMethodProblem.constraint, DualMethodProblem.constraintTranspose,
            Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
            EuclideanSpace.single, Matrix.toEuclideanLin, vecHead, vecTail]
        all_goals norm_num
      · exfalso
        simpa [chapter09Example952AfterFirstFullStepStage] using hi
  · -- The multiplier `(1, 0)` is supported on the singleton working set `{0}`.
    rw [dualMethodMultiplierSupported_iff]
    intro i hi
    fin_cases i
    · simp [chapter09Example952AfterFirstFullStepControlState,
        chapter09Example952AfterFirstFullStepStage] at hi
    · simp [chapter09Example952AfterFirstFullStepControlState,
        chapter09Example952AfterFirstFullStepStage, chapter09Example952FirstMultiplier,
        multiplierPoint]

/-- Helper for Chapter09 Example 9.5.2: selecting the second constraint only changes the
remembered entering index, so the first-full-step stage remains consistent. -/
lemma chapter09Example952_selectedSecondConstraintControlConsistent :
    IsDualMethodConsistentControlState
      chapter09Example952Problem
      chapter09Example952SelectedSecondConstraintState := by
  refine ⟨chapter09Example952_afterFirstFullStepControlConsistent.stage_consistent, ?_⟩
  -- With entering index `1`, the allowed support is the whole set of constraints.
  rw [dualMethodMultiplierSupported_iff]
  intro i hi
  fin_cases i <;>
    simp [chapter09Example952SelectedSecondConstraintState,
      chapter09Example952AfterFirstFullStepStage] at hi

/-- Helper for Chapter09 Example 9.5.2: the terminal Step-2 control state after the second full
step is consistent with the stored final iterate, matrices, and multiplier. -/
lemma chapter09Example952_afterSecondFullStepControlConsistent :
    IsDualMethodConsistentControlState
      chapter09Example952Problem
      chapter09Example952AfterSecondFullStepControlState := by
  refine ⟨?_, ?_⟩
  · change
      IsDualMethodConsistentState
        chapter09Example952Problem
        chapter09Example952AfterSecondFullStepStage
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- The stored final projected inverse Hessian is `G⁻¹ (I - Aᵀ A₃^*)`.
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
          chapter09Example952InverseHessian, chapter09Example952SecondHatG,
          chapter09Example952ConstraintMatrix, chapter09Example952SecondAStar,
          DualMethodProblem.constraintTranspose, Matrix.mul_apply, Matrix.one_apply,
          Fin.sum_univ_two, Fin.sum_univ_three]
    · -- With both inequalities active, `A₃^*` is the full active-set inverse on `{0, 1}`.
      rw [isDualMethodActiveSetInverse_iff]
      constructor
      · intro i hi
        exfalso
        fin_cases i <;> simpa [chapter09Example952AfterSecondFullStepStage] using hi
      · intro i j hi hj
        fin_cases i <;> fin_cases j <;>
          simp [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
            chapter09Example952SecondAStar, chapter09Example952ConstraintMatrix,
            DualMethodProblem.constraintTranspose, Matrix.mul_apply, Fin.sum_univ_three,
            vecHead, vecTail]
        all_goals norm_num
    · -- The stored terminal objective value agrees with the displayed solution value.
      rw [chapter09Example952_objective_apply]
      simp [chapter09Example952AfterSecondFullStepStage, chapter09Example952Solution]
      norm_num
    · -- Both active residuals vanish at the stated solution.
      intro i hi
      fin_cases i
      · norm_num [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
          DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
          chapter09Example952ConstraintMatrix, chapter09Example952Solution]
      · norm_num [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
          DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
          chapter09Example952ConstraintMatrix, chapter09Example952Solution]
    · -- Every direction `Ĝ₃ a_i` is annihilated by both active rows at the terminal stage.
      intro entering i hi
      fin_cases entering <;> fin_cases i <;>
        simp [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
          chapter09Example952ConstraintMatrix, chapter09Example952SecondHatG,
          DualMethodProblem.constraint, DualMethodProblem.constraintTranspose,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          Fin.sum_univ_three, EuclideanSpace.single, Matrix.toEuclideanLin,
          vecHead, vecTail]
      all_goals norm_num
  · -- The final working set is all of `Fin 2`, so the support condition is vacuous.
    rw [dualMethodMultiplierSupported_iff]
    intro i hi
    fin_cases i <;>
      simp [chapter09Example952AfterSecondFullStepControlState,
        chapter09Example952AfterSecondFullStepStage] at hi

/-- Chapter09 Example 9.5.2 (1): Algorithm 9.5.1 initializes the example at
`x₁ = -G⁻¹ g = (0, 3, 1)ᵀ` with empty working set, zero multiplier, `Ĝ₁ = G⁻¹`, and
`A₁^* = 0`. -/
theorem chapter09Example952_initStep :
    DualMethodInitControlStep
      chapter09Example952Problem
      chapter09Example952InitialControlState := by
  refine ⟨chapter09Example952_initialControlConsistent, rfl, ?_⟩
  change DualMethodInitialization chapter09Example952Problem chapter09Example952InitialStage
  refine ⟨chapter09Example952_initialControlConsistent.stage_consistent, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · -- The stored initial point is exactly `-G⁻¹ g`.
    ext i
    fin_cases i <;>
      norm_num [chapter09Example952InitialStage,
        chapter09Example952Problem, chapter09Example952InitialPoint,
        chapter09Example952InverseHessian, chapter09Example952LinearTerm]
  · -- The initialization objective identity evaluates to `-5`.
    simp [chapter09Example952InitialStage, chapter09Example952Problem,
      chapter09Example952InitialPoint, chapter09Example952LinearTerm, point,
      dotProduct, Fin.sum_univ_three, vecHead, vecTail]
    norm_num

/-- Chapter09 Example 9.5.2 (2): at the initial Step-2 state, both residuals are positive and
Algorithm 9.5.1 chooses the first inequality as the entering constraint. -/
theorem chapter09Example952_selectFirstConstraint :
    DualMethodSelectControlStep
      chapter09Example952Problem
      chapter09Example952InitialControlState
      chapter09Example952SelectedFirstConstraintState := by
  refine DualMethodSelectControlStep.mk 0 chapter09Example952_initialControlConsistent
    chapter09Example952_selectedFirstConstraintControlConsistent rfl rfl rfl ?_
  change DualMethodSelectionStep chapter09Example952Problem chapter09Example952InitialStage 0
  refine ⟨chapter09Example952_initialControlConsistent.stage_consistent, ?_, ?_, ?_⟩
  · -- The first residual is maximal among the two initial positive residuals.
    rw [isMostViolatedConstraint_iff]
    intro i
    fin_cases i
    · exact le_rfl
    · norm_num [chapter09Example952InitialStage, chapter09Example952Problem,
        DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
        chapter09Example952ConstraintMatrix, chapter09Example952InitialPoint]
  · -- The chosen first residual is strictly positive.
    norm_num [chapter09Example952InitialStage, chapter09Example952Problem,
      DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
      chapter09Example952ConstraintMatrix, chapter09Example952InitialPoint]
  · -- The stored multiplier is zero in the entering coordinate.
    change (0 : Multiplier) 0 = 0
    rfl

/-- Chapter09 Example 9.5.2 (3): the first full step uses the positive source ratio
`α₁ = r₁ / (a₁ᵀ d₁) = 1`. -/
theorem chapter09Example952_firstFullStep_stepSize :
    chapter09Example952FirstStepSize = 1 := by
  -- The stored first step size is the source value `α₁ = 1`.
  rfl

/-- Chapter09 Example 9.5.2 (4): the first full step updates
`x₂ = x₁ + α₁ • d₁ = (-1, 2, 0)ᵀ`. -/
theorem chapter09Example952_firstFullStep_iterate :
    chapter09Example952AfterFirstFullStepControlState.stage.x =
      chapter09Example952InitialStage.x +
        chapter09Example952FirstStepSize • chapter09Example952FirstDirection := by
  -- Check the affine update `x₂ = x₁ + α₁ d₁` coordinatewise.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952AfterFirstFullStepControlState,
      chapter09Example952AfterFirstFullStepStage, chapter09Example952InitialStage,
      chapter09Example952FirstIterate, chapter09Example952InitialPoint,
      chapter09Example952FirstStepSize, chapter09Example952FirstDirection]

/-- Chapter09 Example 9.5.2 (5): the first full step updates the multiplier to
`barLambda₂ = (1, 0)ᵀ`. -/
theorem chapter09Example952_firstFullStep_multiplier :
    chapter09Example952AfterFirstFullStepControlState.stage.multiplier =
      chapter09Example952FirstMultiplier := by
  -- The stored multiplier after the first full step is definitionally `(1, 0)`.
  rfl

/-- Chapter09 Example 9.5.2 (6): the first full step activates the first inequality, giving
working set `{1}` in source numbering. -/
theorem chapter09Example952_firstFullStep_workingSet :
    chapter09Example952AfterFirstFullStepControlState.stage.workingSet =
      insert 0 chapter09Example952InitialStage.workingSet := by
  -- Both sides name the singleton active set `{0}`.
  ext i
  fin_cases i <;> simp [chapter09Example952AfterFirstFullStepControlState,
    chapter09Example952AfterFirstFullStepStage, chapter09Example952InitialStage]

/-- Chapter09 Example 9.5.2 (7): the first full step starts from the Step-2 choice
`entering = some 0`. -/
theorem chapter09Example952_firstFullStep_entering :
    chapter09Example952SelectedFirstConstraintState.entering = some 0 := by
  -- The remembered entering index is definitionally the first inequality.
  rfl

/-- Chapter09 Example 9.5.2 (8): after the first full step, control returns to Step 2 with no
pending entering constraint. -/
theorem chapter09Example952_firstFullStep_after_entering :
    chapter09Example952AfterFirstFullStepControlState.entering = none := by
  -- After the full step the control state returns to Step 2.
  rfl

/-- Chapter09 Example 9.5.2 (9): the first full-step direction is
`d₁ = Ĝ₁ a₁ = (-1, -1, -1)ᵀ`. -/
theorem chapter09Example952_firstFullStep_direction :
    chapter09Example952FirstDirection =
      chapter09Example952InitialStage.hatG.mulVec
        (chapter09Example952Problem.constraint 0) := by
  -- The initial projected inverse Hessian is the identity, so the direction is the first
  -- constraint normal itself.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952FirstDirection, chapter09Example952InitialStage,
      chapter09Example952Problem, chapter09Example952ConstraintMatrix, chapter09Example952Hessian,
      DualMethodProblem.constraint, DualMethodProblem.constraintTranspose]

/-- Chapter09 Example 9.5.2 (10): the first full-step dual search is
`y₁ = A₁^* a₁ = 0`. -/
theorem chapter09Example952_firstFullStep_dualSearch :
    chapter09Example952FirstDualSearch =
      chapter09Example952InitialStage.aStar.mulVec
        (chapter09Example952Problem.constraint 0) := by
  -- The initial active-set inverse is zero, so the first dual search vanishes.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952FirstDualSearch, chapter09Example952InitialStage,
      chapter09Example952Problem, chapter09Example952ConstraintMatrix,
      chapter09Example952ConstraintBound, DualMethodProblem.constraint,
      DualMethodProblem.constraintTranspose]

/-- Chapter09 Example 9.5.2 (11): the first full step is in the nonblocking branch because the
working set is empty. -/
theorem chapter09Example952_firstFullStep_noBlocking :
    ¬ HasPositiveWorkingComponent
      chapter09Example952InitialStage.workingSet
      chapter09Example952FirstDualSearch := by
  -- The initial working set is empty, so Step 3 has no blocking index.
  rw [hasPositiveWorkingComponent_iff]
  rintro ⟨i, hi, _⟩
  simp [chapter09Example952InitialStage] at hi

/-- Chapter09 Example 9.5.2 (12): the first full-step size is the source ratio
`α₁ = r₁ / (a₁ᵀ d₁)`. -/
theorem chapter09Example952_firstFullStep_stepSize_ratio :
    chapter09Example952FirstStepSize =
      chapter09Example952Problem.residual chapter09Example952InitialStage.x 0 /
        (chapter09Example952Problem.Aineq.mulVec chapter09Example952FirstDirection) 0 := by
  -- Evaluate the residual and directional derivative explicitly to recover `α₁ = 1`.
  norm_num [chapter09Example952FirstStepSize, chapter09Example952InitialStage,
    chapter09Example952Problem, DualMethodProblem.residual_apply,
    chapter09Example952ConstraintBound, chapter09Example952ConstraintMatrix,
    chapter09Example952InitialPoint, chapter09Example952FirstDirection]

/-- Chapter09 Example 9.5.2 (13): the first full-step objective update matches the
Algorithm 9.5.1 full-step formula. -/
theorem chapter09Example952_firstFullStep_objectiveValue :
    chapter09Example952AfterFirstFullStepControlState.stage.objectiveValue =
      chapter09Example952InitialStage.objectiveValue +
        chapter09Example952FirstStepSize *
          (chapter09Example952Problem.Aineq.mulVec chapter09Example952FirstDirection) 0 *
          ((1 / 2 : ℝ) * chapter09Example952FirstStepSize +
            chapter09Example952InitialStage.multiplier 0) := by
  -- The stored objective value matches the quadratic full-step update formula numerically.
  norm_num [chapter09Example952AfterFirstFullStepControlState,
    chapter09Example952AfterFirstFullStepStage, chapter09Example952InitialStage,
    chapter09Example952FirstStepSize, chapter09Example952Problem,
    chapter09Example952ConstraintMatrix, chapter09Example952FirstDirection]

/-- Chapter09 Example 9.5.2 (14): the first full-step multiplier is obtained from the
standard pivot update formula. -/
theorem chapter09Example952_firstFullStep_multiplierPivot :
    chapter09Example952FirstMultiplier =
      multiplierPivotUpdate
        chapter09Example952InitialStage.multiplier
        chapter09Example952FirstDualSearch
        0
        chapter09Example952FirstStepSize := by
  -- The pivot update adds the new entering component and leaves the zero dual search unchanged.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952FirstMultiplier, multiplierPivotUpdate,
      chapter09Example952InitialStage, chapter09Example952FirstDualSearch,
      chapter09Example952FirstStepSize]

/-- Chapter09 Example 9.5.2 (15): after the first full step, `x₂ = (-1, 2, 0)ᵀ` minimizes
the inherited quadratic-program objective on the affine set obtained by replacing the first
inequality by the equality `r₁(x) = 0`. -/
theorem chapter09Example952_firstIterate_isMinOn_firstConstraintEqualitySet :
    IsMinOn
      chapter09Example952Problem.toQuadraticProgram.objective
      {x | chapter09Example952Problem.residual x 0 = 0}
      chapter09Example952FirstIterate := by
  -- On the first equality-constrained subproblem, the gap reduces to a sum of squares.
  intro x hx
  show chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952FirstIterate ≤
    chapter09Example952Problem.toQuadraticProgram.objective x
  have hx0 : chapter09Example952Problem.residual x 0 = 0 := hx
  have hgap :
      chapter09Example952Problem.toQuadraticProgram.objective x -
        chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952FirstIterate =
        (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 2)^2 + x 2^2) -
          chapter09Example952Problem.residual x 0 := by
    -- Expand the objective and the first residual into explicit coordinates.
    rw [chapter09Example952_objective_apply, chapter09Example952_objective_apply]
    simp [chapter09Example952FirstIterate]
    rw [DualMethodProblem.residual_apply]
    simp [chapter09Example952Problem, chapter09Example952ConstraintBound,
      chapter09Example952ConstraintMatrix, Matrix.vecHead, Matrix.vecTail]
    ring_nf
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 2)^2 + x 2^2) := by
    -- Each square term is nonnegative, so the whole quadratic gap term is nonnegative.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 2), sq_nonneg (x 2)]
  nlinarith [hgap, hx0, hnonneg]

/-- Chapter09 Example 9.5.2 (16): at the next Step-2 state, the first residual is zero, the
second residual is positive, and Algorithm 9.5.1 chooses the second inequality as the entering
constraint. -/
theorem chapter09Example952_selectSecondConstraint :
    DualMethodSelectControlStep
      chapter09Example952Problem
      chapter09Example952AfterFirstFullStepControlState
      chapter09Example952SelectedSecondConstraintState := by
  refine DualMethodSelectControlStep.mk 1 chapter09Example952_afterFirstFullStepControlConsistent
    chapter09Example952_selectedSecondConstraintControlConsistent rfl rfl rfl ?_
  change
    DualMethodSelectionStep
      chapter09Example952Problem
      chapter09Example952AfterFirstFullStepStage
      1
  refine ⟨chapter09Example952_afterFirstFullStepControlConsistent.stage_consistent, ?_, ?_, ?_⟩
  · -- At `x₂`, the second residual is maximal because the first residual is already zero.
    rw [isMostViolatedConstraint_iff]
    intro i
    fin_cases i
    · norm_num [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
        DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
        chapter09Example952ConstraintMatrix, chapter09Example952FirstIterate]
    · exact le_rfl
  · -- The second residual remains strictly positive at the first iterate.
    norm_num [chapter09Example952AfterFirstFullStepStage, chapter09Example952Problem,
      DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
      chapter09Example952ConstraintMatrix, chapter09Example952FirstIterate]
  · -- The first full-step multiplier vanishes in the second coordinate.
    change chapter09Example952FirstMultiplier 1 = 0
    norm_num [chapter09Example952FirstMultiplier, multiplierPoint]

/-- Chapter09 Example 9.5.2 (17): the second full step uses the positive source ratio
`α₂ = 1 / 2`. -/
theorem chapter09Example952_secondFullStep_stepSize :
    chapter09Example952SecondStepSize = 1 / 2 := by
  -- The stored second step size is the source value `α₂ = 1 / 2`.
  rfl

/-- Chapter09 Example 9.5.2 (18): the second full step updates
`x₃ = x₂ + (1 / 2) • d₂ = (-1, 3 / 2, 1 / 2)ᵀ`. -/
theorem chapter09Example952_secondFullStep_iterate :
    chapter09Example952AfterSecondFullStepControlState.stage.x =
      chapter09Example952AfterFirstFullStepStage.x +
        chapter09Example952SecondStepSize • chapter09Example952SecondDirection := by
  -- Check the affine update `x₃ = x₂ + α₂ d₂` coordinatewise.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952AfterSecondFullStepControlState,
      chapter09Example952AfterSecondFullStepStage, chapter09Example952AfterFirstFullStepStage,
      chapter09Example952Solution, chapter09Example952FirstIterate,
      chapter09Example952SecondStepSize, chapter09Example952SecondDirection]

/-- Chapter09 Example 9.5.2 (19): the second full step updates the multiplier to
`barLambda₃ = (1, 1 / 2)ᵀ`. -/
theorem chapter09Example952_secondFullStep_multiplier :
    chapter09Example952AfterSecondFullStepControlState.stage.multiplier =
      chapter09Example952FinalMultiplier := by
  -- The stored multiplier after the second full step is definitionally `(1, 1 / 2)`.
  rfl

/-- Chapter09 Example 9.5.2 (20): the second full step activates the second inequality. -/
theorem chapter09Example952_secondFullStep_workingSet :
    chapter09Example952AfterSecondFullStepControlState.stage.workingSet =
      insert 1 chapter09Example952AfterFirstFullStepStage.workingSet := by
  -- Both sides name the final active set `{0, 1}`.
  ext i
  fin_cases i <;> simp [chapter09Example952AfterSecondFullStepControlState,
    chapter09Example952AfterSecondFullStepStage, chapter09Example952AfterFirstFullStepStage]

/-- Chapter09 Example 9.5.2 (21): the second full step starts from the Step-2 choice
`entering = some 1`. -/
theorem chapter09Example952_secondFullStep_entering :
    chapter09Example952SelectedSecondConstraintState.entering = some 1 := by
  -- The remembered entering index is definitionally the second inequality.
  rfl

/-- Chapter09 Example 9.5.2 (22): after the second full step, control returns to Step 2 with
no pending entering constraint. -/
theorem chapter09Example952_secondFullStep_after_entering :
    chapter09Example952AfterSecondFullStepControlState.entering = none := by
  -- After the full step the control state returns to Step 2.
  rfl

/-- Chapter09 Example 9.5.2 (23): the second full-step direction is
`d₂ = Ĝ₂ a₂ = (0, -1, 1)ᵀ`. -/
theorem chapter09Example952_secondFullStep_direction :
    chapter09Example952SecondDirection =
      chapter09Example952AfterFirstFullStepStage.hatG.mulVec
        (chapter09Example952Problem.constraint 1) := by
  -- Multiply the stored projected inverse Hessian by the second constraint normal and
  -- simplify the resulting coordinates.
  ext i
  fin_cases i <;>
    simp [chapter09Example952SecondDirection, chapter09Example952AfterFirstFullStepStage,
      chapter09Example952FirstHatG, chapter09Example952Problem, chapter09Example952ConstraintMatrix,
      DualMethodProblem.constraint, DualMethodProblem.constraintTranspose, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, EuclideanSpace.single, Matrix.toEuclideanLin]
  all_goals ring_nf

/-- Chapter09 Example 9.5.2 (24): the second full-step dual search is
`y₂ = A₂^* a₂ = 0`. -/
theorem chapter09Example952_secondFullStep_dualSearch :
    chapter09Example952SecondDualSearch =
      chapter09Example952AfterFirstFullStepStage.aStar.mulVec
        (chapter09Example952Problem.constraint 1) := by
  -- The stored active-set inverse sends the second constraint normal to zero in this example.
  ext i
  fin_cases i <;>
    simp [chapter09Example952SecondDualSearch, chapter09Example952AfterFirstFullStepStage,
      chapter09Example952FirstAStar, chapter09Example952Problem, chapter09Example952ConstraintMatrix,
      DualMethodProblem.constraint, DualMethodProblem.constraintTranspose, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, EuclideanSpace.single, Matrix.toEuclideanLin]

/-- Chapter09 Example 9.5.2 (25): the second full step is in the nonblocking branch because
the dual search has no positive working-set component. -/
theorem chapter09Example952_secondFullStep_noBlocking :
    ¬ HasPositiveWorkingComponent
      chapter09Example952AfterFirstFullStepStage.workingSet
      chapter09Example952SecondDualSearch := by
  -- The only active component of the dual search is zero, so the full-step branch is nonblocking.
  rw [hasPositiveWorkingComponent_iff]
  rintro ⟨i, hi, hpos⟩
  fin_cases i
  · simp [chapter09Example952SecondDualSearch] at hpos
  · simp [chapter09Example952AfterFirstFullStepStage] at hi

/-- Chapter09 Example 9.5.2 (26): the second full-step size is the source ratio
`α₂ = r₂ / (a₂ᵀ d₂)`. -/
theorem chapter09Example952_secondFullStep_stepSize_ratio :
    chapter09Example952SecondStepSize =
      chapter09Example952Problem.residual chapter09Example952AfterFirstFullStepStage.x 1 /
        (chapter09Example952Problem.Aineq.mulVec chapter09Example952SecondDirection) 1 := by
  -- Evaluate the residual and directional derivative explicitly to recover `α₂ = 1 / 2`.
  norm_num [chapter09Example952SecondStepSize, chapter09Example952AfterFirstFullStepStage,
    chapter09Example952Problem, DualMethodProblem.residual_apply,
    chapter09Example952ConstraintBound, chapter09Example952ConstraintMatrix,
    chapter09Example952FirstIterate, chapter09Example952SecondDirection]

/-- Chapter09 Example 9.5.2 (27): the second full-step objective update matches the
Algorithm 9.5.1 full-step formula. -/
theorem chapter09Example952_secondFullStep_objectiveValue :
    chapter09Example952AfterSecondFullStepControlState.stage.objectiveValue =
      chapter09Example952AfterFirstFullStepStage.objectiveValue +
        chapter09Example952SecondStepSize *
          (chapter09Example952Problem.Aineq.mulVec chapter09Example952SecondDirection) 1 *
          ((1 / 2 : ℝ) * chapter09Example952SecondStepSize +
            chapter09Example952AfterFirstFullStepStage.multiplier 1) := by
  -- The stored objective value matches the quadratic full-step update formula numerically.
  norm_num [chapter09Example952AfterSecondFullStepControlState,
    chapter09Example952AfterSecondFullStepStage, chapter09Example952AfterFirstFullStepStage,
    chapter09Example952SecondStepSize, chapter09Example952Problem,
    chapter09Example952ConstraintMatrix, chapter09Example952SecondDirection,
    chapter09Example952FirstMultiplier]

/-- Chapter09 Example 9.5.2 (28): the second full-step multiplier is obtained from the
standard pivot update formula. -/
theorem chapter09Example952_secondFullStep_multiplierPivot :
    chapter09Example952FinalMultiplier =
      multiplierPivotUpdate
        chapter09Example952AfterFirstFullStepStage.multiplier
        chapter09Example952SecondDualSearch
        1
        chapter09Example952SecondStepSize := by
  -- The second pivot update adds `1 / 2` in the entering coordinate and leaves the zero
  -- dual search unchanged.
  ext i
  fin_cases i <;>
    norm_num [chapter09Example952FinalMultiplier, multiplierPivotUpdate,
      chapter09Example952AfterFirstFullStepStage, chapter09Example952SecondDualSearch,
      chapter09Example952SecondStepSize, chapter09Example952FirstMultiplier]

/-- Helper for Chapter09 Example 9.5.2: the first residual is the affine form
`-1 + x 0 + x 1 + x 2`. -/
lemma chapter09Example952_residual_zero (x : Point) :
    chapter09Example952Problem.residual x 0 = (-1 : ℝ) + x 0 + x 1 + x 2 := by
  -- Expand the residual definition and simplify the first inequality row.
  rw [DualMethodProblem.residual_apply]
  simp [chapter09Example952Problem, chapter09Example952ConstraintBound,
    chapter09Example952ConstraintMatrix, Matrix.vecHead, Matrix.vecTail]
  ring_nf

/-- Helper for Chapter09 Example 9.5.2: the second residual is the affine form
`-1 + x 1 - x 2`. -/
lemma chapter09Example952_residual_one (x : Point) :
    chapter09Example952Problem.residual x 1 = (-1 : ℝ) + x 1 - x 2 := by
  -- Expand the residual definition and simplify the second inequality row.
  rw [DualMethodProblem.residual_apply]
  simp [chapter09Example952Problem, chapter09Example952ConstraintBound,
    chapter09Example952ConstraintMatrix, Matrix.vecHead, Matrix.vecTail]
  ring_nf

/-- Helper for Chapter09 Example 9.5.2: the stated solution has objective value `-13 / 4`. -/
lemma chapter09Example952_solution_objective :
    chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952Solution =
      (-13 / 4 : ℝ) := by
  -- Evaluate the displayed quadratic objective at the candidate solution.
  rw [chapter09Example952_objective_apply]
  simp [chapter09Example952Solution]
  norm_num

/-- Helper for Chapter09 Example 9.5.2: the objective gap to the stated solution splits into
nonnegative square terms and residual corrections. -/
lemma chapter09Example952_objectiveGapToSolution (x : Point) :
    chapter09Example952Problem.toQuadraticProgram.objective x -
      chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952Solution =
      (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 3 / 2)^2 + (x 2 - 1 / 2)^2) -
        chapter09Example952Problem.residual x 0 -
        (1 / 2 : ℝ) * chapter09Example952Problem.residual x 1 := by
  -- Route correction: after repairing the imported `.toQuadraticProgram.objective` surface,
  -- the closing argument is a direct arithmetic gap identity rather than a heavier algorithmic
  -- consistency proof.
  rw [chapter09Example952_objective_apply, chapter09Example952_objective_apply]
  simp [chapter09Example952Solution]
  rw [chapter09Example952_residual_zero, chapter09Example952_residual_one]
  ring_nf

/-- Chapter09 Example 9.5.2 (29): after the second full step, Algorithm 9.5.1 returns to Step 2
and terminates at `x₃ = (-1, 3 / 2, 1 / 2)ᵀ` because all residuals are nonpositive. -/
theorem chapter09Example952_terminalStop :
    DualMethodStopControlStep
      chapter09Example952Problem
      chapter09Example952AfterSecondFullStepControlState := by
  refine ⟨chapter09Example952_afterSecondFullStepControlConsistent, rfl, ?_⟩
  change DualMethodTerminalStep chapter09Example952Problem chapter09Example952AfterSecondFullStepStage
  refine ⟨chapter09Example952_afterSecondFullStepControlConsistent.stage_consistent, ?_⟩
  -- The terminal Step-2 check succeeds because both residuals are exactly zero at `x₃`.
  rw [DualMethodState.terminated_iff]
  intro i
  fin_cases i
  · norm_num [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
      DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
      chapter09Example952ConstraintMatrix, chapter09Example952Solution]
  · norm_num [chapter09Example952AfterSecondFullStepStage, chapter09Example952Problem,
      DualMethodProblem.residual_apply, chapter09Example952ConstraintBound,
      chapter09Example952ConstraintMatrix, chapter09Example952Solution]

/-- Chapter09 Example 9.5.2 (30): the feasible quadratic program with constraints
`-x 0 - x 1 - x 2 ≥ -1` and `x 2 - x 1 ≥ -1` is minimized at
`(-1, 3 / 2, 1 / 2)ᵀ`. -/
theorem chapter09Example952_isMinOn :
    IsMinOn
      chapter09Example952Problem.toQuadraticProgram.objective
      chapter09Example952Problem.feasibleSet
      chapter09Example952Solution := by
  -- Compare any feasible point to the stated solution through the explicit objective-gap identity.
  intro x hx
  show chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952Solution ≤
    chapter09Example952Problem.toQuadraticProgram.objective x
  have hres := (DualMethodProblem.mem_feasibleSet_iff chapter09Example952Problem x).mp hx
  have hres0 : chapter09Example952Problem.residual x 0 ≤ 0 := hres 0
  have hres1 : chapter09Example952Problem.residual x 1 ≤ 0 := hres 1
  have hnonneg :
      0 ≤
        (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 3 / 2)^2 + (x 2 - 1 / 2)^2) -
          chapter09Example952Problem.residual x 0 -
          (1 / 2 : ℝ) * chapter09Example952Problem.residual x 1 := by
    -- Feasibility makes the residual corrections nonnegative, and the square terms are
    -- obviously nonnegative.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 3 / 2), sq_nonneg (x 2 - 1 / 2),
      hres0, hres1]
  nlinarith [chapter09Example952_objectiveGapToSolution x, hnonneg]

/-- Chapter09 Example 9.5.2 (31): the minimizer `(-1, 3 / 2, 1 / 2)ᵀ` is unique among feasible
points of Example 9.5.2. -/
theorem chapter09Example952_eq_solution_of_mem_feasibleSet_of_objective_le
    (x : Point)
    (hx : x ∈ chapter09Example952Problem.feasibleSet)
    (hobj :
      chapter09Example952Problem.toQuadraticProgram.objective x ≤
        chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952Solution) :
    x = chapter09Example952Solution := by
  -- The gap identity and feasibility force every nonnegative term to vanish.
  have hres := (DualMethodProblem.mem_feasibleSet_iff chapter09Example952Problem x).mp hx
  have hres0 : chapter09Example952Problem.residual x 0 ≤ 0 := hres 0
  have hres1 : chapter09Example952Problem.residual x 1 ≤ 0 := hres 1
  have hnonneg :
      0 ≤
        (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 3 / 2)^2 + (x 2 - 1 / 2)^2) -
          chapter09Example952Problem.residual x 0 -
          (1 / 2 : ℝ) * chapter09Example952Problem.residual x 1 := by
    -- Feasibility makes the residual corrections nonnegative, and the square terms are
    -- obviously nonnegative.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 3 / 2), sq_nonneg (x 2 - 1 / 2),
      hres0, hres1]
  have hle :
      chapter09Example952Problem.toQuadraticProgram.objective x -
        chapter09Example952Problem.toQuadraticProgram.objective chapter09Example952Solution ≤ 0 := by
    -- The assumed objective comparison is exactly the nonpositive gap statement.
    linarith
  have hzero :
      (1 / 2 : ℝ) * ((x 0 + 1)^2 + (x 1 - 3 / 2)^2 + (x 2 - 1 / 2)^2) -
        chapter09Example952Problem.residual x 0 -
        (1 / 2 : ℝ) * chapter09Example952Problem.residual x 1 = 0 := by
    -- The gap is squeezed between `0` and itself.
    nlinarith [chapter09Example952_objectiveGapToSolution x, hnonneg, hle]
  have hx0 : x 0 = -1 := by
    -- Vanishing of the nonnegative decomposition forces the first square term to vanish.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 3 / 2), sq_nonneg (x 2 - 1 / 2),
      hres0, hres1, hzero]
  have hx1 : x 1 = 3 / 2 := by
    -- Vanishing of the nonnegative decomposition forces the second square term to vanish.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 3 / 2), sq_nonneg (x 2 - 1 / 2),
      hres0, hres1, hzero]
  have hx2 : x 2 = 1 / 2 := by
    -- Vanishing of the nonnegative decomposition forces the third square term to vanish.
    nlinarith [sq_nonneg (x 0 + 1), sq_nonneg (x 1 - 3 / 2), sq_nonneg (x 2 - 1 / 2),
      hres0, hres1, hzero]
  -- Reassemble the point from its three coordinates.
  ext i
  fin_cases i <;> simp [chapter09Example952Solution, hx0, hx1, hx2]

end

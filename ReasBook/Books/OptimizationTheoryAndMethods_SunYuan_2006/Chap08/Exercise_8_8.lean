/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_14
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_4

noncomputable section

section Chapter08Exercise88

local notation "Point" => Fin 1 → ℝ

-- Domain sampling:
-- * primary domain: second-order constrained optimization for a concrete no-constraint example
-- * inspected owner chain:
--   `ConstrainedOptimizationProblem` from `Chapter01.Definition_1_1_extra_1`
--   `ConstrainedOptimizationProblem.activeIneqIndexSet` from `Definition_8_1_1`
--   `ConstrainedOptimizationProblem.linearizedNullConstraintDirections` from `Definition_8_3_2`
--   `ConstrainedOptimizationProblem.lagrangianHessianQuadratic` from `Theorem_8_3_3`
-- * owner abstraction used here: the existing Chapter 8 constrained-problem/KKT/null-direction
--   surface, specialized to the unconstrained quartic example
-- * primitive data: the quartic objective and the empty constraint family
-- * derived API reused directly: KKT points, `G(xStar, lamStar)`, and the Lagrangian Hessian
--   quadratic form

/-- The quartic objective `x ↦ x₀^4` used for the explicit Chapter 8 counterexample. -/
def quarticNoConstraintObjective (x : Point) : ℝ :=
  x 0 ^ (4 : ℕ)

/-- The explicit constrained-problem owner for the no-constraint quartic example. -/
def quarticNoConstraintProblem :
    ConstrainedOptimizationProblem 1 0 (∅ : Set (Fin 0)) (∅ : Set (Fin 0)) where
  objective := quarticNoConstraintObjective
  constraint := Fin.elim0
  eqIndices_union_ineqIndices := by
    ext i
    exact Fin.elim0 i
  eqIndices_disjoint_ineqIndices := by simp

/-- The candidate minimizer for the quartic no-constraint example is the origin. -/
def quarticNoConstraintPoint : Point :=
  0

/-- The no-constraint example has the unique multiplier vector `Fin 0 → ℝ`. -/
def quarticNoConstraintMultipliers : Fin 0 → ℝ :=
  0

/-- A concrete nonzero direction in `ℝ¹` witnessing failure of strict positivity. -/
def quarticNoConstraintDirection : Point :=
  fun _ ↦ 1

/-- Helper for Chapter08 Exercise 8.8: the quartic objective is everywhere nonnegative. -/
theorem quartic_no_constraint_objective_nonneg (x : Point) :
    0 ≤ quarticNoConstraintObjective x := by
  -- Rewrite the quartic as a square of the quadratic factor.
  dsimp [quarticNoConstraintObjective]
  nlinarith [sq_nonneg (x 0 ^ (2 : ℕ))]

/-- Helper for Chapter08 Exercise 8.8: with no equality or inequality constraints, every point is
feasible. -/
theorem quartic_no_constraint_feasible_set_eq_univ :
    quarticNoConstraintProblem.feasibleSet = Set.univ := by
  -- Expand feasibility and eliminate the empty `Fin 0` constraint families.
  ext x
  simp [ConstrainedOptimizationProblem.feasibleSet, quarticNoConstraintProblem]

/-- Helper for Chapter08 Exercise 8.8: the Euclidean Lagrangian reduces to the transported quartic
objective because the multiplier sum is empty. -/
theorem quartic_no_constraint_euclidean_lagrangian_eq :
    quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers =
      fun x : EuclideanSpace ℝ (Fin 1) ↦
        (((EuclideanSpace.equiv (Fin 1) ℝ) x) 0) ^ (4 : ℕ) := by
  -- Expand the Lagrangian and collapse the empty constraint sum.
  simpa [quarticNoConstraintProblem, quarticNoConstraintObjective, quarticNoConstraintMultipliers]
    using
      quarticNoConstraintProblem.euclideanLagrangian_eq_objective_sub_sum
        quarticNoConstraintMultipliers

/-- Helper for Chapter08 Exercise 8.8: the Euclidean Lagrangian is a smooth quartic polynomial in
the unique coordinate. -/
theorem quartic_no_constraint_euclidean_lagrangian_cont_diff :
    ContDiff ℝ 2
      (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers) := by
  -- After rewriting to the coordinate quartic, `fun_prop` handles the polynomial regularity.
  rw [quartic_no_constraint_euclidean_lagrangian_eq]
  fun_prop

/-- Helper for Chapter08 Exercise 8.8: the Euclidean Lagrangian also has a local minimum at the
origin in the Euclidean model. -/
theorem quartic_no_constraint_euclidean_lagrangian_is_local_min_on :
    IsLocalMinOn
      (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
      Set.univ (WithLp.toLp 2 quarticNoConstraintPoint) := by
  rw [isLocalMinOn_univ_iff]
  have hglobal :
      IsMinOn
        (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
        Set.univ (WithLp.toLp 2 quarticNoConstraintPoint) := by
    -- The transported quartic still has value `0` at the origin and is globally nonnegative.
    rw [isMinOn_univ_iff]
    intro x
    rw [quartic_no_constraint_euclidean_lagrangian_eq]
    have hnonneg :
        0 ≤ (((EuclideanSpace.equiv (Fin 1) ℝ) x) 0) ^ (4 : ℕ) := by
      nlinarith [sq_nonneg ((((EuclideanSpace.equiv (Fin 1) ℝ) x) 0) ^ (2 : ℕ))]
    simpa [quarticNoConstraintPoint] using hnonneg
  -- A global minimizer on `Set.univ` is automatically a local minimizer.
  exact hglobal.isLocalMin (by simp)

/-- Helper for Chapter08 Exercise 8.8: stationarity of the Euclidean Lagrangian at the origin is
the only non-vacuous KKT condition in the no-constraint example. -/
theorem quartic_no_constraint_euclidean_lagrangian_stationary_at_origin :
    gradient (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
      (WithLp.toLp 2 quarticNoConstraintPoint) = 0 := by
  have hdiff :
      DifferentiableAt ℝ
        (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
        (WithLp.toLp 2 quarticNoConstraintPoint) := by
    -- The Euclidean Lagrangian is `C²`, hence differentiable, at the base point.
    exact
      (quartic_no_constraint_euclidean_lagrangian_cont_diff.contDiffAt
        : ContDiffAt ℝ 2
            (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
            (WithLp.toLp 2 quarticNoConstraintPoint)).differentiableAt (by norm_num)
  -- Apply the unconstrained first-order necessary condition on the open set `Set.univ`.
  exact
    gradient_eq_zero_of_isLocalMinOn
      Set.univ
      (quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers)
      (WithLp.toLp 2 quarticNoConstraintPoint)
      isOpen_univ (by simp) hdiff
      quartic_no_constraint_euclidean_lagrangian_is_local_min_on

/-- Helper for Chapter08 Exercise 8.8: in the no-constraint example, the Chapter 8 set
`G(xStar, lamStar)` consists exactly of the nonzero directions. -/
theorem quartic_no_constraint_mem_linearized_null_constraint_directions_iff
    (d : Point) :
    d ∈ quarticNoConstraintProblem.linearizedNullConstraintDirections
        quarticNoConstraintPoint quarticNoConstraintMultipliers ↔
      d ≠ 0 := by
  -- Expand the explicit `G(xStar, lamStar)` formula and collapse the empty constraint side.
  rw [quarticNoConstraintProblem.mem_linearizedNullConstraintDirections_iff_explicit]
  constructor
  · rintro ⟨_, _, hd, _, _⟩
    exact hd
  · intro hd
    refine ⟨?_, ?_, hd, ?_, ?_⟩
    · simpa [ConstrainedOptimizationProblem.mem_iff, quarticNoConstraintProblem]
    · intro i hi
      exact Fin.elim0 i
    · intro i hi
      exact Fin.elim0 i
    · intro i hi
      exact Fin.elim0 i

/-- Helper for Chapter08 Exercise 8.8: the chosen witness direction is nonzero. -/
theorem quartic_no_constraint_direction_nonzero :
    quarticNoConstraintDirection ≠ 0 := by
  -- Compare the unique coordinate to rule out equality with the zero vector.
  intro hzero
  have hcoord := congrArg (fun x : Point ↦ x 0) hzero
  simp [quarticNoConstraintDirection] at hcoord

/-- Helper for Chapter08 Exercise 8.8: the Lagrangian Hessian quadratic form at the origin is
identically zero because the quartic has vanishing second derivative there along every line. -/
theorem quartic_no_constraint_lagrangian_hessian_quadratic_eq_zero (d : Point) :
    quarticNoConstraintProblem.lagrangianHessianQuadratic
      quarticNoConstraintPoint quarticNoConstraintMultipliers d = 0 := by
  let L : EuclideanSpace ℝ (Fin 1) → ℝ :=
    quarticNoConstraintProblem.euclideanLagrangian quarticNoConstraintMultipliers
  let xE : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 quarticNoConstraintPoint
  let dE : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 d
  have h_objective :
      ContDiffAt ℝ 2 quarticNoConstraintProblem.objective quarticNoConstraintPoint := by
    -- The original quartic objective is a polynomial in the unique coordinate.
    change ContDiffAt ℝ 2 (fun x : Point ↦ x 0 ^ (4 : ℕ)) quarticNoConstraintPoint
    fun_prop
  have h_constraints :
      ∀ i : Fin 0,
        ContDiffAt ℝ 2 (quarticNoConstraintProblem.constraint i) quarticNoConstraintPoint := by
    -- There are no constraint functions to check.
    intro i
    exact Fin.elim0 i
  have h_hessian_eq :
      quarticNoConstraintProblem.lagrangianHessianQuadratic
          quarticNoConstraintPoint quarticNoConstraintMultipliers d =
        (iteratedFDeriv ℝ 2 L xE) ![dE, dE] := by
    -- Rewrite the quadratic form via the canonical `iteratedFDeriv` bridge.
    simpa [L, xE, dE] using
      quarticNoConstraintProblem.lagrangianHessianQuadratic_eq_iteratedFDeriv_two
        quarticNoConstraintPoint d quarticNoConstraintMultipliers
        h_objective h_constraints
  have h_diag_zero :
      (iteratedFDeriv ℝ 2 L xE) ![dE, dE] = 0 := by
    have h_line_eq :
        (fun t : ℝ ↦ L (AffineMap.lineMap xE (xE + dE) t)) =
          fun t : ℝ ↦
            t ^ (4 : ℕ) * ((((EuclideanSpace.equiv (Fin 1) ℝ) dE) 0) ^ (4 : ℕ)) := by
      -- Restricting to the line through the origin in direction `dE` produces a scalar quartic.
      funext t
      simpa [L, xE, dE, quarticNoConstraintPoint, AffineMap.lineMap_apply_module',
        quartic_no_constraint_euclidean_lagrangian_eq, mul_pow] using
        (show (t * d 0) ^ (4 : ℕ) = t ^ (4 : ℕ) * (d 0) ^ (4 : ℕ) from by
          rw [mul_pow])
    have h_deriv2_eq :
        (deriv^[2]) (fun t : ℝ ↦ L (AffineMap.lineMap xE (xE + dE) t)) 0 =
          (iteratedFDeriv ℝ 2 L xE) ![dE, dE] := by
      -- Use the Chapter 1 line-restriction bridge from Hessians to one-variable derivatives.
      simpa [L, xE, dE] using
        deriv2_lineMap_eq_iteratedFDeriv_diag
          (S := Set.univ) (f := L) (x := xE) (y := xE + dE) (I := Set.univ) isOpen_univ
          quartic_no_constraint_euclidean_lagrangian_cont_diff.contDiffOn
          (fun _ _ ↦ Set.mem_univ _) (t := 0) (Set.mem_univ _)
    have h_deriv2_zero :
        (deriv^[2]) (fun t : ℝ ↦ L (AffineMap.lineMap xE (xE + dE) t)) 0 = 0 := by
      -- The second derivative of `t ↦ t^4 * c` vanishes at `t = 0`.
      rw [h_line_eq, ← iteratedDeriv_eq_iterate]
      calc
        iteratedDeriv 2
            (fun t : ℝ ↦
              t ^ (4 : ℕ) * ((((EuclideanSpace.equiv (Fin 1) ℝ) dE) 0) ^ (4 : ℕ))) 0
            =
          iteratedDeriv 2 (fun t : ℝ ↦ t ^ (4 : ℕ)) 0 *
            ((((EuclideanSpace.equiv (Fin 1) ℝ) dE) 0) ^ (4 : ℕ)) := by
              simpa using
                iteratedDeriv_mul_const_field
                  (n := 2) (f := fun t : ℝ ↦ t ^ (4 : ℕ))
                  ((((EuclideanSpace.equiv (Fin 1) ℝ) dE) 0) ^ (4 : ℕ)) (x := 0)
        _ = 0 := by
          have hpow_zero : iteratedDeriv 2 (fun t : ℝ ↦ t ^ (4 : ℕ)) 0 = 0 := by
            norm_num [iteratedDeriv_pow]
          rw [hpow_zero]
          simp
    exact h_deriv2_eq.symm.trans h_deriv2_zero
  -- The quadratic form is zero because its `iteratedFDeriv` diagonal is zero.
  exact h_hessian_eq.trans h_diag_zero

/-- The origin is a local minimizer of the quartic no-constraint objective on
the feasible set. -/
theorem quarticNoConstraintPoint_isLocalMinOn :
    IsLocalMinOn quarticNoConstraintProblem
      quarticNoConstraintProblem.feasibleSet quarticNoConstraintPoint := by
  rw [quartic_no_constraint_feasible_set_eq_univ, isLocalMinOn_univ_iff]
  have hglobal : IsMinOn quarticNoConstraintProblem Set.univ quarticNoConstraintPoint := by
    -- The quartic objective has value `0` at the origin and is nonnegative everywhere.
    rw [isMinOn_univ_iff]
    intro x
    simpa [quarticNoConstraintPoint, quarticNoConstraintProblem, quarticNoConstraintObjective]
      using quartic_no_constraint_objective_nonneg x
  -- A global minimizer on `Set.univ` is in particular a local minimizer.
  exact hglobal.isLocalMin (by simp)

/-- The origin with the trivial multiplier vector is a KKT point of the quartic
no-constraint problem. -/
theorem quarticNoConstraintPoint_isKKTPoint :
    quarticNoConstraintProblem.IsKKTPoint quarticNoConstraintPoint
      quarticNoConstraintMultipliers := by
  refine
    { feasible := ?_
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · -- Feasibility is automatic because the feasible set is all of `Point`.
    change quarticNoConstraintPoint ∈ quarticNoConstraintProblem.feasibleSet
    rw [quartic_no_constraint_feasible_set_eq_univ]
    simp [quarticNoConstraintPoint]
  · -- There are no inequality multipliers to check.
    intro i hi
    exact Fin.elim0 i
  · -- The Euclidean Lagrangian is stationary at the origin.
    simpa using quartic_no_constraint_euclidean_lagrangian_stationary_at_origin
  · -- Complementary slackness is vacuous in the no-constraint problem.
    intro i hi
    exact Fin.elim0 i

/-- Chapter08 Exercise 8.8 (1): for the unconstrained quartic example
`x ↦ x₀^4` at the origin, the second-order necessary condition holds on the
Chapter 8 owner `G(xStar, lamStar)`, written as
`problem.linearizedNullConstraintDirections xStar lamStar`. -/
theorem quarticNoConstraintExample_secondOrderNecessaryCondition :
    ∀ d ∈ quarticNoConstraintProblem.linearizedNullConstraintDirections
        quarticNoConstraintPoint quarticNoConstraintMultipliers,
      0 ≤ quarticNoConstraintProblem.lagrangianHessianQuadratic
        quarticNoConstraintPoint quarticNoConstraintMultipliers d := by
  intro d _
  -- The quadratic form is identically zero, so nonnegativity is immediate.
  simpa [quartic_no_constraint_lagrangian_hessian_quadratic_eq_zero d]

/-- In the quartic counterexample, `quarticNoConstraintDirection` belongs to
`G(xStar, lamStar)`. -/
theorem quarticNoConstraintDirection_memLinearizedNullConstraintDirections :
    quarticNoConstraintDirection ∈
      quarticNoConstraintProblem.linearizedNullConstraintDirections
        quarticNoConstraintPoint quarticNoConstraintMultipliers := by
  -- In the no-constraint case, every nonzero direction belongs to `G(xStar, lamStar)`.
  rw [quartic_no_constraint_mem_linearized_null_constraint_directions_iff]
  exact quartic_no_constraint_direction_nonzero

/-- In the quartic counterexample, `quarticNoConstraintDirection` is nonzero
and has zero Lagrangian Hessian quadratic value. -/
theorem quarticNoConstraintDirection_nonzero_and_lagrangianHessianQuadratic_eq_zero :
    quarticNoConstraintDirection ≠ 0 ∧
      quarticNoConstraintProblem.lagrangianHessianQuadratic
        quarticNoConstraintPoint quarticNoConstraintMultipliers
        quarticNoConstraintDirection = 0 := by
  -- Package the witness direction's two key properties together for later reuse.
  exact
    ⟨quartic_no_constraint_direction_nonzero,
      quartic_no_constraint_lagrangian_hessian_quadratic_eq_zero
        quarticNoConstraintDirection⟩

/-- Chapter08 Exercise 8.8 (2): the second-order sufficient condition fails
for the unconstrained quartic example `x ↦ x₀^4` at the origin because some
nonzero direction in `G(xStar, lamStar)` has zero Lagrangian Hessian quadratic
value. -/
theorem quarticNoConstraintExample_secondOrderSufficientConditionFailure :
    ∃ d ∈ quarticNoConstraintProblem.linearizedNullConstraintDirections
        quarticNoConstraintPoint quarticNoConstraintMultipliers,
      quarticNoConstraintProblem.lagrangianHessianQuadratic
          quarticNoConstraintPoint quarticNoConstraintMultipliers d = 0 := by
  -- The fixed nonzero direction `quarticNoConstraintDirection` is the required witness.
  refine
    ⟨quarticNoConstraintDirection,
      quarticNoConstraintDirection_memLinearizedNullConstraintDirections, ?_⟩
  exact quarticNoConstraintDirection_nonzero_and_lagrangianHessianQuadratic_eq_zero.2

end Chapter08Exercise88

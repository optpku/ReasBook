/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Definition_13_3_extra_2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

open scoped BigOperators

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ

-- Domain-style sampling:
-- * primary domain: constrained trust-region feasibility systems with a chosen vector norm on
--   `ℝ^n`, built from affine linearized constraint residuals and penalty/surrogate replacements;
-- * sampled owner declarations:
--   `IsVectorNorm`, `IsVectorNorm.toSeminorm`, and `IsVectorNorm.toAddGroupNorm` in
--   Chapter 01 Definition 1.2.1, together with `linearizedConstraintValue` in
--   Chapter 13 Definition 13.3-extra-2;
-- * core/canonical owners reused here: `IsVectorNorm` for the chosen trust-region norm and
--   `linearizedConstraintValue` for the affine residual map `c + Aᵀ d`;
-- * primitive data in this file: the chosen vector norm `ρ` on coordinate vectors
--   `Fin n → ℝ`, together with the chosen penalty/surrogate functionals;
-- * derived API in this file: the feasible sets and trust-region penalty subproblem built from
--   those primitive choices.
--
-- Semantic recall: Chapter 13 already owns the affine residual map `c + Aᵀ d` as
-- `linearizedConstraintValue`, so this file reuses that owner instead of restating it locally.
-- The chosen trust-region norm is now expressed through Chapter 01's canonical owner
-- `IsVectorNorm`, while the scaled-constraint, piecewise-squares, and penalty constructions
-- remain source-facing.

/-- A step satisfies the chosen trust-region bound exactly when the chosen Chapter 01 vector norm
`ρ` evaluates to at most `Δ` on the coordinate realization `d.ofLp`. -/
def satisfiesTrustRegionConstraint
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) (d : Point) : Prop :=
  ρ d.ofLp ≤ Δ

/-- Unfolding `satisfiesTrustRegionConstraint ρ Δ d` gives the source trust-region bound written
with the chosen Chapter 01 vector norm owner `ρ`. -/
theorem satisfiesTrustRegionConstraint_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) (d : Point) :
    satisfiesTrustRegionConstraint ρ Δ d ↔ ρ d.ofLp ≤ Δ :=
  Iff.rfl

/-- A step satisfies the scaled linearized constraints when equality-block coordinates vanish
and inequality-block coordinates are nonnegative after replacing `c` by `θ • c` in the chapter
owner `linearizedConstraintValue`. -/
def satisfiesScaledLinearizedConstraints
    (eqCount : ℕ) (θ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : Prop :=
  (∀ i : Fin m, i.1 < eqCount → linearizedConstraintValue (θ • c) A d i = 0) ∧
    ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue (θ • c) A d i

/-- Unfolding `satisfiesScaledLinearizedConstraints eqCount θ c A d` gives the equality and
inequality conditions of the scaled linearized system. -/
theorem satisfiesScaledLinearizedConstraints_iff
    (eqCount : ℕ) (θ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    satisfiesScaledLinearizedConstraints eqCount θ c A d ↔
      (∀ i : Fin m, i.1 < eqCount → linearizedConstraintValue (θ • c) A d i = 0) ∧
        ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue (θ • c) A d i :=
  Iff.rfl

/-- The feasible set cut out by the explicit trust-region bound `ρ d ≤ Δ` together with the
scaled linearized constraints
`θ * c_i(x_k) + dᵀ ∇ c_i(x_k) = 0` for `i < eqCount` and
`0 ≤ θ * c_i(x_k) + dᵀ ∇ c_i(x_k)` for `eqCount ≤ i`. -/
def scaledTrustRegionFeasibleSet
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ θ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) : Set Point :=
  {d | satisfiesTrustRegionConstraint ρ Δ d ∧
      satisfiesScaledLinearizedConstraints eqCount θ c A d}

/-- The source-side admissibility conditions for the scaled-constraint trust-region approach:
`eqCount ≤ m`, `0 < Δ`, and `θ ∈ (0, 1]`. -/
def scaledTrustRegionApproachAdmissible
    (m eqCount : ℕ) (Δ θ : ℝ) : Prop :=
  eqCount ≤ m ∧ 0 < Δ ∧ 0 < θ ∧ θ ≤ 1

/-- Chapter13 Remark 13.1-extra-1 (1): membership in
`scaledTrustRegionFeasibleSet ρ eqCount Δ θ c A` is exactly the trust-region bound together with
the scaled linearized equality and inequality constraints. -/
theorem mem_scaledTrustRegionFeasibleSet_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ θ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    d ∈ scaledTrustRegionFeasibleSet ρ eqCount Δ θ c A ↔
      satisfiesTrustRegionConstraint ρ Δ d ∧
        satisfiesScaledLinearizedConstraints eqCount θ c A d :=
  Iff.rfl

/-- The `i`-th term in the piecewise-squares surrogate `(13.1.5)`: equality-block coordinates use
`(c_i + dᵀ ∇ c_i(x_k))^2`, while inequality-block coordinates use
`(min 0 (c_i + dᵀ ∇ c_i(x_k)))^2`. -/
def linearizedViolationSquareTerm
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (d : Point) (i : Fin m) : ℝ :=
  if i.1 < eqCount then
    (linearizedConstraintValue c A d i) ^ (2 : ℕ)
  else
    (min (0 : ℝ) (linearizedConstraintValue c A d i)) ^ (2 : ℕ)

/-- Unfolding `linearizedViolationSquareTerm eqCount c A d i` gives the source piecewise square
attached to the `i`-th linearized constraint. -/
theorem linearizedViolationSquareTerm_eq
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (d : Point) (i : Fin m) :
    linearizedViolationSquareTerm eqCount c A d i =
      if i.1 < eqCount then
        (linearizedConstraintValue c A d i) ^ (2 : ℕ)
      else
        (min (0 : ℝ) (linearizedConstraintValue c A d i)) ^ (2 : ℕ) :=
  rfl

/-- The piecewise-squares linearized violation from `(13.1.5)`, obtained by summing the
equality-block squares and the inequality-block squares of the negative parts. -/
def linearizedViolationSquares
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : ℝ :=
  ∑ i : Fin m, linearizedViolationSquareTerm eqCount c A d i

/-- Evaluating `linearizedViolationSquares eqCount c A d` gives the sum of the source
piecewise-square terms. -/
theorem linearizedViolationSquares_eq
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    linearizedViolationSquares eqCount c A d =
      ∑ i : Fin m, linearizedViolationSquareTerm eqCount c A d i :=
  rfl

/-- A step satisfies the piecewise-squares surrogate constraint `(13.1.5)` exactly when the
sum of equality-block squares and inequality-block negative-part squares is bounded by `ξ`. -/
def satisfiesLinearizedSquaresConstraint
    (eqCount : ℕ) (ξ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : Prop :=
  linearizedViolationSquares eqCount c A d ≤ ξ

/-- Unfolding `satisfiesLinearizedSquaresConstraint eqCount ξ c A d` gives the single
piecewise-squares constraint from `(13.1.5)`. -/
theorem satisfiesLinearizedSquaresConstraint_iff
    (eqCount : ℕ) (ξ : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    satisfiesLinearizedSquaresConstraint eqCount ξ c A d ↔
      linearizedViolationSquares eqCount c A d ≤ ξ :=
  Iff.rfl

/-- The feasible set cut out by the explicit trust-region bound `ρ d ≤ Δ` together with the
piecewise-squares surrogate bound `linearizedViolationSquares eqCount c A d ≤ ξ`. -/
def piecewiseSquaresTrustRegionFeasibleSet
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ ξ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) : Set Point :=
  {d | satisfiesTrustRegionConstraint ρ Δ d ∧
      satisfiesLinearizedSquaresConstraint eqCount ξ c A d}

/-- The source-side admissibility conditions for the piecewise-squares trust-region approach:
`eqCount ≤ m`, `0 < Δ`, and `0 ≤ ξ`. -/
def piecewiseSquaresTrustRegionApproachAdmissible
    (m eqCount : ℕ) (Δ ξ : ℝ) : Prop :=
  eqCount ≤ m ∧ 0 < Δ ∧ 0 ≤ ξ

/-- Chapter13 Remark 13.1-extra-1 (2): membership in
`piecewiseSquaresTrustRegionFeasibleSet ρ eqCount Δ ξ c A` is exactly the trust-region bound
together with the piecewise-squares surrogate constraint `(13.1.5)`. -/
theorem mem_piecewiseSquaresTrustRegionFeasibleSet_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (eqCount : ℕ) (Δ ξ : ℝ)
    (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    d ∈ piecewiseSquaresTrustRegionFeasibleSet ρ eqCount Δ ξ c A ↔
      satisfiesTrustRegionConstraint ρ Δ d ∧
        satisfiesLinearizedSquaresConstraint eqCount ξ c A d :=
  Iff.rfl

/-- When `ξ = 0`, the single piecewise-squares constraint is equivalent to the original
linearized equality constraints on `i < eqCount` together with the linearized inequality
constraints on `eqCount ≤ i`. -/
theorem satisfiesLinearizedSquaresConstraint_zero_iff
    (eqCount : ℕ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    satisfiesLinearizedSquaresConstraint eqCount 0 c A d ↔
      (∀ i : Fin m, i.1 < eqCount → linearizedConstraintValue c A d i = 0) ∧
        ∀ i : Fin m, eqCount ≤ i.1 → 0 ≤ linearizedConstraintValue c A d i := by
  rw [satisfiesLinearizedSquaresConstraint_iff]
  constructor
  · intro h
    have hsum_nonneg :
        0 ≤ linearizedViolationSquares eqCount c A d := by
      rw [linearizedViolationSquares_eq]
      exact Finset.sum_nonneg fun i _ ↦ by
        by_cases hi : i.1 < eqCount
        · simp [linearizedViolationSquareTerm, hi, sq_nonneg]
        · simp [linearizedViolationSquareTerm, hi, sq_nonneg]
    have hsum_eq : linearizedViolationSquares eqCount c A d = 0 :=
      le_antisymm h hsum_nonneg
    have hterm_zero : ∀ i : Fin m, linearizedViolationSquareTerm eqCount c A d i = 0 := by
      rw [linearizedViolationSquares_eq] at hsum_eq
      intro i
      exact
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ by
          by_cases hj : j.1 < eqCount
          · simp [linearizedViolationSquareTerm, hj, sq_nonneg]
          · simp [linearizedViolationSquareTerm, hj, sq_nonneg]).1 hsum_eq i (by simp)
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa [linearizedViolationSquareTerm, hi] using hterm_zero i
    · intro i hi
      have hmin_sq_zero : (min (0 : ℝ) (linearizedConstraintValue c A d i)) ^ (2 : ℕ) = 0 := by
        simpa [linearizedViolationSquareTerm, Nat.not_lt.mpr hi] using hterm_zero i
      have hmin_zero : min (0 : ℝ) (linearizedConstraintValue c A d i) = 0 := by
        simpa using hmin_sq_zero
      simpa using hmin_zero
  · rintro ⟨heq, hineq⟩
    have hterm_zero : ∀ i : Fin m, linearizedViolationSquareTerm eqCount c A d i = 0 := by
      intro i
      by_cases hi : i.1 < eqCount
      · have hvalue : linearizedConstraintValue c A d i = 0 := heq i hi
        simpa [linearizedViolationSquareTerm, hi, hvalue]
      · have hle : eqCount ≤ i.1 := Nat.not_lt.mp hi
        have hvalue : 0 ≤ linearizedConstraintValue c A d i := hineq i hle
        simpa [linearizedViolationSquareTerm, hi, min_eq_left hvalue]
    have hsum_eq : linearizedViolationSquares eqCount c A d = 0 := by
      simp [linearizedViolationSquares_eq, hterm_zero]
    exact hsum_eq.le

/-- The penalty-subproblem objective obtained by adding the scaled penalty of the affine
linearized constraint residual `c + Aᵀ d` to the base model objective. -/
def trustRegionPenaltyObjective
    (constraintPenalty : ConstraintPoint → ℝ) (σ : ℝ)
    (modelObjective : Point → ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : ℝ :=
  modelObjective d + σ * constraintPenalty (linearizedConstraintValue c A d)

/-- Unfolding `trustRegionPenaltyObjective constraintPenalty σ modelObjective c A d` gives the
base model objective plus the scaled penalty term on the linearized constraint residual. -/
theorem trustRegionPenaltyObjective_eq
    (constraintPenalty : ConstraintPoint → ℝ) (σ : ℝ)
    (modelObjective : Point → ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    trustRegionPenaltyObjective constraintPenalty σ modelObjective c A d =
      modelObjective d + σ * constraintPenalty (linearizedConstraintValue c A d) :=
  rfl

/-- The feasible set for the third trust-region approach consists exactly of the trial steps
that satisfy the explicit trust-region bound `ρ d ≤ Δ`. -/
def trustRegionPenaltyFeasibleSet
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) : Set Point :=
  {d | satisfiesTrustRegionConstraint ρ Δ d}

/-- Membership in `trustRegionPenaltyFeasibleSet ρ Δ` is exactly the source trust-region
constraint `satisfiesTrustRegionConstraint ρ Δ d`. -/
theorem mem_trustRegionPenaltyFeasibleSet_iff
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ) (d : Point) :
    d ∈ trustRegionPenaltyFeasibleSet ρ Δ ↔ satisfiesTrustRegionConstraint ρ Δ d :=
  Iff.rfl

/-- Chapter13 Remark 13.1-extra-1 (3): the third constrained trust-region approach replaces the
linearized equality/inequality system by the penalty-subproblem objective
`d ↦ modelObjective d + σ * constraintPenalty (c + Aᵀ d)`, optimized over the trust-region
feasible set `trustRegionPenaltyFeasibleSet ρ Δ`. -/
def trustRegionPenaltySubproblem
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ)
    (constraintPenalty : ConstraintPoint → ℝ) (σ : ℝ)
    (modelObjective : Point → ℝ) (c : ConstraintPoint) (A : Jacobian) :
    trustRegionPenaltyFeasibleSet ρ Δ → ℝ :=
  fun d ↦ trustRegionPenaltyObjective constraintPenalty σ modelObjective c A d

/-- Evaluating `trustRegionPenaltySubproblem ρ Δ constraintPenalty σ modelObjective c A` at an
admissible trial step gives the penalty objective on that trust-region-constrained step. -/
theorem trustRegionPenaltySubproblem_apply
    (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] (Δ : ℝ)
    (constraintPenalty : ConstraintPoint → ℝ) (σ : ℝ)
    (modelObjective : Point → ℝ) (c : ConstraintPoint) (A : Jacobian)
    (d : trustRegionPenaltyFeasibleSet ρ Δ) :
    trustRegionPenaltySubproblem ρ Δ constraintPenalty σ modelObjective c A d =
      trustRegionPenaltyObjective constraintPenalty σ modelObjective c A d :=
  rfl

#print axioms satisfiesTrustRegionConstraint
#print axioms linearizedConstraintValue
#print axioms scaledTrustRegionFeasibleSet
#print axioms linearizedViolationSquareTerm
#print axioms linearizedViolationSquares
#print axioms satisfiesLinearizedSquaresConstraint
#print axioms piecewiseSquaresTrustRegionFeasibleSet
#print axioms trustRegionPenaltyObjective
#print axioms trustRegionPenaltyFeasibleSet
#print axioms trustRegionPenaltySubproblem

end

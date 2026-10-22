/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

section

-- Semantic recall: `lean_leansearch` surfaced the Hilbert-space adjoint API
-- `ContinuousLinearMap.adjoint`, but no existing project owner for this exact SQP subproblem.
-- This file therefore keeps the quadratic objective, the linearized equality constraints, and
-- the eventual subproblem assumption explicit at the source-facing level.

section Objective

variable {Point : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]

/-- The quadratic SQP subproblem objective
`d ↦ gᵀ d + (1 / 2) dᵀ B d`. -/
def sqpSubproblemObjective
    (g : Point) (B : Point →L[ℝ] Point) (d : Point) : ℝ :=
  inner ℝ g d + (1 / 2 : ℝ) * inner ℝ d (B d)

/-- Unfolding `sqpSubproblemObjective g B d` gives the source quadratic model. -/
theorem sqpSubproblemObjective_eq
    (g : Point) (B : Point →L[ℝ] Point) (d : Point) :
    sqpSubproblemObjective g B d =
      inner ℝ g d + (1 / 2 : ℝ) * inner ℝ d (B d) :=
  rfl

end Objective

section Constraints

variable {Point Multiplier : Type*}
variable [NormedAddCommGroup Point] [InnerProductSpace ℝ Point] [CompleteSpace Point]
variable [NormedAddCommGroup Multiplier] [InnerProductSpace ℝ Multiplier]
  [CompleteSpace Multiplier]

/-- The linearized equality constraints `A(x_k)ᵀ d = -ĉ(x_k)` written with the Hilbert-space
adjoint of `A(x_k)`. -/
def satisfiesSqpLinearizedConstraints
    (A : Multiplier →L[ℝ] Point) (cHat : Multiplier) (d : Point) : Prop :=
  A.adjoint d = -cHat

/-- Unfolding `satisfiesSqpLinearizedConstraints A cHat d` gives the source linearized
constraint equation `Aᵀ d = -ĉ`. -/
theorem satisfiesSqpLinearizedConstraints_iff
    (A : Multiplier →L[ℝ] Point) (cHat : Multiplier) (d : Point) :
    satisfiesSqpLinearizedConstraints A cHat d ↔ A.adjoint d = -cHat :=
  Iff.rfl

/-- A step `d` solves the equality-constrained SQP quadratic subproblem when it satisfies the
linearized constraints and minimizes the quadratic model over all linearly feasible directions. -/
def isSqpSubproblemSolution
    (g : Point) (B : Point →L[ℝ] Point)
    (A : Multiplier →L[ℝ] Point) (cHat : Multiplier) (d : Point) : Prop :=
  satisfiesSqpLinearizedConstraints A cHat d ∧
    ∀ d' : Point, satisfiesSqpLinearizedConstraints A cHat d' →
      sqpSubproblemObjective g B d ≤ sqpSubproblemObjective g B d'

/-- Unfolding `isSqpSubproblemSolution g B A cHat d` gives the feasibility and minimality
clauses of the SQP subproblem. -/
theorem isSqpSubproblemSolution_iff
    (g : Point) (B : Point →L[ℝ] Point)
    (A : Multiplier →L[ℝ] Point) (cHat : Multiplier) (d : Point) :
    isSqpSubproblemSolution g B A cHat d ↔
      satisfiesSqpLinearizedConstraints A cHat d ∧
        ∀ d' : Point, satisfiesSqpLinearizedConstraints A cHat d' →
          sqpSubproblemObjective g B d ≤ sqpSubproblemObjective g B d' :=
  Iff.rfl

/-- A solution of the SQP subproblem satisfies the linearized equality constraints. -/
theorem isSqpSubproblemSolution.feasible
    {g : Point} {B : Point →L[ℝ] Point}
    {A : Multiplier →L[ℝ] Point} {cHat : Multiplier} {d : Point}
    (h : isSqpSubproblemSolution g B A cHat d) :
    satisfiesSqpLinearizedConstraints A cHat d :=
  h.1

/-- A solution of the SQP subproblem minimizes the quadratic model over linearly feasible
directions. -/
theorem isSqpSubproblemSolution.objective_le
    {g : Point} {B : Point →L[ℝ] Point}
    {A : Multiplier →L[ℝ] Point} {cHat : Multiplier} {d : Point}
    (h : isSqpSubproblemSolution g B A cHat d)
    (d' : Point) (hd' : satisfiesSqpLinearizedConstraints A cHat d') :
    sqpSubproblemObjective g B d ≤ sqpSubproblemObjective g B d' :=
  h.2 d' hd'

/-- Chapter12 Assumption 12.3.2: for all sufficiently large `k`, the recorded SQP step `d k`
solves the quadratic program
`min_d (inner ℝ (g k) d + (1 / 2) * inner ℝ d (B k d))`
subject to the active linearized constraints
`(activeJacobian (x k) xStar).adjoint d = -activeConstraintValues (x k) xStar`,
where `activeJacobian (x k) xStar` represents `A(x_k)` and
`activeConstraintValues (x k) xStar` represents `ĉ(x_k)` for the active index set
`E ∪ I(x*)`. -/
def satisfiesEventualSqpSubproblemAssumption
    (x : ℕ → Point) (xStar : Point) (g : ℕ → Point)
    (B : ℕ → Point →L[ℝ] Point)
    (activeJacobian : Point → Point → Multiplier →L[ℝ] Point)
    (activeConstraintValues : Point → Point → Multiplier)
    (d : ℕ → Point) : Prop :=
  ∃ K : ℕ, ∀ k ≥ K,
    isSqpSubproblemSolution
      (g k) (B k)
      (activeJacobian (x k) xStar)
      (activeConstraintValues (x k) xStar)
      (d k)

/-- Unfolding `satisfiesEventualSqpSubproblemAssumption` gives the eventual source statement:
for all sufficiently large `k`, `d k` solves the corresponding SQP subproblem. -/
theorem satisfiesEventualSqpSubproblemAssumption_iff
    (x : ℕ → Point) (xStar : Point) (g : ℕ → Point)
    (B : ℕ → Point →L[ℝ] Point)
    (activeJacobian : Point → Point → Multiplier →L[ℝ] Point)
    (activeConstraintValues : Point → Point → Multiplier)
    (d : ℕ → Point) :
    satisfiesEventualSqpSubproblemAssumption
        x xStar g B activeJacobian activeConstraintValues d ↔
      ∃ K : ℕ, ∀ k ≥ K,
        isSqpSubproblemSolution
          (g k) (B k)
          (activeJacobian (x k) xStar)
          (activeConstraintValues (x k) xStar)
          (d k) :=
  Iff.rfl

/-- `satisfiesEventualSqpSubproblemAssumption x xStar g B activeJacobian
activeConstraintValues d` gives the canonical `Filter.atTop` eventuality that `d k` solves the
corresponding SQP subproblem. -/
theorem satisfiesEventualSqpSubproblemAssumption.eventually
    {x : ℕ → Point} {xStar : Point} {g : ℕ → Point}
    {B : ℕ → Point →L[ℝ] Point}
    {activeJacobian : Point → Point → Multiplier →L[ℝ] Point}
    {activeConstraintValues : Point → Point → Multiplier}
    {d : ℕ → Point}
    (h :
      satisfiesEventualSqpSubproblemAssumption
        x xStar g B activeJacobian activeConstraintValues d) :
    ∀ᶠ k in Filter.atTop,
      isSqpSubproblemSolution
        (g k) (B k)
        (activeJacobian (x k) xStar)
        (activeConstraintValues (x k) xStar)
        (d k) := by
  rcases h with ⟨K, hK⟩
  exact Filter.eventually_atTop.2 ⟨K, fun k hk ↦ hK k hk⟩

/-- Rewriting `satisfiesEventualSqpSubproblemAssumption` at `Filter.atTop` recovers the
canonical eventual-form companion to the source threshold statement. -/
theorem satisfiesEventualSqpSubproblemAssumption_iff_eventually
    (x : ℕ → Point) (xStar : Point) (g : ℕ → Point)
    (B : ℕ → Point →L[ℝ] Point)
    (activeJacobian : Point → Point → Multiplier →L[ℝ] Point)
    (activeConstraintValues : Point → Point → Multiplier)
    (d : ℕ → Point) :
    satisfiesEventualSqpSubproblemAssumption
        x xStar g B activeJacobian activeConstraintValues d ↔
      ∀ᶠ k in Filter.atTop,
        isSqpSubproblemSolution
          (g k) (B k)
          (activeJacobian (x k) xStar)
          (activeConstraintValues (x k) xStar)
          (d k) := by
  constructor
  · exact satisfiesEventualSqpSubproblemAssumption.eventually
  · rw [Filter.eventually_atTop]
    rintro ⟨K, hK⟩
    exact ⟨K, fun k hk ↦ hK k hk⟩

end Constraints

end

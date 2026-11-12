/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.FeasibleRegion
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective

open scoped Matrix MixedIntegerNotation

@[expose] public section

section Definition12

variable {m n p : ℕ}

/-- Definition 1.2 (1). A mixed integer linear program is the optimization problem
`max c x + h y` subject to `A x + G y ≤ b`, `x ∈ ℤ_+^n`, `y ∈ ℝ_+^p`. -/
structure MixedIntegerLinearProgram (m n p : ℕ) where
  integerMatrix : Matrix (Fin m) (Fin n) ℝ
  continuousMatrix : Matrix (Fin m) (Fin p) ℝ
  rhs : Fin m → ℝ
  integerObjective : Fin n → ℝ
  continuousObjective : Fin p → ℝ

namespace MixedIntegerLinearProgram

/-- Construct a mixed integer linear program from its coefficient and objective data. -/
def ofCoefficients
    (integerMatrix : Matrix (Fin m) (Fin n) ℝ)
    (continuousMatrix : Matrix (Fin m) (Fin p) ℝ)
    (rhs : Fin m → ℝ)
    (integerObjective : Fin n → ℝ)
    (continuousObjective : Fin p → ℝ) :
    MixedIntegerLinearProgram m n p :=
  { integerMatrix := integerMatrix
    continuousMatrix := continuousMatrix
    rhs := rhs
    integerObjective := integerObjective
    continuousObjective := continuousObjective }

/-- The nonnegative real relaxation cut out by the mixed linear inequalities of `P`. -/
def lpRelaxation (P : MixedIntegerLinearProgram m n p) : Set (MixedRealPoint n p) :=
  lp_relaxation_feasible_set P.integerMatrix P.continuousMatrix P.rhs

/-- `P.lpRelaxation` is the canonical LP-relaxation feasible set attached to the coefficient data
of `P`. -/
theorem lpRelaxation_eq_lp_relaxation_feasible_set
    (P : MixedIntegerLinearProgram m n p) :
    P.lpRelaxation = lp_relaxation_feasible_set P.integerMatrix P.continuousMatrix P.rhs := rfl

/-- Definition 1.2 (2). The feasible set of `P`, called its mixed integer linear set, consists of
the mixed-integer points in the nonnegative relaxation `P.lpRelaxation`. -/
def feasibleSet (P : MixedIntegerLinearProgram m n p) : Set (MixedRealPoint n p) :=
  milp_feasible_set P.integerMatrix P.continuousMatrix P.rhs

/-- `P.feasibleSet` is the canonical mixed-integer feasible set cut out by the coefficient data of
`P`. -/
theorem feasibleSet_eq_milp_feasible_set
    (P : MixedIntegerLinearProgram m n p) :
    P.feasibleSet = milp_feasible_set P.integerMatrix P.continuousMatrix P.rhs := rfl

/-- The objective function `(x, y) ↦ c x + h y` of `P`. -/
def objectiveValue (P : MixedIntegerLinearProgram m n p) : MixedRealPoint n p → ℝ :=
  mixed_linear_objective P.integerObjective P.continuousObjective

/-- The set of objective values attained by feasible points of `P`. -/
def objectiveValues (P : MixedIntegerLinearProgram m n p) : Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.lpRelaxation` is exactly the mixed system `A x + G y ≤ b` together with
coordinatewise nonnegativity of the integer and continuous blocks. -/
theorem mem_lpRelaxation_iff
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    xy ∈ P.lpRelaxation ↔
      P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 := by
  simpa [lpRelaxation] using
    (mem_lp_relaxation_feasible_set_iff :
      xy ∈ lp_relaxation_feasible_set P.integerMatrix P.continuousMatrix P.rhs ↔
        P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
          0 ≤ xy.1 ∧ 0 ≤ xy.2)

/-- Membership in `P.feasibleSet` is exactly the mixed system `A x + G y ≤ b` together with
coordinatewise nonnegativity and membership in the canonical mixed lattice `ℤ^n × ℝ^p`. -/
theorem mem_feasibleSet_iff_mem_mixed_integer_lattice
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    xy ∈ P.feasibleSet ↔
      P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ xy ∈ (ℤ^n×ℝ^p) := by
  simpa [feasibleSet] using
    (mem_milp_feasible_set_iff_mem_mixed_integer_lattice :
      xy ∈ milp_feasible_set P.integerMatrix P.continuousMatrix P.rhs ↔
        P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
          0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ xy ∈ (ℤ^n×ℝ^p))

/-- Membership in `P.feasibleSet` is exactly the mixed system `A x + G y ≤ b` together with
coordinatewise integrality of `x` and coordinatewise nonnegativity of `x` and `y`. -/
theorem mem_feasibleSet_iff
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    xy ∈ P.feasibleSet ↔
      P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ ∀ j : Fin n, ∃ z : ℤ, xy.1 j = (z : ℝ) := by
  simpa [feasibleSet] using
    (mem_milp_feasible_set_iff :
      xy ∈ milp_feasible_set P.integerMatrix P.continuousMatrix P.rhs ↔
        P.integerMatrix *ᵥ xy.1 + P.continuousMatrix *ᵥ xy.2 ≤ P.rhs ∧
          0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ ∀ j : Fin n, ∃ z : ℤ, xy.1 j = (z : ℝ))

/-- The mixed-integer feasible set of `P` is contained in the LP relaxation of `P`. -/
theorem feasibleSet_subset_lpRelaxation
    (P : MixedIntegerLinearProgram m n p) :
    P.feasibleSet ⊆ P.lpRelaxation := by
  exact milp_feasible_set_subset_lp_relaxation_feasible_set
    P.integerMatrix P.continuousMatrix P.rhs

/-- Every feasible point of `P` lies in the canonical mixed-integer lattice `ℤ^n × ℝ^p`. -/
theorem feasibleSet_subset_mixed_integer_lattice
    (P : MixedIntegerLinearProgram m n p) :
    P.feasibleSet ⊆ (ℤ^n×ℝ^p) := by
  exact milp_feasible_set_subset_mixed_integer_lattice
    P.integerMatrix P.continuousMatrix P.rhs

/-- Unfolding equation for the objective function of `P`. -/
theorem objectiveValue_def
    (P : MixedIntegerLinearProgram m n p)
    (xy : MixedRealPoint n p) :
    P.objectiveValue xy =
      P.integerObjective ⬝ᵥ xy.1 + P.continuousObjective ⬝ᵥ xy.2 := by
  simpa [objectiveValue] using
    mixed_linear_objective_def P.integerObjective P.continuousObjective xy

/-- Membership in `P.objectiveValues` means that the value is attained at some feasible point. -/
theorem mem_objectiveValues_iff
    (P : MixedIntegerLinearProgram m n p)
    (z : ℝ) :
    z ∈ P.objectiveValues ↔ ∃ xy ∈ P.feasibleSet, P.objectiveValue xy = z :=
  Iff.rfl

end MixedIntegerLinearProgram

end Definition12

end

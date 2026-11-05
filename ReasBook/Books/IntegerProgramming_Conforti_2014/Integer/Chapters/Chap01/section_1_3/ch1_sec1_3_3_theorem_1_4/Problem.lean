/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.YesSet
public import Mathlib.Computability.RE
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Basic

@[expose] public section

-- The namespace of coded instances of quadratically constrained integer feasibility.
namespace QuadraticIntegerFeasibility

/-- A coded linear monomial consists of a variable index together with its integer coefficient. -/
structure LinearTerm where
  index : ℕ
  coefficient : ℤ

namespace LinearTerm

/-- Build a coded linear monomial from its variable index and coefficient. -/
def ofData (index : ℕ) (coefficient : ℤ) : LinearTerm where
  index := index
  coefficient := coefficient

/-- The variable index of `LinearTerm.ofData index coefficient` is `index`. -/
theorem ofData_index (index : ℕ) (coefficient : ℤ) :
    (ofData index coefficient).index = index :=
  rfl

/-- The coefficient of `LinearTerm.ofData index coefficient` is `coefficient`. -/
theorem ofData_coefficient (index : ℕ) (coefficient : ℤ) :
    (ofData index coefficient).coefficient = coefficient :=
  rfl

instance : Primcodable LinearTerm :=
  Primcodable.ofEquiv (ℕ × ℤ)
    { toFun := fun term ↦ (term.index, term.coefficient)
      invFun := fun data ↦
        match data with
        | (index, coefficient) => ofData index coefficient
      left_inv := by
        intro term
        cases term
        rfl
      right_inv := by
        intro data
        cases data
        rfl }

end LinearTerm

/-- A coded quadratic monomial consists of two variable indices together with their integer
coefficient. -/
structure QuadraticTerm where
  leftIndex : ℕ
  rightIndex : ℕ
  coefficient : ℤ

namespace QuadraticTerm

/-- Build a coded quadratic monomial from its two variable indices and coefficient. -/
def ofData (leftIndex rightIndex : ℕ) (coefficient : ℤ) : QuadraticTerm where
  leftIndex := leftIndex
  rightIndex := rightIndex
  coefficient := coefficient

/-- The left variable index of `QuadraticTerm.ofData i j coefficient` is `i`. -/
theorem ofData_leftIndex (i j : ℕ) (coefficient : ℤ) :
    (ofData i j coefficient).leftIndex = i :=
  rfl

/-- The right variable index of `QuadraticTerm.ofData i j coefficient` is `j`. -/
theorem ofData_rightIndex (i j : ℕ) (coefficient : ℤ) :
    (ofData i j coefficient).rightIndex = j :=
  rfl

/-- The coefficient of `QuadraticTerm.ofData i j coefficient` is `coefficient`. -/
theorem ofData_coefficient (i j : ℕ) (coefficient : ℤ) :
    (ofData i j coefficient).coefficient = coefficient :=
  rfl

instance : Primcodable QuadraticTerm :=
  Primcodable.ofEquiv (ℕ × ℕ × ℤ)
    { toFun := fun term ↦ (term.leftIndex, term.rightIndex, term.coefficient)
      invFun := fun data ↦
        match data with
        | (leftIndex, rightIndex, coefficient) => ofData leftIndex rightIndex coefficient
      left_inv := by
        intro term
        cases term
        rfl
      right_inv := by
        intro data
        cases data
        rfl }

end QuadraticTerm

/-- A quadratic inequality over `x₁, ..., xₙ` is coded by an integer constant term, a finite list
of linear monomials with integer coefficients, and a finite list of quadratic monomials with
integer coefficients. -/
structure Constraint where
  constant : ℤ
  linearTerms : List LinearTerm
  quadraticTerms : List QuadraticTerm

namespace Constraint

/-- Build a coded quadratic inequality from its constant, linear terms, and quadratic terms. -/
def ofData (constant : ℤ) (linearTerms : List LinearTerm)
    (quadraticTerms : List QuadraticTerm) : Constraint where
  constant := constant
  linearTerms := linearTerms
  quadraticTerms := quadraticTerms

/-- The constant term of `Constraint.ofData constant linearTerms quadraticTerms` is `constant`. -/
theorem ofData_constant (constant : ℤ) (linearTerms : List LinearTerm)
    (quadraticTerms : List QuadraticTerm) :
    (ofData constant linearTerms quadraticTerms).constant = constant :=
  rfl

/-- The linear terms of `Constraint.ofData constant linearTerms quadraticTerms` are
`linearTerms`. -/
theorem ofData_linearTerms (constant : ℤ) (linearTerms : List LinearTerm)
    (quadraticTerms : List QuadraticTerm) :
    (ofData constant linearTerms quadraticTerms).linearTerms = linearTerms :=
  rfl

/-- The quadratic terms of `Constraint.ofData constant linearTerms quadraticTerms` are
`quadraticTerms`. -/
theorem ofData_quadraticTerms (constant : ℤ) (linearTerms : List LinearTerm)
    (quadraticTerms : List QuadraticTerm) :
    (ofData constant linearTerms quadraticTerms).quadraticTerms = quadraticTerms :=
  rfl

/-- The canonical `Primcodable` instance for coded quadratic inequalities. -/
instance : Primcodable Constraint :=
  Primcodable.ofEquiv (ℤ × (List LinearTerm × List QuadraticTerm))
    { toFun := fun constraint ↦
        (constraint.constant, (constraint.linearTerms, constraint.quadraticTerms))
      invFun := fun data ↦
        match data with
        | (constant, (linearTerms, quadraticTerms)) =>
            ofData constant linearTerms quadraticTerms
      left_inv := by
        intro constraint
        cases constraint
        rfl
      right_inv := by
        intro data
        cases data
        rfl }

end Constraint

/-- A coded quadratically constrained integer feasibility instance consists of a declared number of
variables together with a finite list of quadratic inequalities in those variables. -/
structure Code where
  variableCount : ℕ
  constraints : List Constraint

namespace Code

/-- Build a coded quadratically constrained integer feasibility instance from its declared number of
variables and finite list of quadratic inequalities. -/
def ofData (variableCount : ℕ) (constraints : List Constraint) : Code where
  variableCount := variableCount
  constraints := constraints

/-- The declared variable count of `Code.ofData variableCount constraints` is `variableCount`. -/
theorem ofData_variableCount (variableCount : ℕ) (constraints : List Constraint) :
    (ofData variableCount constraints).variableCount = variableCount :=
  rfl

/-- The coded quadratic inequalities of `Code.ofData variableCount constraints` are
`constraints`. -/
theorem ofData_constraints (variableCount : ℕ) (constraints : List Constraint) :
    (ofData variableCount constraints).constraints = constraints :=
  rfl

/-- The canonical `Primcodable` instance for coded quadratic integer feasibility instances. -/
instance : Primcodable Code :=
  Primcodable.ofEquiv (ℕ × List Constraint)
    { toFun := fun code ↦ (code.variableCount, code.constraints)
      invFun := fun data ↦
        match data with
        | (variableCount, constraints) => ofData variableCount constraints
      left_inv := by
        intro code
        cases code
        rfl
      right_inv := by
        intro data
        cases data
        rfl }

end Code

/-- The encoding size of a coded quadratically constrained integer feasibility instance is the
binary length of the declared variable count together with the entrywise encoding contribution of
every constant term, variable index, and coefficient appearing in the listed inequalities. -/
def encodingSize (code : Code) : ℕ :=
  Nat.size code.variableCount +
    code.constraints.foldl
      (fun acc constraint ↦
        acc + EncodingSize.integer constraint.constant +
          constraint.linearTerms.foldl
            (fun termAcc term ↦
              termAcc + Nat.size term.index + EncodingSize.integer term.coefficient)
            0 +
          constraint.quadraticTerms.foldl
            (fun termAcc term ↦
              termAcc + Nat.size term.leftIndex + Nat.size term.rightIndex +
                EncodingSize.integer term.coefficient)
            0)
      0

/-- Expanding `encodingSize` yields the declared variable-count contribution together with the
entrywise encoding contributions of the listed linear and quadratic monomials. -/
theorem encodingSize_eq (code : Code) :
    encodingSize code =
      Nat.size code.variableCount +
        code.constraints.foldl
          (fun acc constraint ↦
            acc + EncodingSize.integer constraint.constant +
              constraint.linearTerms.foldl
                (fun termAcc term ↦
                  termAcc + Nat.size term.index + EncodingSize.integer term.coefficient)
                0 +
              constraint.quadraticTerms.foldl
                (fun termAcc term ↦
                  termAcc + Nat.size term.leftIndex + Nat.size term.rightIndex +
                    EncodingSize.integer term.coefficient)
                0)
          0 :=
  rfl

/-- Evaluate one coded quadratic inequality on an integral assignment. -/
def evalConstraint (constraint : Constraint) (assignment : List ℤ) : ℤ :=
  constraint.constant +
    constraint.linearTerms.foldl
      (fun acc term ↦ acc + term.coefficient * assignment.getD term.index 0)
      0 +
    constraint.quadraticTerms.foldl
      (fun acc term ↦
        acc + term.coefficient * assignment.getD term.leftIndex 0 *
          assignment.getD term.rightIndex 0)
      0

/-- Expanding `evalConstraint` adds the constant, linear, and quadratic contributions of the coded
inequality. -/
theorem evalConstraint_def (constraint : Constraint) (assignment : List ℤ) :
    evalConstraint constraint assignment =
      constraint.constant +
        constraint.linearTerms.foldl
          (fun acc term ↦ acc + term.coefficient * assignment.getD term.index 0)
          0 +
        constraint.quadraticTerms.foldl
          (fun acc term ↦
            acc + term.coefficient * assignment.getD term.leftIndex 0 *
              assignment.getD term.rightIndex 0)
          0 :=
  rfl

/-- A coded system is well formed when it contains at least one quadratic inequality; the variable
bound side conditions are expressed by requiring every coded variable index to lie in
`x₁, ..., xₙ`. -/
def wellFormed (code : Code) : Prop :=
  0 < code.variableCount ∧
    code.constraints ≠ [] ∧
    (∀ constraint ∈ code.constraints,
      ∀ term ∈ constraint.linearTerms, term.index < code.variableCount) ∧
    (∀ constraint ∈ code.constraints,
      ∀ term ∈ constraint.quadraticTerms,
        term.leftIndex < code.variableCount ∧ term.rightIndex < code.variableCount)

/-- Expanding `wellFormed` recovers the source side condition that the finite family of quadratic
inequalities is nonempty, the variable count is positive, and every coded variable index lies in
the declared range. -/
theorem wellFormed_iff (code : Code) :
    wellFormed code ↔
      0 < code.variableCount ∧
        code.constraints ≠ [] ∧
        (∀ constraint ∈ code.constraints,
          ∀ term ∈ constraint.linearTerms, term.index < code.variableCount) ∧
        (∀ constraint ∈ code.constraints,
          ∀ term ∈ constraint.quadraticTerms,
            term.leftIndex < code.variableCount ∧ term.rightIndex < code.variableCount) :=
  Iff.rfl

/-- A coded quadratically constrained integer feasibility instance has a solution when it is well
formed and admits an integral assignment of the declared length satisfying every coded quadratic
inequality. -/
def hasSolution (code : Code) : Prop :=
  wellFormed code ∧
    ∃ assignment : List ℤ,
      assignment.length = code.variableCount ∧
      ∀ constraint ∈ code.constraints, evalConstraint constraint assignment ≤ 0

/-- Expanding `hasSolution` recovers the textbook yes-predicate: a nonempty finite family of
quadratic inequalities in `n ≥ 1` variables together with an integral assignment in `ℤ^n`
satisfying all of them. -/
theorem hasSolution_iff (code : Code) :
    hasSolution code ↔
      0 < code.variableCount ∧
        code.constraints ≠ [] ∧
        (∀ constraint ∈ code.constraints,
          ∀ term ∈ constraint.linearTerms, term.index < code.variableCount) ∧
        (∀ constraint ∈ code.constraints,
          ∀ term ∈ constraint.quadraticTerms,
            term.leftIndex < code.variableCount ∧ term.rightIndex < code.variableCount) ∧
        ∃ assignment : List ℤ,
          assignment.length = code.variableCount ∧
          ∀ constraint ∈ code.constraints, evalConstraint constraint assignment ≤ 0 := by
  rw [hasSolution, wellFormed_iff]
  simp [and_assoc]

/-- The canonical decision problem asking whether a coded finite nonempty system of quadratic
integer inequalities admits an integral solution. -/
noncomputable def decisionProblem : DecisionProblem :=
  DecisionProblem.ofYesSet encodingSize { code | hasSolution code }

/-- The canonical coding on `decisionProblem.Instance` is inherited from `Code`. -/
instance : Primcodable decisionProblem.Instance := by
  change Primcodable Code
  infer_instance

/-- The Boolean answer of `decisionProblem` is `true` exactly for the solvable coded systems of
quadratic integer inequalities. -/
theorem decisionProblem_answer_eq_true_iff (code : Code) :
    decisionProblem.answer code = true ↔ hasSolution code := by
  simp [decisionProblem]

end QuadraticIntegerFeasibility

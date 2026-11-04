/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Init

@[expose] public section

/-- A decision problem consists of its instance type, an encoding-size function on instances, and
the correct Boolean answer for each instance. -/
structure DecisionProblem where
  Instance : Type
  encodingSize : Instance → Nat
  answer : Instance → Bool

/-- A computational problem consists of its instance type, an encoding-size function on instances,
a family of admissible solutions, an encoding size for each solution, and the assumption that each
instance admits at least one solution. -/
structure ComputationalProblem where
  Instance : Type
  encodingSize : Instance → Nat
  Solution : Instance → Type
  solutionEncodingSize : (i : Instance) → Solution i → Nat
  solutionExists : ∀ i : Instance, Nonempty (Solution i)

namespace DecisionProblem

/-- View a decision problem as a computational problem whose solutions are correct Boolean answers.
-/
def toProblem (D : DecisionProblem) : ComputationalProblem where
  Instance := D.Instance
  encodingSize := D.encodingSize
  Solution := fun i ↦ { b : Bool // b = D.answer i }
  solutionEncodingSize := fun _ _ ↦ (1 : Nat)
  solutionExists := fun i ↦ ⟨⟨D.answer i, rfl⟩⟩

/-- Any solution of `D.toProblem` carries the correct Boolean answer for the underlying instance.
-/
theorem toProblem_solution_value
    (D : DecisionProblem)
    (i : D.Instance)
    (s : D.toProblem.Solution i) :
    s.1 = D.answer i := by
  -- The subtype witness stored in `s` records exactly the required equality.
  exact s.2

end DecisionProblem

namespace ComputationalProblem

/-- The type of an instance of `Q` paired with one of its solutions. -/
def solutionInput (Q : ComputationalProblem) : Type :=
  Sigma Q.Solution

/-- The encoding size of an instance of `Q` together with one of its solutions. -/
def solutionInputEncodingSize (Q : ComputationalProblem) : Q.solutionInput → Nat
  | ⟨i, s⟩ => Q.encodingSize i + Q.solutionEncodingSize i s

/-- Expanding `Q.solutionInputEncodingSize` on a concrete pair adds the instance size and the
solution size. -/
theorem solutionInputEncodingSize_mk
    (Q : ComputationalProblem)
    (i : Q.Instance)
    (s : Q.Solution i) :
    Q.solutionInputEncodingSize ⟨i, s⟩ = Q.encodingSize i + Q.solutionEncodingSize i s := by
  -- This is the defining computation rule for `solutionInputEncodingSize`.
  rfl

end ComputationalProblem

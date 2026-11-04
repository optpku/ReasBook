/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_19.Problem
import Mathlib.Data.Set.Defs
import Mathlib.Data.Matrix.Mul

open scoped BigOperators Matrix

/-- A binary integer linear feasibility instance consists of an integer matrix together with an
integer right-hand side vector. -/
structure ZeroOneILPInstance where
  m : ℕ
  n : ℕ
  matrix : Matrix (Fin m) (Fin n) ℤ
  rhs : Fin m → ℤ

namespace ZeroOneILPInstance

/-- Build a binary integer linear feasibility instance from its coefficient matrix and right-hand
side vector. -/
def ofSystem {m n : ℕ} (matrix : Matrix (Fin m) (Fin n) ℤ) (rhs : Fin m → ℤ) :
    ZeroOneILPInstance where
  m := m
  n := n
  matrix := matrix
  rhs := rhs

/-- The coefficient matrix of `ZeroOneILPInstance.ofSystem matrix rhs` is `matrix`. -/
theorem ofSystem_matrix {m n : ℕ} (matrix : Matrix (Fin m) (Fin n) ℤ) (rhs : Fin m → ℤ) :
    (ZeroOneILPInstance.ofSystem matrix rhs).matrix = matrix :=
  rfl

/-- The right-hand side vector of `ZeroOneILPInstance.ofSystem matrix rhs` is `rhs`. -/
theorem ofSystem_rhs {m n : ℕ} (matrix : Matrix (Fin m) (Fin n) ℤ) (rhs : Fin m → ℤ) :
    (ZeroOneILPInstance.ofSystem matrix rhs).rhs = rhs :=
  rfl

/-- The encoding size of a binary integer linear feasibility instance is the sum of the encoding
sizes of its matrix rows and its right-hand side vector. -/
def encodingSize (I : ZeroOneILPInstance) : ℕ :=
  (∑ i, EncodingSize.integerVector (I.matrix i)) + EncodingSize.integerVector I.rhs

/-- Expanding `I.encodingSize` gives the rowwise matrix contribution plus the right-hand side
contribution. -/
theorem encodingSize_eq (I : ZeroOneILPInstance) :
    I.encodingSize =
      (∑ i, EncodingSize.integerVector (I.matrix i)) + EncodingSize.integerVector I.rhs :=
  rfl

/-- A binary integer linear feasibility instance is feasible when some binary vector satisfies the
system `I.matrix *ᵥ x ≤ I.rhs`. -/
def hasFeasibleAssignment (I : ZeroOneILPInstance) : Prop :=
  ∃ β : Fin I.n → Bool, ∀ i, (I.matrix *ᵥ (fun j ↦ if β j then 1 else 0)) i ≤ I.rhs i

/-- The feasible set of a binary integer linear system consists of its binary integer vectors
satisfying `I.matrix *ᵥ x ≤ I.rhs`. -/
def feasibleSet (I : ZeroOneILPInstance) : Set (Fin I.n → ℤ) :=
  {x | (∀ j, x j = 0 ∨ x j = 1) ∧ I.matrix *ᵥ x ≤ I.rhs}

/-- Membership in `I.feasibleSet` is exactly the source binary-system feasibility condition. -/
theorem mem_feasibleSet_iff (I : ZeroOneILPInstance) (x : Fin I.n → ℤ) :
    x ∈ I.feasibleSet ↔
      (∀ j, x j = 0 ∨ x j = 1) ∧ I.matrix *ᵥ x ≤ I.rhs :=
  Iff.rfl

/-- Expanding `I.hasFeasibleAssignment` recovers the textbook existential over an integer vector
whose coordinates are all `0` or `1`. -/
theorem hasFeasibleAssignment_iff_exists_binaryIntVector (I : ZeroOneILPInstance) :
    I.hasFeasibleAssignment ↔
      ∃ x : Fin I.n → ℤ, (∀ j, x j = 0 ∨ x j = 1) ∧ I.matrix *ᵥ x ≤ I.rhs := by
  constructor
  · rintro ⟨β, hβ⟩
    -- Translate the Boolean witness into its canonical `0/1` integer vector.
    refine ⟨fun j ↦ if β j then 1 else 0, ?_, ?_⟩
    · intro j
      by_cases h : β j
      · right
        simp [h]
      · left
        simp [h]
    · -- The feasibility inequality is exactly the one stored in the Boolean witness.
      simpa using hβ
  · rintro ⟨x, hxBinary, hxFeasible⟩
    let β : Fin I.n → Bool := fun j ↦ if x j = 1 then true else false
    refine ⟨β, ?_⟩
    intro i
    have hxAsBool : (fun j ↦ if β j then 1 else 0) = x := by
      -- Binary coordinates let us recover `x` from the Boolean assignment `β`.
      funext j
      dsimp [β]
      rcases hxBinary j with h0 | h1
      · simp [h0]
      · simp [h1]
    -- Rewrite the translated `0/1` vector back to the original feasible witness.
    rw [hxAsBool]
    exact hxFeasible i

/-- A binary integer linear system is feasible exactly when its canonical feasible set is
nonempty. -/
theorem hasFeasibleAssignment_iff_exists_mem_feasibleSet (I : ZeroOneILPInstance) :
    I.hasFeasibleAssignment ↔ ∃ x : Fin I.n → ℤ, x ∈ I.feasibleSet := by
  simpa [feasibleSet] using I.hasFeasibleAssignment_iff_exists_binaryIntVector

/-- The canonical decision problem attached to binary integer linear feasibility uses instances
`ZeroOneILPInstance`, the encoding size `ZeroOneILPInstance.encodingSize`, and the Boolean answer
obtained from decidable feasibility. -/
noncomputable def decisionProblem : DecisionProblem where
  Instance := ZeroOneILPInstance
  encodingSize := ZeroOneILPInstance.encodingSize
  answer := fun I ↦ by
    classical
    exact decide I.hasFeasibleAssignment

/-- The Boolean answer of `ZeroOneILPInstance.decisionProblem` is true exactly when the underlying
binary integer linear system has a feasible `0/1` solution. -/
theorem decisionProblem_answer_eq_true_iff (I : ZeroOneILPInstance) :
    ZeroOneILPInstance.decisionProblem.answer I = true ↔ I.hasFeasibleAssignment := by
  classical
  -- Unfold the decision-problem answer to the Boolean `decide` of feasibility.
  simp [decisionProblem]

end ZeroOneILPInstance

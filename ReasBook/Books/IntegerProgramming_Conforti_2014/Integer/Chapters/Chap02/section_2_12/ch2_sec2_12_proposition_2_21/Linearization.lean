/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_12.ch2_sec2_12_definition_2_51.Problem

namespace ZeroOnePolynomialProgram

variable {m n : ℕ}

/-- A pure `0`--`1` linear reformulation of a `0`--`1` polynomial program `P`, with finitely many
additional binary variables and linear constraints. -/
structure PureLinearization (P : ZeroOnePolynomialProgram m n) where
  vars : ℕ
  constraints : ℕ
  program : MixedIntegerLinearProgram constraints vars 0
  isMixedZeroOne : program.IsMixedZeroOne
  xEmbedding : Fin n ↪ Fin vars
  ofOriginal :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ P.feasibleSet →
      ∃ z : Fin vars → ℝ,
        (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ program.mixedZeroOneFeasibleSet ∧
          (∀ i : Fin n, z (xEmbedding i) = x i) ∧
          program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) = P.objectiveValue x
  toOriginal :
    ∀ ⦃z : Fin vars → ℝ⦄,
      (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ program.mixedZeroOneFeasibleSet →
        let x : Fin n → ℝ := fun i ↦ z (xEmbedding i)
        x ∈ P.feasibleSet ∧
          P.objectiveValue x = program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i)

namespace PureLinearization

variable {P : ZeroOnePolynomialProgram m n}

/-- The feasible vectors of `L` viewed on the pure binary block alone. -/
def feasibleSet
    (L : PureLinearization P) : Set (Fin L.vars → ℝ) :=
  {z | (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ L.program.mixedZeroOneFeasibleSet}

/-- The objective value of the reformulated pure `0`--`1` linear program on a binary vector
`z`. -/
def objectiveValue
    (L : PureLinearization P)
    (z : Fin L.vars → ℝ) : ℝ :=
  L.program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i)

/-- The set of objective values attained by feasible vectors of the reformulation `L`. -/
def objectiveValues
    (L : PureLinearization P) : Set ℝ :=
  L.objectiveValue '' L.feasibleSet

/-- Membership in `L.feasibleSet` is exactly membership in the underlying pure-binary feasible
set of `L.program` with empty continuous block. -/
theorem mem_feasibleSet_iff
    (L : PureLinearization P)
    (z : Fin L.vars → ℝ) :
    z ∈ L.feasibleSet ↔
      (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ L.program.mixedZeroOneFeasibleSet := by
  -- Unfold the wrapper feasible set to expose its underlying pure-binary membership condition.
  rfl

/-- Unfolding equation for the objective value of the reformulation `L` on a pure binary vector
`z`. -/
theorem objectiveValue_def
    (L : PureLinearization P)
    (z : Fin L.vars → ℝ) :
    L.objectiveValue z =
      L.program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) := by
  -- Unfold the wrapper objective to recover the objective of the underlying linear program.
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_12/ch2_sec2_12_proposition_2_21/Linearization.lean.
The reformulation `L` preserves the set of attained objective values of the original polynomial
program `P`. -/
theorem objectiveValues_eq
    (L : PureLinearization P) :
    P.objectiveValues = L.objectiveValues := by
  -- Compare membership at an arbitrary value and transport its feasible witness in each direction.
  ext r
  constructor
  · intro hr
    rcases mem_objectiveValues_iff.mp hr with ⟨x, hx, hvalue⟩
    rcases L.ofOriginal hx with ⟨z, hz, -, hbridge⟩
    rw [objectiveValues]
    refine ⟨z, (L.mem_feasibleSet_iff z).mpr hz, ?_⟩
    -- The forward bridge identifies the reformulated objective with the original value.
    calc
      L.objectiveValue z =
          L.program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) :=
        L.objectiveValue_def z
      _ = P.objectiveValue x := hbridge
      _ = r := hvalue
  · intro hr
    rw [objectiveValues] at hr
    rcases hr with ⟨z, hz, hvalue⟩
    rcases L.toOriginal ((L.mem_feasibleSet_iff z).mp hz) with ⟨hx, hbridge⟩
    refine mem_objectiveValues_iff.mpr ⟨fun i ↦ z (L.xEmbedding i), hx, ?_⟩
    -- The backward bridge recovers the original objective and then the attained target value.
    calc
      P.objectiveValue (fun i ↦ z (L.xEmbedding i)) =
          L.program.objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) := hbridge
      _ = L.objectiveValue z := (L.objectiveValue_def z).symm
      _ = r := hvalue

#print axioms objectiveValues_eq

end PureLinearization

end ZeroOnePolynomialProgram

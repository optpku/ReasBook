/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_definition_2_29.SAT

namespace SAT.Clause

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14/Clause.lean: on a binary
integer vector, the clause objective is bounded below by `-(C.negativeCount : ℤ)`. -/
theorem objectiveGeNegNegativeCountOfBinary
    {n : ℕ} (C : SAT.Clause n) {x : Fin n → ℤ}
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    -(C.negativeCount : ℤ) ≤ C.objective x := by
  -- Shift the objective by the negative-literal count and use nonnegativity of every slack.
  rw [neg_le_iff_add_nonneg, objective_add_negativeCount_eq_sumLiteralSlack]
  exact Finset.sum_nonneg fun l _hl ↦ literalSlack_nonneg_of_binary hx l

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14/Clause.lean: on a binary
integer vector, strict violation of the clause inequality is equivalent to falsifying the clause. -/
theorem objectiveLtRhsIffFalsifiedByOfBinary
    {n : ℕ} (C : SAT.Clause n) {x : Fin n → ℤ}
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    C.objective x < 1 - (C.negativeCount : ℤ) ↔ C.falsifiedBy x := by
  constructor
  · intro hlt
    -- Integer discreteness turns strict violation into the matching upper bound.
    have hupper : C.objective x ≤ -(C.negativeCount : ℤ) := by
      rw [← Int.lt_add_one_iff]
      simpa [sub_eq_add_neg, add_comm] using hlt
    -- The global lower bound therefore forces the objective to attain its falsifying minimum.
    have heq : C.objective x = -(C.negativeCount : ℤ) :=
      le_antisymm hupper (objectiveGeNegNegativeCountOfBinary C hx)
    exact (C.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary hx).mp heq
  · intro hfalsified
    -- Falsification attains the minimum, which lies strictly below its integer successor.
    have heq : C.objective x = -(C.negativeCount : ℤ) :=
      (C.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary hx).mpr hfalsified
    rw [heq, sub_eq_add_neg, add_comm]
    exact Int.lt_add_one_iff.mpr (le_refl (-(C.negativeCount : ℤ)))

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_5/ch2_sec2_5_proposition_2_14/Clause.lean. A Boolean assignment
fails to satisfy a clause exactly when its canonical `0/1` integer encoding strictly violates the
clause inequality. -/
theorem notSatisfiedByIffObjectiveLtRhsOfBoolVector
    {n : ℕ} (C : SAT.Clause n) (τ : Fin n → Bool) :
    ¬ C.satisfiedBy τ ↔
      C.objective (fun j ↦ if τ j then 1 else 0) < 1 - (C.negativeCount : ℤ) := by
  -- The canonical integer encoding has binary coordinates.
  have hbinary : ∀ j, (if τ j then (1 : ℤ) else 0) = 0 ∨
      (if τ j then (1 : ℤ) else 0) = 1 := by
    intro j
    cases τ j <;> simp
  -- Literal non-satisfaction is exactly the corresponding encoded falsity condition.
  have hliteral (l : SAT.Literal n) :
      ¬ l.satisfiedBy τ ↔
        match l with
        | .pos j => (if τ j then (1 : ℤ) else 0) = 0
        | .neg j => (if τ j then (1 : ℤ) else 0) = 1 := by
    cases l with
    | pos j =>
        cases hτ : τ j <;> simp [SAT.Literal.satisfiedBy, hτ]
    | neg j =>
        cases hτ : τ j <;> simp [SAT.Literal.satisfiedBy, hτ]
  -- Rewrite strict violation as falsification and compare the two literalwise predicates.
  rw [objectiveLtRhsIffFalsifiedByOfBinary C hbinary,
    satisfiedBy_iff_exists_mem, falsifiedBy_iff]
  constructor
  · intro hnot l hl
    exact (hliteral l).mp fun hsatisfied ↦ hnot ⟨l, hl, hsatisfied⟩
  · intro hall hsatisfied
    obtain ⟨l, hl, hlSatisfied⟩ := hsatisfied
    exact (hliteral l).mpr (hall l hl) hlSatisfied

end SAT.Clause

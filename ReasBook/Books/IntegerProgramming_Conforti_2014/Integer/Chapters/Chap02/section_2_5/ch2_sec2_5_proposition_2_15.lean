/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Order.Bounds.Defs
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_5.ch2_sec2_5_proposition_2_15.Program

namespace InferenceIP

/-- Proposition 2.15. For the inference `0/1` integer program attached to the clause matrix `A`,
there exists a feasible binary vector that falsifies `C` if and only if the least attained clause
objective value on `objectiveValues A C` is `-(C.negativeCount : ℤ)`. -/
theorem exists_falsifying_feasible_iff_isLeast_objectiveValues
    {m n : ℕ}
    (A : SAT.ClauseMatrix m n)
    (C : SAT.Clause n) :
    (∃ x : Fin n → ℤ,
      x ∈ feasibleSet A ∧ C.falsifiedBy x) ↔
      IsLeast (objectiveValues A C) (-(C.negativeCount : ℤ)) := by
  -- The clause objective is bounded below by `-(C.negativeCount : ℤ)` on every binary vector.
  have objective_ge_neg_negativeCount_of_binary :
      ∀ {x : Fin n → ℤ}, (∀ j, x j = 0 ∨ x j = 1) → -(C.negativeCount : ℤ) ≤ C.objective x := by
    intro x hxBinary
    -- Rewrite the shifted objective as a sum of nonnegative literal slack terms.
    have hsum_nonneg : 0 ≤ Finset.sum C (SAT.Clause.literalSlack x) := by
      exact Finset.sum_nonneg fun l _hl ↦ SAT.Clause.literalSlack_nonneg_of_binary hxBinary l
    have hobjective_nonneg : 0 ≤ C.objective x + (C.negativeCount : ℤ) := by
      rw [SAT.Clause.objective_add_negativeCount_eq_sumLiteralSlack C x]
      exact hsum_nonneg
    exact (neg_le_iff_add_nonneg).2 hobjective_nonneg
  -- Package the pointwise lower bound at the attained-value-set level for the `IsLeast` proof.
  have objectiveValues_lowerBound :
      ∀ {r : ℤ}, r ∈ objectiveValues A C → -(C.negativeCount : ℤ) ≤ r := by
    intro r hr
    rcases mem_objectiveValues_iff.mp hr with ⟨x, hx, rfl⟩
    exact objective_ge_neg_negativeCount_of_binary (feasible_binary hx)
  constructor
  · rintro ⟨x, hx, hfalse⟩
    have hxBinary : ∀ j, x j = 0 ∨ x j = 1 := feasible_binary hx
    -- A feasible falsifying vector attains the binary minimum objective value exactly.
    have hobjective : C.objective x = -(C.negativeCount : ℤ) := by
      exact (SAT.Clause.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary C hxBinary).2
        hfalse
    refine ⟨mem_objectiveValues_iff.mpr ⟨x, hx, hobjective⟩, ?_⟩
    intro r hr
    exact objectiveValues_lowerBound hr
  · rintro ⟨hrmin, _⟩
    rcases mem_objectiveValues_iff.mp hrmin with ⟨x, hx, hobjective⟩
    have hxBinary : ∀ j, x j = 0 ∨ x j = 1 := feasible_binary hx
    -- Attaining the minimum objective forces every clause literal to be falsified.
    have hfalse : C.falsifiedBy x := by
      exact (SAT.Clause.objective_eq_neg_negativeCount_iff_falsifiedBy_of_binary C hxBinary).1
        hobjective
    exact ⟨x, hx, hfalse⟩

end InferenceIP

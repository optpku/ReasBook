/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_zero_one

/-- Definition 2.62, supporting remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_62/ZeroOneSet.lean`:
the `0`--`1` set `{x | is_zero_one_vector x ∧ A.mulVec x ≤ b}` cut out by real matrix data
`A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`. -/
def zeroOneSet
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | is_zero_one_vector x ∧ A.mulVec x ≤ b}

/-- A point belongs to `zeroOneSet A b` exactly when it is binary and satisfies `A x ≤ b`. -/
theorem mem_zeroOneSet_iff
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {x : Fin n → ℝ} :
    x ∈ zeroOneSet A b ↔ is_zero_one_vector x ∧ A.mulVec x ≤ b := by
  -- Membership unfolds directly to the defining binary and inequality conditions.
  rfl

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_62/ZeroOneSet.lean

Membership in `zeroOneSet A b` is equivalent to membership in the mixed `0,1` linear set with
empty continuous block. -/
theorem mem_zeroOneSet_iff_mem_mixedZeroOneLinearSet
    {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {x : Fin n → ℝ} :
    x ∈ zeroOneSet A b ↔
      (x, fun i ↦ Fin.elim0 i) ∈ mixedZeroOneLinearSet A (0 : Matrix (Fin m) (Fin 0) ℝ) b := by
  -- Expose both membership predicates before eliminating the empty continuous block.
  rw [mem_zeroOneSet_iff, mem_mixedZeroOneLinearSet_iff]
  constructor
  · rintro ⟨hx, hA⟩
    -- Reorder the conditions and normalize the zero matrix contribution.
    refine ⟨?_, is_zero_one_vector_iff.mp hx, ?_⟩
    · simpa only [Matrix.zero_mulVec, add_zero] using hA
    · -- Nonnegativity is vacuous because the continuous coordinate type is empty.
      intro i
      exact Fin.elim0 i
  · rintro ⟨hA, hx, -⟩
    -- Reassemble binary feasibility after deleting the empty continuous block.
    refine ⟨is_zero_one_vector_iff.mpr hx, ?_⟩
    simpa only [Matrix.zero_mulVec, add_zero] using hA

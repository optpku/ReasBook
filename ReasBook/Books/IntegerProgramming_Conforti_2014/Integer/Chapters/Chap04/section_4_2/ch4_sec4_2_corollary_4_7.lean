/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_6
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_definition_4_2_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 4.7 is source-facing row-bicoloring language built on the Chapter 4.2 row-view bridge
owner.
-/

section Corollary47

variable {m n : Type*}

/-- Helper for Corollary 4.7: a column bicoloring of the transpose submatrix is exactly a row
bicoloring of the original row submatrix. -/
lemma equitable_row_bicoloring_submatrix_transpose_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix m n ℤ) (row : ι ↪ m) (red blue : Finset ι) :
    is_equitable_bicoloring (A.transpose.submatrix id row) red blue ↔
      is_equitable_row_bicoloring (A.submatrix row id) red blue := by
  -- Reinterpret the transpose column-bicoloring predicate as the row-view predicate.
  rw [is_equitable_row_bicoloring, Matrix.transpose_submatrix]

/-- Corollary 4.7. A matrix `A` is totally unimodular if and only if every row submatrix of `A`
admits an equitable row-bicoloring. -/
theorem totally_unimodular_iff_every_row_submatrix_admits_equitable_row_bicoloring
    (A : Matrix m n ℤ) :
    A.IsTotallyUnimodular ↔
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (row : ι ↪ m),
        ∃ red blue : Finset ι,
          is_equitable_row_bicoloring (A.submatrix row id) red blue := by
  constructor
  · intro hA
    -- Apply Theorem 4.6 to `A.transpose`, whose columns are the rows of `A`.
    have hTranspose : A.transpose.IsTotallyUnimodular :=
      (Matrix.transpose_isTotallyUnimodular_iff A).2 hA
    intro ι _ _ row
    obtain ⟨red, blue, hColor⟩ :=
      (totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring A.transpose).1
        hTranspose row
    -- Convert the transpose-side witness back to the source row-bicoloring language.
    refine ⟨red, blue, ?_⟩
    exact (equitable_row_bicoloring_submatrix_transpose_iff A row red blue).1 hColor
  · intro hRow
    -- Prove total unimodularity of the transpose by supplying row-submatrix witnesses.
    have hTranspose : A.transpose.IsTotallyUnimodular := by
      refine
        (totally_unimodular_iff_every_column_submatrix_admits_equitable_bicoloring
          A.transpose).2 ?_
      intro ι _ _ row
      obtain ⟨red, blue, hColor⟩ := hRow row
      -- The given row-bicoloring of `A` is the needed column-bicoloring of `A.transpose`.
      refine ⟨red, blue, ?_⟩
      exact (equitable_row_bicoloring_submatrix_transpose_iff A row red blue).2 hColor
    exact (Matrix.transpose_isTotallyUnimodular_iff A).1 hTranspose

end Corollary47

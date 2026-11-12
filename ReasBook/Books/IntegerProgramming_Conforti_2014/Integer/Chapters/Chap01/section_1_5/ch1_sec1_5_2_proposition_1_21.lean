/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_lemma_1_3.RowOperations

@[expose] public section

namespace Matrix

section Proposition21

variable {n : ℕ}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_21.lean.
Proposition 1.21: if `U` is obtained from the identity matrix by a unimodular row operation, then
`U` is unimodular. -/
theorem isUnit_det_of_isElementaryUnimodularRowMatrix
    {U : Matrix (Fin n) (Fin n) ℤ}
    (hU : IsElementaryUnimodularRowMatrix U) :
    IsUnit U.det := by
  -- Decompose the elementary row operation into the three defining cases.
  rcases hU with ⟨i, j, hij, rfl⟩ | ⟨i, rfl⟩ | ⟨i, j, c, hij, rfl⟩
  · -- Normalize to the row-swap matrix and reuse its determinant-unit lemma.
    simpa using isUnit_det_rowSwapMatrix i j
  · -- Normalize to the row-negation matrix and reuse its determinant-unit lemma.
    simpa using isUnit_det_rowNegMatrix i
  · -- Normalize to the row-addition matrix and pass along the distinct-row hypothesis.
    simpa using isUnit_det_rowAddMatrix i j c hij

end Proposition21

end Matrix

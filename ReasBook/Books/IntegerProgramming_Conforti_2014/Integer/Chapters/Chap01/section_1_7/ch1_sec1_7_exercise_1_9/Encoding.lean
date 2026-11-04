/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_12

@[expose] public section

open scoped BigOperators

/-- A bit-length style encoding size for a rational matrix, obtained by summing the encoding sizes
of its rows. -/
def rational_matrix_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∑ i, EncodingSize.rationalVector (A i)

/-- A bit-length style encoding size for a rational linear system, obtained by adding the encoding
size of the coefficient matrix and that of the right-hand side vector. -/
def rational_linear_system_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : ℕ :=
  rational_matrix_encoding_size A + EncodingSize.rationalVector b

end

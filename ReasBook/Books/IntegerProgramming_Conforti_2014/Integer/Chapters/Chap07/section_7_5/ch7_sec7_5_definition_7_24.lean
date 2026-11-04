/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1.Encoding
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped Matrix

-- Owner reuse in this file:
-- * Chapter 1.3.1: `EncodingSize.rational`
-- * Chapter 3.5-extra-1 / 4.1: `is_rational_polyhedron`, `rational_matrix_polyhedron`,
--   `mem_rational_matrix_polyhedron`

section Definition724

variable {n L : ℕ} {P : Set (Fin n → ℝ)}

/-- Definition 7.24. A certificate that the polyhedron `P ⊆ ℝ^n` belongs to a well-described
family with input length `L`: one has `n ≤ L`, a rational matrix description `P = {x | A x ≤ b}`,
and a polynomial bound in `L` for the encoding size of every entry of `(A, b)`. -/
structure WellDescribedPolyhedron
    (P : Set (Fin n → ℝ))
    (L : ℕ) where
  /-- The ambient dimension is bounded by the input length. -/
  dimension_le_input_length : n ≤ L
  /-- The number of inequalities in the chosen rational presentation of `P`. -/
  rows : ℕ
  /-- The rational matrix in the inequality presentation of `P`. -/
  matrix : Matrix (Fin rows) (Fin n) ℚ
  /-- The rational right-hand side in the inequality presentation of `P`. -/
  rhs : Fin rows → ℚ
  /-- The chosen presentation defines `P`. -/
  eq_polyhedron : P = rational_matrix_polyhedron matrix rhs
  /-- The polynomial controlling the entrywise encoding size bound. -/
  encoding_bound_polynomial : Polynomial ℕ
  /-- Every coefficient of the defining matrix has encoding size polynomially bounded by `L`. -/
  matrix_entry_encoding_bound :
    ∀ i : Fin rows, ∀ j : Fin n,
      EncodingSize.rational (matrix i j) ≤ encoding_bound_polynomial.eval L
  /-- Every entry of the right-hand side vector has encoding size polynomially bounded by `L`. -/
  rhs_entry_encoding_bound :
    ∀ i : Fin rows, EncodingSize.rational (rhs i) ≤ encoding_bound_polynomial.eval L

namespace WellDescribedPolyhedron

/-- A well-described polyhedron is, in particular, a rational polyhedron in the Chapter 4.1
matrix-presentation sense. -/
theorem is_rational_polyhedron
    (hP : WellDescribedPolyhedron P L) :
    is_rational_polyhedron P :=
  is_rational_polyhedron_iff.mpr ⟨hP.rows, hP.matrix, hP.rhs, by
    simpa [rational_matrix_polyhedron] using hP.eq_polyhedron⟩

/-- Membership in a well-described polyhedron is membership in its chosen rational inequality
presentation. -/
theorem mem_iff
    (hP : WellDescribedPolyhedron P L)
    (x : Fin n → ℝ) :
    x ∈ P ↔
      (hP.matrix.map (Rat.castHom ℝ)) *ᵥ x ≤ fun i ↦ (hP.rhs i : ℝ) := by
  simpa [hP.eq_polyhedron] using mem_rational_matrix_polyhedron hP.matrix hP.rhs x

end WellDescribedPolyhedron

end Definition724

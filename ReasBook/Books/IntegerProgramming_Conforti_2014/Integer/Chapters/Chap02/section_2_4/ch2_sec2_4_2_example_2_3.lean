import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- direct local inspection of Mathlib's matrix API.

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_example_2_3.lean:
the maximal-clique versus node incidence matrix `A_c` displayed in Example 2.3. -/
def example_2_3_clique_matrix : Matrix (Fin 3) (Fin 5) ℚ :=
  !![(1 : ℚ), 1, 0, 0, 1;
    0, 1, 1, 1, 0;
    0, 1, 0, 1, 1]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_example_2_3.lean:
the fractional point `(0, 1/2, 1/2, 1/2, 0)` used in Example 2.3. -/
def example_2_3_fractional_point : Fin 5 → ℚ :=
  ![(0 : ℚ), 1 / 2, 1 / 2, 1 / 2, 0]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_example_2_3.lean:
the fractional point from Example 2.3 lies in the unit cube. -/
theorem example_2_3_fractional_point_mem_unit_cube :
    ∀ i, 0 ≤ example_2_3_fractional_point i ∧ example_2_3_fractional_point i ≤ 1 := by
  -- Enumerating the five coordinates reduces both bounds to rational arithmetic.
  intro i
  fin_cases i
  · norm_num [example_2_3_fractional_point]
  · norm_num [example_2_3_fractional_point]
  · norm_num [example_2_3_fractional_point]
  · norm_num [example_2_3_fractional_point]
  · norm_num [example_2_3_fractional_point]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_2_example_2_3.lean.
Example 2.3. For the maximal-clique incidence matrix `A_c` of Fig. 2.1, the point
`(0, 1/2, 1/2, 1/2, 0)` yields row values `(1/2, 3/2, 1)`, so the clique inequality
`x₂ + x₃ + x₄ ≤ 1` is violated. -/
theorem example_2_3_clique_matrix_mulVec_fractional_point :
    example_2_3_clique_matrix.mulVec example_2_3_fractional_point =
      ![(1 : ℚ) / 2, 3 / 2, 1] := by
  -- Extensionality isolates each of the three row sums of the explicit matrix.
  ext i
  fin_cases i
  · norm_num [example_2_3_clique_matrix, example_2_3_fractional_point,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [example_2_3_clique_matrix, example_2_3_fractional_point,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num [example_2_3_clique_matrix, example_2_3_fractional_point,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

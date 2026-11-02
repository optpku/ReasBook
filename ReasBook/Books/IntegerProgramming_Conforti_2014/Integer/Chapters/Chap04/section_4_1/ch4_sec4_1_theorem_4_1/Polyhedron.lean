import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

open scoped Matrix

/-- The subset of `ℝ^n` cut out by a rational inequality system after coercing the data to `ℝ`. -/
abbrev rational_matrix_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Set (Fin n → ℝ) :=
  polyhedron_le_set (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))

/-- Membership in `rational_matrix_polyhedron A b` is the corresponding real inequality system. -/
theorem mem_rational_matrix_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℝ) :
    x ∈ rational_matrix_polyhedron A b ↔
      (A.map (Rat.castHom ℝ)) *ᵥ x ≤ fun i ↦ (b i : ℝ) :=
  Iff.rfl

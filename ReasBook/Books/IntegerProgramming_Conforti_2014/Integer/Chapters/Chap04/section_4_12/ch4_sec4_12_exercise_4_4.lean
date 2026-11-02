import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped Matrix

-- Semantic search note: `lean_leansearch` was unavailable in this session; this file uses
-- Mathlib's canonical `Matrix.IsTotallyUnimodular` together with the Chapter 4 owner
-- `is_integral`.

section Exercise44

/-- The `3 × 3` integer matrix displayed in Exercise 4.4. -/
def exercise_4_4_matrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(1 : ℤ), 1, 1;
    0, -1, 1;
    0, 0, 1]

/-- The real matrix obtained from `exercise_4_4_matrix` by entrywise casting. -/
def exercise_4_4_matrix_real : Matrix (Fin 3) (Fin 3) ℝ :=
  exercise_4_4_matrix.map (Int.castRingHom ℝ)

/-- The polyhedron `{x ∈ ℝ^3 : A x = b}` from Exercise 4.4 for an integral right-hand side `b`. -/
def exercise_4_4_polyhedron (b : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  {x | exercise_4_4_matrix_real *ᵥ x = fun i ↦ (b i : ℝ)}

/-- Helper for Exercise 4.4: the unique integral solution of the triangular system `A x = b`. -/
def exercise_4_4_solution_int (b : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![b 0 + b 1 - 2 * b 2, b 2 - b 1, b 2]

/-- Helper for Exercise 4.4: the real point obtained by casting the explicit integral solution. -/
def exercise_4_4_solution (b : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun i ↦ (exercise_4_4_solution_int b i : ℝ)

/-- Helper for Exercise 4.4: the chosen submatrix is the explicit matrix `[[1,1],[-1,1]]`. -/
lemma exercise_4_4_bad_minor_eq :
    exercise_4_4_matrix.submatrix ![0, 1] ![1, 2] = !![(1 : ℤ), 1; -1, 1] := by
  -- Compute the four entries of the selected minor directly.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exercise_4_4_matrix]

/-- Helper for Exercise 4.4: the chosen `2 × 2` minor of `A` has determinant `2`. -/
lemma exercise_4_4_bad_minor_det_two :
    Matrix.det (exercise_4_4_matrix.submatrix ![0, 1] ![1, 2]) = (2 : ℤ) := by
  -- Rewrite to the explicit `2 × 2` matrix and evaluate its determinant.
  rw [exercise_4_4_bad_minor_eq, Matrix.det_fin_two_of]
  norm_num

/-- Exercise 4.4 (1). The displayed matrix `A` is not totally unimodular. -/
theorem exercise_4_4_matrix_not_totally_unimodular :
    ¬ exercise_4_4_matrix.IsTotallyUnimodular := by
  intro hTU
  -- A totally unimodular matrix forces this bad minor determinant to be a sign value.
  have hminor :
      Matrix.det (exercise_4_4_matrix.submatrix ![0, 1] ![1, 2]) ∈
        Set.range (SignType.cast : SignType → ℤ) :=
    hTU 2 ![0, 1] ![1, 2] (by decide) (by decide)
  rw [exercise_4_4_bad_minor_det_two] at hminor
  -- But `2` is not one of `0`, `1`, or `-1`.
  rw [SignType.range_eq (SignType.cast : SignType → ℤ)] at hminor
  norm_num at hminor

/-- Helper for Exercise 4.4: the first row of `A` sends `x` to `x₀ + x₁ + x₂`. -/
lemma exercise_4_4_row_zero_mulVec (x : Fin 3 → ℝ) :
    (exercise_4_4_matrix_real *ᵥ x) 0 = x 0 + x 1 + x 2 := by
  -- Expand the dot product against the first row of the matrix.
  simp [exercise_4_4_matrix_real, exercise_4_4_matrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- Helper for Exercise 4.4: the second row of `A` sends `x` to `-x₁ + x₂`. -/
lemma exercise_4_4_row_one_mulVec (x : Fin 3 → ℝ) :
    (exercise_4_4_matrix_real *ᵥ x) 1 = -x 1 + x 2 := by
  -- Expand the dot product against the second row of the matrix.
  simp [exercise_4_4_matrix_real, exercise_4_4_matrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- Helper for Exercise 4.4: the third row of `A` sends `x` to `x₂`. -/
lemma exercise_4_4_row_two_mulVec (x : Fin 3 → ℝ) :
    (exercise_4_4_matrix_real *ᵥ x) 2 = x 2 := by
  -- Expand the dot product against the third row of the matrix.
  simp [exercise_4_4_matrix_real, exercise_4_4_matrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

/-- Helper for Exercise 4.4: the explicit real solution really satisfies the system `A x = b`. -/
lemma exercise_4_4_solution_mem_polyhedron (b : Fin 3 → ℤ) :
    exercise_4_4_solution b ∈ exercise_4_4_polyhedron b := by
  -- Check the three row equations of the triangular system directly.
  ext i
  fin_cases i
  · simp [exercise_4_4_row_zero_mulVec, exercise_4_4_solution, exercise_4_4_solution_int]
    ring
  · simp [exercise_4_4_row_one_mulVec, exercise_4_4_solution, exercise_4_4_solution_int]
  · simp [exercise_4_4_row_two_mulVec, exercise_4_4_solution, exercise_4_4_solution_int]

/-- Helper for Exercise 4.4: every feasible point is forced to equal the explicit solution. -/
lemma exercise_4_4_eq_solution_of_mem_polyhedron
    {b : Fin 3 → ℤ} {x : Fin 3 → ℝ} (hx : x ∈ exercise_4_4_polyhedron b) :
    x = exercise_4_4_solution b := by
  -- Read the third, second, and first equations in order and back-substitute.
  have hAx : exercise_4_4_matrix_real *ᵥ x = fun i ↦ (b i : ℝ) := hx
  have hx2 : x 2 = (b 2 : ℝ) := by
    simpa [exercise_4_4_row_two_mulVec] using congrFun hAx 2
  have hx1eq : -x 1 + x 2 = (b 1 : ℝ) := by
    simpa [exercise_4_4_row_one_mulVec] using congrFun hAx 1
  have hx1 : x 1 = (b 2 : ℝ) - (b 1 : ℝ) := by
    linarith [hx1eq, hx2]
  have hx0eq : x 0 + x 1 + x 2 = (b 0 : ℝ) := by
    simpa [exercise_4_4_row_zero_mulVec] using congrFun hAx 0
  have hx0 : x 0 = (b 0 : ℝ) + (b 1 : ℝ) - 2 * (b 2 : ℝ) := by
    linarith [hx0eq, hx1, hx2]
  -- Equality of the three coordinates gives equality of vectors.
  ext i
  fin_cases i
  · simpa [exercise_4_4_solution, exercise_4_4_solution_int] using hx0
  · simpa [exercise_4_4_solution, exercise_4_4_solution_int] using hx1
  · simpa [exercise_4_4_solution, exercise_4_4_solution_int] using hx2

/-- Helper for Exercise 4.4: the feasible set is the singleton containing the explicit solution. -/
lemma exercise_4_4_polyhedron_eq_singleton_solution (b : Fin 3 → ℤ) :
    exercise_4_4_polyhedron b = {exercise_4_4_solution b} := by
  -- The explicit solution is feasible, and the triangular system has no other solution.
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨exercise_4_4_solution_mem_polyhedron b, ?_⟩
  intro x hx
  exact exercise_4_4_eq_solution_of_mem_polyhedron hx

/-- Helper for Exercise 4.4: the explicit solution is an integer vector in the Chapter 4 sense. -/
lemma exercise_4_4_solution_mem_integerVectors (b : Fin 3 → ℤ) :
    exercise_4_4_solution b ∈ integerVectors 3 := by
  refine ⟨exercise_4_4_solution_int b, ?_⟩
  ext i
  simp [exercise_4_4_solution]

/-- Helper for Exercise 4.4: the integral points of the polyhedron form the same singleton. -/
lemma exercise_4_4_integer_points_eq_singleton_solution (b : Fin 3 → ℤ) :
    exercise_4_4_polyhedron b ∩ integerVectors 3 = {exercise_4_4_solution b} := by
  -- The only feasible point is already integral, so intersecting with `ℤ^3` does not change the
  -- singleton feasible set.
  ext x
  constructor
  · intro hx
    have hx' : x ∈ exercise_4_4_polyhedron b := hx.1
    rw [exercise_4_4_polyhedron_eq_singleton_solution] at hx'
    simpa using hx'
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨exercise_4_4_solution_mem_polyhedron b, exercise_4_4_solution_mem_integerVectors b⟩

/-- Exercise 4.4 (2), in canonical Chapter 4 form. For every integral right-hand side `b`, the
polyhedron `{x ∈ ℝ^3 : A x = b}` is integral. -/
theorem exercise_4_4_polyhedron_isIntegral
    (b : Fin 3 → ℤ) :
    is_integral (exercise_4_4_polyhedron b) := by
  rw [is_integral_iff]
  -- Both the polyhedron and its integral-point set are the singleton containing the explicit
  -- solution.
  calc
    exercise_4_4_polyhedron b = {exercise_4_4_solution b} := by
      rw [exercise_4_4_polyhedron_eq_singleton_solution]
    _ = convexHull ℝ ({exercise_4_4_solution b} : Set (Fin 3 → ℝ)) := by
      rw [convexHull_singleton]
    _ = convexHull ℝ (exercise_4_4_polyhedron b ∩ integerVectors 3) := by
      rw [← exercise_4_4_integer_points_eq_singleton_solution]

/-- Exercise 4.4 (2). For every integral right-hand side `b`, the polyhedron
`{x ∈ ℝ^3 : A x = b}` equals the convex hull of its integer points. -/
theorem exercise_4_4_polyhedron_is_integral
    (b : Fin 3 → ℤ) :
    exercise_4_4_polyhedron b =
      convexHull ℝ (exercise_4_4_polyhedron b ∩ integerVectors 3) := by
  exact (is_integral_iff).1 (exercise_4_4_polyhedron_isIntegral b)

end Exercise44

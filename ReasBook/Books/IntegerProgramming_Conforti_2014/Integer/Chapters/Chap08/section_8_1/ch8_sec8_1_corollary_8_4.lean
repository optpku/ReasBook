/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_easy_block_feasible_set
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_theorem_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Corollary84

variable {m₁ m₂ n : ℕ}

/-- Weak-duality half of the Section 8.1 easy-block comparison:
the integer-program optimum `z_I` is bounded above by the Lagrangian dual bound `z_LD`
on the canonical pure-integer easy block
`Q = pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)`. -/
theorem integer_program_value_le_lagrangian_dual_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ)
    (c : Fin n → ℝ) :
    integer_program_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ≤
      lagrangian_dual_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) :=
  by
    -- Compare `z_I` with each fixed-multiplier relaxation value, then infimize over `λ ≥ 0`.
    rw [lagrangian_dual_value_eq_sInf]
    refine le_sInf ?_
    rintro _ ⟨lam, hlam, rfl⟩
    -- Proposition 8.1 gives the pointwise weak-duality estimate for every nonnegative `λ`.
    exact integer_program_value_le_lagrangian_relaxation_value A₁ b₁ c
      (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) lam hlam

/-- Helper for Corollary 8.4: enlarging the base set can only increase the Section 8.1
integer-program value. -/
lemma integerProgramValue_mono
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    {Q R : Set (Fin n → ℝ)}
    (hQR : Q ⊆ R) :
    integer_program_value A₁ b₁ c Q ≤ integer_program_value A₁ b₁ c R := by
  -- Rewrite both values as suprema so one feasible witness can be transported along `Q ⊆ R`.
  rw [integer_program_value_eq_sSup, integer_program_value_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact le_sSup ⟨x, ⟨hQR hx.1, hx.2⟩, rfl⟩

/-- Helper for Corollary 8.4: every matrix polyhedron `polyhedron_le_set A b` is convex. -/
lemma polyhedronLeSet_convex
    {m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  intro x hx y hy a c ha hc hac i
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a • x + c • y)) i
        = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
      calc
        ∑ j, A i j * (a * x j + c * y j)
            = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                refine Finset.sum_congr rfl ?_
                intro j _
                ring
        _ = (∑ j, a * (A i j * x j)) + ∑ j, c * (A i j * y j) := by
              rw [Finset.sum_add_distrib]
        _ = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
              simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ a * b i + c * b i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
    _ = b i := by
      rw [← add_mul, hac, one_mul]

/-- Helper for Corollary 8.4: the convex hull of the pure-integer points of the easy block stays
inside the ambient nonnegative matrix polyhedron. -/
lemma convexHull_pureIntegerPoints_subset_nonnegativeMatrixPolyhedron
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ) :
    convexHull ℝ (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ⊆
      nonnegative_matrix_polyhedron A₂ b₂ := by
  -- Every generator already lies in the ambient easy block, and that block is convex.
  refine convexHull_min ?_ ?_
  · intro x hx
    exact (mem_pure_integer_points_iff.mp hx).1
  · rw [nonnegative_matrix_polyhedron_eq_polyhedron_le_set]
    exact polyhedronLeSet_convex _ _

/-- Strong-duality half of the Section 8.1 easy-block comparison:
under the standing nonemptiness hypothesis from Theorem 8.2 on the convexified feasible region
of `Q = pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)`, the Lagrangian dual bound
`z_LD` is bounded above by the usual linear-programming relaxation bound `z_LP`
on the continuous easy block `nonnegative_matrix_polyhedron A₂ b₂`. -/
theorem lagrangian_dual_value_le_linear_programming_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ)
    (c : Fin n → ℝ)
    (hfeas :
      Set.Nonempty
        (convex_hull_feasible_set A₁ b₁
          (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)))) :
    lagrangian_dual_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ≤
      integer_program_value A₁ b₁ c (nonnegative_matrix_polyhedron A₂ b₂) := by
  have hQ :
      HasEasyBlockIntegerOrigin
        (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) := by
    exact ⟨m₂, A₂, b₂, rfl⟩
  -- Rewrite `z_LD` using Theorem 8.2, then enlarge the base set from `conv(Q)` to the full easy
  -- block via the convex-hull inclusion bridge.
  calc
    lagrangian_dual_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) =
        integer_program_value A₁ b₁ c
          (convexHull ℝ (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂))) := by
            simpa using
              lagrangian_dual_value_eq_integer_program_value_on_convex_hull
                A₁ b₁ c
                (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂))
                hQ
                hfeas
    _ ≤ integer_program_value A₁ b₁ c (nonnegative_matrix_polyhedron A₂ b₂) :=
      integerProgramValue_mono A₁ b₁ c
        (convexHull_pureIntegerPoints_subset_nonnegativeMatrixPolyhedron A₂ b₂)

/-- Corollary 8.4. Under the standing nonemptiness hypothesis from Theorem 8.2 on the
convexified feasible region of the Section 8.1 easy block
`Q = pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)`, one has `z_I ≤ z_LD ≤ z_LP`. -/
theorem integer_program_value_le_lagrangian_dual_value_le_linear_programming_relaxation_value
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℤ)
    (b₂ : Fin m₂ → ℤ)
    (c : Fin n → ℝ)
    (hfeas :
      Set.Nonempty
        (convex_hull_feasible_set A₁ b₁
          (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)))) :
    integer_program_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ≤
        lagrangian_dual_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ∧
      lagrangian_dual_value A₁ b₁ c (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) ≤
        integer_program_value A₁ b₁ c (nonnegative_matrix_polyhedron A₂ b₂) :=
  by
    constructor
    · -- The lower bound is the weak-duality estimate already proved above.
      exact integer_program_value_le_lagrangian_dual_value A₁ b₁ A₂ b₂ c
    · -- The upper bound is the convex-hull comparison established just above.
      exact
        lagrangian_dual_value_le_linear_programming_relaxation_value
          A₁ b₁ A₂ b₂ c hfeas

end Corollary84

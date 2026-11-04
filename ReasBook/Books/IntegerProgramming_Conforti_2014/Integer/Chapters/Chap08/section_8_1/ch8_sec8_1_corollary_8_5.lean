/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_easy_block_feasible_set
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_theorem_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Corollary85

variable {m n : ℕ}

/-- Helper for Corollary 8.5: imposing the easy-block inequalities twice does not change the
underlying feasible set. -/
lemma lagrangianIntegerFeasibleSet_eq_easyBlock
    (A₂ : Matrix (Fin m) (Fin n) ℝ)
    (b₂ : Fin m → ℝ) :
    lagrangian_integer_feasible_set A₂ b₂ (easy_block_feasible_set A₂ b₂) =
      easy_block_feasible_set A₂ b₂ := by
  -- Both sides encode the same inequalities; the Lagrangian feasible-set owner only repeats
  -- the easy-block row constraints.
  ext x
  rw [mem_lagrangian_integer_feasible_set_iff, mem_easy_block_feasible_set_iff]
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hx.1⟩

/-- Helper for Corollary 8.5: at multiplier `0`, the Lagrangian relaxation over the easy block is
exactly the usual LP-relaxation value on that same easy block. -/
lemma lagrangianRelaxationValue_zero_eq_integerProgramValue_easyBlock
    (A₂ : Matrix (Fin m) (Fin n) ℝ)
    (b₂ : Fin m → ℝ)
    (c : Fin n → ℝ) :
    lagrangian_relaxation_value A₂ b₂ c (easy_block_feasible_set A₂ b₂) 0 =
      integer_program_value A₂ b₂ c (easy_block_feasible_set A₂ b₂) := by
  -- Rewrite both values as suprema over the same owner, then simplify the zero penalty.
  rw [lagrangian_relaxation_value_eq_sSup, integer_program_value_eq_sSup,
    lagrangianIntegerFeasibleSet_eq_easyBlock]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    simp

/-- Corollary 8.5 (1). If `convexHull ℝ Q = {x ∈ ℝ^n_+ | A₂ *ᵥ x ≤ b²}`, then for every
objective vector `c ∈ ℝ^n` the Lagrangian dual bound equals the usual linear-programming
relaxation bound. Here the LP relaxation is the existing Proposition 8.1 owner specialized to the
continuous easy-block set `easy_block_feasible_set A₂ b₂`. -/
theorem lagrangian_dual_value_eq_linear_programming_relaxation_value_of_convexHull_eq
    (Q : Set (Fin n → ℝ))
    (A₂ : Matrix (Fin m) (Fin n) ℝ)
    (b₂ : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hQ : convexHull ℝ Q = easy_block_feasible_set A₂ b₂) :
    lagrangian_dual_value A₂ b₂ c Q =
      integer_program_value A₂ b₂ c (easy_block_feasible_set A₂ b₂) := by
  refine le_antisymm ?_ ?_
  · -- Evaluate the dual infimum at the feasible multiplier `λ = 0`.
    rw [lagrangian_dual_value_eq_sInf]
    have hzero : (0 : Fin m → ℝ) ∈ Set.Ici (0 : Fin m → ℝ) := by
      intro i
      simp
    have hRelaxZero :
        lagrangian_relaxation_value A₂ b₂ c Q 0 ≤
          integer_program_value A₂ b₂ c (easy_block_feasible_set A₂ b₂) := by
      -- Transport `z_LR(0)` across the convex-hull identity, then collapse the zero penalty.
      rw [lagrangianRelaxationValue_eq_convexHull A₂ b₂ c Q 0, hQ,
        lagrangianRelaxationValue_zero_eq_integerProgramValue_easyBlock A₂ b₂ c]
    have hdualZero :
        lagrangian_dual_value A₂ b₂ c Q ≤ lagrangian_relaxation_value A₂ b₂ c Q 0 := by
      exact (lagrangian_dual_value_eq_sInf A₂ b₂ c Q).symm ▸
        sInf_le ⟨(0 : Fin m → ℝ), hzero, rfl⟩
    exact hdualZero.trans hRelaxZero
  · -- Rewrite the LP side back to the convex hull and apply the generic weak-duality bound.
    rw [← hQ]
    exact integer_program_value_on_convex_hull_le_lagrangian_dual_value A₂ b₂ c Q

/-- Companion bridge for Corollary 8.5 (2): when `A₂` is totally unimodular, the nonnegative
polyhedron `{x ∈ ℝ^n_+ | A₂ *ᵥ x ≤ b²}` is already the convex hull of its pure-integer points. -/
theorem pure_integer_hull_eq_nonnegative_matrix_polyhedron_of_totally_unimodular
    (A₂ : Matrix (Fin m) (Fin n) ℤ)
    (b₂ : Fin m → ℤ)
    (hA₂ : A₂.IsTotallyUnimodular) :
    pure_integer_hull (nonnegative_matrix_polyhedron A₂ b₂) =
      nonnegative_matrix_polyhedron A₂ b₂ := by
  rw [pure_integer_hull_eq_convexHull]
  simpa [integerVectors] using
    (is_integral_iff.mp
      (nonnegative_matrix_polyhedron_is_integral_of_isTotallyUnimodular A₂ b₂ hA₂)).symm

/-- Corollary 8.5 (2). In the pure-integer case, if `A₂` is totally unimodular and `b²` is an
integral vector, then the Lagrangian dual bound equals the usual linear-programming relaxation
bound for every objective vector `c ∈ ℝ^n`. Here the pure-integer bound is the existing Chapter
8.1 owner applied to `pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)`, whose convex
hull is the ambient nonnegative polyhedron by the Hoffman-Kruskal integrality theorem. -/
theorem
    pure_integer_lagrangian_dual_value_eq_linear_programming_relaxation_value_of_totally_unimodular
    (A₂ : Matrix (Fin m) (Fin n) ℤ)
    (b₂ : Fin m → ℤ)
    (c : Fin n → ℝ)
    (hA₂ : A₂.IsTotallyUnimodular) :
    lagrangian_dual_value (A₂.map (Int.castRingHom ℝ)) (fun i ↦ (b₂ i : ℝ)) c
        (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) =
      integer_program_value (A₂.map (Int.castRingHom ℝ)) (fun i ↦ (b₂ i : ℝ)) c
        (nonnegative_matrix_polyhedron A₂ b₂) := by
  have hQ :
      convexHull ℝ (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) =
        easy_block_feasible_set (A₂.map (Int.castRingHom ℝ)) (fun i ↦ (b₂ i : ℝ)) := by
    calc
      convexHull ℝ (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂)) =
          pure_integer_hull (nonnegative_matrix_polyhedron A₂ b₂) := rfl
      _ = nonnegative_matrix_polyhedron A₂ b₂ :=
          pure_integer_hull_eq_nonnegative_matrix_polyhedron_of_totally_unimodular A₂ b₂ hA₂
      _ =
          easy_block_feasible_set (A₂.map (Int.castRingHom ℝ)) (fun i ↦ (b₂ i : ℝ)) := by
          ext x
          rw [nonnegative_matrix_polyhedron, easy_block_feasible_set, Set.mem_inter_iff,
            mem_polyhedron_le_set_iff]
          rfl
  simpa [easy_block_feasible_set, nonnegative_matrix_polyhedron, polyhedron_le_set] using
    lagrangian_dual_value_eq_linear_programming_relaxation_value_of_convexHull_eq
      (pure_integer_points (nonnegative_matrix_polyhedron A₂ b₂))
      (A₂.map (Int.castRingHom ℝ))
      (fun i ↦ (b₂ i : ℝ))
      c
      hQ

end Corollary85

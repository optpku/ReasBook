/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_theorem_4_51
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_1

open scoped Matrix NonnegativeRankNotation

universe u v w

/-!
Domain-style sampling for this refine pass:
* primary domain: extension complexity via slack matrices, nonnegative rank, and rectangle covers
* source-facing owners inspected: `polyhedron_le_set`, `linear_extended_system`, `slack_matrix`
* core/canonical owner theorem reused here:
  `nonnegative_rank_le_extended_formulation_constraint_count`
* bridge/view theorem added here: `rectangle_covering_number_le_nonnegative_rank`

This file operates at the `bridge/view` layer: Lemma 4.53 is the rectangle-covering corollary of
the chapter's canonical nonnegative-rank lower bound for extended formulations.
-/

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_10_1/ch4_sec4_10_1_lemma_4_53.lean`: the support of a product of
entrywise-nonnegative real matrices is the union of the products of the factor supports. -/
private theorem matrix_support_mul_eq_iUnion_prod_of_nonnegative
    {m : Type u} {n : Type v} {k : Type w} [Fintype k]
    (F : Matrix m k ℝ) (W : Matrix k n ℝ)
    (hF : 0 ≤ F) (hW : 0 ≤ W) :
    matrix_support (F * W) =
      ⋃ h, ({i | F i h ≠ 0} : Set m).prod ({j | W h j ≠ 0} : Set n) := by
  ext p
  rcases p with ⟨i, j⟩
  rw [mem_matrix_support_iff, Matrix.mul_apply]
  constructor
  · -- A nonzero sum has a nonzero summand, which supplies one rectangular support.
    intro hsum
    obtain ⟨h, _, hh⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    refine Set.mem_iUnion.mpr ⟨h, ?_⟩
    exact (mul_ne_zero_iff.mp hh)
  · -- A selected nonzero summand is positive, while every other summand is nonnegative.
    intro hp
    obtain ⟨h, hFi, hWj⟩ := Set.mem_iUnion.mp hp
    have hterm : 0 < F i h * W h j := by
      exact mul_pos (lt_of_le_of_ne (hF i h) (Ne.symm hFi))
        (lt_of_le_of_ne (hW h j) (Ne.symm hWj))
    exact ne_of_gt ((Finset.sum_pos_iff_of_nonneg
      (fun q _ ↦ mul_nonneg (hF i q) (hW q j))).2
      ⟨h, Finset.mem_univ h, hterm⟩)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_10_1/ch4_sec4_10_1_lemma_4_53.lean`: a union of at most `k`
nonempty product supports gives a rectangle cover of size at most `k`. -/
private theorem rectangle_covering_number_le_iUnion_prod
    {m : Type u} {n : Type v} {α : Type w}
    [Finite m] [Finite n] [Zero α] [One α] [NeZero (1 : α)]
    {k : Type*} [Fintype k]
    (S : Matrix m n α) (I : k → Set m) (J : k → Set n)
    (hSupport : matrix_support S = ⋃ h, (I h).prod (J h)) :
    rectangle_covering_number S ≤ Fintype.card k := by
  classical
  let T : Type _ := {h : k // (I h).Nonempty ∧ (J h).Nonempty}
  let eT : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let R : Fin (Fintype.card T) → Matrix m n α := fun t ↦
    rectangle_indicator (I (eT.symm t).1) (J (eT.symm t).1)
  have hR : is_rectangle_cover S R := by
    refine (is_rectangle_cover_iff).mpr ⟨?_, ?_⟩
    · -- Filtering to `T` ensures that every retained product is a genuine rectangle.
      intro t
      exact rectangle_indicator_is_rectangle_matrix (eT.symm t).2.1 (eT.symm t).2.2
    · -- Reindexing the active products preserves exactly the original support union.
      ext p
      rcases p with ⟨i, j⟩
      constructor
      · intro hp
        rw [hSupport] at hp
        obtain ⟨h, hi, hj⟩ := Set.mem_iUnion.mp hp
        let t : T := ⟨h, ⟨⟨i, hi⟩, ⟨j, hj⟩⟩⟩
        refine Set.mem_iUnion.mpr ⟨eT t, ?_⟩
        have hpProd : (i, j) ∈ (I h).prod (J h) := ⟨hi, hj⟩
        simp only [R, matrix_support_rectangle_indicator, eT.symm_apply_apply]
        exact hpProd
      · intro hp
        obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
        rw [hSupport]
        refine Set.mem_iUnion.mpr ⟨(eT.symm t).1, ?_⟩
        simp only [R, matrix_support_rectangle_indicator] at ht
        exact ht
  -- The active-index subtype has cardinality no larger than the original index type.
  calc
    rectangle_covering_number S ≤ Fintype.card T := rectangle_covering_number_le hR
    _ ≤ Fintype.card k := by
      simpa [T] using
        (Fintype.card_subtype_le (fun h : k ↦ (I h).Nonempty ∧ (J h).Nonempty))

/-- A nonnegative matrix has rectangle covering number at most its nonnegative rank. -/
theorem rectangle_covering_number_le_nonnegative_rank
    {m : Type u} {n : Type v} [Finite m] [Finite n]
    (S : Matrix.Nonnegative m n ℝ) :
    rectangle_covering_number (S : Matrix m n ℝ) ≤ rank₊ S := by
  -- A minimal nonnegative factorization controls the support by rank-many products.
  obtain ⟨F, W, hF, hW, hS⟩ :=
    (has_nonnegative_rank_factorization_iff.mp (nonnegative_rank_isLeast S).1)
  have hSupport :
      matrix_support (S : Matrix m n ℝ) =
        ⋃ h, ({i | F i h ≠ 0} : Set m).prod ({j | W h j ≠ 0} : Set n) := by
    calc
      matrix_support (S : Matrix m n ℝ) = matrix_support (F * W) :=
        congrArg matrix_support hS
      _ = ⋃ h, ({i | F i h ≠ 0} : Set m).prod ({j | W h j ≠ 0} : Set n) :=
        matrix_support_mul_eq_iUnion_prod_of_nonnegative F W hF hW
  have hcover := rectangle_covering_number_le_iUnion_prod
    (S : Matrix m n ℝ) (fun h ↦ {i | F i h ≠ 0}) (fun h ↦ {j | W h j ≠ 0}) hSupport
  simpa only [Fintype.card_fin] using hcover

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_10_1/ch4_sec4_10_1_lemma_4_53.lean

Lemma 4.53. Let `P ⊆ ℝ^n` be a polytope. Every extended formulation of `P` has a number of
constraints at least equal to the rectangle covering number of the slack matrix of any
facet-defining system of linear inequalities describing `P`. -/
theorem rectangle_covering_number_le_extended_formulation_constraint_count
    {m n p : ℕ}
    {ρ : Type u} {σ : Type v} {κ : Type w}
    [Fintype ρ] [Fintype σ] [Fintype κ]
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (Aeq : Matrix ρ (Fin n) ℝ)
    (Beq : Matrix ρ κ ℝ)
    (beq : ρ → ℝ)
    (Aineq : Matrix σ (Fin n) ℝ)
    (Bineq : Matrix σ κ ℝ)
    (bineq : σ → ℝ)
    (hP_vertices : P = convexHull ℝ (Set.range vertices))
    (hP_system : P = polyhedron_le_set A b)
    (hfacets : ∀ i : Fin m, maximalProperFaceInequality P (A i) (b i))
    (hEF : P = Prod.fst '' linear_extended_system Aeq Beq beq Aineq Bineq bineq) :
    rectangle_covering_number (slack_matrix A b vertices) ≤ Fintype.card ρ + Fintype.card σ :=
  by
    let hvertices :=
      vertices_feasible_of_polytope_description P A b vertices hP_vertices hP_system
    let S : Matrix.Nonnegative (Fin m) (Fin p) ℝ :=
      ⟨slack_matrix A b vertices, slack_matrix_nonneg hvertices⟩
    -- First compare the slack support invariant with the nonnegative rank of its bundled matrix.
    have hcover : rectangle_covering_number (slack_matrix A b vertices) ≤ rank₊ S := by
      simpa [S] using rectangle_covering_number_le_nonnegative_rank S
    -- The imported Yannakakis bound controls that rank by the formulation's constraint count.
    have hrank : rank₊ S ≤ Fintype.card ρ + Fintype.card σ := by
      simpa [hvertices, S] using
        nonnegative_rank_le_extended_formulation_constraint_count
          P A b vertices Aeq Beq beq Aineq Bineq bineq
            hP_vertices hP_system hfacets hEF
    exact hcover.trans hrank

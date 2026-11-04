/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the formulation
-- below follows the chapter's permutahedron owner together with the canonical Birkhoff-polytope
-- API for doubly stochastic matrices.

/-- The feasible set from Exercise 4.1 is the vertex set of the third permutahedron, i.e. the
integer triples in `ℝ^3` whose coordinates are exactly `1`, `2`, and `3` in some order. -/
def exercise_4_1_feasible_set : Set (Fin 3 → ℝ) :=
  permutahedron_vertices 3

/-- The binary assignment formulation encoding that each coordinate receives exactly one value in
`{1, 2, 3}` and each value is used exactly once. -/
def exercise_4_1_milp (x : Fin 3 → ℝ) (y : Fin 3 × Fin 3 → ℝ) : Prop :=
  (∀ i : Fin 3, ∑ j : Fin 3, y (i, j) = 1) ∧
    (∀ j : Fin 3, ∑ i : Fin 3, y (i, j) = 1) ∧
    (∀ i j : Fin 3, y (i, j) = 0 ∨ y (i, j) = 1) ∧
    ∀ i : Fin 3, x i = ∑ j : Fin 3, ascending_vector 3 j * y (i, j)

/-- The linear-programming relaxation of the assignment formulation from `exercise_4_1_milp`. -/
def exercise_4_1_relaxation (x : Fin 3 → ℝ) (y : Fin 3 × Fin 3 → ℝ) : Prop :=
  (∀ i : Fin 3, ∑ j : Fin 3, y (i, j) = 1) ∧
    (∀ j : Fin 3, ∑ i : Fin 3, y (i, j) = 1) ∧
    (∀ i j : Fin 3, 0 ≤ y (i, j)) ∧
    ∀ i : Fin 3, x i = ∑ j : Fin 3, ascending_vector 3 j * y (i, j)

/-- The linear projection sending an assignment matrix to the induced value vector. -/
def exercise_4_1_projection : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 3 → ℝ) :=
  (LinearMap.applyₗ (ascending_vector 3)).comp Matrix.toLin'.toLinearMap

/-- Helper for Exercise 4.1: the projection map is the weighted row-sum formula from the model. -/
lemma exercise_4_1_projection_apply (M : Matrix (Fin 3) (Fin 3) ℝ) :
    exercise_4_1_projection M = fun i ↦ ∑ j : Fin 3, ascending_vector 3 j * M i j := by
  -- Unfold the linear map and rewrite matrix-vector multiplication rowwise.
  ext i
  simp [exercise_4_1_projection, Matrix.toLin'_apply', Matrix.mulVec, dotProduct, mul_comm]

/-- Helper for Exercise 4.1: projecting a permutation matrix recovers the corresponding
permutation of `(1, 2, 3)`. -/
lemma exercise_4_1_projection_permMatrix (σ : Equiv.Perm (Fin 3)) :
    exercise_4_1_projection (σ.permMatrix ℝ) = ascending_vector 3 ∘ σ := by
  -- The projection is matrix-vector multiplication by the value vector, and permutation matrices
  -- act by permuting coordinates.
  have hmul : Matrix.mulVec (σ.permMatrix ℝ) (ascending_vector 3) = ascending_vector 3 ∘ σ :=
    Matrix.permMatrix_mulVec σ
  ext i
  rw [exercise_4_1_projection_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using
    congrArg (fun v : Fin 3 → ℝ ↦ v i) hmul

/-- Helper for Exercise 4.1: a triple of `0/1` entries summing to `1` is one of the three
standard basis rows. -/
lemma exercise_4_1_row_pattern_of_zero_one_sum_one {a b c : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hsum : a + b + c = 1) :
    (a = 1 ∧ b = 0 ∧ c = 0) ∨
      (a = 0 ∧ b = 1 ∧ c = 0) ∨
      (a = 0 ∧ b = 0 ∧ c = 1) := by
  -- Enumerating the eight binary possibilities leaves exactly the three unit vectors.
  rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl
  · norm_num at hsum
  · exact Or.inr <| Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr <| Or.inl ⟨rfl, rfl, rfl⟩
  · norm_num at hsum
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · norm_num at hsum
  · norm_num at hsum
  · norm_num at hsum

/-- Helper for Exercise 4.1: every `0/1` row with sum `1` contains a unique entry equal to `1`. -/
lemma exercise_4_1_row_has_unique_one
    {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hrow : ∀ i : Fin 3, ∑ j : Fin 3, M i j = 1)
    (h01 : ∀ i j : Fin 3, M i j = 0 ∨ M i j = 1) (i : Fin 3) :
    ∃! j : Fin 3, M i j = 1 := by
  -- Rewrite the fixed-size row sum and classify the resulting binary triple.
  have hsum := hrow i
  rw [Fin.sum_univ_three] at hsum
  obtain hpat :=
    exercise_4_1_row_pattern_of_zero_one_sum_one (h01 i 0) (h01 i 1) (h01 i 2) hsum
  rcases hpat with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨0, h0, ?_⟩
    intro j hj
    fin_cases j <;> simp [h0, h1, h2] at hj ⊢
  · refine ⟨1, h1, ?_⟩
    intro j hj
    fin_cases j <;> simp [h0, h1, h2] at hj ⊢
  · refine ⟨2, h2, ?_⟩
    intro j hj
    fin_cases j <;> simp [h0, h1, h2] at hj ⊢

/-- Helper for Exercise 4.1: a `0/1` matrix with every row and column summing to `1`
is a permutation matrix. -/
lemma exists_permMatrix_of_zero_one_row_col_sums_one
    {M : Matrix (Fin 3) (Fin 3) ℝ}
    (hrow : ∀ i : Fin 3, ∑ j : Fin 3, M i j = 1)
    (hcol : ∀ j : Fin 3, ∑ i : Fin 3, M i j = 1)
    (h01 : ∀ i j : Fin 3, M i j = 0 ∨ M i j = 1) :
    ∃ σ : Equiv.Perm (Fin 3), M = σ.permMatrix ℝ := by
  classical
  -- Choose, in each row, the unique column where the entry is `1`.
  let f : Fin 3 → Fin 3 := fun i ↦ Classical.choose (exercise_4_1_row_has_unique_one hrow h01 i)
  have hf_one : ∀ i : Fin 3, M i (f i) = 1 := by
    intro i
    exact (Classical.choose_spec (exercise_4_1_row_has_unique_one hrow h01 i)).1
  have hf_unique : ∀ i j : Fin 3, M i j = 1 → j = f i := by
    intro i j hj
    exact (Classical.choose_spec (exercise_4_1_row_has_unique_one hrow h01 i)).2 j hj
  have hnonneg : ∀ i j : Fin 3, 0 ≤ M i j := by
    intro i j
    rcases h01 i j with hij | hij <;> linarith
  -- Two distinct rows cannot choose the same column, otherwise that column sum would exceed `1`.
  have hf_injective : Function.Injective f := by
    intro i i' hEq
    fin_cases i <;> fin_cases i'
    · rfl
    · have hcol0 : ∑ k : Fin 3, M k (f 0) = 1 := hcol (f 0)
      have h1eq : M 1 (f 0) = M 1 (f 1) := by
        simpa using congrArg (fun t ↦ M 1 t) hEq
      have h1 : M 1 (f 0) = 1 := by
        calc
          M 1 (f 0) = M 1 (f 1) := h1eq
          _ = 1 := hf_one 1
      rw [Fin.sum_univ_three, hf_one 0, h1] at hcol0
      have : False := by linarith [hnonneg 2 (f 0)]
      exact this.elim
    · have hcol0 : ∑ k : Fin 3, M k (f 0) = 1 := hcol (f 0)
      have h2eq : M 2 (f 0) = M 2 (f 2) := by
        simpa using congrArg (fun t ↦ M 2 t) hEq
      have h2 : M 2 (f 0) = 1 := by
        calc
          M 2 (f 0) = M 2 (f 2) := h2eq
          _ = 1 := hf_one 2
      rw [Fin.sum_univ_three, hf_one 0, h2] at hcol0
      have : False := by linarith [hnonneg 1 (f 0)]
      exact this.elim
    · have hcol1 : ∑ k : Fin 3, M k (f 1) = 1 := hcol (f 1)
      have h0eq : M 0 (f 1) = M 0 (f 0) := by
        simpa using congrArg (fun t ↦ M 0 t) hEq
      have h0 : M 0 (f 1) = 1 := by
        calc
          M 0 (f 1) = M 0 (f 0) := h0eq
          _ = 1 := hf_one 0
      rw [Fin.sum_univ_three, h0, hf_one 1] at hcol1
      have : False := by linarith [hnonneg 2 (f 1)]
      exact this.elim
    · rfl
    · have hcol1 : ∑ k : Fin 3, M k (f 1) = 1 := hcol (f 1)
      have h2eq : M 2 (f 1) = M 2 (f 2) := by
        simpa using congrArg (fun t ↦ M 2 t) hEq
      have h2 : M 2 (f 1) = 1 := by
        calc
          M 2 (f 1) = M 2 (f 2) := h2eq
          _ = 1 := hf_one 2
      rw [Fin.sum_univ_three, hf_one 1, h2] at hcol1
      have : False := by linarith [hnonneg 0 (f 1)]
      exact this.elim
    · have hcol2 : ∑ k : Fin 3, M k (f 2) = 1 := hcol (f 2)
      have h0eq : M 0 (f 2) = M 0 (f 0) := by
        simpa using congrArg (fun t ↦ M 0 t) hEq
      have h0 : M 0 (f 2) = 1 := by
        calc
          M 0 (f 2) = M 0 (f 0) := h0eq
          _ = 1 := hf_one 0
      rw [Fin.sum_univ_three, h0, hf_one 2] at hcol2
      have : False := by linarith [hnonneg 1 (f 2)]
      exact this.elim
    · have hcol2 : ∑ k : Fin 3, M k (f 2) = 1 := hcol (f 2)
      have h1eq : M 1 (f 2) = M 1 (f 1) := by
        simpa using congrArg (fun t ↦ M 1 t) hEq
      have h1 : M 1 (f 2) = 1 := by
        calc
          M 1 (f 2) = M 1 (f 1) := h1eq
          _ = 1 := hf_one 1
      rw [Fin.sum_univ_three, h1, hf_one 2] at hcol2
      have : False := by linarith [hnonneg 0 (f 2)]
      exact this.elim
    · rfl
  -- Turn the injective row-choice map into the underlying permutation.
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf_injective)
  have hentry : ∀ i j : Fin 3, M i j = if σ i = j then 1 else 0 := by
    intro i j
    by_cases h : σ i = j
    · have hfi : f i = j := by simpa [σ] using h
      simpa [h, hfi] using hf_one i
    · rcases h01 i j with hij | hij
      · simp [h, hij]
      · have hji : j = σ i := by
          simpa [σ] using hf_unique i j hij
        exact (h hji.symm).elim
  -- Entrywise comparison now identifies the matrix as the corresponding permutation matrix.
  refine ⟨σ, ?_⟩
  ext i j
  simpa [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, PEquiv.toMatrix_apply] using hentry i j

/-- Helper for Exercise 4.1: the feasible set consists exactly of the six permutation vectors
of `(1, 2, 3)`. -/
lemma exercise_4_1_feasible_set_iff_exists_perm (x : Fin 3 → ℝ) :
    x ∈ exercise_4_1_feasible_set ↔
      ∃ σ : Equiv.Perm (Fin 3), x = ascending_vector 3 ∘ σ := by
  simpa [exercise_4_1_feasible_set] using
    (mem_permutahedron_vertices_iff :
      x ∈ permutahedron_vertices 3 ↔ ∃ σ : Equiv.Perm (Fin 3), x = ascending_vector 3 ∘ σ)

/-- Helper for Exercise 4.1: the relaxation constraints are exactly membership in the doubly
stochastic polytope together with the projection equation. -/
lemma exercise_4_1_relaxation_iff_matrix_mem_doublyStochastic
    (x : Fin 3 → ℝ) (y : Fin 3 × Fin 3 → ℝ) :
    exercise_4_1_relaxation x y ↔
      ((Function.curry y : Matrix (Fin 3) (Fin 3) ℝ) ∈ doublyStochastic ℝ (Fin 3)) ∧
        x = exercise_4_1_projection (Function.curry y) := by
  -- Rewrite the relaxation constraints into the standard doubly stochastic API plus projection.
  constructor
  · rintro ⟨hrow, hcol, hnonneg, hx⟩
    refine ⟨?_, ?_⟩
    · exact (mem_doublyStochastic_iff_sum).2
        ⟨fun i j ↦ by simpa [Function.curry] using hnonneg i j,
        fun i ↦ by simpa [Function.curry] using hrow i,
        fun j ↦ by simpa [Function.curry] using hcol j⟩
    · ext i
      simpa [exercise_4_1_projection_apply, Function.curry] using hx i
  · rintro ⟨hM, hx⟩
    have hM' := (mem_doublyStochastic_iff_sum).1 hM
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa [Function.curry] using hM'.2.1 i
    · intro j
      simpa [Function.curry] using hM'.2.2 j
    · intro i j
      simpa [Function.curry] using hM'.1 i j
    · intro i
      simpa [exercise_4_1_projection_apply, Function.curry] using
        congrArg (fun v : Fin 3 → ℝ ↦ v i) hx

/-- Helper for Exercise 4.1: the projection of the permutation matrices is exactly the feasible
set. -/
lemma exercise_4_1_permMatrix_projection_eq_feasible_set :
    exercise_4_1_projection '' {σ.permMatrix ℝ | σ : Equiv.Perm (Fin 3)} =
      exercise_4_1_feasible_set := by
  ext x
  constructor
  · rintro ⟨M, ⟨σ, rfl⟩, hx⟩
    -- Once the source matrix is a permutation matrix, the image point is the matching permutation
    -- vector, hence feasible.
    refine (exercise_4_1_feasible_set_iff_exists_perm x).2 ⟨σ, ?_⟩
    simpa [exercise_4_1_projection_permMatrix σ] using hx.symm
  · intro hx
    rcases (exercise_4_1_feasible_set_iff_exists_perm x).1 hx with ⟨σ, rfl⟩
    -- Conversely, every feasible permutation vector is the image of its permutation matrix.
    exact ⟨σ.permMatrix ℝ, ⟨σ, rfl⟩, exercise_4_1_projection_permMatrix σ⟩

/-- The binary assignment formulation projects exactly to the integer triples in
`exercise_4_1_feasible_set`. -/
theorem exercise_4_1_exact_formulation (x : Fin 3 → ℝ) :
    x ∈ exercise_4_1_feasible_set ↔
      ∃ y : Fin 3 × Fin 3 → ℝ, exercise_4_1_milp x y := by
  constructor
  · intro hx
    rcases (exercise_4_1_feasible_set_iff_exists_perm x).1 hx with ⟨σ, rfl⟩
    refine ⟨Function.uncurry (σ.permMatrix ℝ), ?_⟩
    have hperm : σ.permMatrix ℝ ∈ doublyStochastic ℝ (Fin 3) := permMatrix_mem_doublyStochastic
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Permutation matrices have row sums equal to `1`.
      intro i
      simpa [Function.uncurry] using sum_row_of_mem_doublyStochastic hperm i
    · -- Permutation matrices have column sums equal to `1`.
      intro j
      simpa [Function.uncurry] using sum_col_of_mem_doublyStochastic hperm j
    · -- Each entry of a permutation matrix is binary.
      intro i j
      by_cases h : σ i = j
      · right
        simp [Function.uncurry, Equiv.Perm.permMatrix,
          Equiv.toPEquiv_apply, PEquiv.toMatrix_apply, h]
      · left
        simp [Function.uncurry, Equiv.Perm.permMatrix,
          Equiv.toPEquiv_apply, PEquiv.toMatrix_apply, h]
    · -- The matrix-vector product computes the assigned value in each row.
      intro i
      simpa [Function.uncurry] using
        congrArg (fun v : Fin 3 → ℝ ↦ v i) (exercise_4_1_projection_permMatrix σ).symm
  · rintro ⟨y, hy⟩
    rcases hy with ⟨hrow, hcol, h01, hx_eq⟩
    let M : Matrix (Fin 3) (Fin 3) ℝ := Function.curry y
    obtain ⟨σ, hM⟩ := exists_permMatrix_of_zero_one_row_col_sums_one
      (by simpa [M, Function.curry] using hrow)
      (by simpa [M, Function.curry] using hcol)
      (by simpa [M, Function.curry] using h01)
    have hx_perm : x = ascending_vector 3 ∘ σ := by
      -- Replace the assignment matrix by the permutation matrix extracted from its `0/1`
      -- row-and-column-sum structure, then evaluate the projection rowwise.
      ext i
      calc
        x i = ∑ j : Fin 3, ascending_vector 3 j * y (i, j) := hx_eq i
        _ = ∑ j : Fin 3, ascending_vector 3 j * M i j := by rfl
        _ = exercise_4_1_projection M i := by
          simpa using congrArg (fun v : Fin 3 → ℝ ↦ v i) (exercise_4_1_projection_apply M).symm
        _ = exercise_4_1_projection (σ.permMatrix ℝ) i := by
          simpa [M] using
            congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ ↦ exercise_4_1_projection N i) hM
        _ = (ascending_vector 3 ∘ σ) i := by
          simpa using congrArg (fun v : Fin 3 → ℝ ↦ v i) (exercise_4_1_projection_permMatrix σ)
    exact (exercise_4_1_feasible_set_iff_exists_perm x).2 ⟨σ, hx_perm⟩

/-- Exercise 4.1. An assignment-matrix relaxation gives a perfect formulation for the triples
`x ∈ {1, 2, 3}^3` whose coordinates are pairwise distinct. -/
theorem exercise_4_1_perfect_formulation :
    convexHull ℝ exercise_4_1_feasible_set =
      {x : Fin 3 → ℝ | ∃ y : Fin 3 × Fin 3 → ℝ, exercise_4_1_relaxation x y} := by
  -- Rewrite both sides through the linear projection of the Birkhoff polytope.
  calc
    convexHull ℝ exercise_4_1_feasible_set =
        convexHull ℝ
          (exercise_4_1_projection '' {σ.permMatrix ℝ | σ : Equiv.Perm (Fin 3)}) := by
      rw [exercise_4_1_permMatrix_projection_eq_feasible_set.symm]
    _ = exercise_4_1_projection '' convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm (Fin 3)} := by
      symm
      exact LinearMap.image_convexHull exercise_4_1_projection _
    _ = exercise_4_1_projection '' doublyStochastic ℝ (Fin 3) := by
      rw [doublyStochastic_eq_convexHull_permMatrix]
    _ = {x : Fin 3 → ℝ | ∃ y : Fin 3 × Fin 3 → ℝ, exercise_4_1_relaxation x y} := by
      ext x
      constructor
      · rintro ⟨M, hM, rfl⟩
        -- Any projected doubly stochastic matrix yields a relaxation witness by currying.
        refine ⟨Function.uncurry M, ?_⟩
        refine
          (exercise_4_1_relaxation_iff_matrix_mem_doublyStochastic
            (exercise_4_1_projection M) (Function.uncurry M)).2 ?_
        constructor
        · simpa using hM
        · simp
      · rintro ⟨y, hy⟩
        -- Conversely, every relaxation witness comes from the associated doubly stochastic matrix.
        let hrel :=
          (exercise_4_1_relaxation_iff_matrix_mem_doublyStochastic x y).1 hy
        exact ⟨Function.curry y, hrel.1, hrel.2.symm⟩

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this file uses the
-- concrete row/column-incidence matrix for the textbook system together with the chapter's
-- `Module.finrank ℝ (affineSpan ℝ S).direction` convention for dimensions.

/-- The matrix of the `2n` row-sum and column-sum equations defining the assignment polytope,
with rows indexed by `Fin n ⊕ Fin n` and variables indexed by pairs `(i, j)`. -/
def assignment_constraint_matrix (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n × Fin n) ℝ :=
  fun r c ↦
    match r with
    | Sum.inl i => if c.1 = i then 1 else 0
    | Sum.inr j => if c.2 = j then 1 else 0

/-- On a row-equation index `inl i`, the assignment-constraint matrix records whether the first
coordinate of the variable index is `i`. -/
theorem assignment_constraint_matrix_apply_inl (n : ℕ) (i i' j : Fin n) :
    assignment_constraint_matrix n (Sum.inl i) (i', j) = if i' = i then 1 else 0 := by
  rfl

/-- On a column-equation index `inr j`, the assignment-constraint matrix records whether the
second coordinate of the variable index is `j`. -/
theorem assignment_constraint_matrix_apply_inr (n : ℕ) (j i j' : Fin n) :
    assignment_constraint_matrix n (Sum.inr j) (i, j') = if j' = j then 1 else 0 := by
  rfl

/-- The assignment polytope in `ℝ^{n^2}`, written with coordinates indexed by pairs `(i, j)` as
the pair-indexed view of the canonical doubly stochastic-matrix owner. -/
def assignment_polytope (n : ℕ) : Set (Fin n × Fin n → ℝ) :=
  (fun x ↦ Matrix.of (fun i j ↦ x (i, j))) ⁻¹'
    (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))

/-- A point of `ℝ^{n^2}` belongs to the assignment polytope exactly when each row sum and column
sum is `1` and all coordinates are nonnegative. -/
theorem mem_assignment_polytope_iff {n : ℕ} {x : Fin n × Fin n → ℝ} :
    x ∈ assignment_polytope n ↔
      (∀ i : Fin n, ∑ j : Fin n, x (i, j) = 1) ∧
        (∀ j : Fin n, ∑ i : Fin n, x (i, j) = 1) ∧
          ∀ i j : Fin n, 0 ≤ x (i, j) := by
  change (Matrix.of (fun i j ↦ x (i, j))) ∈ doublyStochastic ℝ (Fin n) ↔
      (∀ i : Fin n, ∑ j : Fin n, x (i, j) = 1) ∧
        (∀ j : Fin n, ∑ i : Fin n, x (i, j) = 1) ∧
          ∀ i j : Fin n, 0 ≤ x (i, j)
  rw [mem_doublyStochastic_iff_sum]
  constructor
  · rintro ⟨hnonneg, hrow, hcol⟩
    exact ⟨fun i ↦ by simpa [Matrix.of_apply] using hrow i,
      fun j ↦ by simpa [Matrix.of_apply] using hcol j,
      fun i j ↦ by simpa [Matrix.of_apply] using hnonneg i j⟩
  · rintro ⟨hrow, hcol, hnonneg⟩
    exact ⟨fun i j ↦ by simpa [Matrix.of_apply] using hnonneg i j,
      fun i ↦ by simpa [Matrix.of_apply] using hrow i,
      fun j ↦ by simpa [Matrix.of_apply] using hcol j⟩

/-- Helper for Example 3.18: in the positive-size case, the textbook lower-bound argument uses the
diagonal columns and the superdiagonal columns. -/
def assignment_selected_column (n : ℕ) : Fin (n + 1) ⊕ Fin n → Fin (n + 1) × Fin (n + 1)
  | Sum.inl i => (i, i)
  | Sum.inr i => (i.castSucc, i.succ)

/-- Helper for Example 3.18: evaluating the selected-column combination at the first column-sum row
isolates the first diagonal coefficient. -/
theorem assignment_selected_columns_sum_apply_inr_zero
    (n : ℕ) (g : Fin (n + 1) ⊕ Fin n → ℝ) :
    (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
      (Sum.inr 0) =
      g (Sum.inl 0) := by
  -- Only the `(0,0)` diagonal column meets the first column equation.
  simp [assignment_selected_column, Matrix.col, assignment_constraint_matrix_apply_inl,
    assignment_constraint_matrix_apply_inr, Fintype.sum_sum_type]

/-- Helper for Example 3.18: at the `i`th row-sum equation, only the diagonal column `(i,i)` and
the superdiagonal column `(i,i+1)` contribute. -/
theorem assignment_selected_columns_sum_apply_inl_castSucc
    (n : ℕ) (g : Fin (n + 1) ⊕ Fin n → ℝ) (i : Fin n) :
    (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
      (Sum.inl i.castSucc) =
      g (Sum.inl i.castSucc) + g (Sum.inr i) := by
  -- The row equation indexed by `i` sees exactly the two textbook-selected variables in that row.
  simp [assignment_selected_column, Matrix.col, assignment_constraint_matrix_apply_inl,
    assignment_constraint_matrix_apply_inr, Fintype.sum_sum_type]

/-- Helper for Example 3.18: at the `(i+1)`st column-sum equation, only the diagonal column
`(i+1,i+1)` and the superdiagonal column `(i,i+1)` contribute. -/
theorem assignment_selected_columns_sum_apply_inr_succ
    (n : ℕ) (g : Fin (n + 1) ⊕ Fin n → ℝ) (i : Fin n) :
    (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
      (Sum.inr i.succ) =
      g (Sum.inl i.succ) + g (Sum.inr i) := by
  -- The matching column equation contains the same superdiagonal coefficient and the next
  -- diagonal coefficient.
  simp [assignment_selected_column, Matrix.col, assignment_constraint_matrix_apply_inl,
    assignment_constraint_matrix_apply_inr, Fintype.sum_sum_type]

/-- Helper for Example 3.18: the textbook-selected columns are linearly independent. -/
theorem assignment_selected_columns_linearIndependent (n : ℕ) :
    LinearIndependent ℝ
      (fun s : Fin (n + 1) ⊕ Fin n ↦
        (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s)) := by
  -- Eliminate the coefficients in the textbook order: first the first diagonal coefficient, then
  -- alternate row and column equations to kill the superdiagonal and diagonal terms.
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have hdiag0 : g (Sum.inl 0) = 0 := by
    have h := congrArg (fun f ↦ f (Sum.inr 0)) hg
    change
      (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
        (Sum.inr 0) = 0 at h
    rw [assignment_selected_columns_sum_apply_inr_zero] at h
    simpa using h
  have hdiag : ∀ i : Fin (n + 1), g (Sum.inl i) = 0 := by
    refine Fin.induction hdiag0 ?_
    intro i hi
    have hsuper : g (Sum.inr i) = 0 := by
      have h := congrArg (fun f ↦ f (Sum.inl i.castSucc)) hg
      change
        (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
          (Sum.inl i.castSucc) = 0 at h
      rw [assignment_selected_columns_sum_apply_inl_castSucc] at h
      simpa [hi] using h
    have h := congrArg (fun f ↦ f (Sum.inr i.succ)) hg
    change
      (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
        (Sum.inr i.succ) = 0 at h
    rw [assignment_selected_columns_sum_apply_inr_succ] at h
    simpa [hsuper] using h
  cases s with
  | inl i =>
      exact hdiag i
  | inr i =>
      have h := congrArg (fun f ↦ f (Sum.inl i.castSucc)) hg
      change
        (∑ s, g s • (assignment_constraint_matrix (n + 1)).col (assignment_selected_column n s))
          (Sum.inl i.castSucc) = 0 at h
      rw [assignment_selected_columns_sum_apply_inl_castSucc] at h
      simpa [hdiag i.castSucc] using h

/-- Helper for Example 3.18: the selected-column family gives the rank lower bound in the
positive-size case. -/
theorem assignment_constraint_matrix_rank_lower_bound_succ (n : ℕ) :
    2 * (n + 1) - 1 ≤ (assignment_constraint_matrix (n + 1)).rank := by
  let B : Matrix (Fin (n + 1) ⊕ Fin n) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ :=
    (assignment_constraint_matrix (n + 1))ᵀ.submatrix (assignment_selected_column n) id
  have hB_rows :
      LinearIndependent ℝ B.row := by
    -- Transposing turns the selected columns into rows of the submatrix `B`.
    simpa [B, Matrix.row, Matrix.col, Matrix.submatrix_apply, Matrix.transpose_apply]
      using assignment_selected_columns_linearIndependent n
  have hB_rank : B.rank = Fintype.card (Fin (n + 1) ⊕ Fin n) := by
    exact LinearIndependent.rank_matrix hB_rows
  have hsub :
      B.rank ≤ (assignment_constraint_matrix (n + 1))ᵀ.rank := by
    simpa [B] using
      Matrix.rank_submatrix_le (A := (assignment_constraint_matrix (n + 1))ᵀ)
        (r := assignment_selected_column n) (c := id)
  have hcard : Fintype.card (Fin (n + 1) ⊕ Fin n) = 2 * (n + 1) - 1 := by
    simp [Fintype.card_sum, Fintype.card_fin]
    omega
  calc
    2 * (n + 1) - 1 = Fintype.card (Fin (n + 1) ⊕ Fin n) := by
      symm
      exact hcard
    _ = B.rank := by
      symm
      exact hB_rank
    _ ≤ (assignment_constraint_matrix (n + 1))ᵀ.rank := hsub
    _ = (assignment_constraint_matrix (n + 1)).rank := by
      simpa using Matrix.rank_transpose (assignment_constraint_matrix (n + 1))

/-- Helper for Example 3.18: the explicit dependence among the row and column equations gives the
rank upper bound in the positive-size case. -/
theorem assignment_constraint_matrix_rank_upper_bound_succ (n : ℕ) :
    (assignment_constraint_matrix (n + 1)).rank ≤ 2 * (n + 1) - 1 := by
  let relation : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ :=
    Sum.elim (fun _ ↦ (1 : ℝ)) (fun _ ↦ (-1 : ℝ))
  have hrelation_mem :
      relation ∈ LinearMap.ker ((assignment_constraint_matrix (n + 1))ᵀ).mulVecLin := by
    -- Each variable column meets exactly one row equation and one column equation, so the `+1`
    -- and `-1` contributions cancel.
    rw [LinearMap.mem_ker]
    ext c
    rcases c with ⟨i, j⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    calc
      (∑ x : Fin (n + 1), assignment_constraint_matrix (n + 1) (Sum.inl x) (i, j) * relation (Sum.inl x))
          + ∑ x : Fin (n + 1),
              assignment_constraint_matrix (n + 1) (Sum.inr x) (i, j) * relation (Sum.inr x)
          = (1 : ℝ) + (-1 : ℝ) := by
              rw [Fintype.sum_eq_single i]
              · rw [Fintype.sum_eq_single j]
                · simp [assignment_constraint_matrix, relation]
                · intro x hx
                  have hx' : j ≠ x := by
                    simpa [eq_comm] using hx
                  simp [assignment_constraint_matrix, relation, hx']
              · intro x hx
                have hx' : i ≠ x := by
                  simpa [eq_comm] using hx
                simp [assignment_constraint_matrix, relation, hx']
      _ = 0 := by ring
  have hrelation_ne : relation ≠ 0 := by
    -- The relation is nonzero because it takes value `1` on every row-equation index.
    intro h
    have h0 := congrArg (fun f ↦ f (Sum.inl 0)) h
    simp [relation] at h0
  have hker_ne_bot :
      LinearMap.ker ((assignment_constraint_matrix (n + 1))ᵀ).mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨relation, hrelation_mem, hrelation_ne⟩
  have hker_pos :
      1 ≤ Module.finrank ℝ
        (LinearMap.ker ((assignment_constraint_matrix (n + 1))ᵀ).mulVecLin) := by
    exact (Submodule.one_le_finrank_iff).2 hker_ne_bot
  have hkernel_formula :
      Module.finrank ℝ (LinearMap.ker ((assignment_constraint_matrix (n + 1))ᵀ).mulVecLin) =
        Fintype.card (Fin (n + 1) ⊕ Fin (n + 1)) -
          ((assignment_constraint_matrix (n + 1))ᵀ).rank := by
    simpa using
      finrank_matrix_kernel_eq_card_sub_rank ((assignment_constraint_matrix (n + 1))ᵀ)
  rw [hkernel_formula, Fintype.card_sum, Fintype.card_fin] at hker_pos
  have htranspose_rank :
      ((assignment_constraint_matrix (n + 1))ᵀ).rank ≤ 2 * (n + 1) - 1 := by
    omega
  calc
    (assignment_constraint_matrix (n + 1)).rank
        = ((assignment_constraint_matrix (n + 1))ᵀ).rank := by
            symm
            simpa using Matrix.rank_transpose (assignment_constraint_matrix (n + 1))
    _ ≤ 2 * (n + 1) - 1 := htranspose_rank

/-- Helper for Example 3.18: the assignment constraints vanish exactly when all row sums and all
column sums vanish. -/
theorem assignment_constraint_matrix_mulVec_zero_iff {n : ℕ} {v : Fin n × Fin n → ℝ} :
    assignment_constraint_matrix n *ᵥ v = 0 ↔
      (∀ i : Fin n, ∑ j : Fin n, v (i, j) = 0) ∧
        (∀ j : Fin n, ∑ i : Fin n, v (i, j) = 0) := by
  constructor
  · intro h
    constructor
    · intro i
      -- Evaluating the matrix equation at a row-equation index recovers the row sum.
      have hi := congrArg (fun f ↦ f (Sum.inl i)) h
      change ((assignment_constraint_matrix n).row (Sum.inl i)) ⬝ᵥ v = 0 at hi
      simpa [Matrix.row, dotProduct, Fintype.sum_prod_type, assignment_constraint_matrix_apply_inl]
        using hi
    · intro j
      -- Evaluating at a column-equation index recovers the column sum.
      have hj := congrArg (fun f ↦ f (Sum.inr j)) h
      change ((assignment_constraint_matrix n).row (Sum.inr j)) ⬝ᵥ v = 0 at hj
      simpa [Matrix.row, dotProduct, Fintype.sum_prod_type, assignment_constraint_matrix_apply_inr]
        using hj
  · rintro ⟨hrow, hcol⟩
    -- Conversely, the matrix coordinates are exactly the row and column sums.
    ext r
    cases r with
    | inl i =>
        change ((assignment_constraint_matrix n).row (Sum.inl i)) ⬝ᵥ v = 0
        simpa [Matrix.row, dotProduct, Fintype.sum_prod_type, assignment_constraint_matrix_apply_inl]
          using hrow i
    | inr j =>
        change ((assignment_constraint_matrix n).row (Sum.inr j)) ⬝ᵥ v = 0
        simpa [Matrix.row, dotProduct, Fintype.sum_prod_type, assignment_constraint_matrix_apply_inr]
          using hcol j

/-- Helper for Example 3.18: every point in the affine hull of the assignment polytope still
satisfies the row-sum and column-sum equations. -/
theorem affineSpan_assignment_polytope_subset_row_column_solution_set {n : ℕ} :
    (affineSpan ℝ (assignment_polytope n) : Set (Fin n × Fin n → ℝ)) ⊆
      {x | (∀ i : Fin n, ∑ j : Fin n, x (i, j) = 1) ∧
        (∀ j : Fin n, ∑ i : Fin n, x (i, j) = 1)} := by
  intro x hx
  -- The affine span is closed under affine combinations, and the defining equalities are affine.
  refine affineSpan_induction (k := ℝ) (s := assignment_polytope n)
    (p := fun y : Fin n × Fin n → ℝ ↦
      (∀ i : Fin n, ∑ j : Fin n, y (i, j) = 1) ∧
        (∀ j : Fin n, ∑ i : Fin n, y (i, j) = 1)) hx ?_ ?_
  · intro y hy
    rcases mem_assignment_polytope_iff.1 hy with ⟨hrow, hcol, -⟩
    exact ⟨hrow, hcol⟩
  · intro c u v w hu hv hw
    rcases hu with ⟨hu_row, hu_col⟩
    rcases hv with ⟨hv_row, hv_col⟩
    rcases hw with ⟨hw_row, hw_col⟩
    constructor
    · intro i
      calc
        ∑ j : Fin n, (c • (u - v) + w) (i, j)
            = ∑ j : Fin n, (c * (u (i, j) - v (i, j)) + w (i, j)) := by
                rfl
        _ = ∑ j : Fin n, c * (u (i, j) - v (i, j)) + ∑ j : Fin n, w (i, j) := by
              rw [Finset.sum_add_distrib]
        _ = c * ∑ j : Fin n, (u (i, j) - v (i, j)) + ∑ j : Fin n, w (i, j) := by
              rw [Finset.mul_sum]
        _ = c * (∑ j : Fin n, u (i, j) - ∑ j : Fin n, v (i, j)) + ∑ j : Fin n, w (i, j) := by
              rw [Finset.sum_sub_distrib]
        _ = c * (1 - 1) + 1 := by rw [hu_row i, hv_row i, hw_row i]
        _ = 1 := by ring
    · intro j
      calc
        ∑ i : Fin n, (c • (u - v) + w) (i, j)
            = ∑ i : Fin n, (c * (u (i, j) - v (i, j)) + w (i, j)) := by
                rfl
        _ = ∑ i : Fin n, c * (u (i, j) - v (i, j)) + ∑ i : Fin n, w (i, j) := by
              rw [Finset.sum_add_distrib]
        _ = c * ∑ i : Fin n, (u (i, j) - v (i, j)) + ∑ i : Fin n, w (i, j) := by
              rw [Finset.mul_sum]
        _ = c * (∑ i : Fin n, u (i, j) - ∑ i : Fin n, v (i, j)) + ∑ i : Fin n, w (i, j) := by
              rw [Finset.sum_sub_distrib]
        _ = c * (1 - 1) + 1 := by rw [hu_col j, hv_col j, hw_col j]
        _ = 1 := by ring

/-- Helper for Example 3.18: once a feasible base point is fixed, every direction of the affine
hull lies in the kernel of the assignment-constraint matrix. -/
theorem direction_assignment_polytope_le_kernel
    (n : ℕ) (x0 : Fin n × Fin n → ℝ) (hx0 : x0 ∈ assignment_polytope n) :
    (affineSpan ℝ (assignment_polytope n)).direction ≤
      LinearMap.ker (assignment_constraint_matrix n).mulVecLin := by
  have hx0_aff : x0 ∈ affineSpan ℝ (assignment_polytope n) :=
    subset_affineSpan ℝ (assignment_polytope n) hx0
  have hx0_eq := affineSpan_assignment_polytope_subset_row_column_solution_set hx0_aff
  -- Route correction: express a direction as a difference from the fixed feasible point `x0`.
  intro v hv
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff] at hv
  rw [LinearMap.mem_ker]
  change assignment_constraint_matrix n *ᵥ v = 0
  rw [assignment_constraint_matrix_mulVec_zero_iff]
  rcases hv with ⟨x, hx_aff, rfl⟩
  have hx_eq := affineSpan_assignment_polytope_subset_row_column_solution_set hx_aff
  constructor
  · intro i
    calc
      ∑ j : Fin n, (x -ᵥ x0) (i, j)
          = ∑ j : Fin n, (x (i, j) - x0 (i, j)) := by
              rfl
      _ = ∑ j : Fin n, x (i, j) - ∑ j : Fin n, x0 (i, j) := by
              rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hx_eq.1 i, hx0_eq.1 i]
      _ = 0 := by ring
  · intro j
    calc
      ∑ i : Fin n, (x -ᵥ x0) (i, j)
          = ∑ i : Fin n, (x (i, j) - x0 (i, j)) := by
              rfl
      _ = ∑ i : Fin n, x (i, j) - ∑ i : Fin n, x0 (i, j) := by
              rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hx_eq.2 j, hx0_eq.2 j]
      _ = 0 := by ring

/-- Helper for Example 3.18: for positive size, the uniform point with all entries `1 / (n+1)` is
strictly feasible for the nonnegativity constraints. -/
theorem assignment_uniform_point_mem_polytope_succ (n : ℕ) :
    (fun _ : Fin (n + 1) × Fin (n + 1) ↦ (1 : ℝ) / (n + 1)) ∈ assignment_polytope (n + 1) := by
  rw [mem_assignment_polytope_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Every row contains `n + 1` identical entries equal to `1 / (n + 1)`.
    intro i
    have hnn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    calc
      ∑ j : Fin (n + 1), (fun _ : Fin (n + 1) × Fin (n + 1) ↦ (1 : ℝ) / (n + 1)) (i, j)
          = ∑ _j : Fin (n + 1), ((1 : ℝ) / (n + 1)) := by
              rfl
      _ = (n + 1 : ℝ) * ((1 : ℝ) / (n + 1)) := by
            simp [Finset.sum_const, Fintype.card_fin]
      _ = 1 := by
            field_simp [hnn]
  · -- The same constant computation gives each column sum.
    intro j
    have hnn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    calc
      ∑ i : Fin (n + 1), (fun _ : Fin (n + 1) × Fin (n + 1) ↦ (1 : ℝ) / (n + 1)) (i, j)
          = ∑ _i : Fin (n + 1), ((1 : ℝ) / (n + 1)) := by
              rfl
      _ = (n + 1 : ℝ) * ((1 : ℝ) / (n + 1)) := by
            simp [Finset.sum_const, Fintype.card_fin]
      _ = 1 := by
            field_simp [hnn]
  · -- Strict positivity is immediate because `n + 1 > 0`.
    intro i j
    have hpos : (0 : ℝ) < n + 1 := by
      exact_mod_cast Nat.succ_pos n
    exact le_of_lt (one_div_pos.mpr hpos)

/-- Helper for Example 3.18: in the positive-size case, every kernel vector is a direction of the
assignment polytope's affine hull. -/
theorem assignment_kernel_subset_direction_succ (n : ℕ) :
    LinearMap.ker (assignment_constraint_matrix (n + 1)).mulVecLin ≤
      (affineSpan ℝ (assignment_polytope (n + 1))).direction := by
  let x0 : Fin (n + 1) × Fin (n + 1) → ℝ := fun _ ↦ (1 : ℝ) / (n + 1)
  have hx0 : x0 ∈ assignment_polytope (n + 1) := by
    simpa [x0] using assignment_uniform_point_mem_polytope_succ n
  rcases mem_assignment_polytope_iff.1 hx0 with ⟨hx0_row, hx0_col, -⟩
  have hx0_aff : x0 ∈ affineSpan ℝ (assignment_polytope (n + 1)) :=
    subset_affineSpan ℝ (assignment_polytope (n + 1)) hx0
  intro v hv
  rw [LinearMap.mem_ker] at hv
  change assignment_constraint_matrix (n + 1) *ᵥ v = 0 at hv
  rw [assignment_constraint_matrix_mulVec_zero_iff] at hv
  rcases hv with ⟨hv_row, hv_col⟩
  let C : ℝ := ∑ p : Fin (n + 1) × Fin (n + 1), |v p|
  let ε : ℝ := ((1 : ℝ) / (n + 1)) / (C + 1)
  let x : Fin (n + 1) × Fin (n + 1) → ℝ := x0 + ε • v
  have hC_nonneg : 0 ≤ C := by
    exact Finset.sum_nonneg fun p hp ↦ abs_nonneg (v p)
  have hε_pos : 0 < ε := by
    apply div_pos
    · exact one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
    · linarith
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hbound : ∀ p : Fin (n + 1) × Fin (n + 1), |v p| ≤ C := by
    intro p
    let rest : ℝ := Finset.sum (Finset.univ.erase p) fun q ↦ |v q|
    have hsplit : C = |v p| + rest := by
      simp [rest, C, Finset.sum_erase_add, Finset.mem_univ]
    have hrest_nonneg : 0 ≤ rest := by
      exact Finset.sum_nonneg fun q hq ↦ abs_nonneg (v q)
    linarith
  have hεC_le : ε * C ≤ (1 : ℝ) / (n + 1) := by
    have hC1_pos : 0 < C + 1 := by
      linarith
    have hfrac :
        C / (C + 1) ≤ (1 : ℝ) := by
      have hdiv :
          C / (C + 1) ≤ (C + 1) / (C + 1) := by
        exact div_le_div_of_nonneg_right (by linarith) hC1_pos.le
      have hone : (C + 1) / (C + 1) = (1 : ℝ) := by
        field_simp [hC1_pos.ne']
      exact hdiv.trans_eq hone
    have hx0_nonneg : 0 ≤ (1 : ℝ) / (n + 1) := by
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n))
    have hmul := mul_le_mul_of_nonneg_left hfrac hx0_nonneg
    simpa [ε, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hx : x ∈ assignment_polytope (n + 1) := by
    rw [mem_assignment_polytope_iff]
    refine ⟨?_, ?_, ?_⟩
    · -- The kernel equations preserve every row sum.
      intro i
      calc
        ∑ j : Fin (n + 1), x (i, j)
            = ∑ j : Fin (n + 1), (x0 (i, j) + ε * v (i, j)) := by
                rfl
        _ = (∑ j : Fin (n + 1), x0 (i, j)) + ∑ j : Fin (n + 1), ε * v (i, j) := by
              rw [Finset.sum_add_distrib]
        _ = (∑ j : Fin (n + 1), x0 (i, j)) + ε * (∑ j : Fin (n + 1), v (i, j)) := by
              rw [Finset.mul_sum]
        _ = 1 + ε * 0 := by rw [hx0_row i, hv_row i]
        _ = 1 := by ring
    · -- The same kernel equations preserve every column sum.
      intro j
      calc
        ∑ i : Fin (n + 1), x (i, j)
            = ∑ i : Fin (n + 1), (x0 (i, j) + ε * v (i, j)) := by
                rfl
        _ = (∑ i : Fin (n + 1), x0 (i, j)) + ∑ i : Fin (n + 1), ε * v (i, j) := by
              rw [Finset.sum_add_distrib]
        _ = (∑ i : Fin (n + 1), x0 (i, j)) + ε * (∑ i : Fin (n + 1), v (i, j)) := by
              rw [Finset.mul_sum]
        _ = 1 + ε * 0 := by rw [hx0_col j, hv_col j]
        _ = 1 := by ring
    · -- The strict positivity of `x0` and the smallness of `ε` keep all coordinates nonnegative.
      intro i j
      have hij_bound : ε * |v (i, j)| ≤ (1 : ℝ) / (n + 1) := by
        exact le_trans (mul_le_mul_of_nonneg_left (hbound (i, j)) hε_nonneg) hεC_le
      have hbase : 0 ≤ (1 : ℝ) / (n + 1) - ε * |v (i, j)| := by
        linarith
      have hcompare :
          (1 : ℝ) / (n + 1) - ε * |v (i, j)| ≤
            (1 : ℝ) / (n + 1) + ε * v (i, j) := by
        have hnegabs : -|v (i, j)| ≤ v (i, j) := neg_abs_le (v (i, j))
        have hmul : ε * (-|v (i, j)|) ≤ ε * v (i, j) := by
          exact mul_le_mul_of_nonneg_left hnegabs hε_nonneg
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
          add_le_add_left hmul ((1 : ℝ) / (n + 1))
      have hnonneg :
          0 ≤ (1 : ℝ) / (n + 1) + ε * v (i, j) := by
        exact le_trans hbase hcompare
      simpa [x0, x] using hnonneg
  have hεv_mem :
      ε • v ∈ (affineSpan ℝ (assignment_polytope (n + 1))).direction := by
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx0_aff]
    refine ⟨x, subset_affineSpan ℝ (assignment_polytope (n + 1)) hx, ?_⟩
    -- The chosen point is exactly the translate of `x0` by the scaled kernel vector `ε • v`.
    change ε • v = x - x0
    dsimp [x]
    abel
  have hv_mem :
      v ∈ (affineSpan ℝ (assignment_polytope (n + 1))).direction := by
    have hscaled :=
      (affineSpan ℝ (assignment_polytope (n + 1))).direction.smul_mem ε⁻¹ hεv_mem
    simpa [hε_pos.ne', smul_smul] using hscaled
  exact hv_mem

/-- Example 3.18 (1). The matrix of the row-sum and column-sum equations defining the assignment
polytope has rank `2n - 1`. -/
theorem assignment_constraint_matrix_rank (n : ℕ) :
    (assignment_constraint_matrix n).rank = 2 * n - 1 := by
  cases n with
  | zero =>
      -- For `n = 0`, the matrix has no rows and no columns, so its rank is `0`.
      have hA : assignment_constraint_matrix 0 = 0 := by
        ext r c
        exact Fin.elim0 c.1
      simpa [hA]
  | succ n =>
      -- For positive size, the upper and lower bounds match the textbook value.
      exact le_antisymm
        (assignment_constraint_matrix_rank_upper_bound_succ n)
        (assignment_constraint_matrix_rank_lower_bound_succ n)

/-- Example 3.18 (2). The assignment polytope has dimension `n^2 - 2n + 1`; in natural-number
arithmetic we record this as `n^2 - (2n - 1)`. -/
theorem assignment_polytope_finrank_direction_affineSpan (n : ℕ) :
    Module.finrank ℝ (affineSpan ℝ (assignment_polytope n)).direction =
      n * n - (2 * n - 1) := by
  cases n with
  | zero =>
      -- The ambient space for `n = 0` is zero-dimensional, so the affine-span direction is too.
      apply Nat.eq_zero_of_le_zero
      simpa using
        (Submodule.finrank_le (affineSpan ℝ (assignment_polytope 0)).direction :
          Module.finrank ℝ (affineSpan ℝ (assignment_polytope 0)).direction ≤
            Module.finrank ℝ (Fin 0 × Fin 0 → ℝ))
  | succ n =>
      have hx0 : (fun _ : Fin (n + 1) × Fin (n + 1) ↦ (1 : ℝ) / (n + 1)) ∈
          assignment_polytope (n + 1) := assignment_uniform_point_mem_polytope_succ n
      have hdir_le_ker :
          Module.finrank ℝ (affineSpan ℝ (assignment_polytope (n + 1))).direction ≤
            Module.finrank ℝ
              (LinearMap.ker (assignment_constraint_matrix (n + 1)).mulVecLin) :=
        Submodule.finrank_mono
          (direction_assignment_polytope_le_kernel (n + 1)
            (fun _ ↦ (1 : ℝ) / (n + 1)) hx0)
      have hker_le_dir :
          Module.finrank ℝ
              (LinearMap.ker (assignment_constraint_matrix (n + 1)).mulVecLin) ≤
            Module.finrank ℝ (affineSpan ℝ (assignment_polytope (n + 1))).direction :=
        Submodule.finrank_mono (assignment_kernel_subset_direction_succ n)
      calc
        Module.finrank ℝ (affineSpan ℝ (assignment_polytope (n + 1))).direction
            = Module.finrank ℝ
                (LinearMap.ker (assignment_constraint_matrix (n + 1)).mulVecLin) := by
                  exact le_antisymm hdir_le_ker hker_le_dir
        _ = Fintype.card (Fin (n + 1) × Fin (n + 1)) -
              (assignment_constraint_matrix (n + 1)).rank := by
                simpa using
                  finrank_matrix_kernel_eq_card_sub_rank
                    (assignment_constraint_matrix (n + 1))
        _ = (n + 1) * (n + 1) - (2 * (n + 1) - 1) := by
              rw [assignment_constraint_matrix_rank]
              simp [Fintype.card_prod, Fintype.card_fin]

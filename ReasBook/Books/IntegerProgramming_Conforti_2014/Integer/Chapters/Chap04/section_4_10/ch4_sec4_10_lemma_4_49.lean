import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10.ch4_sec4_10_definition_4_10_extra_2

open Matrix
open scoped Matrix NonnegativeRankNotation

section LinearOrderedField

variable {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Nonnegative row and column scalings preserve entrywise nonnegativity, even after reindexing
rows and columns. -/
theorem row_col_scaling_reindex_nonneg
    (S : Matrix m n R)
    (σ : Equiv.Perm m)
    (τ : Equiv.Perm n)
    (r : m → R)
    (c : n → R)
    (hS_nonneg : 0 ≤ S)
    (hr : ∀ i, 0 ≤ r i)
    (hc : ∀ j, 0 ≤ c j) :
    0 ≤ diagonal r * (S.reindex σ τ) * diagonal c := by
  intro i j
  -- Evaluate the transformed entry and multiply the three nonnegative factors.
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simpa [Matrix.reindex_apply, mul_assoc] using
    mul_nonneg (mul_nonneg (hr i) (hS_nonneg (σ.symm i) (τ.symm j))) (hc j)

/-- Positive row and column scalings preserve entrywise nonnegativity after row and column
reindexing. -/
theorem row_col_scaling_reindex_nonneg_of_pos
    (S : Matrix m n R)
    (σ : Equiv.Perm m)
    (τ : Equiv.Perm n)
    (r : m → R)
    (c : n → R)
    (hS_nonneg : 0 ≤ S)
    (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    0 ≤ diagonal r * (S.reindex σ τ) * diagonal c :=
  row_col_scaling_reindex_nonneg S σ τ r c hS_nonneg
    (fun i ↦ le_of_lt (hr i))
    (fun j ↦ le_of_lt (hc j))

/-- A nonnegative factorization transports across row/column reindexing and nonnegative diagonal
scalings. -/
theorem has_nonnegative_rank_factorization_row_col_scaling_reindex
    {t : ℕ}
    {S : Matrix m n R}
    (σ : Equiv.Perm m)
    (τ : Equiv.Perm n)
    (r : m → R)
    (c : n → R)
    (hr : ∀ i, 0 ≤ r i)
    (hc : ∀ j, 0 ≤ c j)
    (hfact : has_nonnegative_rank_factorization S t) :
    has_nonnegative_rank_factorization (diagonal r * (S.reindex σ τ) * diagonal c) t := by
  rcases (has_nonnegative_rank_factorization_iff).1 hfact with ⟨F, W, hF, hW, hmul⟩
  have hreindex_mul :
      (F.reindex σ (Equiv.refl _)) * (W.reindex (Equiv.refl _) τ) = S.reindex σ τ := by
    -- Reindexing the two factors separately is the same as reindexing their product.
    calc
      (F.reindex σ (Equiv.refl _)) * (W.reindex (Equiv.refl _) τ)
          = (F * W).reindex σ τ := by
              simpa [Matrix.reindex_apply] using
                (Matrix.submatrix_mul_equiv F W σ.symm (Equiv.refl (Fin t)) τ.symm)
      _ = S.reindex σ τ := by
        rw [← hmul]
  refine (has_nonnegative_rank_factorization_iff).2 ?_
  refine ⟨diagonal r * (F.reindex σ (Equiv.refl _)),
    (W.reindex (Equiv.refl _) τ) * diagonal c, ?_, ?_, ?_⟩
  · intro i j
    -- The left factor only scales reindexed rows, so nonnegativity is entrywise immediate.
    rw [Matrix.diagonal_mul]
    simpa [Matrix.reindex_apply] using mul_nonneg (hr i) (hF (σ.symm i) j)
  · intro i j
    -- The right factor only scales reindexed columns, so nonnegativity is also entrywise.
    rw [Matrix.mul_diagonal]
    simpa [Matrix.reindex_apply] using mul_nonneg (hW i (τ.symm j)) (hc j)
  · -- Normalize the transported product back to the target scaled-and-reindexed matrix.
    calc
      diagonal r * (S.reindex σ τ) * diagonal c
          = diagonal r * ((F.reindex σ (Equiv.refl _)) * (W.reindex (Equiv.refl _) τ)) *
              diagonal c := by
              rw [hreindex_mul]
      _ = (diagonal r * (F.reindex σ (Equiv.refl _))) *
            ((W.reindex (Equiv.refl _) τ) * diagonal c) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc]

omit [IsStrictOrderedRing R] in
/-- Helper for Lemma 4.49: reindexing back and applying reciprocal diagonal scalings recovers the
original matrix. -/
lemma undo_row_col_scaling_reindex
    (S : Matrix m n R)
    (σ : Equiv.Perm m)
    (τ : Equiv.Perm n)
    (r : m → R)
    (c : n → R)
    (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    diagonal (fun i ↦ (r (σ i))⁻¹) *
        ((diagonal r * (S.reindex σ τ) * diagonal c).reindex σ.symm τ.symm) *
        diagonal (fun j ↦ (c (τ j))⁻¹) =
      S := by
  ext i j
  have hr_ne : r (σ i) ≠ 0 := ne_of_gt (hr (σ i))
  have hc_ne : c (τ j) ≠ 0 := ne_of_gt (hc (τ j))
  -- Evaluate the entry after reindexing back, so the inverse scalings cancel explicitly.
  simp [Matrix.reindex_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hr_ne, hc_ne, mul_assoc]

/-- Positive row and column scalings together with row/column reindexing preserve nonnegative
rank. This is the generic matrix-equivalence lemma underlying Lemma 4.49. -/
theorem nonnegative_rank_eq_of_matrix_row_col_scaling_reindex
    (S : Matrix.Nonnegative m n R)
    (σ : Equiv.Perm m)
    (τ : Equiv.Perm n)
    (r : m → R)
    (c : n → R)
    (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    rank₊
      ⟨diagonal r * ((S : Matrix m n R).reindex σ τ) * diagonal c,
        row_col_scaling_reindex_nonneg_of_pos (S : Matrix m n R) σ τ r c S.2 hr hc⟩ =
      rank₊ S := by
  let T : Matrix.Nonnegative m n R :=
    ⟨diagonal r * ((S : Matrix m n R).reindex σ τ) * diagonal c,
      row_col_scaling_reindex_nonneg_of_pos (S : Matrix m n R) σ τ r c S.2 hr hc⟩
  let rinv : m → R := fun i ↦ (r (σ i))⁻¹
  let cinv : n → R := fun j ↦ (c (τ j))⁻¹
  have hforward :
      rank₊ T ≤ rank₊ S := by
    have hleast := nonnegative_rank_isLeast S
    -- Transport a minimal factorization of `S` to a factorization of the transformed matrix.
    exact nonnegative_rank_le_of_has_nonnegative_rank_factorization
      (has_nonnegative_rank_factorization_row_col_scaling_reindex σ τ r c
        (fun i ↦ le_of_lt (hr i))
        (fun j ↦ le_of_lt (hc j))
        hleast.1)
  have hreverse :
      rank₊ S ≤ rank₊ T := by
    have hleast := nonnegative_rank_isLeast T
    have hback :
        has_nonnegative_rank_factorization
          (diagonal rinv * ((T : Matrix m n R).reindex σ.symm τ.symm) * diagonal cinv)
          (rank₊ T) := by
      -- Apply the same transport lemma to the inverse permutations and reciprocal scalings.
      exact has_nonnegative_rank_factorization_row_col_scaling_reindex σ.symm τ.symm rinv cinv
        (fun i ↦ le_of_lt (inv_pos.mpr (hr (σ i))))
        (fun j ↦ le_of_lt (inv_pos.mpr (hc (τ j))))
        hleast.1
    have hback_eq :
        has_nonnegative_rank_factorization (S : Matrix m n R)
          (rank₊ T) := by
      have hundo :
          diagonal rinv * ((T : Matrix m n R).reindex σ.symm τ.symm) * diagonal cinv =
            (S : Matrix m n R) := by
        -- The inverse transport really reconstructs the original matrix.
        simpa [T, rinv, cinv, Matrix.reindex_apply] using
          (undo_row_col_scaling_reindex (S := (S : Matrix m n R)) σ τ r c hr hc)
      rw [hundo] at hback
      exact hback
    exact nonnegative_rank_le_of_has_nonnegative_rank_factorization hback_eq
  -- The two transported minimal factorizations give both inequalities.
  simpa [T] using le_antisymm hforward hreverse

end LinearOrderedField

/-- Lemma 4.49. Two slack matrices that differ only by row and column permutations together with
positive row and column scalings have the same nonnegative rank. -/
theorem nonnegative_rank_eq_of_row_col_scaling_reindex
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (vertices : Fin p → Fin n → ℝ)
    (A' : Matrix (Fin m) (Fin n) ℝ)
    (b' : Fin m → ℝ)
    (vertices' : Fin p → Fin n → ℝ)
    (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin p))
    (r : Fin m → ℝ)
    (c : Fin p → ℝ)
    (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (hS_nonneg : 0 ≤ slack_matrix A b vertices)
    (hscaled :
      slack_matrix A' b' vertices' =
        diagonal r * (slack_matrix A b vertices).reindex σ τ * diagonal c) :
    rank₊
      ⟨slack_matrix A' b' vertices', by
        rw [hscaled]
        exact row_col_scaling_reindex_nonneg_of_pos
          (slack_matrix A b vertices) σ τ r c hS_nonneg hr hc⟩ =
      rank₊ ⟨slack_matrix A b vertices, hS_nonneg⟩ := by
  simpa [hscaled] using nonnegative_rank_eq_of_matrix_row_col_scaling_reindex
    ⟨slack_matrix A b vertices, hS_nonneg⟩ σ τ r c hr hc

import Mathlib

open scoped BigOperators
open Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: the policy-requested Lean semantic search tool `lean_leansearch` was
-- unavailable in this session, so the statement below was matched against local determinant-file
-- conventions by direct repository inspection.

section Exercise98

/-- Helper for Exercise 9.8: the standard Euclidean basis determinant of the column family of a
matrix is the matrix determinant. -/
lemma basisFun_det_matrix_cols_eq_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (fun j ↦ WithLp.toLp 2 (B.col j)) = B.det := by
  -- Route correction: use the current `WithLp.toLp` Euclidean-space coercion.
  -- In the standard Euclidean basis, the coordinate matrix of the columns is definitionally `B`.
  rw [Module.Basis.det_apply]
  congr 1

/-- Helper for Exercise 9.8: Hadamard's inequality for families of vectors in the standard
Euclidean basis. -/
lemma abs_basisFun_det_le_prod_norm {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v| ≤ ∏ i, ‖v i‖ := by
  -- Route correction: derive the orientation from the Euclidean basis instead of relying on an
  -- unavailable `Module.Oriented` instance.
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by
    simp⟩
  -- The absolute value of the determinant agrees with the absolute value of the volume form.
  simpa [o.volumeForm_robust' (EuclideanSpace.basisFun (Fin n) ℝ) v] using
    o.abs_volumeForm_apply_le v

/-- Helper for Exercise 9.8: an entrywise bound controls the Euclidean norm of each column. -/
lemma matrix_col_norm_le_sqrt_card_mul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM_bound : ∀ i j, |B i j| ≤ M) :
    ∀ j, ‖WithLp.toLp 2 (B.col j)‖ ≤ Real.sqrt n * M := by
  intro j
  -- Square both sides to compare the Euclidean norm with the sum of coordinate squares.
  have hsq : ‖WithLp.toLp 2 (B.col j)‖ ^ 2 ≤ (Real.sqrt n * M) ^ 2 := by
    -- Square both sides so the Euclidean norm becomes a sum of squares.
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, (B.col j i) ^ 2 ≤ ∑ i : Fin n, M ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : |B i j| ≤ M := hM_bound i j
        have hleft : -M ≤ B i j := (abs_le.mp hij).1
        have hright : B i j ≤ M := (abs_le.mp hij).2
        simp [Matrix.col_apply]
        nlinarith
      _ = n * M ^ 2 := by simp
      _ = (Real.sqrt n * M) ^ 2 := by
        calc
          (n : ℝ) * M ^ 2 = (Real.sqrt n) ^ 2 * M ^ 2 := by
            rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
          _ = (Real.sqrt n * M) ^ 2 := by ring
  have hright_nonneg : 0 ≤ Real.sqrt n * M := mul_nonneg (Real.sqrt_nonneg _) hM0
  -- With both sides nonnegative, the squared estimate implies the norm estimate.
  nlinarith [hsq, norm_nonneg (WithLp.toLp 2 (B.col j)), hright_nonneg]

/-- Helper for Exercise 9.8: the constant product `(√n M)^n` is the same as
`n^(n/2) M^n` in the `Real.rpow` notation used by the chapter. -/
lemma sqrt_card_mul_pow_eq_rpow_card_div_two_mul_pow {n : ℕ} (M : ℝ) :
    (Real.sqrt n * M) ^ n = Real.rpow (n : ℝ) ((n : ℝ) / 2) * M ^ n := by
  -- Separate the `√n` contribution from the `M` contribution.
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (show 0 ≤ (n : ℝ) by positivity)]
  congr 1
  ring

/-- Helper for Exercise 9.8: the determinant bound in the concrete `Fin n` indexing model. -/
lemma abs_det_le_rpow_card_div_two_mul_pow_fin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (M : ℝ) (hM_bound : ∀ i j, |B i j| ≤ M) :
    |B.det| ≤ Real.rpow (n : ℝ) ((n : ℝ) / 2) * M ^ n := by
  cases n with
  | zero =>
      -- In dimension `0`, both the determinant and the right-hand side are `1`.
      simp
  | succ n =>
      -- In the nonempty case, one entry bound already forces `M` to be nonnegative.
      have hM0 : 0 ≤ M := by
        have h00 : |B 0 0| ≤ M := hM_bound 0 0
        exact le_trans (abs_nonneg _) h00
      calc
        |B.det| =
            |(EuclideanSpace.basisFun (Fin n.succ) ℝ).toBasis.det
                (fun j ↦ WithLp.toLp 2 (B.col j))| := by
              rw [basisFun_det_matrix_cols_eq_det]
        _ ≤ ∏ j, ‖WithLp.toLp 2 (B.col j)‖ := abs_basisFun_det_le_prod_norm _
        _ ≤ ∏ _j : Fin n.succ, Real.sqrt n.succ * M := by
              apply Finset.prod_le_prod
              · intro j hj
                exact norm_nonneg _
              · intro j hj
                exact matrix_col_norm_le_sqrt_card_mul B hM0 hM_bound j
        _ = (Real.sqrt n.succ * M) ^ n.succ := by simp
        _ = Real.rpow (n.succ : ℝ) ((n.succ : ℝ) / 2) * M ^ n.succ := by
              rw [sqrt_card_mul_pow_eq_rpow_card_div_two_mul_pow]

/-- Exercise 9.8. If every entry of the real square matrix `B` has absolute value at most `M`,
then `|det B| ≤ (card ι)^((card ι)/2) M^(card ι)`. For `ι = Fin n`, this is the textbook bound
`|det B| ≤ n^(n/2) M^n`. In particular this applies when `M` is the absolute value of a largest
entry of `B`. -/
theorem abs_det_le_rpow_card_div_two_mul_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ)
    (M : ℝ)
    (hM_bound : ∀ i j, |B i j| ≤ M) :
    |B.det| ≤
      Real.rpow (Fintype.card ι : ℝ) ((Fintype.card ι : ℝ) / 2) * M ^ Fintype.card ι := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let B' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := B.reindex e e
  -- Reindex to `Fin (card ι)` so the Euclidean-space Hadamard inequality applies directly.
  have hdet : |B.det| = |B'.det| := by
    simpa [B'] using (Matrix.abs_det_reindex e e B).symm
  have hB'_bound : ∀ i j, |B' i j| ≤ M := by
    intro i j
    simpa [B', Matrix.reindex_apply] using hM_bound (e.symm i) (e.symm j)
  calc
    |B.det| = |B'.det| := hdet
    _ ≤ Real.rpow (Fintype.card ι : ℝ) ((Fintype.card ι : ℝ) / 2) * M ^ Fintype.card ι :=
      abs_det_le_rpow_card_div_two_mul_pow_fin B' M hB'_bound

end Exercise98

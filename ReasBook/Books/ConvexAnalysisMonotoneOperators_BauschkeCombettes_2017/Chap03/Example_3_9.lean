/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8

noncomputable section

open scoped Matrix.Norms.Frobenius

private abbrev rankLESet (M N q : ℕ) : Set (Matrix (Fin M) (Fin N) ℝ) :=
  { B | B.rank ≤ q }

private lemma mem_rankLESet_iff {M N q : ℕ} {B : Matrix (Fin M) (Fin N) ℝ} :
    B ∈ rankLESet M N q ↔ B.rank ≤ q :=
  Iff.rfl

private lemma isBestApproximation_iff_mem_and_norm_sub_eq_infDist {M N : ℕ}
    {A P : Matrix (Fin M) (Fin N) ℝ} {C : Set (Matrix (Fin M) (Fin N) ℝ)} :
    IsBestApproximation A C P ↔ P ∈ C ∧ ‖A - P‖ = Metric.infDist A C := by
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  simp [dist_eq_norm]

private lemma isBestApproximation_iff_mem_and_forall_norm_sub_le {M N : ℕ}
    {A P : Matrix (Fin M) (Fin N) ℝ} {C : Set (Matrix (Fin M) (Fin N) ℝ)} :
    IsBestApproximation A C P ↔ P ∈ C ∧ ∀ B ∈ C, ‖A - P‖ ≤ ‖A - B‖ := by
  rw [isBestApproximation_iff_mem_and_norm_sub_eq_infDist]
  constructor
  · rintro ⟨hP, hdist⟩
    refine ⟨hP, fun B hB ↦ ?_⟩
    rw [hdist]
    simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := A) hB
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, le_antisymm ?_ (Metric.infDist_le_dist_of_mem (x := A) hP)⟩
    exact (Metric.le_infDist (x := A) (s := C) ⟨P, hP⟩).2 fun B hB ↦ by
      simpa [dist_eq_norm] using hmin B hB

/-- The rectangular diagonal matrix whose diagonal entries are the singular values of `A`. -/
def singularValueDiagonal {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun i j ↦ if i.1 = j.1 then (Matrix.toEuclideanLin A).singularValues i.1 else 0

-- Proof sketch: unfold `singularValueDiagonal` and evaluate the defining `if` on the diagonal.
/-- On diagonal indices, `singularValueDiagonal A` records the singular values of `A`. -/
lemma singularValueDiagonal_apply_diag {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin (min M N)) :
    singularValueDiagonal A ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_left M N)⟩
        ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right M N)⟩ =
      (Matrix.toEuclideanLin A).singularValues i.1 := by
  -- On matching row and column indices, the defining `if` takes the diagonal branch.
  simp [singularValueDiagonal]

/-- The diagonal truncation keeping only the first `q` singular values of `A`. -/
def truncatedSingularValueDiagonal {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun i j ↦ if i.1 = j.1 ∧ i.1 < q then (Matrix.toEuclideanLin A).singularValues i.1 else 0

-- Proof sketch: unfold `truncatedSingularValueDiagonal` and use the hypotheses `i = j` and
-- `i.1 < q` to trigger the defining branch.
/-- Below the truncation index, `truncatedSingularValueDiagonal A q` agrees with the singular value
diagonal of `A`. -/
lemma truncatedSingularValueDiagonal_apply_of_lt {M N q : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    {i : Fin M} {j : Fin N} (hij : i.1 = j.1) (hi : i.1 < q) :
    truncatedSingularValueDiagonal A q i j = (Matrix.toEuclideanLin A).singularValues i.1 := by
  -- The truncation keeps diagonal entries whose index is strictly below `q`.
  have hj : j.1 < q := hij.symm ▸ hi
  simp [truncatedSingularValueDiagonal, hij, hj]

/-- Helper for Example 3.9: the left factor carrying the first `q` singular values of `A`. -/
private def truncatedSingularValueLeftFactor {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ) :
    Matrix (Fin M) (Fin q) ℝ :=
  fun i k ↦ if i.1 = k.1 then (Matrix.toEuclideanLin A).singularValues i.1 else 0

/-- Helper for Example 3.9: the right factor selecting the first `q` coordinate columns. -/
private def truncatedSingularValueRightFactor {N q : ℕ} :
    Matrix (Fin q) (Fin N) ℝ :=
  fun k j ↦ if k.1 = j.1 then 1 else 0

/-- Helper for Example 3.9: the truncated singular-value diagonal factors through `ℝ^q`. -/
private lemma truncatedSingularValueDiagonal_factorization {M N q : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) :
    truncatedSingularValueDiagonal A q =
      truncatedSingularValueLeftFactor A q * truncatedSingularValueRightFactor (N := N) := by
  ext i j
  -- Separate the cases according to whether the row index survives the truncation.
  by_cases hiq : i.1 < q
  · let k : Fin q := ⟨i.1, hiq⟩
    by_cases hij : i.1 = j.1
    · -- When `i = j` and `i < q`, exactly one summand survives in the matrix product.
      have hj : j.1 < q := hij.symm ▸ hiq
      change truncatedSingularValueDiagonal A q i j =
        ∑ l : Fin q,
          truncatedSingularValueLeftFactor A q i l *
            truncatedSingularValueRightFactor (N := N) l j
      rw [Finset.sum_eq_single k]
      · simp [truncatedSingularValueLeftFactor, truncatedSingularValueRightFactor,
          truncatedSingularValueDiagonal, hij, hj, k]
      · intro l _ hl
        have hil : i.1 ≠ l.1 := by
          intro h
          have hlk : l = k := by
            apply Fin.ext
            simpa [k] using h.symm
          exact hl hlk
        simp [truncatedSingularValueLeftFactor, hil]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
    · -- When `i ≠ j`, the candidate diagonal summand also vanishes on the right factor.
      change truncatedSingularValueDiagonal A q i j =
        ∑ l : Fin q,
          truncatedSingularValueLeftFactor A q i l *
            truncatedSingularValueRightFactor (N := N) l j
      rw [Finset.sum_eq_single k]
      · simp [truncatedSingularValueLeftFactor, truncatedSingularValueRightFactor,
          truncatedSingularValueDiagonal, hiq, hij, k]
      · intro l _ hl
        have hil : i.1 ≠ l.1 := by
          intro h
          have hlk : l = k := by
            apply Fin.ext
            simpa [k] using h.symm
          exact hl hlk
        simp [truncatedSingularValueLeftFactor, hil]
      · intro hk
        exact False.elim (hk (Finset.mem_univ k))
  · -- If `i ≥ q`, every entry in the `i`-th row of the left factor is zero.
    change truncatedSingularValueDiagonal A q i j =
      ∑ l : Fin q,
        truncatedSingularValueLeftFactor A q i l *
          truncatedSingularValueRightFactor (N := N) l j
    have hleft : ∀ l : Fin q, truncatedSingularValueLeftFactor A q i l = 0 := by
      intro l
      have hil : i.1 ≠ l.1 := by
        intro h
        exact hiq (h ▸ l.2)
      simp [truncatedSingularValueLeftFactor, hil]
    simp [truncatedSingularValueDiagonal, hiq, hleft]

/-- Helper for Example 3.9: truncating the singular-value diagonal yields a matrix of rank at most
`q`. -/
private lemma truncated_singular_value_diagonal_rank_le {M N q : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) :
    (truncatedSingularValueDiagonal A q).rank ≤ q := by
  -- Factor the truncation through `ℝ^q`, then bound the intermediate rank by the width `q`.
  rw [truncatedSingularValueDiagonal_factorization]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  exact Matrix.rank_le_width _

/-- The rank-`q` truncation associated to a chosen singular value decomposition of `A`. -/
def eckartYoungApproximation {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  ((U : Matrix (Fin M) (Fin M) ℝ) * truncatedSingularValueDiagonal A q) *
    Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)

/-- Helper for Example 3.9: transporting the chosen SVD by the orthogonal factors recovers the
singular-value diagonal. -/
private lemma svd_coordinates_eq_singularValueDiagonal {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd :
      A =
        ((U : Matrix (Fin M) (Fin M) ℝ) * singularValueDiagonal A) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) :
    Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A * (V : Matrix (Fin N) (Fin N) ℝ) =
      singularValueDiagonal A := by
  -- Multiply the SVD identity on the left by `Uᵀ` and on the right by `V`.
  have h :=
    congrArg
      (fun X : Matrix (Fin M) (Fin N) ℝ =>
        Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X *
          (V : Matrix (Fin N) (Fin N) ℝ))
      hsvd
  have hU :
      Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (U : Matrix (Fin M) (Fin M) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin M) (R := ℝ)).mp U.2
  have hV :
      Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
          (V : Matrix (Fin N) (Fin N) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp V.2
  have h' :
      Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (A * (V : Matrix (Fin N) (Fin N) ℝ)) =
        Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          ((U : Matrix (Fin M) (Fin M) ℝ) * singularValueDiagonal A) := by
    simpa [Matrix.mul_assoc, hV] using h
  calc
    Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A * (V : Matrix (Fin N) (Fin N) ℝ)
        = Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            (A * (V : Matrix (Fin N) (Fin N) ℝ)) := by
              simp [Matrix.mul_assoc]
    _ = Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          ((U : Matrix (Fin M) (Fin M) ℝ) * singularValueDiagonal A) := h'
    _ = (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (U : Matrix (Fin M) (Fin M) ℝ)) * singularValueDiagonal A := by
            rw [← Matrix.mul_assoc]
    _ = singularValueDiagonal A := by
      simp [hU]

/-- Helper for Example 3.9: transporting the chosen truncation to SVD coordinates recovers the
truncated singular-value diagonal. -/
private lemma svd_coordinates_eckartYoungApproximation_eq_truncation {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        eckartYoungApproximation A q U V *
        (V : Matrix (Fin N) (Fin N) ℝ) =
      truncatedSingularValueDiagonal A q := by
  -- Expand the definition of the truncation and cancel the orthogonal factors.
  have hU :
      Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (U : Matrix (Fin M) (Fin M) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin M) (R := ℝ)).mp U.2
  have hV :
      Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
          (V : Matrix (Fin N) (Fin N) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp V.2
  calc
    Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        eckartYoungApproximation A q U V *
        (V : Matrix (Fin N) (Fin N) ℝ)
        =
      Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        ((U : Matrix (Fin M) (Fin M) ℝ) * truncatedSingularValueDiagonal A q) := by
          simp [eckartYoungApproximation, Matrix.mul_assoc, hV]
    _ =
      (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        (U : Matrix (Fin M) (Fin M) ℝ)) *
          truncatedSingularValueDiagonal A q := by
            rw [← Matrix.mul_assoc]
    _ = truncatedSingularValueDiagonal A q := by
      simp [hU]

/-- Helper for Example 3.9: transporting a matrix into the chosen SVD coordinates preserves rank. -/
private lemma orthogonal_transport_rank_eq {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin N) ℝ) :
    (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
        (V : Matrix (Fin N) (Fin N) ℝ)).rank =
      B.rank := by
  -- Orthogonal matrices have unit determinant, so left and right multiplication preserve rank.
  have hU : IsUnit ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).det) := by
    simpa [Matrix.det_transpose] using Matrix.UnitaryGroup.det_isUnit U
  have hV : IsUnit ((V : Matrix (Fin N) (Fin N) ℝ).det) :=
    Matrix.UnitaryGroup.det_isUnit V
  calc
    ((((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
        (V : Matrix (Fin N) (Fin N) ℝ))).rank
        = (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B)).rank := by
            simpa using Matrix.rank_mul_eq_left_of_isUnit_det
              (A := (V : Matrix (Fin N) (Fin N) ℝ))
              (B := Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * B) hV
    _ = B.rank := by
      simpa using Matrix.rank_mul_eq_right_of_isUnit_det
        (A := Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ))
        (B := B) hU

/-- Helper for Example 3.9: transporting a diagonal competitor back to the original coordinates
also preserves rank. -/
private lemma orthogonal_untransport_rank_eq {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin N) ℝ) :
    ((((U : Matrix (Fin M) (Fin M) ℝ) * B) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))).rank =
      B.rank := by
  -- The inverse transport uses the same determinant argument.
  have hU : IsUnit ((U : Matrix (Fin M) (Fin M) ℝ).det) := Matrix.UnitaryGroup.det_isUnit U
  have hV : IsUnit ((Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)).det) := by
    simpa [Matrix.det_transpose] using Matrix.UnitaryGroup.det_isUnit V
  calc
    ((((U : Matrix (Fin M) (Fin M) ℝ) * B) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))).rank
        = (((U : Matrix (Fin M) (Fin M) ℝ) * B)).rank := by
            simpa using Matrix.rank_mul_eq_left_of_isUnit_det
              (A := Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
              (B := (U : Matrix (Fin M) (Fin M) ℝ) * B) hV
    _ = B.rank := by
      simpa using Matrix.rank_mul_eq_right_of_isUnit_det
        (A := (U : Matrix (Fin M) (Fin M) ℝ))
        (B := B) hU

/-- Helper for Example 3.9: the transport to singular coordinates preserves the rank constraint. -/
private lemma orthogonal_transport_mem_rankLESet_iff {M N q : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    {B : Matrix (Fin M) (Fin N) ℝ} :
    (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
        (V : Matrix (Fin N) (Fin N) ℝ)) ∈ rankLESet M N q ↔
      B ∈ rankLESet M N q := by
  -- This is just the rank equality written in membership form.
  rw [mem_rankLESet_iff, mem_rankLESet_iff, orthogonal_transport_rank_eq U V B]

/-- Helper for Example 3.9: the inverse transport preserves the rank constraint as well. -/
private lemma orthogonal_untransport_mem_rankLESet_iff {M N q : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    {B : Matrix (Fin M) (Fin N) ℝ} :
    (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) ∈ rankLESet M N q ↔
      B ∈ rankLESet M N q := by
  -- This is the same rank invariance for the inverse transport.
  rw [mem_rankLESet_iff, mem_rankLESet_iff, orthogonal_untransport_rank_eq U V B]

/-- Helper for Example 3.9: orthogonal left multiplication preserves the Euclidean `ℓ²` norm of a
column vector after passing to `WithLp 2`. -/
private lemma orthogonal_mulVec_toLp_norm_eq {M : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (x : Fin M → ℝ) :
    ‖WithLp.toLp 2 ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)‖ =
      ‖WithLp.toLp 2 x‖ := by
  -- Compare squared norms and use `U * Uᵀ = 1` to cancel the transport.
  have hU :
      (U : Matrix (Fin M) (Fin M) ℝ) * Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin M) (R := ℝ)).mp U.2
  have hsq :
      ‖WithLp.toLp 2 ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 := by
    calc
      ‖WithLp.toLp 2 ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)‖ ^ 2
          = ∑ i, ‖((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x) i‖ ^ 2 := by
              simpa using PiLp.norm_sq_eq_of_L2 (fun _ : Fin M => ℝ)
                (WithLp.toLp 2 ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x))
      _ = dotProduct ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)
            ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x) := by
            simp [dotProduct, pow_two]
      _ = dotProduct (Matrix.vecMul ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)
            (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ))) x := by
            rw [← Matrix.dotProduct_mulVec]
      _ = dotProduct (((U : Matrix (Fin M) (Fin M) ℝ)).mulVec
            ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)) x := by
            rw [Matrix.vecMul_transpose]
      _ = dotProduct ((((U : Matrix (Fin M) (Fin M) ℝ) *
            Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)).mulVec x)) x := by
            rw [Matrix.mulVec_mulVec]
      _ = dotProduct x x := by
            simp [hU]
      _ = ∑ i, ‖x i‖ ^ 2 := by
            simp [dotProduct, pow_two]
      _ = ‖WithLp.toLp 2 x‖ ^ 2 := by
            simpa using
              (PiLp.norm_sq_eq_of_L2 (fun _ : Fin M => ℝ) (WithLp.toLp 2 x)).symm
  exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq

/-- Helper for Example 3.9: squaring the Frobenius norm gives the sum of the squared entries. -/
private lemma frobenius_norm_sq_eq_sum {M N : ℕ} (X : Matrix (Fin M) (Fin N) ℝ) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  -- Expand the Frobenius norm and collapse the resulting square root.
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul]
  · norm_num
  · positivity

/-- Helper for Example 3.9: transporting Frobenius distances through orthogonal coordinates leaves
them unchanged. -/
private lemma frobenius_orthogonal_transport_eq {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (A B : Matrix (Fin M) (Fin N) ℝ) :
    ‖A - B‖ =
      ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * (A - B)) *
        (V : Matrix (Fin N) (Fin N) ℝ)‖ := by
  let X := A - B
  -- First prove invariance under left multiplication by transporting each column.
  have hleft :
      ‖Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X‖ = ‖X‖ := by
    have hsq :
        ‖Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X‖ ^ 2 = ‖X‖ ^ 2 := by
      calc
        ‖Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X‖ ^ 2
            = ∑ i, ∑ j, ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) i j‖ ^ 2 :=
              frobenius_norm_sq_eq_sum _
        _ = ∑ j, ∑ i, ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) i j‖ ^ 2 := by
              rw [Finset.sum_comm]
        _ = ∑ j,
              ‖WithLp.toLp 2
                  ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X).col j)‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro j _
                simpa [Matrix.col_apply] using
                  (PiLp.norm_sq_eq_of_L2 (fun _ : Fin M => ℝ)
                    (WithLp.toLp 2
                      ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X).col j))).symm
        _ = ∑ j, ‖WithLp.toLp 2 (X.col j)‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [Matrix.col_apply, Matrix.mul_apply, dotProduct] using
                orthogonal_mulVec_toLp_norm_eq U (X.col j)
        _ = ∑ j, ∑ i, ‖X i j‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j _
              simpa [Matrix.col_apply] using
                (PiLp.norm_sq_eq_of_L2 (fun _ : Fin M => ℝ) (WithLp.toLp 2 (X.col j)))
        _ = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
              rw [Finset.sum_comm]
        _ = ‖X‖ ^ 2 := by
              rw [frobenius_norm_sq_eq_sum]
    exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
  -- Then transport right multiplication through transpose and reuse the same argument.
  have hright :
      ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) * (V : Matrix (Fin N) (Fin N) ℝ)‖ =
        ‖Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X‖ := by
    have htrans :
        ‖Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
            (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))‖ =
          ‖Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)‖ := by
      -- Apply the left-invariance result to the transposed matrix.
      have hsq :
          ‖Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
              (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))‖ ^ 2 =
            ‖Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)‖ ^ 2 := by
        calc
          ‖Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
              (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))‖ ^ 2
              = ∑ i, ∑ j,
                  ‖(Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
                      (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))) i j‖ ^ 2 :=
                  frobenius_norm_sq_eq_sum _
          _ = ∑ j, ∑ i,
                ‖(Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
                    (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))) i j‖ ^ 2 := by
                rw [Finset.sum_comm]
          _ = ∑ j,
                ‖WithLp.toLp 2
                    ((Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
                        (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))).col j)‖ ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  simpa [Matrix.col_apply] using
                    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => ℝ)
                      (WithLp.toLp 2
                        ((Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
                            (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))).col j))).symm
          _ = ∑ j,
                ‖WithLp.toLp 2 ((Matrix.transpose X *
                    (U : Matrix (Fin M) (Fin M) ℝ)).col j)‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro j _
                simpa [Matrix.col_apply, Matrix.mul_apply, dotProduct] using
                  orthogonal_mulVec_toLp_norm_eq V
                    ((Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)).col j)
          _ = ∑ j, ∑ i, ‖(Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)) i j‖ ^ 2 := by
                refine Finset.sum_congr rfl ?_
                intro j _
                simpa [Matrix.col_apply] using
                  (PiLp.norm_sq_eq_of_L2 (fun _ : Fin N => ℝ)
                    (WithLp.toLp 2
                      ((Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)).col j)))
          _ = ∑ i, ∑ j, ‖(Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)) i j‖ ^ 2 := by
                rw [Finset.sum_comm]
          _ = ‖Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)‖ ^ 2 := by
                rw [frobenius_norm_sq_eq_sum]
      exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq
    calc
      ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) * (V : Matrix (Fin N) (Fin N) ℝ)‖
          =
        ‖Matrix.transpose
            (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) *
                (V : Matrix (Fin N) (Fin N) ℝ)))‖ := by
              simpa using
                (Matrix.frobenius_norm_transpose
                  (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) *
                      (V : Matrix (Fin N) (Fin N) ℝ)))).symm
      _ = ‖Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
            (Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ))‖ := by
              simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ‖Matrix.transpose X * (U : Matrix (Fin M) (Fin M) ℝ)‖ := htrans
      _ = ‖Matrix.transpose (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X)‖ := by
              simp [Matrix.transpose_mul]
      _ = ‖Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X‖ := by
              simpa using
                Matrix.frobenius_norm_transpose
                  (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X)
  -- Combine the two exact isometries.
  simpa [X] using hleft.symm.trans hright.symm

/-- Helper for Example 3.9: transporting to SVD coordinates and back fixes every matrix. -/
private lemma orthogonal_transport_round_trip {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin N) ℝ) :
    ((U : Matrix (Fin M) (Fin M) ℝ) *
        (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
          (V : Matrix (Fin N) (Fin N) ℝ))) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) =
      B := by
  -- Cancel `Uᵀ U` on the left and `V Vᵀ` on the right.
  have hU :
      (U : Matrix (Fin M) (Fin M) ℝ) *
          Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin M) (R := ℝ)).mp U.2
  have hV :
      (V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ)).mp V.2
  calc
    ((U : Matrix (Fin M) (Fin M) ℝ) *
        (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
          (V : Matrix (Fin N) (Fin N) ℝ))) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)
        =
      (((U : Matrix (Fin M) (Fin M) ℝ) *
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ))) * B) *
        ((V : Matrix (Fin N) (Fin N) ℝ) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) := by
            simp [Matrix.mul_assoc]
    _ = B := by
      simp [hU, hV]

/-- Helper for Example 3.9: transporting back to SVD coordinates after returning to the original
basis fixes the diagonal competitor. -/
private lemma orthogonal_untransport_round_trip {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin N) ℝ) :
    (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
        (V : Matrix (Fin N) (Fin N) ℝ) =
      B := by
  -- This is the same cancellation in the opposite direction.
  have hU :
      Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (U : Matrix (Fin M) (Fin M) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin M) (R := ℝ)).mp U.2
  have hV :
      Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
          (V : Matrix (Fin N) (Fin N) ℝ) =
        1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp V.2
  calc
    (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
        (V : Matrix (Fin N) (Fin N) ℝ)
        =
      ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
          (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
        (Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) *
          (V : Matrix (Fin N) (Fin N) ℝ)) := by
            simp [Matrix.mul_assoc]
    _ = B := by
      simp [hU, hV]

/-- Helper for Example 3.9: orthogonal transport converts a Frobenius difference into the
corresponding difference of transported matrices. -/
private lemma orthogonal_transport_sub_eq {M N : ℕ}
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (A B : Matrix (Fin M) (Fin N) ℝ) :
    ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * (A - B)) *
        (V : Matrix (Fin N) (Fin N) ℝ) =
      (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
          (V : Matrix (Fin N) (Fin N) ℝ)) -
        ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * B) *
          (V : Matrix (Fin N) (Fin N) ℝ)) := by
  -- Expand the subtraction through both matrix multiplications and reassociate once.
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- Helper for Example 3.9: transporting the error against an untransported candidate reduces to
the diagonal-model error. -/
private lemma orthogonal_untransport_sub_eq {M N : ℕ}
    (A P : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
        (A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
        (V : Matrix (Fin N) (Fin N) ℝ) =
      (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
          (V : Matrix (Fin N) (Fin N) ℝ)) - P := by
  -- First rewrite the transported subtraction, then cancel the round-trip on the candidate term.
  rw [orthogonal_transport_sub_eq U V A
    (((U : Matrix (Fin M) (Fin M) ℝ) * P) * Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))]
  simp [orthogonal_untransport_round_trip U V P]

/-- Helper for Example 3.9: the matrix rank equals the Euclidean dimension of the range of the
associated linear map. -/
private lemma rank_eq_finrank_range_toEuclideanLin {M N : ℕ}
    (B : Matrix (Fin M) (Fin N) ℝ) :
    B.rank = Module.finrank ℝ ↥((Matrix.toEuclideanLin B).range) := by
  -- Rewrite the abstract rank formula using the `PiLp` bases that define `toEuclideanLin`.
  simpa [Matrix.toLpLin_eq_toLin (m := Fin M) (n := Fin N) (R := ℝ) (p := 2) (q := 2)] using
    (Matrix.rank_eq_finrank_range_toLin B
      (PiLp.basisFun 2 ℝ (Fin M))
      (PiLp.basisFun 2 ℝ (Fin N)))

/-- Helper for Example 3.9: the squared norms of the coordinate projections onto a subspace add up
to its dimension. -/
private lemma coordinate_projection_mass_eq_finrank {M : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M))) :
    ∑ i : Fin M, ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 =
      Module.finrank ℝ S := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S
  have hproj (i : Fin M) :
      ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 =
        ∑ k : Fin (Module.finrank ℝ S),
          (inner ℝ ((b k : S) : EuclideanSpace ℝ (Fin M))
            (EuclideanSpace.basisFun (Fin M) ℝ i)) ^ 2 := by
    -- Expand the orthogonal projection in an orthonormal basis of `S`.
    have hsum :=
      b.sum_sq_inner_right (S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i))
    simpa [b.repr_apply_apply, S.inner_orthogonalProjection_eq_of_mem_left] using hsum.symm
  calc
    ∑ i : Fin M, ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2
        = ∑ i : Fin M,
            ∑ k : Fin (Module.finrank ℝ S),
              (inner ℝ ((b k : S) : EuclideanSpace ℝ (Fin M))
                (EuclideanSpace.basisFun (Fin M) ℝ i)) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hproj i
    _ = ∑ k : Fin (Module.finrank ℝ S),
          ∑ i : Fin M,
            (inner ℝ ((b k : S) : EuclideanSpace ℝ (Fin M))
              (EuclideanSpace.basisFun (Fin M) ℝ i)) ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin (Module.finrank ℝ S), ‖((b k : S) : EuclideanSpace ℝ (Fin M))‖ ^ 2 := by
          -- Swap the sums and use Parseval on the ambient coordinate basis.
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa [real_inner_comm] using
            (EuclideanSpace.basisFun (Fin M) ℝ).sum_sq_inner_right
              (((b k : S) : EuclideanSpace ℝ (Fin M)))
    _ = ∑ _k : Fin (Module.finrank ℝ S), (1 : ℝ) := by
          -- Each basis vector of `S` has norm one.
          refine Finset.sum_congr rfl ?_
          intro k _
          have hk : ‖b k‖ = 1 := (b.orthonormal).left k
          change ‖b k‖ ^ 2 = 1
          nlinarith
    _ = Module.finrank ℝ S := by
      simp

/-- Helper for Example 3.9: an antitone singular-value square sequence captures at most the top
`q` total mass under box and total-mass constraints. -/
private lemma singular_value_weighted_sum_le_of_mass_le {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) {q : ℕ} (hqM : q < M) (a : Fin M → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i) (ha_le_one : ∀ i, a i ≤ 1)
    (ha_sum : Finset.sum Finset.univ a ≤ q) :
    Finset.sum Finset.univ
        (fun i : Fin M => ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * a i) ≤
      Finset.sum (Finset.range q) (fun j ↦ ((Matrix.toEuclideanLin A).singularValues j) ^ 2) := by
  let w : ℕ → ℝ := fun i ↦ ((Matrix.toEuclideanLin A).singularValues i) ^ 2
  let aNat : ℕ → ℝ := fun i ↦ if h : i < M then a ⟨i, h⟩ else 0
  have hwanti : Antitone w := by
    intro i j hij
    -- The singular values are antitone, so their squares are as well.
    have hσ :=
      (Matrix.toEuclideanLin A).singularValues_antitone hij
    have hσi := (Matrix.toEuclideanLin A).singularValues_nonneg i
    have hσj := (Matrix.toEuclideanLin A).singularValues_nonneg j
    dsimp [w]
    nlinarith
  have hwnonneg : ∀ i < M, 0 ≤ w i := by
    intro i hi
    -- Every squared singular value is nonnegative.
    dsimp [w]
    nlinarith [(Matrix.toEuclideanLin A).singularValues_nonneg i]
  have ha_eq : Finset.sum (Finset.range M) aNat = ∑ i : Fin M, a i := by
    -- Rewrite the `Fin M` mass constraint as a range sum on natural indices.
    simpa [aNat] using (Fin.sum_univ_eq_sum_range (f := aNat) M).symm
  have ha_sum_nat : Finset.sum (Finset.range M) aNat ≤ q := by
    rw [ha_eq]
    exact ha_sum
  have hsplitsum :
      Finset.sum (Finset.range q) (fun i ↦ w i * aNat i) +
          Finset.sum (Finset.Ico q M) (fun i ↦ w i * aNat i) =
        Finset.sum (Finset.range M) (fun i ↦ w i * aNat i) := by
    -- Split the weighted sum into the first `q` indices and the remaining tail.
    simpa using
      (Finset.sum_range_add_sum_Ico (f := fun i ↦ w i * aNat i) (Nat.le_of_lt hqM))
  have htail_le :
      Finset.sum (Finset.Ico q M) (fun i ↦ w i * aNat i) ≤
        Finset.sum (Finset.Ico q M) (fun i ↦ w q * aNat i) := by
    -- Antitonicity bounds every tail weight by the `q`-th one.
    refine Finset.sum_le_sum ?_
    intro i hi
    have hiq : q ≤ i := (Finset.mem_Ico.mp hi).1
    have hiM : i < M := (Finset.mem_Ico.mp hi).2
    have hwi : w i ≤ w q := hwanti hiq
    have hai_nonneg : 0 ≤ aNat i := by
      simp [aNat, hiM, ha_nonneg]
    nlinarith
  have htail_mass :
      Finset.sum (Finset.Ico q M) aNat ≤ q - Finset.sum (Finset.range q) aNat := by
    -- The total mass bound controls the tail once the head is separated off.
    have hdecomp := (Finset.sum_range_add_sum_Ico (f := aNat) (Nat.le_of_lt hqM))
    linarith
  have hwq_nonneg : 0 ≤ w q := hwnonneg q hqM
  have htail_le' :
      Finset.sum (Finset.Ico q M) (fun i ↦ w q * aNat i) ≤
        w q * (q - Finset.sum (Finset.range q) aNat) := by
    -- Multiply the tail-mass estimate by the nonnegative boundary weight.
    have hmul := mul_le_mul_of_nonneg_left htail_mass hwq_nonneg
    simpa [Finset.mul_sum] using hmul
  have hones :
      q - Finset.sum (Finset.range q) aNat =
        Finset.sum (Finset.range q) (fun i ↦ (1 : ℝ) - aNat i) := by
    -- Convert the remaining mass into a sum of the deficits `1 - a_i`.
    rw [Finset.sum_sub_distrib]
    simp
  have hmain :
      Finset.sum (Finset.range q) (fun i ↦ w i * aNat i) +
          Finset.sum (Finset.Ico q M) (fun i ↦ w i * aNat i) ≤
        Finset.sum (Finset.range q) w := by
    -- Replace the tail by the boundary weight and absorb the leftover mass into the head.
    calc
      Finset.sum (Finset.range q) (fun i ↦ w i * aNat i) +
          Finset.sum (Finset.Ico q M) (fun i ↦ w i * aNat i)
          ≤ Finset.sum (Finset.range q) (fun i ↦ w i * aNat i) +
              Finset.sum (Finset.Ico q M) (fun i ↦ w q * aNat i) := by
                gcongr
      _ ≤ Finset.sum (Finset.range q) (fun i ↦ w i * aNat i) +
            w q * (q - Finset.sum (Finset.range q) aNat) := by
              gcongr
      _ = Finset.sum (Finset.range q) (fun i ↦ w i * aNat i + w q * ((1 : ℝ) - aNat i)) := by
            rw [hones, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ Finset.sum (Finset.range q) w := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hiq : i < q := Finset.mem_range.mp hi
            have hwiq : w q ≤ w i := hwanti (Nat.le_of_lt hiq)
            have hai_nonneg : 0 ≤ aNat i := by
              simp [aNat, Nat.lt_trans hiq hqM, ha_nonneg]
            have hai_le_one : aNat i ≤ 1 := by
              simp [aNat, Nat.lt_trans hiq hqM, ha_le_one]
            nlinarith
  have hsum_nat :
      Finset.sum (Finset.range M) (fun i ↦ w i * aNat i) ≤ Finset.sum (Finset.range q) w := by
    rw [← hsplitsum]
    exact hmain
  have hsum_eq :
      Finset.sum (Finset.range M) (fun i ↦ w i * aNat i) =
        ∑ i : Fin M, w i.1 * a i := by
    -- Return from the range sum back to the original `Fin M` indexing.
    simpa [aNat] using
      (Fin.sum_univ_eq_sum_range (f := fun i ↦ w i * aNat i) M).symm
  rw [← hsum_eq]
  simpa [w] using hsum_nat

/-- Helper for Example 3.9: the singular-value diagonal sends a coordinate basis vector to the
matching singular-value column. -/
private lemma singularValueDiagonal_toEuclideanLin_basisFun_ofLp {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (j : Fin N) (i : Fin M) :
    (Matrix.toEuclideanLin (singularValueDiagonal A)
        (EuclideanSpace.basisFun (Fin N) ℝ j)).ofLp i =
      if i.1 = j.1 then (Matrix.toEuclideanLin A).singularValues i.1 else 0 := by
  -- Unfold the diagonal matrix and read off the `j`-th column entrywise.
  simp [singularValueDiagonal]

/-- Helper for Example 3.9: the truncated singular-value diagonal has the same coordinate-column
formula, with entries beyond the truncation index removed. -/
private lemma truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp {M N q : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (j : Fin N) (i : Fin M) :
    (Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q)
        (EuclideanSpace.basisFun (Fin N) ℝ j)).ofLp i =
      if i.1 = j.1 ∧ i.1 < q then (Matrix.toEuclideanLin A).singularValues i.1 else 0 := by
  -- This is the same direct column computation for the truncated diagonal.
  simp [truncatedSingularValueDiagonal]

/-- Helper for Example 3.9: the Frobenius norm squared is the sum of the squared Euclidean norms
of the coordinate columns. -/
private lemma frobenius_norm_sq_eq_sum_basis_columns {M N : ℕ}
    (X : Matrix (Fin M) (Fin N) ℝ) :
    ‖X‖ ^ 2 =
      ∑ j : Fin N, ‖Matrix.toEuclideanLin X (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 := by
  -- Reindex the Frobenius entrywise sum by columns and recognize each inner sum as a Euclidean
  -- column norm.
  calc
    ‖X‖ ^ 2 = ∑ i : Fin M, ∑ j : Fin N, ‖X i j‖ ^ 2 := frobenius_norm_sq_eq_sum X
    _ = ∑ j : Fin N, ∑ i : Fin M,
          ‖(Matrix.toEuclideanLin X (EuclideanSpace.basisFun (Fin N) ℝ j)).ofLp i‖ ^ 2 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [show ((Matrix.toEuclideanLin X (EuclideanSpace.basisFun (Fin N) ℝ j)).ofLp) =
                (Matrix.toLin' X) (EuclideanSpace.basisFun (Fin N) ℝ j).ofLp by
                  simpa using
                    (Matrix.ofLp_toLpLin (p := 2) (q := 2) X
                      (EuclideanSpace.basisFun (Fin N) ℝ j))]
            simpa using congrFun (Matrix.mulVec_single_one X j) i
    _ = ∑ j : Fin N, ‖Matrix.toEuclideanLin X (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa using
            (PiLp.norm_sq_eq_of_L2 (fun _ : Fin M => ℝ)
              (Matrix.toEuclideanLin X (EuclideanSpace.basisFun (Fin N) ℝ j))).symm

/-- Helper for Example 3.9: the diagonal column indexed by `i` is the corresponding singular value
times the `i`-th coordinate basis vector. -/
private lemma singularValueDiagonal_toEuclideanLin_basisFun_eq_smul {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (hi : i.1 < N) :
    Matrix.toEuclideanLin (singularValueDiagonal A)
        (EuclideanSpace.basisFun (Fin N) ℝ ⟨i.1, hi⟩) =
      (Matrix.toEuclideanLin A).singularValues i.1 • EuclideanSpace.basisFun (Fin M) ℝ i := by
  -- Compare the two vectors coordinatewise using the previously computed column entries.
  ext k
  have hcoord :=
    singularValueDiagonal_toEuclideanLin_basisFun_ofLp A ⟨i.1, hi⟩ k
  by_cases hk : k = i
  · subst hk
    simpa [EuclideanSpace.basisFun_apply] using hcoord
  · have hk' : k.1 ≠ i.1 := by
      intro hki
      exact hk (Fin.ext hki)
    simpa [EuclideanSpace.basisFun_apply, hk, hk'] using hcoord

/-- Helper for Example 3.9: the truncated diagonal column is either the original singular-value
column or zero, depending on whether the index lies below the cutoff. -/
private lemma truncatedSingularValueDiagonal_toEuclideanLin_basisFun_eq_smul {M N q : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (hi : i.1 < N) :
    Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q)
        (EuclideanSpace.basisFun (Fin N) ℝ ⟨i.1, hi⟩) =
      if i.1 < q then
        (Matrix.toEuclideanLin A).singularValues i.1 • EuclideanSpace.basisFun (Fin M) ℝ i
      else 0 := by
  -- Compare the truncated column with the claimed coordinate-basis formula entrywise.
  by_cases hiq : i.1 < q
  · ext k
    have hcoord :=
      truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp (q := q) A ⟨i.1, hi⟩ k
    by_cases hk : k = i
    · subst hk
      simp [hiq] at hcoord ⊢
      exact hcoord
    · have hk' : k.1 ≠ i.1 := by
        intro hki
        exact hk (Fin.ext hki)
      simpa [EuclideanSpace.basisFun_apply, hk, hk', hiq] using hcoord
  · ext k
    have hcoord :=
      truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp (q := q) A ⟨i.1, hi⟩ k
    by_cases hk : k = i
    · subst hk
      simp [hiq] at hcoord ⊢
      exact hcoord
    · have hk' : k.1 ≠ i.1 := by
        intro hki
        exact hk (Fin.ext hki)
      simpa [EuclideanSpace.basisFun_apply, hk, hk', hiq] using hcoord

/-- Helper for Example 3.9: the squared distance from a diagonal column to its orthogonal
projection records exactly the missing projection mass. -/
private lemma diagonal_column_projection_error_sq {M : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M))) (i : Fin M) (σ : ℝ) :
    ‖σ • EuclideanSpace.basisFun (Fin M) ℝ i -
        S.starProjection (σ • EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 =
      σ ^ 2 *
        (1 - ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2) := by
  let e : EuclideanSpace ℝ (Fin M) := EuclideanSpace.basisFun (Fin M) ℝ i
  -- Use the orthogonal decomposition into the projection and its complement.
  have hpyth :
      ‖σ • e‖ ^ 2 =
        ‖S.starProjection (σ • e)‖ ^ 2 + ‖σ • e - S.starProjection (σ • e)‖ ^ 2 := by
    calc
      ‖σ • e‖ ^ 2 = ‖S.starProjection (σ • e)‖ ^ 2 + ‖Sᗮ.starProjection (σ • e)‖ ^ 2 :=
        S.norm_sq_eq_add_norm_sq_starProjection (σ • e)
      _ = ‖S.starProjection (σ • e)‖ ^ 2 + ‖σ • e - S.starProjection (σ • e)‖ ^ 2 := by
            rw [Submodule.starProjection_orthogonal_val]
  have hnorm : ‖σ • e‖ ^ 2 = σ ^ 2 := by
    rw [norm_smul]
    have he : ‖e‖ = 1 := by
      simp [e]
    rw [he, mul_one]
    simpa using (sq_abs σ)
  have hproj :
      ‖S.starProjection (σ • e)‖ ^ 2 = σ ^ 2 * ‖S.orthogonalProjection e‖ ^ 2 := by
    have hmap : S.starProjection (σ • e) = σ • S.starProjection e := by
      simp
    rw [hmap, norm_smul, show S.starProjection e = S.orthogonalProjection e by rfl, mul_pow]
    simpa [mul_assoc] using
      congrArg (fun x : ℝ => x * ‖S.orthogonalProjection e‖ ^ 2) (sq_abs σ)
  nlinarith

/-- Helper for Example 3.9: if a coordinate basis vector has projection norm one, then it already
lies in the subspace and its orthogonal projection is itself. -/
private lemma orthogonalProjection_basis_eq_of_norm_sq_eq_one {M : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M))) (i : Fin M)
    (hproj : ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 = 1) :
    S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i) =
      EuclideanSpace.basisFun (Fin M) ℝ i := by
  let e : EuclideanSpace ℝ (Fin M) := EuclideanSpace.basisFun (Fin M) ℝ i
  -- Pythagoras shows the orthogonal complement component vanishes once the projection has norm `1`.
  have hpyth :
      ‖e‖ ^ 2 =
        ‖S.orthogonalProjection e‖ ^ 2 + ‖e - S.starProjection e‖ ^ 2 := by
    simpa [e, show S.starProjection e = S.orthogonalProjection e by rfl] using
      S.norm_sq_eq_add_norm_sq_starProjection e
  have hunit : ‖e‖ ^ 2 = 1 := by
    have he : ‖e‖ = 1 := by
      simp [e, EuclideanSpace.basisFun_apply]
    nlinarith
  have hzero_norm : ‖e - S.starProjection e‖ = 0 := by
    have hzero_sq : ‖e - S.starProjection e‖ ^ 2 = 0 := by
      rw [hproj] at hpyth
      nlinarith
    nlinarith [sq_nonneg ‖e - S.starProjection e‖, hzero_sq]
  have heq : e - S.starProjection e = 0 := by
    exact norm_eq_zero.mp hzero_norm
  have heq' : e = S.starProjection e := sub_eq_zero.mp heq
  simpa [e, show S.starProjection e = S.orthogonalProjection e by rfl] using heq'.symm

/-- Helper for Example 3.9: under a strict singular-value gap, equality in the weighted capture
bound forces the projection profile to be the sharp `0/1` head indicator. -/
private lemma projection_mass_rigidity_of_strict_gap {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) {q : ℕ} (hq_pos : 0 < q) (hqM : q < M)
    {a : Fin M → ℝ} (ha_nonneg : ∀ i, 0 ≤ a i) (ha_le_one : ∀ i, a i ≤ 1)
    (ha_sum : Finset.sum Finset.univ a ≤ q)
    (hEq :
      ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * a i =
        Finset.sum (Finset.range q)
          (fun j ↦ ((Matrix.toEuclideanLin A).singularValues j) ^ 2))
    (hgap :
      (Matrix.toEuclideanLin A).singularValues (q - 1) ≠
        (Matrix.toEuclideanLin A).singularValues q) :
    ∀ i : Fin M, a i = if i.1 < q then (1 : ℝ) else 0 := by
  let w : ℕ → ℝ := fun i ↦ ((Matrix.toEuclideanLin A).singularValues i) ^ 2
  let aNat : ℕ → ℝ := fun i ↦ if h : i < M then a ⟨i, h⟩ else 0
  have ha_eq :
      Finset.sum (Finset.range M) aNat = ∑ i : Fin M, a i := by
    -- Rewrite the `Fin M` mass constraint as a range sum on natural numbers.
    simpa [aNat] using (Fin.sum_univ_eq_sum_range (f := aNat) M).symm
  have ha_total :
      Finset.sum (Finset.range M) aNat ≤ q := by
    rw [ha_eq]
    exact ha_sum
  have hwanti : Antitone w := by
    intro i j hij
    have hσ := (Matrix.toEuclideanLin A).singularValues_antitone hij
    have hσi := (Matrix.toEuclideanLin A).singularValues_nonneg i
    have hσj := (Matrix.toEuclideanLin A).singularValues_nonneg j
    dsimp [w]
    nlinarith
  have hboundary :
      w q < w (q - 1) := by
    have hσle :=
      (Matrix.toEuclideanLin A).singularValues_antitone (Nat.pred_le q)
    have hσq := (Matrix.toEuclideanLin A).singularValues_nonneg q
    have hσqm1 := (Matrix.toEuclideanLin A).singularValues_nonneg (q - 1)
    have hσlt :
        (Matrix.toEuclideanLin A).singularValues q <
          (Matrix.toEuclideanLin A).singularValues (q - 1) := by
      refine lt_of_le_of_ne hσle ?_
      simpa [eq_comm] using hgap
    dsimp [w]
    nlinarith
  have hEqw :
      ∑ i : Fin M, w i.1 * a i = Finset.sum (Finset.range q) w := by
    simpa [w] using hEq
  have hsplitsum :
      Finset.sum (Finset.range q) (fun n ↦ w n * aNat n) +
          Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n) =
        Finset.sum (Finset.range M) (fun n ↦ w n * aNat n) := by
    -- Split the weighted sum into head and tail contributions.
    simpa using
      (Finset.sum_range_add_sum_Ico (f := fun n ↦ w n * aNat n) (Nat.le_of_lt hqM))
  have hsplita :
      Finset.sum (Finset.range q) aNat + Finset.sum (Finset.Ico q M) aNat =
        Finset.sum (Finset.range M) aNat := by
    -- Split the total captured mass at the same cutoff.
    simpa using (Finset.sum_range_add_sum_Ico (f := aNat) (Nat.le_of_lt hqM))
  have hheadsplit :
      Finset.sum (Finset.range q) w -
          Finset.sum (Finset.range q) (fun n ↦ w n * aNat n) =
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
          w q * (q - Finset.sum (Finset.range q) aNat) := by
    -- Separate the head deficit into strict-gap loss and unused head mass.
    calc
      Finset.sum (Finset.range q) w -
          Finset.sum (Finset.range q) (fun n ↦ w n * aNat n)
          =
        Finset.sum (Finset.range q) (fun n ↦ w n - w n * aNat n) := by
          rw [← Finset.sum_sub_distrib]
      _ =
        Finset.sum (Finset.range q)
          (fun n ↦ (w n - w q) * (1 - aNat n) + w q * (1 - aNat n)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ =
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
          Finset.sum (Finset.range q) (fun n ↦ w q * (1 - aNat n)) := by
            rw [Finset.sum_add_distrib]
      _ =
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
          w q * (q - Finset.sum (Finset.range q) aNat) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_sub_distrib]
            simp
  have htaildecomp :
      Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n) =
        w q * Finset.sum (Finset.Ico q M) aNat -
          Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n) := by
    -- The tail loss is the boundary weight times tail mass minus the captured tail weight.
    calc
      Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n)
          =
        Finset.sum (Finset.Ico q M) (fun n ↦ w q * aNat n - w n * aNat n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ =
        Finset.sum (Finset.Ico q M) (fun n ↦ w q * aNat n) -
          Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n) := by
            rw [Finset.sum_sub_distrib]
      _ =
        w q * Finset.sum (Finset.Ico q M) aNat -
          Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n) := by
            rw [Finset.mul_sum]
  have hsum_eq :
      Finset.sum (Finset.range M) (fun n ↦ w n * aNat n) =
        Finset.sum (Finset.range q) w := by
    -- Return to `Fin M` indexing and use the assumed equality of weighted sums.
    have hsum_fin :
        Finset.sum (Finset.range M) (fun n ↦ w n * aNat n) =
          ∑ i : Fin M, w i.1 * a i := by
      simpa [aNat] using
        (Fin.sum_univ_eq_sum_range (f := fun n ↦ w n * aNat n) M).symm
    rw [hsum_fin]
    exact hEqw
  have hhead_zero :
      ∀ n ∈ Finset.range q, (w n - w q) * (1 - aNat n) = 0 := by
    have hdecomp :
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
            w q * (q - Finset.sum (Finset.range M) aNat) +
            Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n) = 0 := by
      calc
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
            w q * (q - Finset.sum (Finset.range M) aNat) +
            Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n)
            =
          (Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) +
              w q * (q - Finset.sum (Finset.range q) aNat)) +
            (Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n) -
              w q * Finset.sum (Finset.Ico q M) aNat) := by
                rw [show q - Finset.sum (Finset.range M) aNat =
                    q - Finset.sum (Finset.range q) aNat - Finset.sum (Finset.Ico q M) aNat by
                      rw [← hsplita]
                      ring]
                ring
        _ =
          (Finset.sum (Finset.range q) w -
              Finset.sum (Finset.range q) (fun n ↦ w n * aNat n)) +
            ((w q * Finset.sum (Finset.Ico q M) aNat -
                Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n)) -
              w q * Finset.sum (Finset.Ico q M) aNat) := by
                rw [← hheadsplit, htaildecomp]
        _ = Finset.sum (Finset.range q) w -
            (Finset.sum (Finset.range q) (fun n ↦ w n * aNat n) +
              Finset.sum (Finset.Ico q M) (fun n ↦ w n * aNat n)) := by
                ring
        _ = Finset.sum (Finset.range q) w -
            Finset.sum (Finset.range M) (fun n ↦ w n * aNat n) := by
              rw [hsplitsum]
        _ = 0 := by
              rw [hsum_eq]
              ring
    have hhead_nonneg :
        ∀ n ∈ Finset.range q, 0 ≤ (w n - w q) * (1 - aNat n) := by
      intro n hn
      have hnq : n < q := Finset.mem_range.mp hn
      have hwn : w q ≤ w n := hwanti (Nat.le_of_lt hnq)
      have hle_one : aNat n ≤ 1 := by
        have hnM : n < M := Nat.lt_trans hnq hqM
        simpa [aNat, hnM] using ha_le_one ⟨n, hnM⟩
      have hnonneg : 0 ≤ aNat n := by
        have hnM : n < M := Nat.lt_trans hnq hqM
        simpa [aNat, hnM] using ha_nonneg ⟨n, hnM⟩
      nlinarith
    have htail_nonneg :
        ∀ n ∈ Finset.Ico q M, 0 ≤ (w q - w n) * aNat n := by
      intro n hn
      have hnq : q ≤ n := (Finset.mem_Ico.mp hn).1
      have hnM : n < M := (Finset.mem_Ico.mp hn).2
      have hwn : w n ≤ w q := hwanti hnq
      have hnonneg : 0 ≤ aNat n := by
        simpa [aNat, hnM] using ha_nonneg ⟨n, hnM⟩
      nlinarith
    have hmass_nonneg : 0 ≤ w q * (q - Finset.sum (Finset.range M) aNat) := by
      have hwq_nonneg : 0 ≤ w q := by
        dsimp [w]
        nlinarith [(Matrix.toEuclideanLin A).singularValues_nonneg q]
      have hmass : 0 ≤ q - Finset.sum (Finset.range M) aNat := by
        linarith
      exact mul_nonneg hwq_nonneg hmass
    have hheadsum_nonneg :
        0 ≤ Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) :=
      Finset.sum_nonneg hhead_nonneg
    have htailsum_nonneg :
        0 ≤ Finset.sum (Finset.Ico q M) (fun n ↦ (w q - w n) * aNat n) :=
      Finset.sum_nonneg htail_nonneg
    have hheadsum_zero :
        Finset.sum (Finset.range q) (fun n ↦ (w n - w q) * (1 - aNat n)) = 0 := by
      nlinarith [hheadsum_nonneg, hmass_nonneg, htailsum_nonneg, hdecomp]
    exact (Finset.sum_eq_zero_iff_of_nonneg hhead_nonneg).mp hheadsum_zero
  intro i
  by_cases hiq : i.1 < q
  · have hi_head :
        (w i.1 - w q) * (1 - aNat i.1) = 0 :=
      hhead_zero i.1 (Finset.mem_range.mpr hiq)
    have hstrict : 0 < w i.1 - w q := by
      have hi_le_pred : i.1 ≤ q - 1 := Nat.le_pred_of_lt hiq
      have hi_le : w (q - 1) ≤ w i.1 := hwanti hi_le_pred
      linarith
    have hiM : i.1 < M := i.2
    have hnat : a i = 1 := by
      have hi_head' : (w i.1 - w q) * (1 - a i) = 0 := by
        simpa [aNat, hiM] using hi_head
      have hone : 1 - a i = 0 := by
        rcases mul_eq_zero.mp hi_head' with hzero | hone
        · exact False.elim ((ne_of_gt hstrict) hzero)
        · exact hone
      linarith
    simpa [hiq] using hnat
  · have ha_eq_one :
        ∀ j : Fin M, j.1 < q → a j = 1 := by
      intro j hj
      have hj_head :
          (w j.1 - w q) * (1 - aNat j.1) = 0 :=
        hhead_zero j.1 (Finset.mem_range.mpr hj)
      have hj_strict : 0 < w j.1 - w q := by
        have hj_le_pred : j.1 ≤ q - 1 := Nat.le_pred_of_lt hj
        have hj_le : w (q - 1) ≤ w j.1 := hwanti hj_le_pred
        linarith
      have hjM : j.1 < M := j.2
      have hnat : a j = 1 := by
        have hj_head' : (w j.1 - w q) * (1 - a j) = 0 := by
          simpa [aNat, hjM] using hj_head
        have hone : 1 - a j = 0 := by
          rcases mul_eq_zero.mp hj_head' with hzero | hone
          · exact False.elim ((ne_of_gt hj_strict) hzero)
          · exact hone
        linarith
      exact hnat
    have hhead_sum :
        Finset.sum (Finset.range q) aNat = q := by
      calc
        Finset.sum (Finset.range q) aNat =
          Finset.sum (Finset.range q) (fun _ ↦ (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnq : n < q := Finset.mem_range.mp hn
            have hnM : n < M := Nat.lt_trans hnq hqM
            have hna : aNat n = 1 := by
              simpa [aNat, hnM] using ha_eq_one ⟨n, hnM⟩ hnq
            simp [hna]
        _ = q := by
          simp
    have htail_sum_zero :
        Finset.sum (Finset.Ico q M) aNat = 0 := by
      have htail_nonneg_mass : 0 ≤ Finset.sum (Finset.Ico q M) aNat := by
        refine Finset.sum_nonneg ?_
        intro n hn
        have hnM : n < M := (Finset.mem_Ico.mp hn).2
        simpa [aNat, hnM] using ha_nonneg ⟨n, hnM⟩
      nlinarith [ha_total, hsplita, hhead_sum, htail_nonneg_mass]
    have htail_zero :
        aNat i.1 = 0 := by
      have hiIco : i.1 ∈ Finset.Ico q M := Finset.mem_Ico.mpr ⟨Nat.le_of_not_lt hiq, i.2⟩
      have hnonneg : ∀ n ∈ Finset.Ico q M, 0 ≤ aNat n := by
        intro n hn
        have hnM : n < M := (Finset.mem_Ico.mp hn).2
        simpa [aNat, hnM] using ha_nonneg ⟨n, hnM⟩
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp htail_sum_zero i.1 hiIco
    simpa [aNat, i.2, hiq] using htail_zero

/-- Helper for Example 3.9: a column-indexed weighted sum can be rewritten as a full `Fin M`
sum because singular values vanish past the column dimension. -/
private lemma column_indexed_weighted_sum_eq {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (d : Fin M → ℝ)
    (hσ_zero : ∀ n : ℕ, N ≤ n → (Matrix.toEuclideanLin A).singularValues n = 0) :
    (∑ j : Fin N,
        if hj : j.1 < M then
          ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 * d ⟨j.1, hj⟩
        else 0) =
      ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * d i := by
  let g : ℕ → ℝ := fun n ↦
    if hM : n < M then
      ((Matrix.toEuclideanLin A).singularValues n) ^ 2 * d ⟨n, hM⟩
    else 0
  have hleft :
      (∑ j : Fin N,
          if hj : j.1 < M then
            ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 * d ⟨j.1, hj⟩
          else 0) =
        Finset.sum (Finset.range N) g := by
    -- Rewrite the column-indexed sum as a range sum on natural numbers.
    simpa [g] using (Fin.sum_univ_eq_sum_range (f := g) N)
  have hright :
      Finset.sum (Finset.range M) g =
        ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * d i := by
    -- The target weighted sum is the same range sum viewed through `Fin M`.
    simpa [g] using (Fin.sum_univ_eq_sum_range (f := g) M).symm
  by_cases hMN : M ≤ N
  · -- When `M ≤ N`, the range sum over `N` has a zero tail after index `M`.
    rw [hleft]
    calc
      Finset.sum (Finset.range N) g
          = Finset.sum (Finset.range M) g + Finset.sum (Finset.Ico M N) g := by
              symm
              exact Finset.sum_range_add_sum_Ico (f := g) hMN
      _ = Finset.sum (Finset.range M) g := by
            have htail : Finset.sum (Finset.Ico M N) g = 0 := by
              refine Finset.sum_eq_zero ?_
              intro n hn
              have hnM : M ≤ n := (Finset.mem_Ico.mp hn).1
              simp [g, Nat.not_lt.mpr hnM]
            rw [htail, add_zero]
      _ = ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * d i := hright
  · have hNM : N ≤ M := le_of_not_ge hMN
    -- When `N ≤ M`, the extra `Fin M` tail is zero because the singular values vanish there.
    rw [hleft]
    calc
      Finset.sum (Finset.range N) g
          = Finset.sum (Finset.range N) g + Finset.sum (Finset.Ico N M) g := by
              have htail : Finset.sum (Finset.Ico N M) g = 0 := by
                refine Finset.sum_eq_zero ?_
                intro n hn
                have hnN : N ≤ n := (Finset.mem_Ico.mp hn).1
                have hnM : n < M := (Finset.mem_Ico.mp hn).2
                have hσ : (Matrix.toEuclideanLin A).singularValues n = 0 := hσ_zero n hnN
                simp [g, hnM, hσ]
              rw [htail, add_zero]
      _ = Finset.sum (Finset.range M) g := by
            exact Finset.sum_range_add_sum_Ico (f := g) hNM
      _ = ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 * d i := hright

/-- Helper for Example 3.9: the indicator-weighted head sum is exactly the sum over the first `q`
singular-value indices. -/
private lemma weighted_indicator_sum_eq_range {M : ℕ} (w : ℕ → ℝ) {q : ℕ} (hqM : q < M) :
    Finset.sum (Finset.range M) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0)) =
      Finset.sum (Finset.range q) w := by
  -- Split the range at `q`; the tail vanishes because the indicator is zero there.
  calc
    Finset.sum (Finset.range M) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0))
        = Finset.sum (Finset.range q) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0)) +
            Finset.sum (Finset.Ico q M) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0)) := by
              symm
              exact Finset.sum_range_add_sum_Ico
                (f := fun n ↦ w n * (if n < q then (1 : ℝ) else 0))
                (Nat.le_of_lt hqM)
    _ = Finset.sum (Finset.range q) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0)) := by
          have htail :
              Finset.sum (Finset.Ico q M) (fun n ↦ w n * (if n < q then (1 : ℝ) else 0)) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro n hn
            have hnq : q ≤ n := (Finset.mem_Ico.mp hn).1
            simp [Nat.not_lt.mpr hnq]
          rw [htail, add_zero]
    _ = Finset.sum (Finset.range q) w := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [Finset.mem_range.mp hn]

/-- Helper for Example 3.9: any weighted deficit sum splits into total mass minus captured
weighted mass. -/
private lemma weighted_deficit_eq_total_sub {M : ℕ} (w a : Fin M → ℝ) :
    ∑ i : Fin M, w i * (1 - a i) = (∑ i : Fin M, w i) - ∑ i : Fin M, w i * a i := by
  -- Expand the deficit termwise and distribute the finite sum over subtraction.
  calc
    ∑ i : Fin M, w i * (1 - a i)
        = ∑ i : Fin M, (w i - w i * a i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [mul_sub, mul_one]
    _ = (∑ i : Fin M, w i) - ∑ i : Fin M, w i * a i := by
          rw [Finset.sum_sub_distrib]

/-- Helper for Example 3.9: the diagonal truncation error is the singular-value tail mass written
as a weighted deficit sum. -/
private lemma truncated_diagonal_error_sq {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ)
    (hσ_zero : ∀ n : ℕ, N ≤ n → (Matrix.toEuclideanLin A).singularValues n = 0) :
    ‖singularValueDiagonal A - truncatedSingularValueDiagonal A q‖ ^ 2 =
      ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
        (1 - if i.1 < q then (1 : ℝ) else 0) := by
  have hcol :
      ∀ j : Fin N,
        ‖Matrix.toEuclideanLin
            (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
            (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 =
          if hj : j.1 < M then
            ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
              (1 - if j.1 < q then (1 : ℝ) else 0)
          else 0 := by
    intro j
    by_cases hjM : j.1 < M
    · let i : Fin M := ⟨j.1, hjM⟩
      have hdiag :
          Matrix.toEuclideanLin (singularValueDiagonal A)
              (EuclideanSpace.basisFun (Fin N) ℝ j) =
            (Matrix.toEuclideanLin A).singularValues j.1 • EuclideanSpace.basisFun (Fin M) ℝ i := by
        -- In diagonal coordinates, the `j`-th column is the `j`-th basis vector scaled by `σ_j`.
        dsimp [i]
        simpa using singularValueDiagonal_toEuclideanLin_basisFun_eq_smul A i j.2
      by_cases hjq : j.1 < q
      · have htrunc :
            Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q)
                (EuclideanSpace.basisFun (Fin N) ℝ j) =
              (Matrix.toEuclideanLin A).singularValues j.1 •
                EuclideanSpace.basisFun (Fin M) ℝ i := by
          -- Below the cutoff, truncation keeps the same diagonal column.
          ext k
          have hk :=
            truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp (q := q) A j k
          by_cases hki : k = i
          · subst hki
            simp [i, hjq] at hk ⊢
            exact hk
          · have hkne : k.1 ≠ i.1 := by
              intro hEq
              exact hki (Fin.ext hEq)
            simpa [EuclideanSpace.basisFun_apply, i, hjq, hkne, hki] using hk
        -- The kept columns cancel, so the error contribution is zero.
        have hzero :
            Matrix.toEuclideanLin
                (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
                (EuclideanSpace.basisFun (Fin N) ℝ j) = 0 := by
          rw [show
              Matrix.toEuclideanLin
                (singularValueDiagonal A - truncatedSingularValueDiagonal A q) =
                  Matrix.toEuclideanLin (singularValueDiagonal A) -
                    Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q) by
                simpa using
                  (LinearMap.map_sub (↑Matrix.toEuclideanLin)
                    (singularValueDiagonal A) (truncatedSingularValueDiagonal A q))]
          rw [LinearMap.sub_apply, hdiag, htrunc]
          simp
        calc
          ‖Matrix.toEuclideanLin
              (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
              (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 = ‖(0 :
                EuclideanSpace ℝ (Fin M))‖ ^ 2 := by
                  exact congrArg (fun x ↦ ‖x‖ ^ 2) hzero
          _ = if hj : j.1 < M then
                ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                  (1 - if j.1 < q then (1 : ℝ) else 0)
              else 0 := by
                simp [hjM, hjq]
      · have htrunc :
            Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q)
                (EuclideanSpace.basisFun (Fin N) ℝ j) = 0 := by
          -- Above the cutoff, the truncated column vanishes entrywise.
          ext k
          have hk :=
            truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp (q := q) A j k
          by_cases hkj : k.1 = j.1
          · simpa [hkj, hjq] using hk
          · simpa [hkj, hjq] using hk
        have hnorm :
            ‖(Matrix.toEuclideanLin A).singularValues j.1 •
                EuclideanSpace.basisFun (Fin M) ℝ i‖ ^ 2 =
              ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 := by
          -- A singular-value column has squared norm equal to the square of its singular value.
          rw [norm_smul]
          have hunit : ‖EuclideanSpace.basisFun (Fin M) ℝ i‖ = 1 := by
            simp [EuclideanSpace.basisFun_apply]
          rw [hunit, mul_one]
          simpa using (sq_abs ((Matrix.toEuclideanLin A).singularValues j.1))
        calc
          ‖Matrix.toEuclideanLin
              (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
              (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2
              =
            ‖(Matrix.toEuclideanLin A).singularValues j.1 •
                EuclideanSpace.basisFun (Fin M) ℝ i‖ ^ 2 := by
                  have hdiff :
                      Matrix.toEuclideanLin
                          (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
                          (EuclideanSpace.basisFun (Fin N) ℝ j) =
                        (Matrix.toEuclideanLin A).singularValues j.1 •
                          EuclideanSpace.basisFun (Fin M) ℝ i := by
                    rw [show
                        Matrix.toEuclideanLin
                          (singularValueDiagonal A - truncatedSingularValueDiagonal A q) =
                            Matrix.toEuclideanLin (singularValueDiagonal A) -
                              Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q) by
                          simpa using
                            (LinearMap.map_sub (↑Matrix.toEuclideanLin)
                              (singularValueDiagonal A)
                              (truncatedSingularValueDiagonal A q))]
                    rw [LinearMap.sub_apply, hdiag, htrunc]
                    simp
                  exact congrArg (fun x ↦ ‖x‖ ^ 2) hdiff
          _ =
            (if hj : j.1 < M then
              ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                (1 - if j.1 < q then (1 : ℝ) else 0)
            else 0) := by
              simpa [hjM, hjq] using hnorm
    · have hdiag :
          Matrix.toEuclideanLin (singularValueDiagonal A)
              (EuclideanSpace.basisFun (Fin N) ℝ j) = 0 := by
        -- Once the column index lies beyond `M`, the rectangular diagonal has zero column.
        ext k
        have hk := singularValueDiagonal_toEuclideanLin_basisFun_ofLp A j k
        have hkj : k.1 ≠ j.1 := by
          intro hEq
          exact hjM (hEq.symm ▸ k.2)
        simpa [hkj] using hk
      have htrunc :
          Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q)
              (EuclideanSpace.basisFun (Fin N) ℝ j) = 0 := by
        -- The truncated diagonal has the same zero column outside the row range.
        ext k
        have hk := truncatedSingularValueDiagonal_toEuclideanLin_basisFun_ofLp (q := q) A j k
        have hkj : ¬ (k.1 = j.1 ∧ k.1 < q) := by
          intro hkq
          exact hjM (hkq.1.symm ▸ k.2)
        simpa [hkj] using hk
      have hzero :
          Matrix.toEuclideanLin
              (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
              (EuclideanSpace.basisFun (Fin N) ℝ j) = 0 := by
        rw [show
            Matrix.toEuclideanLin
              (singularValueDiagonal A - truncatedSingularValueDiagonal A q) =
                Matrix.toEuclideanLin (singularValueDiagonal A) -
                  Matrix.toEuclideanLin (truncatedSingularValueDiagonal A q) by
              simpa using
                (LinearMap.map_sub (↑Matrix.toEuclideanLin)
                  (singularValueDiagonal A) (truncatedSingularValueDiagonal A q))]
        rw [LinearMap.sub_apply, hdiag, htrunc]
        simp
      calc
        ‖Matrix.toEuclideanLin
            (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
            (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 = ‖(0 :
              EuclideanSpace ℝ (Fin M))‖ ^ 2 := by
                exact congrArg (fun x ↦ ‖x‖ ^ 2) hzero
        _ = if hj : j.1 < M then
              ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                (1 - if j.1 < q then (1 : ℝ) else 0)
            else 0 := by
              simp [hjM]
  -- Sum the exact column contributions and rewrite the column index by `Fin M`.
  rw [frobenius_norm_sq_eq_sum_basis_columns]
  calc
    ∑ j : Fin N,
        ‖Matrix.toEuclideanLin
            (singularValueDiagonal A - truncatedSingularValueDiagonal A q)
            (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2
        =
      ∑ j : Fin N,
        if hj : j.1 < M then
          ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
            (1 - if j.1 < q then (1 : ℝ) else 0)
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hcol j
    _ =
      ∑ i : Fin M, ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
        (1 - if i.1 < q then (1 : ℝ) else 0) := by
          simpa using
            column_indexed_weighted_sum_eq
              (A := A)
              (d := fun i : Fin M ↦ 1 - if i.1 < q then (1 : ℝ) else 0)
              hσ_zero

/-- Helper for Example 3.9: in diagonal singular coordinates, truncation is the best rank-`q`
Frobenius approximation. -/
private lemma diagonal_truncation_is_best {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ) :
    IsBestApproximation (singularValueDiagonal A) (rankLESet M N q)
      (truncatedSingularValueDiagonal A q) := by
  -- Route correction: the combinatorial weighted-capture estimate is now proved above; the
  -- remaining work is to express the diagonal Frobenius error through projection masses.
  rw [isBestApproximation_iff_mem_and_forall_norm_sub_le]
  by_cases hqM : q < M
  · constructor
    · -- Admissibility is exactly the previously isolated rank estimate for the truncation.
      exact truncated_singular_value_diagonal_rank_le A
    · intro B hB
      -- Convert the competitor's rank bound into a dimension bound for its Euclidean range.
      let S : Submodule ℝ (EuclideanSpace ℝ (Fin M)) := (Matrix.toEuclideanLin B).range
      have hdim : Module.finrank ℝ S ≤ q := by
        simpa [S, rank_eq_finrank_range_toEuclideanLin B] using hB
      have hmass :
          ∑ i : Fin M,
              ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 ≤ q := by
        -- The projection masses sum to the dimension of the competitor range.
        rw [coordinate_projection_mass_eq_finrank S]
        exact_mod_cast hdim
      have hweighted :=
        singular_value_weighted_sum_le_of_mass_le A
          (q := q)
          (hqM := hqM)
          (a := fun i ↦ ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2)
          (ha_nonneg := fun _ ↦ sq_nonneg _)
          (ha_le_one := fun i ↦ by
            -- Projection onto a subspace cannot increase the norm of a unit coordinate vector.
            have hnorm :
                ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ≤
                  ‖EuclideanSpace.basisFun (Fin M) ℝ i‖ :=
              S.norm_orthogonalProjection_apply_le _
            have hunit : ‖EuclideanSpace.basisFun (Fin M) ℝ i‖ = 1 := by
              simp [EuclideanSpace.basisFun_apply]
            have hnorm' :
                ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ≤ 1 := by
              simpa [hunit] using hnorm
            nlinarith [norm_nonneg
              (S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)), hnorm'])
          (ha_sum := hmass)
      have hσ_zero : ∀ n : ℕ, N ≤ n → (Matrix.toEuclideanLin A).singularValues n = 0 := by
        intro n hn
        exact (Matrix.toEuclideanLin A).singularValues_of_finrank_le (by
          simpa using hn)
      by_cases hqN : q < N
      · have hcol_lower :
            ∀ j : Fin N,
              (if hj : j.1 < M then
                ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ ⟨j.1, hj⟩)‖ ^ 2)
              else 0) ≤
                ‖Matrix.toEuclideanLin (singularValueDiagonal A - B)
                  (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 := by
          intro j
          by_cases hjM : j.1 < M
          · let i : Fin M := ⟨j.1, hjM⟩
            let y : EuclideanSpace ℝ (Fin M) :=
              Matrix.toEuclideanLin (singularValueDiagonal A)
                (EuclideanSpace.basisFun (Fin N) ℝ j)
            have hy :
                y =
                  (Matrix.toEuclideanLin A).singularValues j.1 •
                    EuclideanSpace.basisFun (Fin M) ℝ i := by
              -- In the diagonal model, the `j`-th column is the `j`-th basis vector scaled by `σ_j`.
              dsimp [y, i]
              simpa using singularValueDiagonal_toEuclideanLin_basisFun_eq_smul A i j.2
            have hB_mem :
                Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j) ∈ S := by
              -- Every column of `B` lies in the range subspace `S`.
              refine ⟨EuclideanSpace.basisFun (Fin N) ℝ j, rfl⟩
            have hproj_min :
                ‖y - S.starProjection y‖ ≤
                  ‖y - Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j)‖ := by
              -- Orthogonal projection onto `S` is the nearest point of `S` to the diagonal column.
              rw [S.starProjection_minimal y]
              change _ ≤
                ‖y -
                  (⟨Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j),
                    hB_mem⟩ : S)‖
              exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ _
            have hproj_sq :
                ‖y - S.starProjection y‖ ^ 2 ≤
                  ‖y - Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 := by
              nlinarith [norm_nonneg (y - S.starProjection y),
                norm_nonneg (y - Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j)),
                hproj_min]
            calc
              (if hj : j.1 < M then
                ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ ⟨j.1, hj⟩)‖ ^ 2)
              else 0)
                  =
                ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2) := by
                    simp [hjM, i]
              _ =
                ‖(Matrix.toEuclideanLin A).singularValues j.1 •
                    EuclideanSpace.basisFun (Fin M) ℝ i -
                  S.starProjection
                    ((Matrix.toEuclideanLin A).singularValues j.1 •
                      EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 := by
                    symm
                    simpa [i] using
                      diagonal_column_projection_error_sq S i
                        ((Matrix.toEuclideanLin A).singularValues j.1)
              _ = ‖y - S.starProjection y‖ ^ 2 := by
                    simp [hy]
              _ ≤
                ‖y - Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 :=
                  hproj_sq
              _ =
                ‖Matrix.toEuclideanLin (singularValueDiagonal A - B)
                    (EuclideanSpace.basisFun (Fin N) ℝ j)‖ ^ 2 := by
                    simp [y]
          · simpa [hjM] using
              sq_nonneg
                (‖Matrix.toEuclideanLin (singularValueDiagonal A - B)
                    (EuclideanSpace.basisFun (Fin N) ℝ j)‖)
        have hdiag_lower :
            ∑ j : Fin N,
                (if hj : j.1 < M then
                  ((Matrix.toEuclideanLin A).singularValues j.1) ^ 2 *
                    (1 -
                      ‖S.orthogonalProjection
                        (EuclideanSpace.basisFun (Fin M) ℝ ⟨j.1, hj⟩)‖ ^ 2)
                else 0) ≤
              ‖singularValueDiagonal A - B‖ ^ 2 := by
          -- Summing the columnwise projection lower bounds gives the Frobenius lower bound.
          rw [frobenius_norm_sq_eq_sum_basis_columns]
          exact Finset.sum_le_sum fun j _ ↦ hcol_lower j
        have hproj_lower :
            ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2) ≤
              ‖singularValueDiagonal A - B‖ ^ 2 := by
          -- Convert the column-indexed lower bound into the `Fin M` weighted deficit expression.
          rw [← column_indexed_weighted_sum_eq
              (A := A)
              (d := fun i : Fin M ↦
                1 -
                  ‖S.orthogonalProjection
                    (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2)
              hσ_zero]
          exact hdiag_lower
        have hindicator :
            ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (if i.1 < q then (1 : ℝ) else 0) =
              Finset.sum (Finset.range q)
                (fun j ↦ ((Matrix.toEuclideanLin A).singularValues j) ^ 2) := by
          -- The first `q` coordinates are exactly the indices selected by the indicator.
          calc
            ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (if i.1 < q then (1 : ℝ) else 0)
                =
              ∑ i : Fin M,
                if i.1 < q then ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  by_cases hi : i.1 < q
                  · simp [hi]
                  · simp [hi]
            _ =
              Finset.sum (Finset.range M)
                (fun n ↦ if n < q then ((Matrix.toEuclideanLin A).singularValues n) ^ 2 else 0) := by
                    simpa using
                      (Fin.sum_univ_eq_sum_range
                        (f := fun n ↦ if n < q then ((Matrix.toEuclideanLin A).singularValues n) ^ 2 else 0)
                        M)
            _ =
              Finset.sum (Finset.range q)
                (fun j ↦ ((Matrix.toEuclideanLin A).singularValues j) ^ 2) := by
                  simpa [mul_ite, zero_mul, one_mul] using
                    weighted_indicator_sum_eq_range
                      (w := fun n ↦ ((Matrix.toEuclideanLin A).singularValues n) ^ 2)
                      hqM
        have hdeficit_ge :
            ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 - if i.1 < q then (1 : ℝ) else 0) ≤
              ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2) := by
          -- Rewriting both deficits as total mass minus captured mass reduces the claim to
          -- `hweighted`.
          rw [weighted_deficit_eq_total_sub
              (w := fun i : Fin M ↦ ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2)
              (a := fun i : Fin M ↦ if i.1 < q then (1 : ℝ) else 0)]
          rw [weighted_deficit_eq_total_sub
              (w := fun i : Fin M ↦ ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2)
              (a := fun i : Fin M ↦
                ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2)]
          rw [hindicator]
          linarith
        have htrunc_sq :
            ‖singularValueDiagonal A - truncatedSingularValueDiagonal A q‖ ^ 2 =
              ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 - if i.1 < q then (1 : ℝ) else 0) :=
          truncated_diagonal_error_sq A q hσ_zero
        have hsq :
            ‖singularValueDiagonal A - truncatedSingularValueDiagonal A q‖ ^ 2 ≤
              ‖singularValueDiagonal A - B‖ ^ 2 := by
          -- Compare the truncation error to the competitor via the weighted deficit bound.
          calc
            ‖singularValueDiagonal A - truncatedSingularValueDiagonal A q‖ ^ 2 =
              ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 - if i.1 < q then (1 : ℝ) else 0) := htrunc_sq
            _ ≤
              ∑ i : Fin M,
                ((Matrix.toEuclideanLin A).singularValues i.1) ^ 2 *
                  (1 -
                    ‖S.orthogonalProjection
                      (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2) := hdeficit_ge
            _ ≤ ‖singularValueDiagonal A - B‖ ^ 2 := hproj_lower
        exact (sq_le_sq₀
          (norm_nonneg (singularValueDiagonal A - truncatedSingularValueDiagonal A q))
          (norm_nonneg (singularValueDiagonal A - B))).mp hsq
      · have htrunc_eq : truncatedSingularValueDiagonal A q = singularValueDiagonal A := by
          -- If `q` already dominates the domain dimension, every diagonal column is retained.
          ext i j
          by_cases hij : i.1 = j.1
          · have hjq : j.1 < q := Nat.lt_of_lt_of_le j.2 (le_of_not_gt hqN)
            have hiq : i.1 < q := hij.symm ▸ hjq
            simp [truncatedSingularValueDiagonal, singularValueDiagonal, hij, hjq]
          · simp [truncatedSingularValueDiagonal, singularValueDiagonal, hij]
        rw [htrunc_eq, sub_self, norm_zero]
        exact norm_nonneg _
  · have hMq : M ≤ q := le_of_not_gt hqM
    have htrunc : truncatedSingularValueDiagonal A q = singularValueDiagonal A := by
      -- When `q` already dominates the row dimension, the truncation keeps every diagonal entry.
      ext i j
      by_cases hij : i.1 = j.1
      · have hiq : i.1 < q := Nat.lt_of_lt_of_le i.2 hMq
        have hjq : j.1 < q := hij.symm ▸ hiq
        simp [truncatedSingularValueDiagonal, singularValueDiagonal, hij, hjq]
      · simp [truncatedSingularValueDiagonal, singularValueDiagonal, hij]
    constructor
    · -- In this regime every matrix has rank at most `q`, so admissibility is automatic.
      rw [htrunc, mem_rankLESet_iff]
      exact le_trans (Matrix.rank_le_height _) hMq
    · intro B hB
      -- The truncation already equals the target matrix, so the error is zero.
      rw [htrunc, sub_self, norm_zero]
      exact norm_nonneg _

/-- Helper for Example 3.9: a projection profile with unit mass on the first `q` coordinates and
zero mass afterwards determines the first-`q` coordinate subspace. -/
private lemma coordinate_subspace_eq_of_projection_profile {M : ℕ} {q : ℕ} (hqM : q < M)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M)))
    (hhead : ∀ i : Fin M, i.1 < q →
      ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 = 1)
    (htail : ∀ i : Fin M, q ≤ i.1 →
      ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 = 0) :
    S =
      Submodule.span ℝ (Set.range fun i : Fin q ↦
        (EuclideanSpace.basisFun (Fin M) ℝ ⟨i.1, Nat.lt_trans i.2 hqM⟩ :
          EuclideanSpace ℝ (Fin M))) := by
  let T : Submodule ℝ (EuclideanSpace ℝ (Fin M)) :=
    Submodule.span ℝ (Set.range fun i : Fin q ↦
      (EuclideanSpace.basisFun (Fin M) ℝ ⟨i.1, Nat.lt_trans i.2 hqM⟩ :
        EuclideanSpace ℝ (Fin M)))
  have hT_le : T ≤ S := by
    -- The head basis vectors lie in `S` because their projection norm is exactly one.
    refine Submodule.span_le.2 ?_
    rintro x ⟨i, rfl⟩
    let j : Fin M := ⟨i.1, Nat.lt_trans i.2 hqM⟩
    have hproj :
        S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ j) =
          EuclideanSpace.basisFun (Fin M) ℝ j :=
      orthogonalProjection_basis_eq_of_norm_sq_eq_one S j (hhead j i.2)
    have hmem :
        (EuclideanSpace.basisFun (Fin M) ℝ j : EuclideanSpace ℝ (Fin M)) ∈ S := by
      rw [← hproj]
      exact (S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ j)).2
    simpa [j] using hmem
  have hT_finrank : Module.finrank ℝ T = q := by
    -- The first `q` coordinate basis vectors are linearly independent.
    classical
    dsimp [T]
    simpa using finrank_span_eq_card
      (((EuclideanSpace.basisFun (Fin M) ℝ).orthonormal).linearIndependent.comp
        (fun i : Fin q ↦ ⟨i.1, Nat.lt_trans i.2 hqM⟩)
        (by
          intro i j hij
          apply Fin.ext
          simpa using congrArg Fin.val hij))
  have hS_finrank_real : (Module.finrank ℝ S : ℝ) = q := by
    -- Summing the projection masses recovers the dimension and matches the indicator profile.
    calc
      (Module.finrank ℝ S : ℝ)
          =
        ∑ i : Fin M, ‖S.orthogonalProjection (EuclideanSpace.basisFun (Fin M) ℝ i)‖ ^ 2 := by
            symm
            exact coordinate_projection_mass_eq_finrank S
      _ = ∑ i : Fin M, (if i.1 < q then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            by_cases hi : i.1 < q
            · rw [hhead i hi]
              simp [hi]
            · rw [htail i (Nat.le_of_not_lt hi)]
              simp [hi]
      _ = q := by
            calc
              (∑ i : Fin M, (if i.1 < q then (1 : ℝ) else 0))
                  =
                Finset.sum (Finset.range M)
                  (fun n ↦ (1 : ℝ) * (if n < q then (1 : ℝ) else 0)) := by
                    simpa [one_mul] using
                      (Fin.sum_univ_eq_sum_range
                        (f := fun n ↦ (1 : ℝ) * (if n < q then (1 : ℝ) else 0))
                        M)
              _ = Finset.sum (Finset.range q) (fun _ ↦ (1 : ℝ)) := by
                    simpa using weighted_indicator_sum_eq_range
                      (w := fun _ ↦ (1 : ℝ)) hqM
              _ = q := by
                    simp
  have hS_finrank : Module.finrank ℝ S = q := by
    exact_mod_cast hS_finrank_real
  exact (Submodule.eq_of_le_of_finrank_eq hT_le (hT_finrank.trans hS_finrank.symm)).symm

/-- Helper for Example 3.9: the span of the first `q` coordinate basis vectors in `ℝ^M`. -/
private def headCoordinateSubspace {M q : ℕ} (hqM : q ≤ M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin M)) :=
  Submodule.span ℝ (Set.range fun i : Fin q ↦
    (EuclideanSpace.basisFun (Fin M) ℝ ⟨i.1, Nat.lt_of_lt_of_le i.2 hqM⟩ :
      EuclideanSpace ℝ (Fin M)))

/-- Helper for Example 3.9: each of the first `q` coordinate basis vectors lies in the head
coordinate subspace. -/
private lemma basisFun_mem_headCoordinateSubspace {M q : ℕ} (hqM : q ≤ M) (i : Fin q) :
    (EuclideanSpace.basisFun (Fin M) ℝ ⟨i.1, Nat.lt_of_lt_of_le i.2 hqM⟩ :
      EuclideanSpace ℝ (Fin M)) ∈ headCoordinateSubspace hqM := by
  -- The spanning generators belong to their own span.
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Helper for Example 3.9: the head coordinate subspace has dimension `q`. -/
private lemma headCoordinateSubspace_finrank {M q : ℕ} (hqM : q ≤ M) :
    Module.finrank ℝ (headCoordinateSubspace hqM) = q := by
  -- The first `q` coordinate basis vectors remain linearly independent in `ℝ^M`.
  have hlin :
      LinearIndependent ℝ
        (fun i : Fin q ↦
          (EuclideanSpace.basisFun (Fin M) ℝ ⟨i.1, Nat.lt_of_lt_of_le i.2 hqM⟩ :
            EuclideanSpace ℝ (Fin M))) := by
    exact ((EuclideanSpace.basisFun (Fin M) ℝ).orthonormal).linearIndependent.comp
      (fun i : Fin q ↦ ⟨i.1, Nat.lt_of_lt_of_le i.2 hqM⟩)
      (by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij)
  -- Compute the finrank from the independent spanning family.
  simpa [headCoordinateSubspace] using finrank_span_eq_card hlin

/-- Helper for Example 3.9: if every coordinate column of `B` lies in a subspace `S`, then the
matrix rank is bounded by the dimension of `S`. -/
private lemma mem_rankLESet_of_basis_images_le_subspace {M N q : ℕ}
    {B : Matrix (Fin M) (Fin N) ℝ} {S : Submodule ℝ (EuclideanSpace ℝ (Fin M))}
    (hS : Module.finrank ℝ S ≤ q)
    (hcol :
      ∀ j : Fin N,
        Matrix.toEuclideanLin B (EuclideanSpace.basisFun (Fin N) ℝ j) ∈ S) :
    B ∈ rankLESet M N q := by
  -- The range is generated by the images of the coordinate basis, so it sits inside `S`.
  have hrange : (Matrix.toEuclideanLin B).range ≤ S := by
    rw [LinearMap.range_le_iff_comap, eq_top_iff]
    intro x hx
    change Matrix.toEuclideanLin B x ∈ S
    rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr x, map_sum]
    refine Submodule.sum_mem S ?_
    intro j hj
    rw [LinearMap.map_smul]
    exact S.smul_mem _ (hcol j)
  -- Convert the range inclusion into the desired matrix-rank bound.
  rw [mem_rankLESet_iff, rank_eq_finrank_range_toEuclideanLin]
  exact (Submodule.finrank_mono hrange).trans hS

/-- Helper for Example 3.9: the `j`-th diagonal singular-value column belongs to the head
coordinate subspace whenever `j < q`. -/
private lemma singularValueDiagonal_basis_mem_headCoordinateSubspace {M N q : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (hqM : q ≤ M) {j : Fin N} (hjq : j.1 < q) :
    Matrix.toEuclideanLin (singularValueDiagonal A)
      (EuclideanSpace.basisFun (Fin N) ℝ j) ∈ headCoordinateSubspace hqM := by
  let i : Fin q := ⟨j.1, hjq⟩
  have hjM : j.1 < M := Nat.lt_of_lt_of_le hjq hqM
  have hcol :
      Matrix.toEuclideanLin (singularValueDiagonal A)
          (EuclideanSpace.basisFun (Fin N) ℝ j) =
        (Matrix.toEuclideanLin A).singularValues j.1 •
          EuclideanSpace.basisFun (Fin M) ℝ ⟨j.1, hjM⟩ := by
    -- Below the cutoff, the diagonal column is the singular value times the matching basis vector.
    dsimp [i]
    simpa using singularValueDiagonal_toEuclideanLin_basisFun_eq_smul A ⟨j.1, hjM⟩ j.2
  -- The head basis vector lies in the subspace, so any scalar multiple stays there.
  rw [hcol]
  exact (headCoordinateSubspace hqM).smul_mem _
    (basisFun_mem_headCoordinateSubspace hqM i)

/-- Helper for Example 3.9: in diagonal singular coordinates, uniqueness of the truncated best
approximation is equivalent to a gap at the truncation index. -/
private lemma diagonal_truncation_unique_iff_gap {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ) (hq_pos : 0 < q) (h_rank : q < A.rank) :
    (∀ Q, IsBestApproximation (singularValueDiagonal A) (rankLESet M N q) Q →
        Q = truncatedSingularValueDiagonal A q) ↔
      (Matrix.toEuclideanLin A).singularValues (q - 1) ≠
        (Matrix.toEuclideanLin A).singularValues q := by
  -- Route correction: the subspace-identification step is now isolated in
  -- `coordinate_subspace_eq_of_projection_profile`; the remaining blocker is the equality bridge
  -- from best-approximation equality to the rigid projection profile and the explicit equal-gap
  -- second minimizer.
  -- TODO: extract the equality case from `diagonal_truncation_is_best`, then combine it with
  -- `projection_mass_rigidity_of_strict_gap` and
  -- `coordinate_subspace_eq_of_projection_profile` in the strict-gap direction, and build an
  -- explicit equal-gap competitor in the reverse direction.
  sorry

/-- Helper for Example 3.9: best approximation for the rank constraint is equivalent to best
approximation after transporting to singular coordinates. -/
private lemma isBestApproximation_orthogonal_transport_iff {M N q : ℕ}
    (A P : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    IsBestApproximation A (rankLESet M N q)
      (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) ↔
      IsBestApproximation
        (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
          (V : Matrix (Fin N) (Fin N) ℝ))
        (rankLESet M N q) P := by
  -- Route correction: isolate the matrix-algebra rewrites first, then transport admissibility and
  -- the minimizing inequality via the Frobenius isometry.
  rw [isBestApproximation_iff_mem_and_forall_norm_sub_le,
    isBestApproximation_iff_mem_and_forall_norm_sub_le]
  constructor
  · rintro ⟨hmem, hmin⟩
    constructor
    · -- Admissibility descends by undoing the orthogonal change of coordinates.
      exact (orthogonal_untransport_mem_rankLESet_iff U V).mp hmem
    · intro B hB
      -- Compare against the untransported competitor in the original coordinates.
      have htransportB :
          (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) ∈
              rankLESet M N q :=
        (orthogonal_untransport_mem_rankLESet_iff U V).mpr hB
      have horig :=
        hmin
          (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
          htransportB
      have hleft :
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖ =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - P‖ := by
        calc
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖
              =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
                (A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                  Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
                (V : Matrix (Fin N) (Fin N) ℝ)‖ := by
                  simpa using
                    frobenius_orthogonal_transport_eq U V A
                      (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
          _ = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - P‖ := by
                rw [orthogonal_untransport_sub_eq A P U V]
      have hright :
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖ =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - B‖ := by
        calc
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖
              =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
                (A - (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
                  Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
                (V : Matrix (Fin N) (Fin N) ℝ)‖ := by
                  simpa using
                    frobenius_orthogonal_transport_eq U V A
                      (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
                        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
          _ = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - B‖ := by
                rw [orthogonal_untransport_sub_eq A B U V]
      calc
        ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
            (V : Matrix (Fin N) (Fin N) ℝ)) - P‖
            = ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖ := hleft.symm
        _ ≤ ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * B) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖ := horig
        _ = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
              (V : Matrix (Fin N) (Fin N) ℝ)) - B‖ := hright
  · rintro ⟨hmem, hmin⟩
    constructor
    · -- Admissibility lifts by transporting the diagonal competitor back to the original basis.
      exact (orthogonal_untransport_mem_rankLESet_iff U V).mpr hmem
    · intro B hB
      -- Transport the original competitor into the singular-vector coordinates.
      have htransportB :
          (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
            (V : Matrix (Fin N) (Fin N) ℝ)) ∈
              rankLESet M N q :=
        (orthogonal_transport_mem_rankLESet_iff U V).mpr hB
      have hdiag :=
        hmin
          (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
            (V : Matrix (Fin N) (Fin N) ℝ))
          htransportB
      have hleft :
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖ =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - P‖ := by
        calc
          ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖
              =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
                (A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                  Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
                (V : Matrix (Fin N) (Fin N) ℝ)‖ := by
                  simpa using
                    frobenius_orthogonal_transport_eq U V A
                      (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                        Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
          _ = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - P‖ := by
                rw [orthogonal_untransport_sub_eq A P U V]
      have hright :
          ‖A - B‖ =
            ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) -
              (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
                (V : Matrix (Fin N) (Fin N) ℝ))‖ := by
        calc
          ‖A - B‖
              =
            ‖((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * (A - B)) *
                (V : Matrix (Fin N) (Fin N) ℝ)‖ := by
                  simpa using frobenius_orthogonal_transport_eq U V A B
          _ = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) -
              (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
                (V : Matrix (Fin N) (Fin N) ℝ))‖ := by
                rw [orthogonal_transport_sub_eq U V A B]
      calc
        ‖A - (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))‖
            = ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
                (V : Matrix (Fin N) (Fin N) ℝ)) - P‖ := hleft
        _ ≤ ‖(Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
              (V : Matrix (Fin N) (Fin N) ℝ)) -
            (((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * B) *
              (V : Matrix (Fin N) (Fin N) ℝ))‖ := hdiag
        _ = ‖A - B‖ := hright.symm

/-- Helper for Example 3.9: uniqueness of the best rank-`q` approximation is likewise equivalent
after transporting to singular coordinates. -/
private lemma unique_bestApproximation_orthogonal_transport_iff {M N q : ℕ}
    (A P : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    (∀ Q, IsBestApproximation A (rankLESet M N q) Q →
        Q =
          (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) ↔
      ∀ Q, IsBestApproximation
        (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
          (V : Matrix (Fin N) (Fin N) ℝ))
        (rankLESet M N q) Q → Q = P := by
  -- Transport any competing best approximation across the orthogonal change of coordinates and
  -- cancel the round trip.
  constructor
  · intro hunique Q hQ
    -- Push the diagonal competitor back to the original coordinates and apply uniqueness there.
    have htransportQ :
        IsBestApproximation A (rankLESet M N q)
          (((U : Matrix (Fin M) (Fin M) ℝ) * Q) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) :=
      (isBestApproximation_orthogonal_transport_iff A Q U V).mpr hQ
    have heq :
        (((U : Matrix (Fin M) (Fin M) ℝ) * Q) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) =
          (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) :=
      hunique _ htransportQ
    have huntransport :
        (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            ((((U : Matrix (Fin M) (Fin M) ℝ) * Q) *
                Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
            (V : Matrix (Fin N) (Fin N) ℝ) =
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            ((((U : Matrix (Fin M) (Fin M) ℝ) * P) *
                Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)))) *
              (V : Matrix (Fin N) (Fin N) ℝ) :=
      congrArg
        (fun X : Matrix (Fin M) (Fin N) ℝ =>
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * X) *
            (V : Matrix (Fin N) (Fin N) ℝ))
        heq
    have huntransport' :
        (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            (((U : Matrix (Fin M) (Fin M) ℝ) * Q) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
            (V : Matrix (Fin N) (Fin N) ℝ) =
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
              (V : Matrix (Fin N) (Fin N) ℝ) := by
      simpa [Matrix.mul_assoc] using huntransport
    calc
      Q = (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            (((U : Matrix (Fin M) (Fin M) ℝ) * Q) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
            (V : Matrix (Fin N) (Fin N) ℝ) := by
              symm
              exact orthogonal_untransport_round_trip U V Q
      _ = (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) *
            (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
              Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) *
              (V : Matrix (Fin N) (Fin N) ℝ) := huntransport'
      _ = P := orthogonal_untransport_round_trip U V P
  · intro hunique Q hQ
    -- Pull the original competitor back to the diagonal model, use uniqueness there, then
    -- transport the resulting identity forward again.
    let Qdiag : Matrix (Fin M) (Fin N) ℝ :=
      ((Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ)) * Q) *
        (V : Matrix (Fin N) (Fin N) ℝ)
    have hQ_as_transport :
        IsBestApproximation A (rankLESet M N q)
          (((U : Matrix (Fin M) (Fin M) ℝ) * Qdiag) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) := by
      simpa [Qdiag, orthogonal_transport_round_trip U V Q] using hQ
    have hQdiag :
        IsBestApproximation
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
            (V : Matrix (Fin N) (Fin N) ℝ))
          (rankLESet M N q) Qdiag :=
      (isBestApproximation_orthogonal_transport_iff A Qdiag U V).mp hQ_as_transport
    have hdiag_eq : Qdiag = P := hunique Qdiag hQdiag
    have htransport :
        (((U : Matrix (Fin M) (Fin M) ℝ) * Qdiag) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) =
          (((U : Matrix (Fin M) (Fin M) ℝ) * P) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) :=
      congrArg
        (fun X : Matrix (Fin M) (Fin N) ℝ =>
          ((U : Matrix (Fin M) (Fin M) ℝ) * X) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))
        hdiag_eq
    calc
      Q = ((U : Matrix (Fin M) (Fin M) ℝ) * Qdiag) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) := by
              symm
              simpa [Qdiag, Matrix.mul_assoc] using orthogonal_transport_round_trip U V Q
      _ = ((U : Matrix (Fin M) (Fin M) ℝ) * P) *
            Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ) := htransport

-- Proof sketch: use the orthogonal invariance of the Frobenius norm to pass to singular-vector
-- coordinates, compare every rank-`≤ q` competitor with the truncated singular-value diagonal via
-- the Hoffman--Wielandt inequality, and analyze the equality case to characterize uniqueness by
-- the gap between the `q`-th and `(q+1)`-st singular values.
/-- Example 3.9: for a chosen singular value decomposition of `A`, the rank-`q` truncation is a
best Frobenius approximation among matrices of rank at most `q`, and it is the unique best
approximation exactly when the `q`-th singular value differs from the next one. -/
theorem eckart_young_theorem {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) (q : ℕ)
    (hq_pos : 0 < q) (h_rank : q < A.rank)
    (U : Matrix.orthogonalGroup (Fin M) ℝ) (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd :
      A =
        ((U : Matrix (Fin M) (Fin M) ℝ) * singularValueDiagonal A) *
          Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ)) :
    IsBestApproximation A
      ({B : Matrix (Fin M) (Fin N) ℝ | B.rank ≤ q})
      (eckartYoungApproximation A q U V) ∧
      ((∀ Q, IsBestApproximation A ({B : Matrix (Fin M) (Fin N) ℝ | B.rank ≤ q}) Q →
          Q = eckartYoungApproximation A q U V) ↔
        (Matrix.toEuclideanLin A).singularValues (q - 1) ≠
          (Matrix.toEuclideanLin A).singularValues q) := by
  -- Route correction: the admissibility part is now isolated above, so the remaining work is the
  -- spectral core on the diagonal singular-value model and its transport through `hsvd`.
  have hcoordA := svd_coordinates_eq_singularValueDiagonal A U V hsvd
  constructor
  · -- First solve the diagonal model, then transport the best-approximation statement back.
    have hdiag :
        IsBestApproximation
          (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
            (V : Matrix (Fin N) (Fin N) ℝ))
          (rankLESet M N q) (truncatedSingularValueDiagonal A q) := by
      simpa [hcoordA] using diagonal_truncation_is_best A q
    have horig :=
      (isBestApproximation_orthogonal_transport_iff A (truncatedSingularValueDiagonal A q) U V).mpr
        hdiag
    simpa [rankLESet, eckartYoungApproximation] using horig
  · -- The uniqueness criterion is likewise the diagonal one transported back to `A`.
    have hdiag :
        (∀ Q, IsBestApproximation
            (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
              (V : Matrix (Fin N) (Fin N) ℝ))
            (rankLESet M N q) Q → Q = truncatedSingularValueDiagonal A q) ↔
          (Matrix.toEuclideanLin A).singularValues (q - 1) ≠
            (Matrix.toEuclideanLin A).singularValues q := by
      simpa [hcoordA] using diagonal_truncation_unique_iff_gap A q hq_pos h_rank
    have htransport :
        (∀ Q, IsBestApproximation A (rankLESet M N q) Q →
            Q =
              (((U : Matrix (Fin M) (Fin M) ℝ) * truncatedSingularValueDiagonal A q) *
                Matrix.transpose (V : Matrix (Fin N) (Fin N) ℝ))) ↔
          ∀ Q, IsBestApproximation
            (Matrix.transpose (U : Matrix (Fin M) (Fin M) ℝ) * A *
              (V : Matrix (Fin N) (Fin N) ℝ))
            (rankLESet M N q) Q → Q = truncatedSingularValueDiagonal A q :=
      unique_bestApproximation_orthogonal_transport_iff A
        (truncatedSingularValueDiagonal A q) U V
    simpa [rankLESet, eckartYoungApproximation] using htransport.trans hdiag

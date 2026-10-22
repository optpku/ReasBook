/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib
import Mathlib.Data.Fin.SuccPred

open Matrix
open scoped MatrixOrder

-- Semantic recall: `Matrix.IsHermitian.eigenvalues₀` is mathlib's ordered Hermitian eigenvalue API.

namespace Matrix.IsHermitian

/-- A real rank-one self-update of a Hermitian matrix is Hermitian. -/
theorem add_smul_vecMulVec_self
    {n : Type*} [Finite n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (σ : ℝ) (u : n → ℝ) :
    (A + σ • Matrix.vecMulVec u u).IsHermitian := by
  simpa using hA.add
    ((Matrix.posSemidef_vecMulVec_self_star u).isHermitian.smul
      (show IsSelfAdjoint σ by simp [IsSelfAdjoint]))

end Matrix.IsHermitian

section

/-- Helper for Chapter01 Theorem 1.2.17: unitary conjugation transports a real rank-one self-update
by applying the same basis change to the update vector. -/
private theorem conjStarAlgAut_rankOneSelfUpdate
    {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix.unitaryGroup n ℝ) (σ : ℝ)
    (u : n → ℝ) :
    (star (Q : Matrix n n ℝ)) * (σ • Matrix.vecMulVec u u) * Q =
      σ • Matrix.vecMulVec ((star (Q : Matrix n n ℝ)) *ᵥ u)
        ((star (Q : Matrix n n ℝ)) *ᵥ u) := by
  -- Rewrite the rank-one term by matrix multiplication, then identify the transported row vector
  -- with the same `mulVec`.
  have hRow :
      u ᵥ* (Q : Matrix n n ℝ) = (star (Q : Matrix n n ℝ)) *ᵥ u := by
    ext i
    simp_rw [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.star_apply]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [star_trivial, mul_comm]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hRow]

/-- Helper for Chapter01 Theorem 1.2.17: conjugating the rank-one update by the eigenbasis of `A`
turns `A` into a diagonal matrix and transports the update vector accordingly. -/
private theorem eigenbasisRankOneUpdateModel
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (σ : ℝ)
    (u : Fin n → ℝ) :
    (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *
        (A + σ • Matrix.vecMulVec u u) *
        hA.eigenvectorUnitary =
      Matrix.diagonal hA.eigenvalues +
        σ •
          Matrix.vecMulVec
            ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
            ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) := by
  -- The spectral theorem handles `A`, and the update term follows from the previous transport
  -- lemma.
  have hDiag :
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) * A *
          hA.eigenvectorUnitary =
        Matrix.diagonal hA.eigenvalues := by
    simpa [Unitary.conjStarAlgAut_apply] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hUpdate :
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *
            (σ • Matrix.vecMulVec u u) *
            hA.eigenvectorUnitary =
        σ •
          Matrix.vecMulVec
            ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
            ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u) := by
    simpa using conjStarAlgAut_rankOneSelfUpdate hA.eigenvectorUnitary σ u
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [hDiag, hUpdate]

/-- Helper for Chapter01 Theorem 1.2.17: the eigenbasis transport preserves the characteristic
polynomial of the rank-one update, so the original matrix and the diagonal model have the same
ordered spectrum. -/
private theorem explicitStarUnitaryConjCharpoly
    {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix.unitaryGroup n ℝ)
    (M : Matrix n n ℝ) :
    ((star (Q : Matrix n n ℝ)) * M * Q).charpoly = M.charpoly := by
  -- Cycle the unitary factor to the front, then cancel the identity `Q * star Q = 1`.
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, ← Unitary.coe_star, Unitary.coe_mul_star_self,
    one_mul]

/-- Helper for Chapter01 Theorem 1.2.17: the explicit eigenbasis model has the same characteristic
polynomial as the original rank-one update. -/
private theorem eigenbasisRankOneUpdateCharpoly
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (σ : ℝ)
    (u : Fin n → ℝ) :
    (A + σ • Matrix.vecMulVec u u).charpoly =
      (Matrix.diagonal hA.eigenvalues +
          σ •
            Matrix.vecMulVec
              ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
              ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)).charpoly := by
  -- Transport the characteristic polynomial across the explicit unitary conjugation first.
  calc
    (A + σ • Matrix.vecMulVec u u).charpoly =
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *
          (A + σ • Matrix.vecMulVec u u) * hA.eigenvectorUnitary).charpoly := by
      symm
      exact explicitStarUnitaryConjCharpoly hA.eigenvectorUnitary (A + σ • Matrix.vecMulVec u u)
    _ =
        (Matrix.diagonal hA.eigenvalues +
          σ •
            Matrix.vecMulVec
              ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)
              ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u)).charpoly := by
      -- Then rewrite the conjugated matrix into the diagonal-plus-rank-one model.
      rw [eigenbasisRankOneUpdateModel (hA := hA) (σ := σ) (u := u)]

/-- Helper for Chapter01 Theorem 1.2.17: reindexing a diagonal-plus-rank-one model permutes both
the diagonal data and the update vector in the expected way. -/
private theorem reindexDiagonalAddSmulVecMulVec
    {m l : Type*} [DecidableEq m] [DecidableEq l] (e : m ≃ l) (d : m → ℝ) (v : l → ℝ)
    (σ : ℝ) :
    Matrix.reindex e e (Matrix.diagonal d + σ • Matrix.vecMulVec (v ∘ e) (v ∘ e)) =
      Matrix.diagonal (d ∘ e.symm) + σ • Matrix.vecMulVec v v := by
  -- Reindexing composes both the diagonal entries and the rank-one vector with the same
  -- permutation.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.reindex_apply, Matrix.vecMulVec_apply]
  · simp [Matrix.reindex_apply, Matrix.vecMulVec_apply, hij]

/-- Helper for Chapter01 Theorem 1.2.17: after reindexing by the hidden cardinality equivalence,
the eigenbasis diagonal model is written directly in ordered `eigenvalues₀` coordinates. -/
private theorem orderedEigenbasisRankOneUpdateCharpoly
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (σ : ℝ)
    (u : Fin n → ℝ) :
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
    let v := (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u
    let w : Fin (Fintype.card (Fin n)) → ℝ := v ∘ e
    (A + σ • Matrix.vecMulVec u u).charpoly =
      (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w).charpoly := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  let v := (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u
  let w : Fin (Fintype.card (Fin n)) → ℝ := v ∘ e
  have hPublic :
      (A + σ • Matrix.vecMulVec u u).charpoly =
        (Matrix.diagonal hA.eigenvalues + σ • Matrix.vecMulVec v v).charpoly :=
    eigenbasisRankOneUpdateCharpoly (hA := hA) (σ := σ) (u := u)
  have hDiag :
      Matrix.diagonal (hA.eigenvalues₀ ∘ e.symm) = Matrix.diagonal hA.eigenvalues := by
    -- This isolates the hidden `Fintype.equivOfCardEq` indexing used by `eigenvalues`.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.IsHermitian.eigenvalues, e]
    · simp [hij]
  have hReindex :
      Matrix.diagonal hA.eigenvalues + σ • Matrix.vecMulVec v v =
        Matrix.reindex e e (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w) := by
    -- Reindex the ordered model, then rewrite the diagonal entries to the public `eigenvalues`
    -- spelling once.
    symm
    calc
      Matrix.reindex e e (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w) =
          Matrix.diagonal (hA.eigenvalues₀ ∘ e.symm) + σ • Matrix.vecMulVec v v := by
        simpa [w] using
          reindexDiagonalAddSmulVecMulVec (e := e) (d := hA.eigenvalues₀) (v := v) (σ := σ)
      _ = Matrix.diagonal hA.eigenvalues + σ • Matrix.vecMulVec v v := by
        rw [hDiag]
  calc
    (A + σ • Matrix.vecMulVec u u).charpoly =
        (Matrix.diagonal hA.eigenvalues + σ • Matrix.vecMulVec v v).charpoly := hPublic
    _ =
        (Matrix.reindex e e
          (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w)).charpoly := by
      rw [hReindex]
    _ =
        (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w).charpoly := by
      rw [Matrix.charpoly_reindex]

/-- Helper for Chapter01 Theorem 1.2.17: real Hermitian matrices with the same characteristic
polynomial have the same ordered eigenvalue list. -/
private theorem orderedEigenvalues₀_list_eq_of_charpoly_eq
    {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {B : Matrix m m ℝ} {C : Matrix k k ℝ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (hChar : B.charpoly = C.charpoly) :
    List.ofFn hB.eigenvalues₀ = List.ofFn hC.eigenvalues₀ := by
  -- Compare the sorted real roots of the shared characteristic polynomial.
  rw [← hB.sort_roots_charpoly_eq_eigenvalues₀,
    ← hC.sort_roots_charpoly_eq_eigenvalues₀, hChar]

/-- Helper for Chapter01 Theorem 1.2.17: the ordered diagonal-plus-rank-one model is Hermitian. -/
private theorem diagonalAddSmulVecMulVec_isHermitian
    {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) (σ : ℝ) (w : m → ℝ) :
    (Matrix.diagonal d + σ • Matrix.vecMulVec w w).IsHermitian := by
  -- The diagonal part is Hermitian, and the rank-one self-update preserves Hermitianity.
  simpa using (Matrix.isHermitian_diagonal (v := d)).add_smul_vecMulVec_self σ w

/-- Helper for Chapter01 Theorem 1.2.17: a nonnegative scalar multiple of `Matrix.vecMulVec u u`
is positive semidefinite. -/
private theorem rankOneSelfUpdatePosSemidef
    {n : Type*} [Finite n] {σ : ℝ} (hσ : 0 ≤ σ) (u : n → ℝ) :
    (σ • Matrix.vecMulVec u u).PosSemidef := by
  -- Start from the standard positivity of a rank-one self outer product.
  have hRankOne : (Matrix.vecMulVec u u).PosSemidef := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star u)
  -- Positive semidefiniteness is preserved by nonnegative scalar multiplication.
  simpa using hRankOne.smul hσ

/-- Helper for Chapter01 Theorem 1.2.17: a nonnegative rank-one self-update is nonnegative in the
Loewner order on real matrices. -/
private theorem rankOneSelfUpdate_nonneg
    {n : Type*} [Finite n] {σ : ℝ} (hσ : 0 ≤ σ) (u : n → ℝ) :
    0 ≤ σ • Matrix.vecMulVec u u := by
  -- Repackage positive semidefiniteness as matrix nonnegativity for later order comparisons.
  exact (rankOneSelfUpdatePosSemidef hσ u).nonneg

/-- Helper for Chapter01 Theorem 1.2.17: adding a nonnegative rank-one self-update increases a
real matrix in the Loewner order. -/
private theorem le_add_rankOneSelfUpdate
    {n : Type*} [Finite n] (A : Matrix n n ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (u : n → ℝ) :
    A ≤ A + σ • Matrix.vecMulVec u u := by
  -- The difference between the updated matrix and the original matrix is exactly the update term.
  rw [Matrix.le_iff]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    rankOneSelfUpdatePosSemidef hσ u


variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
variable (hA : A.IsHermitian) (u : Fin n → ℝ) {σ : ℝ}

/-- Chapter01 Theorem 1.2.17 (1): if `0 < σ`, then each ordered eigenvalue of `A` is bounded above
by the corresponding ordered eigenvalue of `A + σ • Matrix.vecMulVec u u`. -/
theorem eigenvalues_le_rankOneUpdate_eigenvalues_of_pos
    (hσ : 0 < σ) (i : Fin n) :
    hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) ≤
      (hA.add_smul_vecMulVec_self σ u).eigenvalues₀
        (Fin.cast (Fintype.card_fin n).symm i) :=
    by
  by_cases hu : u = 0
  · -- If the update vector vanishes, the rank-one correction is the zero matrix.
    subst hu
    simp
  · -- Route correction: the remaining case needs a PSD-monotonicity bridge for ordered eigenvalues.
    let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
      Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
    let v := (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u
    let w : Fin (Fintype.card (Fin n)) → ℝ := v ∘ e
    have hChar :
        (A + σ • Matrix.vecMulVec u u).charpoly =
          (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w).charpoly := by
      simpa [e, v, w] using
        orderedEigenbasisRankOneUpdateCharpoly (hA := hA) (σ := σ) (u := u)
    have hSpecList :
        List.ofFn (hA.add_smul_vecMulVec_self σ u).eigenvalues₀ =
          List.ofFn (diagonalAddSmulVecMulVec_isHermitian hA.eigenvalues₀ σ w).eigenvalues₀ :=
      orderedEigenvalues₀_list_eq_of_charpoly_eq
        (hB := hA.add_smul_vecMulVec_self σ u)
        (hC := diagonalAddSmulVecMulVec_isHermitian hA.eigenvalues₀ σ w)
        hChar
    -- Route correction: the transport to the ordered diagonal model is now reduced to equality of
    -- the sorted eigenvalue lists. The remaining blocker is the diagonal same-index inequality plus
    -- the pointwise cast extraction from `hSpecList`.
    sorry

/-- Chapter01 Theorem 1.2.17 (3): if `σ < 0`, then each ordered eigenvalue of
`A + σ • Matrix.vecMulVec u u` is bounded above by the corresponding ordered eigenvalue of `A`. -/
theorem rankOneUpdate_eigenvalues_le_eigenvalues_of_neg
    (hσ : σ < 0) (i : Fin n) :
    (hA.add_smul_vecMulVec_self σ u).eigenvalues₀
        (Fin.cast (Fintype.card_fin n).symm i) ≤
      hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i) :=
    by
  -- Rewrite the original matrix as a positive update of the negatively updated matrix.
  have hPos : 0 < -σ := by linarith
  have hStep :=
    eigenvalues_le_rankOneUpdate_eigenvalues_of_pos
      (hA := hA.add_smul_vecMulVec_self σ u) (u := u) (σ := -σ) hPos i
  -- The second update cancels the first one, so the comparison is with `A` again.
  simpa [show A + σ • Matrix.vecMulVec u u + (-σ) • Matrix.vecMulVec u u = A by
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]] using hStep

end

section

/-- Helper for Chapter01 Theorem 1.2.17: a last-coordinate rank-one update disappears after taking
the `Fin.castSucc` principal submatrix. -/
private theorem lastCoordinateUpdatePrincipalCastSucc_eq
    {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (τ : ℝ) :
    (B + τ • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1)).submatrix
        Fin.castSucc Fin.castSucc =
      B.submatrix Fin.castSucc Fin.castSucc := by
  -- Restricting to `Fin.castSucc` removes the last coordinate, so the update term vanishes.
  ext i j
  simp [Matrix.submatrix_apply, Matrix.vecMulVec, Fin.castSucc_ne_last]

/-- Helper for Chapter01 Theorem 1.2.17: replacing the last row by the last basis vector extracts
the `Fin.castSucc` principal minor. -/
private theorem det_updateRow_last_single_eq_det_castSucc_submatrix
    {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by
  -- Expand along the replaced last row; only the last-column cofactor survives.
  rw [Matrix.det_succ_row _ (Fin.last n)]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [Matrix.submatrix_updateRow_succAbove]
    simp [Fin.succAbove_last]
  · intro j hj hne
    simp [hne]
  · intro h
    simp at h

/-- Helper for Chapter01 Theorem 1.2.17: the last-coordinate rank-one update changes the
characteristic matrix by a single last-row correction. -/
private theorem charmatrix_lastCoordinateUpdate_eq_updateRow
    {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (τ : ℝ) :
    Matrix.charmatrix
        (B + τ • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1)) =
      (Matrix.charmatrix B).updateRow (Fin.last n)
        ((Matrix.charmatrix B (Fin.last n)) +
          (-Polynomial.C τ) • Pi.single (Fin.last n) 1) := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst hi
    by_cases hj : j = Fin.last n
    · -- The unique changed diagonal entry picks up the `-τ` correction.
      subst hj
      simp [Matrix.vecMulVec, sub_eq_add_neg, add_left_comm, add_comm]
    · -- Off-diagonal entries in the last row are unchanged because the update is diagonal.
      simp [Matrix.charmatrix_apply, Matrix.vecMulVec, hj, sub_eq_add_neg]
  · -- Rows away from the last coordinate are untouched by the update.
    simp [Matrix.updateRow_apply, hi, Matrix.charmatrix_apply, Matrix.vecMulVec, sub_eq_add_neg]

/-- Helper for Chapter01 Theorem 1.2.17: updating only the last diagonal entry subtracts the
principal `Fin.castSucc` characteristic polynomial. -/
private theorem charpoly_lastCoordinateUpdate
    {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (τ : ℝ) :
    (B + τ • Matrix.vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1)).charpoly =
      B.charpoly - Polynomial.C τ * (B.submatrix Fin.castSucc Fin.castSucc).charpoly := by
  -- Rewrite the updated characteristic matrix as a single last-row perturbation.
  rw [Matrix.charpoly, Matrix.charpoly, charmatrix_lastCoordinateUpdate_eq_updateRow]
  -- Linearize the determinant in that row, then identify the surviving cofactor.
  rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
  rw [det_updateRow_last_single_eq_det_castSucc_submatrix]
  have hPrincipalCharmatrix :
      (Matrix.charmatrix B).submatrix Fin.castSucc Fin.castSucc =
        Matrix.charmatrix (B.submatrix Fin.castSucc Fin.castSucc) := by
    -- Deleting the last row and column commutes with forming the characteristic matrix.
    ext i j
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij]
  rw [hPrincipalCharmatrix, Matrix.charpoly]
  ring

variable {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
variable (hA : A.IsHermitian) (u : Fin (n + 1) → ℝ) {σ : ℝ}

/-- Helper for Chapter01 Theorem 1.2.17: on `Fin (n + 1)`, the public `eigenvalues` indexing
is the ordered `eigenvalues₀` list reindexed by the hidden cardinality equivalence. -/
private theorem eigenvalues_eq_eigenvalues₀_reindex
    {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian)
    (i : Fin (n + 1)) :
    hA.eigenvalues i =
      hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := by
  -- Expose the hidden reindexing once so later work can separate ordered and public indices.
  rfl

/-- Helper for Chapter01 Theorem 1.2.17: in the ordered `eigenvalues₀` indexing on
`Fin (n + 1)`, the predecessor position `Fin.castSucc i` comes before the successor position
`i.succ`. -/
private theorem orderedIndexCastSucc_le_orderedIndexSucc
    {n : ℕ} (i : Fin n) :
    Fin.cast (Fintype.card_fin (n + 1)).symm (Fin.castSucc i) ≤
      Fin.cast (Fintype.card_fin (n + 1)).symm i.succ := by
  -- This is the exact index comparison needed to invoke `eigenvalues₀_antitone`.
  simpa using Fin.castSucc_le_succ i

/-- Chapter01 Theorem 1.2.17 (2): if `0 < σ`, then every nonterminal ordered eigenvalue of
`A + σ • Matrix.vecMulVec u u` is bounded above by the preceding ordered eigenvalue of `A`. -/
theorem rankOneUpdate_eigenvalues_succ_le_eigenvalues_of_pos
    (hσ : 0 < σ) (i : Fin n) :
    (hA.add_smul_vecMulVec_self σ u).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm i.succ) ≤
      hA.eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm (Fin.castSucc i)) :=
    by
  by_cases hu : u = 0
  · -- If the update vector vanishes, this reduces to the antitonicity of `eigenvalues₀`.
    subst hu
    simpa using
      (hA.eigenvalues₀_antitone
        (orderedIndexCastSucc_le_orderedIndexSucc i))
  · -- Route correction: the remaining case needs the basis-change normalization to a
    -- diagonal-plus-rank-one model. The ordered-index bookkeeping needed for the zero branch is
    -- already isolated in `orderedIndexCastSucc_le_orderedIndexSucc`.
    let e : Fin (Fintype.card (Fin (n + 1))) ≃ Fin (n + 1) :=
      Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))
    let v := (star (hA.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) *ᵥ u
    let w : Fin (Fintype.card (Fin (n + 1))) → ℝ := v ∘ e
    have hChar :
        (A + σ • Matrix.vecMulVec u u).charpoly =
          (Matrix.diagonal hA.eigenvalues₀ + σ • Matrix.vecMulVec w w).charpoly := by
      simpa [e, v, w] using
        orderedEigenbasisRankOneUpdateCharpoly (hA := hA) (σ := σ) (u := u)
    have hSpecList :
        List.ofFn (hA.add_smul_vecMulVec_self σ u).eigenvalues₀ =
          List.ofFn (diagonalAddSmulVecMulVec_isHermitian hA.eigenvalues₀ σ w).eigenvalues₀ :=
      orderedEigenvalues₀_list_eq_of_charpoly_eq
        (hB := hA.add_smul_vecMulVec_self σ u)
        (hC := diagonalAddSmulVecMulVec_isHermitian hA.eigenvalues₀ σ w)
        hChar
    -- Route correction: the transport to the ordered diagonal model is now reduced to equality of
    -- the sorted eigenvalue lists. The remaining blocker is the diagonal shifted inequality plus
    -- the pointwise cast extraction from `hSpecList`.
    sorry

/-- Chapter01 Theorem 1.2.17 (4): if `σ < 0`, then every nonterminal ordered eigenvalue of `A` is
bounded above by the preceding ordered eigenvalue of `A + σ • Matrix.vecMulVec u u`. -/
theorem eigenvalues_succ_le_rankOneUpdate_eigenvalues_of_neg
    (hσ : σ < 0) (i : Fin n) :
    hA.eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm i.succ) ≤
      (hA.add_smul_vecMulVec_self σ u).eigenvalues₀
        (Fin.cast (Fintype.card_fin (n + 1)).symm (Fin.castSucc i)) :=
    by
  -- Rewrite the original matrix as a positive update of the negatively updated matrix.
  have hPos : 0 < -σ := by linarith
  have hStep :=
    rankOneUpdate_eigenvalues_succ_le_eigenvalues_of_pos
      (hA := hA.add_smul_vecMulVec_self σ u) (u := u) (σ := -σ) hPos i
  -- The second update cancels the first one, leaving the original Hermitian matrix.
  simpa [show A + σ • Matrix.vecMulVec u u + (-σ) • Matrix.vecMulVec u u = A by
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]] using hStep

end

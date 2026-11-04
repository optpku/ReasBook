/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_4
import Mathlib.Analysis.InnerProductSpace.Orientation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open InnerProductSpace Module

section Theorem92

namespace Matrix

variable {n : ℕ}

/-- The product of the Euclidean norms of the columns of a square real matrix. -/
noncomputable def columnNormProduct (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ j : Fin n, ‖WithLp.toLp 2 (B.col j)‖

/-- Expanding `B.columnNormProduct` gives the product of the norms of the canonical columns
`B.col j`. -/
theorem columnNormProduct_eq (B : Matrix (Fin n) (Fin n) ℝ) :
    B.columnNormProduct = ∏ j : Fin n, ‖WithLp.toLp 2 (B.col j)‖ :=
  rfl

end Matrix

/-- Helper for Theorem 9.2: the `j`th vector of `euclideanBasisOfMatrix B hB` is exactly the
Euclidean-space column `B.col j`. -/
lemma euclideanBasisOfMatrix_apply_eq_col
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B.det)
    (j : Fin n) :
    euclideanBasisOfMatrix B hB j = WithLp.toLp 2 (B.col j) := by
  -- Evaluate the transported basis vector in coordinates to recover the concrete matrix column.
  ext i
  have hcoord :=
    congrFun
      (Matrix.toLin_self
        (v₁ := Pi.basisFun ℝ (Fin n))
        (v₂ := Pi.basisFun ℝ (Fin n))
        B
        j)
      i
  have hsum :
      ∑ x, B x j * ((Pi.basisFun ℝ (Fin n)) x i) = B i j := by
    rw [Finset.sum_eq_single i]
    · simp [Pi.basisFun_apply]
    · intro x _ hxi
      simp [Pi.basisFun_apply, hxi]
    · intro hi
      simp at hi
  calc
    (euclideanBasisOfMatrix B hB j) i = ∑ x, B x j * ((Pi.basisFun ℝ (Fin n)) x i) := by
      simpa [euclideanBasisOfMatrix, basisOfMatrix, Pi.basisFun_apply] using hcoord
    _ = B i j := hsum

/-- Helper for Theorem 9.2: the standard Euclidean basis determinant of the Euclidean column basis
attached to `B` is exactly `B.det`. -/
lemma basisFun_det_euclideanBasisOfMatrix_eq_det
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B.det) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det (euclideanBasisOfMatrix B hB) = B.det := by
  -- Route correction: first identify the Euclidean basis vectors with the concrete matrix columns.
  have hcols :
      (euclideanBasisOfMatrix B hB : Fin n → EuclideanSpace ℝ (Fin n)) =
        fun j ↦ WithLp.toLp 2 (B.col j) := by
    funext j
    simpa using euclideanBasisOfMatrix_apply_eq_col B hB j
  -- The determinant of the concrete Euclidean column family is the matrix determinant.
  rw [hcols, Module.Basis.det_apply]
  congr 1
  ext i j
  simp [Matrix.col_apply, Basis.toMatrix_apply]

/-- Helper for Theorem 9.2: the diagonal Gram-Schmidt inner product is the squared norm of the
current Gram-Schmidt vector. -/
lemma gramSchmidtBasis_inner_self_eq_norm_sq
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) :
    ⟪gramSchmidt ℝ b i, b i⟫_ℝ = ‖gramSchmidt ℝ b i‖ ^ 2 := by
  -- Expand the basis vector into its Gram-Schmidt part and the earlier correction terms.
  rw [gramSchmidt_def'' ℝ b i]
  have hsum :
      ∑ x ∈ Finset.Iio i,
        ⟪gramSchmidt ℝ b x, b i⟫_ℝ / ↑‖gramSchmidt ℝ b x‖ ^ 2 *
          ⟪gramSchmidt ℝ b i, gramSchmidt ℝ b x⟫_ℝ = 0 := by
    -- Every correction term vanishes because the Gram-Schmidt family is orthogonal.
    apply Finset.sum_eq_zero
    intro x hx
    have hix : i ≠ x := by
      exact ne_of_gt (Finset.mem_Iio.mp hx)
    simp [gramSchmidt_orthogonal ℝ b hix]
  -- Only the diagonal inner product survives.
  simp [inner_add_right, inner_sum, inner_smul_right, hsum]

/-- Helper for Theorem 9.2: the diagonal entry of the Gram-Schmidt orthonormal basis against the
input basis is the norm of the current Gram-Schmidt vector. -/
lemma gramSchmidtOrthonormalBasis_inner_eq_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) :
    let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
      gramSchmidtOrthonormalBasis (by simp) b
    ⟪ob i, b i⟫_ℝ = ‖gramSchmidtBasis b i‖ := by
  dsimp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  have hnonzero : gramSchmidt ℝ b i ≠ 0 := gramSchmidt_ne_zero i b.linearIndependent
  have hnormed : gramSchmidtNormed ℝ b i ≠ 0 := by
    simp [gramSchmidtNormed, hnonzero]
  have hnorm_ne : ‖gramSchmidt ℝ b i‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr hnonzero
  -- Replace the orthonormal basis vector by the normalized Gram-Schmidt vector.
  rw [gramSchmidtOrthonormalBasis_apply (h := hdim) (f := b) (i := i) hnormed]
  -- The diagonal Gram-Schmidt identity converts the inner product into the norm.
  calc
    ⟪gramSchmidtNormed ℝ b i, b i⟫_ℝ = ‖gramSchmidt ℝ b i‖⁻¹ * ⟪gramSchmidt ℝ b i, b i⟫_ℝ := by
      simp [gramSchmidtNormed, inner_smul_left]
    _ = ‖gramSchmidt ℝ b i‖⁻¹ * ‖gramSchmidt ℝ b i‖ ^ 2 := by
      rw [gramSchmidtBasis_inner_self_eq_norm_sq]
    _ = ‖gramSchmidt ℝ b i‖ := by
      rw [pow_two]
      field_simp [hnorm_ne]
    _ = ‖gramSchmidtBasis b i‖ := by
      simp [coe_gramSchmidtBasis]

/-- Helper for Theorem 9.2: the off-diagonal Gram-Schmidt orthonormal coordinate of `b j` along
the earlier direction `k` is `μ_{j,k} ‖g_k‖`. -/
lemma gramSchmidtOrthonormalBasis_inner_eq_coefficient_mul_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (j k : Fin n) :
    let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
      gramSchmidtOrthonormalBasis (by simp) b
    ⟪ob k, b j⟫_ℝ = gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖ := by
  dsimp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  have hnonzero : gramSchmidt ℝ b k ≠ 0 := gramSchmidt_ne_zero k b.linearIndependent
  have hnormed : gramSchmidtNormed ℝ b k ≠ 0 := by
    simp [gramSchmidtNormed, hnonzero]
  -- Replace the orthonormal basis vector by the normalized Gram-Schmidt vector.
  rw [gramSchmidtOrthonormalBasis_apply (h := hdim) (f := b) (i := k) hnormed]
  -- Rewrite the resulting inner product using the definition of the Gram-Schmidt coefficient.
  calc
    ⟪gramSchmidtNormed ℝ b k, b j⟫_ℝ = ‖gramSchmidt ℝ b k‖⁻¹ * ⟪gramSchmidt ℝ b k, b j⟫_ℝ := by
      simp [gramSchmidtNormed, inner_smul_left]
    _ = ‖gramSchmidt ℝ b k‖⁻¹ * ⟪b j, gramSchmidt ℝ b k⟫_ℝ := by
      rw [real_inner_comm]
    _ = gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖ := by
      rw [gram_schmidt_coefficient, coe_gramSchmidtBasis, div_eq_mul_inv]
      field_simp [norm_ne_zero_iff.mpr hnonzero]

/-- Helper for Theorem 9.2: the absolute determinant of a Euclidean basis is the product of the
norms of its Gram-Schmidt vectors. -/
lemma abs_basisFun_det_eq_prod_gramSchmidtBasis_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| = ∏ i : Fin n, ‖gramSchmidtBasis b i‖ := by
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    gramSchmidtOrthonormalBasis hdim b
  have hdet : ob.toBasis.det b = ∏ i, ⟪ob i, b i⟫_ℝ := by
    -- The Gram-Schmidt orthonormal basis makes the change-of-basis matrix upper triangular.
    simpa [ob] using gramSchmidtOrthonormalBasis_det hdim b
  have hdiag : ∀ i : Fin n, ⟪ob i, b i⟫_ℝ = ‖gramSchmidtBasis b i‖ := by
    -- Each diagonal entry is exactly the norm of the current Gram-Schmidt vector.
    intro i
    simpa [ob] using gramSchmidtOrthonormalBasis_inner_eq_norm b i
  have hprod : ∏ i, ⟪ob i, b i⟫_ℝ = ∏ i, ‖gramSchmidtBasis b i‖ := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    exact hdiag i
  calc
    |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| = |o.volumeForm b| := by
      -- Compare the standard basis determinant with the oriented Euclidean volume form.
      symm
      simpa [o] using (o.volumeForm_robust' (EuclideanSpace.basisFun (Fin n) ℝ) b)
    _ = |ob.toBasis.det b| := by
      -- The same volume form can be read in the Gram-Schmidt orthonormal basis.
      simpa [o] using (o.volumeForm_robust' ob b)
    _ = |∏ i, ⟪ob i, b i⟫_ℝ| := by
      rw [hdet]
    _ = ∏ i, ‖gramSchmidtBasis b i‖ := by
      rw [hprod, abs_of_nonneg]
      apply Finset.prod_nonneg
      intro i hi
      exact norm_nonneg _

/-- Helper for Theorem 9.2: consecutive Gram-Schmidt vectors in a reduced basis satisfy the
half-growth inequality on squared norms. -/
lemma reducedBasis_adjacent_gramSchmidt_sq_ge_half
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : IsReducedBasis b)
    (j : Fin (n - 1)) :
    let jCurrent : Fin n := ⟨j.1, Nat.lt_of_lt_pred j.2⟩
    let jNext : Fin n := ⟨j.1 + 1, Nat.succ_lt_of_lt_pred j.2⟩
    ((1 : ℝ) / 2) * ‖gramSchmidtBasis b jCurrent‖ ^ 2 ≤ ‖gramSchmidtBasis b jNext‖ ^ 2 := by
  dsimp
  let jCurrent : Fin n := ⟨j.1, Nat.lt_of_lt_pred j.2⟩
  let jNext : Fin n := ⟨j.1 + 1, Nat.succ_lt_of_lt_pred j.2⟩
  have hjlt : jCurrent < jNext := by
    simp [jCurrent, jNext]
  have hstep :
      ‖gramSchmidtBasis b jCurrent‖ ≤
        ‖gramSchmidtBasis b jNext +
          (gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent‖ := by
    -- Unpack the reduced-basis Step 2 inequality at the adjacent pair.
    simpa [jCurrent, jNext] using hb.condition_ii j
  have hsq :
      ‖gramSchmidtBasis b jCurrent‖ ^ 2 ≤
        ‖gramSchmidtBasis b jNext +
          (gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent‖ ^ 2 := by
    -- Squaring preserves the inequality because both norms are nonnegative.
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hstep
  have hmu :
      |gram_schmidt_coefficient b jNext jCurrent| ≤ (1 : ℝ) / 2 := by
    -- The reduced-basis size-reduction inequality bounds the Gram-Schmidt coefficient.
    exact hb.condition_i hjlt
  have hmu_sq :
      (gram_schmidt_coefficient b jNext jCurrent) ^ 2 ≤ (1 : ℝ) / 4 := by
    nlinarith
  have horth :
      ⟪gramSchmidtBasis b jNext,
        (gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent⟫_ℝ = 0 := by
    -- The two adjacent Gram-Schmidt vectors are orthogonal.
    simp [inner_smul_right, coe_gramSchmidtBasis, gramSchmidt_orthogonal ℝ b hjlt.ne']
  have hnorm_add :
      ‖gramSchmidtBasis b jNext +
          (gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent‖ ^ 2 =
        ‖gramSchmidtBasis b jNext‖ ^ 2 +
          ‖(gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent‖ ^ 2 := by
    -- Orthogonality removes the cross term in the norm-square expansion.
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hnorm_smul :
      ‖(gram_schmidt_coefficient b jNext jCurrent) • gramSchmidtBasis b jCurrent‖ ^ 2 =
        (gram_schmidt_coefficient b jNext jCurrent) ^ 2 * ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by
    -- Rewrite the squared norm of the scalar multiple into the coefficient square times `‖g_j‖²`.
    rw [norm_smul, Real.norm_eq_abs, pow_two]
    calc
      (|gram_schmidt_coefficient b jNext jCurrent| * ‖gramSchmidtBasis b jCurrent‖) *
          (|gram_schmidt_coefficient b jNext jCurrent| * ‖gramSchmidtBasis b jCurrent‖)
          = |gram_schmidt_coefficient b jNext jCurrent| ^ 2 *
              ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by
              ring
      _ = (gram_schmidt_coefficient b jNext jCurrent) ^ 2 *
            ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by
              rw [sq_abs]
  -- Substitute the orthogonal decomposition and the coefficient bound.
  nlinarith [hsq, hmu_sq, hnorm_add, hnorm_smul]

/-- Helper for Theorem 9.2: the prefix sum of earlier Gram-Schmidt squared norms is controlled by
the current Gram-Schmidt squared norm in a reduced basis. -/
lemma reducedBasisPrefixGramSchmidtSqSum_le
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ∑ i ∈ Finset.Iio j, ‖gramSchmidtBasis b i‖ ^ 2 ≤
      (((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j‖ ^ 2 := by
  -- Route correction: package the repeated `Fin` interval normalization as one induction.
  induction j using Fin.induction with
  | zero =>
      -- The base prefix sum is empty.
      rw [show Finset.Iio (0 : Fin (m + 1)) = ∅ by ext i; simp, Finset.sum_empty]
      norm_num
  | succ j ih =>
      have ih' :
          ∑ i ∈ Finset.Iio j.castSucc, ‖gramSchmidtBasis b i‖ ^ 2 ≤
            (((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
        simpa using ih
      have hstepHalf :
          ((1 : ℝ) / 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 ≤
            ‖gramSchmidtBasis b j.succ‖ ^ 2 := by
        simpa using reducedBasis_adjacent_gramSchmidt_sq_ge_half b hb j
      have hstep :
          ‖gramSchmidtBasis b j.castSucc‖ ^ 2 ≤
            2 * ‖gramSchmidtBasis b j.succ‖ ^ 2 := by
        nlinarith
      have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ j.1 := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hfactor_nonneg : 0 ≤ (2 : ℝ) ^ (j.1 + 1) - 1 := by
        have hpow_ge_one' : (1 : ℝ) ≤ (2 : ℝ) ^ (j.1 + 1) := by
          exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      have hIioSucc : Finset.Iio j.succ = Finset.Iic j.castSucc := by
        ext i
        simp [Fin.lt_def, Fin.le_iff_val_le_val]
      -- Add the new predecessor term and use the adjacent half-growth inequality once.
      calc
        ∑ i ∈ Finset.Iio j.succ, ‖gramSchmidtBasis b i‖ ^ 2
            = ∑ i ∈ Finset.Iio j.castSucc, ‖gramSchmidtBasis b i‖ ^ 2 +
                ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
              rw [hIioSucc, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
              simp [add_comm]
        _ ≤ (((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 +
              ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
              nlinarith [ih']
        _ = (((2 : ℝ) ^ (j.1 + 1)) - 1) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
              ring
        _ ≤ (((2 : ℝ) ^ (j.1 + 1)) - 1) * (2 * ‖gramSchmidtBasis b j.succ‖ ^ 2) := by
              nlinarith [hstep, hfactor_nonneg]
        _ = ((((2 : ℝ) ^ (j.succ.1 + 1)) - 2) * ‖gramSchmidtBasis b j.succ‖ ^ 2) := by
              rw [Fin.val_succ, pow_succ]
              ring

/-- Helper for Theorem 9.2: each column of a reduced basis is controlled by the current
Gram-Schmidt vector with the textbook `2^j` squared factor. -/
lemma reducedBasisColumnSq_le_pow_mul_gramSchmidtSq
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ‖b j‖ ^ 2 ≤ (2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = Fintype.card (Fin (m + 1)) := by
    simp
  let ob : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))) :=
    gramSchmidtOrthonormalBasis hdim b
  let term : Fin (m + 1) → ℝ := fun k ↦ ⟪ob k, b j⟫_ℝ ^ 2
  have hparseval : ‖b j‖ ^ 2 = ∑ k : Fin (m + 1), term k := by
    -- Parseval rewrites the squared column norm as the sum of orthonormal coordinates.
    symm
    simpa [ob, term] using OrthonormalBasis.sum_sq_inner_right ob (b j)
  have htail :
      ∀ k ∈ Finset.univ \ Finset.Iic j, term k = 0 := by
    intro k hk
    have hknot : k ∉ Finset.Iic j := (Finset.mem_sdiff.mp hk).2
    have hjk : j < k := by
      simp only [Finset.mem_Iic, not_le] at hknot
      exact hknot
    -- Coordinates above the diagonal vanish by Gram-Schmidt triangularity.
    have hzero : ⟪ob k, b j⟫_ℝ = 0 := by
      simpa [ob] using
        (InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
          (h := hdim)
          (f := b)
          hjk)
    simp [term, hzero]
  have hdiag :
      term j = ‖gramSchmidtBasis b j‖ ^ 2 := by
    -- The diagonal orthonormal coordinate is exactly the current Gram-Schmidt norm.
    rw [show term j = (⟪ob j, b j⟫_ℝ) ^ 2 by rfl]
    rw [gramSchmidtOrthonormalBasis_inner_eq_norm]
  have hoffdiag :
      ∀ k ∈ Finset.Iio j, term k ≤ ((1 : ℝ) / 4) * ‖gramSchmidtBasis b k‖ ^ 2 := by
    intro k hk
    have hmu : |gram_schmidt_coefficient b j k| ≤ (1 : ℝ) / 2 := by
      exact hb.condition_i (Finset.mem_Iio.mp hk)
    have hcoeff :
        term k =
          (gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖) ^ 2 := by
      rw [show term k = (⟪ob k, b j⟫_ℝ) ^ 2 by rfl]
      rw [gramSchmidtOrthonormalBasis_inner_eq_coefficient_mul_norm]
    have hcoeffSq :
        (gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖) ^ 2 ≤
          ((1 : ℝ) / 4) * ‖gramSchmidtBasis b k‖ ^ 2 := by
      have hmu_sq : (gram_schmidt_coefficient b j k) ^ 2 ≤ (1 : ℝ) / 4 := by
        have habs_sq : |gram_schmidt_coefficient b j k| ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
          nlinarith [abs_nonneg (gram_schmidt_coefficient b j k), hmu]
        have hmu_sq' : (gram_schmidt_coefficient b j k) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
          simpa [sq_abs] using habs_sq
        norm_num at hmu_sq' ⊢
        exact hmu_sq'
      nlinarith [hmu_sq, norm_nonneg (gramSchmidtBasis b k)]
    simpa [hcoeff] using hcoeffSq
  have hprefix :
      ∑ k ∈ Finset.Iio j, term k ≤
        ((1 : ℝ) / 4) * ((((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) := by
    -- Bound each lower-triangular coordinate by the reduced-basis coefficient estimate.
    calc
      ∑ k ∈ Finset.Iio j, term k
          ≤ ∑ k ∈ Finset.Iio j, (((1 : ℝ) / 4) * ‖gramSchmidtBasis b k‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro k hk
              exact hoffdiag k hk
      _ = ((1 : ℝ) / 4) * ∑ k ∈ Finset.Iio j, ‖gramSchmidtBasis b k‖ ^ 2 := by
            rw [← Finset.mul_sum]
      _ ≤ ((1 : ℝ) / 4) * ((((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) := by
            have hsum := reducedBasisPrefixGramSchmidtSqSum_le b hb j
            nlinarith
  have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ j.1 := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  -- Keep only the lower-triangular coordinates, then use the coefficient and prefix-sum bounds.
  calc
    ‖b j‖ ^ 2 = ∑ k ∈ Finset.Iic j, term k := by
      rw [hparseval]
      calc
        ∑ k : Fin (m + 1), term k
            = ∑ k : Fin (m + 1), if k ≤ j then term k else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hkj : k ≤ j
              · simp [hkj]
              · have hkout : k ∈ Finset.univ \ Finset.Iic j := by
                  simp [Finset.mem_Iic, hkj]
                have hzero : term k = 0 := htail k hkout
                simp [hkj, hzero]
        _ = ∑ k ∈ Finset.Iic j, term k := by
              rw [← Finset.sum_filter]
              congr 1
              ext k
              simp [Finset.mem_Iic]
    _ = ∑ k ∈ Finset.Iio j, term k + ‖gramSchmidtBasis b j‖ ^ 2 := by
          rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
          simp [hdiag, add_comm]
    _ ≤ ((1 : ℝ) / 4) * ((((2 : ℝ) ^ (j.1 + 1)) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) +
          ‖gramSchmidtBasis b j‖ ^ 2 := by
          nlinarith [hprefix]
    _ = (((2 : ℝ) ^ j.1 + 1) / 2) * ‖gramSchmidtBasis b j‖ ^ 2 := by
          rw [pow_succ]
          ring
    _ ≤ (2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2 := by
          have hgs_nonneg : 0 ≤ ‖gramSchmidtBasis b j‖ ^ 2 := sq_nonneg _
          nlinarith

/-- Helper for Theorem 9.2: unsquaring the per-column estimate yields the `Real.rpow` factor that
matches the textbook statement. -/
lemma reducedBasisNormLeRpowTwoMulGramSchmidtBasisNorm
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ‖b j‖ ≤ Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
  have hsq := reducedBasisColumnSq_le_pow_mul_gramSchmidtSq b hb j
  have hsqrt :
      Real.sqrt (‖b j‖ ^ 2) ≤
        Real.sqrt ((2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2) := by
    exact Real.sqrt_le_sqrt hsq
  -- Take square roots on both sides and normalize the `2` factor into `Real.rpow`.
  calc
    ‖b j‖ = Real.sqrt (‖b j‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt ((2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2) := hsqrt
    _ = Real.sqrt ((2 : ℝ) ^ j.1) * ‖gramSchmidtBasis b j‖ := by
          rw [Real.sqrt_mul (pow_nonneg (by positivity) _), Real.sqrt_sq_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
    _ = Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
          congr 1
          norm_num [div_eq_mul_inv]

/-- Theorem 9.2. If a nonsingular square matrix is reduced, then the product of the Euclidean
norms of its columns is at most `2^(n(n - 1)/4)` times the absolute value of its determinant.
This matrix-facing statement is routed through the chapter's canonical reduced-basis owner on the
associated Euclidean basis `euclideanBasisOfMatrix B hB`. -/
theorem reduced_matrix_column_norm_product_le_abs_det
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B.det)
    (hreduced : IsReducedBasis (euclideanBasisOfMatrix B hB)) :
    B.columnNormProduct ≤
      Real.rpow (2 : ℝ) (((n : ℝ) * (n - 1)) / 4) * |B.det| := by
  cases n with
  | zero =>
      -- In dimension `0`, both sides are the empty product `1`.
      simp [Matrix.columnNormProduct]
  | succ n =>
    let b : Basis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))) := euclideanBasisOfMatrix B hB
    have hbcol :
        ∀ j : Fin (n + 1), ‖WithLp.toLp 2 (B.col j)‖ = ‖b j‖ := by
      intro j
      -- The Euclidean basis attached to `B` is the concrete column family.
      simpa [b] using congrArg norm (euclideanBasisOfMatrix_apply_eq_col B hB j).symm
    have hnorm :
        ∀ j : Fin (n + 1),
          ‖WithLp.toLp 2 (B.col j)‖ ≤
            Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
      intro j
      simpa [hbcol j] using reducedBasisNormLeRpowTwoMulGramSchmidtBasisNorm b hreduced j
    have hprodRpow :
        (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) =
          Real.rpow (2 : ℝ) ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) := by
      have hsum :
          ∑ j : Fin (n + 1), ((j : ℝ) / 2) = (↑n + 1) * ↑n / 4 := by
        have hsumRange :
            ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), (i : ℝ) / 2 = (↑m + 1) * ↑m / 4 := by
          intro m
          induction m with
          | zero =>
              norm_num
          | succ m ih =>
              rw [Finset.sum_range_succ, ih]
              norm_num [Nat.cast_add]
              ring
        calc
          ∑ j : Fin (n + 1), ((j : ℝ) / 2) = ∑ i ∈ Finset.range (n + 1), (i : ℝ) / 2 := by
            rw [Fin.sum_univ_eq_sum_range fun j : ℕ => (j : ℝ) / 2]
          _ = (↑n + 1) * ↑n / 4 := by
            exact hsumRange n
      -- Collapse the product of the `2^(j/2)` factors into the closed form exponent.
      calc
        (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2))
            = Real.rpow (2 : ℝ) (∑ j : Fin (n + 1), ((j : ℝ) / 2)) := by
              symm
              exact Real.rpow_sum_of_pos (by positivity) _ _
        _ = Real.rpow (2 : ℝ) ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) := by
              rw [hsum]
              congr 1
              norm_num
    have hdetabs :
        |(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det b| = |B.det| := by
      -- Rewrite the determinant bridge through the definitional equation `b = euclideanBasisOfMatrix B hB`.
      simpa [b] using congrArg abs (basisFun_det_euclideanBasisOfMatrix_eq_det B hB)
    -- Multiply the per-column norm bounds and rewrite the determinant through Gram-Schmidt.
    calc
      B.columnNormProduct = ∏ j : Fin (n + 1), ‖WithLp.toLp 2 (B.col j)‖ := by
        exact Matrix.columnNormProduct_eq B
      _ ≤ ∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
            apply Finset.prod_le_prod
            · intro j hj
              exact norm_nonneg _
            · intro j hj
              exact hnorm j
      _ = (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) *
            ∏ j : Fin (n + 1), ‖gramSchmidtBasis b j‖ := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) *
            |(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det b| := by
            rw [← abs_basisFun_det_eq_prod_gramSchmidtBasis_norm]
      _ = (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) * |B.det| := by
            rw [hdetabs]
      _ = Real.rpow (2 : ℝ) ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) * |B.det| := by
            rw [hprodRpow]

end Theorem92

/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_6
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Algebra.Order.Round

open InnerProductSpace Module
open scoped BigOperators Matrix

noncomputable section

namespace FlatnessTransference

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: an inverse-transpose
standard column is the corresponding row of the nonsingular inverse. -/
theorem inverseTranspose_mulVec_single_apply
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    ((B.transpose)⁻¹ *ᵥ Pi.single i 1) j = B⁻¹ i j := by
  -- Normalize inverse-transpose multiplication to a single surviving coordinate.
  rw [← Matrix.transpose_nonsing_inv]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate dot square is
the squared Euclidean norm. -/
theorem dotProduct_self_eq_euclideanNorm_sq
    {n : ℕ}
    (x : Fin n → ℝ) :
    x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  -- Read the dot product as the real inner product and use its norm-square identity.
  calc
    x ⬝ᵥ x =
        inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 x) := by
          simp only [PiLp.inner_apply, Real.inner_apply, dotProduct]
    _ = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: rounding all ordinary basis
coordinates gives a lattice point within half the sum of the basis-vector norms. -/
theorem exists_intCombination_dist_le_half_sum_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (b : Basis (Fin n) ℝ E)
    (u : E) :
    ∃ z : Fin n → ℤ,
      ‖u - ∑ i, (z i : ℝ) • b i‖ ≤ (1 / 2 : ℝ) * ∑ i, ‖b i‖ := by
  let z : Fin n → ℤ := fun i ↦ round (b.repr u i)
  refine ⟨z, ?_⟩
  have hdecomp :
      u - ∑ i, (z i : ℝ) • b i =
        ∑ i, (b.repr u i - (z i : ℝ)) • b i := by
    calc
      u - ∑ i, (z i : ℝ) • b i =
          (∑ i, b.repr u i • b i) - ∑ i, (z i : ℝ) • b i := by
            rw [b.sum_repr u]
      _ = ∑ i, (b.repr u i - (z i : ℝ)) • b i := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [sub_smul]
  calc
    ‖u - ∑ i, (z i : ℝ) • b i‖ =
        ‖∑ i, (b.repr u i - (z i : ℝ)) • b i‖ := congrArg norm hdecomp
    _ ≤ ∑ i, ‖(b.repr u i - (z i : ℝ)) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr u i - (z i : ℝ)| * ‖b i‖ := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, (1 / 2 : ℝ) * ‖b i‖ := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_right (by simpa [z] using abs_sub_round (b.repr u i))
        (norm_nonneg _)
    _ = (1 / 2 : ℝ) * ∑ i, ‖b i‖ := by rw [Finset.mul_sum]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: if every integral basis
combination misses the open unit ball about a point, some basis vector has scaled norm above two. -/
theorem exists_long_basisVector_of_intCombination_avoidance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ}
    (b : Basis (Fin n) ℝ E)
    (u : E)
    (hn : n ≠ 0)
    (havoid : ∀ z : Fin n → ℤ, 1 < ‖(∑ i, (z i : ℝ) • b i) - u‖) :
    ∃ i : Fin n, 2 < (n : ℝ) * ‖b i‖ := by
  rcases exists_intCombination_dist_le_half_sum_norm b u with ⟨z, hz⟩
  have hdist :
      ‖(∑ i, (z i : ℝ) • b i) - u‖ =
        ‖u - ∑ i, (z i : ℝ) • b i‖ := by
    rw [← norm_neg]
    congr 1
    simp
  have htwo_lt_sum : 2 < ∑ i, ‖b i‖ := by
    have hfar := havoid z
    rw [hdist] at hfar
    nlinarith
  by_contra hlong
  push Not at hlong
  have hsum :
      ∑ i : Fin n, (n : ℝ) * ‖b i‖ ≤ ∑ _i : Fin n, (2 : ℝ) :=
    Finset.sum_le_sum fun i _ ↦ hlong i
  have hscaled :
      (n : ℝ) * ∑ i, ‖b i‖ ≤ (n : ℝ) * 2 := by
    simpa [Finset.mul_sum] using hsum
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsum_le : ∑ i, ‖b i‖ ≤ 2 := le_of_mul_le_mul_left hscaled hn_pos
  exact (not_lt_of_ge hsum_le) htwo_lt_sum

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: Hadamard's inequality in
the matrix-column norm presentation used by the Chapter 9 reduced-basis API. -/
theorem absDet_le_prod_columnNorm
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ j : Fin n, ‖WithLp.toLp 2 (A.col j)‖ := by
  -- Local instance justification: `Orientation.volumeForm` requires the dimension equality as a
  -- `Fact`; it is canonical here but is not synthesized from the Euclidean-space instance.
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun j ↦ WithLp.toLp 2 (A.col j)
  have hdet :
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v = A.det := by
    -- The coordinate matrix of the column family is exactly `A`.
    rw [Module.Basis.det_apply]
    congr 1
  calc
    |A.det| = |o.volumeForm v| := by
      rw [← hdet]
      exact (o.volumeForm_robust' (EuclideanSpace.basisFun (Fin n) ℝ) v).symm
    _ ≤ ∏ i : Fin n, ‖v i‖ := o.abs_volumeForm_apply_le v
    _ = ∏ j : Fin n, ‖WithLp.toLp 2 (A.col j)‖ := by
      rfl

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a dual column of an
inverse transpose is bounded by the product of all complementary primal column norms. -/
theorem inverseTransposeColumn_norm_mul_absDet_le_productErase
    {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B.det)
    (i : Fin n) :
    ‖(WithLp.toLp 2 ((B.transpose)⁻¹ *ᵥ Pi.single i 1) :
        EuclideanSpace ℝ (Fin n))‖ * |B.det| ≤
      ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ := by
  classical
  let q : Fin n → ℝ := (B.transpose)⁻¹ *ᵥ Pi.single i 1
  have htranspose : IsUnit B.transpose.det := Matrix.isUnit_det_transpose B hB
  have hrecover : B.transpose *ᵥ q = Pi.single i 1 := by
    -- Multiplying the inverse-transpose column by `Bᵀ` recovers the standard basis vector.
    calc
      B.transpose *ᵥ q =
          (B.transpose * (B.transpose)⁻¹) *ᵥ Pi.single i 1 := by
            rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ Pi.single i 1 := by
            rw [Matrix.mul_nonsing_inv _ htranspose]
      _ = Pi.single i 1 := Matrix.one_mulVec _
  have hq_ne : q ≠ 0 := by
    intro hq
    have hi := congrFun hrecover i
    simp [hq] at hi
  have hq_pos : 0 < ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ := by
    exact norm_pos_iff.mpr (by simpa using hq_ne)
  have hq_coord (j : Fin n) : q j = B⁻¹ i j := by
    exact inverseTranspose_mulVec_single_apply B i j
  have hq_dot : (B⁻¹ *ᵥ q) i = q ⬝ᵥ q := by
    -- The `i`th row of `B⁻¹` is exactly the coordinate vector `q`.
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hq_coord j]
  have hdet_update : (B.updateCol i q).det = B.det * (q ⬝ᵥ q) := by
    -- Cramer's rule computes the determinant after replacing column `i` by `q`.
    have hcramer := congrFun (B.det_smul_inv_mulVec_eq_cramer q hB) i
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, hq_dot] using hcramer.symm
  have habs_det_update :
      |(B.updateCol i q).det| =
        |B.det| * ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    calc
      |(B.updateCol i q).det| = |B.det * (q ⬝ᵥ q)| := by rw [hdet_update]
      _ = |B.det| * |‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ ^ 2| := by
        rw [abs_mul, dotProduct_self_eq_euclideanNorm_sq]
      _ = |B.det| * ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
        congrArg (fun t : ℝ ↦ |B.det| * t) (abs_of_nonneg (sq_nonneg _))
  have hprod_update :
      (∏ j : Fin n, ‖WithLp.toLp 2 ((B.updateCol i q).col j)‖) =
        ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ *
          ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ := by
    -- Split off the replaced column; every complementary column is unchanged.
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j ↦ ‖WithLp.toLp 2 ((B.updateCol i q).col j)‖) (Finset.mem_univ i)]
    congr 1
    · congr 1
      ext k
      simp [Matrix.col_apply]
    · refine Finset.prod_congr rfl ?_
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      congr 1
      ext k
      simp [Matrix.col_apply, hji]
  have hhadamard := absDet_le_prod_columnNorm (B.updateCol i q)
  rw [habs_det_update, hprod_update] at hhadamard
  -- Cancel the positive norm of the dual column from Hadamard's inequality.
  refine le_of_mul_le_mul_left ?_ hq_pos
  calc
    ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ *
          (‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ * |B.det|) =
        |B.det| * ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by ring
    _ ≤ ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ *
          ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ := hhadamard

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the diagonal
Gram–Schmidt pairing is the squared norm of the current orthogonal vector. -/
lemma gramSchmidtBasis_inner_self_eq_norm_sq
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) :
    ⟪InnerProductSpace.gramSchmidt ℝ b i, b i⟫_ℝ =
      ‖InnerProductSpace.gramSchmidt ℝ b i‖ ^ 2 := by
  -- Expand the basis vector and discard all earlier orthogonal correction terms.
  rw [InnerProductSpace.gramSchmidt_def'' ℝ b i]
  have hsum :
      ∑ x ∈ Finset.Iio i,
        ⟪InnerProductSpace.gramSchmidt ℝ b x, b i⟫_ℝ /
            ↑‖InnerProductSpace.gramSchmidt ℝ b x‖ ^ 2 *
          ⟪InnerProductSpace.gramSchmidt ℝ b i,
            InnerProductSpace.gramSchmidt ℝ b x⟫_ℝ = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hix : i ≠ x := ne_of_gt (Finset.mem_Iio.mp hx)
    simp [InnerProductSpace.gramSchmidt_orthogonal ℝ b hix]
  simp [inner_add_right, inner_sum, inner_smul_right, hsum]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the diagonal coordinate in
the Gram–Schmidt orthonormal basis is the norm of the corresponding orthogonal vector. -/
lemma gramSchmidtOrthonormalBasis_inner_eq_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) :
    let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
      InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) b
    ⟪ob i, b i⟫_ℝ = ‖gramSchmidtBasis b i‖ := by
  dsimp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  have hnonzero : InnerProductSpace.gramSchmidt ℝ b i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero i b.linearIndependent
  have hnormed : InnerProductSpace.gramSchmidtNormed ℝ b i ≠ 0 := by
    simp [InnerProductSpace.gramSchmidtNormed, hnonzero]
  have hnorm_ne : ‖InnerProductSpace.gramSchmidt ℝ b i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hnonzero
  -- Normalize the diagonal Gram–Schmidt vector and cancel its nonzero norm.
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply
    (h := hdim) (f := b) (i := i) hnormed]
  calc
    ⟪InnerProductSpace.gramSchmidtNormed ℝ b i, b i⟫_ℝ =
        ‖InnerProductSpace.gramSchmidt ℝ b i‖⁻¹ *
          ⟪InnerProductSpace.gramSchmidt ℝ b i, b i⟫_ℝ := by
            simp [InnerProductSpace.gramSchmidtNormed, inner_smul_left]
    _ = ‖InnerProductSpace.gramSchmidt ℝ b i‖⁻¹ *
          ‖InnerProductSpace.gramSchmidt ℝ b i‖ ^ 2 := by
            rw [gramSchmidtBasis_inner_self_eq_norm_sq]
    _ = ‖InnerProductSpace.gramSchmidt ℝ b i‖ := by
          rw [pow_two]
          field_simp [hnorm_ne]
    _ = ‖gramSchmidtBasis b i‖ := by simp [coe_gramSchmidtBasis]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: an earlier orthonormal
Gram–Schmidt coordinate is the reduction coefficient times the earlier orthogonal norm. -/
lemma gramSchmidtOrthonormalBasis_inner_eq_coefficient_mul_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (j k : Fin n) :
    let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
      InnerProductSpace.gramSchmidtOrthonormalBasis (by simp) b
    ⟪ob k, b j⟫_ℝ = gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖ := by
  dsimp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  have hnonzero : InnerProductSpace.gramSchmidt ℝ b k ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero k b.linearIndependent
  have hnormed : InnerProductSpace.gramSchmidtNormed ℝ b k ≠ 0 := by
    simp [InnerProductSpace.gramSchmidtNormed, hnonzero]
  -- Expand the normalized vector, then identify the coefficient and cancel its denominator.
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply
    (h := hdim) (f := b) (i := k) hnormed]
  calc
    ⟪InnerProductSpace.gramSchmidtNormed ℝ b k, b j⟫_ℝ =
        ‖InnerProductSpace.gramSchmidt ℝ b k‖⁻¹ *
          ⟪InnerProductSpace.gramSchmidt ℝ b k, b j⟫_ℝ := by
            simp [InnerProductSpace.gramSchmidtNormed, inner_smul_left]
    _ = ‖InnerProductSpace.gramSchmidt ℝ b k‖⁻¹ *
          ⟪b j, InnerProductSpace.gramSchmidt ℝ b k⟫_ℝ := by
            rw [real_inner_comm]
    _ = gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖ := by
          rw [gram_schmidt_coefficient, coe_gramSchmidtBasis, div_eq_mul_inv]
          field_simp [norm_ne_zero_iff.mpr hnonzero]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the determinant of a Euclidean
basis is the product of its Gram–Schmidt norms. -/
lemma abs_basisFun_det_eq_prod_gramSchmidtBasis_norm
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| =
      ∏ i : Fin n, ‖gramSchmidtBasis b i‖ := by
  -- Local instance justification: the orientation API records the evident Euclidean dimension
  -- equality as a `Fact`, but instance search does not synthesize it from the space itself.
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by
    simp
  let ob : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim b
  have hdet : ob.toBasis.det b = ∏ i, ⟪ob i, b i⟫_ℝ := by
    simpa [ob] using InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim b
  have hdiag : ∀ i : Fin n, ⟪ob i, b i⟫_ℝ = ‖gramSchmidtBasis b i‖ := by
    intro i
    simpa [ob] using gramSchmidtOrthonormalBasis_inner_eq_norm b i
  have hprod : ∏ i, ⟪ob i, b i⟫_ℝ = ∏ i, ‖gramSchmidtBasis b i‖ := by
    exact Finset.prod_congr rfl fun i _ ↦ hdiag i
  -- Evaluate one volume form in the standard and Gram–Schmidt orthonormal bases.
  calc
    |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| = |o.volumeForm b| := by
      symm
      simpa [o] using (o.volumeForm_robust' (EuclideanSpace.basisFun (Fin n) ℝ) b)
    _ = |ob.toBasis.det b| := by
      simpa [o] using (o.volumeForm_robust' ob b)
    _ = |∏ i, ⟪ob i, b i⟫_ℝ| := by rw [hdet]
    _ = ∏ i, ‖gramSchmidtBasis b i‖ := by
      rw [hprod, abs_of_nonneg]
      exact Finset.prod_nonneg fun i _ ↦ norm_nonneg _

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: adjacent Gram–Schmidt vectors
of a reduced basis satisfy the half-growth inequality. -/
lemma reducedBasis_adjacent_gramSchmidt_sq_ge_half
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : IsReducedBasis b)
    (j : Fin (n - 1)) :
    let jCurrent : Fin n := ⟨j.1, Nat.lt_of_lt_pred j.2⟩
    let jNext : Fin n := ⟨j.1 + 1, Nat.succ_lt_of_lt_pred j.2⟩
    ((1 : ℝ) / 2) * ‖gramSchmidtBasis b jCurrent‖ ^ 2 ≤
      ‖gramSchmidtBasis b jNext‖ ^ 2 := by
  dsimp
  let jCurrent : Fin n := ⟨j.1, Nat.lt_of_lt_pred j.2⟩
  let jNext : Fin n := ⟨j.1 + 1, Nat.succ_lt_of_lt_pred j.2⟩
  have hjlt : jCurrent < jNext := by simp [jCurrent, jNext]
  have hstep :
      ‖gramSchmidtBasis b jCurrent‖ ≤
        ‖gramSchmidtBasis b jNext +
          gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent‖ := by
    simpa [jCurrent, jNext] using hb.condition_ii j
  have hsq :
      ‖gramSchmidtBasis b jCurrent‖ ^ 2 ≤
        ‖gramSchmidtBasis b jNext +
          gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hstep
  have hmu : |gram_schmidt_coefficient b jNext jCurrent| ≤ (1 : ℝ) / 2 :=
    hb.condition_i hjlt
  have hmu_sq : gram_schmidt_coefficient b jNext jCurrent ^ 2 ≤ (1 : ℝ) / 4 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (gram_schmidt_coefficient b jNext jCurrent))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hmu
    rw [sq_abs] at hsquare
    norm_num at hsquare ⊢
    exact hsquare
  have horth :
      ⟪gramSchmidtBasis b jNext,
        gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent⟫_ℝ = 0 := by
    simp [inner_smul_right, coe_gramSchmidtBasis,
      InnerProductSpace.gramSchmidt_orthogonal ℝ b hjlt.ne']
  have hnorm_add :
      ‖gramSchmidtBasis b jNext +
          gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent‖ ^ 2 =
        ‖gramSchmidtBasis b jNext‖ ^ 2 +
          ‖gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent‖ ^ 2 := by
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hnorm_smul :
      ‖gram_schmidt_coefficient b jNext jCurrent • gramSchmidtBasis b jCurrent‖ ^ 2 =
        gram_schmidt_coefficient b jNext jCurrent ^ 2 *
          ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, pow_two]
    calc
      (|gram_schmidt_coefficient b jNext jCurrent| * ‖gramSchmidtBasis b jCurrent‖) *
            (|gram_schmidt_coefficient b jNext jCurrent| * ‖gramSchmidtBasis b jCurrent‖) =
          |gram_schmidt_coefficient b jNext jCurrent| ^ 2 *
            ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by ring
      _ = gram_schmidt_coefficient b jNext jCurrent ^ 2 *
            ‖gramSchmidtBasis b jCurrent‖ ^ 2 := by rw [sq_abs]
  nlinarith [hsq, hmu_sq, hnorm_add, hnorm_smul]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: an earlier Gram–Schmidt
prefix is bounded by a geometric multiple of the current squared norm. -/
lemma reducedBasisPrefixGramSchmidtSqSum_le
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ∑ i ∈ Finset.Iio j, ‖gramSchmidtBasis b i‖ ^ 2 ≤
      ((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j‖ ^ 2 := by
  induction j using Fin.induction with
  | zero =>
      rw [show Finset.Iio (0 : Fin (m + 1)) = ∅ by ext i; simp, Finset.sum_empty]
      norm_num
  | succ j ih =>
      have ih' :
          ∑ i ∈ Finset.Iio j.castSucc, ‖gramSchmidtBasis b i‖ ^ 2 ≤
            ((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
        simpa using ih
      have hstepHalf :
          ((1 : ℝ) / 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 ≤
            ‖gramSchmidtBasis b j.succ‖ ^ 2 := by
        simpa using reducedBasis_adjacent_gramSchmidt_sq_ge_half b hb j
      have hstep : ‖gramSchmidtBasis b j.castSucc‖ ^ 2 ≤
          2 * ‖gramSchmidtBasis b j.succ‖ ^ 2 := by
        nlinarith
      have hfactor_nonneg : 0 ≤ (2 : ℝ) ^ (j.1 + 1) - 1 := by
        have hpow : (1 : ℝ) ≤ 2 ^ (j.1 + 1) := one_le_pow₀ (by norm_num)
        linarith
      have hIioSucc : Finset.Iio j.succ = Finset.Iic j.castSucc := by
        ext i
        simp [Fin.lt_def, Fin.le_iff_val_le_val]
      -- Add the new predecessor and use adjacent half-growth once.
      calc
        ∑ i ∈ Finset.Iio j.succ, ‖gramSchmidtBasis b i‖ ^ 2 =
            ∑ i ∈ Finset.Iio j.castSucc, ‖gramSchmidtBasis b i‖ ^ 2 +
              ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
                rw [hIioSucc, Finset.Iic_eq_cons_Iio, Finset.sum_cons]
                simp [add_comm]
        _ ≤ ((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 +
              ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by nlinarith [ih']
        _ = ((2 : ℝ) ^ (j.1 + 1) - 1) * ‖gramSchmidtBasis b j.castSucc‖ ^ 2 := by
              ring
        _ ≤ ((2 : ℝ) ^ (j.1 + 1) - 1) *
              (2 * ‖gramSchmidtBasis b j.succ‖ ^ 2) := by
                nlinarith [hstep, hfactor_nonneg]
        _ = ((2 : ℝ) ^ (j.succ.1 + 1) - 2) * ‖gramSchmidtBasis b j.succ‖ ^ 2 := by
              rw [Fin.val_succ, pow_succ]
              ring

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: every reduced-basis vector is
controlled by its current Gram–Schmidt vector with the standard power-of-two factor. -/
lemma reducedBasisColumnSq_le_pow_mul_gramSchmidtSq
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ‖b j‖ ^ 2 ≤ (2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) =
      Fintype.card (Fin (m + 1)) := by simp
  let ob : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))) :=
    InnerProductSpace.gramSchmidtOrthonormalBasis hdim b
  let term : Fin (m + 1) → ℝ := fun k ↦ ⟪ob k, b j⟫_ℝ ^ 2
  have hparseval : ‖b j‖ ^ 2 = ∑ k : Fin (m + 1), term k := by
    symm
    simpa [ob, term] using OrthonormalBasis.sum_sq_inner_right ob (b j)
  have htail : ∀ k ∈ Finset.univ \ Finset.Iic j, term k = 0 := by
    intro k hk
    have hknot : k ∉ Finset.Iic j := (Finset.mem_sdiff.mp hk).2
    have hjk : j < k := by simpa only [Finset.mem_Iic, not_le] using hknot
    have hzero : ⟪ob k, b j⟫_ℝ = 0 := by
      simpa [ob] using
        (InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular
          (h := hdim) (f := b) hjk)
    simp [term, hzero]
  have hdiag : term j = ‖gramSchmidtBasis b j‖ ^ 2 := by
    rw [show term j = ⟪ob j, b j⟫_ℝ ^ 2 by rfl]
    rw [gramSchmidtOrthonormalBasis_inner_eq_norm]
  have hoffdiag : ∀ k ∈ Finset.Iio j,
      term k ≤ ((1 : ℝ) / 4) * ‖gramSchmidtBasis b k‖ ^ 2 := by
    intro k hk
    have hmu : |gram_schmidt_coefficient b j k| ≤ (1 : ℝ) / 2 :=
      hb.condition_i (Finset.mem_Iio.mp hk)
    have hcoeff :
        term k = (gram_schmidt_coefficient b j k * ‖gramSchmidtBasis b k‖) ^ 2 := by
      rw [show term k = ⟪ob k, b j⟫_ℝ ^ 2 by rfl]
      rw [gramSchmidtOrthonormalBasis_inner_eq_coefficient_mul_norm]
    have hmu_sq : gram_schmidt_coefficient b j k ^ 2 ≤ (1 : ℝ) / 4 := by
      have habs_sq : |gram_schmidt_coefficient b j k| ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
        nlinarith [abs_nonneg (gram_schmidt_coefficient b j k), hmu]
      rw [sq_abs] at habs_sq
      norm_num at habs_sq ⊢
      exact habs_sq
    rw [hcoeff]
    nlinarith [hmu_sq, norm_nonneg (gramSchmidtBasis b k)]
  have hprefix :
      ∑ k ∈ Finset.Iio j, term k ≤
        ((1 : ℝ) / 4) *
          (((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) := by
    calc
      ∑ k ∈ Finset.Iio j, term k ≤
          ∑ k ∈ Finset.Iio j, ((1 : ℝ) / 4) * ‖gramSchmidtBasis b k‖ ^ 2 := by
            exact Finset.sum_le_sum fun k hk ↦ hoffdiag k hk
      _ = ((1 : ℝ) / 4) * ∑ k ∈ Finset.Iio j, ‖gramSchmidtBasis b k‖ ^ 2 := by
            rw [← Finset.mul_sum]
      _ ≤ ((1 : ℝ) / 4) *
          (((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) := by
            nlinarith [reducedBasisPrefixGramSchmidtSqSum_le b hb j]
  have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ j.1 := one_le_pow₀ (by norm_num)
  -- Keep the lower-triangular coordinates and apply the prefix estimate.
  calc
    ‖b j‖ ^ 2 = ∑ k ∈ Finset.Iic j, term k := by
      rw [hparseval]
      calc
        ∑ k : Fin (m + 1), term k =
            ∑ k : Fin (m + 1), if k ≤ j then term k else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hkj : k ≤ j
              · simp [hkj]
              · have hkout : k ∈ Finset.univ \ Finset.Iic j := by simp [hkj]
                simp [hkj, htail k hkout]
        _ = ∑ k ∈ Finset.Iic j, term k := by
              rw [← Finset.sum_filter]
              congr 1
              ext k
              simp [Finset.mem_Iic]
    _ = ∑ k ∈ Finset.Iio j, term k + ‖gramSchmidtBasis b j‖ ^ 2 := by
          rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
          simp [hdiag, add_comm]
    _ ≤ ((1 : ℝ) / 4) *
          (((2 : ℝ) ^ (j.1 + 1) - 2) * ‖gramSchmidtBasis b j‖ ^ 2) +
        ‖gramSchmidtBasis b j‖ ^ 2 := by nlinarith [hprefix]
    _ = (((2 : ℝ) ^ j.1 + 1) / 2) * ‖gramSchmidtBasis b j‖ ^ 2 := by
          rw [pow_succ]
          ring
    _ ≤ (2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2 := by
          nlinarith [sq_nonneg ‖gramSchmidtBasis b j‖]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: unsquaring the reduced-column
estimate gives its `Real.rpow` form. -/
lemma reducedBasisNormLeRpowTwoMulGramSchmidtBasisNorm
    {m : ℕ}
    (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (hb : IsReducedBasis b)
    (j : Fin (m + 1)) :
    ‖b j‖ ≤ Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
  have hsq := reducedBasisColumnSq_le_pow_mul_gramSchmidtSq b hb j
  have hsqrt :
      Real.sqrt (‖b j‖ ^ 2) ≤
        Real.sqrt ((2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2) :=
    Real.sqrt_le_sqrt hsq
  calc
    ‖b j‖ = Real.sqrt (‖b j‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt ((2 : ℝ) ^ j.1 * ‖gramSchmidtBasis b j‖ ^ 2) := hsqrt
    _ = Real.sqrt ((2 : ℝ) ^ j.1) * ‖gramSchmidtBasis b j‖ := by
          rw [Real.sqrt_mul (pow_nonneg (by positivity) _), Real.sqrt_sq_eq_abs,
            abs_of_nonneg (norm_nonneg _)]
    _ = Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
          congr 1
          norm_num [div_eq_mul_inv]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the product of the norms of a
reduced Euclidean basis is bounded by its covolume times the standard reduction factor. -/
theorem reducedBasisNormProduct_le_absDet
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : IsReducedBasis b) :
    (∏ j : Fin n, ‖b j‖) ≤
      Real.rpow (2 : ℝ) (((n : ℝ) * (n - 1)) / 4) *
        |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| := by
  cases n with
  | zero => simp
  | succ n =>
      have hnorm : ∀ j : Fin (n + 1),
          ‖b j‖ ≤ Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ :=
        reducedBasisNormLeRpowTwoMulGramSchmidtBasisNorm b hb
      have hprodRpow :
          (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) =
            Real.rpow (2 : ℝ)
              ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) := by
        have hsum : ∑ j : Fin (n + 1), ((j : ℝ) / 2) = (↑n + 1) * ↑n / 4 := by
          have hsumRange : ∀ m : ℕ,
              ∑ i ∈ Finset.range (m + 1), (i : ℝ) / 2 = (↑m + 1) * ↑m / 4 := by
            intro m
            induction m with
            | zero => norm_num
            | succ m ih =>
                rw [Finset.sum_range_succ, ih]
                norm_num [Nat.cast_add]
                ring
          calc
            ∑ j : Fin (n + 1), ((j : ℝ) / 2) =
                ∑ i ∈ Finset.range (n + 1), (i : ℝ) / 2 := by
                  rw [Fin.sum_univ_eq_sum_range fun j : ℕ ↦ (j : ℝ) / 2]
            _ = (↑n + 1) * ↑n / 4 := hsumRange n
        calc
          (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) =
              Real.rpow (2 : ℝ) (∑ j : Fin (n + 1), ((j : ℝ) / 2)) := by
                symm
                exact Real.rpow_sum_of_pos (by positivity) _ _
          _ = Real.rpow (2 : ℝ)
                ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) := by
                  rw [hsum]
                  congr 1
                  norm_num
      -- Multiply the pointwise column estimates and substitute the determinant product identity.
      calc
        ∏ j : Fin (n + 1), ‖b j‖ ≤
            ∏ j : Fin (n + 1),
              Real.rpow (2 : ℝ) ((j : ℝ) / 2) * ‖gramSchmidtBasis b j‖ := by
                apply Finset.prod_le_prod
                · intro j _
                  exact norm_nonneg _
                · intro j _
                  exact hnorm j
        _ = (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) *
              ∏ j : Fin (n + 1), ‖gramSchmidtBasis b j‖ := by
                rw [Finset.prod_mul_distrib]
        _ = (∏ j : Fin (n + 1), Real.rpow (2 : ℝ) ((j : ℝ) / 2)) *
              |(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det b| := by
                rw [← abs_basisFun_det_eq_prod_gramSchmidtBasis_norm]
        _ = Real.rpow (2 : ℝ)
              ((((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) - 1)) / 4) *
              |(EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.det b| := by
                rw [hprodRpow]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate matrix of a
Euclidean basis relative to the standard Euclidean basis. -/
noncomputable def basisMatrix
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) : Matrix (Fin n) (Fin n) ℝ :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix b

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: a column of the coordinate
matrix is the underlying coordinate function of the corresponding basis vector. -/
lemma basisMatrix_col_toLp
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (j : Fin n) :
    WithLp.toLp 2 ((basisMatrix b).col j) = b j := by
  -- The standard Euclidean basis representation evaluates coordinatewise.
  ext i
  simp [basisMatrix, Basis.toMatrix_apply]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: the coordinate matrix of a
basis is nonsingular. -/
lemma basisMatrix_isUnit_det
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    IsUnit (basisMatrix b).det := by
  -- This is exactly the change-of-basis determinant, which is a unit for any two bases.
  simpa [basisMatrix, Module.Basis.det_apply] using
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.isUnit_det b

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: transporting the column
lattice of a basis coordinate matrix to Euclidean space yields the integral span of that basis. -/
lemma image_basisMatrix_lattice
    {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm '' matrix_generated_lattice (basisMatrix b) =
      Submodule.span ℤ (Set.range b) := by
  rw [image_span_cols_eq_euclidean_span_cols]
  have hcolumns :
      (EuclideanSpace.equiv (Fin n) ℝ).symm ∘ (basisMatrix b).col = b := by
    funext j
    simpa using basisMatrix_col_toLp b j
  rw [hcolumns]

/-- Helper for Theorem 9.7
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_2_theorem_9_7.lean`: avoidance of every translate
of a nonsingular rational lattice produces a short nonzero inverse-transpose integral vector. -/
theorem existsShortInverseTransposeIntegerVector
    {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℚ)
    (u : Fin n → ℝ)
    (hn : n ≠ 0)
    (hdet : IsUnit C.det)
    (havoid : ∀ z : Fin n → ℤ,
      1 < ‖(WithLp.toLp 2
        (C.map (Rat.castHom ℝ) *ᵥ (Int.cast ∘ z) - u) :
          EuclideanSpace ℝ (Fin n))‖) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧
        2 * ‖(WithLp.toLp 2
          (((C.map (Rat.castHom ℝ)).transpose)⁻¹ *ᵥ (Int.cast ∘ d)) :
            EuclideanSpace ℝ (Fin n))‖ ≤
          (n : ℝ) * Real.rpow 2 ((((n * (n - 1) : ℕ) : ℝ)) / 4) := by
  classical
  let A : Matrix (Fin n) (Fin n) ℝ := C.map (Rat.castHom ℝ)
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    have hdet_map : A.det = (Rat.castHom ℝ) C.det := by
      exact ((Rat.castHom ℝ).map_det C).symm
    rw [hdet_map]
    intro hzero
    apply hdet.ne_zero
    exact (Rat.castHom ℝ).injective (by simpa using hzero)
  let input : RationalBasis n := ⟨C, hdet⟩
  obtain ⟨b, hbspan, hbreduced⟩ := input.exists_reducedBasis_sameLattice
  let B : Matrix (Fin n) (Fin n) ℝ := basisMatrix b
  have hB : IsUnit B.det := by
    simpa [B] using basisMatrix_isUnit_det b
  have hspanB :
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' matrix_generated_lattice B =
        Submodule.span ℤ (Set.range b) := by
    simpa [B] using image_basisMatrix_lattice b
  have hspanRaw : matrix_generated_lattice A = matrix_generated_lattice B := by
    -- Both raw column lattices have the same injective image in Euclidean space.
    apply SetLike.ext'
    apply (EuclideanSpace.equiv (Fin n) ℝ).symm.injective.image_injective
    simpa [A, input] using hbspan.trans hspanB.symm
  obtain ⟨U, hU, hBU⟩ :=
    (span_cols_eq_iff_exists_unimodular_right_mul A B hA).mp hspanRaw
  let uE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 u
  have havoidBasis : ∀ z : Fin n → ℤ,
      1 < ‖(∑ i, (z i : ℝ) • b i) - uE‖ := by
    intro z
    have hsum_mem : (∑ i, (z i : ℝ) • b i) ∈ Submodule.span ℤ (Set.range b) := by
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨z, ?_⟩
      refine Finset.sum_congr rfl ?_
      intro i _
      exact (IsScalarTower.algebraMap_smul ℝ (z i) (b i)).symm
    have hsum_image :
        (∑ i, (z i : ℝ) • b i) ∈
          (EuclideanSpace.equiv (Fin n) ℝ).symm '' matrix_generated_lattice A := by
      rw [hbspan]
      exact hsum_mem
    rcases hsum_image with ⟨x, hx, hxsum⟩
    rcases mem_matrix_generated_lattice_iff.mp hx with ⟨z', hxz'⟩
    have hxz'' : x = A *ᵥ (Int.cast ∘ z') := by simpa using hxz'
    have hvector :
        (WithLp.toLp 2 (A *ᵥ (Int.cast ∘ z') - u) : EuclideanSpace ℝ (Fin n)) =
          (∑ i, (z i : ℝ) • b i) - uE := by
      rw [← hxz'']
      simpa [uE] using congrArg (fun y ↦ y - uE) hxsum
    rw [← hvector]
    simpa [A] using havoid z'
  obtain ⟨i, hiLong⟩ := exists_long_basisVector_of_intCombination_avoidance b uE hn havoidBasis
  let q : Fin n → ℝ := (B.transpose)⁻¹ *ᵥ Pi.single i 1
  have hqNorm_nonneg :
      0 ≤ ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ := norm_nonneg _
  have hdetAbs_pos : 0 < |B.det| := abs_pos.mpr hB.ne_zero
  have hcofactor :
      ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ * |B.det| ≤
        ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ := by
    simpa [q] using inverseTransposeColumn_norm_mul_absDet_le_productErase B hB i
  have hcolumnNorm (j : Fin n) : ‖WithLp.toLp 2 (B.col j)‖ = ‖b j‖ := by
    simpa [B] using congrArg norm (basisMatrix_col_toLp b j)
  let reductionFactor : ℝ := Real.rpow 2 (((n : ℝ) * (n - 1)) / 4)
  have hproduct :
      (∏ j : Fin n, ‖WithLp.toLp 2 (B.col j)‖) ≤ reductionFactor * |B.det| := by
    simpa [reductionFactor, hcolumnNorm, B, basisMatrix, Module.Basis.det_apply] using
      reducedBasisNormProduct_le_absDet b hbreduced
  have hproductSplit :
      (∏ j : Fin n, ‖WithLp.toLp 2 (B.col j)‖) =
        ‖b i‖ * ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j ↦ ‖WithLp.toLp 2 (B.col j)‖) (Finset.mem_univ i), hcolumnNorm]
  have hdualTimesColumn :
      ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ * ‖b i‖ ≤ reductionFactor := by
    apply le_of_mul_le_mul_right _ hdetAbs_pos
    calc
      (‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ * ‖b i‖) * |B.det| =
          ‖b i‖ *
            (‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ * |B.det|) := by ring
      _ ≤ ‖b i‖ * ∏ j ∈ Finset.univ.erase i, ‖WithLp.toLp 2 (B.col j)‖ :=
        mul_le_mul_of_nonneg_left hcofactor (norm_nonneg _)
      _ = ∏ j : Fin n, ‖WithLp.toLp 2 (B.col j)‖ := hproductSplit.symm
      _ ≤ reductionFactor * |B.det| := hproduct
  have hshort :
      2 * ‖(WithLp.toLp 2 q : EuclideanSpace ℝ (Fin n))‖ ≤
        (n : ℝ) * reductionFactor := by
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  let Utr : Matrix (Fin n) (Fin n) ℤ := U.transpose
  have hUtr : IsUnit Utr.det := by
    simpa [Utr] using Matrix.isUnit_det_transpose U hU
  let V : Matrix (Fin n) (Fin n) ℤ := Utr⁻¹
  let d : Fin n → ℤ := V *ᵥ Pi.single i 1
  have hd_ne : d ≠ 0 := by
    have hrecover : Utr *ᵥ d = Pi.single i 1 := by
      calc
        Utr *ᵥ d = (Utr * V) *ᵥ Pi.single i 1 := by
          change Utr *ᵥ (V *ᵥ Pi.single i 1) = _
          rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) ℤ) *ᵥ Pi.single i 1 := by
          change (Utr * Utr⁻¹) *ᵥ Pi.single i 1 = _
          rw [Matrix.mul_nonsing_inv _ hUtr]
        _ = Pi.single i 1 := Matrix.one_mulVec _
    intro hd
    have hi := congrFun hrecover i
    simp [hd] at hi
  have hBq : B.transpose *ᵥ q = Pi.single i 1 := by
    calc
      B.transpose *ᵥ q = (B.transpose * (B.transpose)⁻¹) *ᵥ Pi.single i 1 := by
        change B.transpose *ᵥ ((B.transpose)⁻¹ *ᵥ Pi.single i 1) = _
        rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ Pi.single i 1 := by
        rw [Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_transpose B hB)]
      _ = Pi.single i 1 := Matrix.one_mulVec _
  have htransposeBU : B.transpose = Utr.map (Int.castRingHom ℝ) * A.transpose := by
    calc
      B.transpose = (A * U.map (Int.castRingHom ℝ)).transpose :=
        congrArg Matrix.transpose hBU
      _ = (U.map (Int.castRingHom ℝ)).transpose * A.transpose := Matrix.transpose_mul _ _
      _ = Utr.map (Int.castRingHom ℝ) * A.transpose := by
        rw [← Matrix.transpose_map]
  have hUtrAq :
      Utr.map (Int.castRingHom ℝ) *ᵥ (A.transpose *ᵥ q) = Pi.single i 1 := by
    calc
      Utr.map (Int.castRingHom ℝ) *ᵥ (A.transpose *ᵥ q) =
          (Utr.map (Int.castRingHom ℝ) * A.transpose) *ᵥ q := by
            exact Matrix.mulVec_mulVec _ _ _
      _ = B.transpose *ᵥ q := by rw [← htransposeBU]
      _ = Pi.single i 1 := hBq
  have hVUtr :
      V.map (Int.castRingHom ℝ) * Utr.map (Int.castRingHom ℝ) = 1 := by
    rw [← Matrix.map_mul]
    simp [V, Matrix.nonsing_inv_mul _ hUtr]
  have hcast_d :
      Int.cast ∘ d = V.map (Int.castRingHom ℝ) *ᵥ Pi.single i 1 := by
    funext j
    simpa [d] using
      (RingHom.map_mulVec (Int.castRingHom ℝ) V (Pi.single i 1) j)
  have hAq : A.transpose *ᵥ q = Int.cast ∘ d := by
    calc
      A.transpose *ᵥ q =
          (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (A.transpose *ᵥ q) := by simp
      _ = (V.map (Int.castRingHom ℝ) * Utr.map (Int.castRingHom ℝ)) *ᵥ
          (A.transpose *ᵥ q) := by rw [hVUtr]
      _ = V.map (Int.castRingHom ℝ) *ᵥ
          (Utr.map (Int.castRingHom ℝ) *ᵥ (A.transpose *ᵥ q)) := by
            exact (Matrix.mulVec_mulVec _ _ _).symm
      _ = V.map (Int.castRingHom ℝ) *ᵥ Pi.single i 1 := by rw [hUtrAq]
      _ = Int.cast ∘ d := hcast_d.symm
  have hqTarget : (A.transpose)⁻¹ *ᵥ (Int.cast ∘ d) = q := by
    calc
      (A.transpose)⁻¹ *ᵥ (Int.cast ∘ d) =
          (A.transpose)⁻¹ *ᵥ (A.transpose *ᵥ q) := by rw [hAq]
      _ = ((A.transpose)⁻¹ * A.transpose) *ᵥ q := by
            rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ q := by
            rw [Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_transpose A hA)]
      _ = q := Matrix.one_mulVec _
  refine ⟨d, hd_ne, ?_⟩
  rw [show C.map (Rat.castHom ℝ) = A by rfl, hqTarget]
  have hexponent :
      (((n : ℝ) * (n - 1)) / 4) = (((n * (n - 1) : ℕ) : ℝ) / 4) := by
    rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one]
  simpa [reductionFactor, hexponent] using hshort


end FlatnessTransference

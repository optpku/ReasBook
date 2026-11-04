/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_1_theorem_9_6.Reduction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Integer
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection

noncomputable section Theorem96

open InnerProductSpace Module
open scoped BigOperators Matrix

-- Route correction: the unavailable Theorem 9.2 and Lemma 9.3 artifacts are replaced here by
-- dependency-closed column-evaluation and lower-triangular Gram-Schmidt interfaces.
namespace EuclideanBasisOfMatrix

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: evaluation of a Euclidean
basis constructed from a nonsingular matrix recovers the corresponding column. -/
lemma apply_eq_col {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (j : Fin n) :
    euclideanBasisOfMatrix A hA j = WithLp.toLp 2 (A.col j) := by
  -- Compare coordinates and collapse the matrix-vector product against the standard basis vector.
  ext i
  have hcoord :=
    congrFun
      (Matrix.toLin_self
        (v₁ := Pi.basisFun ℝ (Fin n))
        (v₂ := Pi.basisFun ℝ (Fin n))
        A
        j)
      i
  have hsum :
      ∑ x, A x j * ((Pi.basisFun ℝ (Fin n)) x i) = A i j := by
    rw [Finset.sum_eq_single i]
    · simp [Pi.basisFun_apply]
    · intro x _ hxi
      simp [Pi.basisFun_apply, hxi]
    · intro hi
      simp at hi
  calc
    (euclideanBasisOfMatrix A hA j) i =
        ∑ x, A x j * ((Pi.basisFun ℝ (Fin n)) x i) := by
      simpa [euclideanBasisOfMatrix, basisOfMatrix, Pi.basisFun_apply] using hcoord
    _ = A i j := hsum

end EuclideanBasisOfMatrix

namespace GramSchmidtUpdate

universe u

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a lower-triangular update
keeps each updated earlier vector in the corresponding original prefix span. -/
lemma updatedVector_mem_prefixSpan
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ Submodule.span ℝ (B '' Set.Iio j))
    {i j : Fin n} (hij : i < j) :
    B' i ∈ Submodule.span ℝ (B '' Set.Iio j) := by
  -- Enlarge the update error's prefix and add back the original generator.
  have hdiff : B' i - B i ∈ Submodule.span ℝ (B '' Set.Iio j) := by
    exact (Submodule.span_mono (Set.image_mono <| Set.Iio_subset_Iio hij.le)) (hstep i)
  have hbase : B i ∈ Submodule.span ℝ (B '' Set.Iio j) :=
    Submodule.subset_span ⟨i, hij, rfl⟩
  simpa [add_comm] using
    Submodule.add_mem (Submodule.span ℝ (B '' Set.Iio j)) hdiff hbase

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every original earlier
vector belongs to the corresponding prefix span after a lower-triangular update. -/
lemma originalVector_mem_updatedPrefixSpan
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ Submodule.span ℝ (B '' Set.Iio j))
    {i j : Fin n} (hij : i < j) :
    B i ∈ Submodule.span ℝ (B' '' Set.Iio j) := by
  -- Well-founded induction expresses each correction using already transported generators.
  let P : Fin n → Prop := fun i =>
    ∀ j : Fin n, i < j → B i ∈ Submodule.span ℝ (B' '' Set.Iio j)
  have haux : ∀ i : Fin n, P i := by
    intro i
    refine wellFounded_lt.induction i ?_
    intro i ih j hij
    have hbase : B' i ∈ Submodule.span ℝ (B' '' Set.Iio j) :=
      Submodule.subset_span ⟨i, hij, rfl⟩
    have hcorr : B' i - B i ∈ Submodule.span ℝ (B' '' Set.Iio j) := by
      refine (Submodule.span_le.2 ?_) (hstep i)
      intro x hx
      rcases hx with ⟨k, hk, rfl⟩
      exact ih k hk j (hk.trans hij)
    simpa using Submodule.sub_mem (Submodule.span ℝ (B' '' Set.Iio j)) hbase hcorr
  exact haux i j hij

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: lower-triangular basis
updates preserve every earlier prefix span. -/
lemma prefixSpan_eq_ofLowerTriangularUpdate
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ Submodule.span ℝ (B '' Set.Iio j))
    (j : Fin n) :
    Submodule.span ℝ (B '' Set.Iio j) = Submodule.span ℝ (B' '' Set.Iio j) := by
  -- Compare the spans by transporting each generating family in the two directions.
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, hij, rfl⟩
    exact originalVector_mem_updatedPrefixSpan B B' hstep hij
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, hij, rfl⟩
    exact updatedVector_mem_prefixSpan B B' hstep hij

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the correction between an
input basis vector and its Gram-Schmidt vector lies in the earlier prefix span. -/
lemma sub_gramSchmidt_mem_prefixSpan
    (C : Basis (Fin n) ℝ E) (j : Fin n) :
    C j - gramSchmidt ℝ C j ∈ Submodule.span ℝ (C '' Set.Iio j) := by
  -- Each projection term lies in the span of an earlier Gram-Schmidt vector.
  have hsum :
      ∑ i ∈ Set.Iio j, (ℝ ∙ gramSchmidt ℝ C i).starProjection (C j) ∈
        Submodule.span ℝ (gramSchmidt ℝ C '' Set.Iio j) := by
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hgen :
        gramSchmidt ℝ C i ∈ Submodule.span ℝ (gramSchmidt ℝ C '' Set.Iio j) := by
      exact Submodule.subset_span ⟨i, by simpa using hi, rfl⟩
    have hle :
        ℝ ∙ gramSchmidt ℝ C i ≤ Submodule.span ℝ (gramSchmidt ℝ C '' Set.Iio j) := by
      exact (Submodule.span_singleton_le_iff_mem _ _).2 hgen
    exact hle <| Submodule.starProjection_apply_mem (ℝ ∙ gramSchmidt ℝ C i) (C j)
  have hdecomp :
      C j - gramSchmidt ℝ C j =
        ∑ i ∈ Set.Iio j, (ℝ ∙ gramSchmidt ℝ C i).starProjection (C j) := by
    -- Rearrange the standard Gram-Schmidt decomposition into a correction identity.
    rw [sub_eq_iff_eq_add']
    simpa [add_comm, add_left_comm, add_assoc] using gramSchmidt_def' ℝ C j
  have hmem :
      C j - gramSchmidt ℝ C j ∈
        Submodule.span ℝ (gramSchmidt ℝ C '' Set.Iio j) := by
    rw [hdecomp]
    exact hsum
  rwa [span_gramSchmidt_Iio ℝ C j] at hmem

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a Gram-Schmidt vector is
orthogonal to the span of all earlier input basis vectors. -/
lemma gramSchmidt_mem_prefixOrthogonal
    (C : Basis (Fin n) ℝ E) (j : Fin n) :
    gramSchmidt ℝ C j ∈ (Submodule.span ℝ (C '' Set.Iio j))ᗮ := by
  -- Replace the input prefix by its Gram-Schmidt span and verify orthogonality on generators.
  rw [Submodule.mem_orthogonal']
  intro v hv
  rw [← span_gramSchmidt_Iio ℝ C j] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩
      rw [inner_eq_zero_symm]
      exact gramSchmidt_orthogonal ℝ C hi.ne
  | zero =>
      simp
  | add x y hx hy hx0 hy0 =>
      simp [inner_add_right, hx0, hy0]
  | smul a x hx hx0 =>
      simp [inner_smul_right, hx0]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a lower-triangular basis
update preserves the complete Gram-Schmidt basis. -/
theorem gramSchmidtBasis_eq_ofLowerTriangularUpdate
    (B B' : Basis (Fin n) ℝ E)
    (hstep : ∀ j, B' j - B j ∈ Submodule.span ℝ (B '' Set.Iio j)) :
    gramSchmidtBasis B = gramSchmidtBasis B' := by
  -- Pointwise, the difference lies both in the common prefix span and its orthogonal complement.
  ext j
  let K : Submodule ℝ E := Submodule.span ℝ (B '' Set.Iio j)
  have hprefix :
      Submodule.span ℝ (B '' Set.Iio j) = Submodule.span ℝ (B' '' Set.Iio j) :=
    prefixSpan_eq_ofLowerTriangularUpdate B B' hstep j
  have hstepj : B' j - B j ∈ K := by
    simpa [K] using hstep j
  have hcorrB : B j - gramSchmidt ℝ B j ∈ K := by
    simpa [K] using sub_gramSchmidt_mem_prefixSpan B j
  have hcorrB' : B' j - gramSchmidt ℝ B' j ∈ K := by
    dsimp [K]
    rw [hprefix]
    exact sub_gramSchmidt_mem_prefixSpan B' j
  have horthB : gramSchmidt ℝ B j ∈ Kᗮ := by
    simpa [K] using gramSchmidt_mem_prefixOrthogonal B j
  have horthB' : gramSchmidt ℝ B' j ∈ Kᗮ := by
    dsimp [K]
    rw [hprefix]
    exact gramSchmidt_mem_prefixOrthogonal B' j
  have hspan : gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ K := by
    have hrewrite :
        gramSchmidt ℝ B' j - gramSchmidt ℝ B j =
          (B' j - B j) - (B' j - gramSchmidt ℝ B' j) +
            (B j - gramSchmidt ℝ B j) := by
      abel_nf
    rw [hrewrite]
    exact Submodule.add_mem K (Submodule.sub_mem K hstepj hcorrB') hcorrB
  have horth : gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ Kᗮ := by
    exact Submodule.sub_mem Kᗮ horthB' horthB
  have hzero : gramSchmidt ℝ B' j - gramSchmidt ℝ B j = 0 := by
    have hmem : gramSchmidt ℝ B' j - gramSchmidt ℝ B j ∈ K ⊓ Kᗮ := ⟨hspan, horth⟩
    simpa [K.inf_orthogonal_eq_bot] using hmem
  simpa [coe_gramSchmidtBasis] using (sub_eq_zero.mp hzero).symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the diagonal inner product
between a Gram-Schmidt vector and its input vector is its squared norm. -/
lemma inner_self_eq_norm_sq (B : Basis (Fin n) ℝ E) (i : Fin n) :
    ⟪gramSchmidt ℝ B i, B i⟫_ℝ = ‖gramSchmidt ℝ B i‖ ^ 2 := by
  -- Expand the input vector; all earlier correction terms vanish by orthogonality.
  rw [gramSchmidt_def'' ℝ B i]
  have hsum :
      ∑ x ∈ Finset.Iio i,
        ⟪gramSchmidt ℝ B x, B i⟫_ℝ / ↑‖gramSchmidt ℝ B x‖ ^ 2 *
          ⟪gramSchmidt ℝ B i, gramSchmidt ℝ B x⟫_ℝ = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hix : i ≠ x := ne_of_gt (Finset.mem_Iio.mp hx)
    simp [gramSchmidt_orthogonal ℝ B hix]
  simp [inner_add_right, inner_sum, inner_smul_right, hsum]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: subtracting a scalar multiple
of the `k`th input vector shifts the `k`th Gram-Schmidt coefficient by that scalar whenever the
Gram-Schmidt basis itself is unchanged. -/
lemma coefficient_sub_smul_self
    (B B' : Basis (Fin n) ℝ E) (j k : Fin n) (q : ℝ)
    (hgs : gramSchmidtBasis B = gramSchmidtBasis B')
    (hvec : B' j = B j - q • B k) :
    gram_schmidt_coefficient B' j k = gram_schmidt_coefficient B j k - q := by
  -- Rewrite to the original Gram-Schmidt vector, then divide the diagonal identity by its norm.
  have hgsk : gramSchmidtBasis B k = gramSchmidtBasis B' k :=
    congrArg (fun C : Basis (Fin n) ℝ E ↦ C k) hgs
  have hinner :
      ⟪B k, gramSchmidtBasis B k⟫_ℝ = ‖gramSchmidtBasis B k‖ ^ 2 := by
    rw [real_inner_comm, coe_gramSchmidtBasis]
    exact inner_self_eq_norm_sq B k
  have hnorm : ‖gramSchmidtBasis B k‖ ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact norm_ne_zero_iff.mpr ((gramSchmidtBasis B).ne_zero k)
  rw [gram_schmidt_coefficient, gram_schmidt_coefficient, hvec, ← hgsk,
    inner_sub_left, inner_smul_left, hinner]
  simp only [starRingEnd_apply, star_trivial]
  rw [sub_div, mul_div_cancel_right₀ q hnorm]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: subtracting a multiple of an
input vector earlier than `l` does not change the `l`th Gram-Schmidt coefficient when the
Gram-Schmidt basis is unchanged. -/
lemma coefficient_sub_smul_of_lt
    (B B' : Basis (Fin n) ℝ E) (j k l : Fin n) (q : ℝ)
    (hkl : k < l)
    (hgs : gramSchmidtBasis B = gramSchmidtBasis B')
    (hvec : B' j = B j - q • B k) :
    gram_schmidt_coefficient B' j l = gram_schmidt_coefficient B j l := by
  -- The later Gram-Schmidt vector is orthogonal to the earlier input vector being subtracted.
  have hgsl : gramSchmidtBasis B l = gramSchmidtBasis B' l :=
    congrArg (fun C : Basis (Fin n) ℝ E ↦ C l) hgs
  have hbase : B k ∈ Submodule.span ℝ (B '' Set.Iio l) :=
    Submodule.subset_span ⟨k, hkl, rfl⟩
  have horth := gramSchmidt_mem_prefixOrthogonal B l
  rw [Submodule.mem_orthogonal'] at horth
  have hzero : ⟪B k, gramSchmidtBasis B l⟫_ℝ = 0 := by
    rw [real_inner_comm, coe_gramSchmidtBasis]
    exact horth (B k) hbase
  rw [gram_schmidt_coefficient, gram_schmidt_coefficient, hvec, ← hgsl,
    inner_sub_left, inner_smul_left, hzero]
  simp

end GramSchmidtUpdate

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram matrix of Euclidean
matrix columns is the transpose-times-matrix product. -/
lemma EuclideanBasisOfMatrix.gram_columns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.gram ℝ (fun j ↦ WithLp.toLp 2 (A.col j)) = Aᵀ * A := by
  -- Expand the Euclidean inner product and matrix multiplication entrywise.
  ext i j
  simp only [Matrix.gram_apply, EuclideanSpace.inner_toLp_toLp, Matrix.mul_apply,
    dotProduct, Matrix.col_apply, Matrix.transpose_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the rational Gram matrix of
the original coordinate columns. -/
def RationalBasis.rationalGramMatrix {n : ℕ} (B : RationalBasis n) :
    Matrix (Fin n) (Fin n) ℚ :=
  B.basisMatrixᵀ * B.basisMatrix

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the rational Gram matrix
after an integral change of columns. -/
def RationalBasis.changedRationalGram {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  (U.map (Int.castRingHom ℚ))ᵀ * B.rationalGramMatrix * U.map (Int.castRingHom ℚ)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the fixed-denominator
integral Gram matrix transported by an integral column change. -/
def RationalBasis.integralGramMatrix {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Uᵀ * B.rationalGramMatrix.num * U

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the determinant of a leading
principal block of the fixed-denominator integral Gram matrix. -/
def RationalBasis.prefixGramDet {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  ((B.integralGramMatrix U).submatrix
    ((↑) : Set.Iic j → Fin n) ((↑) : Set.Iic j → Fin n)).det

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the natural-valued sum of
the absolute leading integral Gram determinants. -/
def RationalBasis.prefixGramPotential {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  ∑ j, (B.prefixGramDet U j).natAbs

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: casting the numerator of a
rational matrix recovers its fixed denominator times the original matrix. -/
lemma Matrix.num_map_ratCast_eq_den_smul {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) :
    A.num.map (Int.castRingHom ℚ) = (A.den : ℚ) • A := by
  -- Clear the nonzero common denominator entrywise using `Matrix.num_div_den`.
  ext i j
  have hden : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  have hentry := (div_eq_iff hden).mp (A.num_div_den i j)
  simpa [Matrix.map_apply, smul_apply, mul_comm] using hentry

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the transported integral
Gram matrix casts to the fixed denominator times the transported rational Gram matrix. -/
lemma RationalBasis.integralGramMatrix_map_ratCast {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) :
    (B.integralGramMatrix U).map (Int.castRingHom ℚ) =
      (B.rationalGramMatrix.den : ℚ) • B.changedRationalGram U := by
  -- Move the cast through both products and use the numerator/denominator identity once.
  rw [RationalBasis.integralGramMatrix, RationalBasis.changedRationalGram,
    Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.num_map_ratCast_eq_den_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the vectors of a rational
basis are the Euclidean images of its matrix columns. -/
lemma RationalBasis.inputBasis_apply_eq_col {n : ℕ} (B : RationalBasis n) (j : Fin n) :
    B.basis j = WithLp.toLp 2 ((B.basisMatrix.map (Rat.castHom ℝ)).col j) := by
  -- Unfold only the basis wrapper and use the established matrix-column computation rule.
  unfold RationalBasis.basis
  exact EuclideanBasisOfMatrix.apply_eq_col
    (B.basisMatrix.map (Rat.castHom ℝ)) _ j

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the basis attached to a
rational matrix spans its matrix-generated lattice. -/
lemma RationalBasis.inputBasis_span {n : ℕ} (B : RationalBasis n) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm ''
        matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
      Submodule.span ℤ (Set.range B.basis) := by
  -- Transport the coordinate-column span to Euclidean space.
  rw [image_span_cols_eq_euclidean_span_cols]
  -- Identify the transported columns with the vectors of `B.basis`.
  have hRange :
      Set.range ((EuclideanSpace.equiv (Fin n) ℝ).symm ∘
          (B.basisMatrix.map (Rat.castHom ℝ)).col) =
        Set.range B.basis := by
    apply congrArg Set.range
    funext j
    exact (B.inputBasis_apply_eq_col j).symm
  rw [hRange]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a unimodular integral
right change of a rational basis matrix remains nonsingular over `ℝ`. -/
lemma RationalBasis.unimodularChange_isUnit_det {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    IsUnit
      (((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)).det) := by
  -- First preserve determinant units over `ℚ`, then transport the product determinant to `ℝ`.
  have hUQ : IsUnit (U.map (Int.castRingHom ℚ)).det := by
    have hdet : ((U.det : ℤ) : ℚ) = (U.map (Int.castRingHom ℚ)).det := by
      simpa only [RingHom.mapMatrix_apply] using (Int.castRingHom ℚ).map_det U
    rw [← hdet]
    exact hU.map (Int.castRingHom ℚ)
  have hProduct : IsUnit (B.basisMatrix * U.map (Int.castRingHom ℚ)).det := by
    rw [Matrix.det_mul]
    exact B.nonsingular.mul hUQ
  have hdet :
      (((B.basisMatrix * U.map (Int.castRingHom ℚ)).det : ℚ) : ℝ) =
        ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)).det := by
    simpa only [RingHom.mapMatrix_apply] using
      (Rat.castHom ℝ).map_det (B.basisMatrix * U.map (Int.castRingHom ℚ))
  rw [← hdet]
  exact hProduct.map (Rat.castHom ℝ)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Euclidean basis obtained
from a rational basis by a unimodular integral right change. -/
noncomputable def RationalBasis.basisAfterUnimodular {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  euclideanBasisOfMatrix
    ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ))
    (B.unimodularChange_isUnit_det U hU)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: evaluation of a
unimodularly changed basis is evaluation of the corresponding matrix column. -/
lemma RationalBasis.basisAfterUnimodular_apply {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (j : Fin n) :
    B.basisAfterUnimodular U hU j =
      WithLp.toLp 2
        (((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)).col j) := by
  -- Apply the established computation rule for a Euclidean matrix basis.
  exact EuclideanBasisOfMatrix.apply_eq_col _ _ j

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a unimodular integral
right change preserves the lattice spanned by a rational basis. -/
lemma RationalBasis.basisAfterUnimodular_span {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm ''
        matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
      Submodule.span ℤ (Set.range (B.basisAfterUnimodular U hU)) := by
  -- Theorem 9.1 identifies the changed coordinate lattice with the original one.
  have hOriginal : IsUnit (B.basisMatrix.map (Rat.castHom ℝ)).det := by
    have hdet : ((B.basisMatrix.det : ℚ) : ℝ) =
        (B.basisMatrix.map (Rat.castHom ℝ)).det := by
      simpa only [RingHom.mapMatrix_apply] using (Rat.castHom ℝ).map_det B.basisMatrix
    rw [← hdet]
    exact B.nonsingular.map (Rat.castHom ℝ)
  have hCast :
      (U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        U.map (Int.castRingHom ℝ) := by
    ext i j
    simp only [Matrix.map_apply]
    exact_mod_cast rfl
  have hMatrix :
      (B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        B.basisMatrix.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ) := by
    rw [Matrix.map_mul, hCast]
  have hLattice :
      matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
        matrix_generated_lattice
          ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) := by
    apply (span_cols_eq_iff_exists_unimodular_right_mul _ _ hOriginal).2
    exact ⟨U, hU, hMatrix⟩
  -- Transport both matrix column lattices to Euclidean space and identify the changed columns.
  rw [hLattice, image_span_cols_eq_euclidean_span_cols]
  have hRange :
      Set.range
          ((EuclideanSpace.equiv (Fin n) ℝ).symm ∘
            ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)).col) =
        Set.range (B.basisAfterUnimodular U hU) := by
    apply congrArg Set.range
    funext j
    exact (B.basisAfterUnimodular_apply U hU j).symm
  rw [hRange]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: right multiplication by an
off-diagonal integral transvection preserves unit determinant. -/
lemma RationalBasis.mulTransvection_isUnit_det {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k ≠ j) (q : ℤ) :
    IsUnit (U * Matrix.transvection k j q).det := by
  -- The transvection has determinant one, so the product retains the original determinant.
  rw [Matrix.det_mul, Matrix.det_transvection_of_ne k j hkj q, mul_one]
  exact hU

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: casting an integral column
transvection commutes with the rational basis-matrix change. -/
lemma RationalBasis.changedMatrix_mulTransvection {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ) :
    ((B.basisMatrix *
          (U * Matrix.transvection k j q).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) =
      ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *
        Matrix.transvection k j (q : ℝ) := by
  -- Move both scalar casts through multiplication and identify the cast transvection entrywise.
  have hCastU :
      (U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        U.map (Int.castRingHom ℝ) := by
    ext a b
    simp only [Matrix.map_apply]
    exact_mod_cast rfl
  have hCastT :
      ((Matrix.transvection k j q).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        Matrix.transvection k j (q : ℝ) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply,
      Matrix.single_apply, Matrix.one_apply]
    split_ifs
    all_goals norm_num
  calc
    ((B.basisMatrix *
          (U * Matrix.transvection k j q).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) =
        B.basisMatrix.map (Rat.castHom ℝ) *
          ((U * Matrix.transvection k j q).map (Int.castRingHom ℚ)).map
            (Rat.castHom ℝ) := by
      rw [Matrix.map_mul]
    _ = B.basisMatrix.map (Rat.castHom ℝ) *
          (U.map (Int.castRingHom ℝ) * Matrix.transvection k j (q : ℝ)) := by
      rw [Matrix.map_mul, Matrix.map_mul, hCastU, hCastT]
    _ = (B.basisMatrix.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ)) *
          Matrix.transvection k j (q : ℝ) := by
      rw [Matrix.mul_assoc]
    _ = ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) *
          Matrix.transvection k j (q : ℝ) := by
      rw [Matrix.map_mul, hCastU]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: an integral right
transvection adds the indicated earlier basis multiple to exactly one basis vector. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_apply {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k ≠ j) (q : ℤ) (l : Fin n) :
    B.basisAfterUnimodular (U * Matrix.transvection k j q)
        (RationalBasis.mulTransvection_isUnit_det U hU hkj q) l =
      if l = j then
        B.basisAfterUnimodular U hU l +
          (q : ℝ) • B.basisAfterUnimodular U hU k
      else B.basisAfterUnimodular U hU l := by
  -- Rewrite both bases as matrix columns, then use the two transvection column formulas.
  rw [B.basisAfterUnimodular_apply]
  rw [B.changedMatrix_mulTransvection]
  by_cases hl : l = j
  · subst l
    rw [if_pos rfl, B.basisAfterUnimodular_apply, B.basisAfterUnimodular_apply]
    ext i
    simp [Matrix.col_apply, Matrix.mul_transvection_apply_same]
  · rw [if_neg hl, B.basisAfterUnimodular_apply]
    ext i
    simp [Matrix.col_apply, Matrix.mul_transvection_apply_of_ne, hl]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: at the changed column, the
difference produced by a negative transvection is the corresponding negative scalar multiple. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_sub_apply_same {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k ≠ j) (q : ℤ) :
    B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU hkj (-q)) j -
        B.basisAfterUnimodular U hU j =
      (-q : ℝ) • B.basisAfterUnimodular U hU k := by
  -- Specialize the column-update formula and cancel the unchanged column.
  rw [B.basisAfterUnimodular_mulTransvection_apply U hU hkj (-q) j,
    if_pos rfl, add_sub_cancel_left]
  simp

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: away from the changed
column, a transvection produces zero basis-vector difference. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_sub_apply_of_ne {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k ≠ j) (q : ℤ) (l : Fin n) (hl : l ≠ j) :
    B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU hkj (-q)) l -
        B.basisAfterUnimodular U hU l = 0 := by
  -- Specialize the unchanged-column branch and subtract the common vector.
  rw [B.basisAfterUnimodular_mulTransvection_apply U hU hkj (-q) l,
    if_neg hl, sub_self]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the changed vector under a
negative column transvection is the old vector minus the selected integral multiple. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_apply_same_sub {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k ≠ j) (q : ℤ) :
    B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
        (RationalBasis.mulTransvection_isUnit_det U hU hkj (-q)) j =
      B.basisAfterUnimodular U hU j -
        (q : ℝ) • B.basisAfterUnimodular U hU k := by
  -- Specialize the update formula and normalize the cast of the negative integer coefficient.
  rw [B.basisAfterUnimodular_mulTransvection_apply U hU hkj (-q) j, if_pos rfl]
  simp [sub_eq_add_neg]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: subtracting an integral
multiple of an earlier column is a lower-triangular basis update. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_lowerTriangular {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k < j) (q : ℤ) :
    ∀ l,
      B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU (ne_of_lt hkj) (-q)) l -
        B.basisAfterUnimodular U hU l ∈
      Submodule.span ℝ (B.basisAfterUnimodular U hU '' Set.Iio l) := by
  -- The changed column is an earlier-generator multiple, while every other difference is zero.
  intro l
  by_cases hl : l = j
  · subst l
    rw [B.basisAfterUnimodular_mulTransvection_sub_apply_same U hU (ne_of_lt hkj) q]
    have hgen :
        B.basisAfterUnimodular U hU k ∈
          Submodule.span ℝ (B.basisAfterUnimodular U hU '' Set.Iio j) :=
      Submodule.subset_span ⟨k, hkj, rfl⟩
    exact Submodule.smul_mem _ (-q : ℝ) hgen
  · rw [B.basisAfterUnimodular_mulTransvection_sub_apply_of_ne U hU (ne_of_lt hkj) q l hl]
    exact Submodule.zero_mem _

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: subtracting an integral
multiple of an earlier column preserves the complete Gram-Schmidt basis. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_gramSchmidtBasis {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k < j) (q : ℤ) :
    gramSchmidtBasis (B.basisAfterUnimodular U hU) =
      gramSchmidtBasis
        (B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU (ne_of_lt hkj) (-q))) := by
  -- Feed the separately certified lower-triangular update into Gram-Schmidt invariance.
  exact GramSchmidtUpdate.gramSchmidtBasis_eq_ofLowerTriangularUpdate _ _
    (B.basisAfterUnimodular_mulTransvection_lowerTriangular U hU hkj q)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: an earlier-column shear
subtracts its integral coefficient from the corresponding Gram-Schmidt coefficient. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_coefficient {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k < j) (q : ℤ) :
    gram_schmidt_coefficient
        (B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU (ne_of_lt hkj) (-q))) j k =
      gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k - (q : ℝ) := by
  -- Combine Gram-Schmidt invariance with the explicit changed-vector formula.
  exact GramSchmidtUpdate.coefficient_sub_smul_self _ _ j k (q : ℝ)
    (B.basisAfterUnimodular_mulTransvection_gramSchmidtBasis U hU hkj q)
    (B.basisAfterUnimodular_mulTransvection_apply_same_sub U hU (ne_of_lt hkj) q)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: an earlier-column shear
leaves every coefficient indexed strictly after the source column unchanged. -/
lemma RationalBasis.basisAfterUnimodular_mulTransvection_coefficient_of_lt {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j l : Fin n} (hkj : k < j) (hkl : k < l) (q : ℤ) :
    gram_schmidt_coefficient
        (B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU (ne_of_lt hkj) (-q))) j l =
      gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j l := by
  -- Apply the abstract coefficient invariance to the verified shear interfaces.
  exact GramSchmidtUpdate.coefficient_sub_smul_of_lt _ _ j k l (q : ℝ) hkl
    (B.basisAfterUnimodular_mulTransvection_gramSchmidtBasis U hU hkj q)
    (B.basisAfterUnimodular_mulTransvection_apply_same_sub U hU (ne_of_lt hkj) q)

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: choosing the nearest integer
for an earlier-column shear makes the selected Gram-Schmidt coefficient at most `1 / 2`. -/
lemma RationalBasis.basisAfterUnimodular_roundTransvection_coefficient_bound {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    {k j : Fin n} (hkj : k < j) :
    let q : ℤ := round (gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k)
    |gram_schmidt_coefficient
        (B.basisAfterUnimodular (U * Matrix.transvection k j (-q))
          (RationalBasis.mulTransvection_isUnit_det U hU (ne_of_lt hkj) (-q))) j k| ≤
      (1 : ℝ) / 2 := by
  -- The coefficient update is exactly the nearest-integer remainder.
  dsimp
  rw [B.basisAfterUnimodular_mulTransvection_coefficient U hU hkj]
  exact abs_sub_round _

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: equality of one input
vector and of the Gram-Schmidt bases preserves every coefficient of that vector. -/
lemma GramSchmidtUpdate.coefficient_eq_of_apply_eq_of_gramSchmidtBasis_eq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C C' : Basis (Fin n) ℝ E) (j k : Fin n)
    (hvec : C' j = C j) (hgs : gramSchmidtBasis C = gramSchmidtBasis C') :
    gram_schmidt_coefficient C' j k = gram_schmidt_coefficient C j k := by
  -- Rewrite the input vector and the relevant Gram-Schmidt vector to the original basis.
  have hgsk : gramSchmidtBasis C k = gramSchmidtBasis C' k :=
    congrArg (fun D : Basis (Fin n) ℝ E ↦ D k) hgs
  rw [gram_schmidt_coefficient, gram_schmidt_coefficient, hvec, ← hgsk]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a reverse sweep through a
fixed column size-reduces the requested terminal interval while preserving all other columns and
the complete Gram-Schmidt basis. -/
lemma RationalBasis.exists_columnSizeReducedUnimodularForSteps {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det)
    (j : Fin n) (steps : ℕ) (hsteps : steps ≤ j.val) :
    ∃ (U' : Matrix (Fin n) (Fin n) ℤ) (hU' : IsUnit U'.det),
      gramSchmidtBasis (B.basisAfterUnimodular U hU) =
          gramSchmidtBasis (B.basisAfterUnimodular U' hU') ∧
        (∀ l, l ≠ j →
          B.basisAfterUnimodular U' hU' l = B.basisAfterUnimodular U hU l) ∧
        ∀ k, j.val - steps ≤ k.val → k < j →
          |gram_schmidt_coefficient (B.basisAfterUnimodular U' hU') j k| ≤
            (1 : ℝ) / 2 := by
  -- Induct on the number of already processed indices, adding the next shear on the left.
  induction steps generalizing U with
  | zero =>
      refine ⟨U, hU, rfl, ?_, ?_⟩
      · intro l hl
        rfl
      · intro k hinterval hkj
        omega
  | succ steps ih =>
      have hprevious : steps ≤ j.val := by omega
      obtain ⟨U₁, hU₁, hgs₁, hcols₁, hbounds₁⟩ := ih U hU hprevious
      let k : Fin n := ⟨j.val - (steps + 1), by omega⟩
      have hkj : k < j := by
        apply Fin.mk_lt_mk.mpr
        omega
      let q : ℤ := round
        (gram_schmidt_coefficient (B.basisAfterUnimodular U₁ hU₁) j k)
      let U₂ : Matrix (Fin n) (Fin n) ℤ := U₁ * Matrix.transvection k j (-q)
      have hU₂ : IsUnit U₂.det := by
        exact RationalBasis.mulTransvection_isUnit_det U₁ hU₁ (ne_of_lt hkj) (-q)
      refine ⟨U₂, hU₂, ?_, ?_, ?_⟩
      · -- The new shear is lower triangular, so concatenate the two Gram-Schmidt equalities.
        exact hgs₁.trans
          (B.basisAfterUnimodular_mulTransvection_gramSchmidtBasis U₁ hU₁ hkj q)
      · -- Only column `j` changes in either the previous sweep or the new shear.
        intro l hlj
        calc
          B.basisAfterUnimodular U₂ hU₂ l =
              B.basisAfterUnimodular U₁ hU₁ l := by
            dsimp [U₂, hU₂]
            rw [B.basisAfterUnimodular_mulTransvection_apply U₁ hU₁
              (ne_of_lt hkj) (-q) l, if_neg hlj]
          _ = B.basisAfterUnimodular U hU l := hcols₁ l hlj
      · -- The new endpoint is bounded by rounding; later processed indices retain their bounds.
        intro l hinterval hlj
        by_cases hlk : l = k
        · subst l
          dsimp [U₂, hU₂, q]
          exact B.basisAfterUnimodular_roundTransvection_coefficient_bound U₁ hU₁ hkj
        · have hkl : k < l := by
            have hkle : k.val ≤ l.val := by
              simpa [k] using hinterval
            have hkne : k.val ≠ l.val := by
              intro hval
              apply hlk
              exact Fin.ext hval.symm
            exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne hkle hkne)
          have hpreviousInterval : j.val - steps ≤ l.val := by
            have hklval : k.val < l.val := hkl
            simp only [k] at hklval
            omega
          dsimp [U₂, hU₂, q]
          rw [B.basisAfterUnimodular_mulTransvection_coefficient_of_lt U₁ hU₁ hkj hkl]
          exact hbounds₁ l hpreviousInterval hlj

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every unimodular
representative can be size-reduced by lower-triangular integral shears without changing its
Gram-Schmidt basis. -/
lemma RationalBasis.exists_sizeReducedUnimodular {n : ℕ}
    (B : RationalBasis n) (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    ∃ (U' : Matrix (Fin n) (Fin n) ℤ) (hU' : IsUnit U'.det),
      gramSchmidtBasis (B.basisAfterUnimodular U hU) =
          gramSchmidtBasis (B.basisAfterUnimodular U' hU') ∧
        basis_reduction_condition_i (B.basisAfterUnimodular U' hU') := by
  -- Sweep columns from left to right while retaining the bounds on every completed column.
  have hsweep : ∀ m : ℕ, m ≤ n →
      ∃ (U' : Matrix (Fin n) (Fin n) ℤ) (hU' : IsUnit U'.det),
        gramSchmidtBasis (B.basisAfterUnimodular U hU) =
            gramSchmidtBasis (B.basisAfterUnimodular U' hU') ∧
          ∀ j : Fin n, j.val < m → ∀ k, k < j →
            |gram_schmidt_coefficient (B.basisAfterUnimodular U' hU') j k| ≤
              (1 : ℝ) / 2 := by
    intro m hm
    induction m with
    | zero =>
        refine ⟨U, hU, rfl, ?_⟩
        intro j hj
        omega
    | succ m ih =>
        have hmn : m ≤ n := by omega
        obtain ⟨U₁, hU₁, hgs₁, hbounds₁⟩ := ih hmn
        by_cases hmn' : m < n
        · let j : Fin n := ⟨m, hmn'⟩
          obtain ⟨U₂, hU₂, hgs₂, hcols₂, hbounds₂⟩ :=
            B.exists_columnSizeReducedUnimodularForSteps U₁ hU₁ j j.val (le_refl j.val)
          refine ⟨U₂, hU₂, hgs₁.trans hgs₂, ?_⟩
          intro l hl k hkl
          by_cases hlj : l = j
          · subst l
            exact hbounds₂ k (by simp) hkl
          · have hlm : l.val < m := by
              have hlval_ne : l.val ≠ m := by
                intro hval
                apply hlj
                exact Fin.ext (by simpa [j] using hval)
              omega
            have hvec := hcols₂ l hlj
            have hcoeff :=
              GramSchmidtUpdate.coefficient_eq_of_apply_eq_of_gramSchmidtBasis_eq
                (B.basisAfterUnimodular U₁ hU₁)
                (B.basisAfterUnimodular U₂ hU₂) l k hvec hgs₂
            rw [hcoeff]
            exact hbounds₁ l hlm k hkl
        · have hmnEq : m = n := by omega
          subst m
          omega
  obtain ⟨U', hU', hgs, hbounds⟩ := hsweep n (le_refl n)
  refine ⟨U', hU', hgs, ?_⟩
  -- At the completed sweep, every finite target index lies in the processed range.
  intro j k hkj
  exact hbounds j j.isLt k hkj

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: right multiplication by a
swap matrix evaluates a column at the swapped index. -/
lemma Matrix.mul_swap_apply_equiv {R m n : Type*} [Semiring R] [Fintype n] [DecidableEq n]
    (A : Matrix m n R) (i j k : n) (a : m) :
    (A * Matrix.swap R i j) a k = A a (Equiv.swap i j k) := by
  -- Split according to whether the requested column is one of the two exchanged columns.
  by_cases hki : k = i
  · subst k
    rw [Matrix.mul_swap_apply_left, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst k
      rw [Matrix.mul_swap_apply_right, Equiv.swap_apply_right]
    · rw [Matrix.mul_swap_of_ne hki hkj]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: left multiplication by a
swap matrix evaluates a row at the swapped index. -/
lemma Matrix.swap_mul_apply_equiv {R m n : Type*} [Semiring R] [Fintype n] [DecidableEq n]
    (A : Matrix n m R) (i j k : n) (a : m) :
    (Matrix.swap R i j * A) k a = A (Equiv.swap i j k) a := by
  -- Split according to whether the requested row is one of the two exchanged rows.
  by_cases hki : k = i
  · subst k
    rw [Matrix.swap_mul_apply_left, Equiv.swap_apply_left]
  · by_cases hkj : k = j
    · subst k
      rw [Matrix.swap_mul_apply_right, Equiv.swap_apply_right]
    · rw [Matrix.swap_mul_of_ne hki hkj]
      rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: multiplying a unimodular
integer matrix by a column swap remains unimodular. -/
lemma Matrix.isUnit_det_mul_swap {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (i j : Fin n) :
    IsUnit (U * Matrix.swap ℤ i j).det := by
  -- The swap is its own matrix inverse, hence has unit determinant.
  rw [Matrix.det_mul]
  exact hU.mul (Matrix.isUnit_det_of_right_inverse (Matrix.swap_mul_self i j))

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: swapping columns in the
unimodular matrix swaps the corresponding vectors of the changed Euclidean basis. -/
lemma RationalBasis.basisAfterUnimodular_mulSwap_apply {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (i j k : Fin n) :
    B.basisAfterUnimodular (U * Matrix.swap ℤ i j)
        (Matrix.isUnit_det_mul_swap U hU i j) k =
      B.basisAfterUnimodular U hU (Equiv.swap i j k) := by
  -- Cast the swapped coordinate matrix and evaluate its requested column.
  have hInt :
      (U * Matrix.swap ℤ i j).map (Int.castRingHom ℚ) =
        U.map (Int.castRingHom ℚ) * Matrix.swap ℚ i j := by
    rw [Matrix.map_mul, Matrix.map_swap]
  have hmatrix :
      (B.basisMatrix * (U * Matrix.swap ℤ i j).map (Int.castRingHom ℚ)).map
          (Rat.castHom ℝ) =
        (B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) *
          Matrix.swap ℝ i j := by
    calc
      (B.basisMatrix * (U * Matrix.swap ℤ i j).map (Int.castRingHom ℚ)).map
          (Rat.castHom ℝ) =
          (B.basisMatrix *
            (U.map (Int.castRingHom ℚ) * Matrix.swap ℚ i j)).map (Rat.castHom ℝ) := by
        rw [hInt]
      _ = ((B.basisMatrix * U.map (Int.castRingHom ℚ)) *
            Matrix.swap ℚ i j).map (Rat.castHom ℝ) := by
        rw [Matrix.mul_assoc]
      _ = (B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) *
            Matrix.swap ℝ i j := by
        rw [Matrix.map_mul, Matrix.map_swap]
  rw [B.basisAfterUnimodular_apply, B.basisAfterUnimodular_apply]
  ext a
  simp only [Matrix.col_apply, hmatrix]
  exact Matrix.mul_swap_apply_equiv
    ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) i j k a

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the fixed-denominator Gram
matrix of a column-swapped representative is conjugated by the same swap matrix. -/
lemma RationalBasis.integralGramMatrix_mulSwap {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    B.integralGramMatrix (U * Matrix.swap ℤ i j) =
      Matrix.swap ℤ i j * B.integralGramMatrix U * Matrix.swap ℤ i j := by
  -- Transpose the product, use symmetry of the swap, and reassociate the four factors.
  simp only [RationalBasis.integralGramMatrix, Matrix.transpose_mul, Matrix.transpose_swap]
  noncomm_ring

namespace GramSchmidtUpdate

universe v

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [WellFoundedLT ι]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the unit upper-triangular
coefficient matrix expressing a family in its Gram-Schmidt family. -/
noncomputable def gramSchmidtChangeMatrix (w : ι → E) : Matrix ι ι ℝ :=
  fun i j ↦ if i = j then 1 else if i < j then
    ⟪gramSchmidt ℝ w i, w j⟫_ℝ / ‖gramSchmidt ℝ w i‖ ^ 2 else 0

omit [Fintype ι] in
/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram-Schmidt change
matrix has diagonal entries equal to one. -/
lemma gramSchmidtChangeMatrix_apply_self (w : ι → E) (i : ι) :
    gramSchmidtChangeMatrix w i i = 1 := by
  -- The diagonal branch of the coefficient matrix is definitionally one.
  simp [gramSchmidtChangeMatrix]

omit [Fintype ι] in
/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram-Schmidt change
matrix is upper triangular. -/
lemma gramSchmidtChangeMatrix_blockTriangular (w : ι → E) :
    (gramSchmidtChangeMatrix w).BlockTriangular id := by
  -- An entry below the diagonal reaches the zero branch of the definition.
  intro i j hji
  change j < i at hji
  rw [gramSchmidtChangeMatrix, if_neg hji.ne', if_neg (not_lt.mpr hji.le)]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram-Schmidt change
matrix has determinant one. -/
lemma gramSchmidtChangeMatrix_det (w : ι → E) :
    (gramSchmidtChangeMatrix w).det = 1 := by
  -- Evaluate the determinant of the unit upper-triangular matrix on its diagonal.
  rw [Matrix.det_of_upperTriangular (gramSchmidtChangeMatrix_blockTriangular w)]
  simp [gramSchmidtChangeMatrix_apply_self]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: multiplication by the
Gram-Schmidt change matrix reconstructs every vector of the original family. -/
lemma sum_gramSchmidtChangeMatrix_smul (w : ι → E) (j : ι) :
    ∑ i, gramSchmidtChangeMatrix w i j • gramSchmidt ℝ w i = w j := by
  classical
  -- Discard entries above `j`, split off the diagonal, and use the defining decomposition.
  have hsupport :
      ∑ i ∈ insert j (Finset.Iio j),
          gramSchmidtChangeMatrix w i j • gramSchmidt ℝ w i =
        ∑ i, gramSchmidtChangeMatrix w i j • gramSchmidt ℝ w i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hnot
    have hij : j < i := by
      have hne : i ≠ j := by
        intro hij
        subst i
        exact hnot (Finset.mem_insert.mpr (Or.inl rfl))
      have hnotlt : ¬i < j := by
        intro hlt
        exact hnot (Finset.mem_insert.mpr (Or.inr (Finset.mem_Iio.mpr hlt)))
      exact lt_of_le_of_ne (not_lt.mp hnotlt) hne.symm
    simp [gramSchmidtChangeMatrix, ne_of_gt hij, not_lt.mpr hij.le]
  rw [← hsupport, Finset.sum_insert Finset.notMem_Iio_self]
  simp only [gramSchmidtChangeMatrix_apply_self, one_smul]
  have hcoeff :
      ∑ i ∈ Finset.Iio j,
          gramSchmidtChangeMatrix w i j • gramSchmidt ℝ w i =
        ∑ i ∈ Finset.Iio j,
          (⟪gramSchmidt ℝ w i, w j⟫_ℝ / ‖gramSchmidt ℝ w i‖ ^ 2) •
            gramSchmidt ℝ w i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i < j := Finset.mem_Iio.mp hi
    simp [gramSchmidtChangeMatrix, hij.ne, hij]
  rw [hcoeff]
  exact (gramSchmidt_def'' ℝ w j).symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram matrix factors
through the Gram-Schmidt change matrix and the Gram matrix of the orthogonalized family. -/
lemma gram_eq_changeMatrix_transpose_mul (w : ι → E) :
    Matrix.gram ℝ w =
      (gramSchmidtChangeMatrix w)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ w) *
        gramSchmidtChangeMatrix w := by
  -- Expand both matrix products and replace each reconstructed sum by the original vector.
  ext i j
  calc
    (Matrix.gram ℝ w) i j = ⟪w i, w j⟫_ℝ := rfl
    _ = ⟪∑ x, gramSchmidtChangeMatrix w x i • gramSchmidt ℝ w x,
          ∑ y, gramSchmidtChangeMatrix w y j • gramSchmidt ℝ w y⟫_ℝ := by
      rw [sum_gramSchmidtChangeMatrix_smul, sum_gramSchmidtChangeMatrix_smul]
    _ = ∑ x, ∑ y,
          gramSchmidtChangeMatrix w x i *
            ⟪gramSchmidt ℝ w x, gramSchmidt ℝ w y⟫_ℝ *
              gramSchmidtChangeMatrix w y j := by
      simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ((gramSchmidtChangeMatrix w)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ w) *
          gramSchmidtChangeMatrix w) i j := by
      have hswap :
          (∑ x, ∑ y,
            gramSchmidtChangeMatrix w x i *
              ⟪gramSchmidt ℝ w x, gramSchmidt ℝ w y⟫_ℝ *
                gramSchmidtChangeMatrix w y j) =
            ∑ y, ∑ x,
              gramSchmidtChangeMatrix w x i *
                ⟪gramSchmidt ℝ w x, gramSchmidt ℝ w y⟫_ℝ *
                  gramSchmidtChangeMatrix w y j := Finset.sum_comm
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply,
        Finset.sum_mul] using hswap

omit [Fintype ι] in
/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the Gram matrix of a
Gram-Schmidt family is diagonal with squared norms on the diagonal. -/
lemma gram_gramSchmidt_eq_diagonal (w : ι → E) :
    Matrix.gram ℝ (gramSchmidt ℝ w) =
      Matrix.diagonal (fun i ↦ ‖gramSchmidt ℝ w i‖ ^ 2) := by
  -- Orthogonality kills off-diagonal entries, while self-inner-products are squared norms.
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · rw [Matrix.gram_apply, Matrix.diagonal_apply_ne _ hij]
    exact gramSchmidt_orthogonal ℝ w hij

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the determinant of a real
Gram matrix is the product of the squared norms produced by Gram-Schmidt. -/
lemma det_gram_eq_prod_norm_sq (w : ι → E) :
    (Matrix.gram ℝ w).det = ∏ i, ‖gramSchmidt ℝ w i‖ ^ 2 := by
  -- Take determinants in the triangular Gram factorization and evaluate the diagonal factor.
  rw [gram_eq_changeMatrix_transpose_mul w, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, gramSchmidtChangeMatrix_det,
    gram_gramSchmidt_eq_diagonal, Matrix.det_diagonal, one_mul, mul_one]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: restricting a family to an
initial interval commutes with Gram-Schmidt orthogonalization. -/
lemma gramSchmidt_restrict_finIic {n : ℕ} (w : Fin n → E) (j : Fin n)
    (i : Set.Iic j) :
    gramSchmidt ℝ (w ∘ ((↑) : Set.Iic j → Fin n)) i = gramSchmidt ℝ w i.1 := by
  -- Strong induction on the numeric index identifies the two predecessor sums.
  have haux : ∀ (m : ℕ) (hmn : m < n) (hmj : m ≤ j.val),
      gramSchmidt ℝ (w ∘ ((↑) : Set.Iic j → Fin n)) ⟨⟨m, hmn⟩, hmj⟩ =
        gramSchmidt ℝ w ⟨m, hmn⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hmn hmj
        rw [gramSchmidt_def, gramSchmidt_def]
        congr 1
        apply Finset.sum_bij (fun k hk ↦ k.1)
        · intro k hk
          simpa only [Finset.mem_Iio, Fin.mk_lt_mk] using hk
        · intro a ha b hb hab
          exact Subtype.ext hab
        · intro k hk
          let k' : Set.Iic j := ⟨k, (Finset.mem_Iio.mp hk).le.trans hmj⟩
          refine ⟨k', ?_, rfl⟩
          simpa only [Finset.mem_Iio, Fin.mk_lt_mk, k'] using hk
        · intro k hk
          change
            (ℝ ∙ gramSchmidt ℝ (w ∘ ((↑) : Set.Iic j → Fin n)) k).starProjection
                (w ⟨m, hmn⟩) =
              (ℝ ∙ gramSchmidt ℝ w k.1).starProjection (w ⟨m, hmn⟩)
          have hkm : k.1.val < m := by
            simpa only [Finset.mem_Iio, Fin.mk_lt_mk] using hk
          rw [ih k.1.val hkm k.1.isLt k.2]
  exact haux i.1.val i.1.isLt i.2

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a leading principal Gram
determinant is the product of the squared norms of the corresponding ambient Gram-Schmidt vectors.
-/
lemma det_gram_finIic_eq_prod_norm_sq {n : ℕ} (C : Basis (Fin n) ℝ E) (j : Fin n) :
    (Matrix.gram ℝ (C ∘ ((↑) : Set.Iic j → Fin n))).det =
      ∏ i : Set.Iic j, ‖gramSchmidt ℝ C i.1‖ ^ 2 := by
  -- Apply the generic determinant identity and identify the restricted Gram-Schmidt vectors.
  calc
    (Matrix.gram ℝ (C ∘ ((↑) : Set.Iic j → Fin n))).det =
        ∏ i : Set.Iic j,
          ‖gramSchmidt ℝ (C ∘ ((↑) : Set.Iic j → Fin n)) i‖ ^ 2 :=
      det_gram_eq_prod_norm_sq _
    _ = ∏ i : Set.Iic j, ‖gramSchmidt ℝ C i.1‖ ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [gramSchmidt_restrict_finIic]

end GramSchmidtUpdate

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: Gram–Schmidt at an index
depends only on the input family through that index. -/
lemma GramSchmidtUpdate.gramSchmidt_eq_of_eqOn_Iic {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : Fin n → E) (i : Fin n) (h : ∀ k, k ≤ i → v k = w k) :
    gramSchmidt ℝ v i = gramSchmidt ℝ w i := by
  -- Restrict both families to the common finite prefix and use pointwise equality there.
  let last : Set.Iic i := ⟨i, le_refl i⟩
  rw [← GramSchmidtUpdate.gramSchmidt_restrict_finIic v i last,
    ← GramSchmidtUpdate.gramSchmidt_restrict_finIic w i last]
  congr 1
  funext k
  exact h k.1 k.2

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: after swapping adjacent
columns, the new Gram–Schmidt vector at the lower index is the old two-term Lovász vector. -/
lemma RationalBasis.gramSchmidt_mulSwap_current {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (k j : Fin n)
    (hAdjacent : j.val = k.val + 1) :
    gramSchmidt ℝ
        (B.basisAfterUnimodular (U * Matrix.swap ℤ k j)
          (Matrix.isUnit_det_mul_swap U hU k j)) k =
      gramSchmidt ℝ (B.basisAfterUnimodular U hU) j +
        gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k •
          gramSchmidt ℝ (B.basisAfterUnimodular U hU) k := by
  -- Name the old and swapped bases, then identify all vectors strictly before the swap.
  let C := B.basisAfterUnimodular U hU
  let D := B.basisAfterUnimodular (U * Matrix.swap ℤ k j)
    (Matrix.isUnit_det_mul_swap U hU k j)
  have hkj : k ≠ j := by
    intro h
    subst j
    omega
  have hDapply (l : Fin n) : D l = C (Equiv.swap k j l) := by
    exact B.basisAfterUnimodular_mulSwap_apply U hU k j l
  have hprior (l : Fin n) (hlk : l < k) : D l = C l := by
    rw [hDapply, Equiv.swap_apply_of_ne_of_ne]
    · exact ne_of_lt hlk
    · intro hlj
      subst l
      omega
  have hgsPrior (l : Fin n) (hlk : l < k) :
      gramSchmidt ℝ D l = gramSchmidt ℝ C l := by
    apply GramSchmidtUpdate.gramSchmidt_eq_of_eqOn_Iic D C l
    intro a hal
    exact hprior a (hal.trans_lt hlk)
  have hDk : D k = C j := by
    rw [hDapply, Equiv.swap_apply_left]
  -- The predecessor sums agree because every earlier vector and Gram–Schmidt vector agrees.
  have hsum :
      ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ D l).starProjection (D k) =
        ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ C l).starProjection (C j) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hgsPrior l (Finset.mem_Iio.mp hl), hDk]
  have hIio : Finset.Iio j = insert k (Finset.Iio k) := by
    ext l
    simp only [Finset.mem_Iio, Finset.mem_insert]
    constructor
    · intro hlj
      by_cases hlk : l = k
      · exact Or.inl hlk
      · exact Or.inr (by omega)
    · rintro (rfl | hlk)
      · omega
      · omega
  have hknot : k ∉ Finset.Iio k := by
    simp
  have hdecomp := gramSchmidt_def'' ℝ C j
  rw [hIio, Finset.sum_insert hknot] at hdecomp
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdecomp
  have hterm :
      (⟪gramSchmidt ℝ C k, C j⟫_ℝ / ‖gramSchmidt ℝ C k‖ ^ 2) •
          gramSchmidt ℝ C k =
        gram_schmidt_coefficient C j k • gramSchmidt ℝ C k := by
    unfold gram_schmidt_coefficient
    rw [coe_gramSchmidtBasis, real_inner_comm]
  rw [hterm] at hdecomp
  have hprojection :
      ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ C l).starProjection (C j) =
        ∑ l ∈ Finset.Iio k,
          (⟪gramSchmidt ℝ C l, C j⟫_ℝ / ‖gramSchmidt ℝ C l‖ ^ 2) •
            gramSchmidt ℝ C l := by
    simp only [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  have hsolve :
      C j - ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ C l).starProjection (C j) =
        gramSchmidt ℝ C j + gram_schmidt_coefficient C j k • gramSchmidt ℝ C k := by
    rw [hprojection, sub_eq_iff_eq_add]
    calc
      C j = gramSchmidt ℝ C j +
          (gram_schmidt_coefficient C j k • gramSchmidt ℝ C k +
            ∑ x ∈ Finset.Iio k,
              (⟪gramSchmidt ℝ C x, C j⟫_ℝ / ‖gramSchmidt ℝ C x‖ ^ 2) •
                gramSchmidt ℝ C x) := hdecomp
      _ = (gramSchmidt ℝ C j +
            gram_schmidt_coefficient C j k • gramSchmidt ℝ C k) +
          ∑ x ∈ Finset.Iio k,
            (⟪gramSchmidt ℝ C x, C j⟫_ℝ / ‖gramSchmidt ℝ C x‖ ^ 2) •
              gramSchmidt ℝ C x := by
        abel
  -- Subtract the common earlier-projection sum from the old adjacent decomposition.
  change gramSchmidt ℝ D k =
    gramSchmidt ℝ C j + gram_schmidt_coefficient C j k • gramSchmidt ℝ C k
  have hsum' := hsum
  rw [hDk] at hsum'
  calc
    gramSchmidt ℝ D k =
        D k - ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ D l).starProjection (D k) :=
      gramSchmidt_def ℝ D k
    _ = C j -
        ∑ l ∈ Finset.Iio k, (ℝ ∙ gramSchmidt ℝ C l).starProjection (C j) := by
      rw [hDk, hsum']
    _ = gramSchmidt ℝ C j +
        gram_schmidt_coefficient C j k • gramSchmidt ℝ C k := hsolve

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the real cast of the
transported rational Gram matrix is the Gram matrix of the changed Euclidean basis. -/
lemma RationalBasis.changedRationalGram_map_real {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) :
    (B.changedRationalGram U).map (Rat.castHom ℝ) =
      Matrix.gram ℝ (B.basisAfterUnimodular U hU) := by
  -- Cast the matrix products, reassociate them, and identify the resulting Euclidean columns.
  have hCastU :
      (U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        U.map (Int.castRingHom ℝ) := by
    ext i j
    simp only [Matrix.map_apply]
    exact_mod_cast rfl
  have hChanged :
      (B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ) =
        B.basisMatrix.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ) := by
    rw [Matrix.map_mul, hCastU]
  calc
    (B.changedRationalGram U).map (Rat.castHom ℝ) =
        (U.map (Int.castRingHom ℝ))ᵀ *
          (B.basisMatrix.map (Rat.castHom ℝ))ᵀ *
            B.basisMatrix.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ) := by
      simp only [RationalBasis.changedRationalGram, RationalBasis.rationalGramMatrix,
        Matrix.map_mul, Matrix.transpose_map, hCastU]
      noncomm_ring
    _ = ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ))ᵀ *
          ((B.basisMatrix * U.map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) := by
      rw [hChanged, Matrix.transpose_mul]
      noncomm_ring
    _ = Matrix.gram ℝ (B.basisAfterUnimodular U hU) := by
      rw [← EuclideanBasisOfMatrix.gram_columns]
      congr 1
      funext j
      exact (B.basisAfterUnimodular_apply U hU j).symm

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a leading integral Gram
determinant casts to the fixed denominator power times its rational Gram determinant. -/
lemma RationalBasis.prefixGramDet_cast_rat {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    (B.prefixGramDet U j : ℚ) =
      (B.rationalGramMatrix.den : ℚ) ^ Fintype.card (Set.Iic j) *
        ((B.changedRationalGram U).submatrix
          ((↑) : Set.Iic j → Fin n) ((↑) : Set.Iic j → Fin n)).det := by
  -- Cast the principal block, use the fixed-denominator matrix identity, and take determinants.
  let f : Set.Iic j → Fin n := (↑)
  calc
    (B.prefixGramDet U j : ℚ) =
        (((B.integralGramMatrix U).submatrix f f).map
          (Int.castRingHom ℚ)).det := by
      simpa [RationalBasis.prefixGramDet] using
        (Int.castRingHom ℚ).map_det ((B.integralGramMatrix U).submatrix f f)
    _ = (((B.integralGramMatrix U).map (Int.castRingHom ℚ)).submatrix f f).det := by
      rw [Matrix.submatrix_map]
    _ = (((B.rationalGramMatrix.den : ℚ) •
          B.changedRationalGram U).submatrix f f).det := by
      rw [B.integralGramMatrix_map_ratCast U]
    _ = ((B.rationalGramMatrix.den : ℚ) •
          (B.changedRationalGram U).submatrix f f).det := by
      have hsub := Matrix.submatrix_smul
        (l := Set.Iic j) (o := Set.Iic j)
        (B.rationalGramMatrix.den : ℚ) (B.changedRationalGram U)
      exact congrArg Matrix.det (congrFun (congrFun hsub f) f)
    _ = (B.rationalGramMatrix.den : ℚ) ^ Fintype.card (Set.Iic j) *
          ((B.changedRationalGram U).submatrix f f).det := by
      rw [Matrix.det_smul]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the real value of a leading
integral Gram determinant is the fixed denominator power times the Gram-Schmidt prefix product. -/
lemma RationalBasis.prefixGramDet_cast_real {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (j : Fin n) :
    (B.prefixGramDet U j : ℝ) =
      (B.rationalGramMatrix.den : ℝ) ^ Fintype.card (Set.Iic j) *
        ∏ i : Set.Iic j,
          ‖gramSchmidt ℝ (B.basisAfterUnimodular U hU) i.1‖ ^ 2 := by
  -- Cast the rational identity, identify the changed Gram matrix, then use the prefix formula.
  have hcast := congrArg (Rat.castHom ℝ) (B.prefixGramDet_cast_rat U j)
  have hdet := (Rat.castHom ℝ).map_det
    ((B.changedRationalGram U).submatrix
      ((↑) : Set.Iic j → Fin n) ((↑) : Set.Iic j → Fin n))
  have hsubmap :
      (Rat.castHom ℝ).mapMatrix ((B.changedRationalGram U).submatrix
          ((↑) : Set.Iic j → Fin n) ((↑) : Set.Iic j → Fin n)) =
        ((B.changedRationalGram U).map (Rat.castHom ℝ)).submatrix
          ((↑) : Set.Iic j → Fin n) ((↑) : Set.Iic j → Fin n) := rfl
  simp only [map_mul, map_pow] at hcast
  rw [hdet, hsubmap, B.changedRationalGram_map_real U hU,
    Matrix.submatrix_gram,
    GramSchmidtUpdate.det_gram_finIic_eq_prod_norm_sq] at hcast
  simpa using hcast

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every leading integral Gram
determinant attached to a unimodular representative is strictly positive. -/
lemma RationalBasis.prefixGramDet_pos {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (j : Fin n) :
    0 < B.prefixGramDet U j := by
  -- Its real cast is a product of a positive denominator power and nonzero squared norms.
  have hden : (0 : ℝ) < B.rationalGramMatrix.den := by
    exact_mod_cast Nat.pos_of_ne_zero B.rationalGramMatrix.den_ne_zero
  have hprod : 0 < ∏ i : Set.Iic j,
      ‖gramSchmidt ℝ (B.basisAfterUnimodular U hU) i.1‖ ^ 2 := by
    apply Finset.prod_pos
    intro i hi
    exact sq_pos_of_pos (norm_pos_iff.mpr
      (gramSchmidt_ne_zero i.1 (B.basisAfterUnimodular U hU).linearIndependent))
  have hreal : (0 : ℝ) < B.prefixGramDet U j := by
    rw [B.prefixGramDet_cast_real U hU j]
    exact mul_pos (pow_pos hden _) hprod
  exact_mod_cast hreal

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: representatives with the
same Gram-Schmidt basis have equal leading integral Gram determinants. -/
lemma RationalBasis.prefixGramDet_eq_of_gramSchmidtBasis_eq {n : ℕ} (B : RationalBasis n)
    (U V : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hgs : gramSchmidtBasis (B.basisAfterUnimodular U hU) =
      gramSchmidtBasis (B.basisAfterUnimodular V hV)) (j : Fin n) :
    B.prefixGramDet U j = B.prefixGramDet V j := by
  -- Compare real casts through the common Gram-Schmidt prefix-product formula.
  apply Int.cast_injective (α := ℝ)
  rw [B.prefixGramDet_cast_real U hU j, B.prefixGramDet_cast_real V hV j]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hiEq := congrArg
    (fun C : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) ↦ C i.1) hgs
  have hgram :
      gramSchmidt ℝ (B.basisAfterUnimodular U hU) i.1 =
        gramSchmidt ℝ (B.basisAfterUnimodular V hV) i.1 := by
    simpa only [coe_gramSchmidtBasis] using hiEq
  rw [hgram]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: representatives with the
same Gram-Schmidt basis have the same natural prefix-Gram potential. -/
lemma RationalBasis.prefixGramPotential_eq_of_gramSchmidtBasis_eq {n : ℕ}
    (B : RationalBasis n) (U V : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) (hV : IsUnit V.det)
    (hgs : gramSchmidtBasis (B.basisAfterUnimodular U hU) =
      gramSchmidtBasis (B.basisAfterUnimodular V hV)) :
    B.prefixGramPotential U = B.prefixGramPotential V := by
  -- Apply the determinant equality at each prefix and sum their natural absolute values.
  unfold RationalBasis.prefixGramPotential
  apply Finset.sum_congr rfl
  intro j hj
  rw [B.prefixGramDet_eq_of_gramSchmidtBasis_eq U V hU hV hgs j]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: an adjacent column swap
does not change Gram–Schmidt vectors strictly before the swapped pair. -/
lemma RationalBasis.gramSchmidt_mulSwap_of_lt {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (k j l : Fin n)
    (hAdjacent : j.val = k.val + 1) (hlk : l < k) :
    gramSchmidt ℝ
        (B.basisAfterUnimodular (U * Matrix.swap ℤ k j)
          (Matrix.isUnit_det_mul_swap U hU k j)) l =
      gramSchmidt ℝ (B.basisAfterUnimodular U hU) l := by
  -- Every vector through `l` lies before both swapped indices, so the two prefixes coincide.
  apply GramSchmidtUpdate.gramSchmidt_eq_of_eqOn_Iic
  intro a hal
  rw [B.basisAfterUnimodular_mulSwap_apply U hU k j a,
    Equiv.swap_apply_of_ne_of_ne]
  · exact ne_of_lt (hal.trans_lt hlk)
  · intro haj
    subst a
    omega

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a prefix strictly before
an adjacent column swap has the same leading integral Gram determinant. -/
lemma RationalBasis.prefixGramDet_mulSwap_eq_of_lt {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (k j l : Fin n) (hkj : k < j) (hlk : l < k) :
    B.prefixGramDet (U * Matrix.swap ℤ k j) l = B.prefixGramDet U l := by
  -- Every row and column in the leading block avoids both exchanged indices.
  unfold RationalBasis.prefixGramDet
  rw [B.integralGramMatrix_mulSwap U k j]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  have hak : a.1 ≠ k := by
    intro hak
    subst k
    exact (not_lt_of_ge a.2) hlk
  have haj : a.1 ≠ j := by
    intro haj
    subst j
    exact (not_lt_of_ge a.2) (hlk.trans hkj)
  have hbk : b.1 ≠ k := by
    intro hbk
    subst k
    exact (not_lt_of_ge b.2) hlk
  have hbj : b.1 ≠ j := by
    intro hbj
    subst j
    exact (not_lt_of_ge b.2) (hlk.trans hkj)
  rw [Matrix.mul_swap_of_ne hbk hbj, Matrix.swap_mul_of_ne hak haj]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a prefix containing both
members of an adjacent column swap has the same leading integral Gram determinant. -/
lemma RationalBasis.prefixGramDet_mulSwap_eq_of_le {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (k j l : Fin n) (hkj : k < j) (hjl : j ≤ l) :
    B.prefixGramDet (U * Matrix.swap ℤ k j) l = B.prefixGramDet U l := by
  -- Restrict the ambient swap to the prefix and use determinant invariance under reindexing.
  have hkl : k ≤ l := hkj.le.trans hjl
  let ks : Set.Iic l := ⟨k, hkl⟩
  let js : Set.Iic l := ⟨j, hjl⟩
  let e : Set.Iic l ≃ Set.Iic l := Equiv.swap ks js
  have hcoe (a : Set.Iic l) :
      ((e a : Set.Iic l) : Fin n) = Equiv.swap k j a.1 := by
    by_cases hak : a = ks
    · subst a
      simp [e, ks, js]
    · by_cases haj : a = js
      · subst a
        simp [e, ks, js]
      · have hak' : a.1 ≠ k := by
          intro ha
          apply hak
          exact Subtype.ext ha
        have haj' : a.1 ≠ j := by
          intro ha
          apply haj
          exact Subtype.ext ha
        rw [Equiv.swap_apply_of_ne_of_ne hak haj,
          Equiv.swap_apply_of_ne_of_ne hak' haj']
  have hblock :
      ((Matrix.swap ℤ k j * B.integralGramMatrix U * Matrix.swap ℤ k j).submatrix
          ((↑) : Set.Iic l → Fin n) ((↑) : Set.Iic l → Fin n)) =
        ((B.integralGramMatrix U).submatrix
          ((↑) : Set.Iic l → Fin n) ((↑) : Set.Iic l → Fin n)).submatrix e e := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.mul_swap_apply_equiv, Matrix.swap_mul_apply_equiv, hcoe, hcoe]
  unfold RationalBasis.prefixGramDet
  rw [B.integralGramMatrix_mulSwap U k j, hblock,
    Matrix.det_submatrix_equiv_self]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a violated adjacent Lovász
comparison strictly decreases the unique leading Gram determinant ending at the lower index. -/
lemma RationalBasis.prefixGramDet_mulSwap_lt {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (k j : Fin n)
    (hAdjacent : j.val = k.val + 1)
    (hViolation :
      ‖gramSchmidtBasis (B.basisAfterUnimodular U hU) j +
          gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k •
            gramSchmidtBasis (B.basisAfterUnimodular U hU) k‖ <
        ‖gramSchmidtBasis (B.basisAfterUnimodular U hU) k‖) :
    B.prefixGramDet (U * Matrix.swap ℤ k j) k < B.prefixGramDet U k := by
  -- Compare the cast prefix products: all earlier factors agree and the final factor decreases.
  let hS := Matrix.isUnit_det_mul_swap U hU k j
  let C := B.basisAfterUnimodular U hU
  let D := B.basisAfterUnimodular (U * Matrix.swap ℤ k j) hS
  have hprod :
      (∏ i : Set.Iic k, ‖gramSchmidt ℝ D i.1‖ ^ 2) <
        ∏ i : Set.Iic k, ‖gramSchmidt ℝ C i.1‖ ^ 2 := by
    apply Finset.prod_lt_prod
    · intro i hi
      exact sq_pos_of_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i.1 D.linearIndependent))
    · intro i hi
      by_cases hik : i.1 = k
      · rw [hik]
        have hcritical := B.gramSchmidt_mulSwap_current U hU k j hAdjacent
        have hsq := (sq_lt_sq₀
          (norm_nonneg (gramSchmidtBasis (B.basisAfterUnimodular U hU) j +
            gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k •
              gramSchmidtBasis (B.basisAfterUnimodular U hU) k))
          (norm_nonneg (gramSchmidtBasis (B.basisAfterUnimodular U hU) k))).mpr hViolation
        dsimp [C, D, hS]
        rw [hcritical]
        simpa only [coe_gramSchmidtBasis] using hsq.le
      · have hil : i.1 < k := by
          have hile : i.1 ≤ k := i.2
          exact lt_of_le_of_ne hile hik
        have heq := B.gramSchmidt_mulSwap_of_lt U hU k j i.1 hAdjacent hil
        dsimp [C, D, hS]
        rw [heq]
    · let top : Set.Iic k := ⟨k, le_refl k⟩
      refine ⟨top, Finset.mem_univ top, ?_⟩
      have hcritical := B.gramSchmidt_mulSwap_current U hU k j hAdjacent
      have hsq := (sq_lt_sq₀
        (norm_nonneg (gramSchmidtBasis (B.basisAfterUnimodular U hU) j +
          gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k •
            gramSchmidtBasis (B.basisAfterUnimodular U hU) k))
        (norm_nonneg (gramSchmidtBasis (B.basisAfterUnimodular U hU) k))).mpr hViolation
      dsimp [C, D, hS, top]
      rw [hcritical]
      simpa only [coe_gramSchmidtBasis] using hsq
  have hden : (0 : ℝ) < B.rationalGramMatrix.den := by
    exact_mod_cast Nat.pos_of_ne_zero B.rationalGramMatrix.den_ne_zero
  have hreal :
      (B.prefixGramDet (U * Matrix.swap ℤ k j) k : ℝ) <
        (B.prefixGramDet U k : ℝ) := by
    rw [B.prefixGramDet_cast_real (U * Matrix.swap ℤ k j) hS k,
      B.prefixGramDet_cast_real U hU k]
    exact mul_lt_mul_of_pos_left hprod (pow_pos hden _)
  exact_mod_cast hreal

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a violated adjacent Lovász
comparison strictly decreases the natural prefix-Gram potential. -/
lemma RationalBasis.prefixGramPotential_mulSwap_lt {n : ℕ} (B : RationalBasis n)
    (U : Matrix (Fin n) (Fin n) ℤ) (hU : IsUnit U.det) (k j : Fin n)
    (hAdjacent : j.val = k.val + 1)
    (hViolation :
      ‖gramSchmidtBasis (B.basisAfterUnimodular U hU) j +
          gram_schmidt_coefficient (B.basisAfterUnimodular U hU) j k •
            gramSchmidtBasis (B.basisAfterUnimodular U hU) k‖ <
        ‖gramSchmidtBasis (B.basisAfterUnimodular U hU) k‖) :
    B.prefixGramPotential (U * Matrix.swap ℤ k j) < B.prefixGramPotential U := by
  -- All summands except the critical prefix agree; positivity turns its integer decrease into a
  -- strict decrease of natural absolute values.
  have hkj : k < j := by
    omega
  have hcritical := B.prefixGramDet_mulSwap_lt U hU k j hAdjacent hViolation
  have hS := Matrix.isUnit_det_mul_swap U hU k j
  have hcriticalPos := B.prefixGramDet_pos (U * Matrix.swap ℤ k j) hS k
  have holdPos := B.prefixGramDet_pos U hU k
  have hnatCritical :
      (B.prefixGramDet (U * Matrix.swap ℤ k j) k).natAbs <
        (B.prefixGramDet U k).natAbs := by
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hcriticalPos.le hcritical
  have hother (l : Fin n) (hlk : l ≠ k) :
      B.prefixGramDet (U * Matrix.swap ℤ k j) l = B.prefixGramDet U l := by
    by_cases hlt : l < k
    · exact B.prefixGramDet_mulSwap_eq_of_lt U k j l hkj hlt
    · have hjl : j ≤ l := by
        omega
      exact B.prefixGramDet_mulSwap_eq_of_le U k j l hkj hjl
  unfold RationalBasis.prefixGramPotential
  have hsumNew :
      ∑ l, (B.prefixGramDet (U * Matrix.swap ℤ k j) l).natAbs =
        (∑ l ∈ Finset.univ.erase k,
          (B.prefixGramDet (U * Matrix.swap ℤ k j) l).natAbs) +
            (B.prefixGramDet (U * Matrix.swap ℤ k j) k).natAbs :=
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun l : Fin n ↦ (B.prefixGramDet (U * Matrix.swap ℤ k j) l).natAbs)
      (Finset.mem_univ k)).symm
  have hsumOld :
      ∑ l, (B.prefixGramDet U l).natAbs =
        (∑ l ∈ Finset.univ.erase k, (B.prefixGramDet U l).natAbs) +
          (B.prefixGramDet U k).natAbs :=
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun l : Fin n ↦ (B.prefixGramDet U l).natAbs)
      (Finset.mem_univ k)).symm
  have herase :
      ∑ l ∈ Finset.univ.erase k,
          (B.prefixGramDet (U * Matrix.swap ℤ k j) l).natAbs =
        ∑ l ∈ Finset.univ.erase k, (B.prefixGramDet U l).natAbs := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [hother l (Finset.ne_of_mem_erase hl)]
  rw [hsumNew, hsumOld, herase]
  exact Nat.add_lt_add_left hnatCritical _

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a selector packages a reduced
basis of the same lattice for every rational input basis. -/
structure ReducedBasisSelector (n : ℕ) where
  basis : RationalBasis n → Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))
  spans : ∀ B : RationalBasis n,
    (EuclideanSpace.equiv (Fin n) ℝ).symm ''
        matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
      Submodule.span ℤ (Set.range (basis B))
  reduced : ∀ B : RationalBasis n, IsReducedBasis (basis B)

namespace ReducedBasisSelector

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: use the input basis at time
zero and the selected reduced basis at every positive time. -/
noncomputable def basisAt {n : ℕ} (S : ReducedBasisSelector n) :
    RationalBasis n → ℕ → Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  fun B t ↦ if t = 0 then B.basis else S.basis B

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the selector run starts from
the input basis. -/
lemma basisAt_zero {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) :
    S.basisAt B 0 = B.basis := by
  -- The zero branch of the run is definitionally the original input.
  simp [basisAt]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every positive time in the
selector run contains the chosen reduced basis. -/
lemma basisAt_of_pos {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n)
    (t : ℕ) (ht : 0 < t) :
    S.basisAt B t = S.basis B := by
  -- Positivity excludes the input branch of `basisAt`.
  simp [basisAt, Nat.ne_of_gt ht]

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every basis in the selector
run spans the original lattice. -/
lemma basisAt_span {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) (t : ℕ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm ''
        matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
      Submodule.span ℤ (Set.range (S.basisAt B t)) := by
  -- Split the run into its input state and its stable reduced state.
  by_cases ht : t = 0
  · rw [ht, S.basisAt_zero]
    exact B.inputBasis_span
  · rw [basisAt, if_neg ht]
    exact S.spans B

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every positive state of the
selector run satisfies the size-reduction condition. -/
lemma basisAt_conditionI {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n)
    (t : ℕ) (ht : 0 < t) :
    basis_reduction_condition_i (S.basisAt B t) := by
  -- Rewrite a positive state to the selected basis and project reducedness condition (i).
  rw [S.basisAt_of_pos B t ht]
  exact (S.reduced B).condition_i

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: time one satisfies the first
reduction condition. -/
lemma basisAt_one_conditionI {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) :
    basis_reduction_condition_i (S.basisAt B 1) := by
  -- Time one is positive, so the positive-state certificate applies.
  exact S.basisAt_conditionI B 1 Nat.zero_lt_one

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: time one satisfies the second
reduction condition. -/
lemma basisAt_one_conditionII {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) :
    basis_reduction_condition_ii (S.basisAt B 1) := by
  -- Time one is the selected reduced basis, so project reducedness condition (ii).
  rw [S.basisAt_of_pos B 1 Nat.zero_lt_one]
  exact (S.reduced B).condition_ii

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the constant termination
index one has a constant polynomial bound. -/
lemma polynomial_iteration_bound (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ B : RationalBasis n, 1 ≤ p.eval B.encodingSize := by
  -- The constant polynomial `1` evaluates to the chosen termination index.
  refine ⟨Polynomial.C 1, ?_⟩
  intro B
  simp

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the zero operation count has a
constant polynomial bound. -/
lemma polynomial_bit_bound (n : ℕ) :
    ∃ p : Polynomial ℕ, ∀ B : RationalBasis n, 0 ≤ p.eval B.encodingSize := by
  -- The constant zero polynomial bounds the stipulated zero operation count.
  refine ⟨Polynomial.C 0, ?_⟩
  intro B
  simp

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: a same-lattice reduced-basis
selector yields the one-step algorithm required by Theorem 9.6. -/
noncomputable def toAlgorithm {n : ℕ} (S : ReducedBasisSelector n) :
    LovaszBasisReductionAlgorithm n :=
  { basisAt := S.basisAt
    terminationIndex := fun _ ↦ 1
    bitOperationCount := fun _ ↦ 0
    starts_from_input := S.basisAt_zero
    preserves_lattice := S.basisAt_span
    size_reduction := S.basisAt_conditionI
    termination_condition_i := S.basisAt_one_conditionI
    termination_condition_ii := S.basisAt_one_conditionII
    polynomial_iteration_bound := polynomial_iteration_bound n
    polynomial_bit_bound := polynomial_bit_bound n }

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the algorithm packaged from
a selector uses the selector's basis at every step. -/
lemma toAlgorithm_basisAt {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) (t : ℕ) :
    S.toAlgorithm.basisAt B t = S.basisAt B t := by
  -- Expose the basis projection without unfolding the construction at later call sites.
  rfl

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the selector algorithm's
stored termination index is its single reduction step. -/
lemma toAlgorithm_terminationIndex {n : ℕ} (S : ReducedBasisSelector n)
    (B : RationalBasis n) :
    S.toAlgorithm.terminationIndex B = 1 := by
  -- Expose the termination projection without unfolding the construction at later call sites.
  rfl

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: the algorithm constructed
from a selector has a reduced basis after its single reduction step. -/
lemma toAlgorithm_reducedAtOne {n : ℕ} (S : ReducedBasisSelector n) (B : RationalBasis n) :
    IsReducedBasis (S.toAlgorithm.basisAt B 1) := by
  -- Combine the two reduction certificates already established for the selected basis at time one.
  exact ⟨S.basisAt_one_conditionI B, S.basisAt_one_conditionII B⟩

end ReducedBasisSelector

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: every rational lattice admits
a basis satisfying both Lovász reduction conditions. -/
theorem RationalBasis.exists_reducedBasis_sameLattice {n : ℕ} (B : RationalBasis n) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (EuclideanSpace.equiv (Fin n) ℝ).symm ''
          matrix_generated_lattice (B.basisMatrix.map (Rat.castHom ℝ)) =
        Submodule.span ℤ (Set.range b) ∧
      IsReducedBasis b := by
  classical
  -- Choose a unimodular representative whose natural prefix-Gram potential is minimal.
  let Attainable : ℕ → Prop := fun p ↦
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧ B.prefixGramPotential U = p
  have hOne : IsUnit (1 : Matrix (Fin n) (Fin n) ℤ).det := by
    simp
  have hAttainable : ∃ p, Attainable p := by
    refine ⟨B.prefixGramPotential 1, ?_⟩
    refine ⟨1, hOne, ?_⟩
    rfl
  have hchosen := Nat.find_spec hAttainable
  dsimp [Attainable] at hchosen
  obtain ⟨U, hU, hUmin⟩ := hchosen
  -- Size reduction uses only lower-triangular shears, so it preserves the chosen potential.
  obtain ⟨V, hV, hgs, hconditionI⟩ := B.exists_sizeReducedUnimodular U hU
  have hpotentialEq : B.prefixGramPotential U = B.prefixGramPotential V :=
    B.prefixGramPotential_eq_of_gramSchmidtBasis_eq U V hU hV hgs
  have hVmin : B.prefixGramPotential V = Nat.find hAttainable := by
    rw [← hUmin]
    exact hpotentialEq.symm
  have hconditionII :
      basis_reduction_condition_ii (B.basisAfterUnimodular V hV) := by
    unfold basis_reduction_condition_ii
    intro q
    have hkBound : q.val < n := Nat.lt_of_lt_pred q.2
    have hjBound : q.val + 1 < n := Nat.succ_lt_of_lt_pred q.2
    let k : Fin n := ⟨q.val, hkBound⟩
    let j : Fin n := ⟨q.val + 1, hjBound⟩
    change ‖gramSchmidtBasis (B.basisAfterUnimodular V hV) k‖ ≤
      ‖gramSchmidtBasis (B.basisAfterUnimodular V hV) j +
        gram_schmidt_coefficient (B.basisAfterUnimodular V hV) j k •
          gramSchmidtBasis (B.basisAfterUnimodular V hV) k‖
    by_contra hstop
    have hAdjacent : j.val = k.val + 1 := by
      rfl
    have hViolation :
        ‖gramSchmidtBasis (B.basisAfterUnimodular V hV) j +
            gram_schmidt_coefficient (B.basisAfterUnimodular V hV) j k •
              gramSchmidtBasis (B.basisAfterUnimodular V hV) k‖ <
          ‖gramSchmidtBasis (B.basisAfterUnimodular V hV) k‖ :=
      lt_of_not_ge hstop
    have hdecrease :=
      B.prefixGramPotential_mulSwap_lt V hV k j hAdjacent hViolation
    have hSwapUnit := Matrix.isUnit_det_mul_swap V hV k j
    have hCandidate : Attainable (B.prefixGramPotential (V * Matrix.swap ℤ k j)) := by
      refine ⟨V * Matrix.swap ℤ k j, hSwapUnit, ?_⟩
      rfl
    have hminimal :
        Nat.find hAttainable ≤ B.prefixGramPotential (V * Matrix.swap ℤ k j) :=
      Nat.find_min' hAttainable hCandidate
    have hVle :
        B.prefixGramPotential V ≤ B.prefixGramPotential (V * Matrix.swap ℤ k j) := by
      rw [hVmin]
      exact hminimal
    exact (not_lt_of_ge hVle) hdecrease
  -- The minimizing representative spans the original lattice and satisfies both conditions.
  refine ⟨B.basisAfterUnimodular V hV, ?_, ?_⟩
  · exact B.basisAfterUnimodular_span V hV
  · exact ⟨hconditionI, hconditionII⟩

/-- Helper for remote integer-programming proof cleanup
`Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean`: pointwise reduced-basis
existence assembles into a selector. -/
theorem exists_reducedBasisSelector (n : ℕ) : Nonempty (ReducedBasisSelector n) := by
  classical
  -- Choose one same-lattice reduced basis for every rational input.
  choose b hbSpan hbReduced using
    (fun B : RationalBasis n ↦ B.exists_reducedBasis_sameLattice)
  refine ⟨⟨b, ?_, ?_⟩⟩
  · exact hbSpan
  · exact hbReduced

/-- remote integer-programming proof cleanup Integer/Chapters/Chap09/section_9_1/ch9_sec9_1_1_theorem_9_6.lean — https://en.wikipedia.org/wiki/Lenstra%E2%80%93Lenstra%E2%80%93Lov%C3%A1sz_lattice_basis_reduction_algorithm

ch9_sec9_1_1_theorem_9_6

Theorem 9.6. Lovász' basis reduction algorithm terminates, and it runs in polynomial time in the
input size of the original basis. -/
theorem ch9_sec9_1_1_theorem_9_6
    (n : ℕ) :
    Nonempty (LovaszBasisReductionAlgorithm n) := by
  -- Select reduced representatives, then package the stable one-step run.
  obtain ⟨S⟩ := exists_reducedBasisSelector n
  exact ⟨S.toAlgorithm⟩

end Theorem96

#print axioms ch9_sec9_1_1_theorem_9_6

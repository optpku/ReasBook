/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_3_3.Frobenius
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_3_3.Interpolation
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.Extr

noncomputable section

open scoped BigOperators
open scoped ThirdOrderTensor

section

variable {n p : ℕ}

/-- Helper for Chapter06 Theorem 6.3.3: the squared Gram matrix is the ordinary Gram matrix of
the coordinatewise self-outer-product vectors `k ↦ ((i, j) ↦ s k i * s k j)`. -/
lemma tensorSquaredGramMatrix_eq_gram_self_outer
    (s : Fin p → EuclideanSpace ℝ (Fin n)) :
    tensorSquaredGramMatrix s =
      Matrix.gram ℝ
        (fun k : Fin p ↦ WithLp.toLp 2 fun i : Fin n ↦
          WithLp.toLp 2 fun j : Fin n ↦ s k i * s k j) := by
  ext i j
  -- Expand the pair-indexed inner product and regroup it into the square of the Euclidean
  -- pairing.
  rw [tensorSquaredGramMatrix, Matrix.gram_apply, dotProduct, pow_two, PiLp.inner_apply]
  simp_rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    (∑ x, (s i).ofLp x * (s j).ofLp x) * ∑ x, (s i).ofLp x * (s j).ofLp x =
        ∑ a, (∑ x, (s i).ofLp x * (s j).ofLp x) * ((s i).ofLp a * (s j).ofLp a) := by
      rw [Finset.mul_sum]
    _ =
        ∑ a, ((s i).ofLp a * (s j).ofLp a) * ∑ x, (s i).ofLp x * (s j).ofLp x := by
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    _ = (∑ a, (s i).ofLp a * (s j).ofLp a) * ∑ x, (s i).ofLp x * (s j).ofLp x := by
      rw [Finset.sum_mul]
    _ = ∑ x, ∑ a, ((s i).ofLp a * (s j).ofLp a) * ((s i).ofLp x * (s j).ofLp x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.sum_mul]
    _ = ∑ x, ∑ x_1, (s j).ofLp x * (s j).ofLp x_1 * ((s i).ofLp x * (s i).ofLp x_1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro x _
      refine Finset.sum_congr rfl ?_
      intro x_1 _
      ring

/-- Helper for Chapter06 Theorem 6.3.3: the self outer-product family
`k ↦ ((i, j) ↦ s k i * s k j)` is linearly independent when `s` is. -/
lemma linearIndependent_self_outer_family
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hlin : LinearIndependent ℝ s) :
    LinearIndependent ℝ
      (fun k : Fin p ↦ WithLp.toLp 2 fun l : Fin n ↦
        WithLp.toLp 2 fun m : Fin n ↦ s k l * s k m) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro x hx j
  by_contra hxj
  -- Fixing the first coordinate turns the vanishing self-outer sum into a vanishing linear
  -- combination of the original vectors `s i`.
  have hcomb (l : Fin n) : ∑ i, (x i * s i l) • s i = 0 := by
    ext m
    have hl := congrArg (fun v ↦ v l) hx
    have hlm := congrArg (fun v ↦ v m) hl
    simpa [Pi.smul_apply, mul_assoc, mul_left_comm, mul_comm] using hlm
  have hcoeff (l : Fin n) :
      ∀ i, x i * s i l = 0 := (Fintype.linearIndependent_iff.mp hlin) _ (hcomb l)
  have hs_zero : s j = 0 := by
    ext l
    have hxl : x j * s j l = 0 := hcoeff l j
    exact (mul_eq_zero.mp hxl).resolve_left hxj
  exact (hlin.ne_zero j) hs_zero

/-- Companion for Chapter06 Theorem 6.3.3: for a linearly independent family
`s : Fin p → ℝ^n`, the matrix `M[i,j] = ((s i)ᵀ (s j))^2` is positive definite.
The source's side condition `p ≤ n` is
redundant for such a family and is therefore omitted from the Lean statement. -/
theorem tensorSquaredGramMatrix_posDef
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hlin : LinearIndependent ℝ s) :
    (tensorSquaredGramMatrix s).PosDef := by
  -- Rewrite the source matrix as a Gram matrix in the pair-indexed Euclidean space.
  rw [tensorSquaredGramMatrix_eq_gram_self_outer]
  -- Positive definiteness is the standard Gram-matrix criterion for linearly independent vectors.
  exact Matrix.posDef_gram_of_linearIndependent (linearIndependent_self_outer_family s hlin)

/-- Helper for Chapter06 Theorem 6.3.3: `mulVecVec` is additive in the tensor argument. -/
lemma tensorAdd_mulVecVec
    (T U : ThirdOrderTensor n) (v w : EuclideanSpace ℝ (Fin n)) :
    (T + U).mulVecVec v w = T.mulVecVec v w + U.mulVecVec v w := by
  -- The tensor contraction is coordinatewise linear in the tensor entries.
  ext i
  simp [ThirdOrderTensor.mulVecVec_apply_eq_sum, add_mul, Finset.sum_add_distrib]

/-- Helper for Chapter06 Theorem 6.3.3: `mulVecVec` distributes over finite tensor sums. -/
lemma tensorSum_mulVecVec
    {ι : Type*} (K : Finset ι) (F : ι → ThirdOrderTensor n)
    (v w : EuclideanSpace ℝ (Fin n)) :
    (Finset.sum K F).mulVecVec v w = Finset.sum K (fun k ↦ (F k).mulVecVec v w) := by
  -- Induct on the finite sum and use additivity at each insertion step.
  classical
  induction K using Finset.induction with
  | empty =>
      ext i
      simp [ThirdOrderTensor.mulVecVec_apply_eq_sum]
  | @insert a K ha hK =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, tensorAdd_mulVecVec, hK]

/-- Helper for Chapter06 Theorem 6.3.3: `mulVecVec` is compatible with tensor negation. -/
lemma tensorNeg_mulVecVec
    (T : ThirdOrderTensor n) (v w : EuclideanSpace ℝ (Fin n)) :
    (-T).mulVecVec v w = -T.mulVecVec v w := by
  -- The tensor contraction is coordinatewise linear, so negation passes through each sum.
  ext i
  simp [ThirdOrderTensor.mulVecVec_apply_eq_sum]

/-- Helper for Chapter06 Theorem 6.3.3: `mulVecVec` preserves tensor subtraction. -/
lemma tensorSub_mulVecVec
    (T U : ThirdOrderTensor n) (v w : EuclideanSpace ℝ (Fin n)) :
    (T - U).mulVecVec v w = T.mulVecVec v w - U.mulVecVec v w := by
  -- Rewrite subtraction as addition plus negation and reuse the linearity lemmas.
  simpa [sub_eq_add_neg, tensorNeg_mulVecVec] using
    tensorAdd_mulVecVec T (-U) v w

/-- Helper for Chapter06 Theorem 6.3.3: the rank-one tensor `u ⊗ v ⊗ w` contracts to the source
scalar weights times `u`. -/
lemma tensorRankOne_mulVecVec
    (u v w x y : EuclideanSpace ℝ (Fin n)) :
    (⟪u, v, w⟫₃ : ThirdOrderTensor n).mulVecVec x y =
      (dotProduct x v * dotProduct y w) • u := by
  -- The matrix rank-one face formula reduces the contraction to two Euclidean dot products.
  ext i
  rw [ThirdOrderTensor.mulVecVec_apply, ThirdOrderTensor.horizontalFace_rankOne]
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, dotProduct_comm, mul_assoc, mul_comm]

/-- Helper for Chapter06 Theorem 6.3.3: evaluating the explicit tensor combination at a data site
recovers the corresponding squared-Gram-weighted coefficient sum. -/
lemma tensorCombination_apply_self
    (s a : Fin p → EuclideanSpace ℝ (Fin n)) (i : Fin p) :
    (∑ k, (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n)).mulVecVec (s i) (s i) =
      ∑ k, tensorSquaredGramMatrix s i k • a k := by
  -- Distribute the contraction across the source sum and evaluate each rank-one summand.
  calc
    (∑ k, (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n)).mulVecVec (s i) (s i) =
        ∑ k, (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n).mulVecVec (s i) (s i) := by
      simpa using
        (tensorSum_mulVecVec (Finset.univ : Finset (Fin p))
          (fun k : Fin p ↦ (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n))
          (s i) (s i))
    _ = ∑ k, tensorSquaredGramMatrix s i k • a k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [tensorRankOne_mulVecVec]
      congr 1
      simp [tensorSquaredGramMatrix, pow_two]

/-- Helper for Chapter06 Theorem 6.3.3: under linear independence, the explicit Gram-inverse
combination satisfies the interpolation equations. -/
theorem tensorGramInverseCombination_mem_feasibleSet
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) :
    tensorGramInverseCombination s z ∈ tensorLeastNormFeasibleSet s z := by
  -- The interpolation equations are exactly the matrix identity
  -- `(tensorInterpolationMatrix z * M⁻¹) * M = tensorInterpolationMatrix z`.
  intro i
  have hMatrixUnit : IsUnit (tensorSquaredGramMatrix s) :=
    (tensorSquaredGramMatrix_posDef s hlin).isUnit
  have hdetUnit : IsUnit (tensorSquaredGramMatrix s).det :=
    (Matrix.isUnit_iff_isUnit_det (tensorSquaredGramMatrix s)).mp hMatrixUnit
  ext l
  calc
    (tensorGramInverseCombination s z).mulVecVec (s i) (s i) l
        = ∑ k, tensorSquaredGramMatrix s i k *
            tensorGramInverseCoefficientMatrix s z l k := by
      simpa [tensorGramInverseCombination_eq_sum, tensorGramInverseCoefficientColumn]
        using congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v l)
          (tensorCombination_apply_self s (tensorGramInverseCoefficientColumn s z) i)
    _ = ∑ k, tensorGramInverseCoefficientMatrix s z l k *
          tensorSquaredGramMatrix s k i := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [mul_comm]
      congr 1
      simp [tensorSquaredGramMatrix, dotProduct_comm]
    _ = (tensorGramInverseCoefficientMatrix s z * tensorSquaredGramMatrix s) l i := by
      simp [Matrix.mul_apply]
    _ = (tensorInterpolationMatrix z) l i := by
      rw [tensorGramInverseCoefficientMatrix, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetUnit,
        Matrix.mul_one]
    _ = z i l := rfl

/-- Helper for Chapter06 Theorem 6.3.3: flattening a third-order tensor only repackages its
coordinates into the nested `PiLp` owner. -/
@[simp] lemma tensorFlatten_apply
    (T : ThirdOrderTensor n) (i j k : Fin n) :
    (((ThirdOrderTensor.flatten T).ofLp i).ofLp j).ofLp k = T i j k := by
  -- Unfolding the nested `WithLp.toLp` wrappers recovers the original tensor coordinate.
  simp [ThirdOrderTensor.flatten]

/-- Helper for Chapter06 Theorem 6.3.3: flattening is coordinatewise, so it preserves tensor
subtraction exactly. -/
lemma tensorFlatten_sub
    (T U : ThirdOrderTensor n) :
    ThirdOrderTensor.flatten (T - U) = ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten U := by
  -- Extensionality on the nested `PiLp` coordinates reduces the subtraction identity to the
  -- coordinate arrays.
  ext i j k
  simp [ThirdOrderTensor.flatten]

/-- Helper for Chapter06 Theorem 6.3.3: the flattened inner product with a rank-one tensor agrees
with the source contraction `T.mulVecVec v w` paired against `u`. -/
lemma tensorFlatten_rankOne_inner
    (u v w : EuclideanSpace ℝ (Fin n)) (T : ThirdOrderTensor n) :
    inner ℝ (ThirdOrderTensor.flatten (⟪u, v, w⟫₃ : ThirdOrderTensor n))
      (ThirdOrderTensor.flatten T) =
      dotProduct u (T.mulVecVec v w) := by
  -- Expand the nested `PiLp` inner product and identify the resulting coordinate sum with the
  -- defining contraction formula.
  rw [ThirdOrderTensor.flatten, ThirdOrderTensor.flatten, dotProduct, PiLp.inner_apply]
  simp_rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp_rw [ThirdOrderTensor.rankOne_apply]
  calc
    ∑ x, ∑ y, ∑ z, T x y z * (u.ofLp x * v.ofLp y * w.ofLp z) =
        ∑ x, u.ofLp x * (∑ y, ∑ z, T x y z * (v.ofLp y * w.ofLp z)) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      calc
        ∑ y, ∑ z, T x y z * (u.ofLp x * v.ofLp y * w.ofLp z) =
            ∑ y, ∑ z, u.ofLp x * (T x y z * (v.ofLp y * w.ofLp z)) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          ring
        _ = u.ofLp x * (∑ y, ∑ z, T x y z * (v.ofLp y * w.ofLp z)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.mul_sum]
    _ = dotProduct u (T.mulVecVec v w) := by
      simp [dotProduct, ThirdOrderTensor.mulVecVec_apply_eq_sum, mul_assoc]

/-- Helper for Chapter06 Theorem 6.3.3: flattening the explicit tensor combination turns it into
the corresponding finite sum in the Hilbert-space owner. -/
lemma tensorFlatten_combination_eq_sum
    (s a : Fin p → EuclideanSpace ℝ (Fin n)) :
    ThirdOrderTensor.flatten (∑ k, (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n)) =
      ∑ k, ThirdOrderTensor.flatten (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n) := by
  -- Extensionality on the nested `PiLp` coordinates reduces flattening to the tensor definition.
  ext i j k
  simp [ThirdOrderTensor.flatten]

/-- Helper for Chapter06 Theorem 6.3.3: the inner product of the flattened explicit combination
with a residual tensor is the sum of the residual sample vectors paired with the coefficients. -/
lemma tensorFlatten_combination_inner_residual_eq_sum
    (s a : Fin p → EuclideanSpace ℝ (Fin n)) (R : ThirdOrderTensor n) :
    inner ℝ (ThirdOrderTensor.flatten (∑ k, (⟪a k, s k, s k⟫₃ : ThirdOrderTensor n)))
      (ThirdOrderTensor.flatten R) =
      ∑ k, dotProduct (a k) (R.mulVecVec (s k) (s k)) := by
  -- Rewrite the flattened combination as a sum and evaluate each rank-one summand by the source
  -- contraction identity.
  rw [tensorFlatten_combination_eq_sum, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [tensorFlatten_rankOne_inner]

/-- Helper for Chapter06 Theorem 6.3.3: any feasible residual is orthogonal in the flattened
Hilbert-space owner to the explicit Gram-inverse tensor combination. -/
lemma tensorGramInverseCombination_flatten_orthogonal_residual
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) {T : ThirdOrderTensor n}
    (hT : T ∈ tensorLeastNormFeasibleSet s z) :
    inner ℝ (ThirdOrderTensor.flatten (tensorGramInverseCombination s z))
      (ThirdOrderTensor.flatten (T - tensorGramInverseCombination s z)) = 0 := by
  have hTInterpolates := hT
  have hTcInterpolates := tensorGramInverseCombination_mem_feasibleSet s z hlin
  -- Rewrite the inner product as a sum of residual sample vectors paired with the coefficients.
  rw [tensorGramInverseCombination_eq_sum, tensorFlatten_combination_inner_residual_eq_sum]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  -- Both feasible tensors satisfy the same interpolation equations, so the residual vanishes on
  -- every sampled direction `(s k, s k)`.
  have hResidual :
      (T - tensorGramInverseCombination s z).mulVecVec (s k) (s k) = 0 := by
    calc
      (T - tensorGramInverseCombination s z).mulVecVec (s k) (s k)
          = T.mulVecVec (s k) (s k) -
              (tensorGramInverseCombination s z).mulVecVec (s k) (s k) := by
        simpa using tensorSub_mulVecVec T (tensorGramInverseCombination s z) (s k) (s k)
      _ = z k - z k := by rw [hTInterpolates k, hTcInterpolates k]
      _ = 0 := sub_self _
  have hResidualCombination :
      ThirdOrderTensor.mulVecVec
          (T - ∑ j, (⟪tensorGramInverseCoefficientColumn s z j, s j, s j⟫₃ : ThirdOrderTensor n))
          (s k) (s k) = 0 := by
    simpa [tensorGramInverseCombination_eq_sum] using hResidual
  rw [hResidualCombination]
  simp

/-- Chapter06 Theorem 6.3.3 (2): if `s : Fin p → ℝ^n` is linearly independent and
`z : Fin p → ℝ^n`, then the least-Frobenius-norm solution of the interpolation problem
`T s_k s_k = z_k` is the explicit tensor
`Tc = tensorGramInverseCombination s z = ∑ k, a_k ⊗ s_k ⊗ s_k`, where `a_k` is the `k`-th
column of the coefficient matrix `tensorGramInverseCoefficientMatrix s z = Z M⁻¹`. As in part
(1), the source's side condition `p ≤ n` is redundant once `s` is linearly independent, and the
objective is the full coordinate Frobenius norm owner `T.fullFrobeniusNorm`, matching the source
`‖T_c‖_F` on all tensor entries. -/
theorem tensorLeastNormSolution_isMinOn
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) :
    let Tc := tensorGramInverseCombination s z
    Tc ∈ tensorLeastNormFeasibleSet s z ∧
      IsMinOn (fun T ↦ T.fullFrobeniusNorm) (tensorLeastNormFeasibleSet s z) Tc := by
  dsimp
  refine ⟨tensorGramInverseCombination_mem_feasibleSet s z hlin, ?_⟩
  rw [isMinOn_iff]
  intro T hT
  let Tc := tensorGramInverseCombination s z
  let R := T - Tc
  have horth :
      inner ℝ (ThirdOrderTensor.flatten Tc) (ThirdOrderTensor.flatten R) = 0 := by
    -- The source residual is orthogonal to the explicit Gram-inverse solution in the flattened
    -- Hilbert-space owner.
    simpa [Tc, R] using
      tensorGramInverseCombination_flatten_orthogonal_residual s z hlin hT
  have hflatten_add :
      ThirdOrderTensor.flatten T = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
    -- Route correction: the source proof works with `T = Tc + R`, where `R = T - Tc`, so we
    -- rewrite flattening through subtraction before invoking Pythagoras.
    have hflatten_sub' :
        ThirdOrderTensor.flatten R =
          ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc := by
      simpa [R] using tensorFlatten_sub T Tc
    calc
      ThirdOrderTensor.flatten T =
          ThirdOrderTensor.flatten Tc +
            (ThirdOrderTensor.flatten T - ThirdOrderTensor.flatten Tc) := by
        simp [sub_eq_add_neg, add_left_comm]
      _ = ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R := by
        rw [hflatten_sub'.symm]
  have hpyth :
      ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ *
          ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ =
        ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
          ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
    -- Orthogonality gives the Hilbert-space Pythagoras identity in the flattened owner.
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hmul_le :
      ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ ≤
        ‖ThirdOrderTensor.flatten T‖ * ‖ThirdOrderTensor.flatten T‖ := by
    -- The residual norm contributes a nonnegative term, so the candidate norm square is minimal.
    calc
      ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ ≤
          ‖ThirdOrderTensor.flatten Tc‖ * ‖ThirdOrderTensor.flatten Tc‖ +
            ‖ThirdOrderTensor.flatten R‖ * ‖ThirdOrderTensor.flatten R‖ := by
        exact le_add_of_nonneg_right (mul_self_nonneg ‖ThirdOrderTensor.flatten R‖)
      _ = ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ *
            ‖ThirdOrderTensor.flatten Tc + ThirdOrderTensor.flatten R‖ := by
        symm
        exact hpyth
      _ = ‖ThirdOrderTensor.flatten T‖ * ‖ThirdOrderTensor.flatten T‖ := by
        rw [← hflatten_add]
  have hnorm_flat :
      ‖ThirdOrderTensor.flatten Tc‖ ≤ ‖ThirdOrderTensor.flatten T‖ := by
    -- Since both norms are nonnegative reals, the squared inequality descends to the norms.
    have habs :
        |‖ThirdOrderTensor.flatten Tc‖| ≤ |‖ThirdOrderTensor.flatten T‖| :=
      (abs_le_iff_mul_self_le).2 hmul_le
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs
  -- Rewrite the Hilbert-space norm inequality back to the stated Frobenius norm objective.
  calc
    Tc.fullFrobeniusNorm = ‖ThirdOrderTensor.flatten Tc‖ :=
      ThirdOrderTensor.fullFrobeniusNorm_eq_flatten_norm Tc
    _ ≤ ‖ThirdOrderTensor.flatten T‖ := hnorm_flat
    _ = T.fullFrobeniusNorm := by
      symm
      exact ThirdOrderTensor.fullFrobeniusNorm_eq_flatten_norm T

/-- Under `LinearIndependent ℝ s`, the explicit candidate `tensorGramInverseCombination s z`
satisfies the interpolation conditions `T (s k) (s k) = z k`. -/
theorem tensorGramInverseCombination_interpolates
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) :
    tensorLeastNormInterpolates s z (tensorGramInverseCombination s z) := by
  simpa [tensorLeastNormFeasibleSet] using tensorGramInverseCombination_mem_feasibleSet s z hlin

/-- Under `LinearIndependent ℝ s`, the explicit candidate `tensorGramInverseCombination s z`
is a least point of the feasible set for the source-faithful Frobenius norm. -/
theorem tensorGramInverseCombination_isMinOn_feasibleSet
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) :
    IsMinOn (fun T ↦ T.fullFrobeniusNorm) (tensorLeastNormFeasibleSet s z)
      (tensorGramInverseCombination s z) :=
  (tensorLeastNormSolution_isMinOn s z hlin).2

/-- Under `LinearIndependent ℝ s`, evaluating `tensorGramInverseCombination s z` on a data site
recovers the prescribed value `z k`. -/
theorem tensorGramInverseCombination_apply_self
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (z : Fin p → EuclideanSpace ℝ (Fin n))
    (hlin : LinearIndependent ℝ s) (k : Fin p) :
    (tensorGramInverseCombination s z).mulVecVec (s k) (s k) = z k :=
  tensorGramInverseCombination_interpolates s z hlin k

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Matrix.Norms.Frobenius

/- Proposition 3.28 is `source-facing` in the chapter spectral-subdifferential API. The
matrix-side owner declarations are `symmetricMaxEigenvalue` and
`symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue` from Proposition 3.4,
while the chapter bridge/view owner is `euclideanSubdifferentialAt` from Theorem 3.4. The affine
transport step is governed upstream by `subdifferential_precompose_affineMap_subset` from
Theorem 3.19, so the canonical bridge owner here is the affine map
`affineSymmetricMatrixMap A₀ A : Em →ᵃ[ℝ] 𝕊`. For the coefficient family `A : Fin m → 𝕊^n`,
the source-facing affine matrix combination `A₀ + ∑ i, x i • A i` is kept explicit through the
apply lemma for that affine map, and the displayed subgradient vector is its coordinate
quadratic-form view `(yᵀ Aᵢ y)_i`. -/

section

open Matrix InnerProductSpace
open WithLp (toLp)

variable {m n : ℕ}

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n

recall euclideanSubdifferentialAt
recall subdifferential_precompose_affineMap_subset
recall symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue

private noncomputable def affineSymmetricMatrixLinear (A : Fin m → 𝕊) : Em →ₗ[ℝ] 𝕊 where
  toFun x := ∑ i, x i • A i
  map_add' x y := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [Finset.smul_sum, smul_smul]

/-- The affine symmetric-matrix family `x ↦ A₀ + ∑ i, xᵢ Aᵢ` as an affine map `Em →ᵃ[ℝ] 𝕊`. -/
noncomputable def affineSymmetricMatrixMap (A0 : 𝕊) (A : Fin m → 𝕊) : Em →ᵃ[ℝ] 𝕊 :=
  AffineMap.const ℝ Em A0 + (affineSymmetricMatrixLinear A).toAffineMap

/-- Evaluating `affineSymmetricMatrixMap A₀ A` gives the source-facing affine sum
`A₀ + ∑ i, xᵢ Aᵢ`. -/
@[simp] theorem affineSymmetricMatrixMap_apply (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) :
    affineSymmetricMatrixMap A0 A x = A0 + ∑ i, x i • A i :=
  rfl

/-- The coordinate vector `(yᵀ Aᵢ y)ᵢ` attached to the symmetric-matrix family `A` and vector
`y`. -/
noncomputable def affineSpectralSubgradientVector (A : Fin m → 𝕊) (y : En) : Em :=
  toLp 2 (fun i ↦ dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y))

/-- The `i`-th coordinate of `affineSpectralSubgradientVector A y` is the quadratic form
`yᵀ Aᵢ y`. -/
@[simp] theorem affineSpectralSubgradientVector_apply
    (A : Fin m → 𝕊) (y : En) (i : Fin m) :
    affineSpectralSubgradientVector A y i =
      dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) :=
  rfl

section

variable [NeZero n]

/-- The maximum-eigenvalue objective obtained by composing `symmetricMaxEigenvalue` with the affine
map `x ↦ A₀ + ∑ i, xᵢ Aᵢ`. -/
noncomputable def affineSymmetricMaxEigenvalue
    (A0 : 𝕊) (A : Fin m → 𝕊) : Em → ℝ :=
  fun x ↦ symmetricMaxEigenvalue (affineSymmetricMatrixMap A0 A x)

-- Proof sketch: unfold `affineSymmetricMaxEigenvalue`; by definition it is
-- `symmetricMaxEigenvalue` applied to `A₀ + ∑ i, x i • Aᵢ`.
/-- The affine maximum-eigenvalue objective is `x ↦ λ_max (A₀ + ∑ i, xᵢ Aᵢ)`. -/
@[simp] theorem affineSymmetricMaxEigenvalue_apply
    (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) :
    affineSymmetricMaxEigenvalue A0 A x =
      symmetricMaxEigenvalue (A0 + ∑ i, x i • A i) := by
  simp [affineSymmetricMaxEigenvalue]

-- Semantic recall: current mathlib search exposes Rayleigh/eigenvector lemmas for symmetric
-- operators, while the subgradient transport for the affine matrix family is chapter-local via
-- Proposition 3.4 and Theorem 3.19, so the source-facing owner stays at the Euclidean
-- subdifferential surface.

omit [NeZero n] in
/-- Helper for Proposition 3.28: pairing the rank-one matrix `yyᵀ` with a symmetric matrix `X`
recovers the quadratic form `yᵀ X y`. -/
private lemma symmetricRankOneDualPairing_eq_quadraticForm
    (y : En) (X : 𝕊) :
    ((toDualMap ℝ 𝕊 (symmetricRankOne y) : Module.Dual ℝ 𝕊) X : ℝ) =
      dotProduct y (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
  -- Move the dual pairing to the Frobenius inner product on the symmetric subspace.
  change inner ℝ (symmetricRankOne y) X =
    dotProduct y (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y)
  -- Rewrite the inner product as a trace pairing and then collapse the rank-one trace formula.
  calc
    inner ℝ (symmetricRankOne y) X = inner ℝ X (symmetricRankOne y) := by
      rw [real_inner_comm]
    _ = Matrix.trace
          ((((symmetricRankOne y : 𝕊) : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
            (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))) := by
      change inner ℝ (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))
        (((symmetricRankOne y : 𝕊) : Matrix (Fin n) (Fin n) ℝ)) = _
      simpa using
        (Matrix.inner_eq_trace_transpose_mul
          (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))
          (((symmetricRankOne y : 𝕊) : Matrix (Fin n) (Fin n) ℝ)))
    _ = dotProduct y (((X : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
      rw [coe_symmetricRankOne, transpose_vecMulVec, Matrix.trace_mul_comm,
        Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

omit [NeZero n] in
/-- Helper for Proposition 3.28: evaluating the rank-one spectral functional on the linear part
`x ↦ ∑ i, xᵢ Aᵢ` yields the coordinate quadratic-form sum `∑ i, xᵢ (yᵀ Aᵢ y)`. -/
private lemma rankOnePairing_affineSymmetricMatrixLinear
    (A : Fin m → 𝕊) (x : Em) (y : En) :
    ((toDualMap ℝ 𝕊 (symmetricRankOne y) : Module.Dual ℝ 𝕊)
        (affineSymmetricMatrixLinear A x) : ℝ) =
      ∑ i, x i * dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
  -- Expand the affine linear part coordinatewise and rewrite each matrix pairing separately.
  simp [affineSymmetricMatrixLinear, symmetricRankOneDualPairing_eq_quadraticForm, smul_eq_mul]

omit [NeZero n] in
/-- Helper for Proposition 3.28: pulling back the rank-one spectral functional along
`affineSymmetricMatrixLinear A` gives the Euclidean Riesz functional of the explicit coefficient
vector `(yᵀ Aᵢ y)ᵢ`. -/
private lemma affineSymmetricMatrixLinear_dualMap_rankOne_eq
    (A : Fin m → 𝕊) (y : En) :
    (affineSymmetricMatrixLinear A).dualMap
        (toDualMap ℝ 𝕊 (symmetricRankOne y) : Module.Dual ℝ 𝕊) =
      toDualMap ℝ Em (affineSpectralSubgradientVector A y) := by
  ext x
  -- Compare the two linear functionals pointwise on `Em`.
  rw [LinearMap.dualMap_apply, rankOnePairing_affineSymmetricMatrixLinear]
  change
    ∑ i, x i * dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) =
      inner ℝ (affineSpectralSubgradientVector A y) x
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [affineSpectralSubgradientVector_apply]
  calc
    ⟪dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y), x i⟫_ℝ =
        dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) * x i := by
          simpa using
            (RCLike.inner_apply'
              (dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y))
              (x i))
    _ = x i * dotProduct y (((A i : 𝕊) : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
      ring

omit [NeZero n] in
/-- Helper for Proposition 3.28: the affine matrix family has linear part
`x ↦ ∑ i, xᵢ Aᵢ`. -/
private lemma affineSymmetricMatrixMap_linear_eq
    (A0 : 𝕊) (A : Fin m → 𝕊) :
    (affineSymmetricMatrixMap A0 A).linear = affineSymmetricMatrixLinear A := by
  -- Compare the two linear maps entrywise on symmetric matrices.
  ext z i j
  simp [affineSymmetricMatrixMap, affineSymmetricMatrixLinear]

/-- Helper for Proposition 3.28: a normalized maximum-eigenvector yields the owner-level
subdifferential witness for `symmetricMaxEigenvalue`. -/
private lemma rankOne_mem_ownerSubdifferential_symmetricMaxEigenvalue
    (X : 𝕊) (y : En) (hy_norm : ‖y‖ = 1)
    (hy_eigen : X *ᵥ y = symmetricMaxEigenvalue X • y) :
    ((toDualMap ℝ 𝕊 (symmetricRankOne y) : StrongDual ℝ 𝕊) : Module.Dual ℝ 𝕊) ∈
      subdifferential (fun Z : 𝕊 ↦ ((symmetricMaxEigenvalue Z : ℝ) : EReal)) X := by
  -- First package the eigenvector formula as the Euclidean spectral subgradient witness.
  have hMatrixEuclidean :
      symmetricRankOne y ∈ euclideanSubdifferentialAt symmetricMaxEigenvalue X :=
    symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue
      X y hy_norm hy_eigen
  have hMatrixStrong :
      toDualMap ℝ 𝕊 (symmetricRankOne y) ∈ subdifferentialAt symmetricMaxEigenvalue X :=
    (mem_euclideanSubdifferentialAt_iff).mp hMatrixEuclidean
  -- Then rewrite to the owner-side `EReal` subdifferential used by affine pullback.
  exact mem_strongDualSubdifferential.mp (by simpa [subdifferentialAt] using hMatrixStrong)

/-- Helper for Proposition 3.28: the affine pullback argument that transports the rank-one
maximum-eigenvalue subgradient to the coefficient-space subgradient witness. -/
private lemma affineSpectralSubgradientVector_mem_subdifferential_via_pullback
    (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) (y : En) (hy_norm : ‖y‖ = 1)
    (hy_eigen :
      affineSymmetricMatrixMap A0 A x *ᵥ y =
        symmetricMaxEigenvalue (affineSymmetricMatrixMap A0 A x) • y) :
    affineSpectralSubgradientVector A y ∈
      euclideanSubdifferentialAt (affineSymmetricMaxEigenvalue A0 A) x := by
  -- Route correction: keep the affine-pullback proof in this file; the prior failure was
  -- structural target ownership, not a defect in the spectral-subgradient argument.
  have hMatrixOwner :
      ((toDualMap ℝ 𝕊 (symmetricRankOne y) : StrongDual ℝ 𝕊) : Module.Dual ℝ 𝕊) ∈
        subdifferential (fun Z : 𝕊 ↦ ((symmetricMaxEigenvalue Z : ℝ) : EReal))
          (affineSymmetricMatrixMap A0 A x) :=
    -- Package the matrix-side eigenvector witness in the owner-level form required by
    -- `subdifferential_precompose_affineMap_subset`.
    rankOne_mem_ownerSubdifferential_symmetricMaxEigenvalue
      (affineSymmetricMatrixMap A0 A x) y hy_norm hy_eigen
  have hPullOwner :
      ((toDualMap ℝ Em (affineSpectralSubgradientVector A y) : StrongDual ℝ Em) :
          Module.Dual ℝ Em) ∈
        subdifferential (fun z : Em ↦ ((affineSymmetricMaxEigenvalue A0 A z : ℝ) : EReal))
          x := by
    -- Pull the owner witness back along the affine matrix map and identify the pulled-back dual.
    have hPull :=
      (subdifferential_precompose_affineMap_subset
        (fun Z : 𝕊 ↦ ((symmetricMaxEigenvalue Z : ℝ) : EReal))
        (affineSymmetricMatrixMap A0 A) x)
        ⟨((toDualMap ℝ 𝕊 (symmetricRankOne y) : StrongDual ℝ 𝕊) : Module.Dual ℝ 𝕊),
          hMatrixOwner, rfl⟩
    simpa [affineSymmetricMaxEigenvalue, affineSymmetricMatrixMap_linear_eq,
      affineSymmetricMatrixLinear_dualMap_rankOne_eq] using hPull
  have hPullStrong :
      toDualMap ℝ Em (affineSpectralSubgradientVector A y) ∈
        subdifferentialAt (affineSymmetricMaxEigenvalue A0 A) x := by
    -- Return from the owner subdifferential to the strong-dual view used by
    -- `euclideanSubdifferentialAt`.
    rw [subdifferentialAt, mem_strongDualSubdifferential]
    simpa using hPullOwner
  -- Finally rewrite the strong-dual witness back to the Euclidean/vector-side subgradient.
  exact (mem_euclideanSubdifferentialAt_iff).mpr hPullStrong

/-- Proposition 3.28: the coefficient vector
`(yᵀ A₁ y, yᵀ A₂ y, ..., yᵀ A_m y)` is a Euclidean subgradient of
`x ↦ λ_max (A₀ + ∑ i, xᵢ Aᵢ)` at `x` whenever `y` is a normalized eigenvector for the largest
eigenvalue of `A₀ + ∑ i, xᵢ Aᵢ`. -/
theorem affineSpectralSubgradientVector_mem_euclideanSubdifferentialAt_affineSymmetricMaxEigenvalue
    (A0 : 𝕊) (A : Fin m → 𝕊) (x : Em) (y : En) (hy_norm : ‖y‖ = 1)
    (hy_eigen :
      (A0 + ∑ i, x i • A i) *ᵥ y =
        symmetricMaxEigenvalue (A0 + ∑ i, x i • A i) • y) :
    affineSpectralSubgradientVector A y ∈
      euclideanSubdifferentialAt
        (fun z : Em ↦ symmetricMaxEigenvalue (A0 + ∑ i, z i • A i)) x := by
  -- Reuse the established affine-pullback proof for the source-facing item entry.
  have hy_eigen_map :
      affineSymmetricMatrixMap A0 A x *ᵥ y =
        symmetricMaxEigenvalue (affineSymmetricMatrixMap A0 A x) • y := by
    simpa [affineSymmetricMatrixMap_apply] using hy_eigen
  simpa [affineSymmetricMaxEigenvalue, affineSymmetricMatrixMap_apply] using
    affineSpectralSubgradientVector_mem_subdifferential_via_pullback
      A0 A x y hy_norm hy_eigen_map

end
end

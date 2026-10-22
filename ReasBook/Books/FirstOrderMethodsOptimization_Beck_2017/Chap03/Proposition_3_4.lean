/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_30
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.InnerProductSpace.Subspace

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix Matrix.Norms.Frobenius RealInnerProductSpace

noncomputable section

section SymmetricMatrices

open Matrix
open Matrix.IsHermitian

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n
local notation "euclideanSubdifferentialAt" =>
  fun f x ↦ euclideanSubdifferential (fun y ↦ (f y : EReal)) x

/- Proposition 3.4 is `source-facing` in the chapter spectral-subdifferential API. The ambient
owner object for the matrix variable is the canonical submodule `symmetricMatrices n = 𝕊^n` from
Definition 1.30, while the spectral owner data comes from mathlib's
`Matrix.IsHermitian.eigenvalues`. The public declarations below keep the book's
maximum-eigenvalue function and rank-one symmetric matrix as the source-facing views derived from
those owners. -/

-- Semantic recall: current mathlib search exposes Rayleigh/eigenvector and symmetric-projection
-- lemmas, but not this subdifferential statement directly, so the chapter-local source-facing API
-- remains the correct owner surface here.

recall euclideanSubdifferential

-- Proof sketch: the project owner criterion `mem_symmetricMatrices_iff` identifies membership in
-- `𝕊^n` with symmetry. The transpose of `vvᵀ` is again `vvᵀ` by `transpose_vecMulVec`.
/-- The real rank-one matrix `vvᵀ` belongs to the symmetric-matrix space `𝕊^n`. -/
private theorem rankOneMatrix_mem_symmetricMatrices (v : E) :
    vecMulVec v v ∈ symmetricMatrices n := by
  rw [mem_symmetricMatrices_iff]
  simp

/-- `symmetricRankOne v` is the symmetric rank-one matrix `vvᵀ`, regarded as an element of
`𝕊^n`. -/
def symmetricRankOne (v : E) : 𝕊 :=
  ⟨vecMulVec v v, rankOneMatrix_mem_symmetricMatrices v⟩

/-- Coercing `symmetricRankOne v` to a matrix recovers the rank-one matrix `vvᵀ`. -/
@[simp] theorem coe_symmetricRankOne (v : E) :
    ((symmetricRankOne v : 𝕊) : Matrix (Fin n) (Fin n) ℝ) = vecMulVec v v :=
  rfl

section

variable [NeZero n]

/-- `symmetricMaxEigenvalue X` is the largest eigenvalue of the symmetric matrix `X`, using the
canonical descending ordering of the Hermitian spectrum. -/
noncomputable def symmetricMaxEigenvalue (X : 𝕊) : ℝ :=
  X.property.isHermitian.eigenvalues₀ 0

/-- `symmetricMaxEigenvalue` is the `0`-th entry of the canonical Hermitian eigenvalue list. -/
@[simp] theorem symmetricMaxEigenvalue_eq_eigenvalues (X : 𝕊) :
    symmetricMaxEigenvalue X = X.property.isHermitian.eigenvalues₀ 0 :=
  rfl

omit [NeZero n] in
/-- Helper for Proposition 3.4: the Riesz pairing with the rank-one matrix `vvᵀ` equals the
corresponding quadratic-form difference. -/
private lemma symmetricRankOneDualPairing_sub_eq (v : E) (X Y : 𝕊) :
    ((InnerProductSpace.toDualMap ℝ 𝕊 (symmetricRankOne v) : Module.Dual ℝ 𝕊) (Y - X) : ℝ) =
      dotProduct v ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) -
        dotProduct v ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by
  -- Move the Riesz pairing to the inherited Frobenius inner product on the symmetric subspace.
  change inner ℝ (symmetricRankOne v) (Y - X) =
    dotProduct v ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) -
      dotProduct v ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)
  -- Work in the ambient matrix space, where the inner product is the trace pairing.
  calc
    inner ℝ (symmetricRankOne v) (Y - X) = inner ℝ (Y - X) (symmetricRankOne v) := by
      rw [real_inner_comm]
    _ = Matrix.trace
          ((((symmetricRankOne v : 𝕊) : Matrix (Fin n) (Fin n) ℝ)ᵀ) *
            (((Y - X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))) := by
      change inner ℝ (((Y - X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))
        (((symmetricRankOne v : 𝕊) : Matrix (Fin n) (Fin n) ℝ)) = _
      simpa using
        (Matrix.inner_eq_trace_transpose_mul
          (((Y - X : 𝕊) : Matrix (Fin n) (Fin n) ℝ))
          (((symmetricRankOne v : 𝕊) : Matrix (Fin n) (Fin n) ℝ)))
    _ = dotProduct v ((((Y : Matrix (Fin n) (Fin n) ℝ) -
          (X : Matrix (Fin n) (Fin n) ℝ)) *ᵥ v)) := by
      have hsub :
          (((Y - X : 𝕊) : Matrix (Fin n) (Fin n) ℝ)) =
            (Y : Matrix (Fin n) (Fin n) ℝ) - (X : Matrix (Fin n) (Fin n) ℝ) :=
        rfl
      rw [coe_symmetricRankOne, transpose_vecMulVec, Matrix.trace_mul_comm,
        Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
      rw [hsub]
    _ = dotProduct v ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) -
          dotProduct v ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by
      rw [Matrix.sub_mulVec, dotProduct_sub]

/-- Helper for Proposition 3.4: a unit eigenvector for `X` realizes the quadratic form value
`symmetricMaxEigenvalue X`. -/
private lemma quadraticForm_eq_symmetricMaxEigenvalue_of_eigenvector
    (X : 𝕊) (v : E) (hv_norm : ‖v‖ = 1)
    (hv_eigen : X *ᵥ v = symmetricMaxEigenvalue X • v) :
    dotProduct v ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) = symmetricMaxEigenvalue X := by
  -- Pair the eigenvector equation with `v` and normalize `dotProduct v v` using `‖v‖ = 1`.
  have hdotself : dotProduct v v = ‖v‖ ^ 2 := by
    have hinner : inner ℝ v v = dotProduct v v :=
      EuclideanSpace.inner_eq_star_dotProduct v v
    rw [← hinner]
    exact real_inner_self_eq_norm_sq v
  have hdotself_one : dotProduct v v = 1 := by
    nlinarith [hdotself, hv_norm]
  have hpair := congrArg (fun w ↦ dotProduct v w) hv_eigen
  simpa [hdotself_one] using hpair

/-- Helper for Proposition 3.4: the quadratic form of a symmetric matrix on a unit vector is
bounded above by its largest eigenvalue. -/
private lemma quadraticForm_le_symmetricMaxEigenvalue_of_unit
    (Y : 𝕊) (u : E) (hu_norm : ‖u‖ = 1) :
    dotProduct u ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) ≤ symmetricMaxEigenvalue Y := by
  let T : E →ₗ[ℝ] E := (Y : Matrix (Fin n) (Fin n) ℝ).toEuclideanLin
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr Y.property.isHermitian
  let b : OrthonormalBasis (Fin (Fintype.card (Fin n))) ℝ E :=
    hT.eigenvectorBasis finrank_euclideanSpace
  let eig : Fin (Fintype.card (Fin n)) → ℝ := hT.eigenvalues finrank_euclideanSpace
  have hAntitone : Antitone eig := hT.eigenvalues_antitone finrank_euclideanSpace
  have hExpand :
      dotProduct u ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) =
        ∑ i : Fin (Fintype.card (Fin n)), eig i * (b.repr u i) ^ (2 : ℕ) := by
    -- Expand the quadratic form in the orthonormal eigenbasis of the symmetric operator.
    calc
      dotProduct u ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) = inner ℝ u (T u) := by
        calc
          dotProduct u ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) =
              dotProduct ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) u := by
            rw [dotProduct_comm]
          _ = inner ℝ u (T u) := by
            simpa [T] using (EuclideanSpace.inner_eq_star_dotProduct u (T u)).symm
      _ = ∑ i : Fin (Fintype.card (Fin n)), (b.repr u i) * (b.repr (T u) i) := by
        rw [← b.sum_inner_mul_inner u (T u)]
        apply Finset.sum_congr rfl
        intro i hi
        simp [OrthonormalBasis.repr_apply_apply, real_inner_comm]
      _ = ∑ i : Fin (Fintype.card (Fin n)), (b.repr u i) * (eig i * b.repr u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show b.repr (T u) i = eig i * b.repr u i by
          simpa [b, eig] using
            hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace u i]
      _ = ∑ i : Fin (Fintype.card (Fin n)), eig i * (b.repr u i) ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hCompare :
      ∑ i : Fin (Fintype.card (Fin n)), eig i * (b.repr u i) ^ (2 : ℕ) ≤
        ∑ i : Fin (Fintype.card (Fin n)), eig 0 * (b.repr u i) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum fun i _ ↦ ?_
    exact mul_le_mul_of_nonneg_right (hAntitone (Fin.zero_le i)) (sq_nonneg _)
  have hCoefficients :
      ∑ i : Fin (Fintype.card (Fin n)), (b.repr u i) ^ (2 : ℕ) = 1 := by
    have hCoeffNorm :
        ∑ i : Fin (Fintype.card (Fin n)), ‖b.repr u i‖ ^ 2 = ‖u‖ ^ 2 := by
      simpa [OrthonormalBasis.repr_apply_apply] using b.sum_sq_norm_inner_right u
    calc
      ∑ i : Fin (Fintype.card (Fin n)), (b.repr u i) ^ (2 : ℕ) =
          ∑ i : Fin (Fintype.card (Fin n)), ‖b.repr u i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [pow_two, Real.norm_eq_abs]
      _ = ‖u‖ ^ 2 := hCoeffNorm
      _ = 1 := by
        nlinarith [hu_norm]
  have hTop : eig 0 = symmetricMaxEigenvalue Y := by
    rfl
  -- Compare each eigenvalue contribution with the top eigenvalue, then use Parseval.
  calc
    dotProduct u ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ u) =
        ∑ i : Fin (Fintype.card (Fin n)), eig i * (b.repr u i) ^ (2 : ℕ) := hExpand
    _ ≤ ∑ i : Fin (Fintype.card (Fin n)), eig 0 * (b.repr u i) ^ (2 : ℕ) := hCompare
    _ = eig 0 * ∑ i : Fin (Fintype.card (Fin n)), (b.repr u i) ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
    _ = eig 0 := by
      rw [hCoefficients, mul_one]
    _ = symmetricMaxEigenvalue Y := hTop

-- Proof sketch: use the Rayleigh quotient characterization
-- `λ_max Y = max_{‖u‖ = 1} uᵀYu`, evaluate it at the given eigenvector `v`, and rewrite
-- `vᵀ(Y - X)v` as the Frobenius inner product with `vvᵀ`, then apply the Riesz identification
-- between `𝕊^n` and its continuous dual, as packaged by `euclideanSubdifferentialAt`.
/-- Proposition 3.4: if `v` is a unit eigenvector of the symmetric matrix `X` for the largest
eigenvalue, then the rank-one matrix `vvᵀ` belongs to the Euclidean subdifferential of the
maximum-eigenvalue function at `X`; equivalently, via the Frobenius trace-pairing Riesz
identification, it represents a dual subgradient at `X`. -/
theorem symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue
    (X : 𝕊) (v : E) (hv_norm : ‖v‖ = 1)
    (hv_eigen : X *ᵥ v = symmetricMaxEigenvalue X • v) :
    symmetricRankOne v ∈ euclideanSubdifferentialAt symmetricMaxEigenvalue X := by
  -- Rewrite Euclidean subgradient membership to the defining affine lower-support inequality.
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_coe_iff]
  intro Y
  have hPair := symmetricRankOneDualPairing_sub_eq (v := v) (X := X) (Y := Y)
  have hEigenvalue :=
    quadraticForm_eq_symmetricMaxEigenvalue_of_eigenvector
      (X := X) (v := v) hv_norm hv_eigen
  have hRayleigh :=
    quadraticForm_le_symmetricMaxEigenvalue_of_unit (Y := Y) (u := v) hv_norm
  -- Route correction: normalize the dual pairing first, then close with the Rayleigh bound.
  calc
    symmetricMaxEigenvalue X +
        (((InnerProductSpace.toDualMap ℝ 𝕊 (symmetricRankOne v) :
            Module.Dual ℝ 𝕊) (Y - X) : ℝ)) =
        symmetricMaxEigenvalue X +
          (dotProduct v ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) -
            dotProduct v ((X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v)) := by
      rw [hPair]
    _ = dotProduct v ((Y : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) := by
      rw [hEigenvalue]
      ring
    _ ≤ symmetricMaxEigenvalue Y := hRayleigh

end

end SymmetricMatrices

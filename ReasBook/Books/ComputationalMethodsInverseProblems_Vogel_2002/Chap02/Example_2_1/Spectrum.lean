/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

open Module.End

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The source quantity `λ_min(A)` for a real matrix `A`, represented by the
infimum of the real spectrum of `A`. -/
def lambdaMin (A : Matrix n n ℝ) : ℝ :=
  sInf (spectrum ℝ A)

/-- The source quantity `λ_max(A)` for a real matrix `A`, represented by the
supremum of the real spectrum of `A`. -/
def lambdaMax (A : Matrix n n ℝ) : ℝ :=
  sSup (spectrum ℝ A)

scoped notation "λ_min(" A ")" => Matrix.lambdaMin A
scoped notation "λ_max(" A ")" => Matrix.lambdaMax A

/-- `λ_min(A)` is the infimum of the real spectrum of `A`. -/
theorem lambdaMin_eq_sInf_spectrum (A : Matrix n n ℝ) :
    λ_min(A) = sInf (spectrum ℝ A) := by
  -- This is just the definition of `λ_min`.
  rfl

/-- `λ_max(A)` is the supremum of the real spectrum of `A`. -/
theorem lambdaMax_eq_sSup_spectrum (A : Matrix n n ℝ) :
    λ_max(A) = sSup (spectrum ℝ A) := by
  -- This is just the definition of `λ_max`.
  rfl

/-- A Hermitian real matrix over a nonempty finite index type has nonempty real
spectrum. -/
theorem realSpectrum_nonempty [Nonempty n] (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (spectrum ℝ A).Nonempty := by
  -- Rewrite the spectrum as the finite set of Hermitian eigenvalues.
  simpa [hA.spectrum_real_eq_range_eigenvalues] using Set.range_nonempty hA.eigenvalues

/-- For a Hermitian real matrix, `λ_min(A)` belongs to the real spectrum. -/
theorem IsHermitian.lambdaMin_mem_spectrum [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    λ_min(A) ∈ spectrum ℝ A := by
  have hspectrum_finite : (spectrum ℝ A).Finite := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using Set.finite_range hA.eigenvalues
  -- The infimum of a nonempty finite real spectrum is attained.
  rw [Matrix.lambdaMin_eq_sInf_spectrum]
  exact (Matrix.realSpectrum_nonempty A hA).csInf_mem hspectrum_finite

/-- For a Hermitian real matrix, `λ_max(A)` belongs to the real spectrum. -/
theorem IsHermitian.lambdaMax_mem_spectrum [Nonempty n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    λ_max(A) ∈ spectrum ℝ A := by
  have hspectrum_finite : (spectrum ℝ A).Finite := by
    simpa [hA.spectrum_real_eq_range_eigenvalues] using Set.finite_range hA.eigenvalues
  -- The supremum of a nonempty finite real spectrum is attained.
  rw [Matrix.lambdaMax_eq_sSup_spectrum]
  exact (Matrix.realSpectrum_nonempty A hA).csSup_mem hspectrum_finite

/-- Example 2.1 (7): for a symmetric real matrix, `λ_min(A)` is an eigenvalue
of the induced linear operator. -/
theorem IsHermitian.hasEigenvalue_lambdaMin [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    HasEigenvalue A.toEuclideanLin (λ_min(A)) := by
  -- Transport the spectral membership statement to the Euclidean operator.
  rw [Module.End.hasEigenvalue_iff_mem_spectrum]
  simpa [Matrix.toEuclideanLin, Matrix.spectrum_toLpLin (A := A) 2] using
    hA.lambdaMin_mem_spectrum

/-- Example 2.1 (8): for a symmetric real matrix, `λ_max(A)` is an eigenvalue
of the induced linear operator. -/
theorem IsHermitian.hasEigenvalue_lambdaMax [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    HasEigenvalue A.toEuclideanLin (λ_max(A)) := by
  -- Transport the spectral membership statement to the Euclidean operator.
  rw [Module.End.hasEigenvalue_iff_mem_spectrum]
  simpa [Matrix.toEuclideanLin, Matrix.spectrum_toLpLin (A := A) 2] using
    hA.lambdaMax_mem_spectrum

namespace IsHermitian

/-- Helper for Example 2.1: every eigenvalue of a Hermitian real matrix lies in
the closed interval `[λ_min(A), λ_max(A)]`. -/
theorem eigenvalue_mem_Icc_lambdaMin_lambdaMax [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    λ_min(A) ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ λ_max(A) := by
  have hspectrum_bddBelow : BddBelow (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range hA.eigenvalues).bddBelow
  have hspectrum_bddAbove : BddAbove (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range hA.eigenvalues).bddAbove
  have hmem : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
  constructor
  · -- The spectral infimum is a lower bound for every eigenvalue.
    simpa [Matrix.lambdaMin_eq_sInf_spectrum] using csInf_le hspectrum_bddBelow hmem
  · -- The spectral supremum is an upper bound for every eigenvalue.
    simpa [Matrix.lambdaMax_eq_sSup_spectrum] using le_csSup hspectrum_bddAbove hmem

/-- Helper for Example 2.1: in the orthonormal eigenbasis of a Hermitian
matrix, applying `A` scales the `i`-th coordinate by the `i`-th eigenvalue. -/
theorem repr_toEuclideanLin_eq_eigenvalue_mul_repr
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ n) (i : n) :
    (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i =
      hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
  have hsymm : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig :
      A.toEuclideanLin (hA.eigenvectorBasis i) =
        hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    simpa [Matrix.toLpLin_apply] using congrFun (hA.mulVec_eigenvectorBasis i) j
  -- Move `A` onto the eigenvector basis element, then use the eigenvector equation.
  calc
    (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i
        = inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x) := by
            rw [OrthonormalBasis.repr_apply_apply]
    _ = inner ℝ (A.toEuclideanLin (hA.eigenvectorBasis i)) x := by
          symm
          exact hsymm (hA.eigenvectorBasis i) x
    _ = inner ℝ (hA.eigenvalues i • hA.eigenvectorBasis i) x := by rw [heig]
    _ = hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
          rw [OrthonormalBasis.repr_apply_apply, real_inner_smul_left]

/-- Helper for Example 2.1: the quadratic form of a Hermitian real matrix is
the eigenvalue-weighted sum of squared coordinates in an orthonormal
eigenbasis. -/
theorem inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr
    {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ n) :
    inner ℝ (A.toEuclideanLin x) x =
      ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
  -- Expand the quadratic form in the orthonormal eigenbasis and collapse cross terms.
  calc
    inner ℝ (A.toEuclideanLin x) x =
        ∑ i,
          inner ℝ (A.toEuclideanLin x) (hA.eigenvectorBasis i) *
            inner ℝ (hA.eigenvectorBasis i) x := by
          symm
          simpa using hA.eigenvectorBasis.sum_inner_mul_inner (A.toEuclideanLin x) x
    _ =
        ∑ i,
          (hA.eigenvalues i * (hA.eigenvectorBasis.repr x i)) *
            (hA.eigenvectorBasis.repr x i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hcoord :
              inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x) =
                hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) := by
            calc
              inner ℝ (hA.eigenvectorBasis i) (A.toEuclideanLin x)
                  = (hA.eigenvectorBasis.repr (A.toEuclideanLin x)) i := by
                      rw [OrthonormalBasis.repr_apply_apply]
              _ = hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) :=
                    hA.repr_toEuclideanLin_eq_eigenvalue_mul_repr x i
          rw [real_inner_comm, hcoord, OrthonormalBasis.repr_apply_apply]
    _ = ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis.repr x i) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

end IsHermitian

/-- For a positive-definite real matrix, the spectral infimum is nonnegative. -/
theorem spectralInf_nonneg_of_posDef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 ≤ sInf (spectrum ℝ A) := by
  -- The spectral infimum is itself one of the positive eigenvalues.
  rw [← Matrix.lambdaMin_eq_sInf_spectrum]
  have hmem : λ_min(A) ∈ spectrum ℝ A := hA.isHermitian.lambdaMin_mem_spectrum
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  rcases hmem with ⟨i, hi⟩
  rw [← hi]
  exact le_of_lt (hA.eigenvalues_pos i)

/-- For a positive-definite real matrix, the spectral supremum is nonnegative. -/
theorem spectralSup_nonneg_of_posDef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 ≤ sSup (spectrum ℝ A) := by
  -- The spectral supremum is itself one of the positive eigenvalues.
  rw [← Matrix.lambdaMax_eq_sSup_spectrum]
  have hmem : λ_max(A) ∈ spectrum ℝ A := hA.isHermitian.lambdaMax_mem_spectrum
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  rcases hmem with ⟨i, hi⟩
  rw [← hi]
  exact le_of_lt (hA.eigenvalues_pos i)

/-- A positive-definite real matrix has strictly positive `λ_min(A)`. -/
theorem lambdaMin_pos_of_posDef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 < λ_min(A) := by
  -- The spectral infimum is realized by a strictly positive eigenvalue.
  have hmem : λ_min(A) ∈ spectrum ℝ A := hA.isHermitian.lambdaMin_mem_spectrum
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  rcases hmem with ⟨i, hi⟩
  rw [← hi]
  exact hA.eigenvalues_pos i

/-- A positive-definite real matrix has strictly positive `λ_max(A)`. -/
theorem lambdaMax_pos_of_posDef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 < λ_max(A) := by
  -- The spectral supremum is realized by a strictly positive eigenvalue.
  have hmem : λ_max(A) ∈ spectrum ℝ A := hA.isHermitian.lambdaMax_mem_spectrum
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  rcases hmem with ⟨i, hi⟩
  rw [← hi]
  exact hA.eigenvalues_pos i

/-- Shifting `A` by `c • 1` acts on vectors as subtracting `c • f`. -/
theorem lowerShift_toEuclideanLin_apply (A : Matrix n n ℝ) (c : ℝ) (f : EuclideanSpace ℝ n) :
    (A - c • (1 : Matrix n n ℝ)).toEuclideanLin f = A.toEuclideanLin f - c • f := by
  -- Expand the matrix action entrywise and simplify the identity matrix action.
  ext i
  simp [Matrix.toLpLin_apply]

/-- The upper spectral shift acts on vectors as `c • f - A f`. -/
theorem upperShift_toEuclideanLin_apply (A : Matrix n n ℝ) (c : ℝ) (f : EuclideanSpace ℝ n) :
    (c • (1 : Matrix n n ℝ) - A).toEuclideanLin f = c • f - A.toEuclideanLin f := by
  -- Expand the matrix action entrywise and simplify the identity matrix action.
  ext i
  simp [Matrix.toLpLin_apply]

/-- Positive semidefiniteness makes the induced quadratic form nonnegative. -/
theorem inner_toEuclideanLin_nonneg_of_posSemidef
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (f : EuclideanSpace ℝ n) :
    0 ≤ inner ℝ (A.toEuclideanLin f) f := by
  -- Reuse the positive-operator characterization of positive semidefinite matrices.
  exact (Matrix.isPositive_toEuclideanLin_iff.mpr hA).inner_nonneg_left f

/-- Subtracting `λ_min(A) • 1` from an SPD matrix leaves a positive-semidefinite
matrix. -/
theorem spectralLowerShift_posSemidef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    (A - λ_min(A) • (1 : Matrix n n ℝ)).PosSemidef := by
  have hshiftHerm :
      (A - λ_min(A) • (1 : Matrix n n ℝ)).IsHermitian := by
    -- Hermitian symmetry is preserved under subtracting a real scalar multiple of the identity.
    simpa using hA.isHermitian.sub
      ((Matrix.isHermitian_one : (1 : Matrix n n ℝ).IsHermitian).smul (IsSelfAdjoint.all _))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hshiftHerm ?_
  intro x
  let f : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hnorm :
      ∑ i, (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 = ‖f‖ ^ 2 := by
    -- Parseval identifies the squared norm with the sum of squared coordinates.
    simpa [OrthonormalBasis.repr_apply_apply, real_inner_comm, pow_two] using
      hA.isHermitian.eigenvectorBasis.sum_inner_mul_inner f f
  have hdecomp :
      inner ℝ ((A - λ_min(A) • (1 : Matrix n n ℝ)).toEuclideanLin f) f =
        ∑ i,
          (hA.isHermitian.eigenvalues i - λ_min(A)) *
            (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
    -- Rewrite the shifted quadratic form in the eigenbasis of `A`.
    calc
      inner ℝ ((A - λ_min(A) • (1 : Matrix n n ℝ)).toEuclideanLin f) f
          = inner ℝ (A.toEuclideanLin f - λ_min(A) • f) f := by
              rw [lowerShift_toEuclideanLin_apply]
      _ = inner ℝ (A.toEuclideanLin f) f - λ_min(A) * ‖f‖ ^ 2 := by
            rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      _ = ∑ i,
            hA.isHermitian.eigenvalues i *
              (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2
            - λ_min(A) * ‖f‖ ^ 2 := by
              rw [hA.isHermitian.inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr]
      _ = ∑ i,
            hA.isHermitian.eigenvalues i *
              (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2
            - λ_min(A) *
              ∑ i, (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
              rw [← hnorm]
      _ = ∑ i,
            (hA.isHermitian.eigenvalues i - λ_min(A)) *
              (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
  have hnonneg :
      0 ≤
        ∑ i,
          (hA.isHermitian.eigenvalues i - λ_min(A)) *
            (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
    -- Each coefficient is nonnegative because `λ_min(A)` is the smallest eigenvalue.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (sub_nonneg.mpr (hA.isHermitian.eigenvalue_mem_Icc_lambdaMin_lambdaMax i).1)
      (sq_nonneg _)
  have hinner_nonneg :
      0 ≤ inner ℝ ((A - λ_min(A) • (1 : Matrix n n ℝ)).toEuclideanLin f) f := by
    rw [hdecomp]
    exact hnonneg
  -- Return to the matrix quadratic form surface.
  simpa [f, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_toLp,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using
    hinner_nonneg

/-- Subtracting an SPD matrix from `λ_max(A) • 1` leaves a
positive-semidefinite matrix. -/
theorem spectralUpperShift_posSemidef [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) :
    (λ_max(A) • (1 : Matrix n n ℝ) - A).PosSemidef := by
  have hshiftHerm :
      (λ_max(A) • (1 : Matrix n n ℝ) - A).IsHermitian := by
    -- Hermitian symmetry is preserved under subtracting from a scalar multiple
    -- of the identity.
    simpa using
      ((Matrix.isHermitian_one : (1 : Matrix n n ℝ).IsHermitian).smul (IsSelfAdjoint.all _)).sub
        hA.isHermitian
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hshiftHerm ?_
  intro x
  let f : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hnorm :
      ∑ i, (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 = ‖f‖ ^ 2 := by
    -- Parseval identifies the squared norm with the sum of squared coordinates.
    simpa [OrthonormalBasis.repr_apply_apply, real_inner_comm, pow_two] using
      hA.isHermitian.eigenvectorBasis.sum_inner_mul_inner f f
  have hdecomp :
      inner ℝ ((λ_max(A) • (1 : Matrix n n ℝ) - A).toEuclideanLin f) f =
        ∑ i,
          (λ_max(A) - hA.isHermitian.eigenvalues i) *
            (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
    -- Rewrite the shifted quadratic form in the eigenbasis of `A`.
    calc
      inner ℝ ((λ_max(A) • (1 : Matrix n n ℝ) - A).toEuclideanLin f) f
          = inner ℝ (λ_max(A) • f - A.toEuclideanLin f) f := by
              rw [upperShift_toEuclideanLin_apply]
      _ = λ_max(A) * ‖f‖ ^ 2 - inner ℝ (A.toEuclideanLin f) f := by
            rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      _ = λ_max(A) * ‖f‖ ^ 2
            - ∑ i,
                hA.isHermitian.eigenvalues i *
                  (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
              rw [hA.isHermitian.inner_toEuclideanLin_eq_sum_eigenvalues_mul_sq_repr]
      _ = λ_max(A) *
            ∑ i, (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2
            - ∑ i,
                hA.isHermitian.eigenvalues i *
                  (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
              rw [← hnorm]
      _ = ∑ i,
            (λ_max(A) - hA.isHermitian.eigenvalues i) *
              (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
  have hnonneg :
      0 ≤
        ∑ i,
          (λ_max(A) - hA.isHermitian.eigenvalues i) *
            (hA.isHermitian.eigenvectorBasis.repr f i) ^ 2 := by
    -- Each coefficient is nonnegative because `λ_max(A)` is the largest eigenvalue.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (sub_nonneg.mpr (hA.isHermitian.eigenvalue_mem_Icc_lambdaMin_lambdaMax i).2)
      (sq_nonneg _)
  have hinner_nonneg :
      0 ≤ inner ℝ ((λ_max(A) • (1 : Matrix n n ℝ) - A).toEuclideanLin f) f := by
    rw [hdecomp]
    exact hnonneg
  -- Return to the matrix quadratic form surface.
  simpa [f, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_toLp,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using
    hinner_nonneg

/-- A lower positive-semidefinite shift gives a lower quadratic-form bound. -/
theorem inner_toEuclideanLin_ge_normSq_of_sub_posSemidef
    (A : Matrix n n ℝ) (c : ℝ)
    (hshift : (A - c • (1 : Matrix n n ℝ)).PosSemidef)
    (f : EuclideanSpace ℝ n) :
    c * ‖f‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin f) f := by
  have hnonneg :
      0 ≤ inner ℝ ((A - c • (1 : Matrix n n ℝ)).toEuclideanLin f) f :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hshift f
  -- Expand the shifted quadratic form and rearrange.
  rw [lowerShift_toEuclideanLin_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hnonneg
  nlinarith

/-- An upper positive-semidefinite shift gives an upper quadratic-form bound. -/
theorem inner_toEuclideanLin_le_normSq_of_sub_posSemidef
    (A : Matrix n n ℝ) (c : ℝ)
    (hshift : (c • (1 : Matrix n n ℝ) - A).PosSemidef)
    (f : EuclideanSpace ℝ n) :
    inner ℝ (A.toEuclideanLin f) f ≤ c * ‖f‖ ^ 2 := by
  have hnonneg :
      0 ≤ inner ℝ ((c • (1 : Matrix n n ℝ) - A).toEuclideanLin f) f :=
    Matrix.inner_toEuclideanLin_nonneg_of_posSemidef _ hshift f
  -- Expand the shifted quadratic form and rearrange.
  rw [upperShift_toEuclideanLin_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hnonneg
  nlinarith

/-- Example 2.1 (7): for an SPD matrix, `λ_min(A)` gives the lower quadratic-form
bound. -/
theorem lambdaMin_mul_normSq_le_inner_toEuclideanLin [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) (f : EuclideanSpace ℝ n) :
    λ_min(A) * ‖f‖ ^ 2 ≤ inner ℝ (A.toEuclideanLin f) f := by
  -- Apply the generic lower bound to the lower spectral shift.
  exact Matrix.inner_toEuclideanLin_ge_normSq_of_sub_posSemidef A (λ_min(A))
    (Matrix.spectralLowerShift_posSemidef A hA) f

/-- Example 2.1 (8): for an SPD matrix, `λ_max(A)` gives the upper quadratic-form
bound. -/
theorem inner_toEuclideanLin_le_lambdaMax_mul_normSq [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) (f : EuclideanSpace ℝ n) :
    inner ℝ (A.toEuclideanLin f) f ≤ λ_max(A) * ‖f‖ ^ 2 := by
  -- Apply the generic upper bound to the upper spectral shift.
  exact Matrix.inner_toEuclideanLin_le_normSq_of_sub_posSemidef A (λ_max(A))
    (Matrix.spectralUpperShift_posSemidef A hA) f

end Matrix

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix
open scoped BigOperators Matrix

-- This file builds on the Chapter 1 vector-norm owner from `Definition_1_2_1` and adds only the
-- matrix-norm-specific source-facing definitions and companion statements used in the sequel.

variable {n : ℕ}

/-- For Chapter01 Definition 1.2.2 (1), a map `matrixNorm : Matrix m n ℝ → ℝ` is a matrix norm if it
is nonnegative, vanishes exactly at `0`, is absolutely homogeneous, and satisfies the triangle
inequality. -/
class IsMatrixNorm {m n : Type} [Fintype m] [Fintype n]
    (matrixNorm : Matrix m n ℝ → ℝ) : Prop where
  nonneg : ∀ A, 0 ≤ matrixNorm A
  eq_zero_iff : ∀ A, matrixNorm A = 0 ↔ A = 0
  smul : ∀ (α : ℝ) (A : Matrix m n ℝ), matrixNorm (α • A) = |α| * matrixNorm A
  add_le : ∀ A B : Matrix m n ℝ, matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B

/-- Unfolding formula for `IsMatrixNorm`. -/
theorem isMatrixNorm_iff {m n : Type} [Fintype m] [Fintype n]
    (matrixNorm : Matrix m n ℝ → ℝ) :
    IsMatrixNorm matrixNorm ↔
      (∀ A, 0 ≤ matrixNorm A) ∧
        (∀ A, matrixNorm A = 0 ↔ A = 0) ∧
        (∀ (α : ℝ) (A : Matrix m n ℝ), matrixNorm (α • A) = |α| * matrixNorm A) ∧
        ∀ A B : Matrix m n ℝ, matrixNorm (A + B) ≤ matrixNorm A + matrixNorm B := by
  -- This theorem only repackages the four structure fields.
  constructor
  · intro hNorm
    exact ⟨hNorm.nonneg, hNorm.eq_zero_iff, hNorm.smul, hNorm.add_le⟩
  · rintro ⟨hNonneg, hZero, hSmul, hAdd⟩
    exact ⟨hNonneg, hZero, hSmul, hAdd⟩

section FrobeniusAsMatrixNorm

open scoped Matrix.Norms.Frobenius

/-- The Frobenius norm on `Matrix m n ℝ` is a matrix norm. -/
instance instIsMatrixNormFrobenius {m n : Type} [Fintype m] [Fintype n] :
    IsMatrixNorm (fun A : Matrix m n ℝ ↦ ‖A‖) := by
  -- The Frobenius norm inherits the matrix-norm axioms from the ambient normed group structure.
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    exact norm_nonneg A
  · intro A
    exact norm_eq_zero
  · intro α A
    simpa [Real.norm_eq_abs] using norm_smul α A
  · intro A B
    exact norm_add_le A B

end FrobeniusAsMatrixNorm

/-- Auxiliary raw supremum formula for the subordinate matrix norm attached to vector norms on
`ℝ^n` and `ℝ^m`; the source-facing statements below impose the `IsVectorNorm` assumptions. -/
noncomputable def inducedMatrixNorm {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ) :
    Matrix (Fin m) (Fin n) ℝ → ℝ :=
  fun A ↦ sSup {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
    r = codomainNorm (A *ᵥ x) / domainNorm x}

/-- For Chapter01 Definition 1.2.2 (2), the subordinate matrix norm attached to vector norms on
`ℝ^n` and `ℝ^m` is the supremum of the matrix-to-vector norm ratio over nonzero vectors. -/
theorem inducedMatrixNorm_eq_sSup_ratio {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    inducedMatrixNorm domainNorm codomainNorm A =
      sSup {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = codomainNorm (A *ᵥ x) / domainNorm x} := by
  -- This is exactly the defining formula of `inducedMatrixNorm`.
  rfl

/-- Helper for Chapter01 Definition 1.2.2: a genuine wrapper around `Fin n → ℝ` so theorem-local
custom norms do not conflict with the standard product norm on function spaces. -/
structure WrappedFinVec (n : ℕ) where
  val : Fin n → ℝ

namespace WrappedFinVec

/-- Helper for Chapter01 Definition 1.2.2: wrapper vectors are equal when their coordinate
functions agree. -/
@[ext] theorem ext {n : ℕ} {x y : WrappedFinVec n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- Helper for Chapter01 Definition 1.2.2: unwraps a wrapped coordinate vector. -/
def equiv (n : ℕ) : WrappedFinVec n ≃ (Fin n → ℝ) where
  toFun := WrappedFinVec.val
  invFun := fun x ↦ ⟨x⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl

instance (n : ℕ) : AddCommGroup (WrappedFinVec n) := (equiv n).addCommGroup

instance (n : ℕ) : Module ℝ (WrappedFinVec n) := (equiv n).module ℝ

@[simp] theorem val_zero {n : ℕ} : (0 : WrappedFinVec n).val = 0 := rfl

@[simp] theorem val_add {n : ℕ} (x y : WrappedFinVec n) : (x + y).val = x.val + y.val := rfl

@[simp] theorem val_neg {n : ℕ} (x : WrappedFinVec n) : (-x).val = -x.val := rfl

@[simp] theorem val_sub {n : ℕ} (x y : WrappedFinVec n) : (x - y).val = x.val - y.val := rfl

@[simp] theorem val_smul {n : ℕ} (a : ℝ) (x : WrappedFinVec n) : (a • x).val = a • x.val := rfl

/-- Helper for Chapter01 Definition 1.2.2: the wrapper is linearly equivalent to the underlying
coordinate space. -/
def linearEquiv (n : ℕ) : WrappedFinVec n ≃ₗ[ℝ] (Fin n → ℝ) where
  __ := equiv n
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

instance (n : ℕ) : FiniteDimensional ℝ (WrappedFinVec n) := by
  -- The wrapper is just a rebundling of the finite-dimensional coordinate space.
  exact (linearEquiv n).symm.finiteDimensional

end WrappedFinVec

/-- Helper for Chapter01 Definition 1.2.2: repackage a vector norm as an additive group norm on the
wrapper type so the custom norm becomes the ambient norm. -/
noncomputable def wrappedVectorNorm {n : ℕ} (vectorNorm : (Fin n → ℝ) → ℝ)
    [IsVectorNorm vectorNorm] : AddGroupNorm (WrappedFinVec n) :=
  { toFun := fun x ↦ vectorNorm x.val
    map_zero' := by
      simpa using IsVectorNorm.map_zero (f := vectorNorm) inferInstance
    add_le' := fun x y ↦ by
      simpa using IsVectorNorm.add_le (f := vectorNorm) x.val y.val
    neg' := fun x ↦ by
      simpa using IsVectorNorm.map_neg (f := vectorNorm) inferInstance x.val
    eq_zero_of_map_eq_zero' := fun x hx ↦ by
      apply WrappedFinVec.ext
      exact (IsVectorNorm.eq_zero_iff (f := vectorNorm) x.val).1 hx }

/-- Helper for Chapter01 Definition 1.2.2: transport matrix-vector multiplication to the wrapper
types carrying the custom norms. -/
noncomputable def wrappedMulVecLinear {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    WrappedFinVec n →ₗ[ℝ] WrappedFinVec m where
  toFun := fun x ↦ ⟨A *ᵥ x.val⟩
  map_add' x y := by
    -- The wrapped map is still the usual matrix-vector multiplication on coordinates.
    apply WrappedFinVec.ext
    simp [Matrix.mulVec_add]
  map_smul' a x := by
    -- Scalar compatibility is inherited from the coordinate-space matrix action.
    apply WrappedFinVec.ext
    simp [Matrix.mulVec_smul]

/-- Helper for Chapter01 Definition 1.2.2: evaluating the wrapped matrix action just unwraps to the
usual `mulVec`. -/
@[simp] theorem wrappedMulVecLinear_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : WrappedFinVec n) :
    (wrappedMulVecLinear A x).val = A *ᵥ x.val :=
  rfl

/-- Helper for Chapter01 Definition 1.2.2: matrix-vector multiplication is bounded by some global
constant for any pair of vector norms on finite-dimensional coordinate spaces. -/
theorem inducedMatrixNorm_has_mulVec_bound {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [hDomain : IsVectorNorm domainNorm] [hCodomain : IsVectorNorm codomainNorm]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin n → ℝ, codomainNorm (A *ᵥ x) ≤ C * domainNorm x := by
  let pDomain : AddGroupNorm (WrappedFinVec n) := wrappedVectorNorm domainNorm
  let pCodomain : AddGroupNorm (WrappedFinVec m) := wrappedVectorNorm codomainNorm
  letI : NormedAddCommGroup (WrappedFinVec n) := AddGroupNorm.toNormedAddCommGroup pDomain
  letI : NormedAddCommGroup (WrappedFinVec m) := AddGroupNorm.toNormedAddCommGroup pCodomain
  letI : NormedSpace ℝ (WrappedFinVec n) := {
    norm_smul_le := fun a x ↦ by
      -- The wrapped domain norm obeys the scalar rule by the source vector-norm axiom.
      change domainNorm (a • x.val) ≤ |a| * domainNorm x.val
      simpa using le_of_eq (hDomain.smul_eq a x.val)
  }
  letI : NormedSpace ℝ (WrappedFinVec m) := {
    norm_smul_le := fun a x ↦ by
      -- The wrapped codomain norm obeys the scalar rule by the source vector-norm axiom.
      change codomainNorm (a • x.val) ≤ |a| * codomainNorm x.val
      simpa using le_of_eq (hCodomain.smul_eq a x.val)
  }
  have hnorm_domain : ∀ x : WrappedFinVec n, ‖x‖ = domainNorm x.val := by
    intro x
    change @Norm.norm (WrappedFinVec n) (AddGroupNorm.toNormedAddGroup pDomain).toNorm x =
      domainNorm x.val
    rfl
  have hnorm_codomain : ∀ x : WrappedFinVec m, ‖x‖ = codomainNorm x.val := by
    intro x
    change @Norm.norm (WrappedFinVec m) (AddGroupNorm.toNormedAddGroup pCodomain).toNorm x =
      codomainNorm x.val
    rfl
  let T : WrappedFinVec n →ₗ[ℝ] WrappedFinVec m := wrappedMulVecLinear A
  -- Route correction: work on genuine wrapper types so the custom vector norms are the ambient
  -- norms, then extract a single global bound from finite-dimensional continuity.
  have hCont : Continuous T := LinearMap.continuous_of_finiteDimensional T
  rcases SemilinearMapClass.bound_of_continuous T hCont with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos.le, ?_⟩
  intro x
  let xWrapped : WrappedFinVec n := ⟨x⟩
  -- Unwrap the operator bound back to the source norms on coordinate vectors.
  simpa [xWrapped, T, hnorm_domain xWrapped, hnorm_codomain (T xWrapped)] using hC xWrapped

/-- Helper for Chapter01 Definition 1.2.2: every nonzero matrix-vector norm ratio is bounded above
by the induced matrix norm defined as the supremum of those ratios. -/
theorem ratio_le_inducedMatrixNorm {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm]
    (A : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : x ≠ 0) :
    codomainNorm (A *ᵥ x) / domainNorm x ≤ inducedMatrixNorm domainNorm codomainNorm A := by
  -- Route correction: stay on the raw supremum formula and obtain boundedness from a single
  -- global matrix-vector estimate, rather than transporting through an operator norm.
  rw [inducedMatrixNorm_eq_sSup_ratio]
  let ratioSet : Set ℝ := {r | ∃ y : Fin n → ℝ, y ≠ 0 ∧
    r = codomainNorm (A *ᵥ y) / domainNorm y}
  have hBdd : BddAbove ratioSet := by
    rcases inducedMatrixNorm_has_mulVec_bound domainNorm codomainNorm A with ⟨C, hCnonneg, hC⟩
    refine ⟨C, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    have hy_norm_ne : domainNorm y ≠ 0 := by
      intro hy_zero
      exact hy ((IsVectorNorm.eq_zero_iff (f := domainNorm) y).1 hy_zero)
    have hy_norm_pos : 0 < domainNorm y := by
      exact lt_of_le_of_ne
        (IsVectorNorm.nonneg (f := domainNorm) y) (by simpa using hy_norm_ne.symm)
    -- Convert the pointwise bound into a ratio bound by dividing by the positive denominator.
    exact (div_le_iff₀ hy_norm_pos).2 (hC y)
  -- The current ratio is one element of the defining set, so it is below the supremum.
  exact le_csSup hBdd ⟨x, hx, rfl⟩

/-- Helper for Chapter01 Definition 1.2.2: any global pointwise matrix-vector bound controls the
induced matrix norm obtained from the raw supremum formula. -/
theorem inducedMatrixNorm_le_of_mulVec_bound {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm]
    (A : Matrix (Fin m) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hMulVec : ∀ x : Fin n → ℝ, codomainNorm (A *ᵥ x) ≤ C * domainNorm x) :
    inducedMatrixNorm domainNorm codomainNorm A ≤ C := by
  let ratioSet : Set ℝ := {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
    r = codomainNorm (A *ᵥ x) / domainNorm x}
  have hratio_le : ∀ r ∈ ratioSet, r ≤ C := by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hx_norm_ne : domainNorm x ≠ 0 := by
      intro hx_zero
      exact hx ((IsVectorNorm.eq_zero_iff (f := domainNorm) x).1 hx_zero)
    have hx_norm_pos : 0 < domainNorm x := by
      exact lt_of_le_of_ne
        (IsVectorNorm.nonneg (f := domainNorm) x) (by simpa using hx_norm_ne.symm)
    -- Divide the assumed pointwise estimate by the positive norm of `x`.
    exact (div_le_iff₀ hx_norm_pos).2 (hMulVec x)
  -- Route correction: eliminate the raw supremum directly by showing that every ratio lies
  -- below the same constant `C`.
  rw [inducedMatrixNorm_eq_sSup_ratio]
  by_cases hratio_nonempty : ratioSet.Nonempty
  · simpa [ratioSet] using (csSup_le hratio_nonempty hratio_le : sSup ratioSet ≤ C)
  · have hratio_empty : ratioSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hratio_nonempty
    simpa [ratioSet, hratio_empty, Real.sSup_empty] using hC

/-- Helper for Chapter01 Definition 1.2.2: the raw supremum defining the induced matrix norm is
nonnegative because every matrix-vector ratio in the defining set is nonnegative. -/
theorem inducedMatrixNorm_nonneg {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ inducedMatrixNorm domainNorm codomainNorm A := by
  -- Read the subordinate norm as a supremum of nonnegative ratios.
  rw [inducedMatrixNorm_eq_sSup_ratio]
  refine Real.sSup_nonneg ?_
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  have hx_norm_ne : domainNorm x ≠ 0 := by
    intro hx_zero
    exact hx ((IsVectorNorm.eq_zero_iff (f := domainNorm) x).1 hx_zero)
  have hx_norm_pos : 0 < domainNorm x := by
    exact lt_of_le_of_ne (IsVectorNorm.nonneg (f := domainNorm) x) (by simpa using hx_norm_ne.symm)
  exact div_nonneg (IsVectorNorm.nonneg (f := codomainNorm) _) hx_norm_pos.le

/-- For Chapter01 Definition 1.2.2 (4), a subordinate matrix norm is consistent with the
corresponding vector norms. -/
theorem inducedMatrixNorm_mulVec_le {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm]
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    codomainNorm (A *ᵥ x) ≤ inducedMatrixNorm domainNorm codomainNorm A * domainNorm x := by
  by_cases hx : x = 0
  · -- The zero vector case is immediate from `A *ᵥ 0 = 0`.
    subst hx
    simp [Matrix.mulVec_zero, IsVectorNorm.map_zero (f := codomainNorm) inferInstance,
      IsVectorNorm.map_zero (f := domainNorm) inferInstance]
  · have hx_norm_ne : domainNorm x ≠ 0 := by
      intro hx_zero
      exact hx ((IsVectorNorm.eq_zero_iff (f := domainNorm) x).1 hx_zero)
    have hx_norm_pos : 0 < domainNorm x := by
      exact lt_of_le_of_ne (IsVectorNorm.nonneg (f := domainNorm) x)
        (by simpa using hx_norm_ne.symm)
    -- The nonzero case is exactly the ratio estimate multiplied back by `domainNorm x`.
    exact (div_le_iff₀ hx_norm_pos).mp
      (ratio_le_inducedMatrixNorm domainNorm codomainNorm A hx)

/-- An induced matrix norm coming from vector norms is again a matrix norm. -/
instance inducedMatrixNorm_isMatrixNorm {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm] :
    IsMatrixNorm (inducedMatrixNorm domainNorm codomainNorm) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    exact inducedMatrixNorm_nonneg domainNorm codomainNorm A
  · intro A
    constructor
    · intro hA
      -- The zero induced norm forces every matrix-vector product to vanish; test on basis vectors.
      apply Matrix.ext
      intro i j
      let e : Fin n → ℝ := Pi.single j 1
      have hMulVecNorm :
          codomainNorm (A *ᵥ e) ≤ inducedMatrixNorm domainNorm codomainNorm A * domainNorm e :=
        inducedMatrixNorm_mulVec_le domainNorm codomainNorm A e
      have hMulVecEqZeroNorm : codomainNorm (A *ᵥ e) = 0 := by
        refine le_antisymm ?_ (IsVectorNorm.nonneg (f := codomainNorm) _)
        simpa [hA] using hMulVecNorm
      have hMulVecEqZero : A *ᵥ e = 0 :=
        (IsVectorNorm.eq_zero_iff (f := codomainNorm) _).1 hMulVecEqZeroNorm
      have hEntry : (A *ᵥ e) i = 0 := by
        simp [hMulVecEqZero]
      simpa [e, Matrix.mulVec_single_one] using hEntry
    · intro hA
      -- The zero matrix has every matrix-vector product equal to zero, so the supremum is `0`.
      subst hA
      refine le_antisymm ?_ (inducedMatrixNorm_nonneg domainNorm codomainNorm 0)
      refine inducedMatrixNorm_le_of_mulVec_bound
        domainNorm codomainNorm (A := 0) (C := 0) le_rfl ?_
      intro x
      simp [Matrix.zero_mulVec, IsVectorNorm.map_zero (f := codomainNorm) inferInstance]
  · intro α A
    have hSmulUpper : ∀ (β : ℝ) (M : Matrix (Fin m) (Fin n) ℝ),
        inducedMatrixNorm domainNorm codomainNorm (β • M) ≤
          |β| * inducedMatrixNorm domainNorm codomainNorm M := by
      intro β M
      refine inducedMatrixNorm_le_of_mulVec_bound domainNorm codomainNorm (A := β • M)
        (C := |β| * inducedMatrixNorm domainNorm codomainNorm M)
        (mul_nonneg (abs_nonneg β) (inducedMatrixNorm_nonneg domainNorm codomainNorm M)) ?_
      intro x
      -- Pointwise scalar homogeneity reduces the new matrix-vector ratio to the old one.
      calc
        codomainNorm ((β • M) *ᵥ x)
            = codomainNorm (β • (M *ᵥ x)) := by rw [Matrix.smul_mulVec]
        _ = |β| * codomainNorm (M *ᵥ x) := by simpa using IsVectorNorm.smul_eq β (M *ᵥ x)
        _ ≤ |β| * (inducedMatrixNorm domainNorm codomainNorm M * domainNorm x) := by
              gcongr
              exact inducedMatrixNorm_mulVec_le domainNorm codomainNorm M x
        _ = (|β| * inducedMatrixNorm domainNorm codomainNorm M) * domainNorm x := by ring
    have hUpper :
        inducedMatrixNorm domainNorm codomainNorm (α • A) ≤
          |α| * inducedMatrixNorm domainNorm codomainNorm A :=
      hSmulUpper α A
    by_cases hα : α = 0
    · -- The zero scalar case collapses to the zero matrix.
      refine le_antisymm hUpper ?_
      simpa [hα] using
        (inducedMatrixNorm_nonneg domainNorm codomainNorm (0 : Matrix (Fin m) (Fin n) ℝ))
    · have hBack :
          inducedMatrixNorm domainNorm codomainNorm A ≤
            |α⁻¹| * inducedMatrixNorm domainNorm codomainNorm (α • A) := by
        simpa [smul_smul, hα, inv_mul_cancel₀] using
          (hSmulUpper α⁻¹ (α • A))
      have hLower :
          |α| * inducedMatrixNorm domainNorm codomainNorm A ≤
            inducedMatrixNorm domainNorm codomainNorm (α • A) := by
        have hMul :=
          mul_le_mul_of_nonneg_left hBack (abs_nonneg α)
        have hAbsNe : |α| ≠ 0 := abs_ne_zero.mpr hα
        have hAbsInv : |α| * |α|⁻¹ = 1 := by
          field_simp [hAbsNe]
        calc
          |α| * inducedMatrixNorm domainNorm codomainNorm A
              ≤ |α| * (|α⁻¹| * inducedMatrixNorm domainNorm codomainNorm (α • A)) := hMul
          _ = (|α| * |α|⁻¹) * inducedMatrixNorm domainNorm codomainNorm (α • A) := by
                rw [abs_inv]
                ring
          _ = inducedMatrixNorm domainNorm codomainNorm (α • A) := by rw [hAbsInv, one_mul]
      exact le_antisymm hUpper hLower
  · intro A B
    -- Bound the sum pointwise and then re-enter through the raw supremum bound lemma.
    refine inducedMatrixNorm_le_of_mulVec_bound domainNorm codomainNorm (A := A + B)
      (C := inducedMatrixNorm domainNorm codomainNorm A +
        inducedMatrixNorm domainNorm codomainNorm B)
      (add_nonneg
        (inducedMatrixNorm_nonneg domainNorm codomainNorm A)
        (inducedMatrixNorm_nonneg domainNorm codomainNorm B)) ?_
    intro x
    calc
      codomainNorm ((A + B) *ᵥ x) = codomainNorm (A *ᵥ x + B *ᵥ x) := by rw [Matrix.add_mulVec]
      _ ≤ codomainNorm (A *ᵥ x) + codomainNorm (B *ᵥ x) :=
            IsVectorNorm.add_le (f := codomainNorm) _ _
      _ ≤ inducedMatrixNorm domainNorm codomainNorm A * domainNorm x +
            inducedMatrixNorm domainNorm codomainNorm B * domainNorm x := by
              gcongr
              · exact inducedMatrixNorm_mulVec_le domainNorm codomainNorm A x
              · exact inducedMatrixNorm_mulVec_le domainNorm codomainNorm B x
      _ = (inducedMatrixNorm domainNorm codomainNorm A +
            inducedMatrixNorm domainNorm codomainNorm B) * domainNorm x := by ring

/-- For Chapter01 Definition 1.2.2 (3), the identity matrix has induced norm `1` with respect to a
vector norm. -/
theorem inducedMatrixNorm_one {n : ℕ}
    [Nonempty (Fin n)] (vectorNorm : (Fin n → ℝ) → ℝ) [IsVectorNorm vectorNorm] :
    inducedMatrixNorm vectorNorm vectorNorm (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  classical
  -- Rewrite to the raw ratio supremum and show the ratio set is exactly `{1}`.
  rw [inducedMatrixNorm_eq_sSup_ratio]
  let i0 : Fin n := Classical.choice ‹Nonempty (Fin n)›
  let x0 : Fin n → ℝ := Pi.single i0 1
  have hx0_ne : x0 ≠ 0 := by
    intro hx0
    have hEval := congrArg (fun f => f i0) hx0
    simp [x0] at hEval
  have hx0_norm_ne : vectorNorm x0 ≠ 0 := by
    intro h0
    exact hx0_ne ((IsVectorNorm.eq_zero_iff (f := vectorNorm) x0).1 h0)
  have hone_mem :
      1 ∈ {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = vectorNorm ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) / vectorNorm x} := by
    refine ⟨x0, hx0_ne, ?_⟩
    rw [one_mulVec]
    field_simp [hx0_norm_ne]
  have hsubset :
      {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = vectorNorm ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) / vectorNorm x} ⊆ {1} := by
    intro r hr
    rcases hr with ⟨x, hx_ne, rfl⟩
    rw [Set.mem_singleton_iff, one_mulVec]
    have hx_norm_ne : vectorNorm x ≠ 0 := by
      intro h0
      exact hx_ne ((IsVectorNorm.eq_zero_iff (f := vectorNorm) x).1 h0)
    field_simp [hx_norm_ne]
  have hEq :
      {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = vectorNorm ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) / vectorNorm x} = {1} := by
    refine Set.Subset.antisymm hsubset ?_
    rintro r rfl
    exact hone_mem
  rw [hEq]
  exact csSup_singleton 1

/-- The induced `ℓ^p` matrix norm associated to the `ℓ^p` vector norms on `ℝ^n` and `ℝ^m`. -/
noncomputable def lpMatrixNorm {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)] :
    Matrix (Fin m) (Fin n) ℝ → ℝ :=
  inducedMatrixNorm (lpNorm p) (lpNorm p)

/-- The set of values `‖A *ᵥ x‖ₚ` obtained from unit `ℓ^p` vectors. -/
noncomputable def lpMatrixNormUnitSphereValues {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) : Set ℝ :=
  {r | ∃ x : Fin n → ℝ, lpNorm p x = 1 ∧ r = lpNorm p (A *ᵥ x)}

/-- Membership in `lpMatrixNormUnitSphereValues` unfolds to a unit `ℓ^p` vector witness. -/
theorem mem_lpMatrixNormUnitSphereValues {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) (r : ℝ) :
    r ∈ lpMatrixNormUnitSphereValues p A ↔
      ∃ x : Fin n → ℝ, lpNorm p x = 1 ∧ r = lpNorm p (A *ᵥ x) := by
  -- Membership is just the set-builder formula.
  rfl

/-- For Chapter01 Definition 1.2.2 (5), the induced `ℓ^p` matrix norm is the supremum of the `ℓ^p`
ratio over nonzero vectors. -/
theorem lpMatrixNorm_eq_sup_ratio {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm p A =
      sSup {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = lpNorm p (A *ᵥ x) / lpNorm p x} := by
  -- The `ℓ^p` owner is the subordinate norm specialized to `lpNorm`.
  rfl

/-- Helper for Chapter01 Definition 1.2.2: normalizing a nonzero vector by its `ℓ^p` norm puts it
on the `ℓ^p` unit sphere. -/
theorem lpNorm_inv_smul_eq_one {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    lpNorm p ((lpNorm p x)⁻¹ • x) = 1 := by
  have hx_norm_ne : lpNorm p x ≠ 0 := by
    intro hx_zero
    exact hx ((IsVectorNorm.eq_zero_iff (f := lpNorm p) x).1 hx_zero)
  have hx_norm_pos : 0 < lpNorm p x := by
    exact lt_of_le_of_ne (IsVectorNorm.nonneg (f := lpNorm p) x) (by simpa using hx_norm_ne.symm)
  -- Normalize the vector and use the scalar rule for the `ℓ^p` norm.
  calc
    lpNorm p ((lpNorm p x)⁻¹ • x) = |(lpNorm p x)⁻¹| * lpNorm p x := by
      simpa using IsVectorNorm.smul_eq (f := lpNorm p) (lpNorm p x)⁻¹ x
    _ = 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr hx_norm_pos.le), inv_mul_cancel₀ hx_norm_ne]

/-- Helper for Chapter01 Definition 1.2.2: the ratio at a nonzero vector equals the value of
`‖A x‖ₚ` on the normalized `ℓ^p` unit-sphere vector. -/
theorem lpNorm_mulVec_inv_smul_eq_ratio {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : x ≠ 0) :
    lpNorm p (A *ᵥ ((lpNorm p x)⁻¹ • x)) = lpNorm p (A *ᵥ x) / lpNorm p x := by
  have hx_norm_ne : lpNorm p x ≠ 0 := by
    intro hx_zero
    exact hx ((IsVectorNorm.eq_zero_iff (f := lpNorm p) x).1 hx_zero)
  have hx_norm_pos : 0 < lpNorm p x := by
    exact lt_of_le_of_ne (IsVectorNorm.nonneg (f := lpNorm p) x) (by simpa using hx_norm_ne.symm)
  -- Move the normalizing scalar through `mulVec`, then read the result by absolute homogeneity.
  calc
    lpNorm p (A *ᵥ ((lpNorm p x)⁻¹ • x))
        = lpNorm p ((lpNorm p x)⁻¹ • (A *ᵥ x)) := by rw [Matrix.mulVec_smul]
    _ = |(lpNorm p x)⁻¹| * lpNorm p (A *ᵥ x) := by
          simpa using IsVectorNorm.smul_eq (f := lpNorm p) (lpNorm p x)⁻¹ (A *ᵥ x)
    _ = lpNorm p (A *ᵥ x) / lpNorm p x := by
          rw [abs_of_nonneg (inv_nonneg.mpr hx_norm_pos.le), div_eq_mul_inv, mul_comm]

/-- Helper for Chapter01 Definition 1.2.2: the unit-sphere value set of `‖A x‖ₚ` is compact after
installing `lpNorm p` as the wrapped ambient norm. -/
theorem lpMatrixNormUnitSphereValues_isCompact {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsCompact (lpMatrixNormUnitSphereValues p A) := by
  let pWrapped : AddGroupNorm (WrappedFinVec n) := wrappedVectorNorm (lpNorm p)
  let qWrapped : AddGroupNorm (WrappedFinVec m) := wrappedVectorNorm (lpNorm p)
  letI : NormedAddCommGroup (WrappedFinVec n) := AddGroupNorm.toNormedAddCommGroup pWrapped
  letI : NormedAddCommGroup (WrappedFinVec m) := AddGroupNorm.toNormedAddCommGroup qWrapped
  letI : NormedSpace ℝ (WrappedFinVec n) := {
    norm_smul_le := fun a x ↦ by
      -- The wrapped `ℓ^p` norm inherits absolute homogeneity from the vector norm.
      change lpNorm p (a • x.val) ≤ |a| * lpNorm p x.val
      simpa using le_of_eq (IsVectorNorm.smul_eq (f := lpNorm p) a x.val)
  }
  letI : NormedSpace ℝ (WrappedFinVec m) := {
    norm_smul_le := fun a x ↦ by
      -- The wrapped codomain uses the same `ℓ^p` norm, so the same scalar rule applies.
      change lpNorm p (a • x.val) ≤ |a| * lpNorm p x.val
      simpa using le_of_eq (IsVectorNorm.smul_eq (f := lpNorm p) a x.val)
  }
  letI : ProperSpace (WrappedFinVec n) := FiniteDimensional.proper ℝ (WrappedFinVec n)
  let unitSphere : Set (WrappedFinVec n) := Metric.sphere (0 : WrappedFinVec n) 1
  let valueMap : WrappedFinVec n → ℝ := fun x ↦ ‖wrappedMulVecLinear A x‖
  have hnorm_domain : ∀ x : WrappedFinVec n, ‖x‖ = lpNorm p x.val := by
    intro x
    change @Norm.norm (WrappedFinVec n) (AddGroupNorm.toNormedAddGroup pWrapped).toNorm x =
      lpNorm p x.val
    rfl
  have hnorm_codomain : ∀ y : WrappedFinVec m, ‖y‖ = lpNorm p y.val := by
    intro y
    change @Norm.norm (WrappedFinVec m) (AddGroupNorm.toNormedAddGroup qWrapped).toNorm y =
      lpNorm p y.val
    rfl
  have hContLinear : Continuous (wrappedMulVecLinear A) :=
    LinearMap.continuous_of_finiteDimensional (wrappedMulVecLinear A)
  have hContValueMap : ContinuousOn valueMap unitSphere := by
    have hContNorm : Continuous fun x : WrappedFinVec n ↦ ‖wrappedMulVecLinear A x‖ :=
      continuous_norm.comp hContLinear
    exact hContNorm.continuousOn
  have hUnitSphereCompact : IsCompact unitSphere := by
    -- Route correction: compactness belongs to the wrapped `ℓ^p` unit sphere, not the default
    -- product sphere on functions.
    simpa [unitSphere, hnorm_domain] using isCompact_sphere (0 : WrappedFinVec n) (1 : ℝ)
  have hImage :
      valueMap '' unitSphere = lpMatrixNormUnitSphereValues p A := by
    ext r
    constructor
    · rintro ⟨x, hx, hr⟩
      have hx_norm : ‖x‖ = (1 : ℝ) := by
        change x ∈ Metric.sphere (0 : WrappedFinVec n) 1 at hx
        simpa using (mem_sphere_iff_norm.mp hx)
      refine ⟨x.val, ?_, ?_⟩
      -- Unwrap sphere membership to recover the unit `ℓ^p` constraint.
      · simpa [hnorm_domain x] using hx_norm
      · simpa [valueMap, wrappedMulVecLinear_apply,
          hnorm_codomain (wrappedMulVecLinear A x)] using hr.symm
    · rintro ⟨x, hx, hr⟩
      have hx_norm : ‖(⟨x⟩ : WrappedFinVec n)‖ = (1 : ℝ) := by
        simpa [hnorm_domain ⟨x⟩] using hx
      refine ⟨⟨x⟩, ?_, ?_⟩
      -- Wrap a unit `ℓ^p` vector back into the compact unit sphere.
      · change (⟨x⟩ : WrappedFinVec n) ∈ Metric.sphere (0 : WrappedFinVec n) 1
        have hx_dist : ‖(⟨x⟩ : WrappedFinVec n) - 0‖ = (1 : ℝ) := by
          simpa using hx_norm
        exact mem_sphere_iff_norm.mpr hx_dist
      · simpa [valueMap, wrappedMulVecLinear_apply,
          hnorm_codomain (wrappedMulVecLinear A ⟨x⟩)] using hr.symm
  -- The compact unit sphere maps continuously to the set of unit-sphere values.
  simpa [hImage] using hUnitSphereCompact.image_of_continuousOn hContValueMap

/-- Helper for Chapter01 Definition 1.2.2: the raw supremum definition of the induced `ℓ^p`
matrix norm is exactly the supremum of the unit-sphere value set. -/
theorem lpMatrixNorm_eq_sSup_unitSphereValues {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm p A = sSup (lpMatrixNormUnitSphereValues p A) := by
  let ratioSet : Set ℝ := {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
    r = lpNorm p (A *ᵥ x) / lpNorm p x}
  have hEq : ratioSet = lpMatrixNormUnitSphereValues p A := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(lpNorm p x)⁻¹ • x, lpNorm_inv_smul_eq_one (p := p) hx, ?_⟩
      -- Normalize the nonzero witness to the unit sphere without changing the ratio value.
      exact (lpNorm_mulVec_inv_smul_eq_ratio (p := p) A hx).symm
    · rintro ⟨x, hx, rfl⟩
      have hx_ne : x ≠ 0 := by
        intro hx_zero
        have hx_norm_zero : lpNorm p x = 0 := by
          simpa [hx_zero] using IsVectorNorm.map_zero (f := lpNorm p) inferInstance
        rw [hx_norm_zero] at hx
        norm_num at hx
      -- A unit-sphere value is already one of the original ratios because the denominator is `1`.
      refine ⟨x, hx_ne, ?_⟩
      rw [hx, div_one]
  -- Replace the raw ratio set by the normalized unit-sphere value set.
  rw [lpMatrixNorm_eq_sup_ratio]
  exact congrArg sSup hEq

/-- For Chapter01 Definition 1.2.2 (6), the induced `ℓ^p` matrix norm is the greatest value of
`‖A *ᵥ x‖ₚ` on the unit `ℓ^p` sphere. -/
theorem lpMatrixNorm_eq_max_on_unitSphere {m n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    IsGreatest (lpMatrixNormUnitSphereValues p A) (lpMatrixNorm p A) := by
  classical
  have hCompact : IsCompact (lpMatrixNormUnitSphereValues p A) :=
    lpMatrixNormUnitSphereValues_isCompact (p := p) A
  have hNonempty : (lpMatrixNormUnitSphereValues p A).Nonempty := by
    let i0 : Fin n := Classical.choice ‹Nonempty (Fin n)›
    let x0 : Fin n → ℝ := Pi.single i0 1
    have hx0_ne : x0 ≠ 0 := by
      intro hx0
      have hEval := congrArg (fun f => f i0) hx0
      simp [x0] at hEval
    refine ⟨lpNorm p (A *ᵥ ((lpNorm p x0)⁻¹ • x0)), ?_⟩
    -- Route correction: produce a genuine unit-sphere witness before invoking compact extrema.
    exact ⟨(lpNorm p x0)⁻¹ • x0, lpNorm_inv_smul_eq_one (p := p) hx0_ne, rfl⟩
  -- Once the unit-sphere value set is compact, its supremum is attained.
  simpa [lpMatrixNorm_eq_sSup_unitSphereValues (p := p) A] using hCompact.isGreatest_sSup hNonempty

/-- A unit `ℓ^p` vector minimizing `‖A x‖ₚ` over the unit `ℓ^p` sphere. -/
def IsLpUnitSphereMinimizer {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  lpNorm p x = 1 ∧
    ∀ y : Fin n → ℝ, lpNorm p y = 1 → lpNorm p (A *ᵥ x) ≤ lpNorm p (A *ᵥ y)

/-- Unfolding formula for `IsLpUnitSphereMinimizer`. -/
theorem isLpUnitSphereMinimizer_iff {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    IsLpUnitSphereMinimizer p A x ↔
      lpNorm p x = 1 ∧
        ∀ y : Fin n → ℝ, lpNorm p y = 1 → lpNorm p (A *ᵥ x) ≤ lpNorm p (A *ᵥ y) := by
  -- This theorem only unfolds the predicate definition.
  rfl

/-- An `ℓ^p` unit-sphere minimizer whose minimum value realizes the inverse induced norm. -/
def IsLpMatrixNormInverseWitness {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  IsLpUnitSphereMinimizer p A x ∧
    lpMatrixNorm p A⁻¹ = 1 / lpNorm p (A *ᵥ x)

/-- Unfolding formula for `IsLpMatrixNormInverseWitness`. -/
theorem isLpMatrixNormInverseWitness_iff {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    IsLpMatrixNormInverseWitness p A x ↔
      IsLpUnitSphereMinimizer p A x ∧
        lpMatrixNorm p A⁻¹ = 1 / lpNorm p (A *ᵥ x) := by
  -- This theorem only unfolds the witness predicate.
  rfl

/-- Helper for Chapter01 Definition 1.2.2: an invertible square matrix attains a strictly positive
minimum of `‖A x‖ₚ` on the unit `ℓ^p` sphere. -/
theorem exists_isLpUnitSphereMinimizer_of_isUnit {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) :
    ∃ x : Fin n → ℝ, IsLpUnitSphereMinimizer p A x ∧ 0 < lpNorm p (A *ᵥ x) := by
  classical
  have hCompact : IsCompact (lpMatrixNormUnitSphereValues p A) :=
    lpMatrixNormUnitSphereValues_isCompact (p := p) A
  have hNonempty : (lpMatrixNormUnitSphereValues p A).Nonempty := by
    let i0 : Fin n := Classical.choice ‹Nonempty (Fin n)›
    let x0 : Fin n → ℝ := Pi.single i0 1
    have hx0_ne : x0 ≠ 0 := by
      intro hx0
      have hEval := congrArg (fun f => f i0) hx0
      simp [x0] at hEval
    refine ⟨lpNorm p (A *ᵥ ((lpNorm p x0)⁻¹ • x0)), ?_⟩
    -- Produce a concrete unit-sphere value before taking the compact minimum.
    exact ⟨(lpNorm p x0)⁻¹ • x0, lpNorm_inv_smul_eq_one (p := p) hx0_ne, rfl⟩
  obtain ⟨μ, hμ⟩ := hCompact.exists_isLeast hNonempty
  rcases hμ.1 with ⟨x, hx_unit, hxμ⟩
  refine ⟨x, ?_, ?_⟩
  · refine ⟨hx_unit, ?_⟩
    intro y hy_unit
    -- The least value in the compact image is exactly the minimizing unit-sphere value.
    simpa [hxμ] using hμ.2 ⟨y, hy_unit, rfl⟩
  · have hx_ne : x ≠ 0 := by
      intro hx_zero
      have hx_norm_zero : lpNorm p x = 0 := by
        simpa [hx_zero] using IsVectorNorm.map_zero (f := lpNorm p) inferInstance
      rw [hx_norm_zero] at hx_unit
      norm_num at hx_unit
    have hAx_nonzero : A *ᵥ x ≠ 0 := by
      intro hAx_zero
      have hInjective : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hA
      apply hx_ne
      exact hInjective (by simpa using hAx_zero)
    have hAx_norm_ne : lpNorm p (A *ᵥ x) ≠ 0 := by
      intro hAx_norm_zero
      apply hAx_nonzero
      exact (IsVectorNorm.eq_zero_iff (f := lpNorm p) (A *ᵥ x)).1 hAx_norm_zero
    -- Invertibility rules out a zero image on a unit vector, so the minimum is strictly positive.
    exact lt_of_le_of_ne (IsVectorNorm.nonneg (f := lpNorm p) (A *ᵥ x))
      (by simpa using hAx_norm_ne.symm)

/-- For Chapter01 Definition 1.2.2 (7), for an invertible square matrix, the minimum value of
`‖A x‖ₚ` on the unit `ℓ^p` sphere has reciprocal equal to the inverse `ℓ^p` matrix norm. -/
theorem lpMatrixNorm_inv_eq_inv_min_ratio {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) :
    ∃ μ : ℝ, IsLeast (lpMatrixNormUnitSphereValues p A) μ ∧
      lpMatrixNorm p A⁻¹ = 1 / μ := by
  classical
  rcases exists_isLpUnitSphereMinimizer_of_isUnit (p := p) A hA with ⟨x, hxMin, hAx_pos⟩
  refine ⟨lpNorm p (A *ᵥ x), ?_, ?_⟩
  · rcases hxMin with ⟨hx_unit, hx_min⟩
    refine ⟨⟨x, hx_unit, rfl⟩, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy_unit, rfl⟩
    -- The minimizer witness packages the least-value part of the source formula.
    exact hx_min y hy_unit
  · rcases hxMin with ⟨hx_unit, hx_min⟩
    have hUpper : lpMatrixNorm p A⁻¹ ≤ 1 / lpNorm p (A *ᵥ x) := by
      refine inducedMatrixNorm_le_of_mulVec_bound
        (domainNorm := lpNorm p) (codomainNorm := lpNorm p) (A := A⁻¹)
        (C := 1 / lpNorm p (A *ᵥ x)) (le_of_lt (one_div_pos.mpr hAx_pos)) ?_
      intro y
      by_cases hy : y = 0
      · -- The zero vector contributes the trivial bound.
        subst hy
        simp [Matrix.mulVec_zero, IsVectorNorm.map_zero (f := lpNorm p) inferInstance]
      · have hcancel : A *ᵥ (A⁻¹ *ᵥ y) = y := by
          -- Rewrite through an explicit unit witness so inverse cancellation is a matrix identity.
          rcases hA with ⟨u, rfl⟩
          simp [Matrix.mulVec_mulVec]
        have hInvy_ne : A⁻¹ *ᵥ y ≠ 0 := by
          intro hInvy_zero
          apply hy
          simpa [hInvy_zero] using hcancel.symm
        have hratio :
            lpNorm p (A *ᵥ x) ≤ lpNorm p y / lpNorm p (A⁻¹ *ᵥ y) := by
          -- Normalize `A⁻¹ *ᵥ y` to the unit sphere, then use minimality of `x`.
          calc
            lpNorm p (A *ᵥ x)
                ≤ lpNorm p (A *ᵥ ((lpNorm p (A⁻¹ *ᵥ y))⁻¹ • (A⁻¹ *ᵥ y))) := by
                    exact hx_min _ (lpNorm_inv_smul_eq_one (p := p) hInvy_ne)
            _ = lpNorm p (A *ᵥ (A⁻¹ *ᵥ y)) / lpNorm p (A⁻¹ *ᵥ y) := by
                  simpa using (lpNorm_mulVec_inv_smul_eq_ratio (p := p) A hInvy_ne)
            _ = lpNorm p y / lpNorm p (A⁻¹ *ᵥ y) := by rw [hcancel]
        have hInvy_norm_pos : 0 < lpNorm p (A⁻¹ *ᵥ y) := by
          have hInvy_norm_ne : lpNorm p (A⁻¹ *ᵥ y) ≠ 0 := by
            intro hInvy_norm_zero
            exact hInvy_ne ((IsVectorNorm.eq_zero_iff (f := lpNorm p) _).1 hInvy_norm_zero)
          exact lt_of_le_of_ne
            (IsVectorNorm.nonneg (f := lpNorm p) _) (by simpa using hInvy_norm_ne.symm)
        have hmul :
            lpNorm p (A *ᵥ x) * lpNorm p (A⁻¹ *ᵥ y) ≤ lpNorm p y := by
          -- Clear the positive denominator in the ratio estimate.
          exact (le_div_iff₀ hInvy_norm_pos).1 hratio
        -- Divide back by the positive minimizing value `‖A x‖ₚ`.
        calc
          lpNorm p (A⁻¹ *ᵥ y) ≤ lpNorm p y / lpNorm p (A *ᵥ x) := by
            exact (le_div_iff₀ hAx_pos).2 (by simpa [mul_comm] using hmul)
          _ = (1 / lpNorm p (A *ᵥ x)) * lpNorm p y := by
                rw [div_eq_mul_inv, one_div, mul_comm]
    have hLower : 1 / lpNorm p (A *ᵥ x) ≤ lpMatrixNorm p A⁻¹ := by
      have hbound := inducedMatrixNorm_mulVec_le
        (domainNorm := lpNorm p) (codomainNorm := lpNorm p) (A := A⁻¹) (A *ᵥ x)
      have hcancelInv : A⁻¹ *ᵥ (A *ᵥ x) = x := by
        -- The inverse matrix sends `A *ᵥ x` back to `x`.
        rcases hA with ⟨u, rfl⟩
        simp [Matrix.mulVec_mulVec]
      rw [hcancelInv, hx_unit] at hbound
      -- This is the induced-norm bound evaluated at the minimizing vector.
      exact (div_le_iff₀ hAx_pos).2 (by simpa [lpMatrixNorm, mul_comm] using hbound)
    -- Combine the two reciprocal inequalities.
    exact le_antisymm hUpper hLower

section LinftyOperatorNorm

open scoped Matrix.Norms.Operator

/-- Helper for Chapter01 Definition 1.2.2: mathlib's `ℓ^∞` operator norm is the textbook maximum
row-sum formula written over `ℝ`. -/
theorem linftyOpNorm_eq_maxRowSumReal {m n : ℕ} [Nonempty (Fin m)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ ∑ j : Fin n, |A i j|) := by
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i : Fin m ↦ ∑ j : Fin n, |A i j|)
  have hEqNN :
      (Finset.univ : Finset (Fin m)).sup (fun i : Fin m ↦ ∑ j : Fin n, ‖A i j‖₊) =
        ∑ j : Fin n, ‖A i0 j‖₊ := by
    apply le_antisymm
    · refine Finset.sup_le ?_
      intro i _hi
      have hleReal : ∑ j : Fin n, |A i j| ≤ ∑ j : Fin n, |A i0 j| := by
        calc
          ∑ j : Fin n, |A i j|
              ≤ Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ ∑ j : Fin n, |A i j|) :=
                Finset.le_sup' (s := Finset.univ)
                  (f := fun i : Fin m ↦ ∑ j : Fin n, |A i j|) (h := Finset.mem_univ i)
          _ = ∑ j : Fin n, |A i0 j| := hi0
      exact NNReal.coe_le_coe.mp (by
        simpa [NNReal.coe_sum, Real.norm_eq_abs] using hleReal)
    · exact Finset.le_sup (s := Finset.univ)
        (f := fun i : Fin m ↦ ∑ j : Fin n, ‖A i j‖₊) (Finset.mem_univ i0)
  -- Route correction: identify the `ℝ≥0` row-sup with the maximizing row, then cast once.
  conv_lhs =>
    rw [Matrix.linfty_opNorm_def, hEqNN]
  calc
    (↑(∑ j : Fin n, ‖A i0 j‖₊) : ℝ) = ∑ j : Fin n, |A i0 j| := by
      simp [NNReal.coe_sum, Real.norm_eq_abs]
    _ = Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ ∑ j : Fin n, |A i j|) := hi0.symm

/-- Helper for Chapter01 Definition 1.2.2: the induced `ℓ^∞` matrix norm agrees with mathlib's
operator norm in `Matrix.Norms.Operator` scope. -/
theorem linftyMatrixNorm_eq_operatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (⊤ : ENNReal) A = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · -- The owner-level `ℓ∞` operator norm is a uniform bound for every matrix-vector ratio.
    refine inducedMatrixNorm_le_of_mulVec_bound
      (domainNorm := lpNorm (⊤ : ENNReal)) (codomainNorm := lpNorm (⊤ : ENNReal))
      (A := A) (C := ‖A‖) (norm_nonneg _) ?_
    intro x
    simpa [linftyNorm, lpNorm] using Matrix.linfty_opNorm_mulVec A x
  · -- Conversely, the induced `ℓ∞` bound controls the operator norm of `mulVec`.
    rw [Matrix.linfty_opNorm_eq_opNorm]
    refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
    · exact inducedMatrixNorm_nonneg (lpNorm (⊤ : ENNReal)) (lpNorm (⊤ : ENNReal)) A
    · intro x
      simpa [lpMatrixNorm, lpNorm] using
        (inducedMatrixNorm_mulVec_le
          (domainNorm := lpNorm (⊤ : ENNReal))
          (codomainNorm := lpNorm (⊤ : ENNReal)) A x)

/-- Helper for Chapter01 Definition 1.2.2: the induced `ℓ^1` matrix norm is bounded above by the
maximum absolute column sum. -/
theorem l1MatrixNorm_le_maxColumnSum {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (1 : ENNReal) A ≤
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|) := by
  let C : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|)
  have hCnonneg : 0 ≤ C := by
    obtain ⟨j0, -, hj0⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|)
    have hsum_nonneg : 0 ≤ ∑ i : Fin m, |A i j0| :=
      Finset.sum_nonneg fun i _hi ↦ abs_nonneg (A i j0)
    simpa [C, hj0] using hsum_nonneg
  refine inducedMatrixNorm_le_of_mulVec_bound
    (domainNorm := lpNorm (1 : ENNReal)) (codomainNorm := lpNorm (1 : ENNReal))
    (A := A) (C := C) hCnonneg ?_
  intro x
  have hx :
      ‖A *ᵥ x‖₁ ≤ C * ‖x‖₁ := by
    -- Estimate each row by the triangle inequality, then factor out the maximal column sum.
    calc
      ‖A *ᵥ x‖₁ = ∑ i : Fin m, |(A *ᵥ x) i| := l1Norm_eq_sum_abs _
      _ = ∑ i : Fin m, |∑ j : Fin n, A i j * x j| := by
            simp [Matrix.mulVec_eq_sum, mul_comm]
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, |A i j * x j| := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin n ↦ A i j * x j))
      _ = ∑ j : Fin n, (∑ i : Fin m, |A i j|) * |x j| := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simp [abs_mul, Finset.mul_sum, mul_comm]
      _ ≤ ∑ j : Fin n, C * |x j| := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            have hjC : ∑ i : Fin m, |A i j| ≤ C := by
              simpa [C] using
                (Finset.le_sup' (s := Finset.univ)
                  (f := fun j : Fin n ↦ ∑ i : Fin m, |A i j|)
                  (h := Finset.mem_univ j))
            exact mul_le_mul_of_nonneg_right
              hjC
              (abs_nonneg (x j))
      _ = C * ∑ j : Fin n, |x j| := by rw [← Finset.mul_sum]
      _ = C * ‖x‖₁ := by rw [l1Norm_eq_sum_abs]
  -- Return to the subordinate-norm owner after proving the source-facing `ℓ¹` estimate.
  simpa [lpMatrixNorm, l1Norm, lpNorm] using hx

/-- Helper for Chapter01 Definition 1.2.2: a maximizing column gives a lower bound for the induced
`ℓ^1` matrix norm. -/
theorem maxColumnSum_le_l1MatrixNorm {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Finset.univ.sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|) ≤
      lpMatrixNorm (1 : ENNReal) A := by
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|)
  let e : Fin n → ℝ := Pi.single j0 1
  have he : e ≠ 0 := by
    intro heq
    have hEval := congrArg (fun f => f j0) heq
    simp [e] at hEval
  have he_norm : lpNorm (1 : ENNReal) e = 1 := by
    change ‖e‖₁ = 1
    rw [l1Norm_eq_sum_abs]
    rw [Finset.sum_eq_single j0]
    · simp [e]
    · intro b _hb hbj0
      simp [e, Pi.single_eq_of_ne hbj0]
    · intro hj0
      exact False.elim (hj0 (Finset.mem_univ j0))
  -- Test the operator norm on the maximizing basis vector `e_{j0}`.
  rw [hj0]
  calc
    ∑ i : Fin m, |A i j0|
        = lpNorm (1 : ENNReal) (A *ᵥ e) / lpNorm (1 : ENNReal) e := by
            rw [he_norm, div_one, Matrix.mulVec_single_one]
            simpa [l1Norm, lpNorm] using (l1Norm_eq_sum_abs (A.col j0)).symm
    _ ≤ inducedMatrixNorm (lpNorm (1 : ENNReal)) (lpNorm (1 : ENNReal)) A :=
          ratio_le_inducedMatrixNorm
            (domainNorm := lpNorm (1 : ENNReal))
            (codomainNorm := lpNorm (1 : ENNReal))
            (A := A) (x := e) he

/-- For Chapter01 Definition 1.2.2 (8), the induced `ℓ^1` matrix norm is the maximum column-sum
norm. -/
theorem l1MatrixNorm_eq_max_columnSum {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (1 : ENNReal) A =
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin n ↦ ∑ i : Fin m, |A i j|) := by
  -- Combine the direct upper and lower column-sum estimates.
  exact le_antisymm
    (l1MatrixNorm_le_maxColumnSum A)
    (maxColumnSum_le_l1MatrixNorm A)

/-- For Chapter01 Definition 1.2.2 (9), the induced `ℓ^∞` matrix norm is the maximum row-sum
norm. -/
theorem linftyMatrixNorm_eq_max_rowSum {m n : ℕ} [Nonempty (Fin m)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (⊤ : ENNReal) A =
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m ↦ ∑ j : Fin n, |A i j|) := by
  -- Rewrite the induced `ℓ^∞` norm to mathlib's operator norm, then apply the explicit row-sum
  -- bridge.
  rw [linftyMatrixNorm_eq_operatorNorm, linftyOpNorm_eq_maxRowSumReal]

end LinftyOperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The induced `ℓ^2` matrix norm agrees with the spectral operator norm. -/
theorem l2MatrixNorm_eq_l2OperatorNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (2 : ENNReal) A = ‖A‖ := by
  refine le_antisymm ?_ ?_
  · -- The owner-level spectral norm is a valid uniform bound for the induced `ℓ₂` norm.
    refine inducedMatrixNorm_le_of_mulVec_bound
      (domainNorm := lpNorm (2 : ENNReal)) (codomainNorm := lpNorm (2 : ENNReal))
      (A := A) (C := ‖A‖) (by
        rw [Matrix.l2_opNorm_def]
        exact norm_nonneg _) ?_
    intro x
    change ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖
    exact Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  · -- The induced `ℓ₂` bound controls the Euclidean operator norm of the associated map.
    rw [Matrix.l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
    · exact inducedMatrixNorm_nonneg (lpNorm (2 : ENNReal)) (lpNorm (2 : ENNReal)) A
    · intro x
      change ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ ≤ lpMatrixNorm (2 : ENNReal) A * ‖x‖
      simpa [l2Norm, lpNorm, lpMatrixNorm] using
        (inducedMatrixNorm_mulVec_le
          (domainNorm := lpNorm (2 : ENNReal))
          (codomainNorm := lpNorm (2 : ENNReal)) A x.ofLp)

/-- A largest eigenvalue witness for the `ℓ^2` induced matrix norm formula of `A`. -/
def IsL2MatrixNormMaxEigenvalueWitness {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) : Prop :=
  IsGreatest (Aᵀ * A).charpoly.roots.toFinset μ ∧
    lpMatrixNorm (2 : ENNReal) A = Real.sqrt μ

/-- Unfolding formula for `IsL2MatrixNormMaxEigenvalueWitness`. -/
theorem isL2MatrixNormMaxEigenvalueWitness_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (μ : ℝ) :
    IsL2MatrixNormMaxEigenvalueWitness A μ ↔
      IsGreatest (Aᵀ * A).charpoly.roots.toFinset μ ∧
        lpMatrixNorm (2 : ENNReal) A = Real.sqrt μ := by
  -- This theorem only unfolds the witness predicate.
  rfl

/-- Helper for Chapter01 Definition 1.2.2: the first ordered eigenvalue of `Aᵀ * A` is a greatest
real root of the characteristic polynomial, and it is nonnegative. -/
theorem transposeMulGreatestRoot {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ μ : ℝ, IsGreatest (Aᵀ * A).charpoly.roots.toFinset μ ∧ 0 ≤ μ := by
  let B : Matrix (Fin n) (Fin n) ℝ := Aᵀ * A
  have hB : B.IsHermitian := by
    -- `Aᵀ * A` is Hermitian over `ℝ`, so its ordered eigenvalue list matches the real roots.
    simpa [B] using Matrix.isHermitian_conjTranspose_mul_self A
  let j0 : Fin n := ⟨0, by
    simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)› : 0 < Fintype.card (Fin n))⟩
  let i0 : Fin (Fintype.card (Fin n)) := ⟨0, Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)›⟩
  have hGreatest : IsGreatest B.charpoly.roots.toFinset (hB.eigenvalues₀ i0) := by
    refine ⟨?_, ?_⟩
    · -- The first ordered eigenvalue appears among the characteristic roots.
      change hB.eigenvalues₀ i0 ∈ (B.charpoly.roots.toFinset : Finset ℝ)
      rw [Multiset.mem_toFinset, hB.roots_charpoly_eq_eigenvalues₀]
      refine Multiset.mem_map.2 ?_
      exact ⟨i0, by simp, rfl⟩
    · intro x hx
      -- Any real characteristic root is one of the ordered eigenvalues, so antitonicity makes it
      -- at most the first entry.
      change x ∈ (B.charpoly.roots.toFinset : Finset ℝ) at hx
      rw [Multiset.mem_toFinset, hB.roots_charpoly_eq_eigenvalues₀] at hx
      rcases Multiset.mem_map.1 hx with ⟨i, _hi, hix⟩
      have hi0 : i0 ≤ i := by
        simp [i0]
      have hanti : hB.eigenvalues₀ i ≤ hB.eigenvalues₀ i0 := hB.eigenvalues₀_antitone hi0
      have hx_eq : x = hB.eigenvalues₀ i := by
        exact hix.symm
      rw [hx_eq]
      exact hanti
  refine ⟨hB.eigenvalues₀ i0, hGreatest, ?_⟩
  -- Positivity of `Aᵀ * A` makes every eigenvalue nonnegative, so the greatest one is too.
  have hnonneg : 0 ≤ hB.eigenvalues j0 := by
    simpa [B] using Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j0
  have hj0_mem : hB.eigenvalues j0 ∈ (B.charpoly.roots.toFinset : Finset ℝ) := by
    rw [Multiset.mem_toFinset, hB.roots_charpoly_eq_eigenvalues]
    refine Multiset.mem_map.2 ?_
    exact ⟨j0, by simp, by simp⟩
  exact le_trans hnonneg (hGreatest.2 hj0_mem)

/-- Helper for Chapter01 Definition 1.2.2: unitary conjugation preserves the `ℓ²` operator norm
of a real square matrix. -/
theorem l2OpNormOrthogonalConjEq {n : ℕ} [Nonempty (Fin n)]
    (U : Matrix.unitaryGroup (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B * U‖ = ‖B‖ := by
  have hU_norm : ‖(U : Matrix (Fin n) (Fin n) ℝ)‖ = 1 := CStarRing.norm_of_mem_unitary U.2
  have hUtranspose_norm : ‖((U : Matrix (Fin n) (Fin n) ℝ)ᵀ)‖ = 1 := by
    -- The transpose of a real unitary matrix has the same `ℓ²` operator norm.
    calc
      ‖((U : Matrix (Fin n) (Fin n) ℝ)ᵀ)‖ = ‖(U : Matrix (Fin n) (Fin n) ℝ)‖ := by
        simpa using Matrix.l2_opNorm_conjTranspose (U : Matrix (Fin n) (Fin n) ℝ)
      _ = 1 := hU_norm
  have hUstar_norm : ‖star (U : Matrix (Fin n) (Fin n) ℝ)‖ = 1 := by
    change ‖((U : Matrix (Fin n) (Fin n) ℝ)ᵀ)‖ = 1
    exact hUtranspose_norm
  apply le_antisymm
  · -- First bound the conjugated matrix above by repeated submultiplicativity.
    calc
      ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B * U‖
          ≤ ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B‖ * ‖(U : Matrix (Fin n) (Fin n) ℝ)‖ :=
            Matrix.l2_opNorm_mul _ _
      _ ≤ (‖star (U : Matrix (Fin n) (Fin n) ℝ)‖ * ‖B‖) * ‖(U : Matrix (Fin n) (Fin n) ℝ)‖ := by
            gcongr
            exact Matrix.l2_opNorm_mul _ _
      _ = ‖B‖ := by simp [hU_norm, hUstar_norm]
  · have hUU :
        (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := Unitary.mul_star_self_of_mem U.2
    have hRecover :
        (U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B * U) *
          star (U : Matrix (Fin n) (Fin n) ℝ) = B := by
      -- Conjugating back by `U` and `U⋆` collapses to the identity matrix.
      calc
        (U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B * U) *
            star (U : Matrix (Fin n) (Fin n) ℝ)
            = (U : Matrix (Fin n) (Fin n) ℝ) *
                ((star (U : Matrix (Fin n) (Fin n) ℝ) * B) * U) *
                star (U : Matrix (Fin n) (Fin n) ℝ) := by
                  simp [Matrix.mul_assoc]
        _ = (((U : Matrix (Fin n) (Fin n) ℝ) *
                (star (U : Matrix (Fin n) (Fin n) ℝ) * B)) *
              (U : Matrix (Fin n) (Fin n) ℝ)) *
              star (U : Matrix (Fin n) (Fin n) ℝ) := by
                simp [Matrix.mul_assoc]
        _ = (U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B) *
              ((U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ)) := by
                simp [Matrix.mul_assoc]
        _ = (U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B) := by
              rw [hUU, mul_one]
        _ = ((U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ)) * B := by
              rw [← Matrix.mul_assoc]
        _ = B := by rw [hUU, one_mul]
    -- Apply the same submultiplicative estimate to the conjugated-back expression.
    calc
      ‖B‖
          = ‖(U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B * U) *
              star (U : Matrix (Fin n) (Fin n) ℝ)‖ := by rw [hRecover]
      _ ≤ ‖(U : Matrix (Fin n) (Fin n) ℝ) * (star (U : Matrix (Fin n) (Fin n) ℝ) * B * U)‖ *
            ‖star (U : Matrix (Fin n) (Fin n) ℝ)‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(U : Matrix (Fin n) (Fin n) ℝ)‖ *
            ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B * U‖) *
            ‖star (U : Matrix (Fin n) (Fin n) ℝ)‖ := by
              gcongr
              exact Matrix.l2_opNorm_mul _ _
      _ = ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B * U‖ := by simp [hU_norm, hUstar_norm]

/-- Helper for Chapter01 Definition 1.2.2: for a nonnegative antitone diagonal, the `ℓ²`
operator norm is the first diagonal entry. -/
theorem l2OpNormDiagonalEqTopEntryOfNonnegAntitone {n : ℕ} [Nonempty (Fin n)]
    (d : Fin n → ℝ) (hdAnti : Antitone d) (hdNonneg : ∀ i, 0 ≤ d i) :
    let i0 : Fin n := ⟨0, by
      simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)› : 0 < Fintype.card (Fin n))⟩
    ‖Matrix.diagonal d‖ = d i0 := by
  let i0 : Fin n := ⟨0, by
    simpa using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin n)› : 0 < Fintype.card (Fin n))⟩
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · -- The sup norm of the diagonal entries is bounded above by the first ordered value.
    rw [pi_norm_le_iff_of_nonneg (hdNonneg i0)]
    intro i
    have hi0 : i0 ≤ i := Nat.zero_le _
    have hle : d i ≤ d i0 := hdAnti hi0
    simpa [Real.norm_eq_abs, abs_of_nonneg (hdNonneg i)] using hle
  · -- The first entry itself is bounded by the ambient sup norm.
    have hcoord : ‖d i0‖ ≤ ‖d‖ := norm_le_pi_norm d i0
    simpa [Real.norm_eq_abs, abs_of_nonneg (hdNonneg i0)] using hcoord

/-- Helper for Chapter01 Definition 1.2.2: `Aᵀ * A` has a greatest real charpoly root, and that
greatest root is exactly the `ℓ²` operator norm of `Aᵀ * A`. -/
theorem transposeMulGreatestRootAndNorm {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ μ : ℝ, IsGreatest (Aᵀ * A).charpoly.roots.toFinset μ ∧ ‖Aᵀ * A‖ = μ := by
  let B : Matrix (Fin n) (Fin n) ℝ := Aᵀ * A
  have hB : B.IsHermitian := by
    -- `Aᵀ * A` is Hermitian, so we can diagonalize it in an orthonormal eigenbasis.
    simpa [B] using Matrix.isHermitian_conjTranspose_mul_self A
  let U : Matrix.unitaryGroup (Fin n) ℝ := hB.eigenvectorUnitary
  obtain ⟨μ, hμ_greatest, hμ_nonneg⟩ := transposeMulGreatestRoot A
  have hEigenNonneg : ∀ i : Fin n, 0 ≤ hB.eigenvalues i := by
    intro i
    simpa [B] using Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  have hEigenLe : ∀ i : Fin n, hB.eigenvalues i ≤ μ := by
    intro i
    have hi_mem : hB.eigenvalues i ∈ (B.charpoly.roots.toFinset : Finset ℝ) := by
      rw [Multiset.mem_toFinset, hB.roots_charpoly_eq_eigenvalues]
      refine Multiset.mem_map.2 ?_
      exact ⟨i, by simp, by simp⟩
    exact hμ_greatest.2 hi_mem
  have hμ_memEigen : ∃ i : Fin n, hB.eigenvalues i = μ := by
    have hμ_mem : μ ∈ (B.charpoly.roots.toFinset : Finset ℝ) := hμ_greatest.1
    rw [Multiset.mem_toFinset, hB.roots_charpoly_eq_eigenvalues] at hμ_mem
    rcases Multiset.mem_map.1 hμ_mem with ⟨i, _hi, hμi⟩
    refine ⟨i, ?_⟩
    simpa using hμi
  have hDiagNorm : ‖Matrix.diagonal hB.eigenvalues‖ = μ := by
    -- Every diagonal entry is bounded above by the greatest root `μ`, and one entry attains `μ`.
    rw [Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg hμ_nonneg]
      intro i
      simpa [Real.norm_eq_abs, abs_of_nonneg (hEigenNonneg i)] using hEigenLe i
    · rcases hμ_memEigen with ⟨i, hi⟩
      have hcoord : ‖hB.eigenvalues i‖ ≤ ‖hB.eigenvalues‖ := norm_le_pi_norm hB.eigenvalues i
      simpa [hi, Real.norm_eq_abs, abs_of_nonneg hμ_nonneg] using hcoord
  have hDiagEq :
      star (U : Matrix (Fin n) (Fin n) ℝ) * B * U = Matrix.diagonal hB.eigenvalues := by
    -- Route correction: stay on the matrix-level diagonalization theorem instead of unfolding
    -- `toLin'` transports.
    simpa [B, U, Matrix.IsHermitian.eigenvalues] using hB.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨μ, hμ_greatest, ?_⟩
  -- Transport the norm to the diagonal eigenvalue model, then identify the top entry with `μ`.
  calc
    ‖B‖ = ‖star (U : Matrix (Fin n) (Fin n) ℝ) * B * U‖ := by
      symm
      simpa [U] using l2OpNormOrthogonalConjEq (U := U) (B := B)
    _ = ‖Matrix.diagonal hB.eigenvalues‖ := by rw [hDiagEq]
    _ = μ := hDiagNorm

/-- Chapter01 Definition 1.2.2 (10): for rectangular `A`, there is a greatest real root of
`(Aᵀ * A).charpoly` whose square root equals the induced `ℓ^2` matrix norm. -/
theorem l2MatrixNorm_eq_sqrt_maxEigenvalue_transpose_mul {m n : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ μ : ℝ, IsGreatest (Aᵀ * A).charpoly.roots.toFinset μ ∧
      lpMatrixNorm (2 : ENNReal) A = Real.sqrt μ := by
  obtain ⟨μ, hμ_greatest, hμ_norm⟩ := transposeMulGreatestRootAndNorm A
  have hμ_nonneg : 0 ≤ μ := by
    rw [← hμ_norm]
    exact norm_nonneg _
  have hsq : ‖A‖ ^ 2 = μ := by
    calc
      ‖A‖ ^ 2 = ‖A‖ * ‖A‖ := by ring
      _ = ‖Aᵀ * A‖ := by
            simpa using (Matrix.l2_opNorm_conjTranspose_mul_self A).symm
      _ = μ := hμ_norm
  have hnorm_eq : ‖A‖ = Real.sqrt μ := by
    -- Both sides are nonnegative, so the squared identity identifies the norm with `√μ`.
    nlinarith [hsq, Real.sq_sqrt hμ_nonneg, norm_nonneg A, Real.sqrt_nonneg μ]
  refine ⟨μ, hμ_greatest, ?_⟩
  -- Finish by rewriting the induced `ℓ²` matrix norm to mathlib's spectral operator norm.
  simpa [l2MatrixNorm_eq_l2OperatorNorm] using hnorm_eq

/-- For Chapter01 Definition 1.2.2 (11), a pair of vector norms and a matrix norm are consistent
when
matrix-vector multiplication is bounded by their product. -/
class MatrixNormConsistent {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    (matrixNorm : Matrix (Fin m) (Fin n) ℝ → ℝ) : Prop where
  mulVec_le : ∀ A x, codomainNorm (A *ᵥ x) ≤ matrixNorm A * domainNorm x

/-- Expands the consistency condition for vector norms and a matrix norm. -/
theorem matrixNormConsistent_iff {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    (matrixNorm : Matrix (Fin m) (Fin n) ℝ → ℝ) :
    MatrixNormConsistent domainNorm codomainNorm matrixNorm ↔
      ∀ A x, codomainNorm (A *ᵥ x) ≤ matrixNorm A * domainNorm x := by
  constructor
  · intro hCons
    exact hCons.mulVec_le
  · intro hCons
    exact ⟨hCons⟩

/-- The induced matrix norm yields a consistent pair of vector and matrix norms. -/
instance inducedMatrixNorm_consistent {m n : ℕ}
    (domainNorm : (Fin n → ℝ) → ℝ) (codomainNorm : (Fin m → ℝ) → ℝ)
    [IsVectorNorm domainNorm] [IsVectorNorm codomainNorm] :
    MatrixNormConsistent domainNorm codomainNorm
      (inducedMatrixNorm domainNorm codomainNorm) where
  mulVec_le := inducedMatrixNorm_mulVec_le domainNorm codomainNorm

/-- For Chapter01 Definition 1.2.2 (12), a square matrix norm is submultiplicative when it
satisfies
`‖A B‖ ≤ ‖A‖ ‖B‖`. -/
class MatrixNormSubmultiplicative {n : Type} [Fintype n]
    (matrixNorm : Matrix n n ℝ → ℝ) : Prop where
  mul_le : ∀ A B : Matrix n n ℝ, matrixNorm (A * B) ≤ matrixNorm A * matrixNorm B

/-- Expands submultiplicativity for a square matrix norm. -/
theorem matrixNormSubmultiplicative_iff {n : Type} [Fintype n]
    (matrixNorm : Matrix n n ℝ → ℝ) :
    MatrixNormSubmultiplicative matrixNorm ↔
      ∀ A B : Matrix n n ℝ, matrixNorm (A * B) ≤ matrixNorm A * matrixNorm B := by
  constructor
  · intro hSub
    exact hSub.mul_le
  · intro hSub
    exact ⟨hSub⟩

/-- Every square induced matrix norm is
submultiplicative. -/
instance inducedMatrixNorm_isSubmultiplicative {n : ℕ}
    (vectorNorm : (Fin n → ℝ) → ℝ) [IsVectorNorm vectorNorm] :
    MatrixNormSubmultiplicative
      (inducedMatrixNorm vectorNorm vectorNorm) := by
  refine ⟨?_⟩
  intro A B
  -- Control `(A * B) *ᵥ x` by two successive consistency bounds.
  refine inducedMatrixNorm_le_of_mulVec_bound vectorNorm vectorNorm (A := A * B)
    (C := inducedMatrixNorm vectorNorm vectorNorm A * inducedMatrixNorm vectorNorm vectorNorm B)
    (mul_nonneg
      (inducedMatrixNorm_nonneg vectorNorm vectorNorm A)
      (inducedMatrixNorm_nonneg vectorNorm vectorNorm B)) ?_
  intro x
  calc
    vectorNorm ((A * B) *ᵥ x) = vectorNorm (A *ᵥ (B *ᵥ x)) := by rw [Matrix.mulVec_mulVec]
    _ ≤ inducedMatrixNorm vectorNorm vectorNorm A * vectorNorm (B *ᵥ x) :=
          inducedMatrixNorm_mulVec_le vectorNorm vectorNorm A _
    _ ≤ inducedMatrixNorm vectorNorm vectorNorm A *
          (inducedMatrixNorm vectorNorm vectorNorm B * vectorNorm x) := by
            exact mul_le_mul_of_nonneg_left
              (inducedMatrixNorm_mulVec_le vectorNorm vectorNorm B x)
              (inducedMatrixNorm_nonneg vectorNorm vectorNorm A)
    _ = (inducedMatrixNorm vectorNorm vectorNorm A *
          inducedMatrixNorm vectorNorm vectorNorm B) * vectorNorm x := by ring

/-- For Chapter01 Definition 1.2.2 (13), every square induced `ℓ^p` matrix norm is
submultiplicative. -/
instance lpMatrixNorm_isSubmultiplicative {n : ℕ} (p : ENNReal) [Fact (1 ≤ p)]
    :
    MatrixNormSubmultiplicative
      (lpMatrixNorm p : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  -- This is the square specialization of the generic induced-norm result.
  simpa [lpMatrixNorm] using
    (inducedMatrixNorm_isSubmultiplicative (vectorNorm := lpNorm p))

/-- For Chapter01 Definition 1.2.2 (14), a matrix norm is left orthogonally invariant when left
multiplication by a real orthogonal matrix preserves its value. -/
def IsLeftOrthogonallyInvariantMatrixNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (matrixNorm : Matrix m n ℝ → ℝ) : Prop :=
  ∀ (U : Matrix m m ℝ), U ∈ Matrix.orthogonalGroup m ℝ →
    ∀ A : Matrix m n ℝ, matrixNorm (U * A) = matrixNorm A

/-- Expands left orthogonal invariance for a matrix norm. -/
theorem isLeftOrthogonallyInvariantMatrixNorm_iff {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] (matrixNorm : Matrix m n ℝ → ℝ) :
    IsLeftOrthogonallyInvariantMatrixNorm matrixNorm ↔
      ∀ (U : Matrix m m ℝ), U ∈ Matrix.orthogonalGroup m ℝ →
        ∀ A : Matrix m n ℝ, matrixNorm (U * A) = matrixNorm A := by
  -- The definition is already in iff form.
  rfl

section OperatorNorm

open scoped Matrix.Norms.Operator

/-- The induced `ℓ^∞` matrix norm is consistent with the `ℓ^∞` vector norm. -/
instance linftyOperatorMatrixNorm_consistent {m n : ℕ} :
    MatrixNormConsistent
      (‖·‖∞ : (Fin n → ℝ) → ℝ)
      (‖·‖∞ : (Fin m → ℝ) → ℝ)
      (lpMatrixNorm (⊤ : ENNReal) : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  -- This is the `p = ∞` specialization of the generic induced-norm consistency theorem.
  simpa [linftyNorm, lpMatrixNorm] using
    (inducedMatrixNorm_consistent
      (domainNorm := lpNorm (⊤ : ENNReal))
      (codomainNorm := lpNorm (⊤ : ENNReal)))

end OperatorNorm

section L2OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The induced `ℓ₂` matrix norm is consistent with the `ℓ₂` vector norm. -/
instance l2OperatorMatrixNorm_consistent {m n : ℕ} :
    MatrixNormConsistent
      (‖·‖₂ : (Fin n → ℝ) → ℝ)
      (‖·‖₂ : (Fin m → ℝ) → ℝ)
      (lpMatrixNorm (2 : ENNReal) : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  -- This is the `p = 2` specialization of the generic induced-norm consistency theorem.
  simpa [l2Norm, lpMatrixNorm] using
    (inducedMatrixNorm_consistent
      (domainNorm := lpNorm (2 : ENNReal))
      (codomainNorm := lpNorm (2 : ENNReal)))

/-- The induced `ℓ₂` matrix norm bounds `ℓ₂` matrix-vector multiplication. -/
theorem l2OperatorMatrixNorm_mulVec_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖A *ᵥ x‖₂ ≤
      lpMatrixNorm (2 : ENNReal) A * ‖x‖₂ := by
  -- This is the `p = 2` specialization of the generic subordinate-norm estimate.
  simpa [l2Norm, lpMatrixNorm] using
    (inducedMatrixNorm_mulVec_le
      (domainNorm := lpNorm (2 : ENNReal))
      (codomainNorm := lpNorm (2 : ENNReal))
      A x)

/-- The induced `ℓ₂` matrix norm is submultiplicative on compatible products. -/
theorem l2OperatorMatrixNorm_submultiplicative {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    lpMatrixNorm (2 : ENNReal) (A * B) ≤
      lpMatrixNorm (2 : ENNReal) A * lpMatrixNorm (2 : ENNReal) B := by
  -- Repeat the generic pointwise bound in the rectangular `ℓ₂` setting.
  refine inducedMatrixNorm_le_of_mulVec_bound
    (domainNorm := lpNorm (2 : ENNReal)) (codomainNorm := lpNorm (2 : ENNReal))
    (A := A * B)
    (C := lpMatrixNorm (2 : ENNReal) A * lpMatrixNorm (2 : ENNReal) B)
    (mul_nonneg
      (inducedMatrixNorm_nonneg (lpNorm (2 : ENNReal)) (lpNorm (2 : ENNReal)) A)
      (inducedMatrixNorm_nonneg (lpNorm (2 : ENNReal)) (lpNorm (2 : ENNReal)) B)) ?_
  intro x
  calc
    ‖(A * B) *ᵥ x‖₂ = ‖A *ᵥ (B *ᵥ x)‖₂ := by rw [Matrix.mulVec_mulVec]
    _ ≤ lpMatrixNorm (2 : ENNReal) A * ‖B *ᵥ x‖₂ := l2OperatorMatrixNorm_mulVec_le A (B *ᵥ x)
    _ ≤ lpMatrixNorm (2 : ENNReal) A * (lpMatrixNorm (2 : ENNReal) B * ‖x‖₂) := by
          exact mul_le_mul_of_nonneg_left
            (l2OperatorMatrixNorm_mulVec_le B x)
            (inducedMatrixNorm_nonneg (lpNorm (2 : ENNReal)) (lpNorm (2 : ENNReal)) A)
    _ = (lpMatrixNorm (2 : ENNReal) A * lpMatrixNorm (2 : ENNReal) B) * ‖x‖₂ := by ring

/-- The induced `ℓ₂` matrix norm is a submultiplicative matrix norm on square matrices. -/
instance l2OperatorMatrixNorm_isSubmultiplicative {n : ℕ} :
    MatrixNormSubmultiplicative
      (lpMatrixNorm (2 : ENNReal) : Matrix (Fin n) (Fin n) ℝ → ℝ) := by
  -- This is the square specialization of the generic `ℓ^p` result at `p = 2`.
  simpa using (lpMatrixNorm_isSubmultiplicative (n := n) (p := (2 : ENNReal)))

/-- For Chapter01 Definition 1.2.2 (15), the induced `ℓ₂` matrix norm is left orthogonally
invariant. -/
theorem l2OperatorMatrixNorm_isLeftOrthogonallyInvariant {m n : ℕ} :
    IsLeftOrthogonallyInvariantMatrixNorm
      (lpMatrixNorm (2 : ENNReal) : Matrix (Fin m) (Fin n) ℝ → ℝ) := by
  intro U hU A
  by_cases hm : Nonempty (Fin m)
  · -- Route correction: pass to mathlib's `ℓ₂` operator norm and use `Uᵀ * U = 1` to get
    -- the reverse inequality after the standard submultiplicative upper bound.
    rw [l2MatrixNorm_eq_l2OperatorNorm, l2MatrixNorm_eq_l2OperatorNorm]
    have hU_norm : ‖U‖ = (1 : ℝ) := CStarRing.norm_of_mem_unitary hU
    have hUtU : Uᵀ * U = (1 : Matrix (Fin m) (Fin m) ℝ) :=
      (Matrix.mem_orthogonalGroup_iff' (R := ℝ) (A := U)).1 hU
    have hUt_norm : ‖Uᵀ‖ = (1 : ℝ) := by
      calc
        ‖Uᵀ‖ = ‖U‖ := by simpa using (Matrix.l2_opNorm_conjTranspose U)
        _ = 1 := hU_norm
    apply le_antisymm
    · calc
        ‖U * A‖ ≤ ‖U‖ * ‖A‖ := Matrix.l2_opNorm_mul U A
        _ = ‖A‖ := by simp [hU_norm]
    · calc
        ‖A‖ = ‖Uᵀ * (U * A)‖ := by
          calc
            ‖A‖ = ‖(1 : Matrix (Fin m) (Fin m) ℝ) * A‖ := by simp
            _ = ‖Uᵀ * (U * A)‖ := by rw [← hUtU, Matrix.mul_assoc]
        _ ≤ ‖Uᵀ‖ * ‖U * A‖ := Matrix.l2_opNorm_mul Uᵀ (U * A)
        _ = ‖U * A‖ := by rw [hUt_norm, one_mul]
  · -- If `Fin m` is empty then every `m × n` matrix is definitionally `0`.
    have hEmpty : IsEmpty (Fin m) := not_nonempty_iff.mp hm
    have hZeroU : U = 0 := Subsingleton.elim _ _
    have hZeroA : A = 0 := Subsingleton.elim _ _
    subst hZeroU
    subst hZeroA
    simp

end L2OperatorNorm

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius
open scoped Matrix.Norms.L2Operator

/-- For Chapter01 Definition 1.2.2 (16), the Frobenius norm is the square root of the sum of the
squared entrywise absolute values. -/
theorem frobeniusMatrixNorm_eq {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, |A i j| ^ (2 : ℕ)) := by
  -- Rewrite mathlib's Frobenius `rpow` formula into the textbook square-root form.
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp [Real.norm_eq_abs, sq_abs]

/-- For Chapter01 Definition 1.2.2 (17), the Frobenius norm is the square root of `tr (Aᵀ A)`. -/
theorem frobeniusMatrixNorm_eq_sqrt_trace {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    ‖A‖ = Real.sqrt (Matrix.trace (Aᵀ * A)) := by
  -- First rewrite the Frobenius norm as the entrywise sum of squares.
  rw [frobeniusMatrixNorm_eq]
  -- Then identify `trace (Aᵀ A)` with that same sum.
  congr 1
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp [pow_two]

/-- The Frobenius norm is submultiplicative on compatible matrix products. -/
theorem frobeniusMatrixNorm_submultiplicative {l m n : Type}
    [Fintype l] [Fintype m] [Fintype n] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  -- This is mathlib's Frobenius submultiplicativity theorem.
  simpa using Matrix.frobenius_norm_mul A B

/-- The Frobenius norm is a submultiplicative matrix norm on square matrices. -/
instance frobeniusMatrixNorm_isSubmultiplicative {n : Type} [Fintype n] :
    MatrixNormSubmultiplicative (fun A : Matrix n n ℝ ↦ ‖A‖) := by
  -- Package the previous theorem into the source-facing predicate.
  exact ⟨fun A B ↦ frobeniusMatrixNorm_submultiplicative A B⟩

/-- Helper for Chapter01 Definition 1.2.2: the Frobenius norm is the square root of the sum of
the squared Euclidean column norms. -/
theorem frobeniusMatrixNorm_eq_sqrt_sum_columnL2Sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = Real.sqrt (∑ j : Fin n, ‖A.col j‖₂ ^ 2) := by
  have hcol :
      ∀ j : Fin n, ‖A.col j‖₂ ^ 2 = ∑ i : Fin m, |A i j| ^ (2 : ℕ) := by
    intro j
    rw [l2Norm_eq_sqrt_sum_sq]
    -- Square the Euclidean column norm to recover the entrywise sum of squares in that column.
    simpa using Real.sq_sqrt (Finset.sum_nonneg fun i _hi ↦ by
      exact sq_nonneg (A i j))
  -- Reindex the Frobenius entrywise square sum by columns and rewrite each column block.
  calc
    ‖A‖ = Real.sqrt (∑ i : Fin m, ∑ j : Fin n, |A i j| ^ (2 : ℕ)) := frobeniusMatrixNorm_eq A
    _ = Real.sqrt (∑ j : Fin n, ∑ i : Fin m, |A i j| ^ (2 : ℕ)) := by rw [Finset.sum_comm]
    _ = Real.sqrt (∑ j : Fin n, ‖A.col j‖₂ ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl fun j _hj ↦ (hcol j).symm

/-- Helper for Chapter01 Definition 1.2.2: the Frobenius norm square is the sum of the squared
Euclidean column norms. -/
theorem frobeniusMatrixNorm_sq_eq_sum_columnL2Sq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ ^ 2 = ∑ j : Fin n, ‖A.col j‖₂ ^ 2 := by
  rw [frobeniusMatrixNorm_eq_sqrt_sum_columnL2Sq]
  -- The sum of squared Euclidean column norms is nonnegative, so squaring the square root
  -- returns the sum itself.
  exact Real.sq_sqrt (Finset.sum_nonneg fun j _hj ↦ sq_nonneg ‖A.col j‖₂)

/-- Helper for Chapter01 Definition 1.2.2: the Frobenius norm of `A * B` is controlled by the
spectral norm of `A` and the Frobenius norm of `B`. -/
theorem frobeniusMatrixNorm_mul_le_l2Left {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A * B‖ ≤ lpMatrixNorm (2 : ENNReal) A * ‖B‖ := by
  have hA_nonneg : 0 ≤ lpMatrixNorm (2 : ENNReal) A :=
    inducedMatrixNorm_nonneg (lpNorm (2 : ENNReal)) (lpNorm (2 : ENNReal)) A
  have hTarget_nonneg : 0 ≤ lpMatrixNorm (2 : ENNReal) A * ‖B‖ :=
    mul_nonneg hA_nonneg (norm_nonneg B)
  refine (sq_le_sq₀ (norm_nonneg _) hTarget_nonneg).1 ?_
  calc
    ‖A * B‖ ^ 2 = ∑ j : Fin n, ‖(A * B).col j‖₂ ^ 2 := by
          exact frobeniusMatrixNorm_sq_eq_sum_columnL2Sq (A * B)
    _ = ∑ j : Fin n, ‖A *ᵥ B.col j‖₂ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rfl
    _ ≤ ∑ j : Fin n, (lpMatrixNorm (2 : ENNReal) A * ‖B.col j‖₂) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact (sq_le_sq₀
            (l2Norm_isVectorNorm.nonneg _) (mul_nonneg hA_nonneg (l2Norm_isVectorNorm.nonneg _))).2
            (l2OperatorMatrixNorm_mulVec_le A (B.col j))
    _ = ∑ j : Fin n, (lpMatrixNorm (2 : ENNReal) A) ^ 2 * ‖B.col j‖₂ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
    _ = (lpMatrixNorm (2 : ENNReal) A) ^ 2 * ∑ j : Fin n, ‖B.col j‖₂ ^ 2 := by
          rw [Finset.mul_sum]
    _ = (lpMatrixNorm (2 : ENNReal) A) ^ 2 * ‖B‖ ^ 2 := by
          rw [frobeniusMatrixNorm_sq_eq_sum_columnL2Sq]
    _ = (lpMatrixNorm (2 : ENNReal) A * ‖B‖) ^ 2 := by ring

/-- For Chapter01 Definition 1.2.2 (18), the Frobenius norm satisfies the mixed spectral/Frobenius
estimate `‖A B‖_F ≤ min {‖A‖₂ ‖B‖_F, ‖A‖_F ‖B‖₂}`. -/
theorem frobeniusMatrixNorm_mul_le_min {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    ‖A * B‖ ≤
      min (lpMatrixNorm (2 : ENNReal) A * ‖B‖) (‖A‖ * lpMatrixNorm (2 : ENNReal) B) := by
  have hLeft : ‖A * B‖ ≤ lpMatrixNorm (2 : ENNReal) A * ‖B‖ :=
    frobeniusMatrixNorm_mul_le_l2Left A B
  have hRight :
      ‖A * B‖ ≤ ‖A‖ * lpMatrixNorm (2 : ENNReal) B := by
    -- Apply the left estimate to transposes and rewrite back using transpose invariance.
    have hBtranspose :
        lpMatrixNorm (2 : ENNReal) Bᵀ = lpMatrixNorm (2 : ENNReal) B := by
      rw [l2MatrixNorm_eq_l2OperatorNorm, l2MatrixNorm_eq_l2OperatorNorm]
      simpa using Matrix.l2_opNorm_conjTranspose B
    calc
      ‖A * B‖ = ‖Bᵀ * Aᵀ‖ := by
            rw [← Matrix.transpose_mul, Matrix.frobenius_norm_transpose]
      _ ≤ lpMatrixNorm (2 : ENNReal) Bᵀ * ‖Aᵀ‖ :=
            frobeniusMatrixNorm_mul_le_l2Left Bᵀ Aᵀ
      _ = ‖A‖ * lpMatrixNorm (2 : ENNReal) B := by
            rw [hBtranspose, Matrix.frobenius_norm_transpose, mul_comm]
  -- Both mixed bounds hold, so the minimum of the two also bounds `‖A * B‖`.
  exact le_min hLeft hRight

/-- For Chapter01 Definition 1.2.2 (19), the Frobenius norm is left orthogonally invariant. -/
theorem frobeniusMatrixNorm_isLeftOrthogonallyInvariant {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] :
    IsLeftOrthogonallyInvariantMatrixNorm (fun A : Matrix m n ℝ ↦ ‖A‖) := by
  intro U hU A
  change ‖U * A‖ = ‖A‖
  -- Rewrite both Frobenius norms through `trace ((·)ᵀ (·))`.
  rw [frobeniusMatrixNorm_eq_sqrt_trace, frobeniusMatrixNorm_eq_sqrt_trace]
  have hUtU : Uᵀ * U = (1 : Matrix m m ℝ) :=
    (Matrix.mem_orthogonalGroup_iff' (R := ℝ) (A := U)).1 hU
  -- The orthogonality relation collapses the middle factor to the identity.
  calc
    Real.sqrt (Matrix.trace ((U * A)ᵀ * (U * A)))
      = Real.sqrt (Matrix.trace (Aᵀ * (Uᵀ * U) * A)) := by
          congr 1
          rw [Matrix.transpose_mul]
          congr 1
          calc
            Aᵀ * Uᵀ * (U * A) = Aᵀ * (Uᵀ * (U * A)) := by
              rw [Matrix.mul_assoc]
            _ = Aᵀ * ((Uᵀ * U) * A) := by
              rw [Matrix.mul_assoc]
            _ = Aᵀ * (Uᵀ * U) * A := by
              rw [← Matrix.mul_assoc]
    _ = Real.sqrt (Matrix.trace (Aᵀ * (1 : Matrix m m ℝ) * A)) := by
          rw [hUtU]
    _ = Real.sqrt (Matrix.trace (Aᵀ * A)) := by
          simp

/-- For Chapter01 Definition 1.2.2 (20), the weighted Frobenius norm associated to a symmetric
positive definite square matrix `M` is `A ↦ ‖M * A * M‖`. -/
noncomputable def weightedFrobeniusNorm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun A ↦ ‖M * A * M‖

/-- The weighted Frobenius norm is `‖M A M‖_F`. -/
theorem weightedFrobeniusNorm_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    weightedFrobeniusNorm M A = ‖M * A * M‖ :=
  rfl

/-- A positive definite weight defines a matrix norm through the weighted
Frobenius norm. -/
theorem weightedFrobeniusNorm_isMatrixNorm_of_posDef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hPosDef : M.PosDef) :
    IsMatrixNorm (weightedFrobeniusNorm M) := by
  -- Route correction: the key point is not positivity itself, but invertibility of the weight.
  obtain ⟨U, rfl⟩ := hPosDef.isUnit
  change IsMatrixNorm
    (fun A : Matrix (Fin n) (Fin n) ℝ ↦
      ‖(↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)‖)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    -- Nonnegativity is inherited from the ambient norm.
    exact norm_nonneg _
  · intro A
    constructor
    · intro h
      -- Conjugating by the inverse unit recovers `A` from the zero image.
      have hzero :
          ((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)) = 0 :=
        norm_eq_zero.mp h
      have hzero2 :
          (↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
              (((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ))) *
              (↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 0 := by
        rw [hzero]
        simp
      simpa [mul_assoc] using hzero2
    · intro hA
      simp [hA]
  · intro a A
    -- Scalar homogeneity passes through the conjugation map.
    simpa [mul_assoc] using
      norm_smul a
        ((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ))
  · intro A B
    -- The conjugation map is linear, so the triangle inequality is inherited from the norm.
    simpa [mul_add, add_mul, mul_assoc] using
      norm_add_le
        (((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)))
        (((↑U : Matrix (Fin n) (Fin n) ℝ) * B * (↑U : Matrix (Fin n) (Fin n) ℝ)))

end FrobeniusNorm

section WeightedL2Norm

open scoped Matrix.Norms.L2Operator

/-- For Chapter01 Definition 1.2.2 (21), the weighted `ℓ₂` matrix norm associated to a symmetric
positive definite square matrix `M` is `A ↦ ‖M * A * M‖₂`. -/
noncomputable def weightedL2MatrixNorm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ → ℝ :=
  fun A ↦ ‖M * A * M‖

/-- The weighted `ℓ₂` matrix norm is `‖M A M‖₂`. -/
theorem weightedL2MatrixNorm_eq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    weightedL2MatrixNorm M A = ‖M * A * M‖ :=
  rfl

/-- A positive definite weight defines a matrix norm through the weighted `ℓ₂` norm. -/
theorem weightedL2MatrixNorm_isMatrixNorm_of_posDef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hPosDef : M.PosDef) :
    IsMatrixNorm (weightedL2MatrixNorm M) := by
  -- Route correction: as in the Frobenius case, invertibility of the weight is the decisive fact.
  obtain ⟨U, rfl⟩ := hPosDef.isUnit
  change IsMatrixNorm
    (fun A : Matrix (Fin n) (Fin n) ℝ ↦
      ‖(↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)‖)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A
    -- Nonnegativity is inherited from the ambient `ℓ₂` operator norm.
    exact norm_nonneg _
  · intro A
    constructor
    · intro h
      -- Conjugating by the inverse unit recovers `A` from the zero image.
      have hzero :
          ((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)) = 0 :=
        norm_eq_zero.mp h
      have hzero2 :
          (↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *
              (((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ))) *
              (↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) = 0 := by
        rw [hzero]
        simp
      simpa [mul_assoc] using hzero2
    · intro hA
      simp [hA]
  · intro a A
    -- Scalar homogeneity passes through the conjugation map.
    simpa [mul_assoc] using
      norm_smul a
        ((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ))
  · intro A B
    -- The conjugation map is linear, so the triangle inequality is inherited from the norm.
    simpa [mul_add, add_mul, mul_assoc] using
      norm_add_le
        (((↑U : Matrix (Fin n) (Fin n) ℝ) * A * (↑U : Matrix (Fin n) (Fin n) ℝ)))
        (((↑U : Matrix (Fin n) (Fin n) ℝ) * B * (↑U : Matrix (Fin n) (Fin n) ℝ)))

end WeightedL2Norm

/-- The vector norm obtained by precomposing a vector norm with a change-of-basis matrix `P`. -/
def changeOfBasisVectorNorm {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (vectorNorm : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x ↦ vectorNorm (P *ᵥ x)

/-- `changeOfBasisVectorNorm` is given by the formula `x ↦ ‖P x‖`. -/
theorem changeOfBasisVectorNorm_apply {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (vectorNorm : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    changeOfBasisVectorNorm P vectorNorm x = vectorNorm (P *ᵥ x) := by
  -- This is exactly the definition of the changed vector norm.
  rfl

/-- For Chapter01 Definition 1.2.2 (22), under a nonsingular change of basis, the induced matrix
norm
becomes the conjugated norm `‖P A P⁻¹‖`. -/
theorem inducedMatrixNorm_changeOfBasis_eq {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P)
    (vectorNorm : (Fin n → ℝ) → ℝ) [IsVectorNorm vectorNorm]
    (A : Matrix (Fin n) (Fin n) ℝ) :
    inducedMatrixNorm (changeOfBasisVectorNorm P vectorNorm)
        (changeOfBasisVectorNorm P vectorNorm) A =
      inducedMatrixNorm vectorNorm vectorNorm (P * A * P⁻¹) := by
  obtain ⟨U, rfl⟩ := hP
  -- Compare the two ratio sets by transporting witnesses through the invertible change of basis.
  rw [inducedMatrixNorm_eq_sSup_ratio, inducedMatrixNorm_eq_sSup_ratio]
  have hUinj : Function.Injective ((↑U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ·) :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit U)
  have hUinvinj : Function.Injective ((↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *ᵥ ·) :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit U⁻¹)
  have hset :
      {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = changeOfBasisVectorNorm ↑U vectorNorm (A *ᵥ x) /
          changeOfBasisVectorNorm ↑U vectorNorm x} =
      {r | ∃ x : Fin n → ℝ, x ≠ 0 ∧
        r = vectorNorm (((↑U : Matrix (Fin n) (Fin n) ℝ) * A * ↑↑U⁻¹) *ᵥ x) /
          vectorNorm x} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x, hx, rfl⟩
      -- Push the witness forward by `U`.
      refine ⟨(↑U : Matrix (Fin n) (Fin n) ℝ) *ᵥ x, ?_, ?_⟩
      · exact fun hUx => hx (hUinj <| by simp [hUx])
      · simp [changeOfBasisVectorNorm_apply, Matrix.mulVec_mulVec, mul_assoc]
    · intro hr
      rcases hr with ⟨x, hx, rfl⟩
      -- Pull the witness back by `U⁻¹`.
      refine ⟨(↑↑U⁻¹ : Matrix (Fin n) (Fin n) ℝ) *ᵥ x, ?_, ?_⟩
      · exact fun hUinvx => hx (hUinvinj <| by simpa using hUinvx)
      · simp [changeOfBasisVectorNorm_apply, Matrix.mulVec_mulVec, mul_assoc]
  simp [hset]

section TraceLemmas

-- Chapter01 Definition 1.2.2 (23): the canonical trace owner is `Matrix.trace`, whose definition
-- is the diagonal sum.
#check Matrix.trace

-- The trace is additive on square real matrices.
#check Matrix.trace_add

-- Chapter01 Definition 1.2.2 (24): linearity of the trace is provided by `Matrix.traceLinearMap`.
#check Matrix.traceLinearMap

-- Chapter01 Definition 1.2.2 (25): the trace is invariant under transpose.
#check Matrix.trace_transpose

-- Chapter01 Definition 1.2.2 (26): the trace satisfies the cyclic identity `tr (A B) = tr (B A)`.
#check Matrix.trace_mul_comm

/-- For Chapter01 Definition 1.2.2 (27), after complexification, the trace equals the sum of the
eigenvalues counted with multiplicity. -/
theorem matrixTrace_complexification_eq_sum_eigenvalues {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    ((Matrix.trace A : ℝ) : ℂ) =
      (A.map (algebraMap ℝ ℂ)).charpoly.roots.sum := by
  -- After complexification, the trace matches the complex trace entrywise.
  letI : IsAlgClosed ℂ := Complex.isAlgClosed
  rw [show ((Matrix.trace A : ℝ) : ℂ) = Matrix.trace (A.map (algebraMap ℝ ℂ)) by
    simp [Matrix.trace]]
  -- Then apply the standard trace/eigenvalue formula over an algebraically closed field.
  simpa using (Matrix.trace_eq_sum_roots_charpoly (A := A.map (algebraMap ℝ ℂ)))

end TraceLemmas

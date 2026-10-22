/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_2

open scoped BigOperators

-- Semantic recall: these statements reuse the chapter's source-facing matrix
-- norm owners from Definition 1.2.2. The proof works by wrapping matrices so
-- the abstract norm `N` becomes the ambient norm and then transporting the
-- resulting geometric-series identities back to ordinary matrices.

variable {n : ℕ}

section VonNeumannLemma

variable {N : Matrix (Fin n) (Fin n) ℝ → ℝ}

/-- Helper for Chapter01 Theorem 1.2.5: `WrappedMatrix n N` rebundles
`Matrix (Fin n) (Fin n) ℝ` so the abstract matrix norm `N` can become the
ambient norm. -/
structure WrappedMatrix (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) where
  val : Matrix (Fin n) (Fin n) ℝ

namespace WrappedMatrix

/-- Helper for Chapter01 Theorem 1.2.5: unwrap a wrapped matrix. -/
def equiv (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    WrappedMatrix n N ≃ Matrix (Fin n) (Fin n) ℝ where
  toFun := WrappedMatrix.val
  invFun := fun A ↦ ⟨A⟩
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro A
    rfl

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped matrices inherit their
additive group structure from ordinary matrices. -/
instance instAddCommGroup (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    AddCommGroup (WrappedMatrix n N) :=
  (equiv n N).addCommGroup

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped matrices inherit the scalar
action of `ℝ`. -/
instance instModule (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    Module ℝ (WrappedMatrix n N) :=
  (equiv n N).module ℝ

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped matrices inherit matrix
multiplication. -/
instance instRing (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    Ring (WrappedMatrix n N) :=
  (equiv n N).ring

/-- Helper for Chapter01 Theorem 1.2.5: wrapping does not change the zero
matrix. -/
@[simp] theorem val_zero {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ → ℝ} :
    (0 : WrappedMatrix n N).val = 0 :=
  rfl

/-- Helper for Chapter01 Theorem 1.2.5: wrapping does not change matrix
addition. -/
@[simp] theorem val_add {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (A B : WrappedMatrix n N) :
    (A + B).val = A.val + B.val :=
  rfl

/-- Helper for Chapter01 Theorem 1.2.5: wrapping does not change matrix
negation. -/
@[simp] theorem val_neg {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (A : WrappedMatrix n N) :
    (-A).val = -A.val :=
  rfl

/-- Helper for Chapter01 Theorem 1.2.5: wrapping does not change matrix
multiplication. -/
@[simp] theorem val_mul {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (A B : WrappedMatrix n N) :
    (A * B).val = A.val * B.val :=
  rfl

/-- Helper for Chapter01 Theorem 1.2.5: wrapping does not change the identity
matrix. -/
@[simp] theorem val_one {n : ℕ} {N : Matrix (Fin n) (Fin n) ℝ → ℝ} :
    (1 : WrappedMatrix n N).val = 1 :=
  rfl

/-- Helper for Chapter01 Theorem 1.2.5: the wrapper is linearly equivalent to
the ordinary matrix space. -/
def linearEquiv (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    WrappedMatrix n N ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := WrappedMatrix.val
  invFun := fun A ↦ ⟨A⟩
  left_inv := by
    intro A
    cases A
    rfl
  right_inv := by
    intro A
    rfl
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro a A
    rfl

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped matrix space is
finite-dimensional because it is linearly equivalent to the standard
finite-dimensional matrix space. -/
instance instFiniteDimensional (n : ℕ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    FiniteDimensional ℝ (WrappedMatrix n N) := by
  exact (linearEquiv n N).symm.finiteDimensional

/-- Helper for Chapter01 Theorem 1.2.5: once `N` satisfies the matrix-norm
axioms, it defines the ambient norm on the wrapped matrix space. -/
noncomputable instance instNormedAddCommGroup {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℝ → ℝ} [hNorm : IsMatrixNorm N] :
    NormedAddCommGroup (WrappedMatrix n N) := by
  let p : AddGroupNorm (WrappedMatrix n N) :=
    { toFun := fun A ↦ N A.val
      map_zero' := by
        simpa using (hNorm.eq_zero_iff (0 : Matrix (Fin n) (Fin n) ℝ)).2 rfl
      add_le' := fun A B ↦ by
        simpa using hNorm.add_le A.val B.val
      neg' := fun A ↦ by
        simpa using hNorm.smul (-1) A.val
      eq_zero_of_map_eq_zero' := fun A hA ↦ by
        have hVal : A.val = 0 := (hNorm.eq_zero_iff A.val).1 hA
        cases A
        cases hVal
        rfl }
  exact AddGroupNorm.toNormedAddCommGroup p

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped matrix space is a normed
`ℝ`-vector space because the norm `N` is absolutely homogeneous. -/
noncomputable instance instNormedSpace {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℝ → ℝ} [hNorm : IsMatrixNorm N] :
    NormedSpace ℝ (WrappedMatrix n N) where
  norm_smul_le := fun a A ↦ by
    change N (a • A.val) ≤ |a| * N A.val
    simpa using le_of_eq (hNorm.smul a A.val)

/-- Helper for Chapter01 Theorem 1.2.5: the wrapped ambient norm is
submultiplicative whenever the source matrix norm `N` is submultiplicative. -/
noncomputable instance instNormedRing {n : ℕ}
    {N : Matrix (Fin n) (Fin n) ℝ → ℝ} [hNorm : IsMatrixNorm N]
    [hSub : MatrixNormSubmultiplicative N] :
    NormedRing (WrappedMatrix n N) := by
  refine
    { (inferInstance : Ring (WrappedMatrix n N)),
      (inferInstance : NormedAddCommGroup (WrappedMatrix n N)) with
      norm_mul_le := fun A B ↦ ?_ }
  change N (A.val * B.val) ≤ N A.val * N B.val
  simpa using hSub.mul_le A.val B.val

end WrappedMatrix

/-- Helper for Chapter01 Theorem 1.2.5: under the wrapped ambient norm, the
geometric series for `E` gives both the inverse formula for `1 - E` and the
standard Neumann-series norm bound. -/
theorem oneSubGeometricCore
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (hN_one : N 1 = 1) (E : Matrix (Fin n) (Fin n) ℝ) (hE : N E < 1) :
    IsUnit (1 - E) ∧ (1 - E)⁻¹ = ∑' k : ℕ, E ^ k ∧
      N ((1 - E)⁻¹) ≤ 1 / (1 - N E) := by
  -- Local instance justification (wrapped norm): the helper uses the explicit
  -- source-facing norm hypotheses as the instance inputs needed by the wrapped
  -- Banach-ring API.
  letI : IsMatrixNorm N := hNorm
  -- Local instance justification (wrapped norm): submultiplicativity must also
  -- be available as an instance so the wrapped space carries a normed-ring
  -- structure.
  letI : MatrixNormSubmultiplicative N := hSub
  let Ew : WrappedMatrix n N := ⟨E⟩
  let e := WrappedMatrix.linearEquiv (n := n) (N := N)
  -- Transport infinite sums through the linear equivalence between wrapped and
  -- ordinary matrices.
  have hcont_e : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
  have hcont_esymm : Continuous e.symm :=
    LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
  have hEw : ‖Ew‖ < 1 := by
    change N Ew.val < 1
    simpa [Ew] using hE
  have htsum_map : e (∑' k : ℕ, Ew ^ k) = ∑' k : ℕ, e (Ew ^ k) := by
    simpa using
      Function.LeftInverse.map_tsum (fun k : ℕ ↦ Ew ^ k)
        (g := e) hcont_e hcont_esymm e.left_inv
  have hpow_apply : ∀ k : ℕ, e (Ew ^ k) = E ^ k := by
    intro k
    change (Ew ^ k).val = E ^ k
    induction k with
    | zero =>
        simp [Ew]
    | succ k hk =>
        simp [pow_succ, Ew, hk]
  have hval_tsum : (∑' k : ℕ, Ew ^ k).val = ∑' k : ℕ, E ^ k := by
    change e (∑' k : ℕ, Ew ^ k) = ∑' k : ℕ, E ^ k
    simpa [hpow_apply] using htsum_map
  have hrightw : (1 - Ew) * ∑' k : ℕ, Ew ^ k = 1 := mul_neg_geom_series Ew hEw
  have hright : (1 - E) * ∑' k : ℕ, E ^ k = 1 := by
    -- Read the wrapped right-inverse identity back in the ordinary matrix ring.
    simpa [hval_tsum, Ew, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      congrArg WrappedMatrix.val hrightw
  have hUnit : IsUnit (1 - E) := isUnit_iff_exists_inv.mpr ⟨∑' k : ℕ, E ^ k, hright⟩
  have hInv : (1 - E)⁻¹ = ∑' k : ℕ, E ^ k := Matrix.inv_eq_right_inv hright
  have hboundw :
      ‖∑' k : ℕ, Ew ^ k‖ ≤ ‖(1 : WrappedMatrix n N)‖ - 1 + (1 - ‖Ew‖)⁻¹ :=
    tsum_geometric_le_of_norm_lt_one Ew hEw
  have hnorm_tsum : ‖∑' k : ℕ, Ew ^ k‖ = N (∑' k : ℕ, E ^ k) := by
    -- Apply `N` to the transported sum identity to convert the wrapped norm
    -- bound back to the original matrix norm.
    change N (∑' k : ℕ, Ew ^ k).val = N (∑' k : ℕ, E ^ k)
    simpa using congrArg N hval_tsum
  have hnorm_one : ‖(1 : WrappedMatrix n N)‖ = 1 := by
    change N (1 : Matrix (Fin n) (Fin n) ℝ) = 1
    simpa using hN_one
  have hnorm_Ew : ‖Ew‖ = N E := by
    change N Ew.val = N E
    simp [Ew]
  have hbound : N (∑' k : ℕ, E ^ k) ≤ 1 / (1 - N E) := by
    rw [← hnorm_tsum]
    rw [hnorm_one, hnorm_Ew] at hboundw
    simpa [div_eq_mul_inv] using hboundw
  exact ⟨hUnit, hInv, by simpa [hInv] using hbound⟩

/-- Helper for Chapter01 Theorem 1.2.5: if `N E < 1`, then the geometric series
`∑ E^k` is summable in the ordinary matrix topology as well. -/
theorem oneSubGeometricSummable
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : N E < 1) :
    Summable (fun k : ℕ ↦ E ^ k) := by
  -- Local instance justification (wrapped norm): summability is first obtained
  -- in the wrapped norm where `N` is the ambient norm.
  letI : IsMatrixNorm N := hNorm
  -- Local instance justification (wrapped norm): the geometric-series theorem
  -- still needs the wrapped normed-ring structure built from submultiplicativity.
  letI : MatrixNormSubmultiplicative N := hSub
  let Ew : WrappedMatrix n N := ⟨E⟩
  let e := WrappedMatrix.linearEquiv (n := n) (N := N)
  have hcont_e : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
  have hEw : ‖Ew‖ < 1 := by
    change N Ew.val < 1
    simpa [Ew] using hE
  have hpow_apply : ∀ k : ℕ, e (Ew ^ k) = E ^ k := by
    intro k
    change (Ew ^ k).val = E ^ k
    induction k with
    | zero =>
        simp [Ew]
    | succ k hk =>
        simp [pow_succ, Ew, hk]
  -- Map the wrapped geometric series to the standard matrix topology.
  have hsumMap : Summable (fun k : ℕ ↦ e (Ew ^ k)) := by
    change Summable (e ∘ fun k : ℕ ↦ Ew ^ k)
    exact (summable_geometric_of_norm_lt_one hEw).map e hcont_e
  simpa [hpow_apply] using hsumMap

/-- Helper for Chapter01 Theorem 1.2.5: the perturbation term `1 - A⁻¹ * B` is
the negation of `A⁻¹ * (B - A)`, so both expressions have the same `N`-norm. -/
theorem perturbationErrorNorm_eq
    (hNorm : IsMatrixNorm N) (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) :
    N (1 - A⁻¹ * B) = N (A⁻¹ * (B - A)) := by
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hrewrite : 1 - A⁻¹ * B = -(A⁻¹ * (B - A)) := by
    -- Normalize the perturbation into the `1 - E` shape used by the
    -- Neumann-series core.
    calc
      1 - A⁻¹ * B = -(A⁻¹ * B - 1) := by
        simp [sub_eq_add_neg, add_comm]
      _ = -(A⁻¹ * (B - A)) := by
        rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hA_det]
  rw [hrewrite]
  simpa using hNorm.smul (-1) (A⁻¹ * (B - A))

/-- Consequence of Chapter01 Theorem 1.2.5 (1): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1` and `N E < 1`, then `1 - E` is
nonsingular. -/
theorem vonNeumannLemma_one_sub_isUnit
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (hN_one : N 1 = 1) (E : Matrix (Fin n) (Fin n) ℝ) (hE : N E < 1) :
    IsUnit (1 - E) := by
  -- Extract the invertibility component from the wrapped Neumann-series core.
  exact (oneSubGeometricCore (N := N) hNorm hSub hN_one E hE).1

/-- Consequence of Chapter01 Theorem 1.2.5 (2): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1` and `N E < 1`, then
`(1 - E)⁻¹ = ∑' k : ℕ, E ^ k`. -/
theorem vonNeumannLemma_inv_one_sub_eq_tsum
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (hN_one : N 1 = 1) (E : Matrix (Fin n) (Fin n) ℝ) (hE : N E < 1) :
    (1 - E)⁻¹ = ∑' k : ℕ, E ^ k := by
  -- Extract the inverse formula from the wrapped Neumann-series core.
  exact (oneSubGeometricCore (N := N) hNorm hSub hN_one E hE).2.1

/-- Consequence of Chapter01 Theorem 1.2.5 (3): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1` and `N E < 1`, then
`N ((1 - E)⁻¹) ≤ 1 / (1 - N E)`. -/
theorem vonNeumannLemma_norm_inv_one_sub_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (hN_one : N 1 = 1) (E : Matrix (Fin n) (Fin n) ℝ) (hE : N E < 1) :
    N ((1 - E)⁻¹) ≤ 1 / (1 - N E) := by
  -- Extract the norm estimate from the wrapped Neumann-series core.
  exact (oneSubGeometricCore (N := N) hNorm hSub hN_one E hE).2.2

/-- Consequence of Chapter01 Theorem 1.2.5 (4): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1`, if `A` is nonsingular, and if
`N (A⁻¹ * (B - A)) < 1`, then `B` is nonsingular. -/
theorem vonNeumannLemma_perturbation_isUnit
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) (hBA : N (A⁻¹ * (B - A)) < 1) :
    IsUnit B := by
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hE : N (1 - A⁻¹ * B) < 1 := by
    rwa [perturbationErrorNorm_eq (N := N) hNorm A B hA]
  have hAinvB : IsUnit (A⁻¹ * B) := by
    -- Apply the Neumann lemma to the normalized perturbation `1 - A⁻¹ * B`.
    simpa using
      vonNeumannLemma_one_sub_isUnit (N := N) hNorm hSub hN_one (1 - A⁻¹ * B) hE
  -- Reassemble `B` as `A * (A⁻¹ * B)` and multiply the two unit factors.
  simpa [Matrix.mul_nonsing_inv_cancel_left A B hA_det] using IsUnit.mul hA hAinvB

/-- Consequence of Chapter01 Theorem 1.2.5 (5): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1`, if `A` is nonsingular, and if
`N (A⁻¹ * (B - A)) < 1`, then
`B⁻¹ = ∑' k : ℕ, (1 - A⁻¹ * B) ^ k * A⁻¹`. -/
theorem vonNeumannLemma_perturbation_inv_eq_tsum
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) (hBA : N (A⁻¹ * (B - A)) < 1) :
    B⁻¹ = ∑' k : ℕ, (1 - A⁻¹ * B) ^ k * A⁻¹ := by
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hE : N (1 - A⁻¹ * B) < 1 := by
    rwa [perturbationErrorNorm_eq (N := N) hNorm A B hA]
  have hAinvB_inv :
      (A⁻¹ * B)⁻¹ = ∑' k : ℕ, (1 - A⁻¹ * B) ^ k := by
    -- The normalized perturbation has the same inverse formula as the basic
    -- `1 - E` case.
    simpa using
      vonNeumannLemma_inv_one_sub_eq_tsum (N := N) hNorm hSub hN_one (1 - A⁻¹ * B) hE
  -- Rewrite `B` as `A * (A⁻¹ * B)` and pull the fixed right factor through the
  -- infinite sum.
  calc
    B⁻¹ = (A * (A⁻¹ * B))⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_left A B hA_det]
    _ = (A⁻¹ * B)⁻¹ * A⁻¹ := Matrix.mul_inv_rev A (A⁻¹ * B)
    _ = (∑' k : ℕ, (1 - A⁻¹ * B) ^ k) * A⁻¹ := by rw [hAinvB_inv]
    _ = ∑' k : ℕ, (1 - A⁻¹ * B) ^ k * A⁻¹ := by
      have hsummable :
          Summable (fun k : ℕ ↦ (1 - A⁻¹ * B) ^ k) :=
        oneSubGeometricSummable (N := N) hNorm hSub (1 - A⁻¹ * B) hE
      exact (hsummable.tsum_mul_right A⁻¹).symm

/-- Consequence of Chapter01 Theorem 1.2.5 (6): if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1`, if `A` is nonsingular, and if
`N (A⁻¹ * (B - A)) < 1`, then
`N B⁻¹ ≤ N A⁻¹ / (1 - N (A⁻¹ * (B - A)))`. -/
theorem vonNeumannLemma_perturbation_norm_inv_le
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N) (hN_one : N 1 = 1)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) (hBA : N (A⁻¹ * (B - A)) < 1) :
    N B⁻¹ ≤ N A⁻¹ / (1 - N (A⁻¹ * (B - A))) := by
  have hA_det : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hE : N (1 - A⁻¹ * B) < 1 := by
    rwa [perturbationErrorNorm_eq (N := N) hNorm A B hA]
  have hAinvB_bound :
      N ((A⁻¹ * B)⁻¹) ≤ 1 / (1 - N (A⁻¹ * (B - A))) := by
    -- Reuse the basic inverse bound after normalizing the perturbation into
    -- `1 - A⁻¹ * B`.
    simpa [perturbationErrorNorm_eq (N := N) hNorm A B hA] using
      vonNeumannLemma_norm_inv_one_sub_le
        (N := N) hNorm hSub hN_one (1 - A⁻¹ * B) hE
  -- Factor `B⁻¹` as `(A⁻¹ * B)⁻¹ * A⁻¹` and apply submultiplicativity once.
  calc
    N B⁻¹ = N ((A⁻¹ * B)⁻¹ * A⁻¹) := by
      rw [← Matrix.mul_inv_rev A (A⁻¹ * B), Matrix.mul_nonsing_inv_cancel_left A B hA_det]
    _ ≤ N ((A⁻¹ * B)⁻¹) * N A⁻¹ := hSub.mul_le _ _
    _ ≤ (1 / (1 - N (A⁻¹ * (B - A)))) * N A⁻¹ := by
      exact mul_le_mul_of_nonneg_right hAinvB_bound (hNorm.nonneg _)
    _ = N A⁻¹ / (1 - N (A⁻¹ * (B - A))) := by
      simpa [div_eq_mul_inv] using
        (mul_comm ((1 - N (A⁻¹ * (B - A)))⁻¹) (N A⁻¹))

/-- Chapter01 Theorem 1.2.5: if `N` is a submultiplicative matrix norm on
`Matrix (Fin n) (Fin n) ℝ`, with `N 1 = 1`, then the Neumann series gives the
inverse formula and inverse-norm bound for `1 - E` whenever `N E < 1`; moreover,
if `A` is nonsingular and `N (A⁻¹ * (B - A)) < 1`, then `B` is nonsingular with
the corresponding perturbation-series formula and norm bound for `B⁻¹`. -/
theorem vonNeumannLemma
    (hNorm : IsMatrixNorm N) (hSub : MatrixNormSubmultiplicative N)
    (hN_one : N 1 = 1) :
    (∀ E : Matrix (Fin n) (Fin n) ℝ, N E < 1 →
      IsUnit (1 - E) ∧
        (1 - E)⁻¹ = ∑' k : ℕ, E ^ k ∧
        N ((1 - E)⁻¹) ≤ 1 / (1 - N E)) ∧
    (∀ A B : Matrix (Fin n) (Fin n) ℝ, IsUnit A → N (A⁻¹ * (B - A)) < 1 →
      IsUnit B ∧
        B⁻¹ = ∑' k : ℕ, (1 - A⁻¹ * B) ^ k * A⁻¹ ∧
        N B⁻¹ ≤ N A⁻¹ / (1 - N (A⁻¹ * (B - A)))) := by
  constructor
  · intro E hE
    -- The basic Neumann-series conclusions are exactly the first three component theorems.
    exact ⟨
      vonNeumannLemma_one_sub_isUnit (N := N) hNorm hSub hN_one E hE,
      vonNeumannLemma_inv_one_sub_eq_tsum (N := N) hNorm hSub hN_one E hE,
      vonNeumannLemma_norm_inv_one_sub_le (N := N) hNorm hSub hN_one E hE⟩
  · intro A B hA hBA
    -- The perturbation conclusions are exactly the last three component theorems.
    exact ⟨
      vonNeumannLemma_perturbation_isUnit (N := N) hNorm hSub hN_one A B hA hBA,
      vonNeumannLemma_perturbation_inv_eq_tsum (N := N) hNorm hSub hN_one A B hA hBA,
      vonNeumannLemma_perturbation_norm_inv_le (N := N) hNorm hSub hN_one A B hA hBA⟩

end VonNeumannLemma

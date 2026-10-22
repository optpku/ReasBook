/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.Matrix.Order
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The identity matrix induces a normed additive group structure on real square matrices. -/
local instance matrixIdentityNormedAddCommGroup (N : ℕ) :
    NormedAddCommGroup (Matrix (Fin N) (Fin N) ℝ) :=
  (1 : Matrix (Fin N) (Fin N) ℝ).toMatrixNormedAddCommGroup Matrix.PosDef.one

/-- The identity matrix induces the trace inner product on real square matrices. -/
local instance matrixIdentityInnerProductSpace (N : ℕ) :
    InnerProductSpace ℝ (Matrix (Fin N) (Fin N) ℝ) :=
  (1 : Matrix (Fin N) (Fin N) ℝ).toMatrixInnerProductSpace Matrix.PosDef.one.posSemidef

-- Proof sketch: work in the Hilbert space of self-adjoint real matrices with the trace pairing
-- induced by the identity matrix. In this ambient space, testing dual-cone membership against rank
-- one matrices `x xᵀ` shows that the dual cone is again the cone of positive semidefinite
-- symmetric matrices.
/-- Helper for Example 6.26: on the self-adjoint real matrix subspace, the induced inner product
is the trace pairing. -/
lemma inner_eq_trace_mul_of_mem_selfAdjoint (N : ℕ)
    (A B : ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))) :
    @inner ℝ _ _ A B = Matrix.trace (B.1 * A.1) := by
  have hA : A.1.conjTranspose = A.1 := A.2
  -- The subtype inner product is inherited from the ambient trace inner product on matrices.
  change Matrix.trace (B.1 * 1 * A.1.conjTranspose) = Matrix.trace (B.1 * A.1)
  rw [hA]
  simp

/-- Helper for Example 6.26: the trace pairing of two positive semidefinite real matrices is
nonnegative. -/
lemma trace_mul_nonneg_of_posSemidef (N : ℕ) {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  open scoped MatrixOrder in
  have hBnonneg : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ B := hB.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hBnonneg
  have hB' : B = D.transpose * D := by
    simpa [Matrix.star_eq_conjTranspose] using hD
  have htrace : Matrix.trace (D * A * D.transpose) = Matrix.trace (A * B) := by
    -- Cycle the trace so the positive semidefinite matrix appears in the standard `D * A * Dᵀ` form.
    calc
      Matrix.trace (D * A * D.transpose)
          = Matrix.trace (D.transpose * D * A) := by rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (A * (D.transpose * D)) := by rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (A * B) := by simp [hB']
  have hnonneg : 0 ≤ Matrix.trace (D * A * D.transpose) := by
    -- Positive semidefiniteness is preserved under `D * A * Dᵀ`, and PSD traces are nonnegative.
    simpa [Matrix.mul_assoc] using (hA.mul_mul_conjTranspose_same D).trace_nonneg
  simpa [htrace] using hnonneg

/-- Helper for Example 6.26: the real rank-one matrix `x xᵀ` is self-adjoint. -/
lemma vecMulVec_self_isSelfAdjoint (N : ℕ) (x : Fin N → ℝ) :
    IsSelfAdjoint (Matrix.vecMulVec x x : Matrix (Fin N) (Fin N) ℝ) := by
  -- Entrywise symmetry reduces to commutativity of multiplication in `ℝ`.
  ext i j
  simp [Matrix.vecMulVec, mul_comm]

/-- Helper for Example 6.26: pairing a symmetric matrix against the rank-one tester `x xᵀ`
recovers the associated quadratic form. -/
lemma inner_vecMulVec_self_eq_dotProduct_mulVec (N : ℕ)
    (A : ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))) (x : Fin N → ℝ) :
    @inner ℝ _ _
        (⟨Matrix.vecMulVec x x, vecMulVec_self_isSelfAdjoint N x⟩ :
          ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))) A
      = dotProduct (star x) (A.1.mulVec x) := by
  have hmul : A.1 * Matrix.vecMulVec x x = Matrix.vecMulVec (A.1.mulVec x) x := by
    -- Multiplying by the rank-one tester turns the trace into the quadratic form of `A`.
    ext i j
    calc
      ∑ k, A.1 i k * (x k * x j)
          = ∑ k, (A.1 i k * x k) * x j := by
              congr with k
              ring
      _ = (∑ k, A.1 i k * x k) * x j := by rw [Finset.sum_mul]
      _ = A.1.mulVec x i * x j := by simp [Matrix.mulVec, dotProduct]
      _ = Matrix.vecMulVec (A.1.mulVec x) x i j := by simp [Matrix.vecMulVec]
  -- Rewrite the inner product as a trace, then identify the resulting rank-one trace.
  calc
    @inner ℝ _ _
        (⟨Matrix.vecMulVec x x, vecMulVec_self_isSelfAdjoint N x⟩ :
          ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))) A
        = Matrix.trace (A.1 * Matrix.vecMulVec x x) := by
            change Matrix.trace (A.1 * 1 * (Matrix.vecMulVec x x).conjTranspose) = _
            simp
    _ = Matrix.trace (Matrix.vecMulVec (A.1.mulVec x) x) := by rw [hmul]
    _ = dotProduct (A.1.mulVec x) x := by rw [Matrix.trace_vecMulVec]
    _ = dotProduct (star x) (A.1.mulVec x) := by
          rw [dotProduct_comm]
          simp

/-- Example 6.26: the cone of positive semidefinite matrices in the real symmetric matrix space
`𝕊^N`, modeled by the canonical self-adjoint submodule of `N × N` real matrices, is self-dual. -/
theorem posSemidefSymmetricMatrixCone_isSelfDual (N : ℕ) :
    ({A : ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) | A.1.PosSemidef} :
      Set ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))).IsSelfDual := by
  -- Rewrite self-duality directly through the source-facing dual and polar cones.
  rw [Set.isSelfDual_iff]
  ext A
  constructor
  · intro hA
    rw [Set.mem_dualCone_iff, Set.mem_polarCone_iff_forall_inner_nonpos]
    intro B hB
    -- Positive semidefinite matrices pair nonnegatively under the trace inner product.
    have hnonneg : 0 ≤ @inner ℝ _ _ B A := by
      rw [inner_eq_trace_mul_of_mem_selfAdjoint]
      exact trace_mul_nonneg_of_posSemidef N
        (show A.1.PosSemidef from hA)
        (show B.1.PosSemidef from hB)
    simpa [inner_neg_right] using hnonneg
  · intro hA
    have hpolar :
        -A ∈ Set.polarCone
          {B : ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) | B.1.PosSemidef} :=
      Set.mem_dualCone_iff.mp hA
    have hdual :
        ∀ B,
          B ∈ ({B : ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ)) | B.1.PosSemidef} :
            Set ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))) →
          0 ≤ @inner ℝ _ _ B A := by
      intro B hB
      have hnonpos := Set.mem_polarCone_iff_forall_inner_nonpos.mp hpolar B hB
      simpa [inner_neg_right] using hnonpos
    -- Test the dual inequality on rank-one PSD matrices to recover every quadratic form value.
    change A.1.PosSemidef
    exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg A.2 fun x ↦ by
      have hx :
          (⟨Matrix.vecMulVec x x, vecMulVec_self_isSelfAdjoint N x⟩ :
            ↥(selfAdjoint.submodule ℝ (Matrix (Fin N) (Fin N) ℝ))).1.PosSemidef := by
        simpa using (Matrix.posSemidef_vecMulVec_star_self x)
      have htest := hdual _ hx
      rw [inner_vecMulVec_self_eq_dotProduct_mulVec] at htest
      simpa using htest

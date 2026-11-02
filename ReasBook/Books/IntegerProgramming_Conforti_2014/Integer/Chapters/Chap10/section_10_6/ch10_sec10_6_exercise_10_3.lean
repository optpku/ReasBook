import Mathlib.Analysis.Matrix.Order

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixOrder

-- Domain sampling for this exercise:
-- * primary domain: positive semidefinite real matrices and their trace pairing
-- * core/canonical owner: `Matrix.PosSemidef`
-- * inspected upstream derived API:
--   `Matrix.PosSemidef.mul_mul_conjTranspose_same`,
--   `Matrix.PosSemidef.trace_nonneg`,
--   `CStarAlgebra.nonneg_iff_eq_star_mul_self`
-- * layer choice: source-facing theorem proved through the canonical matrix-order bridge

section Exercise103

variable {ι : Type*} [Fintype ι]

namespace Matrix.PosSemidef

/-- Exercise 10.3. If `A` and `B` are symmetric positive semidefinite real square matrices, then
`Matrix.trace (A * B)` is nonnegative. The source symmetry assumptions are already encoded by
`A.PosSemidef` and `B.PosSemidef`. -/
theorem trace_mul_nonneg
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have htrace : 0 ≤ Matrix.trace (C * A * Cᴴ) :=
    (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm] at htrace
  simpa [Matrix.mul_assoc] using htrace

end Matrix.PosSemidef

end Exercise103

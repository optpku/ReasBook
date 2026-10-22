/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix WithLp
open scoped Matrix.Norms.Frobenius

/-- Example 2.4: after identifying real `M × N` matrices with an iterated `L²` space, the inner
product is given by the trace formula `trace (Aᵀ B)`. -/
theorem matrixToHilbert_inner_eq_trace_transpose_mul
    (M N : ℕ) (A B : Matrix (Fin M) (Fin N) ℝ) :
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (fun j ↦ A i j)))
      (toLp 2 (fun i ↦ toLp 2 (fun j ↦ B i j))) = Matrix.trace (A.transpose * B) := by
  calc
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (fun j ↦ A i j)))
        (toLp 2 (fun i ↦ toLp 2 (fun j ↦ B i j)))
      = Matrix.trace (B * A.transpose) := by
          rw [PiLp.inner_apply, Matrix.trace]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using inner_matrix_row_row A B i i
    _ = Matrix.trace (A.transpose * B) := Matrix.trace_mul_comm B A.transpose

/-- Example 2.4: the canonical matrix norm on `Matrix (Fin M) (Fin N) ℝ` is the Frobenius norm,
written entrywise as the square root of the sum of the squares. -/
theorem matrixToHilbert_norm_eq_frobenius_formula
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) := by
  simp [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, sq]

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable {m n : ℕ}

#check (Matrix.frobeniusNormedAddCommGroup :
  NormedAddCommGroup (Matrix (Fin m) (Fin n) ℝ))

/-- Definition 1.33: the Frobenius norm of a real matrix is `√(Matrix.trace (Aᵀ * A))`. -/
theorem frobenius_norm_eq_sqrt_trace_transpose_mul (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖A‖ = √(Matrix.trace (Aᵀ * A)) := by
  rw [Matrix.frobenius_norm_def, trace_transpose_mul_eq_sum_entrywise_mul, Real.sqrt_eq_rpow]
  congr 1
  simp [pow_two]

/-- The trace `Matrix.trace (Aᵀ * A)` is the sum of the squares of the entries of `A`. -/
theorem trace_transpose_mul_eq_sum_sq_entries (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Aᵀ * A) = ∑ i, ∑ j, A i j ^ 2 := by
  simpa [pow_two] using
    (trace_transpose_mul_eq_sum_entrywise_mul (A := A) (B := A))

#check (frobenius_norm_eq_sqrt_trace_transpose_mul :
  ∀ A : Matrix (Fin m) (Fin n) ℝ, ‖A‖ = √(Matrix.trace (Aᵀ * A)))

#check (trace_transpose_mul_eq_sum_sq_entries :
  ∀ A : Matrix (Fin m) (Fin n) ℝ,
    Matrix.trace (Aᵀ * A) = ∑ i, ∑ j, A i j ^ 2)

end

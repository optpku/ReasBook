/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

section

variable (m n : ℕ)

/- Definition 1.29: the space `ℝ^{m × n}` is formalized as `Matrix (Fin m) (Fin n) ℝ`. The
textbook Frobenius pairing on this matrix space is canonically expressed by
`Matrix.trace (Aᵀ * B)`, and the bridge theorem below identifies that trace with the usual
entrywise double sum. -/
#check (Matrix (Fin m) (Fin n) ℝ)

variable {m n : ℕ}

namespace Matrix

/-- The nested `ℓ²` model used to transport the Frobenius inner product onto
`Matrix (Fin m) (Fin n) ℝ`. -/
private def frobeniusToLp (A : Matrix (Fin m) (Fin n) ℝ) :
    WithLp 2 (Fin m → WithLp 2 (Fin n → ℝ)) :=
  WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ A i j

/-- The real matrix space `ℝ^(m × n)` carries the canonical Frobenius inner product. -/
@[instance_reducible] def frobeniusInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin m) (Fin n) ℝ) := by
  letI : InnerProductSpace ℝ (WithLp 2 (Fin m → WithLp 2 (Fin n → ℝ))) := inferInstance
  refine
    { inner := fun A B ↦ inner ℝ (frobeniusToLp A) (frobeniusToLp B)
      norm_sq_eq_re_inner := ?_
      conj_inner_symm := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro A
    change ‖frobeniusToLp A‖ ^ 2 = RCLike.re (inner ℝ (frobeniusToLp A) (frobeniusToLp A))
    exact norm_sq_eq_re_inner (frobeniusToLp A)
  · intro A B
    change star (inner ℝ (frobeniusToLp B) (frobeniusToLp A)) =
        inner ℝ (frobeniusToLp A) (frobeniusToLp B)
    exact inner_conj_symm (frobeniusToLp A) (frobeniusToLp B)
  · intro A B C
    simpa [frobeniusToLp] using
      inner_add_left (frobeniusToLp A) (frobeniusToLp B) (frobeniusToLp C)
  · intro A B r
    simpa [frobeniusToLp] using
      inner_smul_left (frobeniusToLp A) (frobeniusToLp B) r

namespace Norms.Frobenius

attribute [scoped instance] Matrix.frobeniusInnerProductSpace

end Norms.Frobenius

end Matrix

-- Proof sketch: expand `Matrix.trace` and `Matrix.mul_apply`; the diagonal entry of `Aᵀ * B` at
-- `j` is `∑ i, A i j * B i j`, and then commute the outer and inner finite sums.
/-- The Frobenius pairing on real matrices is the trace formula `Tr(Aᵀ B)`, equivalently the sum
of the entrywise products. -/
theorem trace_transpose_mul_eq_sum_entrywise_mul (A B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Aᵀ * B) = ∑ i, ∑ j, A i j * B i j := by
  rw [show Matrix.trace (Aᵀ * B) = ∑ j, ∑ i, A i j * B i j by
    simp [Matrix.trace, Matrix.mul_apply]]
  rw [Finset.sum_comm]

namespace Matrix

/-- The Frobenius inner product on real matrices is the trace pairing `Tr(Bᵀ A)`. -/
theorem inner_eq_trace_transpose_mul (A B : Matrix (Fin m) (Fin n) ℝ) :
    inner ℝ A B = Matrix.trace (Bᵀ * A) := by
  rw [trace_transpose_mul_eq_sum_entrywise_mul]
  change inner ℝ (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ A i j)
      (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun j ↦ B i j) =
    ∑ i, ∑ j, B i j * A i j
  rw [PiLp.inner_apply]
  have hrow :
      ∀ i,
        inner ℝ (WithLp.toLp 2 fun j ↦ A i j) (WithLp.toLp 2 fun j ↦ B i j) =
          ∑ j, B i j * A i j := by
    intro i
    simpa [dotProduct, mul_comm] using
      EuclideanSpace.inner_toLp_toLp (fun j ↦ A i j) (fun j ↦ B i j)
  simp [hrow]

end Matrix

end

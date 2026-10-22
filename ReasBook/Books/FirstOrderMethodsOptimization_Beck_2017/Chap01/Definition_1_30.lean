/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix
open Matrix

noncomputable section

section

variable {n : ℕ}

/- Definition 1.30: the textbook notation `𝕊^n` is the canonical self-adjoint submodule of real
`n × n` matrices. This abbreviation is the stable owner vocabulary reused throughout the chapter
for the symmetric-matrix space. -/
abbrev symmetricMatrices (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℝ)

/- Definition 1.30: `𝕊^n` is the real vector subspace of `n × n` matrices consisting of the
symmetric matrices. This is the canonical self-adjoint submodule of the real matrix star module. -/
#check (symmetricMatrices n : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))

-- Proof sketch: membership in the canonical self-adjoint submodule is `star A = A`; for real
-- matrices, `star` is conjugate transpose, which is just transpose.
/-- A real `n × n` matrix belongs to `𝕊^n` exactly when it is equal to its transpose. -/
theorem mem_symmetricMatrices_iff {A : Matrix (Fin n) (Fin n) ℝ} :
    A ∈ symmetricMatrices n ↔ Aᵀ = A := by
  change IsSelfAdjoint A ↔ Aᵀ = A
  rw [← Matrix.isHermitian_iff_isSelfAdjoint]
  simp [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

-- Proof sketch: apply the ambient Frobenius-pairing formula from Definition 1.29 to the
-- underlying matrices and rewrite `Aᵀ` as `A` using self-adjointness.
/-- On `𝕊^n`, the textbook dot product is the trace pairing `Tr(AB)`, equivalently the sum of the
entrywise products. -/
theorem matrixDotProduct_eq_sum_mul_symmetricMatrices
    (A B : symmetricMatrices n) :
    Matrix.trace ((A : Matrix (Fin n) (Fin n) ℝ) * (B : Matrix (Fin n) (Fin n) ℝ)) =
      ∑ i, ∑ j, (A : Matrix (Fin n) (Fin n) ℝ) i j * (B : Matrix (Fin n) (Fin n) ℝ) i j := by
  have hA : (A : Matrix (Fin n) (Fin n) ℝ)ᵀ = A := by
    change star (A : Matrix (Fin n) (Fin n) ℝ) = A
    exact A.property
  calc
    Matrix.trace ((A : Matrix (Fin n) (Fin n) ℝ) * (B : Matrix (Fin n) (Fin n) ℝ)) =
        Matrix.trace ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * (B : Matrix (Fin n) (Fin n) ℝ)) := by
          rw [hA]
    _ = ∑ i, ∑ j, (A : Matrix (Fin n) (Fin n) ℝ) i j * (B : Matrix (Fin n) (Fin n) ℝ) i j :=
      trace_transpose_mul_eq_sum_entrywise_mul
        (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)

end

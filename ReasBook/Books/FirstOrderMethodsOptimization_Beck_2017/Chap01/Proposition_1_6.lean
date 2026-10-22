/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section

variable {m n k : ℕ}

-- Proof sketch: use the canonical owner abstraction `LinearMap.toMatrix` with respect to the
-- standard bases `Matrix.stdBasis` on the domain and `Pi.basisFun` on the codomain. The `r`th row
-- of that matrix gives the coefficients of the representing matrix `A r`; expanding `X` in the
-- standard matrix basis yields the entrywise sum, which is then identified with the trace formula.
/-- Proposition 1.6: every linear map from `ℝ^{m × n}` to `ℝ^k` is given coordinatewise by
Frobenius pairings with a family of matrices. -/
theorem exists_matrix_trace_representation
    (𝒜 : Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ A : Fin k → Matrix (Fin m) (Fin n) ℝ,
      ∀ X, 𝒜 X = fun r ↦ Matrix.trace ((A r)ᵀ * X) := by
  classical
  let bM := Matrix.stdBasis ℝ (Fin m) (Fin n)
  let bK := Pi.basisFun ℝ (Fin k)
  let A : Fin k → Matrix (Fin m) (Fin n) ℝ :=
    fun r i j ↦ (LinearMap.toMatrix bM bK 𝒜) r (i, j)
  refine ⟨A, ?_⟩
  intro X
  ext r
  have hsingle (i : Fin m) (j : Fin n) :
      Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℝ) := by
    simp [Matrix.smul_single]
  have hX :
      𝒜 X r = 𝒜 (∑ i, ∑ j, Matrix.single i j (X i j)) r := by
    symm
    simpa using congrArg (fun Y : Matrix (Fin m) (Fin n) ℝ ↦ 𝒜 Y r) (Matrix.matrix_eq_sum_single X).symm
  calc
    𝒜 X r = 𝒜 (∑ i, ∑ j, Matrix.single i j (X i j)) r := hX
    _ = ∑ i, ∑ j, 𝒜 (Matrix.single i j (X i j)) r := by
      simp
    _ = ∑ i, ∑ j, X i j * 𝒜 (Matrix.single i j (1 : ℝ)) r := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hsingle, map_smul]
      simp
    _ = ∑ i, ∑ j, A r i j * X i j := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show 𝒜 (Matrix.single i j (1 : ℝ)) r = A r i j by
        simp [A, bM, bK, LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single]]
      rw [mul_comm]
    _ = Matrix.trace ((A r)ᵀ * X) := by
      rw [show Matrix.trace ((A r)ᵀ * X) = ∑ j, ∑ i, A r i j * X i j by
        simp [Matrix.trace, Matrix.mul_apply]]
      rw [Finset.sum_comm]

end

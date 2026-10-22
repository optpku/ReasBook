/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_25
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

section

variable {m n : ℕ}

/- Proposition 3.30 is a `bridge/view` item in the chapter's max-affine subdifferential API. The
source-facing statement is the active-face weight criterion for optimality, while the matrix
version below is only a coordinate rewrite of the same condition using the owner matrix action
`Aᵀ *ᵥ weights`. -/

/- Proposition 3.30: for the max-affine function
`f(x) = max_i (a_i^T x + b_i)` on `ℝ^n`, the vector-side subdifferential at `x` is exactly the
set of convex combinations of the active slope vectors `a_i`, equivalently the image of the active
face of the standard simplex under the barycentric combination map. -/
recall isMinOn_univ_iff_zero_mem_subdifferentialAt
recall subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace

-- Proof sketch: a point `x` is a global minimizer exactly when the zero vector belongs to the
-- vector-side subdifferential of the max-affine objective at `x`. Then specialize the recalled
-- max-affine subdifferential formula at `g = 0`, which turns membership of the subdifferential
-- into the existence of simplex weights in the active coordinate face of the affine-value vector
-- whose weighted sum of active slopes is zero.
/-- A point `x` minimizes the max-affine objective globally if and only if there are simplex
weights in the active coordinate face of the affine-value vector
`i ↦ a i ⬝ᵥ x + b i` whose weighted sum of the slope vectors is zero. -/
theorem isMinOn_piecewiseLinearMax_iff_exists_activeWeights
    (hm : 0 < m) (a : Fin m → (Fin n → ℝ)) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    IsMinOn (piecewiseLinearMax a b) Set.univ x ↔
      ∃ weights : Fin m → ℝ,
        weights ∈ activeCoordinateFace (fun i ↦ a i ⬝ᵥ x + b i) ∧
          (∑ i, weights i • a i) = 0 := by
  rw [isMinOn_univ_iff_zero_mem_subdifferentialAt]
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [subdifferentialAt_piecewiseLinearMax_eq_image_activeCoordinateFace hm a b x]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨_, ⟨weights, hweights, rfl⟩, hzero⟩
    exact ⟨weights, hweights,
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap).map_eq_zero_iff.mp
        hzero⟩
  · rintro ⟨weights, hweights, hzero⟩
    exact ⟨∑ i, weights i • a i, ⟨weights, hweights, rfl⟩,
      ((dotProductEquiv ℝ (Fin n)).trans LinearMap.toContinuousLinearMap).map_eq_zero_iff.mpr
        hzero⟩

-- Proof sketch: rewrite the weighted-sum condition `∑ i, λ i • A i = 0` as the matrix equation
-- `Aᵀ *ᵥ λ = 0`, and note that
-- `activeCoordinateFace (fun i ↦ A i ⬝ᵥ x + b i)` already packages the simplex
-- constraint together with support on the active affine pieces.
/- Matrix form of the max-affine optimality criterion: the minimizing weights lie in the active
coordinate face of the affine-value vector and annihilate the transpose of the slope matrix. -/
theorem isMinOn_piecewiseLinearMax_matrix_iff_exists_activeWeights
    (hm : 0 < m) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    IsMinOn (piecewiseLinearMax (fun i ↦ A i) b) Set.univ x ↔
      ∃ weights : Fin m → ℝ,
        weights ∈ activeCoordinateFace (fun i ↦ A i ⬝ᵥ x + b i) ∧
          Aᵀ *ᵥ weights = 0 := by
  rw [isMinOn_piecewiseLinearMax_iff_exists_activeWeights hm (fun i ↦ A i) b x]
  constructor
  · rintro ⟨weights, hweights, hsum⟩
    refine ⟨weights, hweights, ?_⟩
    simpa [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] using hsum
  · rintro ⟨weights, hweights, hmul⟩
    refine ⟨weights, hweights, ?_⟩
    simpa [Matrix.mulVec_transpose, Matrix.vecMul_eq_sum] using hmul

end

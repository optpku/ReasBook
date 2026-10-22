/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

noncomputable section

open scoped BigOperators

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `lean_leansearch` surfaced abstract tensor-product contraction APIs, but
-- this item is a coordinate definition on `ℝ^n`, and nearby Chapter 6 files use the explicit
-- `EuclideanSpace ℝ (Fin n)` / matrix surface for finite-dimensional data.

/-- Chapter06 Definition 6.3.1: a third-order tensor on `ℝ^n` is represented by its coordinate
entries `T i j k : ℝ`, equivalently by its `n` horizontal faces indexed by `i : Fin n`. -/
abbrev ThirdOrderTensor (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- The `i`-th horizontal face of a third-order tensor is the matrix with entries
`T i j k`. -/
def ThirdOrderTensor.horizontalFace (T : ThirdOrderTensor n) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j k ↦ T i j k

/-- The entries of the `i`-th horizontal face are the corresponding tensor coordinates. -/
theorem ThirdOrderTensor.horizontalFace_apply
    (T : ThirdOrderTensor n) (i j k : Fin n) :
    T.horizontalFace i j k = T i j k := rfl

/-- The tensor-vector-vector contraction `T v w` is the vector whose `i`-th component is
`vᵀ (T.horizontalFace i) w`. -/
def ThirdOrderTensor.mulVecVec (T : ThirdOrderTensor n) (v w : Point) : Point :=
  WithLp.toLp 2 fun i ↦ dotProduct v ((T.horizontalFace i).mulVec w)

/-- Evaluating `T.mulVecVec v w` at `i` gives the corresponding face contraction
`vᵀ (T.horizontalFace i) w`. -/
theorem ThirdOrderTensor.mulVecVec_apply
    (T : ThirdOrderTensor n) (v w : Point) (i : Fin n) :
    T.mulVecVec v w i = dotProduct v ((T.horizontalFace i).mulVec w) := rfl

/-- Expanding the `i`-th component of `T.mulVecVec v w` gives the coordinate formula
`∑ j, ∑ k, T i j k * v j * w k`. -/
theorem ThirdOrderTensor.mulVecVec_apply_eq_sum
    (T : ThirdOrderTensor n) (v w : Point) (i : Fin n) :
    T.mulVecVec v w i = ∑ j : Fin n, ∑ k : Fin n, T i j k * v j * w k := by
  rw [ThirdOrderTensor.mulVecVec_apply, Matrix.dot_mulVec_eq_sum_sum]
  simp_rw [ThirdOrderTensor.horizontalFace_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  ac_rfl

/-- The Frobenius norm of a third-order tensor is the `ℓ²` norm of its coordinate array. -/
def ThirdOrderTensor.frobeniusNorm (T : ThirdOrderTensor n) : ℝ :=
  ‖WithLp.toLp 2 T‖

/-- Unfolding `T.frobeniusNorm` gives the ambient `ℓ²` norm on the tensor coordinates. -/
theorem ThirdOrderTensor.frobeniusNorm_eq (T : ThirdOrderTensor n) :
    T.frobeniusNorm = ‖WithLp.toLp 2 T‖ := rfl

end

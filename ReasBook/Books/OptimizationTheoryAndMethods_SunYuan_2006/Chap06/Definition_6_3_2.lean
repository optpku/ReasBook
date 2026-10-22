/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_3_1
import Mathlib.Data.Matrix.Mul

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Semantic recall: `lean_leansearch` surfaced `Matrix.vecMulVec` and
-- `Matrix.rank_vecMulVec_le` as the canonical rank-one matrix API. This file keeps the source's
-- third-order tensor as the concrete owner from Definition 6.3.1 and expresses its horizontal
-- faces through `Matrix.vecMulVec`.

namespace ThirdOrderTensor

/-- Chapter06 Definition 6.3.2 (1): the third-order rank-one tensor `u ⊗ v ⊗ w` is the tensor
with entries `T i j k = u i * v j * w k`. -/
def rankOne (u v w : Point) : ThirdOrderTensor n :=
  fun i j k ↦ u i * v j * w k

scoped[ThirdOrderTensor] notation:max "⟪" u ", " v ", " w "⟫₃" => rankOne u v w

open scoped ThirdOrderTensor

/-- Unfolding `⟪u, v, w⟫₃` gives the component formula `u i * v j * w k`. -/
@[simp] theorem rankOne_apply (u v w : Point) (i j k : Fin n) :
    (⟪u, v, w⟫₃) i j k = u i * v j * w k := rfl

/-- Reading the `i`-th horizontal face of `⟪u, v, w⟫₃` returns the corresponding coordinate
formula `u i * v j * w k`. -/
@[simp] theorem horizontalFace_rankOne_apply
    (u v w : Point) (i j k : Fin n) :
    ((⟪u, v, w⟫₃).horizontalFace i) j k = u i * v j * w k := rfl

/-- Chapter06 Definition 6.3.2 (2): the `i`-th horizontal face of `⟪u, v, w⟫₃` is the rank-one
matrix `u i • Matrix.vecMulVec v w`. -/
theorem horizontalFace_rankOne (u v w : Point) (i : Fin n) :
    (⟪u, v, w⟫₃).horizontalFace i = u i • Matrix.vecMulVec v w := by
  ext j k
  simp [Matrix.vecMulVec_apply, mul_assoc]

end ThirdOrderTensor

end

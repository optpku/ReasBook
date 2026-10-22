/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

/- Definition 1.17: for a positive definite matrix `Q`, the `Q`-inner product on `ℝ^n` is
canonically given by the inner-product-space structure induced by `Matrix.toInnerProductSpace`;
its value on `x` and `y` is the matrix expression `xᵀ Q y`. -/
#check Matrix.toInnerProductSpace

variable {n : ℕ}

namespace Matrix

/-- The source-facing `Q`-inner product on `ℝ^n` induced by the canonical owner
`Matrix.toInnerProductSpace`. -/
abbrev qInner (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x y : Fin n → ℝ) : ℝ :=
  letI := Q.toInnerProductSpace hQ.posSemidef
  inner ℝ x y

end Matrix

-- Proof sketch: unfold `Matrix.toInnerProductSpace`; over `ℝ`, the induced inner product is the
-- matrix expression `xᵀ Q y`, which is `dotProduct x (Q.mulVec y)` on `Fin n → ℝ`.
/-- For a positive definite real matrix, the induced inner product is the matrix formula
`xᵀ Q y`. -/
theorem inner_eq_dotProduct_mulVec_of_posDef (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (x y : Fin n → ℝ) :
    letI := Q.toInnerProductSpace hQ.posSemidef
    inner ℝ x y = dotProduct x (Q.mulVec y) := by
  change dotProduct (Q.mulVec y) x = dotProduct x (Q.mulVec y)
  simp [dotProduct_comm]

-- Proof sketch: this is `inner_eq_dotProduct_mulVec_of_posDef` rewritten on the source-facing
-- owner `Matrix.qInner`.
/-- The source-facing `Q`-inner product agrees with the matrix formula `xᵀ Q y`. -/
theorem qInner_eq_dotProduct_mulVec_of_posDef (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (x y : Fin n → ℝ) :
    Q.qInner hQ x y = dotProduct x (Q.mulVec y) := by
  simpa [Matrix.qInner] using inner_eq_dotProduct_mulVec_of_posDef Q hQ x y

end

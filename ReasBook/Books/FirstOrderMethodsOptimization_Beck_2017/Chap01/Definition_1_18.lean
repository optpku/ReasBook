/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_17

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

namespace Matrix

/-- The source-facing `Q`-norm on `ℝ^n` induced by the canonical owner
`Matrix.toNormedAddCommGroup`. -/
abbrev qNorm (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) : ℝ :=
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI := Q.toInnerProductSpace hQ.posSemidef
  ‖x‖

end Matrix

/- Definition 1.18: when `ℝ^n` is endowed with the dot product, the associated Euclidean norm
is the canonical `l_2`-norm on `EuclideanSpace ℝ (Fin n)`, provided by `EuclideanSpace.norm_eq`. -/
#check (EuclideanSpace.norm_eq : ∀ x : EuclideanSpace ℝ (Fin n),
  ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ (2 : ℕ)))

-- Proof sketch: start from `EuclideanSpace.norm_eq` and simplify the real coordinate terms using
-- `Real.norm_eq_abs`, so that `|x i|^2 = x i^2`.
/-- The Euclidean norm on `ℝ^n` is the square root of the sum of the coordinate squares. -/
theorem euclideanSpace_norm_eq_sqrt_sum_sq (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ = √(∑ i, x i ^ (2 : ℕ)) := by
  simpa [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x

/- Definition 1.18: for a positive definite matrix `Q`, the induced norm on `ℝ^n` is the
source-facing `Q`-norm obtained from the owner `Matrix.toNormedAddCommGroup`. -/
#check Matrix.toNormedAddCommGroup

-- Proof sketch: rewrite the induced norm as `√⟪x, x⟫`, and then use the matrix
-- formula for the `Q`-inner product to identify `⟪x, x⟫` with `xᵀ Q x = dotProduct x (Q.mulVec x)`.
/-- If `ℝ^n` is endowed with the `Q`-inner product associated to a positive definite matrix `Q`,
then the induced Euclidean norm is the `Q`-norm `√(xᵀ Q x)`. -/
theorem norm_eq_sqrt_dotProduct_mulVec_of_posDef (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef)
    (x : Fin n → ℝ) :
    let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
    letI := qSeminormed
    let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
    letI := qNormed
    letI : Norm (Fin n → ℝ) := qNormed.toNorm
    letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
    ‖x‖ = √(dotProduct x (Q.mulVec x)) := by
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI := Q.toInnerProductSpace hQ.posSemidef
  have h_norm := norm_eq_sqrt_real_inner x
  rw [inner_eq_dotProduct_mulVec_of_posDef Q hQ x x] at h_norm
  simpa using h_norm

-- Proof sketch: after installing the `Q`-weighted norm and inner-product structures, this is the
-- standard identity `‖x‖² = ⟪x, x⟫` rewritten on the source-facing owners.
/-- In the `Q`-geometry, the squared `Q`-norm is the `Q`-inner self-pairing. -/
theorem qNorm_sq_eq_qInner_self (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qNorm hQ x ^ (2 : ℕ) = Q.qInner hQ x x := by
  have hnorm :
      Q.qNorm hQ x = √(dotProduct x (Q.mulVec x)) := by
    let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
    letI := qSeminormed
    let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
    letI := qNormed
    letI : Norm (Fin n → ℝ) := qNormed.toNorm
    letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
    rw [Matrix.qNorm]
    change @Norm.norm (Fin n → ℝ) qNormed.toNorm x = √(dotProduct x (Q.mulVec x))
    simpa using norm_eq_sqrt_dotProduct_mulVec_of_posDef Q hQ x
  rw [hnorm, qInner_eq_dotProduct_mulVec_of_posDef Q hQ x x]
  exact Real.sq_sqrt (hQ.posSemidef.dotProduct_mulVec_nonneg x)

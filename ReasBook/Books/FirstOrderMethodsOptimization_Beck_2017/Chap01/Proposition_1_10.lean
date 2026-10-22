/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_18
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import Mathlib.Analysis.Normed.Module.FiniteDimension

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

namespace Matrix

/-- The dual norm of the Euclidean pairing functional `y ↦ xᵀ y` when `ℝ^n` is endowed with the
`Q`-norm induced by a positive definite matrix `Q`. -/
abbrev qDualNorm (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) : ℝ :=
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
  dualNorm (dotProductBilin ℝ ℝ x)

end Matrix

namespace Matrix

/-- The Euclidean pairing `xᵀ y` is represented in the `Q`-geometry by the vector `Q⁻¹ x`. -/
theorem qInner_invMulVec_eq_dotProduct
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x y : Fin n → ℝ) :
    Q.qInner hQ (Q⁻¹.mulVec x) y = dotProduct x y := by
  letI : Invertible Q := hQ.isUnit.invertible
  have hQsymm : Q.IsSymm := by
    simpa using hQ.1.eq
  have hQInvsymm : Q⁻¹.IsSymm := hQsymm.inv
  -- Rewrite the weighted inner product to the quadratic form and cancel `Q⁻¹ * Q = 1`.
  calc
    Q.qInner hQ (Q⁻¹.mulVec x) y = dotProduct (Q⁻¹.mulVec x) (Q.mulVec y) := by
      rw [qInner_eq_dotProduct_mulVec_of_posDef]
    _ = (Q⁻¹.mulVec x) ᵥ* Q ⬝ᵥ y := by
      rw [Matrix.dotProduct_mulVec]
    _ = x ᵥ* ((Q⁻¹)ᵀ * Q) ⬝ᵥ y := by
      rw [Matrix.vecMul_mulVec]
    _ = x ᵥ* (Q⁻¹ * Q) ⬝ᵥ y := by
      rw [hQInvsymm.eq]
    _ = x ᵥ* (1 : Matrix (Fin n) (Fin n) ℝ) ⬝ᵥ y := by
      rw [Matrix.inv_mul_of_invertible]
    _ = dotProduct x y := by
      rw [Matrix.vecMul_one]

end Matrix

/-- Helper for Proposition 1.10: the source-facing `Q`-norm is the quadratic-form square root. -/
private lemma qNorm_eq_sqrt_dotProduct_mulVec_of_posDef
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qNorm hQ x = Real.sqrt (dotProduct x (Q.mulVec x)) := by
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
  -- Unfold the source-facing owner and reuse the owner-level norm formula from Definition 1.18.
  rw [Matrix.qNorm]
  change @Norm.norm (Fin n → ℝ) qNormed.toNorm x = Real.sqrt (dotProduct x (Q.mulVec x))
  simpa using norm_eq_sqrt_dotProduct_mulVec_of_posDef Q hQ x

/-- Helper for Proposition 1.10: the `Q`-norm of `Q⁻¹ x` is `√(xᵀ Q⁻¹ x)`. -/
private lemma qNorm_invMulVec_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qNorm hQ (Q⁻¹.mulVec x) = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
  letI : Invertible Q := hQ.isUnit.invertible
  -- Route correction: normalize the source-facing `qNorm` first, then cancel `Q * Q⁻¹ = 1`.
  calc
    Q.qNorm hQ (Q⁻¹.mulVec x) =
        Real.sqrt (dotProduct (Q⁻¹.mulVec x) (Q.mulVec (Q⁻¹.mulVec x))) := by
      rw [qNorm_eq_sqrt_dotProduct_mulVec_of_posDef]
    _ = Real.sqrt (dotProduct (Q⁻¹.mulVec x) x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
    _ = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
      rw [dotProduct_comm]

/-- Helper for Proposition 1.10: a diagonal quadratic form expands to a weighted sum of squares. -/
private lemma dotProduct_diagonal_mulVec_eq_sum_weight_mul_sq
    (w x : Fin n → ℝ) :
    dotProduct x ((diagonal w).mulVec x) = ∑ i, w i * x i ^ (2 : ℕ) := by
  -- Expand the diagonal action and the dot product coordinatewise.
  simp [dotProduct, Matrix.mulVec_diagonal, pow_two, mul_left_comm]

/-- Helper for Proposition 1.10: the inverse diagonal quadratic form expands with reciprocal
weights. -/
private lemma dotProduct_invDiagonal_mulVec_eq_sum_invWeight_mul_sq
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (x : Fin n → ℝ) :
    dotProduct x ((diagonal w)⁻¹.mulVec x) = ∑ i, (w i)⁻¹ * x i ^ (2 : ℕ) := by
  have hwRingInverse : Ring.inverse w = fun i ↦ (w i)⁻¹ := by
    obtain ⟨u, hu⟩ : IsUnit w := by
      rw [Pi.isUnit_iff]
      intro i
      exact isUnit_iff_ne_zero.mpr (hw i).ne'
    ext i
    calc
      Ring.inverse w i = (↑u⁻¹ : Fin n → ℝ) i := by
        simpa [hu] using congrArg (fun f : Fin n → ℝ ↦ f i) (Ring.inverse_unit u)
      _ = (w i)⁻¹ := by
        simp [hu]
  -- Reduce the inverse diagonal matrix to the coordinatewise reciprocal diagonal.
  rw [Matrix.inv_diagonal, hwRingInverse]
  simp [dotProduct, Matrix.mulVec_diagonal, pow_two, mul_assoc, mul_comm]

/-- Helper for Proposition 1.10: the weighted dual norm of the Euclidean pairing functional is
the inverse quadratic-form square root. -/
private lemma qDualNorm_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qDualNorm hQ x = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
  -- Route correction: use direct upper and lower operator-norm bounds instead of the brittle
  -- owner-instance transport through Fréchet-Riesz.
  simpa [Matrix.qDualNorm, qSeminormed, qNormed] using
    (show dualNorm (dotProductBilin ℝ ℝ x) = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) from by
      letI : Invertible Q := hQ.isUnit.invertible
      let a := Real.sqrt (dotProduct x (Q⁻¹.mulVec x))
      have hnorm : ‖Q⁻¹.mulVec x‖ = a := by
        simpa [a] using qNorm_invMulVec_eq_sqrt_dotProduct_inv_mulVec Q hQ x
      have hbound :
          ∀ y : Fin n → ℝ,
            ‖LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ x) y‖ ≤ a * ‖y‖ := by
        intro y
        -- Rewrite the functional as the `Q`-inner product with `Q⁻¹ x` and apply Cauchy-Schwarz.
        have hrepr :
            LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ x) y =
              inner ℝ (Q⁻¹.mulVec x) y := by
          simp [qInner_invMulVec_eq_dotProduct Q hQ x y]
        rw [hrepr]
        calc
          |inner ℝ (Q⁻¹.mulVec x) y| ≤ ‖Q⁻¹.mulVec x‖ * ‖y‖ := abs_real_inner_le_norm _ _
          _ = a * ‖y‖ := by rw [hnorm]
      have hupper : dualNorm (dotProductBilin ℝ ℝ x) ≤ a := by
        rw [dualNorm]
        exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) hbound
      by_cases hx : x = 0
      · -- The zero functional has zero dual norm, so the formula is immediate.
        subst hx
        have hnonneg : 0 ≤ dualNorm (dotProductBilin ℝ ℝ (0 : Fin n → ℝ)) := by
          rw [dualNorm_eq_toContinuousLinearMap_norm]
          exact norm_nonneg _
        have ha_zero : a = 0 := by
          dsimp [a]
          simp
        exact le_antisymm (by simpa [ha_zero] using hupper) (by simpa [ha_zero] using hnonneg)
      · have ha_pos : 0 < a := by
          -- Positive definiteness makes the inverse quadratic form strictly positive
          -- away from zero.
          dsimp [a]
          exact Real.sqrt_pos.2 (hQ.inv.dotProduct_mulVec_pos hx)
        let z : Fin n → ℝ := a⁻¹ • Q⁻¹.mulVec x
        have hz_norm : ‖z‖ = 1 := by
          -- Normalize `Q⁻¹ x` to a unit vector in the weighted norm.
          rw [show z = a⁻¹ • Q⁻¹.mulVec x by rfl]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha_pos), hnorm,
            inv_mul_cancel₀ ha_pos.ne']
        have hz_apply : (dotProductBilin ℝ ℝ x) z = a := by
          -- The normalized witness attains the claimed dual norm value.
          have hQInvPosSemidef : (Q⁻¹).PosSemidef := hQ.inv.posSemidef
          calc
            (dotProductBilin ℝ ℝ x) z = dotProduct x z := rfl
            _ = a⁻¹ * dotProduct x (Q⁻¹.mulVec x) := by
              simp [z, dotProduct_smul]
            _ = a⁻¹ * a ^ (2 : ℕ) := by
              congr 1
              dsimp [a]
              symm
              exact Real.sq_sqrt (hQInvPosSemidef.dotProduct_mulVec_nonneg x)
            _ = a := by
              rw [pow_two, ← mul_assoc, inv_mul_cancel₀ ha_pos.ne', one_mul]
        have hlower : a ≤ dualNorm (dotProductBilin ℝ ℝ x) := by
          have htest := abs_apply_le_dual_norm_mul_norm (dotProductBilin ℝ ℝ x) z
          rw [hz_apply, abs_of_pos ha_pos, hz_norm, mul_one] at htest
          exact htest
        exact le_antisymm hupper hlower)

-- Proof sketch: identify the functional `y ↦ xᵀ y` with the continuous linear functional
-- `LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ x)` on `ℝ^n` equipped with the
-- `Q`-inner-product structure. By Fréchet-Riesz, its dual norm is the `Q`-norm of the
-- representing vector `Q⁻¹ x`.
/-- In the `Q`-geometry, the Euclidean pairing functional `y ↦ xᵀ y` is represented by
`Q⁻¹ x`, so its dual norm is the `Q`-norm of that representing vector. -/
theorem dual_qNorm_eq_qNorm_invMulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qDualNorm hQ x = Q.qNorm hQ (Q⁻¹.mulVec x) := by
  -- Reuse the square-root formula on both sides of the desired identity.
  calc
    Q.qDualNorm hQ x = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
      rw [qDualNorm_eq_sqrt_dotProduct_inv_mulVec]
    _ = Q.qNorm hQ (Q⁻¹.mulVec x) := by
      rw [qNorm_invMulVec_eq_sqrt_dotProduct_inv_mulVec]

-- Proof sketch: combine `dual_qNorm_eq_qNorm_invMulVec` with the quadratic-form formula for the
-- `Q`-norm of `Q⁻¹ x`.
/-- Proposition 1.10: if `ℝ^n` is endowed with the `Q`-norm associated to a positive definite
matrix `Q`, then the dual norm of the Euclidean pairing functional `y ↦ xᵀ y` is
`√(xᵀ Q⁻¹ x) = ‖x‖_{Q⁻¹}`. -/
theorem dual_qNorm_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qDualNorm hQ x = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
  -- This is the source-facing restatement of the helper square-root formula.
  simpa using qDualNorm_eq_sqrt_dotProduct_inv_mulVec Q hQ x

-- Proof sketch: combine `dual_qNorm_eq_qNorm_invMulVec` with the quadratic-form expression for
-- the `Q⁻¹`-norm from Definition 1.18.
/-- In the `Q`-geometry, the dual norm of the Euclidean pairing functional is the `Q⁻¹`-norm of
the coefficient vector. -/
theorem dual_qNorm_eq_inv_qNorm (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (x : Fin n → ℝ) :
    Q.qDualNorm hQ x = Q⁻¹.qNorm hQ.inv x := by
  -- Rewrite both norms to the same quadratic-form square root.
  calc
    Q.qDualNorm hQ x = Real.sqrt (dotProduct x (Q⁻¹.mulVec x)) := by
      rw [dual_qNorm_eq_sqrt_dotProduct_inv_mulVec]
    _ = Q⁻¹.qNorm hQ.inv x := by
      symm
      rw [qNorm_eq_sqrt_dotProduct_mulVec_of_posDef]

-- Proof sketch: specialize the quadratic-form expression for the norm induced by a positive
-- definite matrix to `Q = diagonal w`, then simplify `mulVec_diagonal` and `dotProduct`.
/-- For a diagonal positive definite matrix, the induced `Q`-norm is the weighted Euclidean norm
`√(∑ i, w i x_i^2)`. -/
theorem diagonal_qNorm_eq_sqrt_sum_weight_mul_sq
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (x : Fin n → ℝ) :
    (diagonal w).qNorm (PosDef.diagonal hw) x =
      Real.sqrt (∑ i, w i * x i ^ (2 : ℕ)) := by
  -- Specialize the general quadratic-form norm identity to a diagonal matrix.
  calc
    (diagonal w).qNorm (PosDef.diagonal hw) x =
        Real.sqrt (dotProduct x ((diagonal w).mulVec x)) := by
      rw [qNorm_eq_sqrt_dotProduct_mulVec_of_posDef]
    _ = Real.sqrt (∑ i, w i * x i ^ (2 : ℕ)) := by
      rw [dotProduct_diagonal_mulVec_eq_sum_weight_mul_sq]

-- Proof sketch: apply `dual_qNorm_eq_sqrt_dotProduct_inv_mulVec` with `Q = diagonal w`, rewrite
-- `(diagonal w)⁻¹` as the diagonal matrix with entries `w i` inverted, and simplify
-- `mulVec_diagonal` and `dotProduct`.
/-- For a diagonal positive definite matrix, the dual norm of the Euclidean pairing functional
`y ↦ xᵀ y` is `√(∑ i, (1 / w i) x_i^2)`. -/
theorem dual_diagonal_qNorm_eq_sqrt_sum_invWeight_mul_sq
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (x : Fin n → ℝ) :
    (diagonal w).qDualNorm (PosDef.diagonal hw) x =
      Real.sqrt (∑ i, (w i)⁻¹ * x i ^ (2 : ℕ)) := by
  -- Reduce the diagonal dual norm to the inverse-weighted quadratic form.
  calc
    (diagonal w).qDualNorm (PosDef.diagonal hw) x =
        Real.sqrt (dotProduct x (((diagonal w)⁻¹).mulVec x)) := by
      rw [dual_qNorm_eq_sqrt_dotProduct_inv_mulVec (diagonal w) (PosDef.diagonal hw) x]
    _ = Real.sqrt (∑ i, (w i)⁻¹ * x i ^ (2 : ℕ)) := by
      rw [dotProduct_invDiagonal_mulVec_eq_sum_invWeight_mul_sq w hw x]

end

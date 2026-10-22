/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_9.Scaling

public section

/-!
Remark 7.9 (singular-value scaling).

This source item explains how the Chapter 7 algebraic singular-value law
`(7.49)` interacts with the quadrature normalization from Definition 7.1 to
produce the discrete scaling display `(7.50)`. The sequence-level owner for
`(7.49)` lives in `Book.Ch7.Remark_7_9.Scaling`, where `i = 1` denotes the
first singular mode, and this file supplies the source-facing bridge from that
owner to the `predictiveRisk` normalization.
-/

namespace ContinuousLinearMap.SingularSystem

universe u v w

variable {H₁ : Type u} {H₂ : Type v} {n : Type w}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable [Fintype n]
variable {K : H₁ →L[ℝ] H₂}

/-- Under the algebraic singular-value square-decay law `(7.49)`, the
predictive risk of a quadrature-scaled singular mode is the same algebraic rate
multiplied by the predictive risk of the reference vector. -/
theorem HasAlgebraicSingularValueSquareDecay.predictiveRisk_smul_eq_mul
    {S : SingularSystem K} {h_length : S.length = ⊤} {c p : ℝ}
    (h_decay : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (v : EuclideanSpace ℝ n) (i : ℕ+) :
    predictiveRisk (S.singularValueSequence h_length i • v) =
      (c * (i : ℝ) ^ (-p)) * predictiveRisk v := by
  rw [predictiveRisk_smul, h_decay i]

/-- Remark 7.9 companion. Under the algebraic singular-value square-decay law
`(7.49)`, the predictive risk of a quadrature-scaled singular mode is the same
algebraic rate multiplied by the predictive risk of the reference vector. -/
theorem predictiveRisk_smul_singularValueSequence_eq_mul
    (S : SingularSystem K) (h_length : S.length = ⊤) (c p : ℝ)
    (h_decay : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (v : EuclideanSpace ℝ n) (i : ℕ+) :
    predictiveRisk (S.singularValueSequence h_length i • v) =
      (c * (i : ℝ) ^ (-p)) * predictiveRisk v := by
  exact h_decay.predictiveRisk_smul_eq_mul v i

/-- If `v` is quadrature-normalized in the sense `predictiveRisk v = 1`, then
the Chapter 7 singular-value square-decay law `(7.49)` yields the scaled
display `(7.50)` for the discrete singular mode `S.singularValueSequence h_length i • v`,
with `i = 1` corresponding to the first singular mode. -/
theorem HasAlgebraicSingularValueSquareDecay.predictiveRisk_smul_eq
    {S : SingularSystem K} {h_length : S.length = ⊤} {c p : ℝ}
    (h_decay : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (v : EuclideanSpace ℝ n) (hv : predictiveRisk v = 1) (i : ℕ+) :
    predictiveRisk (S.singularValueSequence h_length i • v) =
      c * (i : ℝ) ^ (-p) := by
  rw [h_decay.predictiveRisk_smul_eq_mul v i, hv, mul_one]

/-- Remark 7.9. If `v` is quadrature-normalized in the sense `predictiveRisk v = 1`,
then the Chapter 7 singular-value square-decay law `(7.49)` yields the scaled
display `(7.50)` for the discrete singular mode `S.singularValueSequence h_length i • v`,
with `i = 1` corresponding to the first singular mode. -/
theorem predictiveRisk_smul_singularValueSequence_eq
    (S : SingularSystem K) (h_length : S.length = ⊤) (c p : ℝ)
    (h_decay : S.HasAlgebraicSingularValueSquareDecay h_length c p)
    (v : EuclideanSpace ℝ n) (hv : predictiveRisk v = 1) (i : ℕ+) :
    predictiveRisk (S.singularValueSequence h_length i • v) =
      c * (i : ℝ) ^ (-p) := by
  exact h_decay.predictiveRisk_smul_eq v hv i

end ContinuousLinearMap.SingularSystem

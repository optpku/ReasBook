/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2

public section

noncomputable section

namespace BFGS

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The BFGS Hessian-approximation update `(3.23)` built from the current
operator `H_v`, the step `s_v`, and the gradient difference `y_v`. -/
def update (H_v : H →L[ℝ] H) (s_v y_v : H) : H →L[ℝ] H :=
  H_v
    - (1 / inner ℝ (H_v s_v) s_v) • ((InnerProductSpace.rankOne ℝ (H_v s_v) s_v).comp H_v)
    + (1 / inner ℝ y_v s_v) • (InnerProductSpace.rankOne ℝ y_v y_v)

/-- The defining pointwise formula for `BFGS.update`. -/
theorem update_apply (H_v : H →L[ℝ] H) (s_v y_v x : H) :
    update H_v s_v y_v x =
      H_v x
        - (inner ℝ s_v (H_v x) / inner ℝ (H_v s_v) s_v) • H_v s_v
        + (inner ℝ y_v x / inner ℝ y_v s_v) • y_v := by
  -- Expand the update once and evaluate the two rank-one operators pointwise.
  simp [update, ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, div_eq_mul_inv,
    sub_eq_add_neg, smul_smul, mul_comm]

/-- If `H_v` is self-adjoint strongly positive, then the denominator
`inner ℝ (H_v s_v) s_v` in the BFGS update formula is strictly positive for every nonzero step
`s_v`. -/
theorem update_denom_pos [CompleteSpace H] (H_v : H →L[ℝ] H) (s_v : H)
    (hH : ContinuousLinearMap.SelfAdjointStronglyPositive H_v) (hs : s_v ≠ 0) :
    0 < inner ℝ (H_v s_v) s_v :=
  hH.inner_pos hs

end BFGS

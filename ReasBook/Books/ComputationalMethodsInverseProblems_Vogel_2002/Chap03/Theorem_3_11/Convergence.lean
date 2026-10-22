/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_11.Iterates

public section

noncomputable section

namespace Newton

universe u

section Model

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The standing local hypotheses in Theorem 3.11: `fStar` is a stationary point of `J`,
`hessian J fStar` is self-adjoint strongly positive, `hessian J` is `K`-Lipschitz, and `μ`
is an explicit lower bound for the quadratic form of `hessian J fStar`. -/
@[mk_iff hasQuadraticConvergenceModel_iff]
structure HasQuadraticConvergenceModel (J : H → ℝ) (fStar : H) (K : NNReal) (μ : ℝ) : Prop where
  /-- The reference point `fStar` is stationary for `J`. -/
  gradient_eq_zero : gradient J fStar = 0
  /-- The Hessian at `fStar` is self-adjoint and strongly positive. -/
  hessian_selfAdjointStronglyPositive :
    ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar)
  /-- The Hessian varies with Lipschitz constant `K`. -/
  hessian_lipschitz : LipschitzWith K (hessian J)
  /-- The explicit spectral lower bound `μ` is positive. -/
  mu_pos : 0 < μ
  /-- The quadratic form of `hessian J fStar` is bounded below by `μ`. -/
  inner_lowerBound (h : H) : μ * ‖h‖ ^ 2 ≤ inner ℝ (hessian J fStar h) h

namespace HasQuadraticConvergenceModel

set_option linter.defProp false in
/-- Build `HasQuadraticConvergenceModel J fStar K μ` from its source-facing clauses. -/
def ofComponents {J : H → ℝ} {fStar : H} {K : NNReal} {μ : ℝ}
    (hgrad : gradient J fStar = 0)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar))
    (hLip : LipschitzWith K (hessian J))
    (hμ : 0 < μ)
    (hLower : ∀ h : H, μ * ‖h‖ ^ 2 ≤ inner ℝ (hessian J fStar h) h) :
    Newton.HasQuadraticConvergenceModel J fStar K μ :=
  ⟨hgrad, hHess, hLip, hμ, hLower⟩

end HasQuadraticConvergenceModel

end Model

section Radius

variable {H : Type u} [NormedAddCommGroup H]

/-- The initial Newton iterate lies in the convergence ball from Theorem 3.11. -/
def StartsInConvergenceBall (f : ℕ → H) (fStar : H) (K : NNReal) (μ : ℝ) : Prop :=
  ‖f 0 - fStar‖ < 1 / (2 * convergenceConstant K μ)

/-- Specification theorem for `StartsInConvergenceBall`. -/
theorem startsInConvergenceBall_iff (f : ℕ → H) (fStar : H) (K : NNReal) (μ : ℝ) :
    StartsInConvergenceBall f fStar K μ ↔
      ‖f 0 - fStar‖ < 1 / (2 * convergenceConstant K μ) :=
  Iff.rfl

end Radius

end Newton

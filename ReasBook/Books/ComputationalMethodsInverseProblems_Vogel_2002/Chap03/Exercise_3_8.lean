/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_11

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Exercise 3.8. Under the setup of Theorem 3.11, the derived quadratic estimate
`(3.19)` is
`‖f (v + 1) - fStar‖ ≤ cStar J fStar γ * ‖f v - fStar‖ ^ 2`. The intermediate
equality `(3.20)` belongs to the proof-level derivation of this estimate rather
than to the public statement surface. This source-facing exercise entry is the
estimate component of the canonical Chapter 3 theorem
`Newton.newtonConvergesWithQuadraticEstimate`. -/
theorem quadraticEstimate_of_sourceHypotheses
    (J : H → ℝ) (f : ℕ → H) (fStar : H) {γ : NNReal}
    (hSecondDerivative :
      ∀ᶠ y in nhds fStar,
        HasFDerivAt J (fderiv ℝ J y) y ∧
          HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) y) y)
    (hgrad : gradient J fStar = 0)
    (hHess :
      ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J fStar))
    (hLip : LipschitzWith γ (hessian J))
    (hNewton : IsIterateSequence J f)
    (h0 : ‖f 0 - fStar‖ < 1 / (2 * cStar J fStar γ)) :
    ∀ v : ℕ,
      ‖f (v + 1) - fStar‖ ≤ cStar J fStar γ * ‖f v - fStar‖ ^ 2 := by
  exact
    (newtonConvergesWithQuadraticEstimate
      J f fStar hSecondDerivative hgrad hHess hLip hNewton h0).2

end Newton

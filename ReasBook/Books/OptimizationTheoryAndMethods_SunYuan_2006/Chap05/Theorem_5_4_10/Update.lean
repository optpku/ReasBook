/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Update
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section

section InverseJacobianQuasiNewtonUpdate

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse-Jacobian-side quasi-Newton step associated to `F`, the current point `x`, and the
current inverse approximation `H` is `x - H (F x)`. -/
def inverseQuasiNewtonNextIterate (F : E → E) (x : E) (H : E →L[ℝ] E) : E :=
  x - H (F x)

/-- The error size `σ (xₖ, xₖ₊₁) = max {‖xₖ - x*‖, ‖xₖ₊₁ - x*‖}` used in `(5.4.61)`. -/
def inverseQuasiNewtonSigma (x xNext xStar : E) : ℝ :=
  max ‖x - xStar‖ ‖xNext - xStar‖

/-- If `H` is invertible, the inverse-side step is exactly the Jacobian-side step built from
`H⁻¹`. -/
theorem inverseQuasiNewtonNextIterate_eq_quasiNewtonNextIterate_inverse
    (F : E → E) (x : E) (H : E →L[ℝ] E) (hH : H.IsInvertible) :
    inverseQuasiNewtonNextIterate F x H = quasiNewtonNextIterate F x H.inverse := by
  simp [inverseQuasiNewtonNextIterate, quasiNewtonNextIterate,
    ContinuousLinearMap.IsInvertible.inverse_inverse hH]

/-- The source-side well-definedness requirements implicit in Theorem 5.4.10 for a set-valued
inverse-Jacobian update rule `U` on an admissibility set `domU`: sufficiently small initial pairs
are admissible with invertible inverse approximations, every admissible invertible pair admits an
update, and every admissible update produces an invertible next inverse approximation and keeps
the next pair admissible for `(5.4.62)`. -/
def SupportsLocalWellDefinedInverseJacobianIteration
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (Ainv : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) : Prop :=
  (∃ ε > 0, ∃ δ > 0, ∀ x H,
      ‖x - xStar‖ < ε →
      ‖H - Ainv‖ < δ →
      (x, H) ∈ domU ∧ H.IsInvertible) ∧
    (∀ x H, (x, H) ∈ domU → H.IsInvertible → (U x H).Nonempty) ∧
    ∀ x H HNext,
      (x, H) ∈ domU →
      H.IsInvertible →
      HNext ∈ U x H →
        HNext.IsInvertible ∧
          (inverseQuasiNewtonNextIterate F x H, HNext) ∈ domU

/-- The inverse-side additive update hypothesis `(5.4.60)` for a set-valued update rule `U`,
including the local admissibility and update-existence conditions needed for the iteration
`(5.4.62)` to be well-defined in the source sense. -/
def SatisfiesInverseAdditiveLocalUpdateBound
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (Ainv : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) (γ : ℝ) : Prop :=
  SupportsLocalWellDefinedInverseJacobianIteration U F xStar Ainv domU ∧
    ∀ {x : E} {H HNext : E →L[ℝ] E},
      (x, H) ∈ domU →
      HNext ∈ U x H →
        ‖HNext - Ainv‖ ≤
          ‖H - Ainv‖ +
            γ / 2 * (‖inverseQuasiNewtonNextIterate F x H - xStar‖ + ‖x - xStar‖)

/-- The inverse-side `σ`-controlled update hypothesis `(5.4.61)` for a set-valued update rule
`U`, including the local admissibility and update-existence conditions needed for the iteration
`(5.4.62)` to be well-defined in the source sense. -/
def SatisfiesInverseSigmaLocalUpdateBound
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (Ainv : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) (α₁ α₂ : ℝ) : Prop :=
  SupportsLocalWellDefinedInverseJacobianIteration U F xStar Ainv domU ∧
    ∀ {x : E} {H HNext : E →L[ℝ] E},
      (x, H) ∈ domU →
      HNext ∈ U x H →
        ‖HNext - Ainv‖ ≤
          (1 + α₁ * inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H) xStar) *
              ‖H - Ainv‖ +
            α₂ * inverseQuasiNewtonSigma x (inverseQuasiNewtonNextIterate F x H) xStar

/-- The Jacobian-side admissibility domain induced from an inverse-side domain by taking
operator inverses on explicitly invertible Jacobian approximations. -/
def jacobianDomOfInverse (domU : Set (E × (E →L[ℝ] E))) : Set (E × (E →L[ℝ] E)) :=
  {p | p.2.IsInvertible ∧ (p.1, p.2.inverse) ∈ domU}

/-- The Jacobian-side update rule induced from an inverse-side update rule by taking operator
inverses on explicitly invertible current and next Jacobian approximations. -/
def jacobianUpdateOfInverse (U : JacobianUpdateFunction E) : JacobianUpdateFunction E :=
  fun x B ↦ {BNext | B.IsInvertible ∧ BNext.IsInvertible ∧ BNext.inverse ∈ U x B.inverse}

end InverseJacobianQuasiNewtonUpdate

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_1

noncomputable section

section JacobianQuasiNewtonUpdate

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The set-valued Jacobian update rule `U` from `(5.4.39)`, sending a current iterate `xₖ` and
Jacobian approximation `Bₖ` to the admissible next approximations `Bₖ₊₁`. -/
abbrev JacobianUpdateFunction (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E → (E →L[ℝ] E) → Set (E →L[ℝ] E)

/-- The quasi-Newton step from `(5.4.38)` attached to `F`, the current iterate `x`, and the
current Jacobian approximation `B`. -/
def quasiNewtonNextIterate (F : E → E) (x : E) (B : E →L[ℝ] E) : E :=
  x - B.inverse (F x)

/-- The local radius `σ(xₖ, xₖ₊₁)` from `(5.4.42)`, written using the explicit next iterate from
`quasiNewtonNextIterate F x B`. -/
def quasiNewtonSigma (F : E → E) (xStar x : E) (B : E →L[ℝ] E) : ℝ :=
  max ‖x - xStar‖ ‖quasiNewtonNextIterate F x B - xStar‖

/-- The source-side well-definedness requirements implicit in Theorem 5.4.9 for a set-valued
Jacobian update rule `U` on an admissibility set `domU`: sufficiently small initial pairs are
admissible with invertible Jacobian approximations, every admissible invertible pair admits an
update, and every admissible update produces an invertible next approximation and keeps the next
pair admissible for `(5.4.38)`-`(5.4.39)`. -/
def SupportsLocalWellDefinedJacobianIteration
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (DFstar : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) : Prop :=
  (∃ ε > 0, ∃ δ > 0, ∀ x B,
      ‖x - xStar‖ < ε →
      ‖B - DFstar‖ < δ →
      (x, B) ∈ domU ∧ B.IsInvertible) ∧
    (∀ x B, (x, B) ∈ domU → B.IsInvertible → (U x B).Nonempty) ∧
    ∀ x B Bnext,
      (x, B) ∈ domU →
      B.IsInvertible →
      Bnext ∈ U x B →
        Bnext.IsInvertible ∧
          (quasiNewtonNextIterate F x B, Bnext) ∈ domU

/-- The additive Jacobian-update hypothesis `(5.4.40)` for a set-valued update rule `U`,
including the local admissibility and step-existence conditions needed for the iteration
`(5.4.38)`-`(5.4.39)` to be well-defined in the source sense. -/
def SatisfiesAdditiveLocalUpdateBound
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (DFstar : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) (γ : ℝ) : Prop :=
  SupportsLocalWellDefinedJacobianIteration U F xStar DFstar domU ∧
    ∀ x B Bnext,
      (x, B) ∈ domU →
      B.IsInvertible →
      Bnext ∈ U x B →
        ‖Bnext - DFstar‖ ≤
          ‖B - DFstar‖ +
            (γ / 2) * (‖quasiNewtonNextIterate F x B - xStar‖ + ‖x - xStar‖)

/-- The `σ`-controlled Jacobian-update hypothesis `(5.4.41)` for a set-valued update rule `U`,
including the local admissibility and step-existence conditions needed for the iteration
`(5.4.38)`-`(5.4.39)` to be well-defined in the source sense. -/
def SatisfiesSigmaLocalUpdateBound
    (U : JacobianUpdateFunction E) (F : E → E) (xStar : E)
    (DFstar : E →L[ℝ] E) (domU : Set (E × (E →L[ℝ] E))) (α1 α2 : ℝ) : Prop :=
  SupportsLocalWellDefinedJacobianIteration U F xStar DFstar domU ∧
    ∀ x B Bnext,
      (x, B) ∈ domU →
      B.IsInvertible →
      Bnext ∈ U x B →
        ‖Bnext - DFstar‖ ≤
          (1 + α1 * quasiNewtonSigma F xStar x B) * ‖B - DFstar‖ +
            α2 * quasiNewtonSigma F xStar x B

end JacobianQuasiNewtonUpdate

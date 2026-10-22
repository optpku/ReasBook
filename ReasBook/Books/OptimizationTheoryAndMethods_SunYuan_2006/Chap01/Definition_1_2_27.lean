/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LineDeriv.Basic

-- Domain sampling:
-- * core/canonical owners: `HasLineDerivWithinAt`, `HasLineDerivAt`, `HasFDerivAt`
-- * this file keeps the chapter's source-facing Gateaux bridge/view owner
--   on the same generic normed-space layer as those calculus notions

section Chapter01Definition127

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E G : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- `A` is a Gateaux derivative of `f` within `D` at `x` if its values give all directional
line derivatives of `f` there. This is the chapter's source-facing Gateaux bridge, owned at the
same generic normed-space level as `HasLineDerivWithinAt`; the book's `ℝⁿ → ℝᵐ` formulation is
its Euclidean specialization. -/
def IsGateauxDerivativeWithinAt
    (D : Set E)
    (f : E → G)
    (x : E)
    (A : E →L[𝕜] G) : Prop :=
  ∀ d : E, HasLineDerivWithinAt 𝕜 f (A d) D x d

/-- Unfolding formula for `IsGateauxDerivativeWithinAt`. -/
theorem isGateauxDerivativeWithinAt_iff
    {D : Set E}
    {f : E → G}
    {x : E}
    {A : E →L[𝕜] G} :
    IsGateauxDerivativeWithinAt 𝕜 D f x A ↔
      ∀ d : E, HasLineDerivWithinAt 𝕜 f (A d) D x d :=
  Iff.rfl

/-- Chapter01 Definition 1.2.27, expressed at the generic normed-space owner level:
`f` is Gateaux differentiable at `x` on the open set `D` if `D` is open, `x ∈ D`, and there is
a continuous linear map `A` such that every directional line derivative of `f` within `D` at `x`
is `A d`. The source `ℝⁿ → ℝᵐ` statement is recovered by specializing to Euclidean spaces over
`ℝ`.

This uses `HasLineDerivWithinAt` as the mathlib encoding of the limit formula
`lim α → 0, ‖α‖⁻¹ * ‖f (x + α • d) - f x - α • A d‖ = 0`. -/
def SunYuanGateauxDifferentiableWithinAt
    (D : Set E)
    (f : E → G)
    (x : E) : Prop :=
  IsOpen D ∧ x ∈ D ∧ ∃ A : E →L[𝕜] G, IsGateauxDerivativeWithinAt 𝕜 D f x A

/-- Unfolding formula for `SunYuanGateauxDifferentiableWithinAt`. -/
theorem gateauxDifferentiableWithinAt_iff
    {D : Set E}
    {f : E → G}
    {x : E} :
    SunYuanGateauxDifferentiableWithinAt 𝕜 D f x ↔
      IsOpen D ∧
        x ∈ D ∧
        ∃ A : E →L[𝕜] G,
          IsGateauxDerivativeWithinAt 𝕜 D f x A :=
  Iff.rfl

end Chapter01Definition127

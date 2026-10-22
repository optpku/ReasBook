/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10.Iteration

noncomputable section

section InverseJacobianQuasiNewtonConvergence

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A small initial inverse pair `(x₀, H₀)` admits a canonical inverse-side quasi-Newton run on
the source update rule, and every such bridge-backed inverse run converges linearly to `xStar`. -/
structure InverseJacobianQuasiNewtonSmallStartConvergence
    (D : Set E) (F : E → E) (domU : Set (E × (E →L[ℝ] E))) (U : JacobianUpdateFunction E)
    (xStar x0 : E) (H0 : E →L[ℝ] E) : Prop where
  exists_iteration :
    ∃ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0, LinearlyConvergesTo A.x xStar
  linear :
    ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0, LinearlyConvergesTo A.x xStar

namespace InverseJacobianQuasiNewtonSmallStartConvergence

/-- The source-facing inverse-side small-start owner packages back into the canonical
Jacobian-side small-start owner on the inverse-induced bridge data once every inverse-side run
from the same small start is known to have invertible stagewise approximations. -/
def toJacobian
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {xStar x0 : E} {H0 : E →L[ℝ] E}
    (h : InverseJacobianQuasiNewtonSmallStartConvergence D F domU U xStar x0 H0)
    (h_invertible :
      ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0, ∀ k : ℕ,
        (A.H k).IsInvertible) :
    JacobianQuasiNewtonSmallStartConvergence D F (jacobianDomOfInverse domU)
      (jacobianUpdateOfInverse U) xStar x0 H0.inverse :=
  { exists_iteration := by
      rcases h.exists_iteration with ⟨A, hA⟩
      exact ⟨A.toJacobian (h_invertible A), hA⟩
    linear := fun A ↦ h.linear A.toInverseIteration }

theorem nonempty_iteration
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))}
    {U : JacobianUpdateFunction E} {xStar x0 : E} {H0 : E →L[ℝ] E}
    (h : InverseJacobianQuasiNewtonSmallStartConvergence D F domU U xStar x0 H0) :
    Nonempty (InverseJacobianQuasiNewtonIteration D F domU U x0 H0) := by
  rcases h.exists_iteration with ⟨A, _⟩
  exact ⟨A⟩

theorem to_exists_and_forall
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))}
    {U : JacobianUpdateFunction E} {xStar x0 : E} {H0 : E →L[ℝ] E}
    (h : InverseJacobianQuasiNewtonSmallStartConvergence D F domU U xStar x0 H0) :
    Nonempty (InverseJacobianQuasiNewtonIteration D F domU U x0 H0) ∧
      ∀ A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0,
        LinearlyConvergesTo A.x xStar := by
  exact ⟨h.nonempty_iteration, h.linear⟩

end InverseJacobianQuasiNewtonSmallStartConvergence

end InverseJacobianQuasiNewtonConvergence

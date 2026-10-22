/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_10.Update
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Iteration

noncomputable section

section InverseJacobianQuasiNewtonIterationOwner

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A source-facing inverse quasi-Newton iteration on `(xₖ, Hₖ)`. The step equation is the
inverse-side update `xₖ₊₁ = xₖ - Hₖ(F xₖ)`, and the next inverse approximation lies in the
source update rule `U (xₖ, Hₖ)`. -/
structure InverseJacobianQuasiNewtonIteration
    (D : Set E) (F : E → E) (domU : Set (E × (E →L[ℝ] E))) (U : JacobianUpdateFunction E)
    (x0 : E) (H0 : E →L[ℝ] E) where
  x : ℕ → E
  H : ℕ → E →L[ℝ] E
  x_zero : x 0 = x0
  H_zero : H 0 = H0
  iterates_mem : ∀ k : ℕ, x k ∈ D
  in_dom : ∀ k : ℕ, (x k, H k) ∈ domU
  step_eq : ∀ k : ℕ, x (k + 1) = inverseQuasiNewtonNextIterate F (x k) (H k)
  update_mem : ∀ k : ℕ, H (k + 1) ∈ U (x k) (H k)

namespace JacobianQuasiNewtonIteration

/-- Every stage of a Jacobian-side run over the inverse-induced bridge data determines an
inverse-side admissible pair by taking the stagewise inverse approximation. -/
theorem inverse_inDom
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {B0 : E →L[ℝ] E}
    (A :
      JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U)
        x0 B0) (k : ℕ) :
    (A.x k, (A.B k).inverse) ∈ domU := by
  have h_dom : (A.B k).IsInvertible ∧ (A.x k, (A.B k).inverse) ∈ domU := by
    simpa [jacobianDomOfInverse] using A.in_dom k
  exact h_dom.2

/-- On the inverse-induced bridge data, the canonical Jacobian-side step is exactly the
source-facing inverse step with the stagewise inverse approximation. -/
theorem inverse_step_eq
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {B0 : E →L[ℝ] E}
    (A :
      JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U)
        x0 B0) (k : ℕ) :
    A.x (k + 1) = inverseQuasiNewtonNextIterate F (A.x k) ((A.B k).inverse) := by
  simpa [inverseQuasiNewtonNextIterate, quasiNewtonNextIterate] using A.step_eq k

/-- On the inverse-induced bridge data, the next inverse approximation belongs to the original
inverse-side update rule `U`. -/
theorem inverse_update_mem
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {B0 : E →L[ℝ] E}
    (A :
      JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U)
        x0 B0) (k : ℕ) :
    (A.B (k + 1)).inverse ∈ U (A.x k) ((A.B k).inverse) := by
  have h_update :
      (A.B k).IsInvertible ∧
        (A.B (k + 1)).IsInvertible ∧
          (A.B (k + 1)).inverse ∈ U (A.x k) (A.B k).inverse := by
    simpa [jacobianUpdateOfInverse] using A.update_mem k
  exact h_update.2.2

/-- Every stage of the canonical Jacobian-side run over the inverse-induced bridge data carries
the source-facing inverse iterate, admissibility, step equation, and update-membership laws. -/
theorem inverse_stepSpec
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {B0 : E →L[ℝ] E}
    (A :
      JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U)
        x0 B0) (k : ℕ) :
    A.x k ∈ D ∧
      (A.x k, (A.B k).inverse) ∈ domU ∧
      A.x (k + 1) = inverseQuasiNewtonNextIterate F (A.x k) ((A.B k).inverse) ∧
      (A.B (k + 1)).inverse ∈ U (A.x k) ((A.B k).inverse) := by
  exact ⟨A.iterates_mem k, A.inverse_inDom k, A.inverse_step_eq k, A.inverse_update_mem k⟩

/-- A canonical Jacobian-side bridge run yields a source-facing inverse-side run by taking
stagewise inverses of the Jacobian approximations. -/
def toInverseIteration
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {H0 : E →L[ℝ] E}
    (A :
      JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U)
        x0 H0.inverse) :
    InverseJacobianQuasiNewtonIteration D F domU U x0 H0 :=
  { x := A.x
    H := fun k ↦ (A.B k).inverse
    x_zero := A.x_zero
    H_zero := by
      have hH0inv : H0.inverse.IsInvertible := by
        simpa [A.B_zero] using A.matrices_invertible 0
      have hH0 : H0.IsInvertible :=
        ContinuousLinearMap.IsInvertible.of_isInvertible_inverse hH0inv
      simpa [A.B_zero] using ContinuousLinearMap.IsInvertible.inverse_inverse hH0
    iterates_mem := A.iterates_mem
    in_dom := A.inverse_inDom
    step_eq := A.inverse_step_eq
    update_mem := A.inverse_update_mem }

end JacobianQuasiNewtonIteration

namespace InverseJacobianQuasiNewtonIteration

/-- If every inverse approximation in a source-facing inverse-side run is invertible, then that
run induces the canonical Jacobian-side run on inverse-induced bridge data by taking stagewise
inverses. -/
def toJacobian
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {H0 : E →L[ℝ] E}
    (A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0)
    (h_invertible : ∀ k : ℕ, (A.H k).IsInvertible) :
    JacobianQuasiNewtonIteration D F (jacobianDomOfInverse domU) (jacobianUpdateOfInverse U) x0
      H0.inverse :=
  { x := A.x
    B := fun k ↦ (A.H k).inverse
    x_zero := A.x_zero
    B_zero := by simp [A.H_zero]
    iterates_mem := A.iterates_mem
    in_dom := fun k ↦ by
      refine ⟨ContinuousLinearMap.IsInvertible.inverse (h_invertible k), ?_⟩
      simpa [ContinuousLinearMap.IsInvertible.inverse_inverse (h_invertible k)] using
        A.in_dom k
    matrices_invertible := fun k ↦
      ContinuousLinearMap.IsInvertible.inverse (h_invertible k)
    step_eq := fun k ↦ by
      simpa [inverseQuasiNewtonNextIterate, quasiNewtonNextIterate,
        ContinuousLinearMap.IsInvertible.inverse_inverse (h_invertible k)] using
        A.step_eq k
    update_mem := fun k ↦ by
      refine
        ⟨ContinuousLinearMap.IsInvertible.inverse (h_invertible k),
          ContinuousLinearMap.IsInvertible.inverse (h_invertible (k + 1)), ?_⟩
      simpa [ContinuousLinearMap.IsInvertible.inverse_inverse (h_invertible k),
        ContinuousLinearMap.IsInvertible.inverse_inverse (h_invertible (k + 1))] using
        A.update_mem k }

/-- Every stage of a source-facing inverse-side bridge run satisfies the ambient-domain,
admissibility, step, and update-membership laws. -/
theorem stepSpec
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))} {U : JacobianUpdateFunction E}
    {x0 : E} {H0 : E →L[ℝ] E}
    (A : InverseJacobianQuasiNewtonIteration D F domU U x0 H0) (k : ℕ) :
    A.x k ∈ D ∧
      (A.x k, A.H k) ∈ domU ∧
      A.x (k + 1) = inverseQuasiNewtonNextIterate F (A.x k) (A.H k) ∧
      A.H (k + 1) ∈ U (A.x k) (A.H k) := by
  exact ⟨A.iterates_mem k, A.in_dom k, A.step_eq k, A.update_mem k⟩

end InverseJacobianQuasiNewtonIteration

end InverseJacobianQuasiNewtonIterationOwner

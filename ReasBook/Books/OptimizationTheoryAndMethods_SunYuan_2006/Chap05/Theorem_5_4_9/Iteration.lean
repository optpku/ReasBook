/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Update
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9.Convergence

noncomputable section

section JacobianQuasiNewtonIterationOwner

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A well-defined Jacobian-side quasi-Newton iteration for `F` with update rule `U`, initial
data `x₀` and `B₀`, and ambient domain `D`. The step equation is `(5.4.38)` and the set-valued
Jacobian update is `(5.4.39)`. -/
structure JacobianQuasiNewtonIteration
    (D : Set E) (F : E → E) (domU : Set (E × (E →L[ℝ] E))) (U : JacobianUpdateFunction E)
    (x0 : E) (B0 : E →L[ℝ] E) where
  x : ℕ → E
  B : ℕ → E →L[ℝ] E
  x_zero : x 0 = x0
  B_zero : B 0 = B0
  iterates_mem : ∀ k : ℕ, x k ∈ D
  in_dom : ∀ k : ℕ, (x k, B k) ∈ domU
  matrices_invertible : ∀ k : ℕ, (B k).IsInvertible
  step_eq : ∀ k : ℕ, x (k + 1) = quasiNewtonNextIterate F (x k) (B k)
  update_mem : ∀ k : ℕ, B (k + 1) ∈ U (x k) (B k)

/-- A small initial pair `(x₀, B₀)` admits a well-defined Jacobian-side quasi-Newton iteration,
and every such iteration converges linearly to `xStar`. This packages the source conclusion of
Theorem 5.4.9 into a reusable owner rather than a raw `Nonempty ∧ ∀` surface. -/
structure JacobianQuasiNewtonSmallStartConvergence
    (D : Set E) (F : E → E) (domU : Set (E × (E →L[ℝ] E))) (U : JacobianUpdateFunction E)
    (xStar x0 : E) (B0 : E →L[ℝ] E) : Prop where
  exists_iteration :
    ∃ A : JacobianQuasiNewtonIteration D F domU U x0 B0, LinearlyConvergesTo A.x xStar
  linear :
    ∀ A : JacobianQuasiNewtonIteration D F domU U x0 B0, LinearlyConvergesTo A.x xStar

theorem JacobianQuasiNewtonSmallStartConvergence.nonempty_iteration
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))}
    {U : JacobianUpdateFunction E} {xStar x0 : E} {B0 : E →L[ℝ] E}
    (h : JacobianQuasiNewtonSmallStartConvergence D F domU U xStar x0 B0) :
    Nonempty (JacobianQuasiNewtonIteration D F domU U x0 B0) := by
  rcases h.exists_iteration with ⟨A, _⟩
  exact ⟨A⟩

theorem JacobianQuasiNewtonSmallStartConvergence.to_exists_and_forall
    {D : Set E} {F : E → E} {domU : Set (E × (E →L[ℝ] E))}
    {U : JacobianUpdateFunction E} {xStar x0 : E} {B0 : E →L[ℝ] E}
    (h : JacobianQuasiNewtonSmallStartConvergence D F domU U xStar x0 B0) :
    Nonempty (JacobianQuasiNewtonIteration D F domU U x0 B0) ∧
      ∀ A : JacobianQuasiNewtonIteration D F domU U x0 B0,
        LinearlyConvergesTo A.x xStar := by
  exact ⟨h.nonempty_iteration, h.linear⟩

end JacobianQuasiNewtonIterationOwner

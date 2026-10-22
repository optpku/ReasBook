/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Algorithm 12.16 is a `bridge/view` specialization rather than a new owner: the accelerated
two-block method is exactly Algorithm 12.4 with `A = id`, primal term `f + g₁`, nonsmooth term
`g₂`, and constant parameter `σ⁻¹`.

Domain sampling against the surrounding chapter API identifies the canonical owners:
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 for the accelerated trajectory;
- `dual_proximal_gradient_primal_x_argmax` and `dual_proximal_gradient_primal_y_step` from
  Algorithm 12.2 for the step-(a) and step-(b) set-valued updates;
- `fista_momentum_update` from Algorithm 10.13 for the scalar recursion
  `t_(k+1) = (1 + sqrt (1 + 4 t_k^2)) / 2`;
- `dual_based_proximal_gradient_identity_stepsize_parameter` from Algorithm 12.1 for the
  admissible identity-map stepsize.

Primitive data are only the iterate families `u`, `y`, `w`, `t` together with the two-block split
`f`, `g₁`, `g₂`. The step clauses and acceleration formulas are derived API from the Chapter 12.4
owner, so this file should reuse that owner directly instead of maintaining a parallel local
trajectory class. -/
recall IsFastDualProximalGradientPrimalTrajectory

section

variable (f g1 g2 : E → EReal) (σ : PosReal) (y0 : E)
variable (u : ℕ → E) (y w : ℕ → E) (t : ℕ → ℝ)
variable
  (h :
    IsFastDualProximalGradientPrimalTrajectory
      (fun x : E ↦ f x + g1 x)
      g2
      (LinearMap.id : E →ₗ[ℝ] E)
      σ
      (dual_based_proximal_gradient_identity_stepsize_parameter σ)
      y0
      u
      y
      w
      t)

local notation "F" => fun x : E ↦ f x + g1 x
local notation "A" => (LinearMap.id : E →ₗ[ℝ] E)
local notation "L" => dual_based_proximal_gradient_identity_stepsize_parameter σ

/- Algorithm 12.16 is exactly the specialized Chapter 12.4 trajectory owner. -/
#check
  (IsFastDualProximalGradientPrimalTrajectory F g2 A σ L y0 u y w t : Prop)

/- Its step-(a) clause is the canonical argmax field at the current extrapolated iterate `w^k`. -/
#check
  (h.primal_step : ∀ k : ℕ, u k ∈ dual_proximal_gradient_primal_x_argmax F A (w k))

/- Its step-(b) clause is the canonical primal proximal update for `g₂` with the identity map and
the reciprocal stepsize `σ⁻¹`. -/
#check
  (h.dual_step :
    ∀ k : ℕ,
      y (k + 1) ∈
        dual_proximal_gradient_primal_y_step
          g2
          A
          (u k)
          (w k)
          L)

/- The acceleration clause is already exposed by the owner theorem from Algorithm 12.4. -/
#check
  (h.acceleration_step_formula :
    ∀ k : ℕ, t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2)

end

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_7
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_9

noncomputable section

universe u v

open scoped Gradient
open InnerProductSpace (toDualMap)

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

local notation "F" => fun z : V ↦ dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V z)
local notation "G" => fun z : V ↦ dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V z)
local notation "gradF" => fun z : V ↦ ∇ (fun z' : V ↦ EReal.toReal (F z')) z
local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

/- Theorem 12.10 follows the same `core/canonical` versus `source-facing` split as
Theorems 12.8 and 12.9.

Domain sampling in Chapter 12 identifies:
- `IsFastDualProximalGradientDualTrajectory` from Algorithm 12.3 as the owner of the accelerated
  dual iterates whose objective gap is bounded in Theorem 12.9;
- `dual_based_proximal_gradient_dual_F_term` and `dual_based_proximal_gradient_dual_G_term` from
  Definition 12.5 as the canonical owners of the split dual terms entering that trajectory,
  viewed on the primal dual-variable space through `toDualMap`;
- `dual_proximal_gradient_primal_x_argmax` from Algorithm 12.2 as the owner of the primal point
  condition used by Lemma 12.7; and
- `IsFastDualProximalGradientPrimalTrajectory` from Algorithm 12.4 as the heavier source-facing
  wrapper that records the auxiliary primal argmax sequence `u^k` at the extrapolated points
  `w^k`.

The primal-distance estimate itself only uses the canonical accelerated dual trajectory together
with the pointwise argmax condition for the comparison sequence `x k`. The Algorithm 12.4 wrapper
therefore belongs only to a thin bridge theorem. -/

-- Proof sketch: apply Lemma 12.7 to the argmax point `x k` attached to the dual iterate `y k`,
-- obtaining `‖x^k - x*‖² ≤ (2 / σ) (q_opt - q(y^k))` for the Chapter 12 dual gap stated with
-- `dual_based_proximal_gradient_lagrange_dual_objective_primal`.
-- Then invoke the core accelerated dual-gap bound from Theorem 12.9 for the same dual trajectory
-- to bound that dual gap by `2 L ‖y^0 - y*‖² / (k + 1)²`, and combine the two inequalities.
/-- The `core/canonical` accelerated primal-distance estimate over the Chapter 12 dual-trajectory
owner, with the primal sequence supplied only through the pointwise argmax condition. -/
theorem fast_dual_proximal_gradient_primal_sqdist_le_of_dual_trajectory
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (x : ℕ → E) (y w : ℕ → V)
    (htraj : IsFastDualProximalGradientDualTrajectory A.toContinuousLinearMap σ G gradF L y0 y w)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax f A (y k))
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
  -- First control the primal squared distance by the dual gap at the same iterate via Lemma 12.7.
  have hhalf_gap :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        qOpt - q (y k) := by
    simpa using
      half_sigma_sqdist_le_dual_gap_of_primal_argmax
        (f := f)
        (g := g)
        (A := A)
        σ
        h_problem
        (y k)
        (x k)
        xStar
        (hx k)
        hxStar
  -- Then insert the accelerated `O(1 / k^2)` dual-gap estimate from Theorem 12.9.
  have hgap_rate :
      qOpt - q (y k) ≤
        ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
    simpa using
      fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory
        (f := f)
        (g := g)
        (A := A)
        σ
        L
        h_problem
        y0
        y
        w
        htraj
        yStar
        hyStar
        k
        hk
  -- The source proof is exactly the transitive sandwich of these two bounds.
  have hbound_ereal :
      ((((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) :=
    le_trans hhalf_gap hgap_rate
  -- Both ends are real coercions, so the remaining work is a scalar inequality in `ℝ`.
  have hbound_real :
      ((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ) ≤
        2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((k + 1 : ℝ) ^ (2 : ℕ)) := by
    exact EReal.coe_le_coe_iff.mp hbound_ereal
  have hσ_pos : 0 < (σ : ℝ) := σ.2
  have hden_pos : 0 < ((k + 1 : ℝ) ^ (2 : ℕ)) := by
    positivity
  -- Clear the positive denominator `(k + 1)^2`, then normalize the factor `(σ / 2)`.
  have hmul :
      (((σ : ℝ) / 2) * ‖x k - xStar‖ ^ (2 : ℕ)) * ((k + 1 : ℝ) ^ (2 : ℕ)) ≤
        2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    exact (le_div_iff₀ hden_pos).mp hbound_real
  have hscaled :
      (σ : ℝ) * ‖x k - xStar‖ ^ (2 : ℕ) * ((k + 1 : ℝ) ^ (2 : ℕ)) ≤
        4 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    nlinarith
  have htotal_pos : 0 < (σ : ℝ) * ((k + 1 : ℝ) ^ (2 : ℕ)) :=
    mul_pos hσ_pos hden_pos
  -- Cancel the positive denominator to recover the displayed primal-distance estimate.
  exact
    (le_div_iff₀ htotal_pos).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

-- Proof sketch: pass from the source-facing Algorithm 12.4 trajectory owner to the canonical
-- accelerated dual-trajectory owner via
-- `IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory`, then apply the core theorem
-- above.
/-- Theorem 12.10: if `y^k` is generated by the fast dual proximal-gradient method with
`L ≥ ‖A‖^2 / σ`, and `x^k` is chosen from
`argmax_x {⟪x, Aᵀ y^k⟫ - f(x)}` for each `k`, then every positive iterate satisfies the primal
estimate
`‖x^k - x*‖^2 ≤ 4 L ‖y^0 - y*‖^2 / (σ (k + 1)^2)`
for any primal optimizer `x*` and any optimal dual solution `y*`. -/
theorem fast_dual_proximal_gradient_primal_sqdist_le
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (u x : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
    (hx : ∀ k : ℕ, x k ∈ dual_proximal_gradient_primal_x_argmax f A (y k))
    (xStar : E)
    (hxStar : IsMinOn (composite_model_objective f (g ∘ A)) Set.univ xStar)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖x k - xStar‖ ^ (2 : ℕ) ≤
      4 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / ((σ : ℝ) * ((k + 1 : ℝ) ^ (2 : ℕ))) := by
  simpa using
    fast_dual_proximal_gradient_primal_sqdist_le_of_dual_trajectory
      f g A σ L h_problem y0 x y w
      (IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory
        (f := f)
        (g := g)
        (A := A)
        h_problem
        htraj)
      hx
      xStar hxStar yStar hyStar k hk

end

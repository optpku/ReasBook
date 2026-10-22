/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Metric

section

variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 11.1 lives in the stochastic projected-subgradient domain.

Domain sampling identifies the owner abstraction as:
- `stochastic_projected_subgradient_method` from Algorithm 8.10, the `core/canonical` pathwise
  stochastic projected-subgradient recursion;
- `stochastic_projected_subgradient_method_succ`, the canonical one-step unfolding theorem for that
  recursion;
- `projected_subgradient_method` from Algorithm 8.3, the deterministic companion owner;
- `metricProjection` / `projectionPoint` from Proposition 3.12, the projection owner layer.

The primitive data here are only the feasible set `C`, the current feasible point `x^k`, the
positive stepsize `t_k`, the realized sampled index `i_k`, and the component subgradient family
`f'_i`. The Chapter 11 formula is therefore a `bridge/view`: it is the one-step specialization of
the existing Chapter 8 owner to a constant stepsize and realized sampled index, not a second
projected-update owner. -/

/- Algorithm 11.1: the underlying pathwise stochastic projected-subgradient recursion is the
existing Chapter 8 owner `stochastic_projected_subgradient_method`. -/
recall stochastic_projected_subgradient_method
recall stochastic_projected_subgradient_method_succ

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
variable (hC_convex : Convex ℝ C) (subgrad : ι → C → E) (t : PosReal) (xk : C) (ik : ι)

local notation "x⁺" =>
  stochastic_projected_subgradient_method C hC_nonempty hC_closed hC_convex
    (fun _ x j ↦ subgrad j x) (fun _ ↦ (t : ℝ)) xk 1 ik

/-- Specializing the Chapter 8 stochastic projected-subgradient owner to one step, constant
stepsize `t_k`, and realized sample `i_k` yields the Chapter 11 update
`P_C (x^k - t_k f'_{i_k}(x^k))`. -/
theorem stochastic_projected_subgradient_method_one_step_eq :
    x⁺ =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((xk : E) - (t : ℝ) • subgrad ik xk) := by
  simpa using
    stochastic_projected_subgradient_method_succ
      C hC_nonempty hC_closed hC_convex
      (fun _ x j ↦ subgrad j x) (fun _ ↦ (t : ℝ)) xk 0 ik

/-- Coercing the one-step specialization of `stochastic_projected_subgradient_method` to the
ambient space yields the projected point `P_C (x^k - t_k f'_{i_k}(x^k))`. -/
@[simp] theorem stochastic_projected_subgradient_method_one_step_coe_eq :
    (x⁺ : E) =
      Pp[C, hC_nonempty, hC_closed, hC_convex]
        ((xk : E) - (t : ℝ) • subgrad ik xk) := by
  simpa [projectionPoint] using
    congrArg ((↑) : C → E)
      (stochastic_projected_subgradient_method_one_step_eq
        C hC_nonempty hC_closed hC_convex subgrad t xk ik)

/-- The one-step specialization of `stochastic_projected_subgradient_method` remains in the
feasible set `C`. -/
@[simp] theorem stochastic_projected_subgradient_method_one_step_mem :
    (x⁺ : E) ∈ C :=
  x⁺.property

end

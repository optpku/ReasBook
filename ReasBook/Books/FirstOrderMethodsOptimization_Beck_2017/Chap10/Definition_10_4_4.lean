/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDualMap)
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 10.4.4 is a `bridge/view` specialization in the constrained first-order-method
domain. The recursive owner already exists upstream as Algorithm 8.3's
`projected_subgradient_method`, and the textbook projected-gradient iteration is exactly that owner
specialized to the selected direction `gₖ(x) = ∇ f(x)`. The positive stepsizes remain primitive
data through `PosReal`, while the constrained quadratic minimization clause is derived from Text
9.11's canonical indicator/quadratic projection bridge.

Domain sampling:
- `projected_subgradient_method` and `projected_subgradient_method_succ` from Algorithm 8.3;
- `PosReal` from Definition 6.7;
- `isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection` from Text 9.11;
- `projectionPoint` from Proposition 3.12 for the ambient-space projection formula.

Accordingly, this file deletes the duplicate local owner and states Definition 10.4.4 directly as
the gradient specialization of the existing Chapter 8 owner. -/
recall projected_subgradient_method
recall projected_subgradient_method_succ
recall isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection

section

variable (f : E → ℝ) (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
variable (hC_convex : Convex ℝ C) (t : ℕ → PosReal) (x0 : C)

local notation "xpg" =>
  projected_subgradient_method C hC_nonempty hC_closed hC_convex
    (fun _ x ↦ ∇ f (x : E)) (fun k ↦ (t k : ℝ)) x0

/- Definition 10.4.4: for a nonempty closed convex feasible set `C`, stepsizes `t_k`, and a
feasible initial point `x0`, the projected gradient method is exactly the Chapter 8 projected
subgradient sequence specialized to `gₖ(x) = ∇ f(x)`. -/
#check (projected_subgradient_method C hC_nonempty hC_closed hC_convex
  (fun _ x ↦ ∇ f (x : E)) (fun k ↦ (t k : ℝ)) x0 : ℕ → C)

/-- One projected-gradient step applies the canonical metric projection onto `C` to the current
iterate minus the current stepsize times the gradient at that iterate. -/
theorem projected_gradient_method_succ (k : ℕ) :
    xpg (k + 1) =
      metricProjection C hC_nonempty hC_closed hC_convex
        ((xpg k : E) - (t k : ℝ) • ∇ f (xpg k : E)) := by
  simpa [div_eq_mul_inv, mul_comm] using
    projected_subgradient_method_succ C hC_nonempty hC_closed hC_convex
      (fun _ x ↦ ∇ f (x : E)) (fun j ↦ (t j : ℝ)) x0 k

/-- Coercing the recursive projected-gradient step to the ambient space gives the textbook
projection formula `x^(k+1) = P_C(x^k - t_k ∇ f(x^k))`. -/
theorem projected_gradient_method_succ_coe (k : ℕ) :
    (xpg (k + 1) : E) =
      Pp[C, hC_nonempty, hC_closed, hC_convex] ((xpg k : E) - (t k : ℝ) • ∇ f (xpg k : E)) := by
  simpa [projectionPoint] using
    congrArg (fun y : C ↦ (y : E)) (projected_gradient_method_succ f C hC_nonempty hC_closed
      hC_convex t x0 k)

-- Proof sketch: specialize Text 9.11's Euclidean indicator/projection bridge at the current
-- iterate `x^k`, the gradient `∇ f(x^k)`, and the positive stepsize `t_k`. Then rewrite the
-- chosen next iterate using `projected_gradient_method_succ_coe`.
/-- The next projected-gradient iterate minimizes the canonical Euclidean indicator/quadratic
Mirror-C update objective with current base point `x^k`, gradient `∇ f(x^k)`, and positive
stepsize `t_k`; by Text 9.11 this is exactly the textbook constrained quadratic argmin formula. -/
theorem projected_gradient_method_step_isMinOn (k : ℕ) :
    IsMinOn
      (mirror_c_update_objective (extendedIndicator C)
        (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)))
        (xpg k : E) (toDualMap ℝ E (∇ f (xpg k : E))) (t k)
      )
      Set.univ
      (xpg (k + 1) : E) := by
  have hpotential :
      (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal))) =
        (fun y : E ↦ (((‖y‖ ^ (2 : ℕ) / 2 : ℝ) : EReal))) := by
    funext y
    congr 1
    ring
  rw [hpotential]
  exact
    (isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection
      C hC_nonempty hC_closed hC_convex (xpg k : E) (∇ f (xpg k : E))
      (xpg (k + 1) : E) (t k).2).2
      (projected_gradient_method_succ_coe f C hC_nonempty hC_closed hC_convex t x0 k)

end

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_66
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 10.8 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the proximal-gradient domain identifies the relevant owners:
- `prox[...]` from Chapter 6 is the `core/canonical` owner for the set-valued proximal update in
  textbook stepsize language;
- `proximal_gradient_step` from Algorithm 10.1 is the canonical reciprocal-curvature bridge from
  the stepsize update to the chapter's curvature-parametrized prox-gradient owner;
- `mem_proximal_gradient_step_iff_isMinOn_curvature_model` from Algorithm 10.66 is the
  curvature-model argmin bridge for that one-step owner;
- `DifferentiableAt` is the canonical regularity owner ensuring that the displayed `∇ f(x^k)` is
  the actual textbook gradient at the iterate;
- `PosReal` is the canonical owner for positive stepsizes.

Primitive data:
- positive stepsizes `t_k`;
- actual differentiability of `f` at each iterate `x^k`;
- the direct stepsize proximal update
  `x^(k+1) ∈ prox[t_k g](x^k - t_k ∇ f(x^k))`.

Derived API:
- the reciprocal-curvature reformulation through `proximal_gradient_step` and
  `is_proximal_gradient_trajectory` is a `bridge/view`;
- the textbook argmin clause with quadratic coefficient `1 / (2 t_k)` is a further
  `bridge/view` consequence of Algorithm 10.66.

Accordingly, this file does not own a second local update-objective definition or a parallel
chosen-step wrapper. The source-facing owner is stated directly in textbook stepsize language on
the proximal map, while the reciprocal-curvature trajectory view is exposed separately as a bridge
to Algorithm 10.1. -/

/-- Definition 10.8 (1): sequences of iterates `x` and positive stepsizes `t` follow the
proximal-gradient method for `f + g` when `f` is differentiable at every iterate `x^k` and the
iterates satisfy the textbook stepsize update
`x^(k+1) ∈ prox[t_k g](x^k - t_k ∇ f(x^k))`. -/
class is_proximal_gradient_trajectory_with_stepsizes
    (f : E → ℝ) (g : E → EReal) (x : ℕ → E) (t : ℕ → PosReal) : Prop where
  /-- The primitive per-iteration data of a Definition 10.8 stepsize trajectory. -/
  step : ∀ k : ℕ,
    DifferentiableAt ℝ f (x k) ∧
      x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k))

/-- Coercion from a Definition 10.8 stepsize trajectory to its primitive per-iteration data. -/
instance is_proximal_gradient_trajectory_with_stepsizes.instCoeFun
    (f : E → ℝ) (g : E → EReal) (x : ℕ → E) (t : ℕ → PosReal) :
    CoeFun
      (is_proximal_gradient_trajectory_with_stepsizes f g x t)
      (fun _ ↦
        ∀ k : ℕ,
          DifferentiableAt ℝ f (x k) ∧
            x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k))) where
  coe h := h.step

/-- Rewriting the reciprocal-curvature one-step owner `proximal_gradient_step` at `L = t⁻¹`
recovers the textbook stepsize proximal update `prox[t g](x - t ∇ f(x))`. -/
theorem proximal_gradient_step_eq_stepsize_form
    (f : E → ℝ) (g : E → EReal) (xk : E) (t : PosReal) :
    proximal_gradient_step f.toEReal g xk t⁻¹ =
      prox[(((t : ℝ) : EReal) • g)] (xk - (t : ℝ) • ∇ f xk) := by
  rw [proximal_gradient_step]
  rw [show (((1 / t⁻¹ : PosReal) : EReal)) = (((t : ℝ) : EReal)) by
    simp [PosReal.coe_inv]]
  rw [show (1 / (t⁻¹ : PosReal) : ℝ) = (t : ℝ) by
    simp [PosReal.coe_inv]]
  rfl

/-- A Definition 10.8 trajectory satisfies, at each iteration `k`, the primitive textbook data:
`f` is differentiable at `x^k` and `x^(k+1)` belongs to the stepsize proximal update set. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    DifferentiableAt ℝ f (x k) ∧
      x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k)) :=
  h k

/-- Along a Definition 10.8 stepsize trajectory, the smooth term `f` is differentiable at each
iterate `x^k`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_differentiableAt
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    DifferentiableAt ℝ f (x k) :=
  (is_proximal_gradient_trajectory_with_stepsizes_step h k).1

/-- Along a Definition 10.8 stepsize trajectory, the next iterate `x^(k+1)` belongs to the
textbook proximal update `prox[t_k g](x^k - t_k ∇ f(x^k))`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_mem_prox
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k)) :=
  (is_proximal_gradient_trajectory_with_stepsizes_step h k).2

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Along a Definition 10.8 stepsize trajectory, the next iterate `x^(k+1)` belongs to the
canonical prox-gradient step with reciprocal curvature parameter `t_k⁻¹`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_mem_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    x (k + 1) ∈ proximal_gradient_step f.toEReal g (x k) (t k)⁻¹ :=
  by
    simpa [proximal_gradient_step_eq_stepsize_form] using
      is_proximal_gradient_trajectory_with_stepsizes_mem_prox h k

omit [CompleteSpace E] in
private theorem is_differentiable_at_toEReal_of_differentiableAt
    {f : E → ℝ} {x : E} (hdiff : DifferentiableAt ℝ f x) :
    is_differentiable_at f.toEReal x := by
  refine ⟨?_, ?_⟩
  · simp [finite_domain, effective_domain]
  · simpa using hdiff

private theorem reciprocal_stepsize_half_eq_inv_two_mul (t : PosReal) :
    (((t⁻¹ : PosReal) : ℝ) / 2) = 1 / (2 * (t : ℝ)) := by
  have ht : (t : ℝ) ≠ 0 := ne_of_gt t.2
  change (t : ℝ)⁻¹ / 2 = 1 / (2 * (t : ℝ))
  field_simp [ht]

/-- The source-facing Definition 10.8 owner canonically induces the reciprocal-curvature
Algorithm 10.1 trajectory for `f.toEReal` and parameters `L_k = t_k⁻¹`. This is the bridge/view
from textbook stepsize language to the chapter's curvature-language owner. -/
theorem is_proximal_gradient_trajectory_with_stepsizes.toCurvatureTrajectory
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) :
    is_proximal_gradient_trajectory f.toEReal g x (fun k ↦ (t k)⁻¹) := by
  intro k
  refine ⟨?_, ?_⟩
  · have hx :
        x k ∈ interior (finite_domain f.toEReal) :=
      (is_differentiable_at_toEReal_of_differentiableAt
        (is_proximal_gradient_trajectory_with_stepsizes_differentiableAt h k)).1
    simp [effective_domain] at hx ⊢
  · simpa using is_proximal_gradient_trajectory_with_stepsizes_mem_step h k

-- Proof sketch: specialize Algorithm 10.66's curvature-parameter argmin bridge at `L = t⁻¹` and
-- rewrite `((t⁻¹ : ℝ) / 2) * ‖x - xk‖²` as `‖x - xk‖² / (2 t)`.
/-- For a positive stepsize `t`, the Chapter 10 prox-gradient step with reciprocal curvature `t⁻¹`
is equivalent to the textbook argmin clause
`xNext ∈ argmin_u [f(xk) + ⟪∇ f(xk), u - xk⟫ + g(u) + ‖u - xk‖² / (2 t)]`,
provided `f` is differentiable at `xk` so that the displayed `∇ f(xk)` is the genuine textbook
gradient. -/
theorem mem_proximal_gradient_step_iff_isMinOn_stepsize_model
    {f : E → ℝ} {g : E → EReal} {xk xNext : E} {t : PosReal}
    (hdiff : DifferentiableAt ℝ f xk) :
    xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
      IsMinOn
        (fun u ↦
          ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
            ((((1 / (2 * (t : ℝ)) : ℝ) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
        Set.univ xNext := by
  have hcurvature :
      xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
        IsMinOn
          (fun u ↦
            ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
              ((((((t⁻¹ : PosReal) : ℝ) / 2) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
          Set.univ xNext :=
    show xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
        IsMinOn
          (fun u ↦
            ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
              ((((((t⁻¹ : PosReal) : ℝ) / 2) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
          Set.univ xNext from
      mem_proximal_gradient_step_iff_isMinOn_curvature_model
        (is_differentiable_at_toEReal_of_differentiableAt hdiff)
  simpa [PosReal.coe_inv, reciprocal_stepsize_half_eq_inv_two_mul, Function.toEReal] using
    hcurvature

/-- Definition 10.8 (2): at each iteration `k`, the next iterate `x^(k+1)` globally
minimizes the linearized quadratic model with stepsize `t_k`. The differentiability clause for the
current iterate `x^k` is available separately from
`is_proximal_gradient_trajectory_with_stepsizes_differentiableAt`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_isMinOn_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    IsMinOn
      (fun u ↦
        ((((f (x k) : ℝ) : EReal) + ((inner ℝ (∇ f (x k)) (u - x k) : ℝ) : EReal)) + g u) +
          ((((1 / (2 * (t k : ℝ)) : ℝ) * ‖u - x k‖ ^ (2 : ℕ)) : ℝ) : EReal))
      Set.univ
      (x (k + 1)) := by
  exact
    (mem_proximal_gradient_step_iff_isMinOn_stepsize_model
      (is_proximal_gradient_trajectory_with_stepsizes_differentiableAt h k)).1
      (is_proximal_gradient_trajectory_with_stepsizes_mem_step h k)

end

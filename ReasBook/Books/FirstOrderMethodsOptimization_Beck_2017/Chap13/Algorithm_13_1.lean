/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 13.1 is `source-facing`: the textbook specifies a feasible iterate `x^k`, a chosen
linear-minimization point `p^k ∈ argmin_{p ∈ C} ⟪p, ∇ f(x^k)⟫`, and a chosen stepsize
`t_k ∈ [0, 1]`.

Domain sampling against the nearby Chapter 13 owners identifies:
- `generalized_conditional_gradient_argmin` from Definition 13.4 as the canonical argmin owner
  for the linearized subproblem;
- `extendedIndicator` from Chapter 2 as the canonical way to encode the feasibility set `C`
  inside that owner;
- the Chapter 10 and 13 algorithm pattern that non-single-valued updates are recorded by a
  trajectory predicate on explicit sequences rather than by a deterministic recursive map.

Accordingly, this file is a `bridge/view` specialization of the generalized conditional-gradient
argmin owner to the constrained case `g = extendedIndicator C`. The public API keeps the source
trajectory predicate and derives the textbook feasible-minimizer reading from the canonical owner,
rather than duplicating a second constrained-only argmin definition. -/

variable (f : E → EReal) (C : Set E) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1)

/- Algorithm 13.1 is the constrained specialization of the canonical Chapter 13 generalized
trajectory owner, obtained by taking `g = extendedIndicator C`. -/
#check is_generalized_conditional_gradient_trajectory
  (fun y ↦ (f y).toReal) (extendedIndicator C) x p t

variable {f C x p t}

-- Proof sketch: unfold `generalized_conditional_gradient_argmin` and
-- `generalized_conditional_gradient_subproblem`,
-- then expand `extendedIndicator C`. Outside `C` the value is `⊤`, so minimizers must lie in `C`;
-- on `C` the indicator term vanishes, reducing the minimizer condition to `IsMinOn` for the
-- linear functional `q ↦ ⟪q, ∇ (fun x ↦ (f x).toReal) (xᵏ)⟫` over `C`.
/-- A point belongs to the canonical generalized conditional-gradient argmin set for
`g = extendedIndicator C` exactly when it is feasible and minimizes the linearized objective
`q ↦ ⟪q, ∇ (fun x ↦ (f x).toReal) (xᵏ)⟫` over `C`. -/
theorem mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
    {f : E → EReal} {C : Set E} (hC : C.Nonempty) {xk p : E} :
    p ∈ generalized_conditional_gradient_argmin
        (fun x ↦ (f x).toReal) (extendedIndicator C) xk ↔
      p ∈ C ∧ IsMinOn (fun q ↦ inner ℝ q (∇ (fun x ↦ (f x).toReal) xk)) C p := by
  rcases hC with ⟨z, hz⟩
  rw [generalized_conditional_gradient_argmin_def]
  change
    p ∈ unconstrained_problem_solutions
      (composite_model_objective
        (fun q ↦ ((inner ℝ q (∇ (fun x ↦ (f x).toReal) xk) : ℝ) : EReal))
        (extendedIndicator C)) ↔
      p ∈ C ∧ IsMinOn (fun q ↦ inner ℝ q (∇ (fun x ↦ (f x).toReal) xk)) C p
  rw [unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
      (fun q ↦ ((inner ℝ q (∇ (fun x ↦ (f x).toReal) xk) : ℝ) : EReal))
      C
      ⟨z, hz, by simp [effective_domain]⟩
      (fun y hy ↦ by simp),
    mem_constrained_problem_solutions_iff]
  constructor
  · rintro ⟨hpC, hpmin⟩
    refine ⟨hpC, ?_⟩
    rw [isMinOn_iff] at hpmin ⊢
    simpa using hpmin
  · rintro ⟨hpC, hpmin⟩
    refine ⟨hpC, ?_⟩
    rw [isMinOn_iff] at hpmin ⊢
    simpa using hpmin

/-- A generalized conditional-gradient trajectory with `g = extendedIndicator C` starts from a
feasible point `x⁰ ∈ C`. -/
theorem is_conditional_gradient_trajectory_zero
    {f : E → EReal} {C : Set E} {x p : ℕ → E}
    {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_generalized_conditional_gradient_trajectory
      (fun y ↦ (f y).toReal) (extendedIndicator C) x p t) :
    x 0 ∈ C := by
  simpa [effective_domain_extendedIndicator] using h.zero_mem_effective_domain

/-- At each iteration `k`, a generalized conditional-gradient trajectory with
`g = extendedIndicator C` picks a feasible minimizer of
`q ↦ ⟪q, ∇ (fun x ↦ (f x).toReal) (xᵏ)⟫` over `C` and updates by
`xᵏ⁺¹ = xᵏ + tₖ (pᵏ - xᵏ)`, with `tₖ ∈ [0, 1]` encoded by the type of `t k`. -/
theorem is_conditional_gradient_trajectory_step
    {f : E → EReal} {C : Set E} {x p : ℕ → E}
    {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_generalized_conditional_gradient_trajectory
      (fun y ↦ (f y).toReal) (extendedIndicator C) x p t) (k : ℕ) :
    p k ∈ C ∧
      IsMinOn (fun q ↦ inner ℝ q (∇ (fun y ↦ (f y).toReal) (x k))) C (p k) ∧
      x (k + 1) = x k + (t k : ℝ) • (p k - x k) := by
  rcases is_generalized_conditional_gradient_trajectory_step h k with ⟨hp, hstep⟩
  rcases
      (mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        ⟨x 0, is_conditional_gradient_trajectory_zero h⟩).mp hp with
    ⟨hpC, hpmin⟩
  exact ⟨hpC, hpmin, hstep⟩

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the local API guidance comes from the nearby
Chapter 10--13 algorithm and definition files. Algorithm 13.2 is `source-facing` in the
generalized conditional-gradient domain.

Domain sampling against the existing owners identifies:
- `effective_domain` for the initialization clause `x⁰ ∈ dom(g)`;
- `generalized_conditional_gradient_subproblem` from Definition 13.4 as the primitive linearized
  objective `p ↦ ⟪p, ∇ f(xᵏ)⟫ + g(p)`;
- `generalized_conditional_gradient_argmin` from Definition 13.4 as the canonical owner of the
  admissible search points;
- `∇` and the ambient inner product for the linearization term inside that subproblem.

Since the linear minimization oracle and the line-search parameter are both chosen at each
iteration, the faithful public API is therefore the trajectory predicate on explicit sequences
`xᵏ`, `pᵏ`, and `tₖ`, stated directly in terms of the existing Definition 13.4 argmin owner
rather than via a parallel local copy. -/

/-- Algorithm 13.2: a triple of sequences `(xᵏ, pᵏ, tₖ)` follows the generalized conditional
gradient method for the composite objective `f + g` when `x⁰ ∈ dom(g)`, each
`pᵏ ∈ argmin_p {⟪p, ∇ f(xᵏ)⟫ + g(p)}`, each `tₖ ∈ [0, 1]`, and
`xᵏ⁺¹ = xᵏ + tₖ (pᵏ - xᵏ)`. The primitive trajectory data are the initial-domain condition, the
chosen argmin point at each step, and the affine update equality; the paired step statement is
derived API. -/
class is_generalized_conditional_gradient_trajectory
    (f : E → ℝ) (g : E → EReal) (x p : ℕ → E) (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop where
  /-- The initial iterate lies in `dom(g)`. -/
  zero_mem_effective_domain : x 0 ∈ effective_domain g
  /-- At each iteration, the chosen search point solves the canonical Chapter 13 linearized
  subproblem. -/
  argmin_mem (k : ℕ) :
    p k ∈ generalized_conditional_gradient_argmin f g (x k)
  /-- At each iteration, the next iterate is obtained by the convex-combination update along the
  chosen search point. -/
  step_eq (k : ℕ) :
    x (k + 1) = x k + (t k : ℝ) • (p k - x k)

-- Proof sketch: extract the initialization clause from the first conjunct of
-- `is_generalized_conditional_gradient_trajectory`.
/-- A generalized conditional-gradient trajectory starts from a point of `dom(g)`. -/
theorem is_generalized_conditional_gradient_trajectory_zero
    {f : E → ℝ} {g : E → EReal} {x p : ℕ → E}
    {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_generalized_conditional_gradient_trajectory f g x p t) :
    x 0 ∈ effective_domain g :=
  h.zero_mem_effective_domain

-- Proof sketch: specialize the defining argmin clause of
-- `is_generalized_conditional_gradient_trajectory` at the iteration index `k`.
/-- At each iteration `k`, a generalized conditional-gradient trajectory chooses a minimizer
`pᵏ` of the canonical linearized subproblem at `xᵏ`. -/
theorem is_generalized_conditional_gradient_trajectory_argmin
    {f : E → ℝ} {g : E → EReal} {x p : ℕ → E}
    {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_generalized_conditional_gradient_trajectory f g x p t) (k : ℕ) :
    p k ∈ generalized_conditional_gradient_argmin f g (x k) :=
  h.argmin_mem k

-- Proof sketch: specialize the defining universal clause of
-- `is_generalized_conditional_gradient_trajectory` at the iteration index `k`.
/-- At each iteration `k`, a generalized conditional-gradient trajectory chooses a minimizer
`pᵏ` of the linearized subproblem at `xᵏ` and updates by
`xᵏ⁺¹ = xᵏ + tₖ (pᵏ - xᵏ)`, with `tₖ ∈ [0, 1]` encoded by the type of `t k`. -/
theorem is_generalized_conditional_gradient_trajectory_step
    {f : E → ℝ} {g : E → EReal} {x p : ℕ → E}
    {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_generalized_conditional_gradient_trajectory f g x p t) (k : ℕ) :
    p k ∈ generalized_conditional_gradient_argmin f g (x k) ∧
      x (k + 1) = x k + (t k : ℝ) • (p k - x k) :=
  ⟨h.argmin_mem k, h.step_eq k⟩

end

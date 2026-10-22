/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 13.4 is `source-facing`: the textbook introduces the chapter notation
`p(x) ∈ arg min_p {⟪p, ∇ f(x)⟫ + g(p)}` for the linearized composite subproblem.

Domain sampling in the surrounding project points to:
- Chapter 10's `composite_model_objective` as the canonical owner for pointwise objective sums;
- Chapter 8's `unconstrained_problem_solutions` as the canonical owner for global argmin sets;
- Chapter 6's `prox` and Chapter 13's later block analogue `partial_conditional_gradient_argmin`
  as the local style for source-facing set-valued minimization owners built from those canonical
  components.

The primitive source-facing data is therefore just the linearized objective. Its argmin set is a
derived source-facing view obtained by applying the Chapter 8 solution-set owner to that
subproblem, since the source does not choose a canonical minimizer. -/

/-- The generalized conditional-gradient linearized subproblem at `x`, namely the objective
`p ↦ ⟪p, ∇ f(x)⟫ + g(p)`. This is the Chapter 10 composite objective specialized to the affine
linearization term `p ↦ ⟪p, ∇ f(x)⟫`. -/
abbrev generalized_conditional_gradient_subproblem
    (f : E → ℝ) (g : E → EReal) (x : E) : E → EReal :=
  composite_model_objective (fun p ↦ ((inner ℝ p (∇ f x) : ℝ) : EReal)) g

-- Proof sketch: unfold `generalized_conditional_gradient_subproblem`; evaluation at `p` is
-- exactly the displayed linearized objective value.
/-- Evaluating the generalized conditional-gradient subproblem at `p` gives
`⟪p, ∇ f(x)⟫ + g(p)`. -/
@[simp] theorem generalized_conditional_gradient_subproblem_apply
    (f : E → ℝ) (g : E → EReal) (x p : E) :
    generalized_conditional_gradient_subproblem f g x p =
      ((inner ℝ p (∇ f x) : ℝ) : EReal) + g p :=
  rfl

/-- Definition 13.4: the chapter notation `p(x) ∈ arg min_p {⟪p, ∇ f(x)⟫ + g(p)}` is formalized
as the Chapter 8 unconstrained solution set of the generalized conditional-gradient linearized
subproblem at `x`, without choosing a canonical minimizer. -/
abbrev generalized_conditional_gradient_argmin
    (f : E → ℝ) (g : E → EReal) (x : E) : Set E :=
  unconstrained_problem_solutions (generalized_conditional_gradient_subproblem f g x)

-- Proof sketch: Definition 13.4's argmin set is exactly the Chapter 8 unconstrained solution-set
-- owner applied to the linearized subproblem.
/-- The Chapter 13 argmin set is exactly the Chapter 8 unconstrained solution set of the
generalized conditional-gradient linearized subproblem. -/
theorem generalized_conditional_gradient_argmin_def
    (f : E → ℝ) (g : E → EReal) (x : E) :
    generalized_conditional_gradient_argmin f g x =
      unconstrained_problem_solutions (generalized_conditional_gradient_subproblem f g x) :=
  rfl

-- Proof sketch: rewrite membership in the Chapter 8 unconstrained solution-set owner.
/-- A point `p` belongs to `generalized_conditional_gradient_argmin f g x` exactly when it
globally minimizes the objective `q ↦ ⟪q, ∇ f(x)⟫ + g(q)`. -/
@[simp] theorem mem_generalized_conditional_gradient_argmin_iff
    {f : E → ℝ} {g : E → EReal} {x p : E} :
    p ∈ generalized_conditional_gradient_argmin f g x ↔
      IsMinOn (generalized_conditional_gradient_subproblem f g x) Set.univ p :=
  mem_unconstrained_problem_solutions_iff

end

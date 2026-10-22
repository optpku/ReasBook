/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}

/- Definition 13.9 is a `bridge/view` specialization of the Chapter 10 constrained/composite
owner API.

Domain sampling in the relevant optimization owner layer:
- `constrained_problem_objective` from Chapter 3 for `min {f x : x ∈ C}`;
- `constrained_problem_solutions` and `unconstrained_problem_solutions` from Chapter 8 for the
  solution-set owners;
- `composite_model_objective` from Chapter 10 for the composite objective `f + g`;
- the Chapter 10 bridge theorems
  `unconstrained_problem_solutions_constrained_problem_objective_eq` and
  `unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq`.

Primitive data are only `f`, `C`, and the indicator specialization `g = extendedIndicator C`.
The Chapter 10 solution-set equalities are the owner-level statements; the `IsMinOn` lemmas below
are thin companions obtained by rewriting membership in those owner sets. This keeps feasibility
explicit on the constrained side, which is mathematically necessary. -/

/- Definition 13.9: the constrained objective already has the canonical owner-level solution-set
bridge in Chapter 10. -/
recall unconstrained_problem_solutions_constrained_problem_objective_eq

/- Definition 13.9: after specializing the nonsmooth term to `extendedIndicator C`, the composite
model already has the canonical owner-level solution-set bridge in Chapter 10. -/
recall unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq

/-- If the feasible set meets the effective domain of `f`, then minimizing the constrained
objective on `E` is exactly being a feasible minimizer of `f` on `C`. -/
theorem isMinOn_constrained_problem_objective_iff
    {f : E → EReal} {C : Set E} {x : E} (hC_dom : (C ∩ effective_domain f).Nonempty) :
    IsMinOn (constrained_problem_objective f C) Set.univ x ↔ x ∈ C ∧ IsMinOn f C x := by
  rw [← mem_unconstrained_problem_solutions_iff,
    unconstrained_problem_solutions_constrained_problem_objective_eq f C hC_dom,
    mem_constrained_problem_solutions_iff]

/-- If the feasible set meets the effective domain of `f` and `f` never takes the value `-∞`
outside `C`, then the composite model with `g = extendedIndicator C` has exactly the feasible
minimizers of `f` on `C` as its global minimizers. -/
theorem isMinOn_composite_model_objective_extendedIndicator_iff
    {f : E → EReal} {C : Set E} {x : E} (hC_dom : (C ∩ effective_domain f).Nonempty)
    (h_ne_bot : ∀ y ∉ C, f y ≠ ⊥) :
    IsMinOn (composite_model_objective f (extendedIndicator C)) Set.univ x ↔
      x ∈ C ∧ IsMinOn f C x := by
  rw [← mem_unconstrained_problem_solutions_iff,
    unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
      f C hC_dom h_ne_bot,
    mem_constrained_problem_solutions_iff]

end

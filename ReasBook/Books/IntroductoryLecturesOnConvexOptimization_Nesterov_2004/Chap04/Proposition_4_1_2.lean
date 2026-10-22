/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 4.1.2 lies in the cubic-regularization monotonicity domain.

Relevant owner declarations sampled before refinement:
* `Antitone` and `antitone_nat_of_succ_le` from mathlib;
* `antitone_nat_iff_succ_le` in `Chap01/Definition_1_4_1`;
* `RelaxedRegularizedNewtonIteration` in `Chap04/Definition_4_1_5`, the chapter owner of the
  iterate sequence, regularization sequence, and update law;
* `RegularizedNewton.acceptingParameters` and
  `RegularizedNewton.mem_acceptingParameters_iff` in `Chap04/Definition_4_1_16`, the canonical
  acceptance predicate at a fixed iterate.

Best owner abstraction:
* source-facing: the monotonicity statement for a relaxed regularized Newton trajectory;
* core/canonical: `Antitone (fun k ↦ f (method k))`;
* bridge/view: the successor-step inequality `f (method (k + 1)) ≤ f (method k)`.

Primitive data:
* a relaxed regularized Newton trajectory `method`;
* the accepted-step membership
  `M_k ∈ RegularizedNewton.acceptingParameters f stepMap modelValue x_k`;
* the on-trajectory underestimator inequality `\tilde f_{M_k}(x_k) ≤ f(x_k)`.

Derived API:
* the one-step decrease `f (method (k + 1)) ≤ f (method k)`;
* the antitone objective-value sequence.

This proposition therefore reuses the chapter owner
`RelaxedRegularizedNewtonIteration` instead of restating the iterate sequence, regularization
sequence, and update law as parallel primitive arguments. -/

open RegularizedNewton

variable {X : Type u}

/-- Proposition 4.1.2: if the iterates satisfy `x_{k+1} = T_{M_k}(x_k)`, each accepted trial
point satisfies `f (T_{M_k}(x_k)) ≤ \tilde f_{M_k}(x_k)`, and the visited model values
`\tilde f_{M_k}(x_k)` underestimate `f(x_k)` along the trajectory, then the objective values
decrease stepwise: `f(x_{k+1}) ≤ f(x_k)` for every `k`. -/
theorem objective_values_nonincreasing
    {f : X → ℝ}
    {stepMap : ℝ → X → X}
    {modelValue : ℝ → X → ℝ}
    {L : ℝ}
    (method : RelaxedRegularizedNewtonIteration stepMap L)
    (haccept :
      ∀ k : ℕ,
        method.regularization k ∈ acceptingParameters f stepMap modelValue (method k))
    (modelValue_le_objective :
      ∀ k : ℕ, modelValue (method.regularization k) (method k) ≤ f (method k))
    (k : ℕ) :
    f (method (k + 1)) ≤ f (method k) := by
  rw [method.x_succ k]
  exact le_trans
    ((mem_acceptingParameters_iff
      f stepMap modelValue (method k) (method.regularization k)).1 (haccept k))
    (modelValue_le_objective k)

/-- If each visited model value underestimates the objective along the trajectory, then the
objective values form an antitone sequence. -/
theorem objective_antitone
    {f : X → ℝ}
    {stepMap : ℝ → X → X}
    {modelValue : ℝ → X → ℝ}
    {L : ℝ}
    (method : RelaxedRegularizedNewtonIteration stepMap L)
    (haccept :
      ∀ k : ℕ,
        method.regularization k ∈ acceptingParameters f stepMap modelValue (method k))
    (modelValue_le_objective :
      ∀ k : ℕ, modelValue (method.regularization k) (method k) ≤ f (method k)) :
    Antitone (fun k ↦ f (method k)) :=
  antitone_nat_of_succ_le fun k ↦ by
    simpa using
      objective_values_nonincreasing
        method
        haccept
        modelValue_le_objective
        k

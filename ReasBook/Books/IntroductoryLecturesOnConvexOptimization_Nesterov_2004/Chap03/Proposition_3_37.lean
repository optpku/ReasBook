/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Algorithm_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace FunctionalConstraintSubgradientMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E 1}

/- Proposition 3.37 is a bridge/view item in the single-constraint subgradient-method domain.

Sampled owner-style declarations:
- `FunctionalConstraintSubgradientMethod.takesObjectiveStep` in `Algorithm_3_3`, the owner
  objective-branch predicate;
- `FunctionalConstraintSubgradientMethod.admissibleIndices` and
  `FunctionalConstraintSubgradientMethod.mem_admissibleIndices_iff` in `Algorithm_3_3`, the
  method-owned textbook family `𝒜(N)` and its canonical membership criterion;
- `ConstrainedSubgradientMethod324.admissibleIndices` in `Theorem_3_2_3` and
  `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices` in `Definition_3_45`,
  the chapter pattern for finite prefix index families on `Fin (N + 1)`.

Best owner abstraction:
- source-facing: the family `method.admissibleIndices N`;
- core/canonical: `takesObjectiveStep`;
- bridge/view: Proposition 3.37 itself, extracting the displayed inequality from membership in
  `𝒜(N)`.

Primitive data:
- the run `method : FunctionalConstraintSubgradientMethod problem`;
- the finite prefix length `N`.

Derived API:
- the owner-level family `method.admissibleIndices N`;
- the canonical membership criterion
  `k ∈ method.admissibleIndices N ↔ problem.constraints 0 (method k) ≤ method.ε`;
- the implication below.

This file no longer re-owns `𝒜(N)` or its membership lemma. Those belong to the method owner in
`Algorithm_3_3`; Proposition 3.37 is the downstream source-facing consequence theorem. -/

/-- Proposition 3.37: every index in `𝒜(N)` is a Case A iteration, hence its iterate satisfies
`f̄(x_k) ≤ ε`. -/
theorem constraint_le_epsilon_of_mem_admissibleIndices
    (method : FunctionalConstraintSubgradientMethod problem) (N : ℕ) {k : Fin (N + 1)}
    (hk : k ∈ method.admissibleIndices N) :
    problem.constraints 0 (method k) ≤ method.ε := by
  -- Membership in the owner-level admissible-index family is exactly the Case A inequality.
  exact (method.mem_admissibleIndices_iff N).1 hk

end FunctionalConstraintSubgradientMethod

end

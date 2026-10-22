/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

open scoped ConstrainedArgmin

noncomputable section

universe u v

section

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Text 6.1.5.1 lies in the chapter's smoothed-dual-oracle / proximal-subproblem decomposition
domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the Chapter 6 owner of the Step (b)
  regularized dual maximizer set;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Definition_6_30`, the bridge expanding that owner to
  the feasible-maximizer formulation;
- `proximalMinimizationProblem` in `Definition_6_26`, the Chapter 6 owner of the Step (c)
  estimating-function minimization problem;
- `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner of feasible minimizer sets.

Best owner abstraction:
- source-facing: the per-iteration split into the Step (b) dual-oracle maximization problem and
  the Step (c) proximal minimization problem;
- core/canonical: `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk`,
  `proximalMinimizationProblem Q₁ d₁ s`, `argmin[Set.univ]`, and `Set.prod`;
- bridge/view: the product of those two canonical solution sets, with membership expanded by
  `Set.mem_prod`.

Primitive data:
- the fixed iterate `y_k`, feasible sets `Q₁`, `Q₂`, linear map `A`, dual penalty `hatφ`,
  prox-terms `d₁`, `d₂`, smoothing parameter `μ`, and linear functional `s`.

Derived API:
- the Step (b) solution set `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk`;
- the Step (c) solution set `argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`;
- their combined decomposition view as a product of canonical solution sets.

Source/core/bridge triage:
- source-facing: Text 6.1.5.1's statement that one iteration decomposes into two canonical
  subproblems;
- core/canonical: the Chapter 6 dual-oracle argmax owner and the Chapter 1 constrained-argmin
  owner;
- bridge/view: the product-set view combining those two owners without introducing a second
  solution package.

The previous version introduced a public structure `SmoothedMethodIterationDecomposition` whose
primitive fields were a chosen dual maximizer and a chosen proximal minimizer. That was too
low-level for this text item: the source mathematics is the intrinsic decomposition into the two
canonical subproblems, not an auxiliary package of chosen outputs. This refinement therefore keeps
only the owner-level surface and the canonical product view of the two solution sets.
-/

variable
  {Q₁ : Set E₁} (Q₂ : Set E₂) (hatφ : E₂ → ℝ)
  (A : E₁ →L[ℝ] StrongDual ℝ E₂) (d₂ : E₂ → ℝ) (μ : ℝ)
  (d₁ : Q₁ → ℝ) (yk : Q₁) (s : StrongDual ℝ E₁)

/- Text 6.1.5.1 uses the Chapter 6 dual-oracle argmax owner for Step (b) and the Chapter 6
proximal minimization problem together with the Chapter 1 argmin owner for Step (c). -/
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff
recall proximalMinimizationProblem

/-- The per-iteration work of the smoothed method at `y_k` is encoded by the product of the Step
(b) smoothed-dual argmax set over `Q₂` and the Step (c) proximal minimizer set over `Q₁`. -/
def smoothedMethodIterationSubproblemSolutions :
    Set (E₂ × Q₁) :=
  smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk ×ˢ
    argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)

-- Proof sketch: unfold `smoothedMethodIterationSubproblemSolutions`, rewrite pair membership in
-- the product set via `Set.mem_prod`, and expand the Step (b) factor with
-- `mem_smoothedPrimalObjectiveArgmax_iff`.
/-- Text 6 1 5 1 Per Iteration Complexity Decomposition: a pair lies in
`smoothedMethodIterationSubproblemSolutions` exactly when its first component is a feasible
maximizer for the Step (b) smoothed oracle subproblem and its second component solves the Step
(c) proximal minimization subproblem. -/
theorem mem_smoothedMethodIterationSubproblemSolutions_iff
    {u : E₂} {x : Q₁} :
    (u, x) ∈ smoothedMethodIterationSubproblemSolutions Q₂ hatφ A d₂ μ d₁ yk s ↔
      u ∈ Q₂ ∧
        IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ yk) Q₂ u ∧
        x ∈ argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s) := by
  -- Rewrite the product decomposition into separate Step (b) and Step (c) memberships.
  rw [smoothedMethodIterationSubproblemSolutions, Set.mem_prod]
  -- Expand the Step (b) owner-level argmax set to the feasible-maximizer formulation.
  rw [mem_smoothedPrimalObjectiveArgmax_iff]
  -- Reassociate the resulting conjunctions into the theorem's stated order.
  constructor
  · rintro ⟨hu, hx⟩
    exact ⟨hu.1, hu.2, hx⟩
  · rintro ⟨hu_mem, hu_max, hx⟩
    exact ⟨⟨hu_mem, hu_max⟩, hx⟩

end

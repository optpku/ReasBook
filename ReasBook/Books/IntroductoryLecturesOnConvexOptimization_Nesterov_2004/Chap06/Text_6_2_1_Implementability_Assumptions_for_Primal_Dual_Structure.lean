/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Text 6.2.1 lies in the chapter's structured primal-dual implementability domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for the ambient
  primal-dual data `Q₁`, `Q₂`, `\hat f`, `\hat φ`, `A`, and their bounded/closed/convex/
  continuous structure;
- `proximalMinimizationProblem` in `Chap06/Definition_6_26`, the canonical owner for the primal
  prox subproblem on `Q₁`;
- `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the canonical owner for the
  regularized dual-oracle argmax set on `Q₂`;
- `η` in `Chap06/Proposition_6_23`, the chapter's positive-smoothing owner pattern
  `μ : {μ : ℝ // 0 < μ}` for a source-facing smoothing object.

Best owner abstraction:
- source-facing: `ImplementablePrimalDualStructure`;
- core/canonical: `StructuredObjectiveModel`, together with `proximalMinimizationProblem`,
  `smoothedPrimalObjectiveArgmax`, the positive smoothing-parameter subtype
  `{μ : ℝ // 0 < μ}`, `HasGradientWithinAt`, and `LipschitzOnWith`;
- bridge/view: the coercion to the primal prox solver, the raw `IsMinOn` / `IsMaxOn` companion
  lemmas, and the derived nonemptiness of `Q₁` and `Q₂` coming from the solver data.

Primitive data:
- the inherited structured-objective data from `StructuredObjectiveModel`;
- the prox terms `d₁`, `d₂`;
- a closed-form primal prox solver and a closed-form regularized dual oracle on the positive
  smoothing surface `μ : {μ : ℝ // 0 < μ}`;
- the within-gradient existence and Lipschitz constants for `hatf` on `Q₁` and `hatφ` on `Q₂`.

Derived API:
- the primal solver specification as membership in the canonical argmin set of
  `proximalMinimizationProblem`;
- the dual-oracle specification as membership in the canonical argmax set
  `smoothedPrimalObjectiveArgmax`;
- the inherited bounded/closed/convex/continuous structure from `StructuredObjectiveModel`;
- the raw minimizer and maximizer views and the induced nonemptiness of the feasible sets.

The previous version stored the ambient primal-dual data as loose parameters and thereby rebuilt a
parallel owner that dropped the inherited bounded/closed/convex/continuous structure already owned
by `StructuredObjectiveModel`. It also stored the tractability clauses as raw `IsMinOn` /
`IsMaxOn` formulas, duplicating the chapter owners already introduced for those subproblems, and
it made the dual oracle total at `μ = 0`. This refinement keeps the source-facing implementability
structure, but expresses it as additional data on top of the chapter owner `StructuredObjectiveModel`,
rewrites the solver API to the canonical owner declarations, and restricts the dual oracle to the
positive smoothing surface used elsewhere in Chapter 6.
-/

/-- Text 6.2.1-Implementability Assumptions for Primal-Dual Structure: an implementable
primal-dual representation provides closed-form solution operators for the primal proximal
subproblem on `Q₁` and, for each positive smoothing parameter `μ > 0`, the regularized dual
oracle subproblem on `Q₂`, and the functions `\hat f` and `\hat φ` have gradients that are
Lipschitz continuous on `Q₁` and `Q₂` with constants `L₁(\hat f)` and `L₂(\hat φ)`. -/
structure ImplementablePrimalDualStructure (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
    extends StructuredObjectiveModel E₁ E₂ where
  /-- The primal prox term `d₁`. -/
  primalProxFunction : E₁ → ℝ
  /-- The dual prox term `d₂`. -/
  dualProxFunction : E₂ → ℝ
  /-- The closed-form primal proximal solver `s ↦ x(s)`. -/
  primalProxSolver : StrongDual ℝ E₁ → primalSet
  /-- The primal proximal solver belongs to the canonical argmin set of the proximal subproblem
  on the inherited primal set. -/
  primalProxSolver_spec :
    ∀ s : StrongDual ℝ E₁,
      primalProxSolver s ∈
        argmin[Set.univ]
          (proximalMinimizationProblem primalSet (fun x : primalSet ↦ primalProxFunction x) s)
  /-- The closed-form dual oracle `u_μ(x)` returns a feasible maximizer of the regularized dual
  subproblem on the inherited dual set for each positive smoothing parameter `μ`. -/
  dualOracleSolver : primalSet → {μ : ℝ // 0 < μ} → dualSet
  /-- The dual oracle belongs to the canonical argmax set of the regularized dual maximand on
  the inherited dual set. -/
  dualOracleSolver_spec :
    ∀ (x : primalSet) (μ : {μ : ℝ // 0 < μ}),
      (dualOracleSolver x μ : E₂) ∈
        smoothedPrimalObjectiveArgmax linearMap dualSet dualPenalty dualProxFunction μ x
  /-- The Lipschitz constant `L₁(\hat f)` for the gradient of `\hat f` on `Q₁`. -/
  smoothPartGradientLipschitzConstant : NNReal
  /-- The gradient of `\hat f` exists on `Q₁` as the canonical within-gradient. -/
  smoothPart_hasGradientWithinAt :
    ∀ ⦃x : E₁⦄, x ∈ primalSet →
      HasGradientWithinAt smoothPart (gradientWithin smoothPart primalSet x) primalSet x
  /-- The gradient of `\hat f` is Lipschitz on `Q₁` with constant `L₁(\hat f)`. -/
  smoothPart_gradient_lipschitz :
    LipschitzOnWith smoothPartGradientLipschitzConstant
      (gradientWithin smoothPart primalSet) primalSet
  /-- The Lipschitz constant `L₂(\hat φ)` for the gradient of `\hat φ` on `Q₂`. -/
  dualPenaltyGradientLipschitzConstant : NNReal
  /-- The gradient of `\hat φ` exists on `Q₂` as the canonical within-gradient. -/
  dualPenalty_hasGradientWithinAt :
    ∀ ⦃u : E₂⦄, u ∈ dualSet →
      HasGradientWithinAt dualPenalty (gradientWithin dualPenalty dualSet u) dualSet u
  /-- The gradient of `\hat φ` is Lipschitz on `Q₂` with constant `L₂(\hat φ)`. -/
  dualPenalty_gradient_lipschitz :
    LipschitzOnWith dualPenaltyGradientLipschitzConstant
      (gradientWithin dualPenalty dualSet) dualSet

namespace ImplementablePrimalDualStructure

/-- An implementable primal-dual structure can be evaluated as its closed-form primal proximal
solver `s ↦ x(s)` on the inherited primal set. -/
instance : CoeFun (ImplementablePrimalDualStructure E₁ E₂)
    (fun problem ↦ StrongDual ℝ E₁ → problem.primalSet) where
  coe problem := problem.primalProxSolver

@[simp] theorem coe_apply
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (s : StrongDual ℝ E₁) :
    problem s = problem.primalProxSolver s :=
  rfl

theorem primalSet_nonempty
    (problem : ImplementablePrimalDualStructure E₁ E₂) :
    problem.primalSet.Nonempty :=
  ⟨problem.primalProxSolver 0, (problem.primalProxSolver 0).property⟩

theorem dualSet_nonempty
    (problem : ImplementablePrimalDualStructure E₁ E₂) :
    problem.dualSet.Nonempty := by
  let μ : {μ : ℝ // 0 < μ} := ⟨1, by positivity⟩
  exact
    ⟨problem.dualOracleSolver (problem.primalProxSolver 0) μ,
      (problem.dualOracleSolver (problem.primalProxSolver 0) μ).property⟩

theorem primalProxSolver_isMinOn
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (s : StrongDual ℝ E₁) :
    IsMinOn
      (proximalMinimizationProblem problem.primalSet
        (fun x : problem.primalSet ↦ problem.primalProxFunction x) s)
      Set.univ (problem.primalProxSolver s) := by
  exact (mem_constrainedArgmin_iff.mp (problem.primalProxSolver_spec s)).2

theorem dualOracleSolver_isMaxOn
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x : problem.primalSet) (μ : {μ : ℝ // 0 < μ}) :
    IsMaxOn
      (smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
        problem.dualProxFunction μ x)
      problem.dualSet
      (problem.dualOracleSolver x μ) := by
  exact
    (mem_smoothedPrimalObjectiveArgmax_iff problem.linearMap problem.dualSet
      problem.dualPenalty problem.dualProxFunction μ x
      (problem.dualOracleSolver x μ)).mp (problem.dualOracleSolver_spec x μ) |>.2

end ImplementablePrimalDualStructure

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.5 lies in the chapter's structured primal-dual convex-objective domain.

Sampled owner-style declarations:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the exact chapter owner for the
  structured primal-dual data
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical derived
  objective on the primal set
- `StructuredObjectiveModel.objective_apply` in `Chap06/Definition_6_6`, the exact source-facing
  evaluation formula
- `PrimalDualObjectiveModel` in `Chap06/Definition_6_28`, the later variant that adds
  nonemptiness hypotheses while already living at the same `NormedSpace` owner level

Best owner abstraction:
- source-facing/core: `StructuredObjectiveModel`
- bridge/view: the coercion from `StructuredObjectiveModel` to its objective function on
  `problem.primalSet`

Primitive data:
- the primal and dual feasible sets together with boundedness, closedness, and convexity
- the functions `smoothPart`, `dualPenalty`
- the linear map `linearMap`
- the continuity and convexity hypotheses for `smoothPart` and `dualPenalty`

Derived API:
- `StructuredObjectiveModel.maximand`
- `StructuredObjectiveModel.objective`
- the coercion to `problem.primalSet → EReal`
- `StructuredObjectiveModel.objective_apply`

Source/core/bridge triage:
- source-facing: `StructuredObjectiveModel`
- core/canonical: the same owner already introduced in `Definition_6_6`
- bridge/view: the objective coercion and the evaluation theorem

The owner abstraction already exists in `Definition_6_6`, so this item should be a direct
recall surface rather than a duplicate local structure. The textbook formula for `f` is then
recovered through the owner objective and its evaluation theorem.
-/

section

/- Definition 6.5: a structured objective model consists of bounded closed convex sets
`Q₁ ⊆ E₁` and `Q₂ ⊆ E₂`, continuous convex functions `\hat f` and `\hat φ`, and a linear
operator `A : E₁ → E₂*`; the associated primal objective is encoded by the recalled chapter
owner and its derived objective API. -/
recall StructuredObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] :
    Type (max u v)

/- The source-facing primal objective attached to a structured model is the direct owner API. -/
recall StructuredObjectiveModel.objective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal

/- The textbook evaluation formula is the direct recall of the owner theorem. -/
recall StructuredObjectiveModel.objective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

end

end

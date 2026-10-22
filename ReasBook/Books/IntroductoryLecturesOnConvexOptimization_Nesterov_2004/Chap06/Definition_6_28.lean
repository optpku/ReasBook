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

/- Definition 6.28 lies in the chapter's finite-dimensional primal-dual objective domain.

Mandatory domain-style sampling before drafting:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for the structured
  primal-dual data `Q₁`, `Q₂`, `\hat f`, `\hat φ`, and `A`;
- `StructuredObjectiveModel.objective` in `Chap06/Definition_6_6`, the canonical primal objective
  induced by that saddle representation;
- `StructuredObjectiveModel.primalOptimalValue` and
  `StructuredObjectiveModel.adjointOptimalValue` in `Chap06/Definition_6_6`, the canonical outer
  values corresponding to the textbook symbols `f^*` and `f_*`;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the canonical dual
  objective whose outer supremum gives `f_*`.

Best owner abstraction:
- source-facing: `PrimalDualObjectiveModel`, which adds the textbook finite-dimensional ambient
  hypotheses and nonemptiness of both feasible sets to the existing Chapter 6 owner;
- core/canonical: `StructuredObjectiveModel`;
- bridge/view: the recalled inherited value API below, with later attainment lemmas recovering the
  textbook min/max formulas from the `EReal` infimum/supremum surface.

Primitive data:
- the inherited structured-objective data from `StructuredObjectiveModel`;
- nonemptiness of the primal and dual feasible sets.

Derived API:
- the inherited owner functions `objective`, `primalOptimalValue`, `adjointObjective`, and
  `adjointOptimalValue`;
- the inherited pointwise formulas `objective_apply`, `primalOptimalValue_eq_saddle_form`,
  `adjointObjective_apply`, and `adjointOptimalValue_def`.

Source/core/bridge triage:
- source-facing: `PrimalDualObjectiveModel`;
- core/canonical: `StructuredObjectiveModel`;
- bridge/view: the recalled inherited value API below.

Definition 6.28 is not a pure recall item: besides the Chapter 6 structured-objective owner, it
adds the source hypotheses that both feasible sets are nonempty and that both ambient spaces are
finite-dimensional real vector spaces. The primal and adjoint value functions themselves remain the
canonical owner API rather than a duplicate `ℝ`-valued wrapper layer.
-/

/-- Definition 6.28 [Chapter6_1.json:65]: a primal-dual objective model consists of
finite-dimensional real vector spaces `E₁` and `E₂`, nonempty bounded closed convex sets
`Q₁ ⊆ E₁` and `Q₂ ⊆ E₂`, continuous convex functions `\hat f` on `Q₁` and `\hat φ` on `Q₂`,
and a linear map `A : E₁ → E₂*`. Its primal objective, adjoint objective, primal optimal value
`f^*`, and adjoint optimal value `f_*` are the canonical Chapter 6 constructions attached to this
structured data. -/
structure PrimalDualObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    extends StructuredObjectiveModel E₁ E₂ where
  /-- The primal feasible set `Q₁` is nonempty. -/
  primalSet_nonempty : primalSet.Nonempty
  /-- The dual feasible set `Q₂` is nonempty. -/
  dualSet_nonempty : dualSet.Nonempty

namespace PrimalDualObjectiveModel

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]

/-- A primal-dual objective model inherits its underlying Chapter 6 structured objective model. -/
instance : Coe (PrimalDualObjectiveModel E₁ E₂) (StructuredObjectiveModel E₁ E₂) where
  coe problem := problem.toStructuredObjectiveModel

section

/- The primal objective of Definition 6.28 is the inherited Chapter 6 owner function. -/
recall StructuredObjectiveModel.objective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal

/- The primal optimal value `f^*` is the inherited outer infimum of the primal objective. -/
recall StructuredObjectiveModel.primalOptimalValue
    (problem : StructuredObjectiveModel E₁ E₂) : EReal

/- The adjoint objective `φ` of Definition 6.28 is the inherited Chapter 6 dual objective. -/
recall StructuredObjectiveModel.adjointObjective
    (problem : StructuredObjectiveModel E₁ E₂) : problem.dualSet → EReal

/- The adjoint optimal value `f_*` is the inherited outer supremum of the adjoint objective. -/
recall StructuredObjectiveModel.adjointOptimalValue
    (problem : StructuredObjectiveModel E₁ E₂) : EReal

/- The textbook saddle formula for the primal objective is the inherited owner theorem. -/
recall StructuredObjectiveModel.objective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

/- The textbook outer primal value is the inherited infimum of the saddle-form objective. -/
recall StructuredObjectiveModel.primalOptimalValue_eq_saddle_form
    (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalOptimalValue =
      sInf (Set.range fun x : problem.primalSet ↦
        sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)))

/- The textbook formula for the adjoint objective is the inherited owner theorem. -/
recall StructuredObjectiveModel.adjointObjective_apply
    (problem : StructuredObjectiveModel E₁ E₂) (u : problem.dualSet) :
    problem.adjointObjective u =
      sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal))

/- The adjoint optimal value is the inherited outer supremum of the adjoint objective. -/
recall StructuredObjectiveModel.adjointOptimalValue_def
    (problem : StructuredObjectiveModel E₁ E₂) :
    problem.adjointOptimalValue = sSup (Set.range problem.adjointObjective)

end

end PrimalDualObjectiveModel

end

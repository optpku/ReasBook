/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_6

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Proposition 6.4 lies in the chapter's structured primal-dual weak-duality domain.

Sampled owner-style declarations in this domain:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for the structured
  saddle-point data;
- `StructuredObjectiveModel.objective`, the canonical primal value function on `Q₁`;
- `StructuredObjectiveModel.adjointObjective`, the canonical dual value function on `Q₂`;
- `iInf_le`, `le_iSup`, and `iSup_iInf_le_iInf_iSup` in mathlib's complete-lattice order API,
  the canonical owner theorems for pointwise slice comparison and the maximin `≤` minimax
  inequality on `EReal`.

Best owner abstraction:
- source-facing: weak duality for a `StructuredObjectiveModel`;
- core/canonical: the owner's complete-lattice `iInf`/`iSup` surfaces for
  `adjointObjective`, `objective`, `adjointOptimalValue`, and `primalOptimalValue`;
- bridge/view: the pointwise comparison
  `StructuredObjectiveModel.adjointObjective_le_objective`.

Primitive data:
- the structured model `problem`.

Derived API:
- `problem.saddleFunction`;
- `problem.objective`;
- `problem.adjointObjective`;
- `problem.primalOptimalValue`;
- `problem.adjointOptimalValue`.

Source/core/bridge triage:
- source-facing: `StructuredObjectiveModel.weakDuality`;
- core/canonical: the owner API from `Definition_6_6` together with `iInf`, `iSup`, and
  `iSup_iInf_le_iInf_iSup`;
- bridge/view: the pointwise saddle comparison theorem
  `StructuredObjectiveModel.adjointObjective_le_objective`.

The previous file kept an attained-extrema specialization as the main proposition. Since
`Definition_6_6` already places the chapter API in `EReal`, weak duality is canonical directly at
the owner level and needs no extra attainment hypotheses. The main proposition therefore reuses the
generic complete-lattice weak-duality owner instead of reproving the same `sSup`/`sInf` pattern
locally.
-/

namespace StructuredObjectiveModel

/-- For every feasible primal-dual pair `(x, u)`, the structured adjoint objective at `u` is
bounded above by the structured primal objective at `x`. -/
theorem adjointObjective_le_objective
    (problem : StructuredObjectiveModel E₁ E₂)
    (u : problem.dualSet) (x : problem.primalSet) :
    problem.adjointObjective u ≤ problem.objective x := by
  change (⨅ x' : problem.primalSet, (problem.saddleFunction x' u : EReal)) ≤
    ⨆ u' : problem.dualSet, (problem.saddleFunction x u' : EReal)
  exact (iInf_le (fun x' : problem.primalSet ↦ (problem.saddleFunction x' u : EReal)) x).trans
    (le_iSup (fun u' : problem.dualSet ↦ (problem.saddleFunction x u' : EReal)) u)

/-- Proposition 6.4: every structured objective model satisfies the weak-duality inequality
`f_* ≤ f^*`. -/
theorem weakDuality
    (problem : StructuredObjectiveModel E₁ E₂) :
    problem.adjointOptimalValue ≤ problem.primalOptimalValue := by
  change (⨆ u : problem.dualSet, ⨅ x : problem.primalSet, (problem.saddleFunction x u : EReal)) ≤
    ⨅ x : problem.primalSet, ⨆ u : problem.dualSet, (problem.saddleFunction x u : EReal)
  exact iSup_iInf_le_iInf_iSup fun u x ↦ (problem.saddleFunction x u : EReal)

end StructuredObjectiveModel

end

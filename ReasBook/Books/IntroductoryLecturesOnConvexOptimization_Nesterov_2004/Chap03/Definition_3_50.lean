/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Set Metric

variable {E : Type*} [PseudoMetricSpace E]

/- This item lies in the chapter's interior-point domain.

Sampled owner-style declarations:
- `Set.interior`, the canonical topological owner of interior points;
- `mem_interior`, the owner theorem exposing interior membership by an open subset;
- `Metric.mem_nhds_iff`, the metric-space owner theorem turning neighborhood membership into
  contained-ball data;
- `exists_ball_subset_effectiveDomain_of_mem_interior` in `Theorem_3_1_11`, the chapter's earlier
  source-facing effective-domain specialization of the same topological owner abstraction;
- `exists_hard_feasibility_problem_for_short_separation_oracle_algorithms` in `Theorem_3_49`,
  whose hard-instance conclusion reuses the same owner predicate downstream in the chapter.

Best abstraction triage:
- source-facing: the canonical interior-nonemptiness predicate attached to `S`;
- core/canonical: `(interior S).Nonempty`;
- bridge/view: `interior_ball_assumption_iff_interior_nonempty`, identifying the textbook
  interior-ball formulation with the owner predicate.

Primitive data:
- the set `S ⊆ E`.

Derived API:
- the textbook interior-ball existential, derived from metric openness of `interior S`;
- center membership in `S`, derived from `0 < ε` and `Metric.ball xStar ε ⊆ S`;
- the bridge equivalence between the textbook ball condition and the owner predicate.

Source/core/bridge triage:
- source-facing: `(interior S).Nonempty`;
- core/canonical: `Set.interior`;
- bridge/view: `interior_ball_assumption_iff_interior_nonempty`.

This file therefore keeps the owner predicate itself as the main numbered recall, and records the
textbook ball formulation only as a companion bridge theorem. -/

section

variable (S : Set E)

/-
Definition 3.50: a set satisfies the interior ball assumption exactly when it has a nonempty
interior. The textbook Euclidean-ball formulation is recorded below as a bridge theorem, while the
main owner expression is the canonical predicate `(interior S).Nonempty`.
-/
#check (interior S).Nonempty

/-- The textbook interior-ball formulation is equivalent to the canonical owner predicate
`(interior S).Nonempty`. -/
-- Proof sketch: translate interior membership to neighborhood membership by
-- `mem_interior_iff_mem_nhds`, then use `Metric.mem_nhds_iff` to pass between neighborhoods and
-- contained positive-radius balls.
theorem interior_ball_assumption_iff_interior_nonempty :
    (∃ xStar : E, ∃ ε > 0, ball xStar ε ⊆ S) ↔ (interior S).Nonempty := by
  constructor
  · rintro ⟨xStar, ε, hε, hball⟩
    refine ⟨xStar, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    exact Metric.mem_nhds_iff.mpr ⟨ε, hε, hball⟩
  · rintro ⟨xStar, hxStar⟩
    rw [mem_interior_iff_mem_nhds] at hxStar
    rcases Metric.mem_nhds_iff.mp hxStar with ⟨ε, hε, hball⟩
    exact ⟨xStar, ε, hε, hball⟩

end

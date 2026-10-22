/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.5 lies in the chapter's real epigraph domain.

Sampled owner declarations:
- `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter owner for epigraphs over a feasible set;
- `strictConstrainedEpigraph` from `Chap05/Theorem_5_3_5`, the strict-epigraph companion in the
  same chapter API;
- mathlib `ConvexOn.convex_epigraph`, the standard convex-epigraph owner theorem;
- mathlib `LowerSemicontinuous.isClosed_epigraph`, the standard closed-epigraph owner theorem.

Best owner abstraction:
- core/canonical:
  `constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))`.

Primitive data:
- the positive half-line `(0, ∞)`;
- the function `x ↦ -log x`.

Derived API:
- the epigraph set itself;
- its specialized membership expansion.

Source/core/bridge triage:
- source-facing: the textbook set `Q₁`;
- core/canonical: the chapter epigraph owner `constrainedEpigraph`;
- bridge/view: the specialized membership theorem below.

This item therefore deletes the parallel local set `q1NegativeLogEpigraph` and reuses the chapter
epigraph owner directly. -/

/- Definition 5.4.8.5 recalls the chapter epigraph owner specialized to `x ↦ -log x` on
`(0, ∞)`. -/
#check constrainedEpigraph (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ (-Real.log x : WithTop ℝ))

/-- Membership in the canonical epigraph expression for Definition 5.4.8.5 means that `x > 0`
and `t ≥ -log x`. -/
theorem mem_constrainedEpigraph_negLog_iff {x t : ℝ} :
    (x, t) ∈ constrainedEpigraph (Set.Ioi (0 : ℝ))
      (fun y : ℝ ↦ (-Real.log y : WithTop ℝ)) ↔
      0 < x ∧ t ≥ -Real.log x := by
  rw [mem_constrainedEpigraph_iff]
  constructor
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt
  · rintro ⟨hx, hxt⟩
    refine ⟨hx, ?_⟩
    exact_mod_cast hxt

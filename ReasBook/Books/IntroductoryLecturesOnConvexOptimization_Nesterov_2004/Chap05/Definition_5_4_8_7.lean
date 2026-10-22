/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.8.7 is a recall-only item in the Chapter 5 exponential-epigraph domain.

Primary domain:
- the exponential epigraph in `ℝ × ℝ`.

Sampled owner declarations:
- `exponentialEpigraphQ2` from `Theorem_5_4_8_3`, the existing chapter source-facing owner for the
  textbook set `Q₂`;
- `mem_exponentialEpigraphQ2_iff` from `Theorem_5_4_8_3`, the canonical companion theorem for the
  defining inequality;
- `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter core epigraph owner underlying
  this example;
- `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the generic membership expansion
  for that core owner.

Best owner abstraction:
- source-facing owner for this numbered item: `exponentialEpigraphQ2`;
- deeper core/canonical bridge: `constrainedEpigraph (Set.univ : Set ℝ)
  (fun x : ℝ ↦ (Real.exp x : WithTop ℝ))`.

Primitive data:
- none in this file; the source-facing owner is already defined upstream in the chapter.

Derived API:
- the owner declaration `exponentialEpigraphQ2`;
- the defining membership theorem `mem_exponentialEpigraphQ2_iff`.

Source/core/bridge triage:
- source-facing: `exponentialEpigraphQ2`, the textbook set `Q₂`;
- core/canonical: the constrained-epigraph expression specialized to `x ↦ exp x`;
- bridge/view: the identification already supplied upstream by
  `mem_exponentialEpigraphQ2_iff`.

The previous version duplicated the chapter source-facing owner by making the deeper epigraph
bridge the main public surface and adding a second membership theorem for the same set. This file
now reuses the existing owner directly and leaves the canonical epigraph expression as background
structure rather than as a competing public API. -/

/- Definition 5.4.8.7 recalls the existing chapter owner for the textbook exponential epigraph
`Q₂`. -/
recall exponentialEpigraphQ2 : Set (ℝ × ℝ)

/- The defining inequality for `Q₂` is recalled through its canonical companion theorem. -/
recall mem_exponentialEpigraphQ2_iff {x t : ℝ} :
    (x, t) ∈ exponentialEpigraphQ2 ↔ t ≥ Real.exp x

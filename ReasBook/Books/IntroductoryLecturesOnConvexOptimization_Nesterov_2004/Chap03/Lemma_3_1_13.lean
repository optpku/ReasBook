/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/- Lemma 3.1.13 is a recall-only bridge in the chapter's finite-family pointwise-supremum /
subdifferential calculus domain for `WithTop ℝ`-valued convex functions.

Primary domain:
- finite nonempty pointwise suprema of closed convex extended-real-valued functions on the
  chapter's intrinsic ambient spaces.

Relevant sampled declarations in this domain:
- `pointwiseSupremumOn`
- `activePointwiseSupremumOnIndices`
- `ClosedConvexFunction`
- `subdifferential`

Best owner abstraction:
- the chapter owner `pointwiseSupremumOn`, specialized in `Lemma_3_13` to the finite set
  `Set.univ`.

Primitive data:
- none in this recall file; the imported owner surface already carries the only primitive
  mathematical inputs, namely a nonempty finite index type together with a family
  `φ : X → ι → WithTop ℝ`.

Derived API recalled here:
- the finite-supremum bridge `pointwiseSupremumOn_univ_eq_sup'`
- the finite active-set bridge
- the closed-convex, interior-domain, and active-subdifferential theorems for the `Set.univ`
  specialization

Source/core/bridge triage:
- source-facing: the finite-family specialization of Lemma 3.13
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`,
  `ClosedConvexFunction`, and `subdifferential`
- bridge/view: `pointwiseSupremumOn_univ_eq_sup'`,
  `mem_activePointwiseSupremumOnIndices_univ_iff`, and this numbered recall surface

This file now recalls the owner-centered `Set.univ` specialization instead of maintaining a
parallel finite-maximum wrapper layer.
-/

recall pointwiseSupremumOn_univ_eq_sup'
recall mem_activePointwiseSupremumOnIndices_univ_iff
recall closedConvexFunction_pointwiseSupremumOn_univ
recall interior_dom_pointwiseSupremumOn_univ
recall subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials

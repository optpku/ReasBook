/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 2.12 is a recall-only item in the epigraph convexity domain for real-valued convex
functions.

Primary domain:
- convexity of epigraphs of convex functions.

Sampled owner-style declarations:
- `ConvexOn`
- `ConvexOn.convex_epigraph`
- `convexOn_iff_convex_epigraph`
- the later Euclidean specialization in `Chap03/Theorem_3_1_2`

Best owner abstraction:
- `ConvexOn.convex_epigraph`

Primitive data:
- a function `f`
- the owner hypothesis `hf : ConvexOn 𝕜 s f`

Derived API:
- convexity of the epigraph `{p | p.1 ∈ s ∧ f p.1 ≤ p.2}`
- in the textbook whole-space specialization, simplification of `p.1 ∈ Set.univ`

Source/core/bridge triage:
- source-facing: Lemma 2.12 as the whole-space epigraph convexity consequence
- core/canonical: `ConvexOn.convex_epigraph`
- bridge/view: specialization to `s = Set.univ`

This file therefore keeps no parallel whole-space wrapper theorem and recalls the canonical owner
declaration directly. -/

recall ConvexOn.convex_epigraph

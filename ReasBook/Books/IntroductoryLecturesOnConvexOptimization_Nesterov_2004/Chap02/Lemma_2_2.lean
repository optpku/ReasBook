/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 2.2 lies in Euclidean first-order convex analysis under affine pullback.

Sampled owner-style declarations:
- mathlib `ContDiffOn.comp`
- mathlib `ConvexOn.comp_affineMap`
- Chapter 2 `ConvexC1On.comp_continuousAffineMap`
- Chapter 2 `ConvexC1On.comp_affineMap`

Best owner abstraction:
- `ConvexC1On.comp_continuousAffineMap`, the canonical owner-level precomposition theorem for the
  `ConvexC1On` owner predicate.

Primitive data:
- the source set `Q`
- the objective `f`
- the owner hypothesis `hf : ConvexC1On Q f`
- the affine map `g`

Derived API:
- the Euclidean specialization `ConvexC1On.comp_affineMap`, obtained from finite-dimensional
  continuity of affine maps.

Source/core/bridge triage:
- source-facing: Lemma 2.2's Euclidean affine pullback statement
- core/canonical: `ConvexC1On.comp_continuousAffineMap`
- bridge/view: the finite-dimensional specialization `ConvexC1On.comp_affineMap`

This item no longer keeps a parallel local theorem shell. The source-facing Euclidean statement now
lives with the `ConvexC1On` owner in `Definition_2_4`, and this file is a direct recall of that
canonical bridge.
-/

recall ConvexC1On.comp_affineMap

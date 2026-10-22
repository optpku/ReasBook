/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.5 is a recall-only surface in the chapter's finite directional-derivative domain.

Primary domain:
- finite one-sided directional derivatives of convex `ℝ ∪ {+∞}`-valued functions at interior
  points of the effective domain.

Sampled owner-style declarations:
- `convexDirectionalDerivative` in `Theorem_3_21`, the chapter owner for the extended-valued
  directional derivative;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the owner
  convexity theorem for the finite theorem-surface view;
- `convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior` and
  `convexDirectionalDerivativeReal_affine_support_of_mem_interior` in `Lemma_3_1_3_1`, the
  source-facing real-valued consequences already consolidated by `Lemma_3_1_5`.

Best owner abstraction:
- the finite directional-derivative owner `f′[hx]`, with the recalled consequence surface
  already gathered upstream by `Lemma_3_1_5`.

Primitive data:
- none in this file; all directional-derivative data is already owned upstream.

Derived API:
- the recalled convexity, positive-homogeneity, and affine-support consequences at an interior
  point.

Source/core/bridge triage:
- source-facing: the three consequences asserted in Lemma 3.5 for the finite directional
  derivative;
- core/canonical: `convexDirectionalDerivative`;
- bridge/view: this numbered-item recall surface, reusing `Lemma_3_1_5`.

The previous version repeated the same three recalls with a second local domain summary. This file
now reuses the earlier chapter recall surface directly and keeps only the numbered-item layer.
-/

recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_affine_support_of_mem_interior

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.5 is now a recall-only surface in the chapter's finite directional-derivative
domain.

Sampled owner-style declarations:
- `convexDirectionalDerivative` in `Theorem_3_21`, the owner extended-valued directional
  derivative;
- `convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior` in `Theorem_3_21`, the owner
  convexity theorem for the theorem-level finite directional-derivative view;
- `convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior`, whose canonical pointwise
  scaling surface is the owner projection `map_smul`, and
  `convexDirectionalDerivativeReal_affine_support_of_mem_interior` in `Lemma_3_1_3_1`, the
  source-facing real directional-derivative consequences.

Best owner abstraction:
- `convexDirectionalDerivative`, together with its theorem-level finite directional-derivative
  view.

Primitive data:
- none in this file; all directional-derivative data is already owned upstream.

Derived API:
- the recalled real-valued consequences used at this point in the chapter.

Source/core/bridge triage:
- source-facing: the real-valued convexity, positive-homogeneity, and affine-support statements;
- core/canonical: `convexDirectionalDerivative`;
- bridge/view: this recall surface.

The previous version duplicated the same real-valued theorem surface with local proofs. This file
now recalls the canonical chapter declarations directly instead of keeping a second parallel copy.
-/

recall convexDirectionalDerivativeReal_convexOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_posHomOn_univ_of_mem_interior

recall convexDirectionalDerivativeReal_affine_support_of_mem_interior

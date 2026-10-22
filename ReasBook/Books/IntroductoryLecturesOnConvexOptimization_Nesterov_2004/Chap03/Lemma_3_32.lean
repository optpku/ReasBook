/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7

-- Declarations for this item will be appended below by the statement pipeline.

section

open MeasureTheory

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open scoped EllipsoidNotation

/-
Lemma 3.32 is a downstream recall of the chapter's ellipsoid-update owner API.

Sampled owner-style declarations:
- `affineEllipsoid` in `Lemma_3_2_7`, the source-facing owner of the textbook ellipsoid
  `E(H, x̄)`;
- `centerCutEllipsoid` in `Lemma_3_2_7`, the source-facing owner of the center cut `E₊`;
- `updatedEllipsoidCenter` and `updatedEllipsoidMatrix` in `Lemma_3_2_7`, the textbook ellipsoid
  update formulas;
- `centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le` in `Lemma_3_2_7`, the owner theorem
  for the containment and volume decrease.

Best owner abstraction:
- source-facing/core owner: the ellipsoid-update API already introduced in `Lemma_3_2_7`;
- bridge/view: this file is recall-only.

Primitive data:
- `H : Mat`;
- `xBar g : E`;
- the valid-update hypotheses `H.PosDef`, `g ≠ 0`, and `1 < n` for the containment theorem.

Derived API:
- the ellipsoid `affineEllipsoid H xBar`;
- the center cut `centerCutEllipsoid H xBar g`;
- the updated center and shape matrix;
- the canonical containment and volume-decrease theorem.

Source/core/bridge triage:
- source-facing: the textbook ellipsoid update and its containment/volume statement;
- core/canonical: the existing owner declarations from `Lemma_3_2_7`;
- bridge/view: this recall file.

Accordingly, this file no longer keeps parallel local copies of the ellipsoid-update definitions or
their main theorem. The owner objects already live upstream, so this file stays theorem-recall-only
and reuses the canonical containment/volume statement directly.
-/

recall centerCutEllipsoid_subset_updatedEllipsoid_and_volume_le
    (H : Mat) (hH : H.PosDef) (xBar g : E) (hg : g ≠ 0) (hn : 1 < n) :
    E₊(H, xBar, g) ⊆ E(H₊(H, g), x̄₊(H, xBar, g)) ∧
      ((volume (E(H₊(H, g), x̄₊(H, xBar, g)))).toReal ≤
        Real.rpow (1 - 1 / (((n : ℝ) + 1) ^ (2 : ℕ))) ((n : ℝ) / 2) *
          (volume (E(H, xBar))).toReal)

end

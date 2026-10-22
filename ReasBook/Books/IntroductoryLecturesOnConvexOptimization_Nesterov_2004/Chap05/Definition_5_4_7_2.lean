/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.7.2 stays in the same planar power-cone barrier domain as
`Definition_5_4_7_1`.

Sampled owner declarations:
* `powerConeQ2` from `Definition_5_4_7_1`, the earlier source-facing owner for the planar cone
  `Q₂`;
* `secondOrderCone` and `secondOrderConeBarrier` from `Lemma_5_4_3_3`, the chapter owner/view for
  the same geometry in canonical `(x, t)` coordinates;
* `Prod.swap`, the canonical bridge between the source `(y, z)` coordinates and the owner
  `(z, y)` coordinates.

Source/core/bridge triage:
* source-facing: the textbook barrier on `Q₂`;
* core/canonical: `secondOrderConeBarrier`;
* bridge/view: the coordinate swap `Prod.swap`.

This file therefore keeps no second public barrier owner: Definition 5.4.7.2 is a recall of the
canonical barrier `secondOrderConeBarrier` seen in `(y, z)` coordinates through `Prod.swap`. -/

set_option linter.hashCommand false in
/- Definition 5.4.7.2 recalls the `(y, z)`-coordinate specialization of the canonical
second-order-cone barrier. -/
#check (secondOrderConeBarrier ∘ Prod.swap : (ℝ × ℝ) → ℝ)

-- Proof sketch: evaluate `secondOrderConeBarrier` at `(z, y)`.
/-- Evaluating the recalled swapped-coordinate second-order-cone barrier at `(y, z)` reproduces
the textbook formula `Φ(y, z) = -log (y^2 - z^2)`. -/
theorem secondOrderConeBarrier_swap_apply (y z : ℝ) :
    (secondOrderConeBarrier ∘ Prod.swap) (y, z) = -Real.log (y ^ (2 : ℕ) - z ^ (2 : ℕ)) := by
  simp [secondOrderConeBarrier_apply]

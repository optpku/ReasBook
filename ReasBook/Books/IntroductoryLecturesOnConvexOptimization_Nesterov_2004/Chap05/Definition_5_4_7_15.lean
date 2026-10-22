/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EuclideanOrthant

/- Definition 5.4.7.15 lies in the Chapter 5 positive-orthant / logarithmic-barrier domain.

Primary domain:
* the strict positive orthant and its standard logarithmic barrier.

Sampled owner declarations:
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the canonical owner and membership view for the strict positive
  orthant;
* `logarithmicBarrier` from `Chap01/Proposition_1_10_17`, the chapter owner for logarithmic
  barriers on strict inequality loci;
* `standardLogarithmicBarrier` from `Definition_5_4_3_2`, the intrinsic Chapter 5 specialization
  of that owner to `positiveOrthant n`;
* `standardLogarithmicBarrierAmbient` from `Definition_5_4_3_2`, the thin ambient bridge used by
  downstream self-concordance files.

Best owner abstraction:
* source-facing: `positiveOrthant n` together with its standard logarithmic barrier;
* core/canonical: the upstream owners `EuclideanSpace.positiveOrthant` and
  `standardLogarithmicBarrier`;
* bridge/view: `standardLogarithmicBarrierAmbient`.

Primitive data:
* the positive orthant owner `EuclideanSpace.positiveOrthant n`.

Derived API:
* the intrinsic barrier owner
  `standardLogarithmicBarrier n : C(↑(EuclideanSpace.positiveOrthant n), ℝ)`;
* the ambient bridge
  `standardLogarithmicBarrierAmbient n : EuclideanSpace ℝ (Fin n) → ℝ`.

This item is therefore recall-only. The file keeps no parallel local copy of the positive-orthant
barrier data and points directly to the existing owner declarations from Chapter 1 / Definition
5.4.3.2. -/

/- Definition 5.4.7.15 recalls the Chapter 1 positive orthant owner. -/
recall EuclideanSpace.positiveOrthant
    (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n))

/- The intrinsic positive-orthant logarithmic barrier is recalled from Definition 5.4.3.2. -/
recall standardLogarithmicBarrier
    (n : ℕ) :
    C(↑(ℝ₊₊^n), ℝ)

/- The ambient bridge for the same barrier is recalled through its canonical owner declaration. -/
recall standardLogarithmicBarrierAmbient
    (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ

end

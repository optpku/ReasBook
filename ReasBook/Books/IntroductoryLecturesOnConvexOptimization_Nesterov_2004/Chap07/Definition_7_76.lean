/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped EuclideanOrthant

noncomputable section

/- Definition 7.76 lies in Chapter 7's positive-orthant / logarithmic-barrier domain.

Mandatory domain-style sampling before refinement:
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the project owner and coordinatewise membership bridge for the
  strict positive orthant;
- `logarithmicBarrier` in `Chap01/Proposition_1_10_17`, the canonical logarithmic-barrier owner on
  strict inequality loci;
- `standardLogarithmicBarrier` and `standardLogarithmicBarrier_apply` in
  `Chap05/Definition_5_4_3_2`, the exact specialization to the strict positive orthant;
- `standardLogarithmicBarrierAmbient` in `Chap05/Definition_5_4_3_2`, the thin ambient bridge for
  the same owner.

Best owner abstraction:
- source-facing: the logarithmic barrier on the interior of `ℝⁿ₊`, i.e. the strict positive
  orthant;
- core/canonical: `positiveOrthant n` and `standardLogarithmicBarrier n`;
- bridge/view: `EuclideanSpace.mem_positiveOrthant_iff`,
  `standardLogarithmicBarrier_apply`, and `standardLogarithmicBarrierAmbient`.

Primitive data:
- the dimension `n`;
- the intrinsic strict positive orthant `positiveOrthant n`.

Derived API:
- the coordinatewise positivity bridge for points of `positiveOrthant n`;
- the intrinsic barrier owner `standardLogarithmicBarrier n`;
- the ambient bridge `standardLogarithmicBarrierAmbient n`;
- the textbook evaluation formula for the intrinsic barrier, available directly from the owner
  file `Chap05/Definition_5_4_3_2`.

Source/core/bridge triage:
- source-facing: Definition 7.76's logarithmic barrier on the strict positive orthant;
- core/canonical: `EuclideanSpace.positiveOrthant` and `standardLogarithmicBarrier`;
- bridge/view: the membership theorem recalled below and the ambient bridge.

The previous file duplicated both the strict-orthant carrier and the same logarithmic barrier
already owned earlier in the project. This refinement keeps Definition 7.76 recall-only and
reuses the existing owner declarations directly instead of maintaining parallel Chapter 7 names.
-/

/- Definition 7.76 recalls the strict positive orthant `ℝⁿ₊₊`. -/
recall EuclideanSpace.positiveOrthant
    (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n))

/- Membership in the recalled strict positive orthant is coordinatewise strict positivity. -/
recall EuclideanSpace.mem_positiveOrthant_iff
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ ℝ₊₊^n ↔ ∀ i : Fin n, 0 < x i

/- Definition 7.76 recalls the intrinsic logarithmic barrier on the strict positive orthant. -/
recall standardLogarithmicBarrier
    (n : ℕ) :
    C(↑(ℝ₊₊^n), ℝ)

/- The ambient bridge for the same barrier is recalled from the canonical owner file. -/
recall standardLogarithmicBarrierAmbient
    (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ

end

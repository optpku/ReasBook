/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}
variable (problem : SeparableOptimizationProblem E m)

/-
Definition 5.4.8.2 lies in the separable optimization / finite additive aggregation domain.

Sampled owner declarations:
- `SeparableOptimizationProblem` in `Definition_5_4_8_1`, the chapter owner of the separable
  problem data;
- `SeparableOptimizationProblem.blockSize` in `Definition_5_4_8_1`, the source-facing field
  recording the block counts `mᵢ`;
- `Finset.sum`, the canonical owner for finite additive aggregation;
- `Fin.sum_univ_eq_sum_range` and `Fin.sum_univ_succ`, the standard bridges from a `Fin`-indexed
  sum to textbook range and head-tail presentations.

Best owner abstraction:
- source-facing: the textbook quantity `M = \sum_{i=0}^m mᵢ` attached to
  `problem : SeparableOptimizationProblem E m`;
- core/canonical: the block-count field `problem.blockSize` together with the canonical sum
  `∑ i, problem.blockSize i`;
- bridge/view: `Fin.sum_univ_eq_sum_range` and `Fin.sum_univ_succ`.

Primitive data:
- `problem : SeparableOptimizationProblem E m`.

Derived API:
- `problem.blockSize : Fin (m + 1) → ℕ`;
- the canonical total block count `∑ i, problem.blockSize i`;
- the standard range and successor decompositions of that same finite sum.

Source/core/bridge triage:
- source-facing: the total number `M` of univariate terms in the separable problem;
- core/canonical: the chapter owner `SeparableOptimizationProblem` and its field `blockSize`;
- bridge/view: the generic `Fin`-sum decomposition lemmas.

This file therefore does not keep a free-standing family of counts. Definition 5.4.8.2 is read
through the chapter owner `problem : SeparableOptimizationProblem E m`, and the textbook quantity
`M` is expressed directly as `∑ i, problem.blockSize i`.
-/

/- Definition 5.4.8.2 recalls the chapter owner field for the block counts `mᵢ`. -/
#check SeparableOptimizationProblem.blockSize

/- Definition 5.4.8.2 recalls the canonical finite-sum owner and its standard `Fin` bridges. -/
recall Finset.sum
recall Fin.sum_univ_eq_sum_range
recall Fin.sum_univ_succ

/- Definition 5.4.8.2 expresses the total number of univariate terms as the canonical sum
`M = \sum_{i=0}^m mᵢ` attached to `problem`. -/
#check ∑ i, problem.blockSize i

end SeparableOptimizationProblem

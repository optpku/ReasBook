/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.1.1 is a recall-only Euclidean specialization in the finite Jensen domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `Lemma_3_1_1`, the earlier chapter recall of `ConvexOn.map_sum_le`
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `Convex.sum_mem`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → EuclideanSpace ℝ (Fin n)` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ` summing to `1`

Derived API:
- the Euclidean specialization of Jensen's inequality
- the positivity-to-nonnegativity bridge `0 < α i → 0 ≤ α i`, which belongs only at use sites

Source/core/bridge triage:
- source-facing: the textbook Euclidean specialization
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: specializing the ambient module to `EuclideanSpace ℝ (Fin n)`

This item adds no new mathematics beyond the owner theorem. The source's positivity wording is a
use-site bridge to the owner's nonnegativity hypothesis, so the file keeps the owner declaration as
the main public entry and lets the Euclidean specialization elaborate directly at call sites. -/

recall ConvexOn.map_sum_le

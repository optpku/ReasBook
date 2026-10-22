/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1 lies in the finite Jensen / convex-combination domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `Convex.sum_mem`
- `ConvexOn.map_add_sum_le`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → E` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ` with `0 ≤ α i` and `∑ i, α i = 1`

Derived API:
- Jensen's inequality at the weighted sum `∑ i, α i • x i`
- the separate domain-membership consequence from `Convex.sum_mem`
- any simplex-packaged or convex-combination-packaged presentation as downstream bridge API, not as
  the owner theorem itself

Source/core/bridge triage:
- source-facing: the explicit finite Jensen inequality from the text
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: `Convex.sum_mem` for domain membership, and later chapter simplex packaging only as a
  presentation layer for the same finite weighted-sum data

The textbook item is Jensen's inequality itself. Since mathlib already owns that statement in the
correct nonnegative-weight form, this file centers the canonical owner declaration directly. The
domain-membership consequence belongs to `Convex.sum_mem` and is not bundled into the main item.
-/

recall ConvexOn.map_sum_le

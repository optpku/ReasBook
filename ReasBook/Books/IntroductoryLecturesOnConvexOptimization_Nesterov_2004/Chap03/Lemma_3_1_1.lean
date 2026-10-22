/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.1 is a recall-only item in the finite Jensen / convex-combination domain.

Primary mathematical domain:
- Jensen's inequality for convex functions on finite weighted sums

Relevant owner-style declarations sampled before refinement:
- `ConvexOn.map_centerMass_le`
- `ConvexOn.map_sum_le`
- `ConvexOn.map_add_sum_le`
- `Convex.sum_mem`

Best owner abstraction:
- `ConvexOn.map_sum_le`

Primitive data:
- a convex-on-set witness `hf : ConvexOn ℝ s f`
- a finite family `x : Fin m → E` with `x i ∈ s`
- a coefficient family `α : Fin m → ℝ`

Derived API:
- Jensen's inequality at the weighted sum `∑ i, α i • x i`
- the positivity-to-nonnegativity specialization `0 < α i → 0 ≤ α i`, used only at call sites
- the separate domain-membership consequence from `Convex.sum_mem`

Source/core/bridge triage:
- source-facing: the textbook finite Jensen inequality with positive coefficients
- core/canonical: `ConvexOn.map_sum_le`
- bridge/view: the redundant positivity specialization from the source wording to the owner
  theorem's nonnegative-weight interface

The exact mathematical content here is already owned canonically by `ConvexOn.map_sum_le`, and the
earlier chapter file `Lemma_3_1.lean` already centers that owner theorem. This file therefore does
not keep a second local `example` proof with the stronger positivity hypotheses; those hypotheses
are bridge-only and should be discharged at the use site by passing `fun i ↦ (hαpos i).le` into
the owner theorem.
-/

recall ConvexOn.map_sum_le

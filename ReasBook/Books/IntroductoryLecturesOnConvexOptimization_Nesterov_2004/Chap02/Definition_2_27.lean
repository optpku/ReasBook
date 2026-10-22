/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.ReciprocalEpigraphOnPositiveRay

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 2.27 is a recall-only item in the Euclidean convex-geometry domain of the
nonnegative first-coordinate ray in `ℝ²`.

Primary domain:
- convex-geometric subsets of `ℝ²` presented by coordinate conditions.

Sampled owner-style declarations:
- `nonnegativeFirstCoordinateRay`, the chapter's canonical owner for `ℝ_+^{1,2}`;
- `mem_nonnegativeFirstCoordinateRay_iff`, the derived coordinate membership criterion;
- `Set.prod`, the canonical product-set owner used to form coordinate-axis subsets;
- `Ici`, the canonical half-line owner for the nonnegative first coordinate.

Best owner abstraction:
- `nonnegativeFirstCoordinateRay : Set (ℝ × ℝ)`

Primitive data:
- the first-coordinate half-line `Ici (0 : ℝ)`;
- the second-coordinate singleton `{(0 : ℝ)}`;
- their product-set realization `Ici (0 : ℝ) ×ˢ ({(0 : ℝ)} : Set ℝ)`.

Derived API:
- `mem_nonnegativeFirstCoordinateRay_iff`, which rewrites membership in the owner set as
  `0 ≤ x.1 ∧ x.2 = 0`.

Source/core/bridge triage:
- source-facing: the textbook ray `ℝ_+^{1,2}`;
- core/canonical: `nonnegativeFirstCoordinateRay`;
- bridge/view: `mem_nonnegativeFirstCoordinateRay_iff`.

This file therefore recalls the upstream owner declaration directly and introduces no parallel
local definition such as `nonnegativeFirstCoordinateAxis`.
-/

recall nonnegativeFirstCoordinateRay : Set (ℝ × ℝ)

recall mem_nonnegativeFirstCoordinateRay_iff (x : ℝ × ℝ) :
    x ∈ nonnegativeFirstCoordinateRay ↔ 0 ≤ x.1 ∧ x.2 = 0

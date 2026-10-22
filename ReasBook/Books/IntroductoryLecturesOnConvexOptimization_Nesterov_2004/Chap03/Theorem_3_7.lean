/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Theorem 3.7 is recall-only in the chapter's affine pullback calculus.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on Euclidean spaces and their affine pullbacks.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ClosedConvexOn.comp_continuousAffineMap` from `Theorem_3_1_2_2`
- `ClosedConvexOn.comp_affineMap` from `Theorem_3_1_2_2`
- mathlib `ConvexOn.comp_affineMap`

Best owner abstraction:
- `ClosedConvexOn`

Primitive data:
- the owner witness `hφ : ClosedConvexOn S φ`
- the affine map `g : Eₙ →ᵃ[ℝ] Eₘ`

Derived API:
- `ClosedConvexOn.comp_affineMap`

Source/core/bridge triage:
- source-facing: the affine-preimage closed-convexity statement
- core/canonical: `ClosedConvexOn.comp_affineMap`
- bridge/view: the earlier continuous-affine owner theorem
  `ClosedConvexOn.comp_continuousAffineMap`

The earlier owner file already proves the exact Euclidean affine-map statement. The `Nonempty` and
bounded hypotheses previously carried here are mathematically redundant for this theorem and do not
belong in the public API. This file therefore recalls the canonical owner theorem directly instead
of keeping a parallel wrapper name.
-/

recall ClosedConvexOn.comp_affineMap
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    {φ : EuclideanSpace ℝ (Fin m) → WithTop ℝ}
    (hφ : ClosedConvexOn S φ)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ClosedConvexOn (g ⁻¹' S) (φ ∘ g)

end

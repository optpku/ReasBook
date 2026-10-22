/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Topology
open scoped WithTopConvexAnalysis
open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace ConvexOn

/- Theorem 3.13 lies in the chapter's local regularity domain for convex `WithTop ℝ`-valued
functions on Euclidean space.

Sampled owner-style declarations in this domain:
- `ConvexOn.exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior` in
  `Theorem_3_1_3_1`, the chapter's source-facing `ℓ₁`-ball regularity theorem;
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain
  and finite real part;
- `EuclideanSpace.l1Seminorm` in `Definition_3_7`, the chapter owner for `ℓ₁` geometry;
- `Bornology.IsBounded`, the canonical bounded-image owner.

Best owner abstraction:
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- source-facing: boundedness of the finite-value image on a sufficiently small `ℓ₁` ball around an
  interior effective-domain point;
- bridge/view:
  `exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior`.

Primitive data:
- the convexity witness `hf : ConvexOn ℝ (dom f) (withTopRealPart f)`;
- the interior point `hx0 : x0 ∈ interior (dom f)`.

Derived API:
- an `ℓ₁` ball contained in `dom f`;
- a uniform absolute-value bound on `withTopRealPart f` over that ball;
- boundedness of the image of that ball under `withTopRealPart f`.

Source/core/bridge triage:
- source-facing: the bounded-image consequence recorded below;
- core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
- bridge/view:
  `exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior`.

This file therefore keeps no parallel effective-domain or finite-value wrapper. The only public
declaration below is the bounded-image companion theorem derived from the chapter's existing
source-facing `ℓ₁`-ball estimate. -/

/- Theorem 3.13 is already the chapter's canonical source-facing `ℓ₁` local regularity theorem,
recorded upstream as
`ConvexOn.exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior` in
`Nesterov.Chap03.Theorem_3_1_3_1`. This file reuses that owner theorem directly and keeps
only the bounded-image consequence as additional derived API. -/
recall exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ ε > 0, ∃ L > 0,
      (l1Seminorm n).ball x0 ε ⊆ dom f ∧
        ∀ ⦃y : E⦄, y ∈ (l1Seminorm n).ball x0 ε →
          |withTopRealPart f y - withTopRealPart f x0| ≤
            L * l1Seminorm n (y - x0)

/-- On a sufficiently small `ℓ₁`-ball around an interior effective-domain point of a convex
`WithTop ℝ`-valued function, the finite-value representative has bounded image. -/
-- Proof sketch: apply
-- `exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior` to obtain `ε` and `L`.
-- On that `ℓ₁`-ball, the estimate bounds every value by
-- `|withTopRealPart f x0| + L * ε`, so the image is bounded in `ℝ`.
theorem exists_l1_ball_subset_effectiveDomain_and_isBounded_image_of_mem_interior
    {f : E → WithTop ℝ}
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    {x0 : E} (hx0 : x0 ∈ interior (dom f)) :
    ∃ ε > 0,
      (l1Seminorm n).ball x0 ε ⊆ dom f ∧
        Bornology.IsBounded
          (withTopRealPart f '' (l1Seminorm n).ball x0 ε) := by
  obtain ⟨ε, hε, L, hL, hsubset, hbound⟩ :=
    exists_l1_ball_subset_effectiveDomain_and_abs_sub_le_of_mem_interior hf hx0
  refine ⟨ε, hε, hsubset, ?_⟩
  have hclosed : Bornology.IsBounded (Metric.closedBall (withTopRealPart f x0) (L * ε)) :=
    Metric.isBounded_closedBall
  refine hclosed.subset ?_
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact le_trans (hbound hy) (mul_le_mul_of_nonneg_left ((Seminorm.mem_ball _).1 hy).le hL.le)

end ConvexOn

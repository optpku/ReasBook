/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u

variable {E : Type u} [PseudoMetricSpace E]

/- Definition 7.3 lies in the nearest-point / distance-to-set domain.

Sampled owner declarations:
* `Metric.infDist`, the canonical distance-to-set owner;
* `Metric.isGLB_infDist`, the attained-infimum bridge for `infDist`;
* `Metric.infDist_le_dist_of_mem`, the pointwise comparison lemma used downstream to recover
  minimizing properties;
* `Metric.infDist_eq_iInf`, the canonical metric-space expansion showing that the owner lives at
  the intrinsic `dist` layer rather than at a norm-specific presentation.

Source/core/bridge triage:
* source-facing/core owner: `IsProjectionPointOn Q x p`;
* bridge/view: `isProjectionPointOn_iff_eq_sInf`.

Primitive data:
* the set `Q`, ambient point `x`, and candidate point `p`.

Derived API:
* feasibility `p ∈ Q`;
* the attained-infimum reformulation of the defining metric equality.

Accordingly, the owner is refined to the intrinsic metric layer
`dist x p = Metric.infDist x Q`; norm formulas belong in downstream bridge lemmas, not in the
core owner. -/

/-- Definition 7.3: a point `p ∈ Q` is a projection of `x` onto `Q` when its distance to `x`
realizes the distance from `x` to the set `Q`. -/
def IsProjectionPointOn (Q : Set E) (x p : E) : Prop :=
  p ∈ Q ∧ dist x p = infDist x Q

/-- A point is a projection of `x` onto `Q` exactly when it lies in `Q` and its distance to `x`
equals the infimum of the distance function on `Q`. -/
-- Proof sketch: if `p` is a projection point, then `p ∈ Q`, so `Q` is nonempty and
-- `Metric.isGLB_infDist` identifies `infDist x Q` with the infimum of `((dist x ·) '' Q)`;
-- conversely, the displayed equality is exactly the defining equality after rewriting that
-- infimum as `infDist x Q`.
theorem isProjectionPointOn_iff_eq_sInf {Q : Set E} {x p : E} :
    IsProjectionPointOn Q x p ↔
      p ∈ Q ∧ dist x p = sInf ((dist x ·) '' Q) := by
  constructor <;> rintro ⟨hpQ, hp⟩
  · have hinf : IsGLB ((dist x ·) '' Q) (infDist x Q) :=
      Metric.isGLB_infDist ⟨p, hpQ⟩
    exact ⟨hpQ, hp.trans (hinf.csInf_eq ⟨_, ⟨p, hpQ, rfl⟩⟩).symm⟩
  · have hinf : IsGLB ((dist x ·) '' Q) (infDist x Q) :=
      Metric.isGLB_infDist ⟨p, hpQ⟩
    exact ⟨hpQ, hp.trans (hinf.csInf_eq ⟨_, ⟨p, hpQ, rfl⟩⟩)⟩

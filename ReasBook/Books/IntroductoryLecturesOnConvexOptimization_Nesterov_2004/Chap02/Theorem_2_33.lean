/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace IsProjectionPointOn

/-- Projection points onto a convex set are unique. -/
theorem eq
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₀ p₁ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₀ p₁) (hp₂ : IsProjectionPointOn Q x₀ p₂) :
    p₁ = p₂ := by
  have hp₁' : ‖x₀ - p₁‖ = ⨅ w : Q, ‖x₀ - w‖ := hp₁.norm_eq_iInf
  have hp₂' : ‖x₀ - p₂‖ = ⨅ w : Q, ‖x₀ - w‖ := hp₂.norm_eq_iInf
  have h₁ : inner ℝ (x₀ - p₁) (p₂ - p₁) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hp₁.1).1 hp₁' p₂ hp₂.1
  have h₂ : inner ℝ (x₀ - p₂) (p₁ - p₂) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hp₂.1).1 hp₂' p₁ hp₁.1
  have h₁' : 0 ≤ inner ℝ (x₀ - p₁) (p₁ - p₂) := by
    have hpair : p₂ - p₁ = -(p₁ - p₂) := by
      abel
    rw [hpair, inner_neg_right] at h₁
    linarith
  have h₂' : inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ 0 := by
    have hrewrite :
        inner ℝ (x₀ - p₂) (p₁ - p₂) =
          inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      calc
        inner ℝ (x₀ - p₂) (p₁ - p₂)
            = inner ℝ ((x₀ - p₁) + (p₁ - p₂)) (p₁ - p₂) := by
                abel_nf
        _ = inner ℝ (x₀ - p₁) (p₁ - p₂) + inner ℝ (p₁ - p₂) (p₁ - p₂) := by
              rw [inner_add_left]
        _ = inner ℝ (x₀ - p₁) (p₁ - p₂) + ‖p₁ - p₂‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq]
    rw [hrewrite] at h₂
    exact h₂
  have hnorm : ‖p₁ - p₂‖ = 0 := by
    nlinarith [h₁', h₂', norm_nonneg (p₁ - p₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end IsProjectionPointOn

/-
Theorem 2.33 lies in the nearest-point / convex-geometry domain.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn Q x₀ p` and `isProjectionPointOn_iff_eq_sInf` from
  `Chap07/Definition_7_3`, the project owner predicate for nearest-point geometry;
* `exists_norm_eq_iInf_of_complete_convex` in
  `Mathlib/Analysis/InnerProductSpace/Projection/Minimal`, the mathlib existence theorem for
  nearest points in complete convex sets;
* `ExistsUnique.choose_eq_iff` in `Mathlib/Logic/ExistsUnique`, the canonical chooser API once
  existence and uniqueness are established;
* `Metric.infDist_zero_of_mem`, the metric owner lemma used for the `Set.univ` specialization.

Best owner abstraction:
* `IsProjectionPointOn Q x₀ p`.

Source/core/bridge triage:
* source-facing: existence and uniqueness of the Euclidean projection point on a nonempty closed
  convex set;
* core/canonical: `IsProjectionPointOn Q x₀ p`;
* bridge/view: the chosen point `euclideanProjection` and the bridge identifying any
  owner-level projection point with that chosen point.

Primitive data:
* the set `Q` and ambient point `x₀`;
* the nonempty / closed / convex hypotheses exactly when they are needed to produce the chosen
  projection point.

Derived API:
* the chosen projection point;
* its owner predicate;
* the equality bridge from an owner-level projection point to the chosen point;
* the specialization to `Set.univ`.

The textbook statement is for `ℝⁿ`, but the owner data and sampled mathlib API show that no
coordinate structure is used. The canonical public owner therefore lives in a complete real inner
product space, and the Euclidean-space version is a specialization.
-/

section ClosedConvexProjection

variable [CompleteSpace E]

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E)

/-- Theorem 2.33, stated at the owner level: every point of a complete real inner product space
has a unique projection point on a nonempty closed convex set `Q`. The Euclidean-space statement
is the specialization to `ℝⁿ`. -/
-- Proof sketch: `hQ_closed.isComplete` upgrades the closed set `Q` to a complete set. Apply
-- `exists_norm_eq_iInf_of_complete_convex` for existence, then use strict convexity of the norm
-- in a real inner product space to show that two minimizing points of `Q` must coincide.
theorem exists_unique_projection_point_of_nonempty_closed_convex
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E) :
    ∃! p : E, IsProjectionPointOn Q x₀ p := by
  obtain ⟨p, hpQ, hpinf⟩ :=
    exists_norm_eq_iInf_of_complete_convex hQ_nonempty hQ_closed.isComplete hQ_convex x₀
  have hp : IsProjectionPointOn Q x₀ p :=
    IsProjectionPointOn.of_norm_eq_iInf hpQ hpinf
  refine ExistsUnique.intro p hp ?_
  intro q hq
  exact hq.eq hQ_convex hp

/-- The Euclidean projection of `x₀` onto a nonempty closed convex set `Q`. -/
noncomputable def euclideanProjection
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E)
    : E :=
  (exists_unique_projection_point_of_nonempty_closed_convex
    Q hQ_nonempty hQ_closed hQ_convex x₀).choose

/-- The chosen Euclidean projection is a projection point in the owner predicate
`IsProjectionPointOn`. -/
theorem euclideanProjection_isProjectionPointOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (x₀ : E) :
    IsProjectionPointOn Q x₀ (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀) := by
  exact
    (exists_unique_projection_point_of_nonempty_closed_convex
      Q hQ_nonempty hQ_closed hQ_convex x₀).choose_spec.1

namespace IsProjectionPointOn

/-- Any Euclidean projection point onto a nonempty closed convex set agrees with the chosen
projection `euclideanProjection`. -/
theorem eq_euclideanProjection
    {Q : Set E} {x₀ p : E}
    (hp : IsProjectionPointOn Q x₀ p) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    p = euclideanProjection Q hQ_nonempty hQ_closed hQ_convex x₀ := by
  exact
    (exists_unique_projection_point_of_nonempty_closed_convex
      Q hQ_nonempty hQ_closed hQ_convex x₀).unique hp
      (euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x₀)

end IsProjectionPointOn

end ClosedConvexProjection

section

variable [CompleteSpace E]

/-- The Euclidean projection onto the whole space is the ambient point itself. -/
@[simp] theorem euclideanProjection_univ
    (x : E) :
    euclideanProjection (Set.univ : Set E)
      Set.univ_nonempty isClosed_univ convex_univ x = x := by
  have hxproj : IsProjectionPointOn (Set.univ : Set E) x x := by
    refine ⟨by simp, ?_⟩
    simp [infDist_zero_of_mem (by simp : x ∈ (Set.univ : Set E))]
  simpa using
    (hxproj.eq_euclideanProjection Set.univ_nonempty isClosed_univ convex_univ).symm

end

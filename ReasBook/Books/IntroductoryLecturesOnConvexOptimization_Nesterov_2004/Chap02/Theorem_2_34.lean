/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_33

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 2.34 lies in the nearest-point / convex-geometry domain.

Sampled owner-style declarations:
* `IsProjectionPointOn Q x p` in `Chap07/Definition_7_3`, the project owner predicate for
  nearest-point geometry;
* `IsProjectionPointOn.inner_sub_nonneg` in `Lemma_2_13`, the owner variational inequality for a
  projection point on a convex set;
* `euclideanProjection` and `euclideanProjection_isProjectionPointOn` in `Theorem_2_33`, the
  chosen map and its bridge back to the owner predicate once existence is available;
* `Submodule.lipschitzWith_orthogonalProjection` in mathlib's linear-subspace projection API,
  showing that the canonical map-level output for a projection operator is `LipschitzWith 1`.

Best owner abstraction:
* `IsProjectionPointOn Q x p`.

Source/core/bridge triage:
* source-facing: nonexpansiveness of metric projection onto a convex set;
* core/canonical: owner-level projection points `IsProjectionPointOn Q x p`;
* bridge/view: the selector-level `LipschitzWith 1` theorem and its specialization to the chosen
  map `euclideanProjection`.

Primitive data:
* the convex set `Q`, ambient points `x₁`, `x₂`, and projection points `p₁`, `p₂`.

Derived API:
* the intrinsic metric comparison `dist p₁ p₂ ≤ dist x₁ x₂` for owner-level projection points;
* the `LipschitzWith 1` theorem for any projection selector on `Q`;
* the chosen-map corollary for `euclideanProjection` once completeness supplies that selector.

The proof uses only real inner-product geometry. Completeness is therefore kept out of the
owner-level and selector-level statements, and is introduced only for the final bridge to the
chosen projection map from `Theorem_2_33`.
-/

namespace IsProjectionPointOn

/-- Any two projection points onto a convex set are at most as far apart as their base points. -/
-- Proof sketch: apply the projection variational inequality to `hp₁` with the feasible point `p₂`
-- and to `hp₂` with the feasible point `p₁`. Adding the two inequalities gives
-- `‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, x₁ - x₂⟫`, and Cauchy--Schwarz yields the desired bound.
theorem dist_le_dist
    {Q : Set E} (hQ_convex : Convex ℝ Q) {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁) (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Any projection selector on a convex set is nonexpansive, recorded in the canonical map-level
form `LipschitzWith 1`. -/
theorem lipschitzWith
    {Q : Set E} (hQ_convex : Convex ℝ Q) {projQ : E → E}
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x)) :
    LipschitzWith 1 projQ := by
  refine LipschitzWith.mk_one ?_
  intro x₁ x₂
  exact (hproj x₁).dist_le_dist hQ_convex (hproj x₂)

end IsProjectionPointOn

section

variable [CompleteSpace E]

/-- Theorem 2.34: the Euclidean projection onto a nonempty closed convex set in a complete real
inner product space is nonexpansive, recorded in the canonical map-level form `LipschitzWith 1`.
The textbook Euclidean-space statement is the specialization to `ℝⁿ`. -/
theorem euclideanProjection_nonexpansive
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) :
    LipschitzWith 1 (euclideanProjection Q hQ_nonempty hQ_closed hQ_convex) :=
  IsProjectionPointOn.lipschitzWith hQ_convex
    (fun x ↦ euclideanProjection_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex x)

end

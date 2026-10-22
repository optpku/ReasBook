/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 2.33 lies in the nearest-point / constrained-argmin domain.

Sampled owner-style declarations:
* `argmin[Q] f` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  constrained minimizer-set owner;
* `IsProjectionPointOn` and `isProjectionPointOn_iff_eq_sInf` in `Chap07/Definition_7_3`, the
  project owner for pointwise projection data;
* `IsMinOn` and `isMinOn_iff` in mathlib, the canonical minimizing-property owner.

Source/core/bridge triage:
* source-facing: the projection set `π_Q(x₀)` and its elements;
* core/canonical: `argmin[Q] (fun x ↦ ‖x - x₀‖)`;
* bridge/view: the pointwise owner predicate `IsProjectionPointOn Q x₀ p` and its minimizing
  reformulation below.

The textbook definition is therefore recorded through the canonical constrained argmin set, with
pointwise projection language recovered by companion bridge lemmas rather than by a parallel local
wrapper. -/

section

variable (Q : Set E) (x₀ : E)

set_option linter.hashCommand false in
/- Definition 2.33: for a nonempty closed set `Q`, the textbook projection set `π_Q(x₀)` is
formalized by the canonical constrained argmin set of the distance function
`x ↦ ‖x - x₀‖` on `Q`. -/
#check (argmin[Q] (fun x : E ↦ ‖x - x₀‖) : Set E)

end

namespace IsProjectionPointOn

/-- A projection point of `x₀` onto `Q` realizes the norm infimum of the distance-to-`x₀`
function on `Q`. -/
theorem norm_eq_iInf {Q : Set E} {x₀ p : E} (hp : IsProjectionPointOn Q x₀ p) :
    ‖x₀ - p‖ = ⨅ w : Q, ‖x₀ - w‖ := by
  simpa [Metric.infDist_eq_iInf, dist_eq_norm] using hp.2

/-- Any feasible point whose norm distance to `x₀` realizes the infimum over `Q` is a projection
point of `x₀` onto `Q`. -/
theorem of_norm_eq_iInf {Q : Set E} {x₀ p : E} (hpQ : p ∈ Q)
    (hpinf : ‖x₀ - p‖ = ⨅ w : Q, ‖x₀ - w‖) :
    IsProjectionPointOn Q x₀ p := by
  exact ⟨hpQ, by simpa [Metric.infDist_eq_iInf, dist_eq_norm] using hpinf⟩

/-- A projection point of `x₀` onto `Q` minimizes the distance-to-`x₀` function on `Q`. -/
-- Proof sketch: unpack `IsProjectionPointOn Q x₀ p` into feasibility and the equality
-- `dist x₀ p = Metric.infDist x₀ Q`; then compare `Metric.infDist x₀ Q` with `dist x₀ y` for each
-- feasible `y ∈ Q`, and rewrite the distances as norms.
theorem isMinOn {Q : Set E} {x₀ p : E} (hp : IsProjectionPointOn Q x₀ p) :
    IsMinOn (fun y ↦ ‖y - x₀‖) Q p := by
  rw [isMinOn_iff]
  intro y hy
  have hdist : dist x₀ p ≤ dist x₀ y := by
    calc
      dist x₀ p = Metric.infDist x₀ Q := hp.2
      _ ≤ dist x₀ y := Metric.infDist_le_dist_of_mem hy
  simpa [dist_eq_norm, norm_sub_rev] using hdist

/-- A point is a projection point of `x₀` onto `Q` exactly when it belongs to `Q` and minimizes
the distance-to-`x₀` function on `Q`. -/
-- Proof sketch: one direction is `isMinOn`. For the converse, combine feasibility with the
-- minimizing inequality, use `Metric.le_infDist` and `Metric.infDist_le_dist_of_mem`, and rewrite
-- the resulting distance equality back into the owner predicate `IsProjectionPointOn`.
theorem iff_isMinOn {Q : Set E} {x₀ p : E} :
    IsProjectionPointOn Q x₀ p ↔
      p ∈ Q ∧ IsMinOn (fun y ↦ ‖y - x₀‖) Q p := by
  constructor
  · intro hp
    exact ⟨hp.1, hp.isMinOn⟩
  · rintro ⟨hpQ, hpmin⟩
    refine ⟨hpQ, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hpQ)⟩
    rw [Metric.le_infDist ⟨p, hpQ⟩]
    intro y hy
    simpa [dist_eq_norm, norm_sub_rev] using (isMinOn_iff.mp hpmin y hy)

/-- Membership in the canonical projection set of `x₀` onto `Q` is equivalent to being a
projection point in the owner predicate `IsProjectionPointOn`. -/
-- Proof sketch: unfold membership in `argmin[Q] (fun y ↦ ‖y - x₀‖)` using
-- `mem_constrainedArgmin_iff`, then apply `iff_isMinOn`.
theorem mem_argmin_iff {Q : Set E} {x₀ p : E} :
    p ∈ argmin[Q] (fun y : E ↦ ‖y - x₀‖) ↔ IsProjectionPointOn Q x₀ p := by
  rw [mem_constrainedArgmin_iff]
  exact iff_isMinOn.symm

end IsProjectionPointOn

end

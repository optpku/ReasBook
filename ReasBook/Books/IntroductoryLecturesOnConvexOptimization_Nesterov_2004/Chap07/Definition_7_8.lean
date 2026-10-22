/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_33

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.8 lies in the nearest-point / norm-minimization domain.

Sampled owner declarations:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the project owner of projection-point data;
* `IsProjectionPointOn.iff_isMinOn` in `Chap02/Definition_2_33`, the canonical bridge from that
  owner to minimizing the distance-to-basepoint function on a set;
* mathlib `IsMinOn` and `isMinOn_iff`, the canonical minimizer API on a set.

Source/core/bridge triage:
* source-facing: the textbook notion “projection of the origin onto `Q1`”;
* core/canonical: `IsProjectionPointOn Q1 (0 : E) x0`;
* bridge/view: norm-minimizer and pointwise norm-comparison reformulations.

Accordingly, the main labeled entry directly reuses the existing projection-point owner specialized
to the base point `0`, and the norm formulas are recorded as companion bridge theorems. -/

universe u

section

variable {E : Type u} [NormedAddCommGroup E]
variable (Q1 : Set E) (x0 : E)

set_option linter.hashCommand false in
/- Definition 7.8: the projection of the origin onto `Q1` with respect to the norm is the
existing projection-point predicate specialized to the base point `0`. -/
#check (IsProjectionPointOn Q1 (0 : E) x0 : Prop)

end

section

variable {E : Type u} [NormedAddCommGroup E]

/-- A projection point of the origin onto `Q1` is exactly a feasible minimizer of the norm on
`Q1`. -/
-- Proof sketch: specialize `IsProjectionPointOn.iff_isMinOn` to the base point `0` and simplify
-- `‖x - 0‖` to `‖x‖`.
theorem isProjectionPointOn_origin_iff_isMinOn_norm {Q1 : Set E} {x0 : E} :
    IsProjectionPointOn Q1 (0 : E) x0 ↔
      x0 ∈ Q1 ∧ IsMinOn (fun x ↦ ‖x‖) Q1 x0 := by
  -- Specialize the projection/minimizer owner equivalence at the origin.
  simpa using
    (IsProjectionPointOn.iff_isMinOn (Q := Q1) (x₀ := (0 : E)) (p := x0))

/-- A point is a projection of the origin onto `Q1` exactly when it lies in `Q1` and its norm is
no larger than the norm of every point of `Q1`. -/
-- Proof sketch: rewrite the `IsMinOn` statement in
-- `isProjectionPointOn_origin_iff_isMinOn_norm` using `isMinOn_iff`.
theorem isProjectionPointOn_origin_iff_forall_norm_le {Q1 : Set E} {x0 : E} :
    IsProjectionPointOn Q1 (0 : E) x0 ↔
      x0 ∈ Q1 ∧ ∀ x ∈ Q1, ‖x0‖ ≤ ‖x‖ := by
  -- Convert the norm minimizer formulation into the explicit pointwise comparison.
  rw [isProjectionPointOn_origin_iff_isMinOn_norm, isMinOn_iff]

end

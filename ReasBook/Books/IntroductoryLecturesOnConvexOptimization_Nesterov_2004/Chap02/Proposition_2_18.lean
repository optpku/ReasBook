/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_26

-- Declarations for this item will be appended below by the statement pipeline.

open Set

local notation "Q" => reciprocalEpigraphOnPositiveRay

/-!
Proposition 2.18 is source-facing in the convex-geometry domain of coordinate projections of the
owner epigraph `reciprocalEpigraphOnPositiveRay` in `ℝ²`.

Sampled owner-style declarations:
* `reciprocalEpigraphOnPositiveRay`
* `mem_reciprocalEpigraphOnPositiveRay_iff`
* `Prod.snd`
* `Set.mem_image`

Best owner abstraction:
* `reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)`

Primitive data:
* the owner set `Q = reciprocalEpigraphOnPositiveRay`

Derived API:
* the second-coordinate image `Prod.snd '' Q`
* its source-facing identification with the positive ray `Ioi (0 : ℝ)`

Source/core/bridge triage:
* source-facing: the textbook statement that the attainable second coordinates in `Q` are exactly
  the positive reals
* core/canonical: the owner set `Q = reciprocalEpigraphOnPositiveRay`
* bridge/view: `mem_reciprocalEpigraphOnPositiveRay_iff` and `Set.mem_image`

No parallel local “hyperbola region” set is introduced here; the proposition is phrased directly
as a statement about the owner set. -/

/-- Proposition 2.18: the second-coordinate projection of
`reciprocalEpigraphOnPositiveRay` is exactly the positive real half-line. The textbook region
`{(τ, x) | 0 < τ ∧ x ≥ 1 / τ}` is already represented by this owner set. -/
-- Proof sketch: if `(τ, x)` belongs to the epigraph, then `x ≥ 1 / τ > 0`. Conversely, for
-- `x > 0` the point `(1 / x, x)` lies in the epigraph and projects to `x`.
theorem snd_image_reciprocalEpigraphOnPositiveRay_eq_Ioi :
    Prod.snd '' Q = Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    -- Extract the positive first coordinate and the lower bound on the second coordinate.
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff p).1 hp with ⟨hp₁, hp₂⟩
    exact lt_of_lt_of_le (one_div_pos.mpr hp₁) hp₂
  · intro hx
    have hmem : (1 / x, x) ∈ Q := by
      -- Choose `τ = 1 / x`, so the defining inequality becomes an equality.
      refine (mem_reciprocalEpigraphOnPositiveRay_iff (1 / x, x)).2 ?_
      constructor
      · exact one_div_pos.mpr hx
      · simp
    exact ⟨(1 / x, x), hmem, rfl⟩

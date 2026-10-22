/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

/-!
Primary domain: convex-geometric subsets of `ℝ²` expressed as owner sets in `Set (ℝ × ℝ)`,
with Proposition 2.15 stated directly as pointwise set identities.

Relevant owner-style declarations sampled before refining this file:
* `reciprocalEpigraphOnPositiveRay`, the imported chapter owner set `Q`
* `nonnegativeFirstCoordinateRay`, the imported chapter owner set `ℝ_+^{1,2}`
* `Set.mem_add`, the canonical bridge for pointwise Minkowski addition of sets
* `Set.mem_sub`, the canonical bridge for pointwise set subtraction

Owner abstraction:
* the owner sets already live in `ReciprocalEpigraphOnPositiveRay.lean`, so this file now keeps
  only the source-facing set identities at the same `Set (ℝ × ℝ)` level.

Primitive data:
* none locally; both owner sets are imported

Derived API:
* the two source-facing set equalities of Proposition 2.15

Source/core/bridge triage:
* source-facing: the two set identities asserted in Proposition 2.15
* core/canonical: the imported owner sets as subsets of `ℝ × ℝ`, together with pointwise `Set`
  addition and subtraction
* bridge/view: the imported membership theorems
-/

/-- Proposition 2.15 (1): subtracting the nonnegative first-coordinate ray from `Q` gives exactly
the open upper half-plane `{x ∈ ℝ² | x₂ > 0}`. -/
-- Proof sketch: if `y = x - r` with `x ∈ Q` and `r` on the horizontal ray, then the second
-- coordinate is unchanged and remains positive because `x.1 > 0` and `x.2 ≥ 1 / x.1`. For the
-- reverse inclusion, given `y.2 > 0`, choose `x.1` large enough so that `1 / x.1 ≤ y.2` and
-- `y.1 ≤ x.1`, then set `x := (x.1, y.2)` and `r := x - y`.
theorem reciprocalEpigraphOnPositiveRay_sub_nonnegativeFirstCoordinateRay :
    reciprocalEpigraphOnPositiveRay - nonnegativeFirstCoordinateRay = {x : ℝ × ℝ | 0 < x.2} := by
  ext y
  constructor
  · rintro ⟨x, hx, r, hr, rfl⟩
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
    rcases (mem_nonnegativeFirstCoordinateRay_iff r).1 hr with ⟨_, hr2⟩
    simpa [hr2] using lt_of_lt_of_le (one_div_pos.mpr hx1) hx2
  · intro hy
    let t : ℝ := max y.1 (1 / y.2)
    have ht_left : y.1 ≤ t := le_max_left _ _
    have ht_right : 1 / y.2 ≤ t := le_max_right _ _
    have ht_pos : 0 < t := lt_of_lt_of_le (one_div_pos.mpr hy) ht_right
    refine Set.mem_sub.2 ?_
    refine ⟨(t, y.2), ?_, (t - y.1, 0), ?_, by ext <;> simp [t]⟩
    · exact (mem_reciprocalEpigraphOnPositiveRay_iff (t, y.2)).2
        ⟨by simpa [t] using ht_pos, (one_div_le ht_pos hy).2 ht_right⟩
    · exact (mem_nonnegativeFirstCoordinateRay_iff (t - y.1, 0)).2
        ⟨by linarith, by simp⟩

/-- Proposition 2.15 (2): adding the nonnegative first-coordinate ray to `Q` leaves `Q`
unchanged. -/
-- Proof sketch: adding `(r, 0)` only increases the first coordinate, so the reciprocal bound
-- `1 / x₁` decreases while the second coordinate stays fixed; the opposite inclusion follows from
-- the zero vector lying on the ray.
theorem reciprocalEpigraphOnPositiveRay_add_nonnegativeFirstCoordinateRay :
    reciprocalEpigraphOnPositiveRay + nonnegativeFirstCoordinateRay =
      reciprocalEpigraphOnPositiveRay := by
  ext y
  constructor
  · rintro ⟨x, hx, r, hr, rfl⟩
    rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
    rcases (mem_nonnegativeFirstCoordinateRay_iff r).1 hr with ⟨hr1, hr2⟩
    refine (mem_reciprocalEpigraphOnPositiveRay_iff (x + r)).2 ?_
    constructor
    · simpa [Prod.fst_add, hr2] using add_pos_of_pos_of_nonneg hx1 hr1
    · have hmono : 1 / (x.1 + r.1) ≤ 1 / x.1 := by
        apply one_div_le_one_div_of_le hx1
        linarith
      simpa [Prod.snd_add, hr2] using le_trans hmono hx2
  · intro hy
    refine Set.mem_add.2 ?_
    refine ⟨y, hy, (0, 0), ?_, by simp⟩
    simpa using (mem_nonnegativeFirstCoordinateRay_iff (0, 0)).2 (by simp)

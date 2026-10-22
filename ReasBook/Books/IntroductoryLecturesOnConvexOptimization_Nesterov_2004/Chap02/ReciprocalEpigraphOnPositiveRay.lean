/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

open Set

/-!
Primary domain: convex-geometric owner subsets of `ℝ²`.

Relevant owner-style declarations sampled for this core file:
* `Set.prod`, the canonical owner for coordinate-axis subsets such as `Ici 0 ×ˢ {0}`
* `ConvexOn.convex_epigraph`, the mathlib owner theorem for epigraph-style subsets
* `convexOn_iff_convex_epigraph`, the canonical bridge between convexity and epigraph convexity

Best owner abstraction:
* `reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)`
* `nonnegativeFirstCoordinateRay : Set (ℝ × ℝ)`

Primitive data:
* the reciprocal epigraph region `Q`
* the nonnegative first-coordinate ray `ℝ_+^{1,2}`

Derived API:
* the companion membership lemmas

Source/core/bridge triage:
* core/canonical: the two owner sets in `Set (ℝ × ℝ)`
* bridge/view: the corresponding coordinate membership lemmas
-/

/-- The set `Q`, viewed as the epigraph of `x ↦ 1 / x` on the positive first-coordinate ray. The
textbook coordinates `x^(1), x^(2)` are represented by `x.1, x.2`. -/
def reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Ioi (0 : ℝ) ∧ 1 / x.1 ≤ x.2}

/-- Membership in `reciprocalEpigraphOnPositiveRay` means that the first coordinate is positive and
the second coordinate lies on or above the reciprocal graph `x₂ = 1 / x₁`. -/
theorem mem_reciprocalEpigraphOnPositiveRay_iff (x : ℝ × ℝ) :
    x ∈ reciprocalEpigraphOnPositiveRay ↔ 0 < x.1 ∧ x.2 ≥ 1 / x.1 := by
  simp [reciprocalEpigraphOnPositiveRay]

/-- The set `ℝ_+^{1,2}`, namely the nonnegative part of the first coordinate axis in `ℝ²`, in the
owner product form `Ici 0 ×ˢ {0}`. -/
def nonnegativeFirstCoordinateRay : Set (ℝ × ℝ) :=
  Ici (0 : ℝ) ×ˢ ({(0 : ℝ)} : Set ℝ)

/-- Membership in `nonnegativeFirstCoordinateRay` means that the first coordinate is nonnegative
and the second coordinate vanishes. -/
theorem mem_nonnegativeFirstCoordinateRay_iff (x : ℝ × ℝ) :
    x ∈ nonnegativeFirstCoordinateRay ↔ 0 ≤ x.1 ∧ x.2 = 0 := by
  simp [nonnegativeFirstCoordinateRay]

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic

section Example133

open AffineMap

variable {𝕜 : Type*} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

-- Semantic recall hits verified for this item: `AffineMap.lineMap`,
-- `AffineMap.lineMap_apply_module'`, and `Convex.affine_image`.

/-- The ray starting at `x₀` in the direction `d` is the affine image of `Set.Ici 0`
under the line map `t ↦ x₀ + t • d`. -/
def ray (𝕜 : Type*) [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (x₀ d : V) : Set V :=
  lineMap x₀ (x₀ + d) '' Set.Ici (0 : 𝕜)

/-- Membership in `ray 𝕜 x₀ d` is given by a nonnegative scalar parameterization. -/
@[simp]
theorem mem_ray_iff {x₀ d x : V} :
    x ∈ ray 𝕜 x₀ d ↔ ∃ t : 𝕜, 0 ≤ t ∧ x = x₀ + t • d := by
  rw [ray]
  constructor <;> rintro ⟨t, ht, rfl⟩ <;> refine ⟨t, by simpa using ht, ?_⟩
  · simp [lineMap_apply_module', add_comm]
  · simp [lineMap_apply_module', add_comm]

/-- Chapter01 Example 1.3.3: the ray
`ray 𝕜 x₀ d = {x | ∃ t : 𝕜, 0 ≤ t ∧ x = x₀ + t • d}` is a convex set.
The source states this for `d ≠ 0`, but the convexity argument does not use that hypothesis. -/
theorem ray_convex (x₀ d : V) : Convex 𝕜 (ray 𝕜 x₀ d) := by
  simpa [ray] using (convex_Ici (0 : 𝕜)).affine_image (lineMap x₀ (x₀ + d))

end Example133

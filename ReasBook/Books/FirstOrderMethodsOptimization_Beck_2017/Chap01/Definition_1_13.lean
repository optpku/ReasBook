/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open WithLp
open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (a : E) (b : ℝ)

/-- Definition 1.13: the half-space with normal vector `a` and offset `b`. -/
noncomputable def halfSpace : Set E :=
  (innerSL ℝ a) ⁻¹' Set.Iic b

/- Definition 1.13: the textbook half-space with normal vector `a` and offset `b` is the
sublevel set of the canonical continuous linear functional `innerSL ℝ a`. -/
#check (halfSpace a b : Set E)

-- Proof sketch: unfold membership in `halfSpace a b`.
/-- A point lies in `halfSpace a b` exactly when its inner product with `a` is at most `b`. -/
theorem mem_halfSpace_iff {a x : E} {b : ℝ} :
    x ∈ halfSpace a b ↔ ⟪a, x⟫ ≤ b := by
  simp [halfSpace]

section

variable {ι : Type*} [Fintype ι]

/-- The Chapter 1 half-space owner transported to the coordinate model `ι → ℝ` through the
canonical `L²` equivalence `toLp 2`. -/
noncomputable def coordinateHalfSpace (a : ι → ℝ) (b : ℝ) : Set (ι → ℝ) :=
  (toLp 2) ⁻¹' halfSpace (toLp 2 a) b

-- Proof sketch: membership in the pulled-back half-space means
-- `⟪toLp 2 a, toLp 2 x⟫ ≤ b`; the standard `toLp` inner-product bridge rewrites this as the
-- coordinate inequality `dotProduct a x ≤ b`.
/-- A coordinate vector `x` lies in `coordinateHalfSpace a b` exactly when
`dotProduct a x ≤ b`. -/
@[simp] theorem mem_coordinateHalfSpace_iff (a x : ι → ℝ) (b : ℝ) :
    x ∈ coordinateHalfSpace a b ↔ dotProduct a x ≤ b := by
  change inner ℝ (toLp 2 a) (toLp 2 x) ≤ b ↔ dotProduct a x ≤ b
  rw [show inner ℝ (toLp 2 a) (toLp 2 x) = dotProduct a x by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp a x)]

end

end

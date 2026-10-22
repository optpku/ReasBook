/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 1.12: the closed line segment between two points in a real vector space is the
canonical mathlib set `segment ℝ x y`; the companion declarations below record the textbook
one-parameter formulas for the closed and open line segments. -/
#check (segment ℝ)

-- Proof sketch: use `segment_eq_image`; then unpack membership in the image of `Icc (0 : ℝ) 1`
-- and rewrite the affine combination to match the textbook coefficient convention.
/-- Companion characterization of membership in the closed line segment `segment ℝ x y` by the
textbook one-parameter formula. -/
theorem mem_segment_iff_exists_real {x y z : E} :
    z ∈ segment ℝ x y ↔
      ∃ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 ∧ α • x + (1 - α) • y = z := by
  rw [segment_symm ℝ x y, segment_eq_image ℝ y x, Set.mem_image]
  constructor
  · rintro ⟨α, hα, hz⟩
    exact ⟨α, hα, by simpa [add_comm] using hz⟩
  · rintro ⟨α, hα, hz⟩
    exact ⟨α, hα, by simpa [add_comm] using hz⟩

/-- The textbook open line segment in a real vector space: it is obtained from the canonical
mathlib `openSegment ℝ x y` by removing the left endpoint, which changes only the diagonal case
`x = y`. -/
def openLineSegment (x y : E) : Set E :=
  openSegment ℝ x y \ {x}

-- Proof sketch: unfold `openLineSegment`; when `x ≠ y`, mathlib already knows that `x` is not in
-- `openSegment ℝ x y`, so removing `{x}` does nothing.
/-- When the endpoints are distinct, the textbook open line segment agrees with mathlib's
`openSegment`. -/
theorem openLineSegment_eq_openSegment {x y : E} (hxy : x ≠ y) :
    openLineSegment x y = openSegment ℝ x y := by
  rw [openLineSegment, Set.diff_singleton_eq_self]
  simpa [left_mem_openSegment_iff] using hxy

-- Proof sketch: combine `openLineSegment_eq_openSegment` with `openSegment_eq_image`; then
-- unpack membership in the image of `Ioo (0 : ℝ) 1` and rewrite the affine combination to match
-- the textbook coefficient convention.
/-- When the endpoints are distinct, membership in the textbook open line segment is given by the
one-parameter formula with parameter in `(0,1)`. -/
theorem mem_openLineSegment_iff {x y z : E} (hxy : x ≠ y) :
    z ∈ openLineSegment x y ↔
      ∃ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 ∧ α • x + (1 - α) • y = z := by
  rw [openLineSegment_eq_openSegment hxy, openSegment_symm ℝ x y, openSegment_eq_image ℝ y x,
    Set.mem_image]
  constructor
  · rintro ⟨α, hα, hz⟩
    exact ⟨α, hα, by simpa [add_comm] using hz⟩
  · rintro ⟨α, hα, hz⟩
    exact ⟨α, hα, by simpa [add_comm] using hz⟩

-- Proof sketch: `openSegment ℝ x x = {x}` in mathlib, so removing the endpoint leaves `∅`.
/-- The textbook open line segment from a point to itself is empty. -/
theorem openLineSegment_self (x : E) :
    openLineSegment x x = (∅ : Set E) := by
  simp [openLineSegment]

end

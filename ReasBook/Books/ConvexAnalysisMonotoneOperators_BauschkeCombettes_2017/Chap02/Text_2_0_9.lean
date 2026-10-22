/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductLevelSet (u : H) (η : ℝ) : Set H :=
  hyperplane (innerSLFlip ℝ u).toLinearMap η

/-- The closed sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductClosedSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iic η

/-- The open strict sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductOpenSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iio η

/-- The inner-product level set is the hyperplane cut out by the real linear functional
`x ↦ ⟪x, u⟫_ℝ`. -/
theorem innerProductLevelSet_eq_hyperplane (u : H) (η : ℝ) :
    innerProductLevelSet u η = hyperplane (innerSLFlip ℝ u).toLinearMap η :=
  rfl

-- Proof sketch: unfold `innerProductLevelSet`; membership is definitionally the equality
-- `inner ℝ x u = η`.
/-- Membership in the inner-product level set is the defining inner-product equation. -/
theorem mem_innerProductLevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductLevelSet u η ↔ ⟪x, u⟫_ℝ = η := by
  rw [innerProductLevelSet, mem_hyperplane_iff]
  change (innerSLFlip ℝ u) x = η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductClosedSublevelSet`; membership is definitionally the
-- inequality `inner ℝ x u ≤ η`.
/-- Membership in the closed inner-product sublevel set is the defining inequality. -/
theorem mem_innerProductClosedSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductClosedSublevelSet u η ↔ ⟪x, u⟫_ℝ ≤ η := by
  rw [innerProductClosedSublevelSet]
  change (innerSLFlip ℝ u) x ≤ η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductOpenSublevelSet`; membership is definitionally the strict
-- inequality `inner ℝ x u < η`.
/-- Membership in the open inner-product strict sublevel set is the defining inequality. -/
theorem mem_innerProductOpenSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductOpenSublevelSet u η ↔ ⟪x, u⟫_ℝ < η := by
  rw [innerProductOpenSublevelSet]
  change (innerSLFlip ℝ u) x < η ↔ _
  rw [innerSLFlip_apply_apply]

/-- Text 2.0.9: if `u ≠ 0`, the closed hyperplane with normal `u` and offset `η` is the level set
of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHyperplane_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductLevelSet u η = {x | ⟪x, u⟫_ℝ = η} := by
  ext x
  simp [mem_innerProductLevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the closed half-space with outer normal `u` and offset `η` is the
sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductClosedSublevelSet u η = {x | ⟪x, u⟫_ℝ ≤ η} := by
  ext x
  simp [mem_innerProductClosedSublevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the open half-space with outer normal `u` and offset `η` is the
strict sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem openHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductOpenSublevelSet u η = {x | ⟪x, u⟫_ℝ < η} := by
  ext x
  simp [mem_innerProductOpenSublevelSet_iff]

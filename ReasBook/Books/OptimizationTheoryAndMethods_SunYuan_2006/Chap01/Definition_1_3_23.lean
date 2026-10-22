/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item: mathlib already provides generic sunYuanHyperplane and
-- half-space API such as `convex_hyperplane`, `convex_halfSpace_le`, and `convex_halfSpace_ge`.
-- The source states these notions in `ℝ^n`, but the source-facing owner declarations below only
-- use real inner-product-space structure. The anchored equation is a bridge view of the shared
-- chapter owners `sunYuanHyperplane` and its associated half-spaces.

section Chapter01Definition1323

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sunYuanHyperplane `{x | ⟪p, x⟫ = α}` determined by the normal `p` and level `α`. -/
def sunYuanHyperplane (p : E) (α : ℝ) : Set E :=
  { x | ⟪p, x⟫ = α }

/-- The closed upper half-space `{x | α ≤ ⟪p, x⟫}`. -/
def closedUpperHalfSpace (p : E) (α : ℝ) : Set E :=
  { x | α ≤ ⟪p, x⟫ }

/-- The closed lower half-space `{x | ⟪p, x⟫ ≤ α}`. -/
def closedLowerHalfSpace (p : E) (α : ℝ) : Set E :=
  { x | ⟪p, x⟫ ≤ α }

/-- The open upper half-space `{x | α < ⟪p, x⟫}`. -/
def openUpperHalfSpace (p : E) (α : ℝ) : Set E :=
  { x | α < ⟪p, x⟫ }

/-- The open lower half-space `{x | ⟪p, x⟫ < α}`. -/
def openLowerHalfSpace (p : E) (α : ℝ) : Set E :=
  { x | ⟪p, x⟫ < α }

/-- Membership in `sunYuanHyperplane p α` is the defining equality `⟪p, x⟫ = α`. -/
@[simp] theorem mem_sunYuanHyperplane_iff {p x : E} {α : ℝ} :
    x ∈ sunYuanHyperplane p α ↔ ⟪p, x⟫ = α :=
  Iff.rfl

/-- Membership in `closedUpperHalfSpace p α` is the defining inequality `α ≤ ⟪p, x⟫`. -/
@[simp] theorem mem_closedUpperHalfSpace_iff {p x : E} {α : ℝ} :
    x ∈ closedUpperHalfSpace p α ↔ α ≤ ⟪p, x⟫ :=
  Iff.rfl

/-- Membership in `closedLowerHalfSpace p α` is the defining inequality `⟪p, x⟫ ≤ α`. -/
@[simp] theorem mem_closedLowerHalfSpace_iff {p x : E} {α : ℝ} :
    x ∈ closedLowerHalfSpace p α ↔ ⟪p, x⟫ ≤ α :=
  Iff.rfl

/-- Membership in `openUpperHalfSpace p α` is the defining inequality `α < ⟪p, x⟫`. -/
@[simp] theorem mem_openUpperHalfSpace_iff {p x : E} {α : ℝ} :
    x ∈ openUpperHalfSpace p α ↔ α < ⟪p, x⟫ :=
  Iff.rfl

/-- Membership in `openLowerHalfSpace p α` is the defining inequality `⟪p, x⟫ < α`. -/
@[simp] theorem mem_openLowerHalfSpace_iff {p x : E} {α : ℝ} :
    x ∈ openLowerHalfSpace p α ↔ ⟪p, x⟫ < α :=
  Iff.rfl

/-- Membership in the sunYuanHyperplane through `xbar` with normal vector `p` is the anchored
orthogonality equation from the source. -/
theorem mem_sunYuanHyperplane_inner_iff_sub_eq_zero {p xbar x : E} :
    x ∈ sunYuanHyperplane p ⟪p, xbar⟫ ↔ ⟪p, x - xbar⟫ = (0 : ℝ) := by
  simp [mem_sunYuanHyperplane_iff, inner_sub_right, sub_eq_zero]

/-- The sunYuanHyperplane through `xbar` with normal `p` is exactly the anchored source equation
`⟪p, x - xbar⟫ = 0`. -/
theorem sunYuanHyperplane_eq_setOf_sub_eq_zero (p xbar : E) :
    sunYuanHyperplane p ⟪p, xbar⟫ = { x | ⟪p, x - xbar⟫ = (0 : ℝ) } := by
  ext x
  exact mem_sunYuanHyperplane_inner_iff_sub_eq_zero

/-- Chapter01 Definition 1.3.23 (1): the source states this for a nonempty set `S ⊆ ℝ^n`, but
the supporting-sunYuanHyperplane predicate itself only uses the real inner-product-space sunYuanHyperplane
`sunYuanHyperplane p ⟪p, xbar⟫` and its two closed half-spaces. -/
def IsSupportingHyperplaneAt (S : Set E) (xbar p : E) : Prop :=
  S.Nonempty ∧
    xbar ∈ frontier S ∧
      p ≠ 0 ∧
        (S ⊆ closedUpperHalfSpace p ⟪p, xbar⟫ ∨
          S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫)

/-- Unfolding formula for `IsSupportingHyperplaneAt`. -/
theorem isSupportingHyperplaneAt_iff (S : Set E) (xbar p : E) :
    IsSupportingHyperplaneAt S xbar p ↔
      S.Nonempty ∧
        xbar ∈ frontier S ∧
          p ≠ 0 ∧
            (S ⊆ closedUpperHalfSpace p ⟪p, xbar⟫ ∨
              S ⊆ closedLowerHalfSpace p ⟪p, xbar⟫) :=
  Iff.rfl

/-- The source's half-space condition is the chapter-owner half-space formulation. -/
theorem isSupportingHyperplaneAt_iff_halfSpace
    {S : Set E} {xbar p : E} :
    IsSupportingHyperplaneAt S xbar p ↔
      S.Nonempty ∧
        xbar ∈ frontier S ∧
          p ≠ 0 ∧
            (S ⊆ { x | (0 : ℝ) ≤ ⟪p, x - xbar⟫ } ∨
              S ⊆ { x | ⟪p, x - xbar⟫ ≤ (0 : ℝ) }) := by
  simp [IsSupportingHyperplaneAt, closedUpperHalfSpace, closedLowerHalfSpace, inner_sub_right]

/-- Chapter01 Definition 1.3.23 (2): a supporting sunYuanHyperplane is proper when `S` is not contained
in the sunYuanHyperplane itself. -/
def IsProperSupportingHyperplaneAt (S : Set E) (xbar p : E) : Prop :=
  IsSupportingHyperplaneAt S xbar p ∧ ¬ S ⊆ sunYuanHyperplane p ⟪p, xbar⟫

/-- Unfolding formula for `IsProperSupportingHyperplaneAt`. -/
theorem isProperSupportingHyperplaneAt_iff (S : Set E) (xbar p : E) :
    IsProperSupportingHyperplaneAt S xbar p ↔
      IsSupportingHyperplaneAt S xbar p ∧ ¬ S ⊆ sunYuanHyperplane p ⟪p, xbar⟫ :=
  Iff.rfl

/-- The source's properness clause is exactly that `S` is not contained in the anchored
sunYuanHyperplane equation `⟪p, x - xbar⟫ = 0`. -/
theorem isProperSupportingHyperplaneAt_iff_not_subset_setOf
    {S : Set E} {xbar p : E} :
    IsProperSupportingHyperplaneAt S xbar p ↔
      IsSupportingHyperplaneAt S xbar p ∧ ¬ S ⊆ { x | ⟪p, x - xbar⟫ = (0 : ℝ) } := by
  constructor
  · rintro ⟨h_supporting, h_not_subset⟩
    refine ⟨h_supporting, ?_⟩
    intro h_subset
    apply h_not_subset
    simpa [sunYuanHyperplane_eq_setOf_sub_eq_zero] using h_subset
  · rintro ⟨h_supporting, h_not_subset⟩
    refine ⟨h_supporting, ?_⟩
    intro h_subset
    apply h_not_subset
    simpa [sunYuanHyperplane_eq_setOf_sub_eq_zero] using h_subset

end Chapter01Definition1323

/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_23

-- Semantic recall hits verified for this item: mathlib has separation theorems such as
-- `separate_convex_open_set` and `geometric_hahn_banach_open_open`, but no canonical owner for
-- the source's sunYuanHyperplane-separation vocabulary. This file reuses the chapter owners
-- `sunYuanHyperplane`, `closedUpperHalfSpace`, `closedLowerHalfSpace`, `openUpperHalfSpace`, and
-- `openLowerHalfSpace` from `Definition_1_3_23`, whose primitive data is just a normal vector
-- and a level in a real inner-product space.

open Set
open scoped RealInnerProductSpace

section Chapter01Definition1326

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `separates S₁ S₂ p α` means the genuine sunYuanHyperplane `sunYuanHyperplane p α`, with nonzero normal
`p`, leaves `S₁` in the closed upper half-space and `S₂` in the closed lower half-space
determined by `p` and `α`. -/
def separates (S₁ S₂ : Set E) (p : E) (α : ℝ) : Prop :=
  p ≠ 0 ∧ S₁ ⊆ closedUpperHalfSpace p α ∧ S₂ ⊆ closedLowerHalfSpace p α

/-- `properlySeparates S₁ S₂ p α` means `sunYuanHyperplane p α` separates `S₁` and `S₂`, and some point
of `S₁ ∪ S₂` lies off the sunYuanHyperplane. As in Definition 1.3.23, the canonical core is that the
relevant set is not contained in the sunYuanHyperplane. -/
def properlySeparates (S₁ S₂ : Set E) (p : E) (α : ℝ) : Prop :=
  separates S₁ S₂ p α ∧ ¬ (S₁ ∪ S₂ ⊆ sunYuanHyperplane p α)

/-- `strictlySeparates S₁ S₂ p α` means the genuine sunYuanHyperplane `sunYuanHyperplane p α`, with nonzero
normal `p`, puts the points of `S₁` and `S₂` in opposite open half-spaces. -/
def strictlySeparates (S₁ S₂ : Set E) (p : E) (α : ℝ) : Prop :=
  p ≠ 0 ∧ S₁ ⊆ openUpperHalfSpace p α ∧ S₂ ⊆ openLowerHalfSpace p α

/-- `stronglySeparates S₁ S₂ p α` means the genuine sunYuanHyperplane `sunYuanHyperplane p α`, with nonzero
normal `p`, admits a positive margin `ε` for which `α + ε ≤ ⟪p, x⟫` on `S₁` and
`⟪p, x⟫ ≤ α` on `S₂`. -/
def stronglySeparates (S₁ S₂ : Set E) (p : E) (α : ℝ) : Prop :=
  p ≠ 0 ∧ ∃ ε > 0, S₁ ⊆ closedUpperHalfSpace p (α + ε) ∧ S₂ ⊆ closedLowerHalfSpace p α

/-- Chapter01 Definition 1.3.26 (1): the source states this for nonempty convex subsets of
`ℝ^n`, but the defining separation condition itself only uses the real inner-product-space
sunYuanHyperplane data
`p ≠ 0` together with the two half-space inclusions. The sunYuanHyperplane `sunYuanHyperplane p α`
separates `S₁` and `S₂` exactly when `p ≠ 0`, `α ≤ ⟪p, x⟫` for all `x ∈ S₁`, and
`⟪p, x⟫ ≤ α` for all `x ∈ S₂`. -/
theorem separates_iff {S₁ S₂ : Set E} {p : E} {α : ℝ} :
    separates S₁ S₂ p α ↔
      p ≠ 0 ∧ (∀ x ∈ S₁, α ≤ ⟪p, x⟫) ∧ ∀ x ∈ S₂, ⟪p, x⟫ ≤ α := by
  simp [separates, Set.subset_def]

/-- Chapter01 Definition 1.3.26 (2): the source states this for nonempty convex subsets of
`ℝ^n`, but the proper-separation clause itself only adds that some point of `S₁ ∪ S₂` lies off
the sunYuanHyperplane. -/
theorem properlySeparates_iff {S₁ S₂ : Set E} {p : E} {α : ℝ} :
    properlySeparates S₁ S₂ p α ↔
      separates S₁ S₂ p α ∧ ∃ x ∈ S₁ ∪ S₂, x ∉ sunYuanHyperplane p α :=
  by
    classical
    simp [properlySeparates, Set.subset_def]

/-- The source's “some point lies off the sunYuanHyperplane” clause is equivalent to saying that
`S₁ ∪ S₂` is not contained in `sunYuanHyperplane p α`. -/
theorem properlySeparates_iff_not_subset_sunYuanHyperplane
    {S₁ S₂ : Set E} {p : E} {α : ℝ} :
    properlySeparates S₁ S₂ p α ↔
      separates S₁ S₂ p α ∧ ¬ (S₁ ∪ S₂ ⊆ sunYuanHyperplane p α) :=
  Iff.rfl

/-- Chapter01 Definition 1.3.26 (3): the source states this for nonempty convex subsets of
`ℝ^n`, but the defining strict-separation condition itself only uses the real inner-product-space
sunYuanHyperplane data
`p ≠ 0` together with the open half-space inclusions. The sunYuanHyperplane `sunYuanHyperplane p α`
strictly separates `S₁` and `S₂` exactly when `p ≠ 0`, `α < ⟪p, x⟫` for all `x ∈ S₁`, and
`⟪p, x⟫ < α` for all `x ∈ S₂`. -/
theorem strictlySeparates_iff {S₁ S₂ : Set E} {p : E} {α : ℝ} :
    strictlySeparates S₁ S₂ p α ↔
      p ≠ 0 ∧ (∀ x ∈ S₁, α < ⟪p, x⟫) ∧ ∀ x ∈ S₂, ⟪p, x⟫ < α := by
  simp [strictlySeparates, Set.subset_def]

/-- Chapter01 Definition 1.3.26 (4): the source states this for nonempty convex subsets of
`ℝ^n`, but the defining strong-separation condition itself only uses the real inner-product-space
sunYuanHyperplane data
`p ≠ 0` together with the margin inequality. The sunYuanHyperplane `sunYuanHyperplane p α` strongly
separates `S₁` and `S₂` exactly when `p ≠ 0` and there exists `ε > 0` such that
`α + ε ≤ ⟪p, x⟫` for all `x ∈ S₁` and `⟪p, x⟫ ≤ α` for all `x ∈ S₂`. -/
theorem stronglySeparates_iff {S₁ S₂ : Set E} {p : E} {α : ℝ} :
    stronglySeparates S₁ S₂ p α ↔
      p ≠ 0 ∧ ∃ ε > 0, (∀ x ∈ S₁, α + ε ≤ ⟪p, x⟫) ∧ ∀ x ∈ S₂, ⟪p, x⟫ ≤ α := by
  simp [stronglySeparates, Set.subset_def]

end Chapter01Definition1326

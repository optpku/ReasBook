/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The hyperplane through `x` with normal vector `u`, given by the level set
`{y | ⟪y, u⟫_ℝ = ⟪x, u⟫_ℝ}`. -/
def supportingHyperplane (x u : H) : Set H :=
  innerProductLevelSet u ⟪x, u⟫_ℝ

/-- Definition 7.1: the support points of `C` are the points of `C` at which some nonzero normal
vector attains the support functional of `C`; the textbook denotes this set by `spts C`, and its
closure is `closure (spts C)`. -/
noncomputable def supportPoints (C : Set H) : Set H :=
  {x : H | x ∈ C ∧ ∃ u : H, u ≠ 0 ∧ innerSupremumOn C u ≤ (⟪x, u⟫_ℝ : EReal)}

scoped notation "spts" => Set.supportPoints

-- The textbook notation `\overline{\operatorname{spts}}\, C` is formalized as `closure (spts C)`.

-- Proof sketch: unfold `supportingHyperplane` and rewrite membership with
-- `mem_innerProductLevelSet_iff`.
/-- Membership in the supporting hyperplane through `x` with normal vector `u` is the equation
`⟪y, u⟫_ℝ = ⟪x, u⟫_ℝ`. -/
theorem mem_supportingHyperplane_iff {x u y : H} :
    y ∈ supportingHyperplane x u ↔ ⟪y, u⟫_ℝ = ⟪x, u⟫_ℝ := by
  -- Unfold the supporting hyperplane into the imported inner-product level set.
  rw [supportingHyperplane, mem_innerProductLevelSet_iff]

-- Proof sketch: unfold `supportPoints` and simplify the set-membership statement.
/-- A point belongs to `spts C` exactly when it lies in `C` and some nonzero normal vector attains
`innerSupremumOn C` at that point. -/
theorem mem_supportPoints_iff {C : Set H} {x : H} :
    x ∈ spts C ↔ x ∈ C ∧ ∃ u : H, u ≠ 0 ∧ innerSupremumOn C u ≤ (⟪x, u⟫_ℝ : EReal) := by
  -- Unfold the definition of `spts` to expose the defining conjunction and existential.
  rfl

-- Proof sketch: use `mem_supportPoints_iff` and project to the first conjunct.
/-- Every support point of `C` belongs to `C`. -/
theorem supportPoints_subset {C : Set H} :
    spts C ⊆ C := by
  intro x hx
  -- Membership in `spts C` immediately records that `x ∈ C`.
  exact (mem_supportPoints_iff.mp hx).1

end

end Set

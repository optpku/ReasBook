/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise InnerProductSpace

universe u

namespace Set

section

variable {E : Type u} [Add E]

/-- Definition 6.48 (1): the recession cone `rec C` is the set of vectors `x` such that
`x + C ⊆ C`, written in Lean as `{x} + C ⊆ C`. -/
def recessionCone (C : Set E) : Set E :=
  {x : E | ({x} : Set E) + C ⊆ C}

scoped notation "rec" => Set.recessionCone

-- Proof sketch: unfold `Set.recessionCone` and simplify membership in the defining subset.
/-- Membership in the recession cone means that translating `C` by `x` keeps it inside `C`. -/
theorem mem_recessionCone_iff {C : Set E} {x : E} :
    x ∈ rec C ↔ ({x} : Set E) + C ⊆ C := by
  -- Unfolding the defining set comprehension identifies membership with the subset condition.
  rfl

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Definition 6.48 (2): the barrier cone `bar C` is the set of vectors `u` for which the support
value `sup ⟪C | u⟫` is finite, represented in Lean by `innerSupremumOn C u < ⊤`. -/
noncomputable def barrierCone (C : Set 𝓗) : Set 𝓗 :=
  {u : 𝓗 | innerSupremumOn C u < ⊤}

scoped notation "bar" => Set.barrierCone

-- Proof sketch: unfold `Set.barrierCone` and simplify membership in the defining subset.
/-- Membership in the barrier cone means that the inner-product supremum of `C` in direction `u` is
finite. -/
theorem mem_barrierCone_iff {C : Set 𝓗} {u : 𝓗} :
    u ∈ bar C ↔ innerSupremumOn C u < ⊤ := by
  -- Unfolding the defining set comprehension identifies membership with finiteness of the supremum.
  rfl

end

end Set

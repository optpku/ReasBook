/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

namespace Set

/-- The symmetrization `U^{±1}` of a set of group elements. -/
def symmetrization {α : Type*} [Group α] (U : Set α) : Set α :=
  U ∪ U⁻¹

end Set

namespace Symmetrization

scoped notation:max U "^{±1}" => Set.symmetrization U

end Symmetrization

open scoped Symmetrization

namespace FreeGroup

variable {X : Type u} [DecidableEq X]

-- Layer triage:
-- `source-facing`: the textbook Nielsen conditions `(N0)` through `(N2)` for a family of words.
-- `core/canonical`: `FreeGroup.IsNReduced` on a subset of the ambient free group.
-- `bridge/view`: a sequence is `N`-reduced exactly when its range satisfies the owner predicate.
--
-- Domain sampling:
-- 1. `FreeGroup.IsNReduced.exists_prefix_middle_segments` in Proposition `1-2-5` builds the
--    chapter's derived API from the set-level owner.
-- 2. `FreeGroup.IsNReduced.norm_list_prod_ge_length` in Corollary `1-2-6` is another owner-side
--    consequence used downstream.
-- 3. `closure_preimage_isFreeGroupBasis_of_isNReduced` in Proposition `1-2-7` treats the same
--    set-level predicate as the canonical input to the free-basis theorem.
--
-- Primitive vs. derived:
-- the primitive data are only the subset `U` and Nielsen's three inequalities on `U ∪ U⁻¹`.
-- Sequence-level phrasing is derived by passing to `Set.range`, so it should stay a thin bridge.

/-- A subset of a free group is `N`-reduced when the Nielsen conditions `(N0)` through `(N2)` hold
for all elements of `U^{±1}`. -/
class IsNReduced (U : Set (FreeGroup X)) : Prop where
  /-- Condition `(N0)`: every element of `U^{±1}` is nontrivial. -/
  n0 {u : FreeGroup X} (hu : u ∈ U^{±1}) : u ≠ 1
  /-- Condition `(N1)`: whenever `uv ≠ 1`, the reduced length of `uv` is at least the reduced
  length of each factor. -/
  n1 {u v : FreeGroup X} (hu : u ∈ U^{±1}) (hv : v ∈ U^{±1}) (huv : u * v ≠ 1) :
      max (norm u) (norm v) ≤ norm (u * v)
  /-- Condition `(N2)`: if neither adjacent product is trivial, then the reduced length of the
  triple product is strictly larger than `|u| - |v| + |w|`. -/
  n2 {u v w : FreeGroup X}
      (hu : u ∈ U^{±1})
      (hv : v ∈ U^{±1})
      (hw : w ∈ U^{±1})
      (huv : u * v ≠ 1)
      (hvw : v * w ≠ 1) :
      (norm u : ℤ) - norm v + norm w < norm (u * v * w)

instance : IsNReduced (∅ : Set (FreeGroup X)) where
  n0 := by
    intro u hu
    rcases hu with hu | hu <;> cases hu
  n1 := by
    intro u v hu hv huv
    rcases hu with hu | hu <;> cases hu
  n2 := by
    intro u v w hu hv hw huv hvw
    rcases hu with hu | hu <;> cases hu

namespace IsNReduced

variable {U : Set (FreeGroup X)}

/-- Every element of an `N`-reduced subset is nontrivial. -/
theorem term_ne_one (hU : IsNReduced U) {u : FreeGroup X} (hu : u ∈ U) :
    u ≠ 1 :=
  hU.n0 (Or.inl hu)

end IsNReduced

end FreeGroup

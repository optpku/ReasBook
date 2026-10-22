/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace Set

section

variable {E : Type u} [AddGroup E]

/-- Definition 6.5 (1): a cone is pointed when its intersection with its negative is contained in
`{0}`. -/
def IsPointedCone (K : Set E) : Prop :=
  K ∩ -K ⊆ ({0} : Set E)

-- Proof sketch: unfold `Set.IsPointedCone`; this is exactly the defining condition from the
-- textbook.
/-- Being a pointed cone means that the intersection with the negative cone is contained in
`{0}`. -/
theorem isPointedCone_iff {K : Set E} :
    IsPointedCone K ↔ K ∩ -K ⊆ ({0} : Set E) := by
  -- This theorem is just the definitional interface for `Set.IsPointedCone`.
  rfl

end

section

variable {E : Type u} [TopologicalSpace E]

/-- Definition 6.5 (2): a cone is solid when it has nonempty interior. -/
def IsSolidCone (K : Set E) : Prop :=
  (interior K).Nonempty

-- Proof sketch: unfold `Set.IsSolidCone`; the textbook definition is exactly nonemptiness of the
-- interior.
/-- Being a solid cone means that the interior is nonempty. -/
theorem isSolidCone_iff {K : Set E} :
    IsSolidCone K ↔ (interior K).Nonempty := by
  -- This theorem is just the definitional interface for `Set.IsSolidCone`.
  rfl

end

end Set

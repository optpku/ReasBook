/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Subgroup

variable {G : Type u} [Group G]

/- Definition 3.4.4: for a subgroup `H` of `G`, its normalizer is the canonical subgroup
`Subgroup.normalizer H`. -/
#check (fun H : Subgroup G ↦ Subgroup.normalizer (H : Set G))

/-- Definition 3.4.4: the Weyl group of `H` is the quotient of its normalizer by `H`, viewed as a
subgroup of `normalizer H`. -/
abbrev weylGroup (H : Subgroup G) : Type u :=
  Subgroup.normalizer H ⧸ H.subgroupOf (Subgroup.normalizer H)

/-- The Weyl group is canonically the quotient of `normalizer H` by the induced copy of `H`. -/
-- Proof sketch: This is immediate from unfolding `weylGroup`.
theorem weylGroup_def (H : Subgroup G) :
    weylGroup H = (Subgroup.normalizer H ⧸ H.subgroupOf (Subgroup.normalizer H)) := by
  -- Unfold the abbreviation to identify the Weyl group with the stated quotient.
  rfl

end Subgroup

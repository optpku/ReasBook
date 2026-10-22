/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 1-2-13: every subgroup of a free group is free.

This source-facing item is exactly the canonical Nielsen-Schreier owner theorem already available
in mathlib, so the file keeps a direct recall of `subgroupIsFreeOfIsFree` rather than introducing
any parallel local wrapper. -/
#check (subgroupIsFreeOfIsFree :
  ∀ {G : Type u} [Group G] [IsFreeGroup G] (H : Subgroup G), IsFreeGroup H)

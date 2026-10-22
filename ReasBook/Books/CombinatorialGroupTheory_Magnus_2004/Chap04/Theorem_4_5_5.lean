/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap04.Definition_4_5_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open scoped Pointwise

noncomputable section

-- Layer triage:
-- `source-facing`: a one-relator group `PresentedGroup (Set.singleton r)`, a Magnus subgroup in
-- the sense of Definition `4-5-4`, and the intersection of that subgroup with a nontrivial
-- conjugate.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
-- `IsMagnusSubgroup` from Definition `4-5-4` for the source-facing Magnus subgroup predicate, and
-- subgroup conjugation via the action of `MulAut.conj`.
-- `bridge/view`: this theorem is stated directly with the chapter owner predicate, so no parallel
-- local Magnus-subgroup wrapper is kept here.
--
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for the one-relator
--    group with defining relator `r`.
-- 2. `IsMagnusSubgroup` from Definition `4-5-4` is the existing source-facing predicate for
--    Magnus subgroups.
-- 3. `MulAut.conj g • M` is mathlib's canonical API for the conjugate subgroup `gMg⁻¹`.
--
-- Primitive vs. derived:
-- the primitive source-facing data are the relator `r`, the subgroup `M`, and the owner-level
-- hypothesis `IsMagnusSubgroup r M`, and the theorem's cyclicity conclusion is stated directly for the
-- canonical conjugate-intersection subgroup.

variable {X : Type u}
variable (r : FreeGroup X)

local instance theorem_4_5_5_decidableEq : DecidableEq X := Classical.decEq X

local notation "G" => PresentedGroup (Set.singleton r)

/-- Theorem 4-5-5: if `r` is cyclically reduced, `M` is a Magnus subgroup of the one-relator
group `PresentedGroup (Set.singleton r)`, and `g` does not lie in `M`, then the
intersection `gMg⁻¹ ∩ M` is cyclic. -/
-- Proof sketch: argue by induction on the length of the cyclically reduced relator. The
-- two-generator case is handled by viewing the group as a free product with amalgamation and using
-- normal-form uniqueness to force the intersection into the amalgamated cyclic subgroup. In the
-- general case, rewrite the one-relator group as an HNN extension after arranging a generator of
-- exponent sum zero; Britton's lemma then reduces a noncyclic conjugate intersection to the
-- induction hypothesis on a shorter relator, and the standard zero-exponent-sum trick covers the
-- remaining case.
theorem conjugate_intersection_isCyclic_of_isMagnusSubgroup
    (hred : FreeGroup.IsCyclicallyReduced r.toWord)
    (M : Subgroup G) (hM : IsMagnusSubgroup r M) (g : G)
    (hg : g ∉ M) :
    IsCyclic ↥((MulAut.conj g • M) ⊓ M) :=
  sorry

end

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)`, expressed canonically as the quotient
-- `PresentedGroup (Set.singleton r)`, together with the hypothesis that the relator `r`
-- is not a proper power in the ambient free group on `X`.
-- `core/canonical`: `PresentedGroup` for the one-relator quotient and `IsMulTorsionFree` for the
-- textbook conclusion that `G` is torsion free.
-- `bridge/view`: the source phrase “`r` is not a proper power” is rendered by the canonical
-- predicate `¬ IsProperPower r`.
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the project's canonical owner for a
--    one-relator group on generators `X`.
-- 2. `IsMulTorsionFree` is mathlib's owner predicate for the torsion-free property of a group.
-- 3. `IsProperPower` from `CombinatorialGroupTheory.Basic` is the shared owner predicate for the
--    proper-power condition on an element of a monoid.
-- 4. Nearby one-relator items in this chapter already state source-facing results directly on
--    `PresentedGroup (Set.singleton r)`, so this proposition follows the same owner level.
-- Primitive vs. derived:
-- the primitive public data are only the generator type `X`, the relator `r`, and the
-- non-proper-power hypothesis on `r`; torsion-freeness of the quotient is the derived conclusion.

/-- Proposition 2-5-17: if `G = (X; r)` is a one-relator group and the relator `r` is not a
proper power in `FreeGroup X`, then the quotient group `PresentedGroup (Set.singleton r)`
is torsion free. -/
-- Proof sketch: this is Magnus's torsion theorem for one-relator groups. If an element of
-- `PresentedGroup (Set.singleton r)` had finite order, choose a lift to `FreeGroup X`;
-- Magnus's analysis of torsion in one-relator quotients shows that some conjugate of a nontrivial
-- power of the relator must represent that torsion element. The hypothesis that `r` is not a
-- proper power rules this out, so every finite-order element is trivial.
theorem isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower
    {X : Type u} (r : FreeGroup X)
    (hr : ¬ IsProperPower r) :
    IsMulTorsionFree (PresentedGroup (Set.singleton r)) := sorry

end

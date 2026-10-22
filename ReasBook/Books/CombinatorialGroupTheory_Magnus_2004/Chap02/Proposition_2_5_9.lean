/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} (r : FreeGroup X)

local notation "G" => PresentedGroup (Set.singleton r : Set (FreeGroup X))

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)`, rendered canonically as the quotient
-- `PresentedGroup (Set.singleton r : Set (FreeGroup X))`, together with the hypothesis that this quotient is
-- itself
-- free.
-- `core/canonical`: `PresentedGroup` for one-relator presentations, `IsFreeGroup` for the
-- ambient freeness hypothesis on the quotient, and `IsPrimitiveElement` as the chapter owner for
-- the statement that `r` belongs to some basis of the ambient free group on `X`.
-- `bridge/view`: `IsPrimitiveElement r` records a same-universe basis witness for `r`; an
-- arbitrary chosen basis is canonically reindexed to its range via
-- `FreeGroupBasis.reindexRange`, so
-- the source wording is recovered without a duplicate existential wrapper theorem.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's canonical owner for a group defined by generators and
--    relators.
-- 2. `IsFreeGroup` is mathlib's owner predicate for freeness of a group.
-- 3. `FreeGroupBasis X F`, together with the owner bridge `FreeGroupBasis.reindexRange`, is the
--    canonical API for chosen free bases and the corresponding basis subset in the ambient group.
-- 4. `IsPrimitiveElement` from `CombinatorialGroupTheory.Basic` is the project owner for the
--    recurring “belongs to some basis”
--    conclusion, while basis witnesses are bridge data.
-- Primitive vs. derived:
-- the primitive data are only the generator type `X`, the relator `r`, and the freeness
-- hypothesis on the quotient; primitivity of `r` is the derived conclusion, while explicit basis
-- witnesses are companion API.

/-- Proposition 2-5-9: if the one-relator group `G = (X; r)` is free, then either `r = 1` or `r`
is primitive in the ambient free group on `X`. -/
-- Proof sketch: if the canonical one-relator quotient
-- `G = PresentedGroup (Set.singleton r : Set (FreeGroup X))` is
-- free, compare its rank with that of the ambient free group `FreeGroup X`. Magnus's freeness
-- criterion for one-relator quotients shows that `G` can be free only when the defining relator
-- is trivial or primitive; the primitive alternative is exactly `IsPrimitiveElement r`.
theorem relator_eq_one_or_isPrimitiveElement_of_presentedGroup_isFree
    (hfree : IsFreeGroup G) :
    r = 1 ∨ IsPrimitiveElement r := sorry

end

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u

namespace GroupPresentation

variable {X : Type u} [Primcodable X]

-- Layer triage:
-- `source-facing`: a presentation datum consisting of a generator type `X` and relator set
-- `R : Set (FreeGroup X)`, together with the textbook condition that the relators are recursively
-- enumerable from finite signed words.
-- `core/canonical`: the chapter owner namespace `GroupPresentation` for presentation-level
-- properties, `FreeGroup.mk` as the canonical map from signed words to the free group, and
-- `REPred` as mathlib's recursively enumerable predicate.
-- `bridge/view`: the source phrase "the presentation `(X; R)` is recursive" is expressed by the
-- predicate on signed words sending `L` to `FreeGroup.mk L ∈ R`.
-- Domain sampling:
-- 1. `Finite X` and `Set.Finite R` from Definition `2-1-2` are the canonical finiteness
--    predicates on the underlying generator type and relator set.
-- 2. `FreeGroup.mk` is the canonical word-to-element map on the free group.
-- 3. `REPred` is mathlib's owner predicate for recursively enumerable subsets of a `Primcodable`
--    type.
-- Primitive vs. derived:
-- the primitive source data are only `X` and `R`; the recursively enumerable word-membership
-- predicate is the derived owner-side API, so no separate wrapper around the presentation data is
-- introduced.

/-- Definition 2-1-3: a presentation with generators indexed by `X` and relator set
`R : Set (FreeGroup X)` is recursive when the set of finite signed words whose image under
`FreeGroup.mk` lies in `R` is recursively enumerable. -/
def IsRecursive (R : Set (FreeGroup X)) : Prop :=
  REPred (fun L : List (X × Bool) ↦ FreeGroup.mk L ∈ R)

end GroupPresentation

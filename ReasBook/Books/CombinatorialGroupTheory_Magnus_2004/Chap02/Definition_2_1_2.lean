/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe v

-- Layer triage:
-- `source-facing`: a presentation datum consisting of a generator type `X` and a relator set
-- `R : Set (FreeGroup X)`, together with the textbook finiteness terminology for that datum.
-- `core/canonical`: `Finite X` for finiteness of the generator type and `Set.Finite R` for
-- finiteness of the relator set.
-- `bridge/view`: the textbook phrase "finite presentation" is exactly the conjunction of these
-- two owner predicates.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for generators-and-relations data from
--    Definition `2-1-1`, but the present item adds only finiteness conditions on the source data.
-- 2. `Finite X` is the canonical finiteness predicate for a type of generators.
-- 3. `Set.Finite R` is the canonical finiteness predicate for a relator set.
-- Primitive vs. derived:
-- the primitive source data are only `X` and `R`; the three textbook finiteness phrases below are
-- direct uses of the owner predicates above, so the file keeps the raw canonical predicates
-- `Finite X` and `Set.Finite R` rather than introducing parallel names such as
-- `GroupPresentation.IsFinitelyGenerated` or `GroupPresentation.IsFinitelyRelated`.

namespace GroupPresentation

variable {X : Type v} {R : Set (FreeGroup X)}

/- Definition 2-1-2 (1): a presentation is finitely generated exactly when its generator type is
finite. -/
#check (Finite X)

/- Definition 2-1-2 (2): a presentation is finitely related exactly when its relator set is
finite. -/
#check (Set.Finite R)

/- Definition 2-1-2 (3): a presentation is finite exactly when it is both finitely generated and
finitely related, i.e. when `Finite X ∧ Set.Finite R`. -/
#check (Finite X ∧ Set.Finite R)

end GroupPresentation

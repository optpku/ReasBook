/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_6

open CategoryTheory
open CategoryTheory.ObjectProperty
open IsFreeGroupoid

namespace OneComplex

-- Layer triage:
-- `source-facing`: a `1`-complex `C`, a vertex `v : C`, and the textbook claim that the
-- fundamental group `π(C, v)` is free.
-- `core/canonical`: `CategoryTheory.ConnectedComponents.Component` is the canonical owner for the
-- connected component of a chosen object, and `IsFreeGroup` is the owner predicate for freeness of
-- a group.
-- `bridge/view`: the chapter-local `OneComplex.fundamentalGroup C v`, written `π(C, v)`, is the
-- source-facing owner for the loop group at `v`; its proof is obtained by restricting the free
-- groupoid structure on `Quiver.Path.pi1 C` to the connected component of `⟨v⟩` and then
-- transporting freeness back along the fully faithful inclusion.
-- Domain sampling:
-- 1. `OneComplex.fundamentalGroup` is the chapter owner for the based fundamental group `π(C, v)`.
-- 2. `CategoryTheory.ConnectedComponents.Component` is the canonical connected-component owner for
--    reducing a loop-group statement to a connected groupoid.
-- 3. `IsFreeGroupoid.endIsFreeOfConnectedFree` is the core freeness theorem for loop groups in a
--    connected free groupoid.
-- 4. `Functor.FullyFaithful.mulEquivEnd` is the canonical bridge transporting the loop group on a
--    connected component back to the ambient endomorphism group.
-- Primitive vs. derived:
-- the primitive data are the `1`-complex `C` and the chosen vertex `v`; the connected component of
-- `⟨v⟩`, the restricted free-groupoid structure on that component, and the endomorphism-group
-- equivalence induced by the inclusion are all derived proof-internal bridge data.

/-- Proposition 3-2-9: if `C` is a `1`-complex and `v` is any vertex of `C`, then the
fundamental group `π(C, v)` is free.

The proof passes to the connected component of `⟨v⟩` in the fundamental groupoid `Π¹(C)`, applies
the canonical free-groupoid theorem there, and transports the resulting free group structure back
along the fully faithful inclusion of that component. No global connectedness hypothesis belongs in
the public statement. -/
theorem fundamentalGroup_isFree (C : OneComplex) (v : C) :
    IsFreeGroup (π(C, v)) := by
  sorry

end OneComplex

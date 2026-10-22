/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_7

universe u v w

open CategoryTheory

-- Layer triage:
-- `source-facing`: for a vertex `v` of a `2`-complex `C`, the loops at `v` in the `1`-skeleton
-- form a semigroup, and their image in the fundamental groupoid is the fundamental group
-- `π(C, v)`.
-- `core/canonical`: `CategoryTheory.Paths C.skeleton` is the canonical path category of the
-- `1`-skeleton, `C.pi` is the already defined fundamental groupoid, and `CategoryTheory.End` is
-- the canonical owner for vertex loops in both settings.
-- `bridge/view`: the textbook notations `Π(C, v)` and `π(C, v)` are expressed by the
-- endomorphism types at `v` before and after quotienting by `2`-equivalence.
-- Domain sampling:
-- 1. `CategoryTheory.Paths.categoryPaths` is the canonical category structure on quiver paths.
-- 2. `CategoryTheory.End` is the canonical owner of loops at a chosen object.
-- 3. `CategoryTheory.End.monoid` gives the multiplicative structure on loops in a category.
-- 4. `CategoryTheory.End.group` upgrades this to a group when the ambient category is a groupoid.

namespace TwoComplex

variable (C : TwoComplex) (v : C.skeleton)

/- Definition 3-2-8: for a vertex `v` of a `2`-complex `C`, the fundamental group `π(C, v)` is
the vertex group at `v` in the fundamental groupoid `π(C)`.

The unquotiented loop set `Π(C, v)` is the endomorphism monoid of `v` in the path category of the
`1`-skeleton, while the quotient group is the endomorphism group `End (⟨v⟩ : C.pi)`. -/
#check (CategoryTheory.End (⟨v⟩ : C.pi))

/-- The source-facing loop semigroup `Π(C, v)` is the endomorphism monoid at `v` in the path
category of the `1`-skeleton. -/
abbrev loopSemigroup (C : TwoComplex) (v : C.skeleton) :=
  CategoryTheory.End ((CategoryTheory.Paths.of C.skeleton).obj v)

/-- The source-facing loop semigroup agrees with the endomorphism monoid of `v` in the path
category of the `1`-skeleton. -/
-- Proof sketch: unfold `loopSemigroup`; it is defined to be this endomorphism monoid.
theorem loopSemigroup_eq_end (C : TwoComplex) (v : C.skeleton) :
    loopSemigroup C v = CategoryTheory.End ((CategoryTheory.Paths.of C.skeleton).obj v) := sorry

/-- The source-facing fundamental group `π(C, v)` is the endomorphism group at `v` in the
fundamental groupoid `π(C)`. -/
abbrev fundamentalGroup (C : TwoComplex) (v : C.skeleton) :=
  CategoryTheory.End (⟨v⟩ : C.pi)

scoped notation "π(" C ", " v ")" => TwoComplex.fundamentalGroup C v

/-- The notation `π(C, v)` is the endomorphism group of the object `⟨v⟩` in the fundamental
groupoid `π(C)`. -/
-- Proof sketch: unfold `fundamentalGroup`; the notation is just the corresponding endomorphism
-- group.
theorem fundamentalGroup_eq_end (C : TwoComplex) (v : C.skeleton) :
    π(C, v) = CategoryTheory.End (⟨v⟩ : C.pi) := sorry

/-- The loop semigroup at `v` inherits a semigroup structure from path composition in the
`1`-skeleton. -/
instance loopSemigroupSemigroup (C : TwoComplex) (v : C.skeleton) :
    Semigroup (loopSemigroup C v) :=
  inferInstance

/-- The fundamental group at `v` inherits a group structure from the groupoid structure on
`π(C)`. -/
noncomputable instance fundamentalGroupGroup (C : TwoComplex) (v : C.skeleton) :
    Group (π(C, v)) :=
  inferInstance

end TwoComplex

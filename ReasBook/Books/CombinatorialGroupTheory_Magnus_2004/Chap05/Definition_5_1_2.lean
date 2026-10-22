/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open Quiver.Path

universe u v

-- Layer triage:
-- `source-facing`: Definition 5-1-2 introduces paths, closed paths, reduced paths, and simple
-- paths in a fixed `1`-complex.
-- `core/canonical`: `OneComplex` from Definition 3-2-1 is the owner abstraction for oriented
-- edges, while `Quiver.Path`, `Quiver.Path.Loop`, `Quiver.Path.IsReduced`, and
-- `Quiver.Path.IsSimple` are the canonical owner declarations for the path notions in this item.
-- `bridge/view`: `OneComplex.Path.edges` recovers the textbook sequence of oriented edges from the
-- canonical total-edge list `Quiver.Path.edgeList`.
-- Domain sampling:
-- 1. `Quiver.Path` is mathlib's canonical endpoint-aware finite path type and already includes the
--    empty path.
-- 2. `Quiver.Path.Loop` is the established owner for closed paths with a remembered basepoint.
-- 3. `Quiver.Path.IsReduced` and `Quiver.Path.IsSimple` already define the reduced/simple path
--    predicates upstream in Chapter 3.
-- 4. `Quiver.Path.edgeList` is the canonical ordered total-edge list, from which the textbook
--    oriented-edge sequence is derived.
-- Primitive vs. derived:
-- this item contributes no new owner object beyond the existing path API on `Quiver.Path`; the
-- only additional source-facing bridge needed here is the oriented-edge list of a path.

namespace OneComplex

/- Definition 5-1-2: a path in a `1`-complex from `a` to `b` is the canonical quiver path
`Quiver.Path a b`, with empty path `Quiver.Path.nil`. -/
#check Quiver.Path

/- A closed path is the special case `Quiver.Path a a`; the owner bundled API for based closed
paths is `Quiver.Path.Loop`. -/
#check Quiver.Path.Loop

/- Reduced paths in a `1`-complex are given by the owner predicate `Quiver.Path.IsReduced`. -/
#check Quiver.Path.IsReduced

/- Simple paths in a `1`-complex are given by the owner predicate `Quiver.Path.IsSimple`. -/
#check Quiver.Path.IsSimple

namespace Path

variable {C : OneComplex.{u, v}}

/-- The underlying sequence of oriented edges traversed by a path. -/
abbrev edges {a b : C} (p : Quiver.Path a b) : List C.Edge :=
  p.edgeList.map fun e ↦ e.hom.1

/-- The empty path traverses no oriented edges. -/
@[simp] theorem edges_nil (a : C) : edges (nil : Quiver.Path a a) = [] := rfl

@[simp] theorem edges_cons {a b c : C} (p : Quiver.Path a b) (e : b ⟶ c) :
    edges (cons p e) = edges p ++ [e.1] := by
  simp [edges, Quiver.Path.edgeList, List.map_append]

end Path

end OneComplex

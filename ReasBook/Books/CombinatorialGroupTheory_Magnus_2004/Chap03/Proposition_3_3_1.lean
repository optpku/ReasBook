/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open Quiver
open Quiver.Path
open scoped Quiver.Path

-- Layer triage:
-- `source-facing`: a morphism of `1`-complexes, the covering-map condition on outgoing oriented
-- edges, and the induced monomorphism on based fundamental groups.
-- `core/canonical`: `OneComplex.Hom` is the chapter owner for morphisms of `1`-complexes,
-- `Quiver.Prefunctor.IsCovering`, `Π¹(C)`, `CategoryTheory.Cat.freeMap`,
-- `CategoryTheory.Quotient.functor`, and `CategoryTheory.Functor.mapEnd` are the owners for the
-- covering condition, the fundamental groupoid, the induced path-category and quotient functors,
-- and the resulting based fundamental group homomorphism, while `Function.Injective` is the owner
-- API for a monomorphism of groups.
-- `bridge/view`: a `1`-complex morphism induces a quiver prefunctor and hence the canonical path
-- and quotient maps; the proposition is stated on `π(C, v)` rather than on raw loop
-- representatives.
-- Domain sampling:
-- 1. `Quiver.Prefunctor` and `Prefunctor.mapPath` are mathlib's owners for maps of quivers and
--    their induced path maps.
-- 2. `Quiver.Prefunctor.IsCovering` is the owner abstraction for coverings of quivers, and in a
--    `1`-complex its star-bijectivity presentation matches the textbook local covering condition.
-- 3. `Quiver.Path.path_one_equiv`, `Quiver.Path.pathOneHomRel`, and `Π¹(C)` are the owners for
--    backtracking-cancellation classes of paths and the resulting quotient groupoid.
-- 4. `CategoryTheory.Cat.freeMap` and `CategoryTheory.Quotient.functor` are the canonical owners
--    for the induced functor on path categories and the resulting map of fundamental groupoids.
-- 5. `OneComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for the based
--    fundamental group, and `CategoryTheory.Functor.mapEnd` is the owner for the induced
--    homomorphism on the endomorphism monoids of base objects.

namespace OneComplex

/-- A morphism of `1`-complexes sends vertices to vertices and oriented edges to oriented edges,
preserving endpoints and the edge-reversing involution. -/
structure Hom (C D : OneComplex.{u, v}) where
  /-- The induced map on vertices. -/
  toVertex : C → D
  /-- The induced map on oriented edges. -/
  toEdge : C.Edge → D.Edge
  /-- Initial vertices are preserved. -/
  map_initial (e : C.Edge) : toVertex (C.initial e) = D.initial (toEdge e)
  /-- Terminal vertices are preserved. -/
  map_terminal (e : C.Edge) : toVertex (C.terminal e) = D.terminal (toEdge e)
  /-- Reversing an edge commutes with the edge map. -/
  map_edgeInv (e : C.Edge) : toEdge (C.edgeInv e) = D.edgeInv (toEdge e)

namespace Hom

variable {C D : OneComplex.{u, v}} (f : Hom C D)

/-- Mapping an arrow of the quiver underlying a `1`-complex preserves its initial vertex. -/
-- Proof sketch: unpack the source arrow subtype and rewrite with `f.map_initial`.
theorem mapQuiverEdge_initial {x y : C} (e : x ⟶ y) :
    D.initial (f.toEdge e.1) = f.toVertex x := sorry

/-- Mapping an arrow of the quiver underlying a `1`-complex preserves its terminal vertex. -/
-- Proof sketch: unpack the source arrow subtype and rewrite with `f.map_terminal`.
theorem mapQuiverEdge_terminal {x y : C} (e : x ⟶ y) :
    D.terminal (f.toEdge e.1) = f.toVertex y := sorry

/-- A morphism of `1`-complexes induces a map on arrows in the associated quivers. -/
def mapQuiverEdge {x y : C} (e : x ⟶ y) : f.toVertex x ⟶ f.toVertex y :=
  ⟨f.toEdge e.1, f.mapQuiverEdge_initial e, f.mapQuiverEdge_terminal e⟩

/-- A morphism of `1`-complexes commutes with edge reversal on quiver arrows. -/
-- Proof sketch: extensionality on the underlying edge together with `f.map_edgeInv` identifies
-- the mapped reversed arrow with the reverse of the mapped arrow.
theorem mapQuiverEdge_reverse {x y : C} (e : x ⟶ y) :
    f.mapQuiverEdge (Quiver.reverse e) = Quiver.reverse (f.mapQuiverEdge e) := sorry

/-- The quiver prefunctor underlying a morphism of `1`-complexes. -/
def toPrefunctor : C ⥤q D where
  obj := f.toVertex
  map := f.mapQuiverEdge

/-- The underlying quiver prefunctor of a `1`-complex morphism preserves edge reversal. -/
instance toPrefunctor_mapReverse : f.toPrefunctor.MapReverse where
  map_reverse' e := by
    simpa using f.mapQuiverEdge_reverse e

/-- A morphism of `1`-complexes maps a path by applying the edge map to each oriented edge. -/
abbrev mapPath {x y : C} (p : Quiver.Path x y) : Quiver.Path (f.toVertex x) (f.toVertex y) :=
  f.toPrefunctor.mapPath p

/-- A morphism of `1`-complexes maps a based loop by transporting its base vertex and path. -/
abbrev mapLoop (p : Loop C) : Loop D :=
  ⟨f.toVertex p.1, f.mapPath p.2⟩

/-- A morphism of `1`-complexes maps a total edge by transporting its endpoints and arrow. -/
def mapTotal (e : Quiver.Total C) : Quiver.Total D :=
  ⟨f.toVertex e.left, f.toVertex e.right, f.mapQuiverEdge e.hom⟩

/-- Mapping the cyclically ordered total-edge list of a cyclic path along a `1`-complex
morphism preserves cyclic composability. -/
theorem cycle_chain_mapTotal (c : CyclicPath C) :
    (c.1.map f.mapTotal).Chain Quiver.Total.Composable := by
  rw [Cycle.chain_map]
  exact c.2.imp fun _ _ h ↦ congrArg f.toVertex h

/-- A morphism of `1`-complexes maps a cyclic path by transporting each total edge. -/
def mapCyclicPath (c : CyclicPath C) : CyclicPath D :=
  ⟨c.1.map f.mapTotal, f.cycle_chain_mapTotal c⟩

/-- Path mapping commutes with path reversal. -/
-- Proof sketch: induct on the path, rewrite the last edge with `f.mapQuiverEdge_reverse`, and
-- use the recursive description of `Quiver.Path.reverse`.
theorem mapPath_reverse {x y : C} (p : Quiver.Path x y) :
    f.mapPath p.reverse = (f.mapPath p).reverse := sorry

/-- A morphism of `1`-complexes preserves the elementary cancellation relation on paths. -/
-- Proof sketch: map every path segment and use `f.mapQuiverEdge_reverse` to show that an inserted
-- or deleted spur still has the form `ee⁻¹` after applying `f`.
theorem mapPath_reduction_step {x y : C} {p q : Quiver.Path x y}
    (h : Quiver.Path.path_one_reduction_step p q) :
    Quiver.Path.path_one_reduction_step (f.mapPath p) (f.mapPath q) := sorry

/-- A morphism of `1`-complexes preserves `1`-equivalence of paths. -/
-- Proof sketch: lift `f.mapPath_reduction_step` through the equivalence closure defining
-- `Quiver.Path.path_one_equiv`.
theorem mapPath_path_one_equiv {x y : C} {p q : Quiver.Path x y}
    (h : Quiver.Path.path_one_equiv p q) :
    Quiver.Path.path_one_equiv (f.mapPath p) (f.mapPath q) := sorry

/-- A morphism of `1`-complexes induces the canonical functor on fundamental groupoids. -/
def pi1Functor : Π¹(C) ⥤ Π¹(D) :=
  CategoryTheory.Quotient.lift _
    (Cat.freeMap f.toPrefunctor ⋙
      CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel D))
    (by
      intro x y p q h
      sorry)

/-- A morphism of `1`-complexes induces a homomorphism on based fundamental groups. -/
noncomputable def inducedFundamentalGroupHom (x : C) : π(C, x) →* π(D, f.toVertex x) :=
  f.pi1Functor.mapEnd (⟨x⟩ : Π¹(C))

/-- If a morphism sends `x` to `y`, then it induces the usual homomorphism
`π(C, x) → π(D, y)`. -/
noncomputable def inducedFundamentalGroupHomOver (x : C) (y : D) (hxy : f.toVertex x = y) :
    π(C, x) →* π(D, y) :=
  hxy ▸ f.inducedFundamentalGroupHom x

/-- The induced homomorphism on based fundamental groups is computed by mapping loop
representatives. -/
-- Proof sketch: unfold `f.inducedFundamentalGroupHom`; it is the vertex-group map induced by the
-- functor `f.pi1Functor`, whose action on a loop class is represented by `f.mapPath`.
theorem inducedFundamentalGroupHom_apply_path (x : C) (p : Quiver.Path x x) :
    f.inducedFundamentalGroupHom x
      ((CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel C)).map p) =
    ((CategoryTheory.Quotient.functor (Quiver.Path.pathOneHomRel D)).map (f.mapPath p)) :=
  sorry

/-- Proposition 3-3-1: if `f : C' → C` is a covering map of `1`-complexes and `v'` is a vertex of
`C'`, then the induced homomorphism
`f.inducedFundamentalGroupHom v' : π(C', v') →* π(C, f.toVertex v')`
is injective, hence a monomorphism of fundamental groups. -/
-- Proof sketch: a quiver covering gives unique lifting of reduced paths from the chosen base
-- vertex via `Prefunctor.IsCovering.pathStar_bijective`; applying this to a loop whose image is
-- trivial shows that the original loop class is already trivial.
theorem inducedFundamentalGroupHom_injective_of_isCovering
    (hf : f.toPrefunctor.IsCovering) (v' : C) :
    Function.Injective (f.inducedFundamentalGroupHom v') := sorry

end Hom

end OneComplex

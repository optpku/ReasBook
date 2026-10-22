/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

-- Layer triage:
-- `source-facing`: a `1`-complex with an explicit set of vertices, an explicit set of oriented
-- edges, and a fixed-point-free orientation-reversing involution on edges.
-- `core/canonical`: mathlib's `Quiver` is the owner abstraction for directed multigraph-style
-- edge data, and `Quiver.IsStronglyConnected` on the symmetrified quiver is the owner predicate
-- for zigzag-connectedness.
-- `bridge/view`: a `1`-complex canonically induces a quiver on its vertex type by taking arrows
-- from `v` to `w` to be edges whose initial and terminal vertices are `v` and `w`.
-- Domain sampling:
-- 1. `Quiver` is mathlib's owner abstraction for directed multigraph-style edge data.
-- 2. `Quiver.IsStronglyConnected (Quiver.Symmetrify C)` is the owner predicate for connectedness
--    by zigzags in a reversible graph.
-- 3. `Quiver.RootedConnected` is the owner class for based reachability, so no extra local
--    wrapper around it belongs in the public API.
-- 4. `Digraph` is too coarse here because it forgets the edge set and cannot distinguish
--    parallel edges.
-- 5. `SimpleGraph.Dart` models oriented edges in an undirected simple graph, but the present item
--    starts from a primitive edge set rather than deriving darts from an underlying simple graph.
-- Primitive vs. derived:
-- the primitive data are the vertex type, edge type, endpoint maps, and inverse-edge map; the
-- induced quiver structure and zigzag-connectedness properties are derived.

/-- Definition 3-2-1: A graph, or 1-complex, consists of a vertex set, an edge set, endpoint maps,
and a fixed-point-free involution on edges that reverses orientation. -/
structure OneComplex where
  /-- The vertices of the 1-complex. -/
  Vertex : Type u
  /-- The oriented edges of the 1-complex. -/
  Edge : Type v
  /-- The initial vertex of an oriented edge. -/
  initial : Edge → Vertex
  /-- The terminal vertex of an oriented edge. -/
  terminal : Edge → Vertex
  /-- The edge with the opposite orientation. -/
  edgeInv : Edge → Edge
  /-- Reversing orientation twice gives back the original edge. -/
  edgeInv_involutive : Function.Involutive edgeInv
  /-- No edge is equal to its oppositely oriented edge. -/
  edgeInv_ne (e : Edge) : edgeInv e ≠ e
  /-- The inverse edge starts at the terminal vertex of the original edge. -/
  initial_edgeInv (e : Edge) : initial (edgeInv e) = terminal e

namespace OneComplex

/-- A 1-complex is used through its vertex type. -/
instance : CoeSort OneComplex (Type u) where
  coe := OneComplex.Vertex

variable (C : OneComplex)

/-- The edge type of a 1-complex carries the notation `e⁻¹` for the oppositely oriented edge. -/
instance edgeInvInst : Inv C.Edge := ⟨C.edgeInv⟩

/-- The reverse edge in a 1-complex terminates at the initial vertex of the original edge. -/
theorem terminal_edgeInv (e : C.Edge) : C.terminal e⁻¹ = C.initial e := by
  change C.terminal (C.edgeInv e) = C.initial e
  simpa [C.edgeInv_involutive e] using (C.initial_edgeInv (C.edgeInv e)).symm

/-- A 1-complex determines a quiver on its vertex type by taking arrows to be edges with prescribed
initial and terminal vertices. -/
instance quiver : Quiver C.Vertex where
  Hom v w := { e : C.Edge // C.initial e = v ∧ C.terminal e = w }

/-- The quiver attached to a 1-complex has involutive edge reversal induced by the inverse-edge
operation on oriented edges. -/
instance hasInvolutiveReverse : Quiver.HasInvolutiveReverse C.Vertex where
  reverse' := fun {_ _} e ↦
    ⟨e.1⁻¹, ⟨(C.initial_edgeInv e.1).trans e.2.2, (C.terminal_edgeInv e.1).trans e.2.1⟩⟩
  inv' := fun _ ↦ Subtype.ext (C.edgeInv_involutive _)

/-- The equivalence relation identifying an oriented edge with its reverse. -/
def geometricEdgeSetoid (C : OneComplex.{u, v}) : Setoid C.Edge where
  r e f := e = f ∨ e = f⁻¹
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      exact Or.inl rfl
    · intro e f h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        calc
          f = (f⁻¹)⁻¹ := by exact (C.edgeInv_involutive f).symm
          _ = e⁻¹ := by exact (congrArg Inv.inv h).symm
    · intro e f g h₁ h₂
      rcases h₁ with rfl | h₁
      · simpa using h₂
      · rcases h₂ with h₂ | h₂
        · right
          simpa [h₂] using h₁
        · left
          calc
            e = f⁻¹ := h₁
            _ = (g⁻¹)⁻¹ := by rw [h₂]
            _ = g := by exact C.edgeInv_involutive g

/-- The geometric edges of a `1`-complex, i.e. oriented edges modulo reversal. -/
abbrev GeometricEdge (C : OneComplex.{u, v}) :=
  Quotient (geometricEdgeSetoid C)

end OneComplex

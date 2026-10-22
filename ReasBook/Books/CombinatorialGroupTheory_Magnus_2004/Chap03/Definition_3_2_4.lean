/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_3

universe u v w

open Quiver
open Quiver.Path

-- Layer triage:
-- `source-facing`: a 2-complex with its 1-skeleton, oriented faces, boundary cycles, inverse
-- faces, and the derived notions of a vertex lying on a face and of a boundary path.
-- `core/canonical`: `OneComplex` is the owner for the 1-skeleton, while
-- `Quiver.Path.CyclicPath`, `Quiver.Path.cyclicPath`, and the predicates from
-- Definition 3-2-3 are the owner API for cyclic boundary data in that skeleton.
-- `bridge/view`: the inverse-edge operation on a `OneComplex` induces the quiver-reversal
-- structure needed to talk about inverse loops and inverse boundary cycles in the skeleton.
-- Domain sampling:
-- 1. `OneComplex` is the project owner abstraction for the textbook 1-skeleton.
-- 2. `Quiver.Path.Loop` is the canonical owner for based loops in the induced quiver.
-- 3. `Quiver.Path.CyclicPath` is the project owner for the basepoint-free cyclic boundary object.
-- 4. `Quiver.Path.IsCyclicallyReducedCycle` is the owner predicate for cyclically reduced
--    boundary cycles, while `Quiver.Path.IsSimple` remains the owner predicate on representatives
--    used to define simple boundary.

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V]

/-- Reversing a cycle flips the adjacency relation. -/
theorem Cycle.chain_reverse_iff {α : Type*} {r : α → α → Prop} {c : Cycle α} :
    c.reverse.Chain r ↔ c.Chain (fun a b ↦ r b a) := by
  refine Quotient.inductionOn' c ?_
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton l a ih =>
      have hne : l ++ [a] ≠ [] := by simp
      simpa [Cycle.reverse_coe, Cycle.chain_coe_cons, Cycle.chain_ne_nil _ hne,
        List.getLast_append_singleton, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using
        (show (List.reverse (a :: l ++ [a])).IsChain r ↔
            (a :: l ++ [a]).IsChain (fun b c ↦ r c b) from List.isChain_reverse)

/-- The inverse of a cycle is obtained by reversing the cyclic order and inverting each edge. -/
def inverseCycle [Quiver.HasReverse V] (c : CyclicPath V) : CyclicPath V :=
  ⟨c.1.reverse.map Total.reverse, by
    rw [Cycle.chain_map, Cycle.chain_reverse_iff]
    exact c.2.imp fun e f h ↦ (Total.composable_reverse_reverse f e).2 h⟩

/-- Reversing a representative loop presents the inverse cyclic path. -/
theorem inverseCycle_cyclicPath [Quiver.HasReverse V] (p : Loop V) :
    inverseCycle (cyclicPath p) = cyclicPath ⟨p.1, p.2.reverse⟩ := by
  sorry

/-- A cycle is simple when it is represented by a simple loop. -/
def IsSimpleCycle (c : CyclicPath V) : Prop :=
  (c.1.map Total.left).Nodup ∧ (c.1.map Total.right).Nodup

/-- A cycle is simple exactly when some simple loop represents it. -/
theorem isSimpleCycle_iff (c : CyclicPath V) :
    IsSimpleCycle c ↔ ∃ p : Loop V, cyclicPath p = c ∧ IsSimple p.2 := by
  sorry

end Quiver.Path

/-- Definition 3-2-4: A 2-complex consists of a 1-skeleton, a set of oriented faces with a
fixed-point-free inverse-face involution, and a boundary map assigning to each face a cyclically
reduced cycle in the 1-skeleton such that the inverse face has the inverse boundary cycle. -/
structure TwoComplex where
  /-- The underlying 1-skeleton of the 2-complex. -/
  skeleton : OneComplex
  /-- The oriented faces of the 2-complex. -/
  Face : Type w
  /-- The boundary cycle attached to a face. -/
  boundary : Face → CyclicPath skeleton
  /-- Each face boundary is a cyclically reduced cycle in the 1-skeleton. -/
  boundary_cyclicallyReduced (D : Face) : IsCyclicallyReducedCycle (boundary D)
  /-- The inverse face with the opposite orientation. -/
  faceInv : Face → Face
  /-- Inverting the orientation of a face twice returns the original face. -/
  faceInv_involutive : Function.Involutive faceInv
  /-- A face is distinct from its inverse face. -/
  faceInv_ne (D : Face) : faceInv D ≠ D
  /-- The boundary of the inverse face is the inverse of the original boundary cycle. -/
  boundary_faceInv (D : Face) : boundary (faceInv D) = inverseCycle (boundary D)

namespace TwoComplex

/-- Faces in a 2-complex use `D⁻¹` for the oppositely oriented face. -/
instance faceInvInst (C : TwoComplex) : Inv C.Face := ⟨C.faceInv⟩

/-- Faces in a `2`-complex use the textbook notation `∂D` for the attached boundary cycle. -/
scoped notation:max "∂" D => TwoComplex.boundary _ D

/-- The equivalence relation identifying an oriented face with its opposite orientation. -/
def geometricFaceSetoid (C : TwoComplex) : Setoid C.Face where
  r D E := D = E ∨ D = E⁻¹
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro D
      exact Or.inl rfl
    · intro D E h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        calc
          E = (E⁻¹)⁻¹ := by exact (C.faceInv_involutive E).symm
          _ = D⁻¹ := by exact (congrArg Inv.inv h).symm
    · intro D E F h₁ h₂
      rcases h₁ with rfl | h₁
      · simpa using h₂
      · rcases h₂ with h₂ | h₂
        · right
          simpa [h₂] using h₁
        · left
          calc
            D = E⁻¹ := h₁
            _ = (F⁻¹)⁻¹ := by rw [h₂]
            _ = F := by exact C.faceInv_involutive F

/-- The geometric faces of a `2`-complex, i.e. oriented faces modulo reversal. -/
abbrev GeometricFace (C : TwoComplex) :=
  Quotient (geometricFaceSetoid C)

/-- A boundary path for a face at a vertex is a closed path based at that vertex whose cyclic
class is the boundary cycle of the face. -/
abbrev BoundaryPath (C : TwoComplex) (D : C.Face) (v : C.skeleton) : Type _ :=
  { p : Quiver.Path v v // cyclicPath ⟨v, p⟩ = ∂D }

/-- A vertex lies on a face when the face has a boundary path based at that vertex. -/
def VertexOnFace (C : TwoComplex) (v : C.skeleton) (D : C.Face) : Prop :=
  Nonempty (C.BoundaryPath D v)

/-- A vertex lies on a face exactly when there exists a boundary path for that face based at the
vertex. -/
-- Proof sketch: unfold `VertexOnFace` and `BoundaryPath`; the existential data is the same on
-- both sides.
theorem vertexOnFace_iff_nonempty_boundaryPath (C : TwoComplex) (v : C.skeleton) (D : C.Face) :
    C.VertexOnFace v D ↔ Nonempty (C.BoundaryPath D v) :=
  Iff.rfl

/-- A face has simple boundary when its boundary cycle is represented by a simple loop. -/
def HasSimpleBoundary (C : TwoComplex) (D : C.Face) : Prop :=
  IsSimpleCycle (∂D)

/-- A face has simple boundary exactly when some based boundary path of the face is simple. -/
-- Proof sketch: unfold `HasSimpleBoundary` and then unfold `IsSimpleCycle`.
theorem hasSimpleBoundary_iff (C : TwoComplex) (D : C.Face) :
    C.HasSimpleBoundary D ↔ ∃ v : C.skeleton, ∃ q : C.BoundaryPath D v, IsSimple q.1 :=
  sorry

/-- A face with simple boundary has at most one boundary path based at any fixed vertex. Together
with `vertexOnFace_iff_nonempty_boundaryPath`, this yields uniqueness at every vertex on the face.
-/
-- Proof sketch: choose a simple representative of the boundary cycle; simplicity implies that two
-- rotations starting at the same vertex coincide, so the corresponding boundary paths are equal.
theorem boundaryPath_subsingleton_of_simple_boundary (C : TwoComplex) (D : C.Face)
    (v : C.skeleton) (hD : C.HasSimpleBoundary D) : Subsingleton (C.BoundaryPath D v) := sorry

end TwoComplex

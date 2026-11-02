import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.MkIffOfInductiveProp

noncomputable section

open scoped BigOperators

universe u w

section Definition_4_3_1_extra_1

variable {V : Type u} {A : Type w}

section Flow

variable [Fintype A]

/-- The total flow on arcs entering the vertex `v`. -/
noncomputable def incoming_flow (head : A → V) (x : A → ℝ) (v : V) : ℝ :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq V := Classical.decEq V
  Finset.sum (Finset.univ.filter fun a ↦ head a = v) x

/-- The total flow on arcs leaving the vertex `v`. -/
noncomputable def outgoing_flow (tail : A → V) (x : A → ℝ) (v : V) : ℝ :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq V := Classical.decEq V
  Finset.sum (Finset.univ.filter fun a ↦ tail a = v) x

end Flow

section ArcInducedDigraph

/-- The finite digraph induced by the arc set `C`, with adjacency determined by the endpoint maps
`tail` and `head`. -/
def arc_induced_digraph (tail head : A → V) (C : Finset A) : Digraph V :=
  let _ : DecidableEq A := Classical.decEq A
  { Adj := fun u v ↦ ∃ a ∈ C, tail a = u ∧ head a = v }

end ArcInducedDigraph

section ArcInducedDigraphLemmas

theorem arc_induced_digraph_adj_iff
    (tail head : A → V) (C : Finset A) (u v : V) :
    (arc_induced_digraph tail head C).Adj u v ↔ ∃ a ∈ C, tail a = u ∧ head a = v := by
  rfl

end ArcInducedDigraphLemmas

section ArcCounts

/-- The number of arcs of `C` entering the vertex `v`. -/
noncomputable def incoming_arc_count (head : A → V) (C : Finset A) (v : V) : ℕ :=
  let _ : DecidableEq V := Classical.decEq V
  (C.filter fun a ↦ head a = v).card

/-- The number of arcs of `C` leaving the vertex `v`. -/
noncomputable def outgoing_arc_count (tail : A → V) (C : Finset A) (v : V) : ℕ :=
  let _ : DecidableEq V := Classical.decEq V
  (C.filter fun a ↦ tail a = v).card

end ArcCounts

section CircuitVertexSet

/-- The vertices incident to at least one arc of `C`. -/
def circuit_vertex_set (tail head : A → V) (C : Finset A) : Set V :=
  {v | ∃ a ∈ C, tail a = v ∨ head a = v}

theorem mem_circuit_vertex_set_iff (tail head : A → V) (C : Finset A) (v : V) :
    v ∈ circuit_vertex_set tail head C ↔ ∃ a ∈ C, tail a = v ∨ head a = v := by
  rfl

end CircuitVertexSet

section CircuitVertices

/-- The vertices incident to at least one arc of `C`. -/
noncomputable def circuit_vertices (tail head : A → V) (C : Finset A) : Finset V :=
  let _ : DecidableEq V := Classical.decEq V
  C.image tail ∪ C.image head

theorem mem_circuit_vertices_iff (tail head : A → V) (C : Finset A) (v : V) :
    v ∈ circuit_vertices tail head C ↔ v ∈ circuit_vertex_set tail head C := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_image.mp hv with ⟨a, haC, htail⟩
      exact ⟨a, haC, Or.inl htail⟩
    · rcases Finset.mem_image.mp hv with ⟨a, haC, hhead⟩
      exact ⟨a, haC, Or.inr hhead⟩
  · rintro ⟨a, haC, htail | hhead⟩
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨a, haC, htail⟩
    · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨a, haC, hhead⟩

end CircuitVertices

section CharacteristicVector

/-- The characteristic vector of the arc set `C`. -/
noncomputable def circuit_characteristic_vector (C : Finset A) : A → ℝ :=
  let _ : DecidableEq A := Classical.decEq A
  fun a ↦ if a ∈ C then 1 else 0

/-- The characteristic vector of `C` takes value `1` exactly on the arcs of `C`. -/
theorem circuit_characteristic_vector_apply [DecidableEq A] (C : Finset A) (a : A) :
    circuit_characteristic_vector C a = if a ∈ C then 1 else 0 := by
  classical
  by_cases ha : a ∈ C <;> simp [circuit_characteristic_vector, ha]

end CharacteristicVector

section Circulation

variable [Fintype A]

/-- Definition 4.3.1-extra-1 (1). A circulation on a finite digraph with arc set `A` and endpoint
maps `tail`, `head` is a nonnegative vector on the arcs whose incoming and outgoing flow agree at
every vertex. -/
@[mk_iff isCirculation_iff]
class IsCirculation (tail head : A → V) (x : A → ℝ) : Prop where
  /-- The incoming and outgoing flow agree at every vertex. -/
  flow_conservation (v : V) : incoming_flow head x v = outgoing_flow tail x v
  /-- The circulation is nonnegative on every arc. -/
  nonneg (a : A) : 0 ≤ x a

/-- Definition 4.3.1-extra-1 (2). The circulation cone of a finite digraph is the set of all
circulations on its arc set. -/
def circulation_cone (tail head : A → V) : Set (A → ℝ) :=
  {x | IsCirculation tail head x}

end Circulation

section CirculationLemmas

variable [Fintype A]

/-- Membership in the circulation cone is exactly the circulation condition. -/
theorem mem_circulation_cone_iff (tail head : A → V) (x : A → ℝ) :
    x ∈ circulation_cone tail head ↔ IsCirculation tail head x := by
  rfl

end CirculationLemmas

section Circuit

/-- Definition 4.3.1-extra-1 (3). A circuit is a finite set of arcs whose induced digraph is
connected on its incident vertices and for which, at every vertex, the number of entering arcs
equals the number of leaving arcs. -/
@[mk_iff isCircuit_iff]
class IsCircuit (tail head : A → V) (C : Finset A) : Prop where
  /-- The digraph induced by `C` is connected after forgetting orientations and restricting to the
  vertices incident to `C`. -/
  connected :
    ((arc_induced_digraph tail head C).toSimpleGraphInclusive.induce
      (circuit_vertex_set tail head C)).Connected
  /-- Every vertex has the same number of entering and leaving arcs of `C`. -/
  balanced (v : V) : incoming_arc_count head C v = outgoing_arc_count tail C v

end Circuit

section SimpleCircuit

/-- Definition 4.3.1-extra-1 (4). A simple circuit is a circuit such that every vertex of the
digraph induced by the chosen arc set has exactly one entering arc and exactly one leaving arc. -/
@[mk_iff isSimpleCircuit_iff]
class IsSimpleCircuit (tail head : A → V) (C : Finset A) : Prop where
  /-- A simple circuit uses at least one arc. -/
  nonempty : C.Nonempty
  /-- The digraph induced by `C` is connected after forgetting orientations and restricting to the
  vertices incident to `C`. -/
  connected :
    ((arc_induced_digraph tail head C).toSimpleGraphInclusive.induce
      (circuit_vertex_set tail head C)).Connected
  /-- Every vertex incident to `C` has exactly one entering arc and one leaving arc. -/
  one_in_one_out (v : V) (hv : v ∈ circuit_vertex_set tail head C) :
    incoming_arc_count head C v = 1 ∧ outgoing_arc_count tail C v = 1

theorem IsSimpleCircuit.balanced
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) (v : V) :
    incoming_arc_count head C v = outgoing_arc_count tail C v := by
  classical
  by_cases hv : v ∈ circuit_vertex_set tail head C
  · rcases hC.one_in_one_out v hv with ⟨hin, hout⟩
    rw [hin, hout]
  · have hin : incoming_arc_count head C v = 0 := by
      rw [incoming_arc_count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a haC hhead
      exact hv ⟨a, haC, Or.inr hhead⟩
    have hout : outgoing_arc_count tail C v = 0 := by
      rw [outgoing_arc_count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a haC htail
      exact hv ⟨a, haC, Or.inl htail⟩
    rw [hin, hout]

theorem IsSimpleCircuit.isCircuit
    {tail head : A → V} {C : Finset A} (hC : IsSimpleCircuit tail head C) :
    IsCircuit tail head C where
  connected := hC.connected
  balanced := hC.balanced

end SimpleCircuit

end Definition_4_3_1_extra_1

end

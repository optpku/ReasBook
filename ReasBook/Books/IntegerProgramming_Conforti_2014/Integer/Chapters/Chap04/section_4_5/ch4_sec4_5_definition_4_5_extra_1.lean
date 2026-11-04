/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19

-- Declarations for this item will be appended below by the statement pipeline.

-- This file uses the canonical `SimpleGraph.IsTree`,
-- `SimpleGraph.Subgraph.spanningCoe`, project owner `SimpleGraph.subgraphIncidenceVector`,
-- and `convexHull ℝ` APIs.

namespace SimpleGraph

namespace Subgraph

variable {V : Type*} {G : SimpleGraph V}

/-- Definition 4.5-extra-1 (1). A spanning tree of `G` is a subgraph `T` whose graph on the full
vertex set, namely `T.spanningCoe`, is a tree. -/
abbrev IsSpanningTree (T : G.Subgraph) : Prop :=
  T.spanningCoe.IsTree

/-- A subgraph is a spanning tree exactly when its spanning coercion is a tree. -/
theorem isSpanningTree_iff {T : G.Subgraph} :
    T.IsSpanningTree ↔ T.spanningCoe.IsTree :=
  Iff.rfl

/-- Definition 4.5-extra-1 (4). If `T` is a spanning tree of a finite graph, then the number of
edges of `T` is one less than the number of vertices. -/
theorem IsSpanningTree.card_edgeSet_add_one_eq_card_verts [Finite V] {T : G.Subgraph}
    (hT : T.IsSpanningTree) :
    Nat.card T.edgeSet + 1 = Nat.card V := by
  have hcard : T.spanningCoe.Connected ∧ Nat.card T.spanningCoe.edgeSet + 1 = Nat.card V :=
    SimpleGraph.isTree_iff_connected_and_card.mp hT
  simpa [Subgraph.edgeSet_spanningCoe] using hcard.2

/-- Helper for Definition 4.5-extra-1: forgetting the induced subgraph back to a simple graph
agrees with inducing the spanning coercion. -/
private theorem coe_induce_eq_spanningCoe_induce (T : G.Subgraph) (S : Set V) :
    (T.induce S).coe = T.spanningCoe.induce S := by
  -- Both graphs live on the subtype `S` and use the same adjacency relation from `T`.
  ext u v
  simp [Subgraph.spanningCoe]

private theorem card_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce [Finite V]
    (T : G.Subgraph) (S : Set V) :
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
  -- Count edges of the induced subgraph by first passing through its underlying simple graph.
  have hcoe_edge_card : Nat.card ((T.induce S).coe.edgeSet) = Nat.card ((T.induce S).edgeSet) := by
    rw [← (T.induce S).image_coe_edgeSet_coe]
    simpa using
      (Nat.card_image_of_injective
        (Function.Embedding.sym2Map (Function.Embedding.subtype (T.induce S).verts)).injective
        ((T.induce S).coe.edgeSet)).symm
  calc
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.induce S).coe.edgeSet) := hcoe_edge_card.symm
    _ = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
          rw [coe_induce_eq_spanningCoe_induce T S]
          rfl

/-- Helper for Definition 4.5-extra-1: a finite forest has at most one fewer edge than vertices. -/
private theorem isAcyclic_card_edgeSet_le_card_verts_sub_one
    {W : Type*} [Finite W] {H : SimpleGraph W} (hH : H.IsAcyclic) :
    Nat.card H.edgeSet ≤ Nat.card W - 1 := by
  classical
  by_cases hW : IsEmpty W
  · let _ : IsEmpty W := hW
    -- On the empty vertex type the edge set is empty, so the inequality is trivial.
    simp
  · let _ : Nonempty W := not_isEmpty_iff.mp hW
    -- Extend the forest to a spanning tree of the complete graph and compare edge counts.
    obtain ⟨K, hHK, -, hK⟩ :=
      SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
        (G := (⊤ : SimpleGraph W)) (H := H) SimpleGraph.connected_top le_top hH
    have h_edge_le : Nat.card H.edgeSet ≤ Nat.card K.edgeSet := by
      -- Monotonicity of the edge finset turns the subgraph inclusion into a cardinality bound.
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← H.edgeFinset_card,
        ← K.edgeFinset_card]
      exact Finset.card_mono (SimpleGraph.edgeFinset_mono hHK)
    have hKcard : Nat.card K.edgeSet + 1 = Nat.card W :=
      (SimpleGraph.isTree_iff_connected_and_card.mp hK).2
    omega

private theorem IsSpanningTree.card_edgeSet_spanningCoe_induce_le_card_verts_sub_one [Finite V]
    {T : G.Subgraph} (hT : T.IsSpanningTree) {S : Set V} :
    Nat.card ((T.spanningCoe.induce S).edgeSet) ≤ Nat.card S - 1 := by
  -- An induced subgraph of a tree is acyclic, so the generic forest bound applies on `S`.
  have hAcyclic : (T.spanningCoe.induce S).IsAcyclic := hT.isAcyclic.induce S
  simpa using isAcyclic_card_edgeSet_le_card_verts_sub_one (H := T.spanningCoe.induce S) hAcyclic

/-- Definition 4.5-extra-1 (5). If `T` is a spanning tree, then the number of edges of `T`
induced on any vertex subset `S` is at most `|S| - 1`. -/
theorem IsSpanningTree.card_edgeSet_induce_le_card_verts_sub_one [Finite V] {T : G.Subgraph}
    (hT : T.IsSpanningTree) {S : Set V} :
    Nat.card ((T.induce S).edgeSet) ≤ Nat.card S - 1 := by
  -- Transfer the subgraph edge count to the induced simple graph where acyclicity is available.
  rw [card_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce T S]
  exact hT.card_edgeSet_spanningCoe_induce_le_card_verts_sub_one

end Subgraph

variable {V : Type*} (G : SimpleGraph V)

/-- The incidence vectors of the spanning trees of `G`. -/
def spanningTreeVertices : Set (G.edgeSet → ℝ) :=
  {x | ∃ T : G.Subgraph, T.IsSpanningTree ∧ x = G.subgraphIncidenceVector ℝ T}

/-- A vector belongs to `spanningTreeVertices G` exactly when it is the incidence vector of a
spanning tree of `G`. -/
theorem mem_spanningTreeVertices_iff {x : G.edgeSet → ℝ} :
    x ∈ G.spanningTreeVertices ↔
      ∃ T : G.Subgraph, T.IsSpanningTree ∧ x = G.subgraphIncidenceVector ℝ T :=
  Iff.rfl

/-- Definition 4.5-extra-1 (2). The spanning tree polytope of `G` is the convex hull of the
incidence vectors of the spanning trees of `G`. -/
def spanningTreePolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ G.spanningTreeVertices

/-- The spanning tree polytope is the convex hull of the spanning-tree incidence vectors. -/
theorem spanningTreePolytope_eq_convexHull :
    G.spanningTreePolytope = convexHull ℝ G.spanningTreeVertices :=
  rfl

/-- Definition 4.5-extra-1 (3). A graph has a spanning tree if and only if it is connected. -/
theorem connected_iff_exists_spanningTree :
    G.Connected ↔ ∃ T : G.Subgraph, T.IsSpanningTree := by
  constructor
  · intro hG
    rcases hG.exists_isTree_le with ⟨T, hTG, hT⟩
    exact ⟨G.toSubgraph T hTG, by
      simpa [Subgraph.IsSpanningTree, SimpleGraph.toSubgraph, Subgraph.spanningCoe] using hT⟩
  · rintro ⟨T, hT⟩
    exact hT.connected.mono T.spanningCoe_le

end SimpleGraph

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Helper for Theorem 4.25: the `0,1` incidence vector of a subgraph in the ambient edge
coordinates of `G`. -/
def subgraphIncidenceVector (R : Type*) [Zero R] [One R] (H : G.Subgraph) : G.edgeSet → R :=
  fun e ↦ if e.1 ∈ H.edgeSet then 1 else 0

section Finite

variable [Fintype V]

/-- Helper for Theorem 4.25: the edge coordinates of the subgraph induced on `U`. -/
def inducedEdgeFinset (U : Set V) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ (e : Sym2 V) ∈ ((⊤ : G.Subgraph).induce U).edgeSet

/-- Helper for Theorem 4.25: membership in `G.inducedEdgeFinset U` is induced-edge membership. -/
theorem mem_inducedEdgeFinset_iff {U : Set V} {e : G.edgeSet} :
    e ∈ G.inducedEdgeFinset U ↔ (e : Sym2 V) ∈ ((⊤ : G.Subgraph).induce U).edgeSet := by
  simp [inducedEdgeFinset]

end Finite

namespace Subgraph

variable {G : SimpleGraph V}

/-- Helper for Theorem 4.25: a spanning tree of `G` is a subgraph whose spanning coercion is a
tree. -/
abbrev IsSpanningTree (T : G.Subgraph) : Prop :=
  T.spanningCoe.IsTree

/-- Helper for Theorem 4.25: a finite spanning tree has one fewer edge than vertices. -/
theorem IsSpanningTree.card_edgeSet_add_one_eq_card_verts [Finite V] {T : G.Subgraph}
    (hT : T.IsSpanningTree) :
    Nat.card T.edgeSet + 1 = Nat.card V := by
  have hcard : T.spanningCoe.Connected ∧ Nat.card T.spanningCoe.edgeSet + 1 = Nat.card V :=
    SimpleGraph.isTree_iff_connected_and_card.mp hT
  simpa [Subgraph.edgeSet_spanningCoe] using hcard.2

/-- Helper for Theorem 4.25: forgetting `T.induce S` to a simple graph agrees with inducing
`T.spanningCoe` on `S`. -/
private theorem coe_induce_eq_spanningCoe_induce (T : G.Subgraph) (S : Set V) :
    (T.induce S).coe = T.spanningCoe.induce S := by
  ext u v
  simp [Subgraph.spanningCoe]

/-- Helper for Theorem 4.25: inducing a subgraph or inducing its spanning coercion gives the same
edge cardinality. -/
private theorem card_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce [Finite V]
    (T : G.Subgraph) (S : Set V) :
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
  have hcoe_edge_card : Nat.card ((T.induce S).coe.edgeSet) = Nat.card ((T.induce S).edgeSet) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    calc
      ((T.induce S).coe.edgeSet).ncard =
          (Sym2.map ((↑) : (T.induce S).verts → V) '' (T.induce S).coe.edgeSet).ncard := by
            symm
            exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
      _ = ((T.induce S).edgeSet).ncard := by
            rw [(T.induce S).image_coe_edgeSet_coe]
  calc
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.induce S).coe.edgeSet) := hcoe_edge_card.symm
    _ = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
          rw [coe_induce_eq_spanningCoe_induce T S]
          rfl

/-- Helper for Theorem 4.25: a finite forest has at most one fewer edge than vertices. -/
private theorem isAcyclic_card_edgeSet_le_card_verts_sub_one
    {W : Type*} [Finite W] {H : SimpleGraph W} (hH : H.IsAcyclic) :
    Nat.card H.edgeSet ≤ Nat.card W - 1 := by
  classical
  by_cases hW : IsEmpty W
  · let _ : IsEmpty W := hW
    simp
  · let _ : Nonempty W := not_isEmpty_iff.mp hW
    obtain ⟨K, hHK, -, hK⟩ :=
      SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
        (G := (⊤ : SimpleGraph W)) (H := H) SimpleGraph.connected_top le_top hH
    have h_edge_le : Nat.card H.edgeSet ≤ Nat.card K.edgeSet := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← H.edgeFinset_card,
        ← K.edgeFinset_card]
      exact Finset.card_mono (SimpleGraph.edgeFinset_mono hHK)
    have hKcard : Nat.card K.edgeSet + 1 = Nat.card W :=
      (SimpleGraph.isTree_iff_connected_and_card.mp hK).2
    omega

/-- Helper for Theorem 4.25: the spanning-coercion induced subgraph of a spanning tree satisfies
the usual forest edge bound. -/
private theorem IsSpanningTree.card_edgeSet_spanningCoe_induce_le_card_verts_sub_one [Finite V]
    {T : G.Subgraph} (hT : T.IsSpanningTree) {S : Set V} :
    Nat.card ((T.spanningCoe.induce S).edgeSet) ≤ Nat.card S - 1 := by
  have hAcyclic : (T.spanningCoe.induce S).IsAcyclic := hT.isAcyclic.induce S
  simpa using isAcyclic_card_edgeSet_le_card_verts_sub_one (H := T.spanningCoe.induce S) hAcyclic

/-- Helper for Theorem 4.25: a spanning tree has at most `|S| - 1` edges on every induced vertex
subset `S`. -/
theorem IsSpanningTree.card_edgeSet_induce_le_card_verts_sub_one [Finite V] {T : G.Subgraph}
    (hT : T.IsSpanningTree) {S : Set V} :
    Nat.card ((T.induce S).edgeSet) ≤ Nat.card S - 1 := by
  rw [card_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce T S]
  exact hT.card_edgeSet_spanningCoe_induce_le_card_verts_sub_one

end Subgraph

/-- Helper for Theorem 4.25: the spanning-tree incidence vectors of `G`. -/
def spanningTreeVertices : Set (G.edgeSet → ℝ) :=
  {x | ∃ T : G.Subgraph, T.IsSpanningTree ∧ x = G.subgraphIncidenceVector ℝ T}

/-- Helper for Theorem 4.25: membership in `G.spanningTreeVertices` means being the incidence
vector of a spanning tree. -/
theorem mem_spanningTreeVertices_iff {x : G.edgeSet → ℝ} :
    x ∈ G.spanningTreeVertices ↔
      ∃ T : G.Subgraph, T.IsSpanningTree ∧ x = G.subgraphIncidenceVector ℝ T :=
  Iff.rfl

/-- Helper for Theorem 4.25: the spanning tree polytope is the convex hull of the spanning-tree
incidence vectors. -/
def spanningTreePolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ G.spanningTreeVertices

/-- Helper for Theorem 4.25: the spanning tree polytope unfolds to the corresponding convex hull. -/
theorem spanningTreePolytope_eq_convexHull :
    G.spanningTreePolytope = convexHull ℝ G.spanningTreeVertices :=
  rfl

/-- Helper for Theorem 4.25: a graph is connected exactly when it has a spanning tree. -/
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

section Theorem_4_25

variable {V : Type*}

/-- Helper for Theorem 4.25: reindex edge-coordinate vectors by the canonical enumeration of
`G.edgeSet`. -/
private noncomputable def graphEdgeCoordinates (G : SimpleGraph V) [Fintype V]
    (x : G.edgeSet → ℝ) : Fin (Nat.card G.edgeSet) → ℝ :=
  fun j ↦ x ((Finite.equivFin G.edgeSet).symm j)

/-- Helper for Theorem 4.25: the inverse coordinate reindexing sends `Fin`-indexed vectors back
to the original `G.edgeSet` coordinates. -/
private noncomputable abbrev graphEdgeCoordinateReindex (G : SimpleGraph V) [Fintype V] :
    (Fin (Nat.card G.edgeSet) → ℝ) ≃ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Finite.equivFin G.edgeSet)

/-- Helper for Theorem 4.25: evaluating the reindexed coordinate vector at an edge recovers the
matching finite coordinate. -/
@[simp] private theorem graphEdgeCoordinateReindex_apply (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ) (e : G.edgeSet) :
    graphEdgeCoordinateReindex G y e = y ((Finite.equivFin G.edgeSet) e) := by
  rw [graphEdgeCoordinateReindex, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- Helper for Theorem 4.25: reindexing native edge coordinates to `Fin` and back is the
identity. -/
@[simp] private theorem graphEdgeCoordinateReindex_graphEdgeCoordinates
    (G : SimpleGraph V) [Fintype V] (x : G.edgeSet → ℝ) :
    graphEdgeCoordinateReindex G (graphEdgeCoordinates G x) = x := by
  -- This is the `apply_symm_apply` identity for the canonical coordinate reindexing equivalence.
  change graphEdgeCoordinateReindex G ((graphEdgeCoordinateReindex G).symm x) = x
  exact LinearEquiv.apply_symm_apply (graphEdgeCoordinateReindex G) x

/-- Helper for Theorem 4.25: reindexing a `Fin`-indexed edge vector back to `G.edgeSet` and then
recovering finite coordinates is the identity. -/
@[simp] private theorem graphEdgeCoordinates_graphEdgeCoordinateReindex
    (G : SimpleGraph V) [Fintype V] (y : Fin (Nat.card G.edgeSet) → ℝ) :
    graphEdgeCoordinates G (graphEdgeCoordinateReindex G y) = y := by
  -- This is the `symm_apply_apply` identity for the same equivalence.
  change (graphEdgeCoordinateReindex G).symm (graphEdgeCoordinateReindex G y) = y
  exact LinearEquiv.symm_apply_apply (graphEdgeCoordinateReindex G) y

/-- Helper for Theorem 4.25: the nonempty proper subset rows in the textbook inequality system. -/
private abbrev spanningTreeConstraintSubsetRow (G : SimpleGraph V) [Fintype V] :=
  {S : Finset V // S.Nonempty ∧ S ≠ Finset.univ}

/-- Helper for Theorem 4.25: a finite row owner for all inequalities in the textbook spanning-tree
system. -/
private abbrev spanningTreeConstraintRow (G : SimpleGraph V) [Fintype V] :=
  spanningTreeConstraintSubsetRow G ⊕ Unit ⊕ Unit ⊕ G.edgeSet

/-- Helper for Theorem 4.25: the row encoding of the total-sum upper bound
`∑_e x_e ≤ |V| - 1`. -/
private abbrev spanningTreeConstraintTotalUpperRow (G : SimpleGraph V) [Fintype V] :
    spanningTreeConstraintRow G :=
  Sum.inr (Sum.inl ())

/-- Helper for Theorem 4.25: the row encoding of the total-sum lower bound
`-∑_e x_e ≤ -( |V| - 1 )`. -/
private abbrev spanningTreeConstraintTotalLowerRow (G : SimpleGraph V) [Fintype V] :
    spanningTreeConstraintRow G :=
  Sum.inr (Sum.inr (Sum.inl ()))

/-- Helper for Theorem 4.25: the row encoding of the coordinatewise nonnegativity inequality
`-x_e ≤ 0`. -/
private abbrev spanningTreeConstraintNonnegRow (G : SimpleGraph V) [Fintype V]
    (e : G.edgeSet) : spanningTreeConstraintRow G :=
  Sum.inr (Sum.inr (Sum.inr e))

/-- Helper for Theorem 4.25: the textbook inequality coefficients on native edge coordinates. -/
private noncomputable def spanningTreeConstraintMatrixNative
    (G : SimpleGraph V) [Fintype V] :
    Matrix (spanningTreeConstraintRow G) G.edgeSet ℚ := fun row e ↦
  match row with
  | Sum.inl S =>
      if e ∈ G.inducedEdgeFinset (S.1 : Set V) then 1 else 0
  | Sum.inr (Sum.inl _) =>
      1
  | Sum.inr (Sum.inr (Sum.inl _)) =>
      -1
  | Sum.inr (Sum.inr (Sum.inr e₀)) =>
      if e = e₀ then -1 else 0

/-- Helper for Theorem 4.25: the textbook right-hand side on native row indices. -/
private noncomputable def spanningTreeConstraintRhsNative
    (G : SimpleGraph V) [Fintype V] :
    spanningTreeConstraintRow G → ℚ := fun row ↦
  match row with
  | Sum.inl S =>
      S.1.card - 1
  | Sum.inr (Sum.inl _) =>
      Fintype.card V - 1
  | Sum.inr (Sum.inr (Sum.inl _)) =>
      -((Fintype.card V - 1 : ℤ) : ℚ)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      0

/-- Helper for Theorem 4.25: the Chapter 4.1 matrix owner obtained by reindexing the textbook
rows and edge coordinates by `Finite.equivFin`. -/
private noncomputable def spanningTreeConstraintPresentationMatrix
    (G : SimpleGraph V) [Fintype V] :
    Matrix (Fin (Nat.card (spanningTreeConstraintRow G))) (Fin (Nat.card G.edgeSet)) ℚ :=
  Matrix.reindex (Finite.equivFin (spanningTreeConstraintRow G)) (Finite.equivFin G.edgeSet)
    (spanningTreeConstraintMatrixNative G)

/-- Helper for Theorem 4.25: the reindexed right-hand side for the Chapter 4.1 matrix owner. -/
private noncomputable def spanningTreeConstraintPresentationRhs
    (G : SimpleGraph V) [Fintype V] :
    Fin (Nat.card (spanningTreeConstraintRow G)) → ℚ :=
  fun i ↦ spanningTreeConstraintRhsNative G ((Finite.equivFin (spanningTreeConstraintRow G)).symm i)

/-- Helper for Theorem 4.25: the explicit `Fin`-indexed rational polyhedron presenting the
textbook inequality system. -/
private noncomputable def spanningTreeConstraintPresentation
    (G : SimpleGraph V) [Fintype V] :
    Set (Fin (Nat.card G.edgeSet) → ℝ) :=
  rational_matrix_polyhedron
    (spanningTreeConstraintPresentationMatrix G)
    (spanningTreeConstraintPresentationRhs G)

/-- Helper for Theorem 4.25: evaluating the reindexed presentation matrix at owner indices
recovers the native coefficient. -/
@[simp] private theorem spanningTreeConstraintPresentationMatrix_apply
    (G : SimpleGraph V) [Fintype V]
    (i : Fin (Nat.card (spanningTreeConstraintRow G)))
    (j : Fin (Nat.card G.edgeSet)) :
    spanningTreeConstraintPresentationMatrix G i j =
      spanningTreeConstraintMatrixNative G
        ((Finite.equivFin (spanningTreeConstraintRow G)).symm i)
        ((Finite.equivFin G.edgeSet).symm j) := by
  -- Unfolding the owner reindexing once gives the stable native row and column.
  rw [spanningTreeConstraintPresentationMatrix, Matrix.reindex_apply]
  rfl

/-- Helper for Theorem 4.25: evaluating the reindexed right-hand side at an owner index recovers
the native right-hand side. -/
@[simp] private theorem spanningTreeConstraintPresentationRhs_apply
    (G : SimpleGraph V) [Fintype V]
    (i : Fin (Nat.card (spanningTreeConstraintRow G))) :
    spanningTreeConstraintPresentationRhs G i =
      spanningTreeConstraintRhsNative G
        ((Finite.equivFin (spanningTreeConstraintRow G)).symm i) := by
  -- The reindexed right-hand side is defined by transporting the native row owner.
  rw [spanningTreeConstraintPresentationRhs]

/-- The inequality system from Theorem 4.25 for the spanning tree polytope of `G`. -/
def spanningTreeConstraintSet (G : SimpleGraph V) [Fintype V] : Set (G.edgeSet → ℝ) :=
  {x | (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) ≤ (S.card - 1 : ℝ)) ∧
    Finset.sum Finset.univ (fun e ↦ x e) = (Fintype.card V - 1 : ℝ) ∧
    ∀ e, 0 ≤ x e}

/-- A point satisfies `spanningTreeConstraintSet G` exactly when it satisfies the edge-subset
inequalities, the total-edge equality, and the nonnegativity inequalities. -/
theorem mem_spanningTreeConstraintSet_iff {G : SimpleGraph V} [Fintype V] {x : G.edgeSet → ℝ} :
    x ∈ spanningTreeConstraintSet G ↔
      (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
        Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) ≤ (S.card - 1 : ℝ)) ∧
      Finset.sum Finset.univ (fun e ↦ x e) = (Fintype.card V - 1 : ℝ) ∧
      ∀ e, 0 ≤ x e := by
  -- This is just the unfolded definition of `spanningTreeConstraintSet`.
  rfl

/-- Helper for Theorem 4.25: a disconnected graph has no spanning-tree vertices, so its spanning
tree polytope is empty. -/
lemma spanningTreePolytope_eq_empty_of_not_connected (G : SimpleGraph V) (hG : ¬ G.Connected) :
    G.spanningTreePolytope = ∅ := by
  rw [G.spanningTreePolytope_eq_convexHull]
  suffices hVertices : G.spanningTreeVertices = (∅ : Set (G.edgeSet → ℝ)) by
    rw [hVertices, convexHull_empty]
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  rcases (G.mem_spanningTreeVertices_iff.mp hx) with ⟨T, hT, rfl⟩
  exact hG ((G.connected_iff_exists_spanningTree).2 ⟨T, hT⟩)

/-- Helper for Theorem 4.25: the edges of a subgraph `H` correspond bijectively to the edges of
`G` that lie in `H`. -/
lemma card_edgeSet_subtype_eq (G : SimpleGraph V) [Fintype V] (H : G.Subgraph) :
    Fintype.card {e : G.edgeSet // e.1 ∈ H.edgeSet} = Fintype.card H.edgeSet := by
  classical
  refine Fintype.card_congr ?_
  refine
    { toFun := fun e ↦ ⟨e.1.1, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, H.edgeSet_subset e.2⟩, e.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    cases e
    rfl
  · intro e
    cases e
    rfl

/-- Helper for Theorem 4.25: summing the indicator of a subgraph edge set over all edges of `G`
recovers the number of edges of the subgraph. -/
lemma sum_edge_indicator_eq_card_edgeSet (G : SimpleGraph V) [Fintype V] (H : G.Subgraph) :
    (∑ e : G.edgeSet, if e.1 ∈ H.edgeSet then (1 : ℝ) else 0) = Fintype.card H.edgeSet := by
  classical
  calc
    (∑ e : G.edgeSet, if e.1 ∈ H.edgeSet then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet).card : ℝ) := by
      simpa using
        (Finset.sum_boole (fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet) Finset.univ : _)
    _ = (Fintype.card {e : G.edgeSet // e.1 ∈ H.edgeSet} : ℝ) := by
      exact congrArg (fun n : ℕ ↦ (n : ℝ))
        ((Fintype.card_of_subtype
          (Finset.univ.filter fun e : G.edgeSet ↦ e.1 ∈ H.edgeSet)
          (by
            intro e
            simp)).symm)
    _ = Fintype.card H.edgeSet := by
      exact congrArg (fun n : ℕ ↦ (n : ℝ)) (card_edgeSet_subtype_eq G H)

/-- Helper for Theorem 4.25: the edge set of `T.induce S` is exactly the intersection of the
edges of `T` with the edges whose endpoints both lie in `S`. -/
lemma induce_edgeSet_eq_inter_induce_top (G : SimpleGraph V) (T : G.Subgraph) (S : Set V) :
    (T.induce S).edgeSet = T.edgeSet ∩ ((⊤ : G.Subgraph).induce S).edgeSet := by
  -- On each edge, membership means being an edge of `T` whose endpoints both lie in `S`.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.Subgraph.mem_edgeSet, Set.mem_inter_iff, SimpleGraph.Subgraph.induce]
      constructor
      · rintro ⟨hu, hv, huv⟩
        exact ⟨huv, hu, hv, T.adj_sub huv⟩
      · rintro ⟨huv, hu, hv, _⟩
        exact ⟨hu, hv, huv⟩

/-- Helper for Theorem 4.25: the subset-edge sum of a spanning-tree incidence vector is exactly
the number of native induced edges in `T.induce S`. -/
lemma induced_incidence_sum_eq_card_induced_edges (G : SimpleGraph V) [Fintype V]
    (T : G.Subgraph) (S : Finset V) :
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e) =
      Fintype.card ((T.induce (S : Set V)).edgeSet) := by
  classical
  calc
    Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e)
        = ∑ e : G.edgeSet,
            if e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet then
              G.subgraphIncidenceVector ℝ T e
            else 0 := by
              rw [SimpleGraph.inducedEdgeFinset, Finset.sum_filter]
    _ = ∑ e : G.edgeSet, if e.1 ∈ (T.induce (S : Set V)).edgeSet then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have hmem :
              e.1 ∈ (T.induce (S : Set V)).edgeSet ↔
                e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet ∧ e.1 ∈ T.edgeSet := by
            rw [induce_edgeSet_eq_inter_induce_top G T (S : Set V)]
            simpa [and_comm]
          by_cases hS : e.1 ∈ ((⊤ : G.Subgraph).induce (S : Set V)).edgeSet
          · by_cases hT : e.1 ∈ T.edgeSet
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
            · simp [SimpleGraph.subgraphIncidenceVector, hS, hT, hmem]
          · simp [hS, hmem, SimpleGraph.subgraphIncidenceVector]
    _ = Fintype.card ((T.induce (S : Set V)).edgeSet) := by
          simpa using sum_edge_indicator_eq_card_edgeSet G (T.induce (S : Set V))

/-- Helper for Theorem 4.25: the incidence vector of a subgraph sums to its edge count. -/
lemma sum_subgraphIncidenceVector_eq_card_edgeSet (G : SimpleGraph V) [Fintype V]
    (T : G.Subgraph) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ T e) = Fintype.card T.edgeSet := by
  -- Expand the indicator definition and use the generic edge-counting lemma.
  simpa [SimpleGraph.subgraphIncidenceVector] using
    sum_edge_indicator_eq_card_edgeSet G T

/-- Helper for Theorem 4.25: a spanning-tree incidence vector has the correct total edge sum. -/
lemma subgraphIncidenceVector_total_sum_of_spanningTree (G : SimpleGraph V) [Fintype V]
    {T : G.Subgraph}
    (hT : T.IsSpanningTree) :
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ T e) = (Fintype.card V - 1 : ℝ) := by
  -- Convert the incidence-vector sum into the edge cardinality and then use the tree count.
  have hcard :
      Fintype.card T.edgeSet + 1 = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using hT.card_edgeSet_add_one_eq_card_verts
  have hedgeCount : Fintype.card T.edgeSet = Fintype.card V - 1 := by
    omega
  have hVpos : 1 ≤ Fintype.card V := by
    omega
  calc
    (∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ T e) = Fintype.card T.edgeSet := by
      simpa using sum_subgraphIncidenceVector_eq_card_edgeSet G T
    _ = (Fintype.card V : ℝ) - 1 := by
      exact_mod_cast hedgeCount
    _ = (Fintype.card V - 1 : ℝ) := by
      rfl

/-- Helper for Theorem 4.25: every spanning-tree incidence vector is coordinatewise nonnegative. -/
lemma subgraphIncidenceVector_nonneg (G : SimpleGraph V) (T : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ T e := by
  -- Each coordinate is either `0` or `1`.
  intro e
  by_cases h : e.1 ∈ T.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Theorem 4.25: if `C` is a connected component, then an edge of `G` belongs to the
induced subgraph on `C.supp` exactly when it does not belong to the induced subgraph on the
complement. -/
lemma component_induced_compl_mem_iff_not_mem (G : SimpleGraph V) [Fintype V]
    (C : G.ConnectedComponent) {e : G.edgeSet} :
    e ∈ G.inducedEdgeFinset (((Finset.univ \ C.supp.toFinset : Finset V) : Set V)) ↔
      e ∉ G.inducedEdgeFinset (C.supp.toFinset : Set V) := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      have hadj : G.Adj u v := by
        simpa using he
      have hiff := C.mem_supp_congr_adj hadj
      by_cases hu : u ∈ C.supp
      · have hv : v ∈ C.supp := hiff.mp hu
        simp [SimpleGraph.inducedEdgeFinset, hu, hv, hadj]
      · have hv : v ∉ C.supp := by
          intro hv
          exact hu (hiff.mpr hv)
        simp [SimpleGraph.inducedEdgeFinset, hu, hv, hadj]

/-- Helper for Theorem 4.25: a disconnected graph makes the inequality system infeasible. -/
lemma spanningTreeConstraintSet_eq_empty_of_not_connected (G : SimpleGraph V) [Fintype V]
    (hG : ¬ G.Connected) :
    spanningTreeConstraintSet G = ∅ := by
  classical
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨hx_subset, hx_total, hx_nonneg⟩
  by_cases hV : IsEmpty V
  · -- If there are no vertices, the total-edge equation asks for `0 = -1`.
    have hsum_zero : Finset.sum Finset.univ (fun e : G.edgeSet ↦ x e) = 0 := by
      simp
    have : (0 : ℝ) = (Fintype.card V - 1 : ℝ) := by
      rw [← hsum_zero]
      exact hx_total
    have : (0 : ℝ) = (-1 : ℝ) := by
      simpa [Fintype.card_ofIsEmpty] using this
    norm_num at this
  · -- Choose a vertex and a second vertex outside its connected component.
    have hV_nonempty : Nonempty V := not_isEmpty_iff.mp hV
    let v : V := Classical.choice hV_nonempty
    have hnot_all_reachable : ¬ ∀ w, G.Reachable v w := by
      intro hall
      apply hG
      exact (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨v, hall⟩
    rcases not_forall.mp hnot_all_reachable with ⟨w, hw⟩
    let C : G.ConnectedComponent := G.connectedComponentMk v
    let S : Finset V := C.supp.toFinset
    have hvS : v ∈ S := by
      simp [S, C]
    have hw_not_S : w ∉ S := by
      intro hwS
      have hEq : G.connectedComponentMk v = G.connectedComponentMk w := by
        simpa [C] using ((SimpleGraph.ConnectedComponent.mem_supp_iff C w).mp
          (by simpa [S] using hwS)).symm
      exact hw (SimpleGraph.ConnectedComponent.exact hEq)
    have hS_nonempty : S.Nonempty := ⟨v, hvS⟩
    have hS_ne_univ : S ≠ Finset.univ := by
      intro hEq
      exact hw_not_S (hEq.symm ▸ Finset.mem_univ _)
    have hSc_nonempty : (Finset.univ \ S).Nonempty := ⟨w, by simp [hw_not_S]⟩
    have hSc_ne_univ : Finset.univ \ S ≠ Finset.univ := by
      intro hEq
      have : v ∈ Finset.univ \ S := hEq.symm ▸ Finset.mem_univ v
      simp [hvS] at this
    have hsplit :
        Finset.sum Finset.univ (fun e : G.edgeSet ↦ x e) =
          Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) +
            Finset.sum (G.inducedEdgeFinset (((Finset.univ \ S : Finset V) : Set V))) (fun e ↦ x e) := by
      -- Split the total sum into the two component-induced edge sets.
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun e : G.edgeSet ↦ e ∈ G.inducedEdgeFinset (S : Set V))]
      have hfilter :
          Finset.univ.filter (fun e : G.edgeSet ↦ e ∉ G.inducedEdgeFinset (S : Set V)) =
            G.inducedEdgeFinset (((Finset.univ \ S : Finset V) : Set V)) := by
        ext e
        have hcompl :
            e ∉ G.inducedEdgeFinset (S : Set V) ↔
              e ∈ G.inducedEdgeFinset (((Finset.univ \ S : Finset V) : Set V)) := by
          simpa [S] using (component_induced_compl_mem_iff_not_mem G C).symm
        simpa using hcompl
      rw [hfilter]
      simp
    have hS_bound := hx_subset S hS_nonempty hS_ne_univ
    have hSc_bound := hx_subset (Finset.univ \ S) hSc_nonempty hSc_ne_univ
    have htotal_le :
        Finset.sum Finset.univ (fun e : G.edgeSet ↦ x e) ≤ (Fintype.card V - 2 : ℝ) := by
      calc
        Finset.sum Finset.univ (fun e : G.edgeSet ↦ x e)
            = Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) +
                Finset.sum (G.inducedEdgeFinset (((Finset.univ \ S : Finset V) : Set V))) (fun e ↦ x e) := by
                  exact hsplit
        _ ≤ (S.card - 1 : ℝ) + (((Finset.univ \ S).card : ℕ) - 1 : ℝ) := by
              gcongr
        _ = (Fintype.card V - 2 : ℝ) := by
              have hcard :
                  (Finset.univ \ S).card + S.card = Fintype.card V := by
                simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
              have hcard_real :
                  ((Finset.univ \ S).card : ℝ) + S.card = Fintype.card V := by
                exact_mod_cast hcard
              nlinarith
    have : ¬ ((Fintype.card V - 1 : ℝ) ≤ (Fintype.card V - 2 : ℝ)) := by
      linarith
    exact this (by simpa [hx_total] using htotal_le)

/-- Helper for Theorem 4.25: the defining inequalities of `spanningTreeConstraintSet G` are
preserved under convex combinations. -/
lemma convex_spanningTreeConstraintSet (G : SimpleGraph V) [Fintype V] :
    Convex ℝ (spanningTreeConstraintSet G) := by
  intro x hx y hy a b ha hb hab
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨hx_subset, hx_total, hx_nonneg⟩
  rcases (mem_spanningTreeConstraintSet_iff).1 hy with ⟨hy_subset, hy_total, hy_nonneg⟩
  refine (mem_spanningTreeConstraintSet_iff).2 ?_
  constructor
  · intro S hS hSuniv
    have hxS := hx_subset S hS hSuniv
    have hyS := hy_subset S hS hSuniv
    have hcoeff :
        a * (S.card - 1 : ℝ) + b * (S.card - 1 : ℝ) = (S.card - 1 : ℝ) := by
      nlinarith [hab]
    calc
      Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ (a • x + b • y) e)
          = a * Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) +
              b * Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ y e) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ a * (S.card - 1 : ℝ) + b * (S.card - 1 : ℝ) := by
            gcongr
      _ = (S.card - 1 : ℝ) := by
            exact hcoeff
  constructor
  · have hcoeff :
        a * (Fintype.card V - 1 : ℝ) + b * (Fintype.card V - 1 : ℝ) =
          (Fintype.card V - 1 : ℝ) := by
      nlinarith [hab]
    calc
      Finset.sum Finset.univ (fun e ↦ (a • x + b • y) e)
          = a * Finset.sum Finset.univ (fun e ↦ x e) +
              b * Finset.sum Finset.univ (fun e ↦ y e) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.mul_sum, Finset.sum_add_distrib]
      _ = a * (Fintype.card V - 1 : ℝ) + b * (Fintype.card V - 1 : ℝ) := by
            rw [hx_total, hy_total]
      _ = (Fintype.card V - 1 : ℝ) := by
            exact hcoeff
  · intro e
    -- Coordinatewise nonnegativity is preserved by nonnegative affine combinations.
    exact add_nonneg (mul_nonneg ha (hx_nonneg e)) (mul_nonneg hb (hy_nonneg e))

/-- Helper for Theorem 4.25: the incidence vector of a spanning tree satisfies all inequalities
from the theorem statement. -/
lemma subgraphIncidenceVector_mem_spanningTreeConstraintSet (G : SimpleGraph V) [Fintype V]
    {T : G.Subgraph} (hT : T.IsSpanningTree) :
    G.subgraphIncidenceVector ℝ T ∈ spanningTreeConstraintSet G := by
  refine (mem_spanningTreeConstraintSet_iff).2 ?_
  constructor
  · intro S hS hSuniv
    -- Rewrite the subset inequality as a native induced-edge count and then apply the tree bound.
    calc
      Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ G.subgraphIncidenceVector ℝ T e)
          = Fintype.card ((T.induce (S : Set V)).edgeSet) := by
            simpa using induced_incidence_sum_eq_card_induced_edges G T S
      _ ≤ (S.card - 1 : ℝ) := by
            have hnat' :
                Nat.card ((T.induce (S : Set V)).edgeSet) ≤ Nat.card (S : Set V) - 1 := by
              exact hT.card_edgeSet_induce_le_card_verts_sub_one
            have hnat :
                Fintype.card ((T.induce (S : Set V)).edgeSet) ≤ S.card - 1 := by
              simpa [Nat.card_eq_card_toFinset (S : Set V), Nat.card_eq_fintype_card] using hnat'
            have hnat_add : Fintype.card ((T.induce (S : Set V)).edgeSet) + 1 ≤ S.card := by
              have hlt :
                  Fintype.card ((T.induce (S : Set V)).edgeSet) < S.card := by
                exact lt_of_le_of_lt hnat (Nat.sub_lt (Finset.card_pos.mpr hS) (by decide))
              exact Nat.succ_le_of_lt hlt
            have hreal_add : (Fintype.card ((T.induce (S : Set V)).edgeSet) : ℝ) + 1 ≤ S.card := by
              exact_mod_cast hnat_add
            nlinarith
  constructor
  · -- The total-edge equation is the standard edge count for a spanning tree.
    simpa using subgraphIncidenceVector_total_sum_of_spanningTree G hT
  · -- Each coordinate is an indicator value, hence nonnegative.
    exact subgraphIncidenceVector_nonneg G T

/-- Helper for Theorem 4.25: the spanning-tree polytope is contained in the inequality system. -/
lemma spanningTreePolytope_subset_spanningTreeConstraintSet (G : SimpleGraph V) [Fintype V] :
    G.spanningTreePolytope ⊆ spanningTreeConstraintSet G := by
  rw [G.spanningTreePolytope_eq_convexHull]
  refine convexHull_min ?_ (convex_spanningTreeConstraintSet G)
  intro x hx
  rcases G.mem_spanningTreeVertices_iff.mp hx with ⟨T, hT, rfl⟩
  exact subgraphIncidenceVector_mem_spanningTreeConstraintSet G hT

/-- Helper for Theorem 4.25: evaluating any reindexed presentation row is the corresponding native
edge-coordinate sum. -/
private theorem spanningTreeConstraintPresentation_rowEval_native
    (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ)
    (row : spanningTreeConstraintRow G) :
    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Finite.equivFin (spanningTreeConstraintRow G)) row) =
      ∑ e : G.edgeSet,
        ((spanningTreeConstraintMatrixNative G row e : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e := by
  -- Evaluate the chosen reindexed row and then reindex the ambient `Fin`-sum back to `G.edgeSet`.
  rw [Matrix.mulVec, dotProduct]
  symm
  exact Fintype.sum_equiv (Finite.equivFin G.edgeSet) _ _ fun e ↦ by
    have hcoeff :
        ((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ))
            ((Finite.equivFin (spanningTreeConstraintRow G)) row)
            ((Finite.equivFin G.edgeSet) e) =
          ((spanningTreeConstraintMatrixNative G row e : ℚ) : ℝ) := by
      change
        ((spanningTreeConstraintPresentationMatrix G
            ((Finite.equivFin (spanningTreeConstraintRow G)) row)
            ((Finite.equivFin G.edgeSet) e) : ℚ) : ℝ) =
          ((spanningTreeConstraintMatrixNative G row e : ℚ) : ℝ)
      rw [spanningTreeConstraintPresentationMatrix_apply]
      rw [Equiv.symm_apply_apply (Finite.equivFin (spanningTreeConstraintRow G)) row,
        Equiv.symm_apply_apply (Finite.equivFin G.edgeSet) e]
    rw [hcoeff, graphEdgeCoordinateReindex_apply]

/-- Helper for Theorem 4.25: the subset-row evaluation in the reindexed matrix owner is exactly
the original induced-edge sum. -/
private theorem spanningTreeConstraint_subset_row_eval
    (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ)
    (S : spanningTreeConstraintSubsetRow G) :
    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Finite.equivFin (spanningTreeConstraintRow G)) (Sum.inl S)) =
      Finset.sum (G.inducedEdgeFinset (S.1 : Set V)) (fun e ↦ graphEdgeCoordinateReindex G y e) := by
  -- Specializing the generic row evaluator turns the row into an indicator-weighted edge sum.
  rw [spanningTreeConstraintPresentation_rowEval_native]
  -- The indicator coefficients collapse the ambient sum back to the induced-edge finset.
  calc
    ∑ e : G.edgeSet,
        ((spanningTreeConstraintMatrixNative G (Sum.inl S) e : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e =
      ∑ e : G.edgeSet,
        if e ∈ G.inducedEdgeFinset (S.1 : Set V) then graphEdgeCoordinateReindex G y e else 0 := by
          change
            Finset.sum Finset.univ
              (fun e : G.edgeSet ↦
                ((spanningTreeConstraintMatrixNative G (Sum.inl S) e : ℚ) : ℝ) *
                  graphEdgeCoordinateReindex G y e) =
              Finset.sum Finset.univ
                (fun e : G.edgeSet ↦
                  if e ∈ G.inducedEdgeFinset (S.1 : Set V) then graphEdgeCoordinateReindex G y e else 0)
          refine Finset.sum_congr rfl ?_
          intro e he_univ
          by_cases he : e ∈ G.inducedEdgeFinset (S.1 : Set V)
          · simp [spanningTreeConstraintMatrixNative, he]
          · simp [spanningTreeConstraintMatrixNative, he]
    _ = Finset.sum (G.inducedEdgeFinset (S.1 : Set V)) (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← Finset.sum_filter]
          simpa

/-- Helper for Theorem 4.25: the total-sum upper-bound row evaluates to the full edge sum. -/
private theorem spanningTreeConstraint_total_upper_row_eval
    (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ) :
    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintTotalUpperRow G)) =
      ∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e := by
  -- The total-upper row has coefficient `1` on every edge.
  simpa [spanningTreeConstraintTotalUpperRow, spanningTreeConstraintMatrixNative] using
    spanningTreeConstraintPresentation_rowEval_native
      G y (spanningTreeConstraintTotalUpperRow G)

/-- Helper for Theorem 4.25: the total-sum lower-bound row evaluates to the negative full edge
sum. -/
private theorem spanningTreeConstraint_total_lower_row_eval
    (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ) :
    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintTotalLowerRow G)) =
      -∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e := by
  -- The total-lower row is the same sum with coefficient `-1` on every edge.
  simpa [spanningTreeConstraintTotalLowerRow, spanningTreeConstraintMatrixNative] using
    spanningTreeConstraintPresentation_rowEval_native
      G y (spanningTreeConstraintTotalLowerRow G)

/-- Helper for Theorem 4.25: the nonnegativity row for `e` evaluates to `-x_e`. -/
private theorem spanningTreeConstraint_nonneg_row_eval
    (G : SimpleGraph V) [Fintype V]
    (y : Fin (Nat.card G.edgeSet) → ℝ)
    (e : G.edgeSet) :
    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
        ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintNonnegRow G e)) =
      -graphEdgeCoordinateReindex G y e := by
  -- The nonnegativity row has a single `-1` coefficient at the chosen edge.
  rw [spanningTreeConstraintPresentation_rowEval_native]
  calc
    ∑ e' : G.edgeSet,
        ((spanningTreeConstraintMatrixNative G (spanningTreeConstraintNonnegRow G e) e' : ℚ) : ℝ) *
          graphEdgeCoordinateReindex G y e' =
      ∑ e' : G.edgeSet, if e' = e then -graphEdgeCoordinateReindex G y e' else 0 := by
          change
            Finset.sum Finset.univ
              (fun e' : G.edgeSet ↦
                ((spanningTreeConstraintMatrixNative G (spanningTreeConstraintNonnegRow G e) e' : ℚ) : ℝ) *
                  graphEdgeCoordinateReindex G y e') =
              Finset.sum Finset.univ
                (fun e' : G.edgeSet ↦ if e' = e then -graphEdgeCoordinateReindex G y e' else 0)
          refine Finset.sum_congr rfl ?_
          intro e' he_univ
          by_cases he' : e' = e
          · simp [spanningTreeConstraintNonnegRow, spanningTreeConstraintMatrixNative, he']
          · simp [spanningTreeConstraintNonnegRow, spanningTreeConstraintMatrixNative, he']
    _ = -graphEdgeCoordinateReindex G y e := by
          rw [Fintype.sum_eq_single e]
          · simp
          · intro e' he'
            simp [he']

/-- Helper for Theorem 4.25: membership in the explicit Chapter 4.1 presentation is equivalent to
membership in the original textbook inequality system after reindexing coordinates. -/
private theorem graphEdgeCoordinateReindex_mem_spanningTreeConstraintPresentation_iff
    (G : SimpleGraph V) [Fintype V]
    {y : Fin (Nat.card G.edgeSet) → ℝ} :
    graphEdgeCoordinateReindex G y ∈ spanningTreeConstraintSet G ↔
      y ∈ spanningTreeConstraintPresentation G := by
  constructor
  · intro hy
    rcases (mem_spanningTreeConstraintSet_iff).1 hy with ⟨hy_subset, hy_total, hy_nonneg⟩
    rw [spanningTreeConstraintPresentation, mem_rational_matrix_polyhedron]
    intro i
    let row : spanningTreeConstraintRow G :=
      (Finite.equivFin (spanningTreeConstraintRow G)).symm i
    match hrow : row with
    | Sum.inl S =>
        have hrow' :
            (Finite.equivFin (spanningTreeConstraintRow G)).symm i = Sum.inl S := by
          simpa [row] using hrow
        have hi :
            (Finite.equivFin (spanningTreeConstraintRow G)) (Sum.inl S) = i := by
          exact
            (congrArg (Finite.equivFin (spanningTreeConstraintRow G)) hrow').symm.trans
              (Equiv.apply_symm_apply (Finite.equivFin (spanningTreeConstraintRow G)) i)
        have hrow :
            (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
              Finset.sum (G.inducedEdgeFinset (S.1 : Set V))
                (fun e ↦ graphEdgeCoordinateReindex G y e) := by
          rw [← hi]
          exact spanningTreeConstraint_subset_row_eval G y S
        have hrhs :
            ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ) =
              (S.1.card - 1 : ℝ) := by
          rw [← hi]
          simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
        rw [hrow]
        change
          Finset.sum (G.inducedEdgeFinset (S.1 : Set V)) (fun e ↦ graphEdgeCoordinateReindex G y e) ≤
            ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ)
        rw [hrhs]
        exact hy_subset S.1 S.2.1 S.2.2
    | Sum.inr (Sum.inl _) =>
            have hrow' :
                (Finite.equivFin (spanningTreeConstraintRow G)).symm i =
                  spanningTreeConstraintTotalUpperRow G := by
              simpa [row, spanningTreeConstraintTotalUpperRow] using hrow
            have hi :
                (Finite.equivFin (spanningTreeConstraintRow G))
                    (spanningTreeConstraintTotalUpperRow G) = i := by
              exact
                (congrArg (Finite.equivFin (spanningTreeConstraintRow G)) hrow').symm.trans
                  (Equiv.apply_symm_apply (Finite.equivFin (spanningTreeConstraintRow G)) i)
            have hrow :
                (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
                  ∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e := by
              rw [← hi]
              exact spanningTreeConstraint_total_upper_row_eval G y
            have hrhs :
                ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ) =
                  (Fintype.card V - 1 : ℝ) := by
              rw [← hi]
              simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
            rw [hrow]
            change (∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e) ≤
              ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ)
            rw [hrhs]
            linarith [hy_total]
    | Sum.inr (Sum.inr (Sum.inl _)) =>
                have hrow' :
                    (Finite.equivFin (spanningTreeConstraintRow G)).symm i =
                      spanningTreeConstraintTotalLowerRow G := by
                  simpa [row, spanningTreeConstraintTotalLowerRow] using hrow
                have hi :
                    (Finite.equivFin (spanningTreeConstraintRow G))
                        (spanningTreeConstraintTotalLowerRow G) = i := by
                  exact
                    (congrArg (Finite.equivFin (spanningTreeConstraintRow G)) hrow').symm.trans
                      (Equiv.apply_symm_apply (Finite.equivFin (spanningTreeConstraintRow G)) i)
                have hrow :
                    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
                      -∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e := by
                  rw [← hi]
                  exact spanningTreeConstraint_total_lower_row_eval G y
                have hrhs :
                    ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ) =
                      -(Fintype.card V - 1 : ℝ) := by
                  rw [← hi]
                  norm_num [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
                rw [hrow]
                change (-∑ e : G.edgeSet, graphEdgeCoordinateReindex G y e) ≤
                  ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ)
                rw [hrhs]
                linarith [hy_total]
    | Sum.inr (Sum.inr (Sum.inr e)) =>
                have hrow' :
                    (Finite.equivFin (spanningTreeConstraintRow G)).symm i =
                      spanningTreeConstraintNonnegRow G e := by
                  simpa [row, spanningTreeConstraintNonnegRow] using hrow
                have hi :
                    (Finite.equivFin (spanningTreeConstraintRow G))
                        (spanningTreeConstraintNonnegRow G e) = i := by
                  exact
                    (congrArg (Finite.equivFin (spanningTreeConstraintRow G)) hrow').symm.trans
                      (Equiv.apply_symm_apply (Finite.equivFin (spanningTreeConstraintRow G)) i)
                have hrow :
                    (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y) i =
                      -graphEdgeCoordinateReindex G y e := by
                  rw [← hi]
                  exact spanningTreeConstraint_nonneg_row_eval G y e
                have hrhs :
                    ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ) = 0 := by
                  rw [← hi]
                  simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
                rw [hrow]
                change (-(graphEdgeCoordinateReindex G y e)) ≤
                  ((spanningTreeConstraintPresentationRhs G i : ℚ) : ℝ)
                rw [hrhs]
                linarith [hy_nonneg e]
  · intro hy
    rw [spanningTreeConstraintPresentation, mem_rational_matrix_polyhedron] at hy
    refine (mem_spanningTreeConstraintSet_iff).2 ?_
    constructor
    · intro S hS hSuniv
      let row : spanningTreeConstraintSubsetRow G := ⟨S, hS, hSuniv⟩
      have hineq :=
        hy ((Finite.equivFin (spanningTreeConstraintRow G)) (Sum.inl row))
      have hrow :
          (((spanningTreeConstraintPresentationMatrix G).map (Rat.castHom ℝ)) *ᵥ y)
              ((Finite.equivFin (spanningTreeConstraintRow G)) (Sum.inl row)) =
            Finset.sum (G.inducedEdgeFinset (S : Set V))
              (fun e ↦ graphEdgeCoordinateReindex G y e) := by
        simpa [row] using spanningTreeConstraint_subset_row_eval G y row
      have hrhs :
          ((spanningTreeConstraintPresentationRhs G
              ((Finite.equivFin (spanningTreeConstraintRow G)) (Sum.inl row)) : ℚ) : ℝ) =
            (S.card - 1 : ℝ) := by
        simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative, row]
      linarith
    constructor
    · have hupper :=
        hy ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintTotalUpperRow G))
      have hlower :=
        hy ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintTotalLowerRow G))
      have hupperEval := spanningTreeConstraint_total_upper_row_eval G y
      have hlowerEval := spanningTreeConstraint_total_lower_row_eval G y
      have hupperRhs :
          ((spanningTreeConstraintPresentationRhs G
              ((Finite.equivFin (spanningTreeConstraintRow G))
                (spanningTreeConstraintTotalUpperRow G)) : ℚ) : ℝ) =
            (Fintype.card V - 1 : ℝ) := by
        simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
      have hlowerRhs :
          ((spanningTreeConstraintPresentationRhs G
              ((Finite.equivFin (spanningTreeConstraintRow G))
                (spanningTreeConstraintTotalLowerRow G)) : ℚ) : ℝ) =
            -(Fintype.card V - 1 : ℝ) := by
        norm_num [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
      linarith
    · intro e
      have hineq :=
        hy ((Finite.equivFin (spanningTreeConstraintRow G))
          (spanningTreeConstraintNonnegRow G e))
      have hrow := spanningTreeConstraint_nonneg_row_eval G y e
      have hrhs :
          ((spanningTreeConstraintPresentationRhs G
              ((Finite.equivFin (spanningTreeConstraintRow G))
                (spanningTreeConstraintNonnegRow G e)) : ℚ) : ℝ) = 0 := by
        simp [spanningTreeConstraintPresentationRhs, spanningTreeConstraintRhsNative]
      linarith

/-- Helper for Theorem 4.25: the textbook spanning-tree constraint set is exactly the image of its
explicit Chapter 4.1 rational owner under the canonical edge-coordinate reindexing. -/
private theorem spanningTreeConstraintSet_eq_reindexed_rational_matrix_polyhedron
    (G : SimpleGraph V) [Fintype V] :
    spanningTreeConstraintSet G =
      graphEdgeCoordinateReindex G '' spanningTreeConstraintPresentation G := by
  ext x
  constructor
  · intro hx
    refine ⟨graphEdgeCoordinates G x, ?_, ?_⟩
    · have hx' :
          graphEdgeCoordinateReindex G (graphEdgeCoordinates G x) ∈ spanningTreeConstraintSet G := by
        simpa using
          (show graphEdgeCoordinateReindex G (graphEdgeCoordinates G x) ∈
              spanningTreeConstraintSet G by
            rw [graphEdgeCoordinateReindex_graphEdgeCoordinates G x]
            exact hx)
      have hreindex :
          graphEdgeCoordinateReindex G (graphEdgeCoordinates G x) ∈ spanningTreeConstraintSet G ↔
            graphEdgeCoordinates G x ∈ spanningTreeConstraintPresentation G :=
        graphEdgeCoordinateReindex_mem_spanningTreeConstraintPresentation_iff G
      exact
        hreindex.1 hx'
    · exact graphEdgeCoordinateReindex_graphEdgeCoordinates G x
  · rintro ⟨y, hy, rfl⟩
    have hreindex :
        graphEdgeCoordinateReindex G y ∈ spanningTreeConstraintSet G ↔
          y ∈ spanningTreeConstraintPresentation G :=
      graphEdgeCoordinateReindex_mem_spanningTreeConstraintPresentation_iff G
    exact
      hreindex.2 hy

/-- Helper for Theorem 4.25: reindexing integer lattice points along a finite coordinate
equivalence preserves the integer-point owner. -/
private theorem funCongrLeft_symm_image_integerPoints
    {α β : Type*} (e : α ≃ β) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
        Set.range (fun z : α → ℤ ↦ Int.cast ∘ z) =
      Set.range (fun z : β → ℤ ↦ Int.cast ∘ z) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨fun b ↦ z (e.symm b), ?_⟩
    -- Reindex the integer witness coordinatewise along the equivalence.
    funext b
    simp
  · rintro ⟨z, rfl⟩
    refine ⟨fun a ↦ (z (e a) : ℝ), ?_, ?_⟩
    · refine ⟨fun a ↦ z (e a), ?_⟩
      funext a
      rfl
    · -- The inverse reindexing recovers the original integer-valued coordinate function.
      funext b
      simp

/-- Helper for Theorem 4.25: coordinate reindexing commutes with intersections of function-space
subsets. -/
private theorem funCongrLeft_symm_image_inter
    {α β : Type*} (e : α ≃ β)
    (P Q : Set (α → ℝ)) :
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' (P ∩ Q) =
      (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
        (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' Q := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxP, hxQ⟩, rfl⟩
    exact ⟨⟨x, hxP, rfl⟩, ⟨x, hxQ, rfl⟩⟩
  · rintro ⟨⟨x, hxP, rfl⟩, ⟨x', hxQ, hImage⟩⟩
    -- Injectivity of the coordinate equivalence forces the two witnesses to agree.
    have hxx' : x = x' := by
      apply (LinearEquiv.funCongrLeft ℝ ℝ e.symm).injective
      simpa using hImage.symm
    exact ⟨x, ⟨hxP, hxx' ▸ hxQ⟩, rfl⟩

/-- Helper for Theorem 4.25: transporting an integral `Fin`-indexed polyhedron through the
canonical edge-coordinate equivalence preserves integrality. -/
private theorem is_integral_funCongrLeft_symm_image
    {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {P : Set (α → ℝ)} (hP : is_integral P) :
    is_integral ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P) := by
  rw [is_integral_iff] at hP ⊢
  calc
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P
        = (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
            convexHull ℝ
              (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z)) := by
            exact congrArg (Set.image (LinearEquiv.funCongrLeft ℝ ℝ e.symm)) hP
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
            (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))) := by
          -- Linear images commute with convex hulls.
          simpa using
            (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toLinearMap.image_convexHull
              (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z))
    _ = convexHull ℝ
          ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P ∩
            Set.range (fun z : β → ℤ ↦ Int.cast ∘ z)) := by
          -- The image of the integral owner is exactly the integral owner on the reindexed side.
          rw [funCongrLeft_symm_image_inter, funCongrLeft_symm_image_integerPoints]

/-- Helper for Theorem 4.25: transporting integrality from the explicit Chapter 4.1 owner to the
native edge-coordinate system uses only the canonical edge reindexing equivalence. -/
private theorem spanningTreeConstraintSet_isIntegral_of_presentation_isIntegral
    (G : SimpleGraph V) [Fintype V]
    (hPresentation : is_integral (spanningTreeConstraintPresentation G)) :
    is_integral (spanningTreeConstraintSet G) := by
  have hImage :
      is_integral (graphEdgeCoordinateReindex G '' spanningTreeConstraintPresentation G) := by
    -- Apply the generic transport lemma to the canonical enumeration of `G.edgeSet`.
    simpa [graphEdgeCoordinateReindex] using
      (is_integral_funCongrLeft_symm_image
        (Finite.equivFin G.edgeSet).symm
        hPresentation)
  simpa [spanningTreeConstraintSet_eq_reindexed_rational_matrix_polyhedron] using hImage

/-- Helper for Theorem 4.25: a connected graph has a spanning-tree incidence vector among the
spanning-tree vertices. -/
lemma spanningTreeVertices_nonempty_of_connected (G : SimpleGraph V) [Fintype V]
    (hG : G.Connected) :
    Set.Nonempty G.spanningTreeVertices := by
  -- Use the connectedness criterion to pick one spanning tree and then record its incidence
  -- vector as a vertex of the spanning-tree polytope description.
  rcases (G.connected_iff_exists_spanningTree).1 hG with ⟨T, hT⟩
  exact ⟨G.subgraphIncidenceVector ℝ T, G.mem_spanningTreeVertices_iff.2 ⟨T, hT, rfl⟩⟩

/-- Helper for Theorem 4.25: a connected graph has a nonempty spanning-tree polytope. -/
lemma spanningTreePolytope_nonempty_of_connected (G : SimpleGraph V) [Fintype V]
    (hG : G.Connected) :
    Set.Nonempty G.spanningTreePolytope := by
  -- Any spanning-tree vertex lies in the convex hull that defines `G.spanningTreePolytope`.
  rcases spanningTreeVertices_nonempty_of_connected G hG with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [G.spanningTreePolytope_eq_convexHull]
  exact subset_convexHull ℝ G.spanningTreeVertices hx

/-- Helper for Theorem 4.25: a connected graph has a feasible point for the textbook inequality
system, namely the incidence vector of a spanning tree. -/
lemma spanningTreeConstraintSet_nonempty_of_connected (G : SimpleGraph V) [Fintype V]
    (hG : G.Connected) :
    Set.Nonempty (spanningTreeConstraintSet G) := by
  -- The connectedness criterion provides a spanning tree, whose incidence vector satisfies the
  -- inequalities proved above.
  rcases (G.connected_iff_exists_spanningTree).1 hG with ⟨T, hT⟩
  exact ⟨G.subgraphIncidenceVector ℝ T,
    subgraphIncidenceVector_mem_spanningTreeConstraintSet G hT⟩

/-- Helper for Theorem 4.25: reindexing the `Fin`-indexed objective back to `G.edgeSet` preserves
its value on the corresponding native point. -/
private theorem graphEdgeCoordinate_dotProduct_reindex
    (G : SimpleGraph V) [Fintype V]
    (c y : Fin (Nat.card G.edgeSet) → ℝ) :
    c ⬝ᵥ y =
      ∑ e : G.edgeSet, graphEdgeCoordinateReindex G c e * graphEdgeCoordinateReindex G y e := by
  -- Expand the `Fin`-indexed dot product and reindex the ambient sum to `G.edgeSet`.
  rw [dotProduct]
  symm
  exact Fintype.sum_equiv (Finite.equivFin G.edgeSet) _ _ fun e ↦ by
    change (graphEdgeCoordinateReindex G c e) * (graphEdgeCoordinateReindex G y e) =
      c ((Finite.equivFin G.edgeSet) e) * y ((Finite.equivFin G.edgeSet) e)
    rw [graphEdgeCoordinateReindex_apply, graphEdgeCoordinateReindex_apply]

/-- Helper for Theorem 4.25: the objective value of a subgraph is its weighted incidence-vector
sum in the ambient edge coordinates. -/
private def treeWeight (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (T : G.Subgraph) : ℝ :=
  ∑ e : G.edgeSet, w e * G.subgraphIncidenceVector ℝ T e

/-- Helper for Theorem 4.25: among all spanning trees of a finite connected graph, one maximizes a
given edge-weight objective. -/
private lemma existsMaxWeightSpanningTree
    (G : SimpleGraph V) [Fintype V] (hG : G.Connected)
    (w : G.edgeSet → ℝ) :
    ∃ T : G.Subgraph, T.IsSpanningTree ∧
      ∀ T' : G.Subgraph, T'.IsSpanningTree → treeWeight G w T' ≤ treeWeight G w T := by
  classical
  letI : Fintype G.Subgraph := Fintype.ofFinite _
  let admissible : Finset G.Subgraph :=
    (Finset.univ : Finset G.Subgraph).filter fun T ↦ T.IsSpanningTree
  have hadmissible : admissible.Nonempty := by
    -- Connectedness supplies one spanning tree, so the finite search space is nonempty.
    rcases (G.connected_iff_exists_spanningTree).1 hG with ⟨T, hT⟩
    exact ⟨T, by simp [admissible, hT]⟩
  obtain ⟨T, hTmem, hTmax⟩ :=
    admissible.exists_max_image (fun T ↦ treeWeight G w T) hadmissible
  refine ⟨T, (Finset.mem_filter.mp hTmem).2, ?_⟩
  intro T' hT'
  -- The chosen tree maximizes `treeWeight` on the filtered finite family of spanning trees.
  have hT'mem : T' ∈ admissible := by
    simp [admissible, hT']
  exact hTmax T' hT'mem

/-- Helper for Theorem 4.25: every spanning-tree incidence vector is an integer edge vector. -/
private lemma subgraphIncidenceVector_mem_integerRange (G : SimpleGraph V) (T : G.Subgraph) :
    G.subgraphIncidenceVector ℝ T ∈
      Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) := by
  refine ⟨fun e ↦ if e.1 ∈ T.edgeSet then 1 else 0, ?_⟩
  -- Each incidence coordinate is exactly the cast of the corresponding `0/1` indicator.
  funext e
  by_cases he : e.1 ∈ T.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, he]
  · simp [SimpleGraph.subgraphIncidenceVector, he]

/-- Helper for Theorem 4.25: summing an ambient edge function with an `if` guard is the same as
filtering the edge finset by that guard first. -/
private lemma edgeSet_sum_ite_eq_sum_filter
    (G : SimpleGraph V) [Fintype V] (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-owner version of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Theorem 4.25: the endpoints of an edge form the corresponding two-element
finset. -/
private lemma edge_toFinset_eq_pair (G : SimpleGraph V) (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints before taking `toFinset`.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Theorem 4.25: an edge lies in `E[G] S` exactly when both of its endpoints lie in
`S`. -/
private lemma mem_inducedEdgeFinset_endpoints_iff
    (G : SimpleGraph V) [Fintype V] (S : Set V) (e : G.edgeSet) :
    e ∈ G.inducedEdgeFinset S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  -- The induced-edge owner is defined by requiring both endpoints to belong to `S`.
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.out_eq] using e.2
  rw [SimpleGraph.mem_inducedEdgeFinset_iff]
  rw [← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [hadj, edge_toFinset_eq_pair]

/-- Helper for Theorem 4.25: the threshold-`τ` heavy subgraph keeps exactly the edges whose
weight is at least `τ`. -/
private def heavySubgraph (G : SimpleGraph V)
    (w : G.edgeSet → ℝ) (τ : ℝ) : G.Subgraph where
  verts := Set.univ
  Adj u v := ∃ h : G.Adj u v, τ ≤ w ⟨s(u, v), G.mem_edgeSet.2 h⟩
  adj_sub := fun h ↦ h.1
  edge_vert := by
    intro u v h
    simp
  symm := by
    intro u v h
    rcases h with ⟨huv, hweight⟩
    refine ⟨huv.symm, ?_⟩
    simpa [Sym2.eq_swap] using hweight

/-- Helper for Theorem 4.25: the heavy-edge threshold sum keeps only coordinates whose weight is at
least `τ`. -/
private def heavyEdgeSum (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ) (x : G.edgeSet → ℝ) : ℝ :=
  ∑ e : G.edgeSet, if τ ≤ w e then x e else 0

/-- Helper for Theorem 4.25: membership in the heavy subgraph edge set is exactly the threshold
inequality on the ambient edge weight. -/
@[simp] private lemma heavySubgraph_mem_edgeSet_iff
    (G : SimpleGraph V) (w : G.edgeSet → ℝ) (τ : ℝ) (e : G.edgeSet) :
    e.1 ∈ (heavySubgraph G w τ).edgeSet ↔ τ ≤ w e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      have huv : G.Adj u v := by
        simpa using he
      -- Unfold the threshold subgraph once and identify the unique ambient edge subtype.
      simp [heavySubgraph, huv]

/-- Helper for Theorem 4.25: rewriting the threshold sum over the heavy-edge subtype removes the
ambient `if` guard. -/
private lemma heavyEdgeSum_eq_sum_subtype
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ) (x : G.edgeSet → ℝ) :
    heavyEdgeSum G w τ x = ∑ e : {e : G.edgeSet // τ ≤ w e}, x e.1 := by
  -- Rewrite the guarded ambient sum as the filtered edge owner, then identify that owner with the
  -- heavy-edge subtype.
  rw [heavyEdgeSum, edgeSet_sum_ite_eq_sum_filter]
  have hsum :
      (Finset.univ.filter fun e : G.edgeSet ↦ τ ≤ w e).sum x =
        ∑ e : {e : G.edgeSet // τ ≤ w e}, x e.1 := by
    refine Finset.sum_subtype (Finset.univ.filter fun e : G.edgeSet ↦ τ ≤ w e) ?_ x
    intro e
    simp
  simpa using hsum

/-- Helper for Theorem 4.25: every heavy edge lies in the induced edge owner of its heavy
connected component. -/
private lemma heavyEdge_mem_inducedEdgeFinset_component
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (e : {e : G.edgeSet // τ ≤ w e}) :
    let H := (heavySubgraph G w τ).spanningCoe
    let C : H.ConnectedComponent := H.connectedComponentMk e.1.1.out.1
    e.1 ∈ G.inducedEdgeFinset (C.supp : Set V) := by
  classical
  dsimp
  rw [mem_inducedEdgeFinset_endpoints_iff]
  let H : SimpleGraph V := (heavySubgraph G w τ).spanningCoe
  let C : H.ConnectedComponent := H.connectedComponentMk e.1.1.out.1
  have hAdjG : G.Adj e.1.1.out.1 e.1.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.1.out_eq] using e.1.2
  have hAdjH : H.Adj e.1.1.out.1 e.1.1.out.2 := by
    -- The threshold witness on `e` promotes the ambient adjacency to a heavy-subgraph adjacency.
    change (heavySubgraph G w τ).Adj e.1.1.out.1 e.1.1.out.2
    refine ⟨hAdjG, ?_⟩
    have hSubtype :
        (⟨s(e.1.1.out.1, e.1.1.out.2), G.mem_edgeSet.2 hAdjG⟩ : G.edgeSet) = e.1 := by
      apply Subtype.ext
      exact e.1.1.out_eq
    simpa [hSubtype] using e.2
  have hfst : e.1.1.out.1 ∈ C.supp := by
    simpa [C] using
      (show e.1.1.out.1 ∈ H.connectedComponentMk e.1.1.out.1 from
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
  have hsnd : e.1.1.out.2 ∈ C.supp := by
    exact (C.mem_supp_congr_adj hAdjH).mp hfst
  exact ⟨hfst, hsnd⟩

/-- Helper for Theorem 4.25: the threshold sum decomposes fiberwise over the heavy connected
components. -/
private lemma heavyEdgeSum_eq_sum_componentFibers
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ) (x : G.edgeSet → ℝ) :
    let H := (heavySubgraph G w τ).spanningCoe
    heavyEdgeSum G w τ x =
      ∑ C : H.ConnectedComponent,
        ∑ e : {e : {e : G.edgeSet // τ ≤ w e} // H.connectedComponentMk e.1.1.out.1 = C},
          x e.1.1 := by
  classical
  dsimp
  -- Rewrite the threshold sum once over the heavy-edge subtype, then split it by component owner.
  let H := (heavySubgraph G w τ).spanningCoe
  calc
    heavyEdgeSum G w τ x = ∑ e : {e : G.edgeSet // τ ≤ w e}, x e.1 := by
      rw [heavyEdgeSum_eq_sum_subtype]
    _ =
        ∑ C : H.ConnectedComponent,
          ∑ e : {e : {e : G.edgeSet // τ ≤ w e} // H.connectedComponentMk e.1.1.out.1 = C},
            x e.1.1 := by
          simpa [H] using
            (Fintype.sum_fiberwise
              (fun e : {e : G.edgeSet // τ ≤ w e} ↦ H.connectedComponentMk e.1.1.out.1)
              (fun e ↦ x e.1)).symm

/-- Helper for Theorem 4.25: for a heavy edge, belonging to a chosen heavy connected component is
equivalent to lying in the induced edge owner of that component support. -/
private lemma heavyEdgeComponent_eq_iff_mem_inducedEdgeFinset
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    {e : G.edgeSet} (hτ : τ ≤ w e) :
    ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.out.1 = C ↔
      e ∈ G.inducedEdgeFinset (C.supp : Set V) := by
  let H := (heavySubgraph G w τ).spanningCoe
  constructor
  · intro hC
    -- The existing component-membership lemma already identifies the heavy edge with the induced
    -- edge owner of its heavy connected component.
    simpa [H, hC] using
      (heavyEdge_mem_inducedEdgeFinset_component G w τ ⟨e, hτ⟩)
  · intro heC
    -- Membership in the induced edge owner places the first endpoint inside `C.supp`, which
    -- identifies the connected component of that endpoint with `C`.
    have hfst :
        e.1.out.1 ∈ C.supp := (mem_inducedEdgeFinset_endpoints_iff G (C.supp : Set V) e).1 heC |>.1
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C e.1.out.1).mp hfst

/-- Helper for Theorem 4.25: normalize a nested heavy-edge component fiber to the filtered
induced-edge owner on that heavy connected component. -/
private noncomputable def heavyEdgeComponentFiber_equiv_filteredInducedEdges
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    {e : {e : G.edgeSet // τ ≤ w e} //
        ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.1.out.1 = C} ≃
      {e : G.edgeSet //
        e ∈ (G.inducedEdgeFinset (C.supp : Set V)).filter (fun e : G.edgeSet ↦ τ ≤ w e)} where
  toFun e := by
    -- Convert component membership of a heavy edge into membership in the filtered induced-edge
    -- owner of the heavy component.
    refine ⟨e.1.1, ?_⟩
    have hmem :
        e.1.1 ∈ G.inducedEdgeFinset (C.supp : Set V) :=
      (heavyEdgeComponent_eq_iff_mem_inducedEdgeFinset G w τ C e.1.2).1 e.2
    simp [Finset.mem_filter, hmem, e.1.2]
  invFun e := by
    -- Read filtered induced-edge membership back as both the threshold witness and the component
    -- equality needed for the nested heavy-edge fiber.
    refine ⟨⟨e.1, ?_⟩, ?_⟩
    · exact (Finset.mem_filter.mp e.2).2
    · exact
        (heavyEdgeComponent_eq_iff_mem_inducedEdgeFinset G w τ C
          (Finset.mem_filter.mp e.2).2).2
          (Finset.mem_filter.mp e.2).1
  left_inv e := by
    -- Both owners store the same ambient edge, so the inverse recovers the original fiber point.
    cases e
    rfl
  right_inv e := by
    -- The forward map also preserves the underlying edge, hence the filtered owner point is
    -- recovered verbatim.
    cases e
    rfl

/-- Helper for Theorem 4.25: summing over a heavy-edge component fiber is the same as summing over
the filtered induced-edge owner of that component. -/
private lemma heavyEdgeComponentFiber_eq_inducedHeavyFilterSum
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    (x : G.edgeSet → ℝ) :
    ∑ e : {e : {e : G.edgeSet // τ ≤ w e} //
        ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.1.out.1 = C},
      x e.1.1 =
      Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ if τ ≤ w e then x e else 0) := by
  classical
  calc
    ∑ e : {e : {e : G.edgeSet // τ ≤ w e} //
        ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.1.out.1 = C},
      x e.1.1 =
        ∑ e : {e : G.edgeSet //
            e ∈ (G.inducedEdgeFinset (C.supp : Set V)).filter (fun e : G.edgeSet ↦ τ ≤ w e)},
          x e.1 := by
          -- The owner equivalence from the nested heavy-edge fiber to the filtered induced-edge
          -- owner lets us transport the sum without further coercion work.
          refine Fintype.sum_equiv
            (heavyEdgeComponentFiber_equiv_filteredInducedEdges G w τ C)
            (fun e ↦ x e.1.1)
            (fun e ↦ x e.1) ?_
          intro e
          rfl
    _ =
        Finset.sum
          ((G.inducedEdgeFinset (C.supp : Set V)).filter (fun e : G.edgeSet ↦ τ ≤ w e))
          (fun e ↦ x e) := by
          -- Replace the subtype owner with the corresponding filtered finset.
          change
            Finset.sum
                (Finset.attach
                  ((G.inducedEdgeFinset (C.supp : Set V)).filter
                    (fun e : G.edgeSet ↦ τ ≤ w e)))
                (fun e : {e : G.edgeSet //
                    e ∈ (G.inducedEdgeFinset (C.supp : Set V)).filter
                      (fun e : G.edgeSet ↦ τ ≤ w e)} ↦
                  x e.1) =
              Finset.sum
                ((G.inducedEdgeFinset (C.supp : Set V)).filter
                  (fun e : G.edgeSet ↦ τ ≤ w e))
                (fun e ↦ x e)
          rw [Finset.sum_attach]
    _ =
        Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ if τ ≤ w e then x e else 0) := by
          -- Finally rewrite the filtered finset sum back to the ambient induced-edge owner with an
          -- explicit threshold guard.
          rw [Finset.sum_filter]

/-- Helper for Theorem 4.25: a disconnected graph cannot have a connected component whose support
is all vertices. -/
private lemma componentSupport_ne_univ_of_not_connected
    (G : SimpleGraph V) [Fintype V]
    (hG : ¬ G.Connected) (C : G.ConnectedComponent) :
    (C.supp : Set V) ≠ Set.univ := by
  intro hC
  apply hG
  -- If one component already contains every vertex, then all vertices are reachable from any one
  -- of its members, so the whole graph is connected.
  rcases C.nonempty_supp with ⟨v, hv⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable G).2 ⟨v, ?_⟩
  intro u
  have hvEq : G.connectedComponentMk v = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp hv
  have hu : u ∈ C.supp := by simpa [hC]
  have huEq : G.connectedComponentMk u = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu
  exact SimpleGraph.ConnectedComponent.exact (hvEq.trans huEq.symm)

/-- Helper for Theorem 4.25: in the disconnected case, each heavy connected component is a proper
vertex subset when viewed as a finset. -/
private lemma componentSupport_toFinset_ne_univ_of_not_connected
    (G : SimpleGraph V) [Fintype V]
    (hG : ¬ G.Connected) (C : G.ConnectedComponent) :
    C.supp.toFinset ≠ Finset.univ := by
  intro hC
  apply componentSupport_ne_univ_of_not_connected G hG C
  ext v
  constructor
  · intro hv
    simp
  · intro hv
    have hv' : v ∈ C.supp.toFinset := by simpa [hC]
    simpa using hv'

/-- Helper for Theorem 4.25: when the heavy subgraph is disconnected, each heavy connected
component satisfies the feasible-side ambient guarded-sum bound needed before the subtype-fiber
normalization step. -/
private lemma inducedHeavyFilterSum_le_card_sub_one_of_not_connected
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (hH : ¬ ((heavySubgraph G w τ).spanningCoe).Connected)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ if τ ≤ w e then x e else 0) ≤
      (Fintype.card C.supp - 1 : ℝ) := by
  classical
  let H := (heavySubgraph G w τ).spanningCoe
  let S : Finset V := C.supp.toFinset
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨hx_subset, _, hx_nonneg⟩
  have hcomponent_nonempty : S.Nonempty := by
    rcases C.nonempty_supp with ⟨v, hv⟩
    exact ⟨v, by simpa [S] using hv⟩
  have hcomponent_ne_univ : S ≠ Finset.univ := by
    simpa [S] using componentSupport_toFinset_ne_univ_of_not_connected H hH C
  have hsubset :
      Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ x e) ≤
        ((S.card - 1 : ℝ)) :=
    by
      -- Normalize the component support through `toFinset` before applying the original subset
      -- inequality from `spanningTreeConstraintSet`.
      simpa [S] using hx_subset S hcomponent_nonempty hcomponent_ne_univ
  have hdrop_guard :
      Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ if τ ≤ w e then x e else 0) ≤
        Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ x e) := by
    -- Coordinatewise nonnegativity lets us discard the threshold guard on the induced-edge sum.
    refine Finset.sum_le_sum ?_
    intro e he
    by_cases hτ : τ ≤ w e
    · simp [hτ]
    · simp [hτ, hx_nonneg e]
  have hcard_support : S.card = Fintype.card C.supp := by
    simpa [S, Nat.card_eq_fintype_card] using
      (Nat.card_eq_card_toFinset (C.supp : Set V)).symm
  calc
    Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ if τ ≤ w e then x e else 0) ≤
      Finset.sum (G.inducedEdgeFinset (C.supp : Set V)) (fun e ↦ x e) := hdrop_guard
    _ ≤ (S.card - 1 : ℝ) := hsubset
    _ = (Fintype.card C.supp - 1 : ℝ) := by rw [hcard_support]

/-- Helper for Theorem 4.25: after normalizing the component-fiber owner, each disconnected heavy
component satisfies the feasible-side threshold bound directly on the nested fiber sum. -/
private lemma heavyEdgeComponentFiber_le_card_sub_one_of_not_connected
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (hH : ¬ ((heavySubgraph G w τ).spanningCoe).Connected)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    ∑ e : {e : {e : G.edgeSet // τ ≤ w e} //
        ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.1.out.1 = C},
      x e.1.1 ≤
      (Fintype.card C.supp - 1 : ℝ) := by
  -- Route correction: normalize the nested heavy-edge fiber first, then reuse the existing
  -- induced-edge feasible bound instead of fighting coercions in the main theorem.
  rw [heavyEdgeComponentFiber_eq_inducedHeavyFilterSum G w τ C x]
  exact inducedHeavyFilterSum_le_card_sub_one_of_not_connected G hx w τ hH C

/-- Helper for Theorem 4.25: if the heavy subgraph is disconnected, the full threshold sum is
bounded by the sum of the heavy-component cardinality terms. -/
private lemma heavyEdgeSum_le_componentCardSum_of_not_connected
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (hH : ¬ ((heavySubgraph G w τ).spanningCoe).Connected) :
    heavyEdgeSum G w τ x ≤
      ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        (Fintype.card C.supp - 1 : ℝ) := by
  classical
  -- Decompose the threshold sum by heavy connected components and bound each fiber separately.
  rw [heavyEdgeSum_eq_sum_componentFibers]
  refine Finset.sum_le_sum ?_
  intro C hC
  exact heavyEdgeComponentFiber_le_card_sub_one_of_not_connected G hx w τ hH C

/-- Helper for Theorem 4.25: the heavy-edge sum of a subgraph incidence vector is exactly the edge
count of the heavy part `T ⊓ heavySubgraph G w τ`. -/
private lemma heavyEdgeSum_subgraphIncidenceVector_eq_card_heavyPart
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ) (T : G.Subgraph) :
    heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) =
      Fintype.card ((T ⊓ heavySubgraph G w τ).edgeSet) := by
  -- Route correction: compare threshold counts through the actual heavy part, not through all
  -- edges induced on a heavy component.
  calc
    heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) =
        ∑ e : G.edgeSet,
          if e.1 ∈ (T ⊓ heavySubgraph G w τ).edgeSet then (1 : ℝ) else 0 := by
      unfold heavyEdgeSum
      refine Finset.sum_congr rfl ?_
      intro e he
      by_cases hT : e.1 ∈ T.edgeSet
      · by_cases hτ : τ ≤ w e
        · simp [SimpleGraph.subgraphIncidenceVector, hT, hτ, heavySubgraph_mem_edgeSet_iff]
        · simp [SimpleGraph.subgraphIncidenceVector, hT, hτ, heavySubgraph_mem_edgeSet_iff]
      · by_cases hτ : τ ≤ w e
        · simp [SimpleGraph.subgraphIncidenceVector, hT, hτ, heavySubgraph_mem_edgeSet_iff]
        · simp [SimpleGraph.subgraphIncidenceVector, hT, hτ, heavySubgraph_mem_edgeSet_iff]
    _ = Fintype.card ((T ⊓ heavySubgraph G w τ).edgeSet) :=
      sum_edge_indicator_eq_card_edgeSet G (T ⊓ heavySubgraph G w τ)

/-- Helper for Theorem 4.25: the threshold sum is always bounded by the total-edge equation of a
feasible point. -/
private lemma heavyEdgeSum_le_total_of_mem_spanningTreeConstraintSet
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (w : G.edgeSet → ℝ) (τ : ℝ) :
    heavyEdgeSum G w τ x ≤ (Fintype.card V - 1 : ℝ) := by
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨_, hx_total, hx_nonneg⟩
  have hle :
      (∑ e : G.edgeSet, if τ ≤ w e then x e else 0) ≤ ∑ e : G.edgeSet, x e := by
    refine Finset.sum_le_sum ?_
    intro e he
    by_cases hτ : τ ≤ w e
    · simp [hτ]
    · simp [hτ, hx_nonneg e]
  -- Dropping the threshold filter can only increase the sum because every coordinate is
  -- nonnegative, and the total sum is fixed by feasibility.
  calc
    heavyEdgeSum G w τ x ≤ ∑ e : G.edgeSet, x e := by
      simpa [heavyEdgeSum] using hle
    _ = (Fintype.card V - 1 : ℝ) := hx_total

/-- Helper for Theorem 4.25: every feasible edge coordinate is at most `1`. -/
private lemma edgeCoordinate_le_one_of_mem_spanningTreeConstraintSet
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G) (e : G.edgeSet) :
    x e ≤ 1 := by
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨hx_subset, hx_total, hx_nonneg⟩
  let S : Finset V := (e : Sym2 V).toFinset
  have hScard : S.card = 2 := by
    -- An edge of a simple graph has two distinct endpoints.
    have hnotDiag : ¬ (e : Sym2 V).IsDiag := G.not_isDiag_of_mem_edgeSet e.2
    simpa [S] using Sym2.card_toFinset_of_not_isDiag (e : Sym2 V) hnotDiag
  have hS_nonempty : S.Nonempty := by
    have hcard_pos : 0 < S.card := by omega
    exact Finset.card_pos.mp hcard_pos
  by_cases hSuniv : S = Finset.univ
  · -- When the edge endpoints exhaust all vertices, the total-edge equation already gives the
    -- bound because every coordinate is nonnegative.
    have hcardV : Fintype.card V = 2 := by
      calc
        Fintype.card V = (Finset.univ : Finset V).card := by simp
        _ = S.card := by rw [← hSuniv]
        _ = 2 := hScard
    have hsum_ge :
        x e ≤ Finset.sum Finset.univ (fun e' : G.edgeSet ↦ x e') := by
      simpa using
        (Finset.single_le_sum (fun e' _ ↦ hx_nonneg e') (Finset.mem_univ e) :
          x e ≤ Finset.sum Finset.univ (fun e' : G.edgeSet ↦ x e'))
    have htotal_one :
        Finset.sum Finset.univ (fun e' : G.edgeSet ↦ x e') = 1 := by
      rw [hcardV] at hx_total
      norm_num at hx_total
      exact hx_total
    linarith
  · -- Otherwise the two-endpoint subset inequality bounds the chosen coordinate.
    have heS : e ∈ G.inducedEdgeFinset (S : Set V) := by
      rw [mem_inducedEdgeFinset_endpoints_iff]
      simp [S, edge_toFinset_eq_pair]
    have hsum_ge :
        x e ≤ Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e' ↦ x e') := by
      simpa using
        (Finset.single_le_sum (fun e' _ ↦ hx_nonneg e') heS :
          x e ≤ Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e' ↦ x e'))
    have hsubset := hx_subset S hS_nonempty hSuniv
    have hsubset_one :
        Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e' ↦ x e') ≤ 1 := by
      rw [hScard] at hsubset
      norm_num at hsubset
      exact hsubset
    linarith

/-- Helper for Theorem 4.25: an integral feasible edge coordinate is either `0` or `1`. -/
private lemma edgeCoordinate_eq_zero_or_one_of_mem_spanningTreeConstraintSet_of_integer
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨_, _, hx_nonneg⟩
  rcases hxInt with ⟨z, hz⟩
  have hze : x e = (z e : ℝ) := by
    simpa using (congrFun hz e).symm
  have hz_nonneg : 0 ≤ z e := by
    have hx_nonneg' : 0 ≤ x e := hx_nonneg e
    rw [hze] at hx_nonneg'
    exact_mod_cast hx_nonneg'
  have hz_le_one : z e ≤ 1 := by
    have hx_le_one : x e ≤ 1 :=
      edgeCoordinate_le_one_of_mem_spanningTreeConstraintSet G hx e
    rw [hze] at hx_le_one
    exact_mod_cast hx_le_one
  have hz_zero_or_one : z e = 0 ∨ z e = 1 := by
    omega
  rcases hz_zero_or_one with hz0 | hz1
  · left
    simpa [hze, hz0]
  · right
    simpa [hze, hz1]

/-- Helper for Theorem 4.25: threshold domination on the finite weight levels, together with equal
total sums, implies the weighted objective inequality. -/
private lemma weightedObjective_le_of_thresholdDomination
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) {x y : G.edgeSet → ℝ}
    (hsum : ∑ e : G.edgeSet, x e = ∑ e : G.edgeSet, y e)
    (hdom :
      ∀ τ ∈ Finset.univ.image w,
        heavyEdgeSum G w τ x ≤ heavyEdgeSum G w τ y) :
    (∑ e : G.edgeSet, w e * x e) ≤ ∑ e : G.edgeSet, w e * y e := by
  classical
  -- Induct on the number of distinct edge weights, compressing the top weight at each step.
  let P : ℕ → Prop := fun n ↦
    ∀ w : G.edgeSet → ℝ,
      (Finset.univ.image w).card = n →
      ∀ {x y : G.edgeSet → ℝ},
        (∑ e : G.edgeSet, x e = ∑ e : G.edgeSet, y e) →
        (∀ τ ∈ Finset.univ.image w,
          heavyEdgeSum G w τ x ≤ heavyEdgeSum G w τ y) →
        (∑ e : G.edgeSet, w e * x e) ≤ ∑ e : G.edgeSet, w e * y e
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih w hwcard x y hsum hdom
    let W : Finset ℝ := Finset.univ.image w
    have hWcard : W.card = n := hwcard
    by_cases hW : W.Nonempty
    · let τ : ℝ := W.max' hW
      have hτW : τ ∈ W := by
        simpa [τ] using Finset.max'_mem W hW
      by_cases hErase : W.erase τ = ∅
      · -- If the top weight is the only weight, then both objectives are just `τ` times the
        -- common total sum.
        have hconst : ∀ e : G.edgeSet, w e = τ := by
          intro e
          have hwe : w e ∈ W := by
            exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
          by_contra hneq
          have hmemErase : w e ∈ W.erase τ := by
            exact Finset.mem_erase.mpr ⟨hneq, hwe⟩
          simpa [hErase] using hmemErase
        have hxObj :
            ∑ e : G.edgeSet, w e * x e = τ * ∑ e : G.edgeSet, x e := by
          calc
            ∑ e : G.edgeSet, w e * x e = ∑ e : G.edgeSet, τ * x e := by
              refine Finset.sum_congr rfl ?_
              intro e he
              rw [hconst e]
            _ = τ * ∑ e : G.edgeSet, x e := by
              symm
              rw [Finset.mul_sum]
        have hyObj :
            ∑ e : G.edgeSet, w e * y e = τ * ∑ e : G.edgeSet, y e := by
          calc
            ∑ e : G.edgeSet, w e * y e = ∑ e : G.edgeSet, τ * y e := by
              refine Finset.sum_congr rfl ?_
              intro e he
              rw [hconst e]
            _ = τ * ∑ e : G.edgeSet, y e := by
              symm
              rw [Finset.mul_sum]
        rw [hxObj, hyObj, hsum]
      · let σ : ℝ := (W.erase τ).max' (Finset.nonempty_iff_ne_empty.mpr hErase)
        let w' : G.edgeSet → ℝ := fun e ↦ if w e = τ then σ else w e
        have hσErase : σ ∈ W.erase τ := by
          simpa [σ] using
            Finset.max'_mem (W.erase τ) (Finset.nonempty_iff_ne_empty.mpr hErase)
        have hσW : σ ∈ W := (Finset.mem_erase.mp hσErase).2
        have hσleτ : σ ≤ τ := Finset.le_max' W σ hσW
        have hw'subset : Finset.univ.image w' ⊆ W.erase τ := by
          intro μ hμ
          rcases Finset.mem_image.mp hμ with ⟨e, -, rfl⟩
          by_cases hEq : w e = τ
          · simpa [w', hEq, σ] using hσErase
          · simpa [w', hEq] using
              (Finset.mem_erase.mpr
                ⟨hEq, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩⟩ :
                  w e ∈ W.erase τ)
        have hw'card_lt : (Finset.univ.image w').card < n := by
          have hle :
              (Finset.univ.image w').card ≤ (W.erase τ).card :=
            Finset.card_le_card hw'subset
          have hlt : (W.erase τ).card < W.card := Finset.card_erase_lt_of_mem hτW
          exact lt_of_le_of_lt hle (hlt.trans_eq hWcard)
        have hdom' :
            ∀ μ ∈ Finset.univ.image w',
              heavyEdgeSum G w' μ x ≤ heavyEdgeSum G w' μ y := by
          intro μ hμ
          have hμErase : μ ∈ W.erase τ := hw'subset hμ
          have hμW : μ ∈ W := (Finset.mem_erase.mp hμErase).2
          have hμleσ : μ ≤ σ := Finset.le_max' (W.erase τ) μ hμErase
          have hxeq : heavyEdgeSum G w' μ x = heavyEdgeSum G w μ x := by
            -- Below the compressed top level, the heavy-edge threshold sum is unchanged.
            unfold heavyEdgeSum
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hEq : w e = τ
            · have hμleτ : μ ≤ τ := le_trans hμleσ hσleτ
              simp [w', hEq, hμleσ, hμleτ]
            · simp [w', hEq]
          have hyeq : heavyEdgeSum G w' μ y = heavyEdgeSum G w μ y := by
            -- The same threshold normalization holds for the comparison vector `y`.
            unfold heavyEdgeSum
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hEq : w e = τ
            · have hμleτ : μ ≤ τ := le_trans hμleσ hσleτ
              simp [w', hEq, hμleσ, hμleτ]
            · simp [w', hEq]
          rw [hxeq, hyeq]
          exact hdom μ hμW
        have hobjx :
            ∑ e : G.edgeSet, w e * x e =
              (∑ e : G.edgeSet, w' e * x e) +
                (τ - σ) * heavyEdgeSum G w τ x := by
          -- Compressing the top weight changes the objective only on the top-weight edges.
          calc
            ∑ e : G.edgeSet, w e * x e =
                ∑ e : G.edgeSet,
                  (w' e * x e + (τ - σ) * (if τ ≤ w e then x e else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro e he
                    by_cases hEq : w e = τ
                    · have hτle : τ ≤ w e := by simpa [hEq]
                      simp [w', hEq, hτle]
                      ring
                    · have hτnot : ¬ τ ≤ w e := by
                        intro hτle
                        have hwe : w e ∈ W := Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
                        exact hEq (le_antisymm (Finset.le_max' W (w e) hwe) hτle)
                      simp [w', hEq, hτnot]
            _ =
                (∑ e : G.edgeSet, w' e * x e) +
                  (τ - σ) * ∑ e : G.edgeSet, (if τ ≤ w e then x e else 0) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ =
                (∑ e : G.edgeSet, w' e * x e) +
                  (τ - σ) * heavyEdgeSum G w τ x := by
                    simp [heavyEdgeSum]
        have hobjy :
            ∑ e : G.edgeSet, w e * y e =
              (∑ e : G.edgeSet, w' e * y e) +
                (τ - σ) * heavyEdgeSum G w τ y := by
          -- The same top-weight compression identity holds for `y`.
          calc
            ∑ e : G.edgeSet, w e * y e =
                ∑ e : G.edgeSet,
                  (w' e * y e + (τ - σ) * (if τ ≤ w e then y e else 0)) := by
                    refine Finset.sum_congr rfl ?_
                    intro e he
                    by_cases hEq : w e = τ
                    · have hτle : τ ≤ w e := by simpa [hEq]
                      simp [w', hEq, hτle]
                      ring
                    · have hτnot : ¬ τ ≤ w e := by
                        intro hτle
                        have hwe : w e ∈ W := Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
                        exact hEq (le_antisymm (Finset.le_max' W (w e) hwe) hτle)
                      simp [w', hEq, hτnot]
            _ =
                (∑ e : G.edgeSet, w' e * y e) +
                  (τ - σ) * ∑ e : G.edgeSet, (if τ ≤ w e then y e else 0) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ =
                (∑ e : G.edgeSet, w' e * y e) +
                  (τ - σ) * heavyEdgeSum G w τ y := by
                    simp [heavyEdgeSum]
        have hrec :=
          ih (Finset.univ.image w').card hw'card_lt w' rfl hsum hdom'
        have htop : heavyEdgeSum G w τ x ≤ heavyEdgeSum G w τ y := hdom τ hτW
        have hcoeff : 0 ≤ τ - σ := sub_nonneg.mpr hσleτ
        calc
          ∑ e : G.edgeSet, w e * x e =
              (∑ e : G.edgeSet, w' e * x e) + (τ - σ) * heavyEdgeSum G w τ x := hobjx
          _ ≤
              (∑ e : G.edgeSet, w' e * y e) + (τ - σ) * heavyEdgeSum G w τ y := by
                exact add_le_add hrec (mul_le_mul_of_nonneg_left htop hcoeff)
          _ = ∑ e : G.edgeSet, w e * y e := hobjy.symm
    · -- With no edge weights at all, the edge owner is empty and both objectives vanish.
      have hEmpty : IsEmpty G.edgeSet := by
        by_contra hE
        letI : Nonempty G.edgeSet := not_isEmpty_iff.mp hE
        exact hW (Finset.univ_nonempty.image w)
      letI : IsEmpty G.edgeSet := hEmpty
      simp
  exact hP (Finset.univ.image w).card w rfl hsum hdom

/-- Helper for Theorem 4.25: the support subgraph keeps exactly the edges whose coordinate is
`1`. -/
private abbrev integralSupportSubgraph (G : SimpleGraph V) (x : G.edgeSet → ℝ) : G.Subgraph where
  verts := {v : V | ∃ w, ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1}
  Adj := fun v w ↦ ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1
  adj_sub := fun h ↦ h.1
  edge_vert := by
    intro v w h
    exact ⟨w, h⟩
  symm := by
    intro v w h
    rcases h with ⟨hvw, hxvw⟩
    refine ⟨hvw.symm, ?_⟩
    simpa [Sym2.eq_swap] using hxvw

/-- Helper for Theorem 4.25: adjacency in the support subgraph means the corresponding edge
coordinate is `1`. -/
private theorem integralSupportSubgraph_adj_iff
    (G : SimpleGraph V) (x : G.edgeSet → ℝ) {u v : V} :
    (integralSupportSubgraph G x).Adj u v ↔
      ∃ h : G.Adj u v, x ⟨s(u, v), G.mem_edgeSet.2 h⟩ = 1 := by
  rfl

/-- Helper for Theorem 4.25: an ambient edge lies in the support subgraph exactly when its
coordinate is `1`. -/
private lemma integralSupportSubgraph_mem_edgeSet_iff
    (G : SimpleGraph V) (x : G.edgeSet → ℝ) (e : G.edgeSet) :
    e.1 ∈ (integralSupportSubgraph G x).edgeSet ↔ x e = 1 := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.out_eq] using e.2
  rw [← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet,
    integralSupportSubgraph_adj_iff G x]
  constructor
  · rintro ⟨hG, hx⟩
    have hSubtype :
        (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hG⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      exact e.1.out_eq
    simpa [hSubtype] using hx
  · intro hx
    refine ⟨hadj, ?_⟩
    have hSubtype :
        (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      exact e.1.out_eq
    simpa [hSubtype] using hx

/-- Helper for Theorem 4.25: inducing the top subgraph of `T.spanningCoe` on `S` recovers the
induced subgraph of `T` on `S`. -/
private lemma topSpanningCoe_induce_edgeSet_eq
    (G : SimpleGraph V) (T : G.Subgraph) (S : Set V) :
    ((⊤ : T.spanningCoe.Subgraph).induce S).edgeSet = (T.induce S).edgeSet := by
  -- Both induced edge owners encode the same condition: adjacency in `T` with both endpoints in
  -- `S`.
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.induce,
        SimpleGraph.Subgraph.spanningCoe]
      constructor
      · rintro ⟨hu, hv, huv⟩
        exact ⟨hu, hv, huv⟩
      · rintro ⟨hu, hv, huv⟩
        exact ⟨hu, hv, huv⟩

/-- Helper for Theorem 4.25: deleting the singleton edge `{f}` from a subgraph preserves exactly
the other ambient edge coordinates. -/
private lemma mem_edgeSet_deleteEdges_singleton_iff
    (G : SimpleGraph V) (T : G.Subgraph) (e : G.edgeSet) (f : Sym2 V) :
    e.1 ∈ (T.deleteEdges ({f} : Set (Sym2 V))).edgeSet ↔ e.1 ∈ T.edgeSet ∧ e.1 ≠ f := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      have huv : G.Adj u v := by
        simpa using he
      rw [SimpleGraph.Subgraph.mem_edgeSet, SimpleGraph.Subgraph.deleteEdges_adj,
        SimpleGraph.Subgraph.mem_edgeSet]
      simp [huv]

/-- Helper for Theorem 4.25: the singleton subgraph generated by `e` contains exactly the ambient
edge coordinate `s(u, v)`. -/
private lemma mem_edgeSet_subgraphOfAdj_iff_eq
    (G : SimpleGraph V) {u v : V} (h : G.Adj u v) (g : G.edgeSet) :
    g.1 ∈ (G.subgraphOfAdj h).edgeSet ↔ g.1 = s(u, v) := by
  rw [SimpleGraph.edgeSet_subgraphOfAdj]
  simp [Set.mem_singleton_iff]

/-- Helper for Theorem 4.25: counting edges in `T.induce S` agrees with counting edges in the
induced simple graph `T.spanningCoe.induce S`. -/
private theorem natCard_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce
    (G : SimpleGraph V) [Finite V] (T : G.Subgraph) (S : Set V) :
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
  have hcoe :
      (T.induce S).coe = T.spanningCoe.induce S := by
    ext u v
    simp [SimpleGraph.Subgraph.spanningCoe]
  have hcoe_edge_card : Nat.card ((T.induce S).coe.edgeSet) = Nat.card ((T.induce S).edgeSet) := by
    classical
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    calc
      ((T.induce S).coe.edgeSet).ncard =
          (Sym2.map ((↑) : (T.induce S).verts → V) '' (T.induce S).coe.edgeSet).ncard := by
            symm
            exact Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
      _ = ((T.induce S).edgeSet).ncard := by
            rw [(T.induce S).image_coe_edgeSet_coe]
  calc
    Nat.card ((T.induce S).edgeSet) = Nat.card ((T.induce S).coe.edgeSet) := hcoe_edge_card.symm
    _ = Nat.card ((T.spanningCoe.induce S).edgeSet) := by
          rw [hcoe]
          rfl

/-- Helper for Theorem 4.25: an integral feasible point equals the incidence vector of its
support subgraph. -/
private lemma integralSupportSubgraph_incidence_eq_of_mem_spanningTreeConstraintSet_of_integer
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x = G.subgraphIncidenceVector ℝ (integralSupportSubgraph G x) := by
  -- Route correction: rebuild the feasible integer point from its `0/1` support before proving
  -- the support graph is connected.
  funext e
  by_cases he : x e = 1
  · have heT : e.1 ∈ (integralSupportSubgraph G x).edgeSet := by
      simpa using (integralSupportSubgraph_mem_edgeSet_iff G x e).2 he
    -- On the support, both the reconstructed incidence vector and `x` equal `1`.
    simp [SimpleGraph.subgraphIncidenceVector, heT, he]
  · have hx0 : x e = 0 := by
      -- Off the support, integrality collapses the coordinate to `0`.
      rcases edgeCoordinate_eq_zero_or_one_of_mem_spanningTreeConstraintSet_of_integer G hx hxInt e with
        hzero | hone
      · exact hzero
      · exact (he hone).elim
    have heT : e.1 ∉ (integralSupportSubgraph G x).edgeSet := by
      intro heT
      exact he ((integralSupportSubgraph_mem_edgeSet_iff G x e).1 heT)
    -- Off the support, both the reconstructed incidence vector and `x` vanish.
    simp [SimpleGraph.subgraphIncidenceVector, heT, hx0]

/-- Helper for Theorem 4.25: an edge crossing a connected component of the support graph has
coordinate `0`. -/
private lemma supportComponentCrossEdge_eq_zero
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (C : (integralSupportSubgraph G x).spanningCoe.ConnectedComponent)
    (e : G.edgeSet)
    (hsep :
      (e.1.out.1 ∈ C.supp ∧ e.1.out.2 ∉ C.supp) ∨
        (e.1.out.2 ∈ C.supp ∧ e.1.out.1 ∉ C.supp)) :
    x e = 0 := by
  rcases edgeCoordinate_eq_zero_or_one_of_mem_spanningTreeConstraintSet_of_integer G hx hxInt e with
    hzero | hone
  · exact hzero
  · exfalso
    let T : G.Subgraph := integralSupportSubgraph G x
    have heT : e.1 ∈ T.edgeSet := by
      simpa [T] using (integralSupportSubgraph_mem_edgeSet_iff G x e).2 hone
    have hAdjT : T.Adj e.1.out.1 e.1.out.2 := by
      exact (SimpleGraph.Subgraph.mem_edgeSet).1 (by simpa [e.1.out_eq] using heT)
    have hAdjSpanning : T.spanningCoe.Adj e.1.out.1 e.1.out.2 := by
      simpa [SimpleGraph.Subgraph.spanningCoe] using hAdjT
    have hiff := C.mem_supp_congr_adj hAdjSpanning
    rcases hsep with ⟨hfst, hsnd⟩ | ⟨hsnd, hfst⟩
    · exact hsnd (hiff.mp hfst)
    · exact hfst (hiff.mpr hsnd)

/-- Helper for Theorem 4.25: the support subgraph of an integral feasible point is a spanning
tree. -/
private theorem integralSupportSubgraph_isSpanningTree_of_mem_spanningTreeConstraintSet_of_integer
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    (integralSupportSubgraph G x).IsSpanningTree := by
  let T : G.Subgraph := integralSupportSubgraph G x
  have hxT : x = G.subgraphIncidenceVector ℝ T :=
    integralSupportSubgraph_incidence_eq_of_mem_spanningTreeConstraintSet_of_integer G hx hxInt
  rcases (mem_spanningTreeConstraintSet_iff).1 hx with ⟨hx_subset, hx_total, hx_nonneg⟩
  have hedgeCountReal : (Fintype.card T.edgeSet : ℝ) = (Fintype.card V - 1 : ℝ) := by
    -- The total-edge equation becomes the support-edge count once `x` is rewritten as an
    -- incidence vector.
    calc
      (Fintype.card T.edgeSet : ℝ) = ∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ T e := by
        symm
        simpa using sum_subgraphIncidenceVector_eq_card_edgeSet G T
      _ = ∑ e : G.edgeSet, x e := by
        rw [hxT]
      _ = (Fintype.card V - 1 : ℝ) := hx_total
  have hedgeCountAddReal : (Fintype.card T.edgeSet : ℝ) + 1 = Fintype.card V := by
    nlinarith [hedgeCountReal]
  have hedgeCountAddNat : Fintype.card T.edgeSet + 1 = Fintype.card V := by
    exact_mod_cast hedgeCountAddReal
  have hedgeCount : Fintype.card T.edgeSet = Fintype.card V - 1 := by
    omega
  have hConnected : T.spanningCoe.Connected := by
    by_contra hdisc
    let y : T.spanningCoe.edgeSet → ℝ := fun _ ↦ 1
    have hy : y ∈ spanningTreeConstraintSet T.spanningCoe := by
      refine (mem_spanningTreeConstraintSet_iff).2 ?_
      constructor
      · intro S hS hSuniv
        -- The support graph inherits the subset inequalities from `x` after rewriting `x` as its
        -- incidence vector.
        calc
          Finset.sum (T.spanningCoe.inducedEdgeFinset (S : Set V)) (fun e ↦ y e) =
              Fintype.card ((T.induce (S : Set V)).edgeSet) := by
                calc
                  Finset.sum (T.spanningCoe.inducedEdgeFinset (S : Set V)) (fun e ↦ y e) =
                      Fintype.card (((⊤ : T.spanningCoe.Subgraph).induce (S : Set V)).edgeSet) := by
                        simpa [y, SimpleGraph.subgraphIncidenceVector] using
                          induced_incidence_sum_eq_card_induced_edges T.spanningCoe
                            (⊤ : T.spanningCoe.Subgraph) S
                  _ = Fintype.card ((T.induce (S : Set V)).edgeSet) := by
                        rw [topSpanningCoe_induce_edgeSet_eq G T (S : Set V)]
          _ = Finset.sum (G.inducedEdgeFinset (S : Set V)) (fun e ↦ x e) := by
                symm
                simpa [hxT] using induced_incidence_sum_eq_card_induced_edges G T S
          _ ≤ (S.card - 1 : ℝ) := hx_subset S hS hSuniv
      constructor
      · -- The all-ones vector on the support graph has the same total sum as `x`.
        calc
          Finset.sum Finset.univ (fun e : T.spanningCoe.edgeSet ↦ y e) =
              Fintype.card ((⊤ : T.spanningCoe.Subgraph).edgeSet) := by
                simpa [y, SimpleGraph.subgraphIncidenceVector] using
                  sum_subgraphIncidenceVector_eq_card_edgeSet T.spanningCoe
                    (⊤ : T.spanningCoe.Subgraph)
          _ = Fintype.card T.edgeSet := by
                simp [SimpleGraph.Subgraph.edgeSet_spanningCoe]
          _ = (Fintype.card V - 1 : ℝ) := by
                exact hedgeCountReal
      · intro e
        -- The constant-one support vector is coordinatewise nonnegative.
        simp [y]
    have hempty :=
      spanningTreeConstraintSet_eq_empty_of_not_connected T.spanningCoe hdisc
    exact Set.notMem_empty y (hempty ▸ hy)
  -- Connectedness together with the support edge count gives the tree criterion.
  have hedgeCardNat : Nat.card T.spanningCoe.edgeSet + 1 = Nat.card V := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.Subgraph.edgeSet_spanningCoe] using hedgeCountAddNat
  have htree :
      T.spanningCoe.IsTree ↔
        T.spanningCoe.Connected ∧ Nat.card T.spanningCoe.edgeSet + 1 = Nat.card V :=
    SimpleGraph.isTree_iff_connected_and_card
  simpa [SimpleGraph.Subgraph.IsSpanningTree] using
    htree.2 ⟨hConnected, hedgeCardNat⟩

/-- Helper for Theorem 4.25: if the heavy subgraph is connected, then the connected-component
cardinality sum collapses to the single term `|V| - 1`. -/
private lemma heavyComponentCardSum_eq_total_of_connected
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (hH : ((heavySubgraph G w τ).spanningCoe).Connected) :
    (∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        (Fintype.card C.supp - 1 : ℝ)) =
      (Fintype.card V - 1 : ℝ) := by
  classical
  let H := ((heavySubgraph G w τ).spanningCoe)
  letI : Subsingleton H.ConnectedComponent :=
    SimpleGraph.Preconnected.subsingleton_connectedComponent hH.preconnected
  obtain ⟨v⟩ := hH.nonempty
  let C₀ : H.ConnectedComponent := H.connectedComponentMk v
  have hSupp : (C₀.supp : Set V) = Set.univ := by
    -- In a connected graph, the unique connected component contains every vertex.
    ext u
    simp only [Set.mem_univ, iff_true]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff C₀ u).2
      (SimpleGraph.ConnectedComponent.sound (hH.preconnected u v))
  have hUniv : (Finset.univ : Finset H.ConnectedComponent) = {C₀} := by
    ext C
    simp [Subsingleton.elim C C₀]
  have hcardSupp : Fintype.card C₀.supp = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hSupp]
    simpa using Nat.card_congr (Equiv.Set.univ V)
  -- After collapsing the component owner to the unique connected component, only the `|V| - 1`
  -- term remains.
  rw [hUniv, Finset.sum_singleton]
  rw [hcardSupp]

/-- Helper for Theorem 4.25: on one heavy connected component, the normalized heavy-edge fiber of
the incidence vector of `T` is exactly the edge count of the induced heavy part. -/
private lemma heavyEdgeComponentFiber_eq_card_inducedHeavyPart
    (G : SimpleGraph V) [Fintype V]
    (w : G.edgeSet → ℝ) (τ : ℝ)
    (T : G.Subgraph)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    ∑ e : {e : {e : G.edgeSet // τ ≤ w e} //
        ((heavySubgraph G w τ).spanningCoe).connectedComponentMk e.1.1.out.1 = C},
      G.subgraphIncidenceVector ℝ T e.1.1 =
      Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) := by
  -- First rewrite the nested fiber to the induced-edge threshold sum on the heavy component.
  rw [heavyEdgeComponentFiber_eq_inducedHeavyFilterSum G w τ C
    (G.subgraphIncidenceVector ℝ T)]
  have hheavy :
      Finset.sum (G.inducedEdgeFinset (C.supp : Set V))
          (fun e ↦ if τ ≤ w e then G.subgraphIncidenceVector ℝ T e else 0) =
        Finset.sum (G.inducedEdgeFinset (C.supp : Set V))
          (fun e ↦ G.subgraphIncidenceVector ℝ (T ⊓ heavySubgraph G w τ) e) := by
    -- On each induced edge, the threshold guard exactly matches membership in the heavy part.
    refine Finset.sum_congr rfl ?_
    intro e he
    by_cases hτ : τ ≤ w e
    · by_cases hT : e.1 ∈ T.edgeSet
      · simp [SimpleGraph.subgraphIncidenceVector, hτ, hT, heavySubgraph_mem_edgeSet_iff]
      · simp [SimpleGraph.subgraphIncidenceVector, hτ, hT, heavySubgraph_mem_edgeSet_iff]
    · by_cases hT : e.1 ∈ T.edgeSet
      · simp [SimpleGraph.subgraphIncidenceVector, hτ, hT, heavySubgraph_mem_edgeSet_iff]
      · simp [SimpleGraph.subgraphIncidenceVector, hτ, hT, heavySubgraph_mem_edgeSet_iff]
  rw [hheavy]
  -- The remaining sum is the standard induced-edge count of the heavy part.
  have hcard :
      Nat.card (((T ⊓ heavySubgraph G w τ).induce (C.supp : Set V)).edgeSet) =
        Nat.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) :=
    natCard_edgeSet_induce_eq_card_edgeSet_spanningCoe_induce
      G (T ⊓ heavySubgraph G w τ) (C.supp : Set V)
  calc
    Finset.sum (G.inducedEdgeFinset (C.supp : Set V))
        (fun e ↦ G.subgraphIncidenceVector ℝ (T ⊓ heavySubgraph G w τ) e) =
      Fintype.card (((T ⊓ heavySubgraph G w τ).induce (C.supp : Set V)).edgeSet) := by
        simpa using
          induced_incidence_sum_eq_card_induced_edges
            G (T ⊓ heavySubgraph G w τ) C.supp.toFinset
    _ = Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) := by
        simpa [Nat.card_eq_fintype_card] using hcard

/-- Helper for Theorem 4.25: the heavy-edge threshold sum of a spanning-tree incidence vector
decomposes componentwise into the edge counts of the induced heavy parts. -/
private lemma heavyEdgeSum_subgraphIncidenceVector_eq_sum_inducedHeavyParts
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (τ : ℝ) :
    heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) =
      ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) := by
  classical
  -- First split the threshold sum by heavy connected component, then rewrite each fiber by the
  -- induced heavy-part edge count already established above.
  rw [heavyEdgeSum_eq_sum_componentFibers]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro C hC
  simpa using heavyEdgeComponentFiber_eq_card_inducedHeavyPart G w τ T C

/-- Helper for Theorem 4.25: if the induced heavy part on a heavy connected component has the
same reachability relation as the ambient heavy component graph, then it is a tree on that
component and therefore has exactly `|C.supp| - 1` edges. -/
private lemma heavyPartComponent_edgeCount_eq_card_sub_one_of_reachable_eq
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    (hreach :
      ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Reachable =
        C.toSimpleGraph.Reachable) :
    Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) =
      Fintype.card C.supp - 1 := by
  let Kc : SimpleGraph C.supp := (T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)
  haveI : Nonempty C.supp := by
    rcases C.nonempty_supp with ⟨v, hv⟩
    exact ⟨⟨v, hv⟩⟩
  have hconn : Kc.Connected := by
    -- The assumed reachability equality transports connectedness from the ambient heavy component.
    refine ⟨fun u v ↦ ?_⟩
    have hC : C.toSimpleGraph.Reachable u v := C.connected_toSimpleGraph u v
    simpa [Kc] using (hreach.symm ▸ hC)
  have hKc_le :
      Kc ≤ T.spanningCoe.induce (C.supp : Set V) := by
    -- Every edge of the induced heavy part is, in particular, an edge of the induced tree.
    intro u v huv
    rw [show Kc = (T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V) from rfl] at huv
    rw [SimpleGraph.induce_adj] at huv ⊢
    exact
      (SimpleGraph.Subgraph.spanningCoe_le_of_le
        (show T ⊓ heavySubgraph G w τ ≤ T from inf_le_left)) huv
  have hacyc : Kc.IsAcyclic := by
    -- Acyclicity descends from `T` to the induced heavy part.
    exact (hT.isAcyclic.induce (C.supp : Set V)).anti hKc_le
  have hcardAdd : Fintype.card Kc.edgeSet + 1 = Fintype.card C.supp := by
    -- Once connectedness and acyclicity are in place, the standard tree cardinality formula
    -- applies on the component vertex type `C.supp`.
    have htree : Kc.IsTree := ⟨hconn, hacyc⟩
    simpa [Nat.card_eq_fintype_card] using
      (SimpleGraph.isTree_iff_connected_and_card.mp htree).2
  have hcardKc : Fintype.card Kc.edgeSet = Fintype.card C.supp - 1 := by
    omega
  simpa [Kc] using hcardKc

/-- Helper for Theorem 4.25: once every induced heavy part has the same reachability relation as
its heavy connected component, the heavy-edge threshold sum rewrites summandwise to the component
cardinality formula. -/
private lemma heavyEdgeSum_subgraphIncidenceVector_eq_componentCardSum_of_reachable_eq
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree) (τ : ℝ)
    (hreach :
      ∀ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Reachable =
          C.toSimpleGraph.Reachable) :
    heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) =
      ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        (Fintype.card C.supp - 1 : ℝ) := by
  -- Rewrite the normalized heavy-edge decomposition term by term using the induced-tree count.
  rw [heavyEdgeSum_subgraphIncidenceVector_eq_sum_inducedHeavyParts G T τ]
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro C hC
  have hcard :
      Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) =
        Fintype.card C.supp - 1 :=
    heavyPartComponent_edgeCount_eq_card_sub_one_of_reachable_eq G T hT τ C (hreach C)
  have hpos : 1 ≤ Fintype.card C.supp := by
    rcases C.nonempty_supp with ⟨v, hv⟩
    exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  calc
    (Fintype.card (((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).edgeSet) :
        ℝ) = ((Fintype.card C.supp - 1 : ℕ) : ℝ) := by
          exact_mod_cast hcard
    _ = (Fintype.card C.supp : ℝ) - 1 := by
          rw [Nat.cast_sub hpos]
          norm_num

/-- Helper for Theorem 4.25: on each heavy connected component, the induced heavy part of a
spanning tree remains acyclic. -/
private lemma heavyPartInduce_isAcyclic
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).IsAcyclic := by
  have hKc_le :
      ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)) ≤
        T.spanningCoe.induce (C.supp : Set V) := by
    -- Every induced heavy edge is, in particular, an induced edge of the ambient tree.
    intro u v huv
    rw [SimpleGraph.induce_adj] at huv ⊢
    exact
      (SimpleGraph.Subgraph.spanningCoe_le_of_le
        (show T ⊓ heavySubgraph G w τ ≤ T from inf_le_left)) huv
  -- Acyclicity descends from the ambient spanning tree to the induced heavy part.
  exact (hT.isAcyclic.induce (C.supp : Set V)).anti hKc_le

/-- Helper for Theorem 4.25: the induced heavy part of a spanning tree sits inside the ambient
heavy component graph. -/
private lemma heavyPartInduce_le_componentGraph
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)) ≤
      C.toSimpleGraph := by
  intro u v huv
  -- Forgetting the tree constraint leaves a heavy edge inside the same heavy component.
  rw [SimpleGraph.induce_adj] at huv
  exact
    (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C u.2 v.2).2 <|
      (SimpleGraph.Subgraph.spanningCoe_le_of_le
        (show T ⊓ heavySubgraph G w τ ≤ heavySubgraph G w τ from inf_le_right)) huv

/-- Helper for Theorem 4.25: a walk in the heavy subgraph that starts in a heavy connected
component never leaves that component support. -/
private lemma walkSupport_subset_component_of_heavyWalk
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    {u v : V}
    (p : ((heavySubgraph G w τ).spanningCoe).Walk u v)
    (hu : u ∈ C.supp) :
    ∀ x, x ∈ p.support → x ∈ C.supp := by
  intro x hx
  have huC :
      ((heavySubgraph G w τ).spanningCoe).connectedComponentMk u = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C u).1 hu
  have hreach : ((heavySubgraph G w τ).spanningCoe).Reachable u x := ⟨p.takeUntil x hx⟩
  exact
    (SimpleGraph.ConnectedComponent.mem_supp_iff C x).2
      ((SimpleGraph.ConnectedComponent.sound hreach).symm.trans huC)

/-- Helper for Theorem 4.25: if every edge on a tree path is heavy, then that path lifts to the
induced heavy part on the corresponding heavy connected component. -/
private lemma treePathReachableInHeavyPart_of_allHeavy
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (p : T.spanningCoe.Walk u v) (hp : p.IsPath)
    (hheavy : ∀ e : Sym2 V, e ∈ p.edges → e ∈ (heavySubgraph G w τ).edgeSet) :
    ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Reachable
      ⟨u, hu⟩ ⟨v, hv⟩ := by
  let K : SimpleGraph V := (T ⊓ heavySubgraph G w τ).spanningCoe
  let pHeavyGraph : ((heavySubgraph G w τ).spanningCoe).Walk u v :=
    p.transfer ((heavySubgraph G w τ).spanningCoe) (fun e he ↦ by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hheavy e he)
  have hKedge : ∀ e : Sym2 V, e ∈ p.edges → e ∈ K.edgeSet := by
    intro e he
    have hTedge : e ∈ T.spanningCoe.edgeSet := p.edges_subset_edgeSet he
    have hHeavyEdge : e ∈ (heavySubgraph G w τ).spanningCoe.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hheavy e he
    -- An edge on the tree path that is also heavy lies in the spanning coercion of the heavy part.
    change e ∈ (T ⊓ heavySubgraph G w τ).edgeSet
    rw [SimpleGraph.Subgraph.edgeSet_inf]
    exact ⟨by simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hTedge, by
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using hHeavyEdge⟩
  let pHeavyPart : K.Walk u v := p.transfer K hKedge
  have hsupport : ∀ x, x ∈ pHeavyPart.support → x ∈ C.supp := by
    intro x hx
    have hxp : x ∈ p.support := by
      simpa [pHeavyPart, K] using hx
    have hxHeavy : x ∈ pHeavyGraph.support := by
      simpa [pHeavyGraph] using hxp
    exact walkSupport_subset_component_of_heavyWalk G τ C pHeavyGraph hu x hxHeavy
  -- Inducing the heavy-part walk to `C.supp` turns it into a witness in the target graph.
  simpa [K, pHeavyPart] using
    (pHeavyPart.induce (C.supp : Set V) hsupport).reachable

/-- Helper for Theorem 4.25: if the endpoints of a tree path are not reachable inside the induced
heavy part, then some edge on that path must be light. -/
private lemma existsLightEdgeOnTreePath_of_not_reachable
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent)
    {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp)
    (p : T.spanningCoe.Walk u v) (hp : p.IsPath)
    (hnreach :
      ¬ ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩) :
    ∃ f : Sym2 V, f ∈ p.edges ∧ f ∉ (heavySubgraph G w τ).edgeSet := by
  by_contra hlight
  have hallHeavy : ∀ e : Sym2 V, e ∈ p.edges → e ∈ (heavySubgraph G w τ).edgeSet := by
    intro e he
    by_contra heLight
    exact hlight ⟨e, he, heLight⟩
  -- If every path edge were heavy, the previous lifting lemma would already connect the endpoints.
  exact hnreach <|
    treePathReachableInHeavyPart_of_allHeavy G T τ C hu hv p hp hallHeavy

/-- Helper for Theorem 4.25: on each heavy connected component, the induced heavy part of a
max-weight spanning tree should be viewed as a maximal acyclic subgraph. -/
private lemma heavyPartInduce_maximalAcyclic_of_maxWeight
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree)
    (hTmax : ∀ T' : G.Subgraph, T'.IsSpanningTree → treeWeight G w T' ≤ treeWeight G w T)
    (τ : ℝ)
    (C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent) :
    Maximal
      (fun H : SimpleGraph C.supp ↦ H ≤ C.toSimpleGraph ∧ H.IsAcyclic)
      ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)) := by
  let Kc : SimpleGraph C.supp := (T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)
  have hKc_le : Kc ≤ C.toSimpleGraph := by
    -- Normalizing to `C.toSimpleGraph` isolates the remaining exchange problem.
    simpa [Kc] using heavyPartInduce_le_componentGraph G T τ C
  have hKc_acyc : Kc.IsAcyclic := by
    -- The heavy part is still a forest because it lies inside the spanning tree.
    simpa [Kc] using heavyPartInduce_isAcyclic G T hT τ C
  refine ⟨⟨hKc_le, hKc_acyc⟩, ?_⟩
  intro H hH hKH
  by_contra hHK
  have hlt : Kc < H := by
    refine lt_of_le_of_ne hKH ?_
    intro hEq
    exact hHK (hEq ▸ le_rfl)
  have hstrict : Kc.edgeSet ⊂ H.edgeSet := SimpleGraph.edgeSet_strict_mono hlt
  obtain ⟨e0, he0H, he0Kc⟩ := Set.exists_of_ssubset hstrict
  induction e0 using Sym2.ind with
  | h u v =>
      have huvH : H.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using he0H
      have hsup_le : Kc ⊔ SimpleGraph.edge u v ≤ H := by
        refine sup_le_iff.mpr ⟨hKH, ?_⟩
        rw [SimpleGraph.edge_le_iff]
        exact Or.inr huvH
      have hsupAcyc : (Kc ⊔ SimpleGraph.edge u v).IsAcyclic := hH.2.anti hsup_le
      have hnotReach : ¬ Kc.Reachable u v := by
        intro hreach
        have hacycInfo :=
          (SimpleGraph.isAcyclic_sup_fromEdgeSet_iff (G := Kc) (u := u) (v := v)).1 hsupAcyc
        have hnotAdjKc : ¬ Kc.Adj u v := by
          simpa [SimpleGraph.mem_edgeSet] using he0Kc
        rcases hacycInfo.2 hreach with hEq | hAdj
        · exact huvH.ne hEq
        · exact hnotAdjKc hAdj
      obtain ⟨p, hpPath⟩ := ExistsUnique.exists (hT.existsUnique_path u.1 v.1)
      obtain ⟨f, hfPath, hfLight⟩ :=
        existsLightEdgeOnTreePath_of_not_reachable G T τ C u.2 v.2 p hpPath (by
          simpa [Kc] using hnotReach)
      have huvC : C.toSimpleGraph.Adj u v := hH.1 huvH
      have hHeavyAdj : (heavySubgraph G w τ).Adj u.1 v.1 := by
        exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj C u.2 v.2).1 huvC
      let e : G.edgeSet := ⟨s(u.1, v.1), G.mem_edgeSet.2 hHeavyAdj.1⟩
      have heHeavy : e.1 ∈ (heavySubgraph G w τ).edgeSet := by
        -- The same component-graph edge is heavy in the ambient graph.
        simpa [e, SimpleGraph.Subgraph.mem_edgeSet] using hHeavyAdj
      have hτe : τ ≤ w e := by
        -- The heavy-subgraph membership converts immediately to the threshold inequality.
        exact (heavySubgraph_mem_edgeSet_iff G w τ e).1 heHeavy
      have he_notin_T : e.1 ∉ T.edgeSet := by
        -- Otherwise the edge would already belong to the induced heavy part `Kc`, contradicting
        -- the choice of `e0` outside `Kc`.
        intro heT
        have hKcAdj : Kc.Adj u v := by
          change ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Adj u v
          rw [SimpleGraph.induce_adj]
          change (T ⊓ heavySubgraph G w τ).Adj u.1 v.1
          rw [SimpleGraph.Subgraph.inf_adj]
          exact ⟨by simpa [e, SimpleGraph.Subgraph.mem_edgeSet] using heT, hHeavyAdj⟩
        have heKc : s(u, v) ∈ Kc.edgeSet := by
          simpa [SimpleGraph.mem_edgeSet] using hKcAdj
        exact he0Kc heKc
      have hf_in_T : f ∈ T.edgeSet := by
        -- Path edges of the unique tree path are ambient tree edges.
        simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using p.edges_subset_edgeSet hfPath
      let fE : G.edgeSet := ⟨f, T.edgeSet_subset hf_in_T⟩
      have hef_ne : e.1 ≠ f := by
        -- The exchanged-in heavy edge is not the exchanged-out light path edge.
        intro hef
        exact he_notin_T (hef ▸ hf_in_T)
      let Tex : G.Subgraph := T.deleteEdges {f} ⊔ G.subgraphOfAdj hHeavyAdj.1
      have hTex_connected : Tex.spanningCoe.Connected := by
        -- The augmented graph `T ∪ {e}` is connected, and deleting `f` preserves connectedness
        -- because `f` lies on the cycle created by the new edge.
        let Tplus : G.Subgraph := T ⊔ G.subgraphOfAdj hHeavyAdj.1
        have hTplus_connected : Tplus.spanningCoe.Connected := by
          exact hT.connected.mono
            (SimpleGraph.Subgraph.spanningCoe_le_of_le
              (show T ≤ Tplus from le_sup_left))
        let pplus : Tplus.spanningCoe.Walk u.1 v.1 :=
          p.mapLe
            (SimpleGraph.Subgraph.spanningCoe_le_of_le
              (show T ≤ Tplus from le_sup_left))
        have hpplus_edges : pplus.edges = p.edges := by
          simpa [pplus] using
            p.edges_mapLe_eq_edges
              (SimpleGraph.Subgraph.spanningCoe_le_of_le
                (show T ≤ Tplus from le_sup_left))
        have hpplus_path : pplus.IsPath := by
          simpa [pplus] using hpPath.mapLe
            (SimpleGraph.Subgraph.spanningCoe_le_of_le
              (show T ≤ Tplus from le_sup_left))
        have he_not_mem_p : e.1 ∉ p.edges := by
          intro hep
          exact he_notin_T <| by
            simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using p.edges_subset_edgeSet hep
        have he_not_mem_pplus : e.1 ∉ pplus.edges := by
          rw [hpplus_edges]
          exact he_not_mem_p
        have hplus : Tplus.spanningCoe.Adj u.1 v.1 := by
          change Tplus.Adj u.1 v.1
          dsimp [Tplus]
          exact Or.inr (SimpleGraph.subgraphOfAdj_adj_self hHeavyAdj.1)
        have hf_not_bridge :
            ¬ Tplus.spanningCoe.IsBridge s(f.out.1, f.out.2) := by
          -- The cycle obtained by closing the tree path with the new edge contains `f`.
          intro hfBridge
          have hfBridge' : Tplus.spanningCoe.IsBridge f := by
            simpa [f.out_eq] using hfBridge
          have hcycle : (SimpleGraph.Walk.cons hplus.symm pplus).IsCycle := by
            rw [SimpleGraph.Walk.cons_isCycle_iff]
            exact ⟨hpplus_path, by simpa [e, Sym2.eq_swap] using he_not_mem_pplus⟩
          have hf_in_pplus : f ∈ pplus.edges := by
            rw [hpplus_edges]
            exact hfPath
          exact (SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem.mp hfBridge').2
            (SimpleGraph.Walk.cons hplus.symm pplus) hcycle (by
              simpa [hf_in_pplus])
        have hdelete_connected :
            (Tplus.spanningCoe.deleteEdges {f}).Connected := by
          simpa [f.out_eq] using
            hTplus_connected.connected_delete_edge_of_not_isBridge
              (x := f.out.1) (y := f.out.2) hf_not_bridge
        have hne_sf : s(u.1, v.1) ≠ f := by
          simpa [e] using hef_ne
        have hkeep :
            (G.subgraphOfAdj hHeavyAdj.1).spanningCoe.deleteEdges ({f} : Set (Sym2 V)) =
              (G.subgraphOfAdj hHeavyAdj.1).spanningCoe := by
          have hsingleton :
              ({s(u.1, v.1)} : Set (Sym2 V)) \ ({f} : Set (Sym2 V)) = {s(u.1, v.1)} := by
            ext g
            by_cases hg : g = s(u.1, v.1)
            · subst hg
              simp [hne_sf]
            · simp [hg]
          calc
            (G.subgraphOfAdj hHeavyAdj.1).spanningCoe.deleteEdges ({f} : Set (Sym2 V)) =
                SimpleGraph.fromEdgeSet ({s(u.1, v.1)} \ ({f} : Set (Sym2 V))) := by
                  rw [SimpleGraph.Subgraph.spanningCoe_subgraphOfAdj,
                    SimpleGraph.deleteEdges_fromEdgeSet]
            _ = SimpleGraph.fromEdgeSet {s(u.1, v.1)} := by
                  rw [hsingleton]
            _ = (G.subgraphOfAdj hHeavyAdj.1).spanningCoe := by
                  rw [SimpleGraph.Subgraph.spanningCoe_subgraphOfAdj]
        have hTex_delete :
            Tex.spanningCoe = Tplus.spanningCoe.deleteEdges {f} := by
          calc
            Tex.spanningCoe =
                (T.deleteEdges {f}).spanningCoe ⊔ (G.subgraphOfAdj hHeavyAdj.1).spanningCoe := by
                  simp [Tex, SimpleGraph.Subgraph.sup_spanningCoe]
            _ = T.spanningCoe.deleteEdges {f} ⊔ (G.subgraphOfAdj hHeavyAdj.1).spanningCoe := by
                  rw [SimpleGraph.Subgraph.deleteEdges_spanningCoe_eq]
            _ = (T.spanningCoe ⊔ (G.subgraphOfAdj hHeavyAdj.1).spanningCoe).deleteEdges {f} := by
                  symm
                  rw [SimpleGraph.deleteEdges_sup, hkeep]
            _ = Tplus.spanningCoe.deleteEdges {f} := by
                  simp [Tplus, SimpleGraph.Subgraph.sup_spanningCoe]
        rw [hTex_delete]
        exact hdelete_connected
      have hnotReach_delete : ¬ (T.deleteEdges {f}).spanningCoe.Reachable u.1 v.1 := by
        -- Deleting a path edge destroys the unique tree path between the path endpoints.
        intro hreach
        obtain ⟨q, hqPath⟩ := hreach.exists_isPath
        let qT : T.spanningCoe.Walk u.1 v.1 :=
          q.mapLe (SimpleGraph.Subgraph.spanningCoe_deleteEdges_le T {f})
        have hqT_edges : qT.edges = q.edges := by
          simpa [qT] using
            q.edges_mapLe_eq_edges
              (SimpleGraph.Subgraph.spanningCoe_deleteEdges_le T {f})
        have hqT_path : qT.IsPath := by
          simpa [qT] using hqPath.mapLe (SimpleGraph.Subgraph.spanningCoe_deleteEdges_le T {f})
        have hqT_eq_p : qT = p := by
          exact congrArg Subtype.val <|
            hT.isAcyclic.path_unique ⟨qT, hqT_path⟩ ⟨p, hpPath⟩
        have hf_in_qT : f ∈ qT.edges := by
          simpa [hqT_eq_p] using hfPath
        have hf_in_q : f ∈ q.edges := by
          rw [← hqT_edges]
          exact hf_in_qT
        have hf_delete : f ∈ (T.deleteEdges {f}).edgeSet := by
          simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using q.edges_subset_edgeSet hf_in_q
        have hf_not_delete : f ∉ (T.deleteEdges {f}).edgeSet := by
          intro hf_delete'
          exact ((mem_edgeSet_deleteEdges_singleton_iff G T fE f).1 hf_delete').2 rfl
        exact hf_not_delete hf_delete
      have hTex_acyclic : Tex.spanningCoe.IsAcyclic := by
        -- Deleting `f` keeps the tree acyclic, and adding `e` back across the cut preserves
        -- acyclicity because the deletion disconnected the path endpoints.
        have hdelete_acyclic : (T.deleteEdges {f}).spanningCoe.IsAcyclic := by
          exact hT.isAcyclic.anti (SimpleGraph.Subgraph.spanningCoe_deleteEdges_le T {f})
        have hadd_acyclic :
            ((T.deleteEdges {f}).spanningCoe ⊔ SimpleGraph.edge u.1 v.1).IsAcyclic :=
          hdelete_acyclic.sup_edge_of_not_reachable hnotReach_delete
        simpa [Tex, e, SimpleGraph.edge, SimpleGraph.Subgraph.sup_spanningCoe,
          SimpleGraph.Subgraph.spanningCoe_subgraphOfAdj] using hadd_acyclic
      have hTex_tree : Tex.IsSpanningTree := ⟨hTex_connected, hTex_acyclic⟩
      have hdelete_coord :
          ∀ g : G.edgeSet,
            G.subgraphIncidenceVector ℝ (T.deleteEdges {f}) g =
              G.subgraphIncidenceVector ℝ T g - if g = fE then (1 : ℝ) else 0 := by
        intro g
        by_cases hgf : g = fE
        · -- At the deleted edge, the incidence drops from `1` to `0`.
          subst hgf
          have hf_not_delete : f ∉ (T.deleteEdges {f}).edgeSet := by
            intro hf_delete
            exact ((mem_edgeSet_deleteEdges_singleton_iff G T fE f).1 hf_delete).2 rfl
          simp [fE, hf_in_T, hf_not_delete, SimpleGraph.subgraphIncidenceVector]
        · by_cases hgT : g.1 ∈ T.edgeSet
          · -- Other tree edges survive the deletion unchanged.
            have hgDel : g.1 ∈ (T.deleteEdges {f}).edgeSet := by
              refine (mem_edgeSet_deleteEdges_singleton_iff G T g f).2 ?_
              refine ⟨hgT, ?_⟩
              intro hEq
              exact hgf (Subtype.ext hEq)
            simp [SimpleGraph.subgraphIncidenceVector, hgT, hgf, hgDel]
          · -- Edges outside the tree stay absent.
            have hgDel : g.1 ∉ (T.deleteEdges {f}).edgeSet := by
              intro hgDel
              exact hgT ((mem_edgeSet_deleteEdges_singleton_iff G T g f).1 hgDel).1
            simp [SimpleGraph.subgraphIncidenceVector, hgT, hgf, hgDel]
      have hTex_coord :
          ∀ g : G.edgeSet,
            G.subgraphIncidenceVector ℝ Tex g =
              G.subgraphIncidenceVector ℝ (T.deleteEdges {f}) g +
                if g = e then (1 : ℝ) else 0 := by
        intro g
        by_cases hge : g = e
        · -- The added heavy edge contributes the new `1` coordinate.
          subst hge
          have heDel : e.1 ∉ (T.deleteEdges {f}).edgeSet := by
            intro heDel
            exact he_notin_T ((mem_edgeSet_deleteEdges_singleton_iff G T e f).1 heDel).1
          have heSub : e.1 ∈ (G.subgraphOfAdj hHeavyAdj.1).edgeSet := by
            simpa [e] using (mem_edgeSet_subgraphOfAdj_iff_eq G hHeavyAdj.1 e).2 rfl
          simp [Tex, SimpleGraph.Subgraph.edgeSet_sup, SimpleGraph.subgraphIncidenceVector,
            heDel, heSub, e]
        · by_cases hgDel : g.1 ∈ (T.deleteEdges {f}).edgeSet
          · -- Existing deleted-tree edges remain present in the union.
            have hge_edge : (g : Sym2 V) ≠ s(u.1, v.1) := by
              intro hgEq
              apply hge
              apply Subtype.ext
              simpa [e] using hgEq
            have hgSub : g.1 ∉ (G.subgraphOfAdj hHeavyAdj.1).edgeSet := by
              intro hgSub
              have hEq : g = e := by
                apply Subtype.ext
                simpa [e] using (mem_edgeSet_subgraphOfAdj_iff_eq G hHeavyAdj.1 g).1 hgSub
              exact hge hEq
            simp [Tex, SimpleGraph.Subgraph.edgeSet_sup, SimpleGraph.subgraphIncidenceVector,
              hge, hge_edge, hgDel, hgSub, e]
          · -- Edges outside both pieces keep coordinate `0`.
            have hge_edge : (g : Sym2 V) ≠ s(u.1, v.1) := by
              intro hgEq
              apply hge
              apply Subtype.ext
              simpa [e] using hgEq
            have hgSub : g.1 ∉ (G.subgraphOfAdj hHeavyAdj.1).edgeSet := by
              intro hgSub
              have hEq : g = e := by
                apply Subtype.ext
                simpa [e] using (mem_edgeSet_subgraphOfAdj_iff_eq G hHeavyAdj.1 g).1 hgSub
              exact hge hEq
            simp [Tex, SimpleGraph.Subgraph.edgeSet_sup, SimpleGraph.subgraphIncidenceVector,
              hge, hge_edge, hgDel, hgSub, e]
      have hweight_delete :
          treeWeight G w (T.deleteEdges {f}) = treeWeight G w T - w fE := by
        -- Removing `f` subtracts exactly its weight from the tree objective.
        unfold treeWeight
        calc
          ∑ g : G.edgeSet, w g * G.subgraphIncidenceVector ℝ (T.deleteEdges {f}) g
              =
                ∑ g : G.edgeSet,
                  ((w g * G.subgraphIncidenceVector ℝ T g) -
                    (w g * if g = fE then (1 : ℝ) else 0)) := by
                  refine Finset.sum_congr rfl ?_
                  intro g _
                  rw [hdelete_coord g]
                  ring
          _ =
              (∑ g : G.edgeSet, w g * G.subgraphIncidenceVector ℝ T g) -
                ∑ g : G.edgeSet, w g * if g = fE then (1 : ℝ) else 0 := by
                  rw [Finset.sum_sub_distrib]
          _ = treeWeight G w T - w fE := by
                simp [treeWeight]
      have hweight_add :
          treeWeight G w Tex = treeWeight G w (T.deleteEdges {f}) + w e := by
        -- Adding `e` to the deleted tree contributes exactly the weight of `e`.
        unfold treeWeight
        calc
          ∑ g : G.edgeSet, w g * G.subgraphIncidenceVector ℝ Tex g
              =
                ∑ g : G.edgeSet,
                  ((w g * G.subgraphIncidenceVector ℝ (T.deleteEdges {f}) g) +
                    (w g * if g = e then (1 : ℝ) else 0)) := by
                  refine Finset.sum_congr rfl ?_
                  intro g _
                  rw [hTex_coord g]
                  ring
          _ =
              (∑ g : G.edgeSet, w g * G.subgraphIncidenceVector ℝ (T.deleteEdges {f}) g) +
                ∑ g : G.edgeSet, w g * if g = e then (1 : ℝ) else 0 := by
                  rw [Finset.sum_add_distrib]
          _ = treeWeight G w (T.deleteEdges {f}) + w e := by
                simp [treeWeight]
      have hτf_false : ¬ τ ≤ w fE := by
        -- The chosen path edge was light, so it lies below the threshold.
        intro hτf
        exact hfLight ((heavySubgraph_mem_edgeSet_iff G w τ fE).2 hτf)
      have hweight_lt : treeWeight G w T < treeWeight G w Tex := by
        -- The swap replaces a light edge by a heavy one, so the objective strictly increases.
        have hw_lt : w fE < w e := lt_of_lt_of_le (lt_of_not_ge hτf_false) hτe
        rw [hweight_add, hweight_delete]
        linarith
      exact (not_lt_of_ge (hTmax Tex hTex_tree)) hweight_lt

/-- Helper for Theorem 4.25: maximal acyclicity of the induced heavy part yields the reachability
equality needed by the already-stabilized heavy-edge sum rewrite. -/
private lemma heavyPartInduce_reachable_eq_componentGraph_of_maxWeight
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree)
    (hTmax : ∀ T' : G.Subgraph, T'.IsSpanningTree → treeWeight G w T' ≤ treeWeight G w T)
    (τ : ℝ) :
    ∀ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
      ((T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)).Reachable =
        C.toSimpleGraph.Reachable := by
  intro C
  let Kc : SimpleGraph C.supp := (T ⊓ heavySubgraph G w τ).spanningCoe.induce (C.supp : Set V)
  have hmax :
      Maximal (fun H : SimpleGraph C.supp ↦ H ≤ C.toSimpleGraph ∧ H.IsAcyclic) Kc := by
    -- This packages the remaining exchange step into the exact maximal-acyclic interface.
    simpa [Kc] using heavyPartInduce_maximalAcyclic_of_maxWeight G T hT hTmax τ C
  -- Mathlib turns maximal acyclicity directly into equality of reachability relations.
  simpa [Kc] using
    (SimpleGraph.reachable_eq_of_maximal_isAcyclic (G := C.toSimpleGraph) Kc hmax)

/-- Helper for Theorem 4.25: a max-weight spanning tree saturates the heavy-component cardinality
bound at every threshold. -/
private lemma heavyEdgeSum_subgraphIncidenceVector_eq_componentCardSum_of_maxWeight
    (G : SimpleGraph V) [Fintype V] {w : G.edgeSet → ℝ}
    (T : G.Subgraph) (hT : T.IsSpanningTree)
    (hTmax : ∀ T' : G.Subgraph, T'.IsSpanningTree → treeWeight G w T' ≤ treeWeight G w T)
    (τ : ℝ) :
    heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) =
      ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
        (Fintype.card C.supp - 1 : ℝ) := by
  -- Route correction: the threshold sum itself is already normalized; the only remaining work is
  -- the maximal-acyclic bridge from the heavy part of `T` to the ambient heavy component graph.
  exact
    heavyEdgeSum_subgraphIncidenceVector_eq_componentCardSum_of_reachable_eq
      G T hT τ
      (heavyPartInduce_reachable_eq_componentGraph_of_maxWeight G T hT hTmax τ)

/-- Helper for Theorem 4.25: a native linear maximum over the spanning-tree constraint set is
attained by a spanning-tree incidence vector. -/
private theorem spanningTreeConstraintSet_exists_spanningTree_maximizer
    (G : SimpleGraph V) [Fintype V] (hG : G.Connected)
    {w : G.edgeSet → ℝ} {z : ℝ}
    (hz :
      IsGreatest
        ((fun x : G.edgeSet → ℝ ↦ ∑ e : G.edgeSet, w e * x e) ''
          spanningTreeConstraintSet G)
        z) :
    ∃ T : G.Subgraph, T.IsSpanningTree ∧
      (∑ e : G.edgeSet, w e * G.subgraphIncidenceVector ℝ T e) = z := by
  -- Route correction: the remaining source-faithful greedy argument belongs on native edge
  -- coordinates after the heavy-edge helper block, so the threshold API is available by name.
  have hzmem := hz.1
  rcases hzmem with ⟨x, hx, hxz⟩
  rcases existsMaxWeightSpanningTree G hG w with ⟨T, hT, hTmax⟩
  have hdom :
      ∀ x ∈ spanningTreeConstraintSet G, ∑ e : G.edgeSet, w e * x e ≤ treeWeight G w T := by
    intro x hx
    have hxTotal :
        ∑ e : G.edgeSet, x e =
          ∑ e : G.edgeSet, G.subgraphIncidenceVector ℝ T e := by
      -- Both feasible points satisfy the same total-edge equation `|V| - 1`.
      rw [subgraphIncidenceVector_total_sum_of_spanningTree G hT]
      exact (mem_spanningTreeConstraintSet_iff.mp hx).2.1
    have hthreshold :
        ∀ τ ∈ Finset.univ.image w,
          heavyEdgeSum G w τ x ≤
            heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) := by
      intro τ hτ
      by_cases hH : ((heavySubgraph G w τ).spanningCoe).Connected
      · -- In the connected heavy case, both sides compare to the single component term `|V| - 1`.
        calc
          heavyEdgeSum G w τ x ≤ (Fintype.card V - 1 : ℝ) :=
            heavyEdgeSum_le_total_of_mem_spanningTreeConstraintSet G hx w τ
          _ =
              ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
                (Fintype.card C.supp - 1 : ℝ) :=
              (heavyComponentCardSum_eq_total_of_connected G w τ hH).symm
          _ = heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) :=
              (heavyEdgeSum_subgraphIncidenceVector_eq_componentCardSum_of_maxWeight
                G T hT hTmax τ).symm
      · -- In the disconnected heavy case, the feasible point is bounded componentwise and the
        -- max-weight tree hits the same component-cardinality total.
        calc
          heavyEdgeSum G w τ x ≤
              ∑ C : ((heavySubgraph G w τ).spanningCoe).ConnectedComponent,
                (Fintype.card C.supp - 1 : ℝ) :=
            heavyEdgeSum_le_componentCardSum_of_not_connected G hx w τ hH
          _ = heavyEdgeSum G w τ (G.subgraphIncidenceVector ℝ T) :=
              (heavyEdgeSum_subgraphIncidenceVector_eq_componentCardSum_of_maxWeight
                G T hT hTmax τ).symm
    -- Once threshold domination is packaged, the finite weight-level comparison closes the
    -- weighted objective inequality.
    simpa [treeWeight] using
      weightedObjective_le_of_thresholdDomination G w hxTotal hthreshold
  have hTreeLe : treeWeight G w T ≤ z := by
    -- The spanning-tree incidence vector is feasible, so its objective value cannot exceed the
    -- assumed optimum `z`.
    exact hz.2 ⟨G.subgraphIncidenceVector ℝ T,
      subgraphIncidenceVector_mem_spanningTreeConstraintSet G hT, by
        simp [treeWeight]⟩
  have hzLeTree : z ≤ treeWeight G w T := by
    -- The remaining native domination lemma compares the maximizing feasible point `x` to `T`.
    rw [← hxz]
    simpa [treeWeight] using hdom x hx
  refine ⟨T, hT, ?_⟩
  -- The tree objective and the optimal value coincide by the two opposite inequalities.
  simpa [treeWeight] using le_antisymm hTreeLe hzLeTree

/-- Helper for Theorem 4.25: once the native greedy certificate is available, every finite linear
optimum on the explicit Chapter 4.1 owner is attained at an integral feasible point. -/
private theorem spanningTreeConstraintPresentation_integralMaximizer_of_isGreatest
    (G : SimpleGraph V) [Fintype V] (hG : G.Connected)
    {c : Fin (Nat.card G.edgeSet) → ℝ} {z : ℝ}
    (hz :
      IsGreatest ((c ⬝ᵥ ·) '' spanningTreeConstraintPresentation G) z) :
    ∃ y ∈ spanningTreeConstraintPresentation G ∩ integerVectors (Nat.card G.edgeSet),
      c ⬝ᵥ y = z := by
  -- Route correction: this wrapper should only transport the objective and the optimal
  -- spanning-tree incidence vector between the reindexed Chapter 4.1 owner and native edge
  -- coordinates.
  have hzNative :
      IsGreatest
        ((fun x : G.edgeSet → ℝ ↦
            ∑ e : G.edgeSet, graphEdgeCoordinateReindex G c e * x e) ''
          spanningTreeConstraintSet G)
        z := by
    rw [spanningTreeConstraintSet_eq_reindexed_rational_matrix_polyhedron G]
    constructor
    · rcases hz.1 with ⟨y, hy, rfl⟩
      refine ⟨graphEdgeCoordinateReindex G y, ⟨y, hy, rfl⟩, ?_⟩
      simpa using (graphEdgeCoordinate_dotProduct_reindex G c y).symm
    · intro z' hz'
      rcases hz' with ⟨x, hx, rfl⟩
      rcases hx with ⟨y, hy, rfl⟩
      have hy_le : c ⬝ᵥ y ≤ z := hz.2 ⟨y, hy, rfl⟩
      rw [graphEdgeCoordinate_dotProduct_reindex G c y] at hy_le
      exact hy_le
  rcases spanningTreeConstraintSet_exists_spanningTree_maximizer G hG hzNative with
    ⟨T, hT, hObjective⟩
  refine ⟨graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hNative :
          graphEdgeCoordinateReindex G
              (graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T)) ∈
            spanningTreeConstraintSet G := by
        rw [graphEdgeCoordinateReindex_graphEdgeCoordinates]
        exact subgraphIncidenceVector_mem_spanningTreeConstraintSet G hT
      have hreindex :
          graphEdgeCoordinateReindex G
              (graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T)) ∈
            spanningTreeConstraintSet G ↔
              graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T) ∈
                spanningTreeConstraintPresentation G :=
        graphEdgeCoordinateReindex_mem_spanningTreeConstraintPresentation_iff G
      exact
        hreindex.1 hNative
    · rcases subgraphIncidenceVector_mem_integerRange G T with ⟨z, hz⟩
      refine ⟨fun j ↦ z ((Finite.equivFin G.edgeSet).symm j), ?_⟩
      -- Reindex the native integer witness along the canonical edge enumeration.
      funext j
      have hzj := congrFun hz ((Finite.equivFin G.edgeSet).symm j)
      simpa [graphEdgeCoordinates] using hzj
  · -- Reindex the native objective equality back to the `Fin`-indexed dot product.
    calc
      c ⬝ᵥ graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T) =
          ∑ e : G.edgeSet,
            graphEdgeCoordinateReindex G c e *
              graphEdgeCoordinateReindex G
                (graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T)) e := by
              exact
                graphEdgeCoordinate_dotProduct_reindex
                  G c (graphEdgeCoordinates G (G.subgraphIncidenceVector ℝ T))
      _ =
          ∑ e : G.edgeSet,
            graphEdgeCoordinateReindex G c e * G.subgraphIncidenceVector ℝ T e := by
              congr with e
              rw [graphEdgeCoordinateReindex_graphEdgeCoordinates]
      _ = z := hObjective

/-- Helper for Theorem 4.25: every integral feasible native point is the incidence vector of a
spanning tree. -/
private theorem integral_mem_spanningTreeVertices_of_mem_spanningTreeConstraintSet
    (G : SimpleGraph V) [Fintype V] {x : G.edgeSet → ℝ}
    (hx : x ∈ spanningTreeConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ G.spanningTreeVertices := by
  let T : G.Subgraph := integralSupportSubgraph G x
  have hT : T.IsSpanningTree :=
    integralSupportSubgraph_isSpanningTree_of_mem_spanningTreeConstraintSet_of_integer G hx hxInt
  have hxT : x = G.subgraphIncidenceVector ℝ T :=
    integralSupportSubgraph_incidence_eq_of_mem_spanningTreeConstraintSet_of_integer G hx hxInt
  -- Once the support graph is a spanning tree, the reconstructed incidence vector is one of the
  -- spanning-tree vertices.
  exact G.mem_spanningTreeVertices_iff.2 ⟨T, hT, hxT⟩

/-- Helper for Theorem 4.25: in the connected case, the reverse inclusion is exactly the remaining
source-faithful greedy-tree/dual-certificate argument from the textbook proof. -/
lemma spanningTreeConstraintSet_subset_spanningTreePolytope_of_connected
    (G : SimpleGraph V) [Fintype V] (hG : G.Connected) :
    spanningTreeConstraintSet G ⊆ G.spanningTreePolytope := by
  intro x hx
  have hPresentationRational :
      is_rational_polyhedron (spanningTreeConstraintPresentation G) := by
    -- The explicit presentation is already a rational matrix polyhedron by construction.
    rw [is_rational_polyhedron_iff]
    refine ⟨Nat.card (spanningTreeConstraintRow G), spanningTreeConstraintPresentationMatrix G,
      spanningTreeConstraintPresentationRhs G, ?_⟩
    ext y
    rfl
  have hPresentationIntegral :
      is_integral (spanningTreeConstraintPresentation G) := by
    -- Invoke Theorem 4.1 once the source-faithful optimum-attainment lemma is available.
    refine
      (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
        (spanningTreeConstraintPresentation G) hPresentationRational).2 ?_
    intro c z hz
    exact
      spanningTreeConstraintPresentation_integralMaximizer_of_isGreatest
        G hG hz
  have hNativeIntegral :
      is_integral (spanningTreeConstraintSet G) := by
    -- Transport integrality back to the native edge-coordinate owner.
    exact spanningTreeConstraintSet_isIntegral_of_presentation_isIntegral
      G hPresentationIntegral
  have hNativeEq :
      spanningTreeConstraintSet G =
        convexHull ℝ
          (spanningTreeConstraintSet G ∩
            Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :=
    (is_integral_iff).mp hNativeIntegral
  have hxHull :
      x ∈ convexHull ℝ
        (spanningTreeConstraintSet G ∩
          Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) := by
    -- The integral description rewrites the feasible point directly into the desired convex hull.
    rw [← hNativeEq]
    exact hx
  have hIntegralPoints :
      spanningTreeConstraintSet G ∩
          Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) ⊆
        G.spanningTreeVertices := by
    intro y hy
    -- The native integer-point classification is the only remaining graph-theoretic step.
    exact integral_mem_spanningTreeVertices_of_mem_spanningTreeConstraintSet
      G hy.1 hy.2
  rw [G.spanningTreePolytope_eq_convexHull]
  -- Once integer feasible points are spanning-tree vertices, convexity finishes the inclusion.
  have hHullSubset :
      convexHull ℝ
          (spanningTreeConstraintSet G ∩
            Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) ⊆
        convexHull ℝ G.spanningTreeVertices := by
    refine convexHull_min ?_ (convex_convexHull ℝ G.spanningTreeVertices)
    intro y hy
    exact subset_convexHull ℝ G.spanningTreeVertices (hIntegralPoints hy)
  exact hHullSubset hxHull

/-- Theorem 4.25. The spanning tree polytope of a finite graph `G` is described by the
edge-subset inequalities, the total-edge equation, and the nonnegativity inequalities. -/
theorem spanningTreePolytope_eq_spanningTreeConstraintSet (G : SimpleGraph V) [Fintype V] :
    G.spanningTreePolytope = spanningTreeConstraintSet G := by
  -- Route correction: the proof should first separate the disconnected case, where the source
  -- argument makes the constraint system infeasible and the polytope is already empty by
  -- `spanningTreePolytope_eq_empty_of_not_connected`.
  by_cases hG : G.Connected
  · refine le_antisymm ?_ ?_
    · -- The forward inclusion is the convex-hull packaging of the spanning-tree feasibility check.
      exact spanningTreePolytope_subset_spanningTreeConstraintSet G
    · -- The connected reverse inclusion is isolated in the dedicated helper above.
      exact spanningTreeConstraintSet_subset_spanningTreePolytope_of_connected G hG
  · -- In the disconnected case both sides are empty, exactly as in the textbook proof.
    rw [spanningTreePolytope_eq_empty_of_not_connected G hG,
      spanningTreeConstraintSet_eq_empty_of_not_connected G hG]

end Theorem_4_25

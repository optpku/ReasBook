/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_theorem_4_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open SimpleGraph

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file keeps the
-- needed `SimpleGraph.Subgraph.IsEdgeCover` definition local and reuses mathlib's
-- `SimpleGraph.lineGraph`, `SimpleGraph.chromaticNumber`, `SimpleGraph.Subgraph.IsMatching`,
-- `SimpleGraph.Subgraph.IsPerfectMatching`, and `SimpleGraph.minDegree`/`maxDegree` APIs by
-- local inspection.

universe u

namespace SimpleGraph.Subgraph

/-- A subgraph of `G` is an edge cover when every vertex of `G` is incident to one of its edges. -/
def IsEdgeCover {V : Type u} {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  H.support = Set.univ

end SimpleGraph.Subgraph

section Exercise_4_22

variable {V : Type u}
variable (G : SimpleGraph V)

/-- For matching subgraphs, being an edge-cover is exactly mathlib's canonical perfect-matching
condition. -/
lemma is_edge_cover_iff_isPerfectMatching {H : G.Subgraph} (hH : H.IsMatching) :
    H.IsEdgeCover ↔ H.IsPerfectMatching := by
  constructor
  · intro h
    exact ⟨hH, by
      simpa [Subgraph.IsEdgeCover, Subgraph.isSpanning_iff, hH.support_eq_verts] using h⟩
  · intro h
    simpa [Subgraph.IsEdgeCover, hH.support_eq_verts] using h.2.verts_eq_univ

/-- Helper for Exercise 4.22: an endpoint of an edge in the `k`-th label graph lies in the support
set used to define the corresponding subgraph. -/
lemma mem_edge_label_support {K : Type*} (C : G.EdgeLabeling K) (k : K) {v w : V}
    (hvw : (C.labelGraph k).Adj v w) :
    v ∈ {u : V | ∃ x, (C.labelGraph k).Adj u x} := by
  -- The support set is defined by existence of an incident edge in the chosen label graph.
  exact ⟨w, hvw⟩

/-- Helper for Exercise 4.22: if two graph edges share the same chosen endpoint, equality of the
corresponding `Sym2` edges forces equality of the opposite endpoints. -/
lemma eq_of_incident_sym2_eq {v w₁ w₂ : V} (_hvw₁ : G.Adj v w₁) (hvw₂ : G.Adj v w₂)
    (h : s(v, w₁) = s(v, w₂)) :
    w₁ = w₂ := by
  -- Unordered edge equality has only the direct or swapped case, and the swapped case would
  -- create a forbidden loop.
  have h' : (v = v ∧ w₁ = w₂) ∨ (v = w₂ ∧ w₁ = v) := by
    simpa using (Sym2.eq).1 h
  rcases h' with h' | h'
  · exact h'.2
  · exact False.elim (hvw₂.ne h'.1)

/-- The `k`-th color class of an edge-labeling, viewed as a subgraph of the ambient graph `G`. -/
abbrev edgeLabelSubgraph (G : SimpleGraph V) {K : Type*} (C : G.EdgeLabeling K) (k : K) :
    G.Subgraph where
  verts := {v : V | ∃ w, (C.labelGraph k).Adj v w}
  Adj := (C.labelGraph k).Adj
  adj_sub := fun h ↦ C.labelGraph_le h
  edge_vert := mem_edge_label_support G C k
  symm := (C.labelGraph k).symm

/-- Helper for Exercise 4.22: adjacency in the label subgraph is exactly adjacency in `G`
with the specified label. -/
lemma edgeLabelSubgraph_adj_iff {K : Type*} (C : G.EdgeLabeling K) {k : K} {v w : V} :
    (edgeLabelSubgraph G C k).Adj v w ↔ ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = k := by
  -- The repaired subgraph keeps the label graph adjacency relation unchanged.
  exact EdgeLabeling.labelGraph_adj v w

/-- An edge-labeling is proper when each color class is a matching. -/
def IsProperEdgeLabeling (G : SimpleGraph V) {K : Type*} (C : G.EdgeLabeling K) : Prop :=
  ∀ k, (edgeLabelSubgraph G C k).IsMatching

/-- Helper for Exercise 4.22: a proper edge-labeling separates adjacent vertices in the line
graph. -/
lemma lineGraphColoringOfIsProperEdgeLabeling_valid {K : Type*} (C : G.EdgeLabeling K)
    (hC : IsProperEdgeLabeling G C) :
    ∀ {e₁ e₂ : G.edgeSet}, G.lineGraph.Adj e₁ e₂ → C e₁ ≠ C e₂ := by
  intro e₁ e₂ hAdj
  -- Adjacent line-graph vertices correspond to incident edges in `G`, so one color would create
  -- two edges through the same vertex inside a matching color class.
  rcases (SimpleGraph.lineGraph_adj_iff_exists).1 hAdj with ⟨hne, v, hv₁, hv₂⟩
  intro hEq
  let w₁ : V := Sym2.Mem.other hv₁
  let w₂ : V := Sym2.Mem.other hv₂
  have hw₁ : v ∈ (e₁ : Sym2 V) := hv₁
  have hw₂ : v ∈ (e₂ : Sym2 V) := hv₂
  have he₁ : (e₁ : Sym2 V) = s(v, w₁) := by
    simp [w₁]
  have he₂ : (e₂ : Sym2 V) = s(v, w₂) := by
    simp [w₂]
  have hadj₁ : G.Adj v w₁ := by
    have hs : s(v, w₁) ∈ G.edgeSet := by
      rw [← he₁]
      exact e₁.2
    exact (G.mem_edgeSet).1 hs
  have hadj₂ : G.Adj v w₂ := by
    have hs : s(v, w₂) ∈ G.edgeSet := by
      rw [← he₂]
      exact e₂.2
    exact (G.mem_edgeSet).1 hs
  let edge₁ : G.edgeSet := ⟨s(v, w₁), (G.mem_edgeSet).2 hadj₁⟩
  let edge₂ : G.edgeSet := ⟨s(v, w₂), (G.mem_edgeSet).2 hadj₂⟩
  have hedge₁ : edge₁ = e₁ := by
    apply Subtype.ext
    exact he₁.symm
  have hedge₂ : edge₂ = e₂ := by
    apply Subtype.ext
    exact he₂.symm
  have hsub₁ : (edgeLabelSubgraph G C (C e₁)).Adj v w₁ := by
    rw [edgeLabelSubgraph_adj_iff]
    refine ⟨hadj₁, ?_⟩
    simpa [edge₁] using congrArg C hedge₁
  have hsub₂ : (edgeLabelSubgraph G C (C e₁)).Adj v w₂ := by
    rw [edgeLabelSubgraph_adj_iff]
    refine ⟨hadj₂, ?_⟩
    calc
      C edge₂ = C e₂ := by simpa [edge₂] using congrArg C hedge₂
      _ = C e₁ := hEq.symm
  have hMatch : (edgeLabelSubgraph G C (C e₁)).IsMatching := hC (C e₁)
  have hw : w₁ = w₂ := hMatch.eq_of_adj_left hsub₁ hsub₂
  have he : e₁ = e₂ := by
    apply Subtype.ext
    rw [he₁, he₂, hw]
  exact hne he

/-- A proper edge-labeling of `G` induces a coloring of its line graph. -/
def lineGraphColoringOfIsProperEdgeLabeling {K : Type*} (C : G.EdgeLabeling K)
    (hC : IsProperEdgeLabeling G C) : G.lineGraph.Coloring K :=
  SimpleGraph.Coloring.mk C (lineGraphColoringOfIsProperEdgeLabeling_valid G C hC)

/-- Helper for Exercise 4.22: every color class of a line-graph coloring is a matching in the
original graph. -/
lemma edgeLabelSubgraph_isMatching_of_lineGraphColoring {K : Type*} (C : G.lineGraph.Coloring K)
    (k : K) :
    (edgeLabelSubgraph G (fun e ↦ C e) k).IsMatching := by
  intro v hv
  -- A vertex belongs to the repaired color class precisely when some `k`-colored edge meets it.
  change ∃ w, (edgeLabelSubgraph G (fun e ↦ C e) k).Adj v w at hv
  rcases hv with ⟨w₀, hw₀⟩
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw
  by_cases hEq : w = w₀
  · exact hEq
  · have hadj₀ : G.Adj v w₀ := (edgeLabelSubgraph G (fun e ↦ C e) k).adj_sub hw₀
    have hadj : G.Adj v w := (edgeLabelSubgraph G (fun e ↦ C e) k).adj_sub hw
    let e₀ : G.edgeSet := ⟨s(v, w₀), (G.mem_edgeSet).2 hadj₀⟩
    let e : G.edgeSet := ⟨s(v, w), (G.mem_edgeSet).2 hadj⟩
    have hLine : G.lineGraph.Adj e₀ e := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨?_, v, ?_, ?_⟩
      · intro hEdge
        have hSym2 : s(v, w₀) = s(v, w) := by
          simpa [e₀, e] using (Subtype.ext_iff.mp hEdge)
        apply hEq
        exact (eq_of_incident_sym2_eq (G := G) (v := v) (w₁ := w₀) (w₂ := w) hadj₀ hadj hSym2).symm
      · change v ∈ s(v, w₀)
        simp [hadj₀.ne]
      · change v ∈ s(v, w)
        simp [hadj.ne]
    have hk₀ : C e₀ = k := by
      rw [edgeLabelSubgraph_adj_iff] at hw₀
      rcases hw₀ with ⟨_, hk₀⟩
      exact hk₀
    have hk : C e = k := by
      rw [edgeLabelSubgraph_adj_iff] at hw
      rcases hw with ⟨_, hk⟩
      exact hk
    exact False.elim ((C.valid hLine) (hk₀.trans hk.symm))

/-- A coloring of the line graph is the same data as a proper edge-labeling of the original
graph. -/
lemma isProperEdgeLabeling_of_lineGraphColoring {K : Type*} (C : G.lineGraph.Coloring K) :
    IsProperEdgeLabeling G (fun e ↦ C e) := by
  -- Each color class is a matching because two same-colored incident edges would violate the
  -- line-graph coloring condition.
  intro k
  exact edgeLabelSubgraph_isMatching_of_lineGraphColoring G C k

/-- Proper edge-labelings of `G` with `n` colors are exactly `n`-colorings of the line graph. -/
lemma lineGraph_colorable_iff_exists_isProperEdgeLabeling {n : ℕ} :
    G.lineGraph.Colorable n ↔ ∃ C : G.EdgeLabeling (Fin n), IsProperEdgeLabeling G C := by
  constructor
  · rintro ⟨C⟩
    exact ⟨fun e ↦ C e, isProperEdgeLabeling_of_lineGraphColoring G C⟩
  · rintro ⟨C, hC⟩
    exact ⟨lineGraphColoringOfIsProperEdgeLabeling G C hC⟩

/-- A finite family of pairwise edge-disjoint edge-cover subgraphs of `G`. -/
def edge_cover_packing (G : SimpleGraph V) (F : Finset G.Subgraph) : Prop :=
  (∀ H ∈ F, H.IsEdgeCover) ∧
    (↑F : Set G.Subgraph).Pairwise (fun H H' ↦ Disjoint H.edgeSet H'.edgeSet)

/-- The maximum number of pairwise edge-disjoint edge-covers of a finite graph `G`. -/
def maximum_disjoint_edge_covers [Finite V] (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset G.Subgraph, edge_cover_packing G F ∧ F.card = k}

variable [Fintype V]
variable [DecidableRel G.Adj]

/-- Helper for Exercise 4.22: every proper edge-labeling of `G` uses at least `Δ(G)` colors,
because a vertex of maximum degree needs a different color on each incident edge. -/
lemma maxDegree_le_card_of_isProper {K : Type*} [Fintype K]
    (C : G.EdgeLabeling K) (hC : IsProperEdgeLabeling G C) :
    G.maxDegree ≤ Fintype.card K := by
  rcases isEmpty_or_nonempty V with hV | hV
  · -- In the empty-vertex case the maximum degree is already zero.
    simp [maxDegree_of_isEmpty]
  · rcases G.exists_maximal_degree_vertex with ⟨v, hv⟩
    let colorOfNeighbor : G.neighborSet v → K :=
      fun w ↦ C ⟨s(v, (w : V)), (G.mem_edgeSet).2 w.property⟩
    have colorOfNeighbor_injective : Function.Injective colorOfNeighbor := by
      intro w₁ w₂ hEq
      -- Two incident edges with the same color lie in the same matching color class.
      have hw₁ :
          (edgeLabelSubgraph G C (colorOfNeighbor w₁)).Adj v (w₁ : V) := by
        change (C.labelGraph (colorOfNeighbor w₁)).Adj v (w₁ : V)
        exact (EdgeLabeling.labelGraph_adj v (w₁ : V)).2 ⟨w₁.property, rfl⟩
      have hw₂ :
          (edgeLabelSubgraph G C (colorOfNeighbor w₁)).Adj v (w₂ : V) := by
        change (C.labelGraph (colorOfNeighbor w₁)).Adj v (w₂ : V)
        exact (EdgeLabeling.labelGraph_adj v (w₂ : V)).2 ⟨w₂.property, hEq.symm⟩
      have hMatch :
          (edgeLabelSubgraph G C (colorOfNeighbor w₁)).IsMatching :=
        hC _
      exact Subtype.ext (hMatch.eq_of_adj_left hw₁ hw₂)
    -- Injecting the neighbors of `v` into the family gives the desired degree bound.
    calc
      G.maxDegree = Fintype.card (G.neighborSet v) := by
        rw [hv, card_neighborSet_eq_degree]
      _ ≤ Fintype.card K := Fintype.card_le_of_injective colorOfNeighbor colorOfNeighbor_injective

/-- Helper for Exercise 4.22: every packing of pairwise edge-disjoint edge-covers has cardinality
at most the minimum degree, because each packed cover must use a distinct edge at a fixed vertex. -/
lemma edge_cover_packing_card_le_minDegree
    [Nonempty V] (F : Finset G.Subgraph) (hF : edge_cover_packing G F) :
    F.card ≤ G.minDegree := by
  classical
  rcases hF with ⟨hEdgeCover, hDisjoint⟩
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  have cover_meets_vertex :
      ∀ H : {H // H ∈ F}, ∃ w : G.neighborSet v, H.1.Adj v (w : V) := by
    intro H
    -- An edge-cover must hit every vertex, in particular the chosen vertex `v`.
    have hvSupport : v ∈ H.1.support := by
      rw [hEdgeCover _ H.2]
      simp
    rcases (show ∃ w, H.1.Adj v w from hvSupport) with ⟨w, hw⟩
    exact ⟨⟨w, H.1.adj_sub hw⟩, hw⟩
  let neighborOfCover : {H // H ∈ F} → G.neighborSet v :=
    fun H ↦ Classical.choose (cover_meets_vertex H)
  have neighborOfCover_adj :
      ∀ H : {H // H ∈ F}, H.1.Adj v (neighborOfCover H : V) :=
    fun H ↦ (Classical.choose_spec (cover_meets_vertex H))
  have neighborOfCover_injective : Function.Injective neighborOfCover := by
    intro H₁ H₂ hEq
    by_cases hHH : H₁.1 = H₂.1
    · exact Subtype.ext hHH
    · -- Distinct packed covers cannot share the same chosen incident edge at `v`.
      have hEdge₁ :
          s(v, (neighborOfCover H₁ : V)) ∈ H₁.1.edgeSet :=
        Subgraph.mem_edgeSet.2 (neighborOfCover_adj H₁)
      have hEdge₂ :
          s(v, (neighborOfCover H₁ : V)) ∈ H₂.1.edgeSet := by
        simpa [hEq] using
          Subgraph.mem_edgeSet.2 (neighborOfCover_adj H₂)
      have hSep :
          Disjoint H₁.1.edgeSet H₂.1.edgeSet :=
        hDisjoint H₁.2 H₂.2 hHH
      rw [Set.disjoint_left] at hSep
      exact False.elim (hSep hEdge₁ hEdge₂)
  have hCard :
      F.card ≤ Fintype.card (G.neighborSet v) := by
    simpa [Finset.card_attach] using
      (Finset.card_le_card_of_injOn neighborOfCover
        (fun H _ ↦ by simp)
        (by
          intro H₁ _ H₂ _ hEq
          exact neighborOfCover_injective hEq) :
        F.attach.card ≤ (Finset.univ : Finset (G.neighborSet v)).card)
  -- Injecting the packed covers into the neighbors of `v` bounds the packing size by `degree v`.
  calc
    F.card ≤ Fintype.card (G.neighborSet v) := hCard
    _ = G.degree v := by rw [card_neighborSet_eq_degree]
    _ = G.minDegree := hv.symm

/-- Helper for Exercise 4.22: incident edges in `G.edgeSet` are counted by the degree. -/
lemma incident_edge_card_eq_degree (v : V) :
    Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} = G.degree v := by
  let incidentEquiv : {e : G.edgeSet // v ∈ (e : Sym2 V)} ≃ G.incidenceSet v :=
    { toFun := fun e ↦ ⟨e.1, e.1.2, e.2⟩
      invFun := fun e ↦ ⟨⟨e.1, e.2.1⟩, e.2.2⟩
      left_inv := by
        intro e
        cases e
        rfl
      right_inv := by
        intro e
        cases e
        rfl }
  -- The incident-edge subtype is equivalent to the incidence-set subtype already used for
  -- `degree`.
  calc
    Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} = Fintype.card (G.incidenceSet v) :=
      Fintype.card_congr incidentEquiv
    _ = G.degree v := G.card_incidenceSet_eq_degree v

/-- Helper for Exercise 4.22: the universal finset of incident edges has cardinality `degree v`. -/
lemma incident_edge_filter_card_eq_degree (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card = G.degree v := by
  -- Realize the filtered universal finset as the canonical fintype on the incident-edge subtype.
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card =
        Fintype.card {e : G.edgeSet // v ∈ (e : Sym2 V)} := by
          symm
          exact Fintype.card_ofFinset
            (p := {e : G.edgeSet | v ∈ (e : Sym2 V)})
            (Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V))
            (fun e ↦ by simp)
    _ = G.degree v := incident_edge_card_eq_degree G v

/-- Helper for Exercise 4.22: summing the color-sliced row sums over all colors recovers the full
row sum. -/
lemma sum_column_color_sum_eq_row_sum
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) (i : Fin m) :
    (∑ c : Fin k, column_color_sum A κ c i) = ∑ j : Fin n, A i j := by
  -- Rewrite filtered sums as indicator sums, then let each column contribute once at its own
  -- color.
  unfold column_color_sum
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp

/-- Helper for Exercise 4.22: reindexing the edge-incidence matrix along `Finite.equivFin`
transports the selected `Fin` entry back to the original edge-set entry. -/
lemma reindexed_edgeIncMatrix_apply (v : V) (j : Fin (Nat.card G.edgeSet)) :
    (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
      (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j =
      G.edgeIncMatrix ℤ v ((Finite.equivFin G.edgeSet).symm j) := by
  -- Unfold the matrix reindexing once so the selected `Fin`-entry becomes the original
  -- edge-indexed incidence entry.
  rw [Matrix.reindex_apply]
  simp [Matrix.submatrix_apply]

/-- Helper for Exercise 4.22: the reindexed edge-incidence entry is the `0/1` indicator that the
chosen vertex is an endpoint of the chosen edge. -/
lemma edge_incidence_entry_reindexed_is_indicator (v : V) (j : Fin (Nat.card G.edgeSet)) :
    (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
      (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j =
      if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) then 1 else 0 := by
  -- Route correction: make the transported entry explicit as a `0/1` endpoint indicator before
  -- taking any sums, so later counting lemmas avoid brittle `Finite.equivFin` reductions.
  rw [reindexed_edgeIncMatrix_apply]
  -- Split on whether the chosen vertex is an endpoint of the chosen edge.
  by_cases h :
      v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V))
  · have hinc :
        (((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V) ∈ G.incidenceSet v := by
      simpa [SimpleGraph.edge_mem_incidenceSet_iff] using h
    rw [if_pos h]
    simpa [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply] using
      G.incMatrix_of_mem_incidenceSet (R := ℤ) hinc
  · have hinc :
        (((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V) ∉ G.incidenceSet v := by
      simpa [SimpleGraph.edge_mem_incidenceSet_iff] using h
    rw [if_neg h]
    simpa [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply] using
      G.incMatrix_of_notMem_incidenceSet (R := ℤ) hinc

/-- Helper for Exercise 4.22: the reindexed edge-incidence row sum at `v` equals `degree v`. -/
lemma reindexed_edgeIncMatrix_row_sum_eq_degree (v : V) :
    (∑ j : Fin (Nat.card G.edgeSet),
        (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
          (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j) = G.degree v := by
  -- First rewrite the row as the sum of endpoint indicators over the reindexed edge columns.
  calc
    ∑ j : Fin (Nat.card G.edgeSet),
        (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
          (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j =
      ∑ j : Fin (Nat.card G.edgeSet),
        if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) then (1 : ℤ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simpa using edge_incidence_entry_reindexed_is_indicator (G := G) v j
    -- Reindex the finite sum back from `Fin` to the actual edge-set type.
    _ = ∑ e : G.edgeSet, if v ∈ (e : Sym2 V) then (1 : ℤ) else 0 := by
          symm
          exact Fintype.sum_equiv (Finite.equivFin G.edgeSet)
            (fun e : G.edgeSet ↦ if v ∈ (e : Sym2 V) then (1 : ℤ) else 0)
            (fun j : Fin (Nat.card G.edgeSet) ↦
              if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) then
                (1 : ℤ)
              else
                0)
            (fun e ↦ by
              have he : (Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) = e :=
                by simpa using Equiv.symm_apply_apply (Finite.equivFin G.edgeSet) e
              have hsym2 :
                  ((((Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) : G.edgeSet) :
                    Sym2 V)) = (e : Sym2 V) := by
                simpa using congrArg (fun x : G.edgeSet ↦ (x : Sym2 V)) he
              change (if v ∈ (e : Sym2 V) then (1 : ℤ) else 0) =
                if v ∈ ((((Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) :
                  G.edgeSet) : Sym2 V)) then (1 : ℤ) else 0
              rw [hsym2])
    -- A sum of `0/1` indicators is exactly the cardinality of the filtered edge set.
    _ = ((Finset.univ.filter fun e : G.edgeSet ↦ v ∈ (e : Sym2 V)).card : ℤ) := by
          simpa using
            (Finset.sum_boole (R := ℤ)
              (p := fun e : G.edgeSet ↦ v ∈ (e : Sym2 V))
              (s := Finset.univ))
    _ = G.degree v := by
          exact congrArg (fun n : ℕ ↦ (n : ℤ)) (incident_edge_filter_card_eq_degree (G := G) v)

/-- Helper for Exercise 4.22: for the reindexed edge-incidence matrix, a row/color sum is exactly
the number of incident edges carrying that color. -/
lemma column_color_sum_edgeIncMatrix_eq_incident_color_count
    {k : ℕ} (κ : Fin (Nat.card G.edgeSet) → Fin k) (c : Fin k) (v : V) :
    column_color_sum
        (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
          (G.edgeIncMatrix ℤ))
        κ c ((Finite.equivFin V) v) =
      ((Finset.univ.filter fun e : G.edgeSet ↦
          v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c).card : ℤ) := by
  unfold column_color_sum
  rw [Finset.sum_filter]
  -- Rewrite the row entries to the endpoint-indicator form before regrouping by actual edges.
  calc
    (∑ j : Fin (Nat.card G.edgeSet),
        if κ j = c then
          (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
            (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j
        else
          (0 : ℤ)) =
      (∑ j : Fin (Nat.card G.edgeSet),
        if κ j = c then
          (if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) then (1 : ℤ) else 0)
        else
          (0 : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hjc : κ j = c
            · simp [hjc]
              simpa using edge_incidence_entry_reindexed_is_indicator (G := G) v j
            · simp [hjc]
    -- Combine the color test and endpoint test into one indicator.
    _ =
      (∑ j : Fin (Nat.card G.edgeSet),
        if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) ∧ κ j = c then
          (1 : ℤ)
        else
          (0 : ℤ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hjc : κ j = c <;>
              by_cases hv :
                v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) <;>
                simp [hjc, hv, and_assoc, and_left_comm, and_comm]
    -- Reindex the filtered sum from `Fin` back to the actual edge set.
    _ =
      (∑ e : G.edgeSet,
        if v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c then (1 : ℤ) else 0) := by
          symm
          exact Fintype.sum_equiv (Finite.equivFin G.edgeSet)
            (fun e : G.edgeSet ↦
              if v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c then (1 : ℤ) else 0)
            (fun j : Fin (Nat.card G.edgeSet) ↦
              if v ∈ ((((Finite.equivFin G.edgeSet).symm j : G.edgeSet) : Sym2 V)) ∧ κ j = c then
                (1 : ℤ)
              else
                0)
            (fun e ↦ by
              have he : (Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) = e :=
                by simpa using Equiv.symm_apply_apply (Finite.equivFin G.edgeSet) e
              have hsym2 :
                  ((((Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) : G.edgeSet) :
                    Sym2 V)) = (e : Sym2 V) := by
                simpa using congrArg (fun x : G.edgeSet ↦ (x : Sym2 V)) he
              change
                (if v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c then (1 : ℤ) else 0) =
                  if
                      v ∈ ((((Finite.equivFin G.edgeSet).symm ((Finite.equivFin G.edgeSet) e) :
                        G.edgeSet) : Sym2 V)) ∧
                        κ ((Finite.equivFin G.edgeSet) e) = c then
                    (1 : ℤ)
                  else
                    0
              rw [hsym2])
    -- The remaining `0/1` sum is the desired filtered cardinality.
    _ = ((Finset.univ.filter fun e : G.edgeSet ↦
        v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c).card : ℤ) := by
          simpa using
            (Finset.sum_boole (R := ℤ)
              (p := fun e : G.edgeSet ↦
                v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c)
              (s := Finset.univ))

/-- Helper for Exercise 4.22: the sum of `1`s over all colors other than `c` is `k - 1`. -/
lemma sum_ones_erase_fin
    {k : ℕ} (hk : 0 < k) (c : Fin k) :
    Finset.sum (Finset.univ.erase c) (fun _ : Fin k ↦ (1 : ℤ)) = (k : ℤ) - 1 := by
  -- Normalize the erased tail by its cardinality and the fact that `Fin k` has exactly `k`
  -- elements.
  calc
    Finset.sum (Finset.univ.erase c) (fun _ : Fin k ↦ (1 : ℤ)) =
        ((Finset.univ.erase c).card : ℤ) := by
      simp
    _ = (k : ℤ) - 1 := by
      have hcard : (Finset.univ.erase c).card = k - 1 := by
        simpa [Finset.card_univ, hk.ne'] using
          Finset.card_erase_of_mem (s := (Finset.univ : Finset (Fin k))) (by simp : c ∈ Finset.univ)
      rw [hcard]
      have hk' : (1 : ℤ) ≤ k := by
        exact_mod_cast hk
      omega

/-- Helper for Exercise 4.22: balanced nonnegative counts with total sum at most the number of
colors must all be at most `1`. -/
lemma pairwise_balanced_counts_le_one_of_sum_le_card
    {k : ℕ} (hk : 0 < k) {a : Fin k → ℤ}
    (hnonneg : ∀ c, 0 ≤ a c)
    (hbal : ∀ c d, Int.natAbs (a c - a d) ≤ 1)
    (hsum : ∑ c, a c ≤ k) :
    ∀ c, a c ≤ 1 := by
  -- Reuse the Exercise 4.11 contradiction template with the present stronger balance hypothesis.
  exact
    balanced_color_sums_le_rhs_of_total_bound (hk := hk) (B := 1)
      (hbalanced := fun c d _ ↦ hbal c d)
      (by simpa using hsum)

/-- Helper for Exercise 4.22: balanced nonnegative counts with total sum at least the number of
colors must all be at least `1`. -/
lemma one_le_pairwise_balanced_counts_of_card_le_sum
    {k : ℕ} (hk : 0 < k) {a : Fin k → ℤ}
    (hnonneg : ∀ c, 0 ≤ a c)
    (hbal : ∀ c d, Int.natAbs (a c - a d) ≤ 1)
    (hsum : (k : ℤ) ≤ ∑ c, a c) :
    ∀ c, 1 ≤ a c := by
  intro c
  by_contra hc
  -- If one color vanishes, balance forces every other count to be at most `1`.
  have hc0 : a c = 0 := by
    have hle : a c ≤ 0 := by
      linarith
    linarith [hnonneg c, hle]
  have hall : ∀ d : Fin k, a d ≤ 1 := by
    intro d
    by_cases hdc : d = c
    · simpa [hdc, hc0]
    · have habs : |a d - a c| ≤ 1 := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hbal d c
      rcases Int.abs_le_one_iff.mp habs with hdiff | hdiff | hdiff <;> linarith [hnonneg d, hc0]
  have hrest :
      Finset.sum (Finset.univ.erase c) a ≤
        Finset.sum (Finset.univ.erase c) (fun _ : Fin k ↦ (1 : ℤ)) := by
    exact Finset.sum_le_sum fun d hd ↦ hall d
  have hsplit : (∑ d : Fin k, a d) = a c + Finset.sum (Finset.univ.erase c) a := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := Finset.univ) (a := c) (f := a) (by simp)).symm
  have hsmall : ∑ d : Fin k, a d ≤ (k : ℤ) - 1 := by
    rw [hsplit, hc0, zero_add]
    calc
      Finset.sum (Finset.univ.erase c) a ≤
          Finset.sum (Finset.univ.erase c) (fun _ : Fin k ↦ (1 : ℤ)) := hrest
      _ = (k : ℤ) - 1 := sum_ones_erase_fin hk c
  have hcontr : (k : ℤ) ≤ (k : ℤ) - 1 := le_trans hsum hsmall
  linarith

/-- Helper for Exercise 4.22: if the maximum degree is zero, then the graph has no edges. -/
lemma edgeSet_isEmpty_of_maxDegree_eq_zero (hΔ : G.maxDegree = 0) : IsEmpty G.edgeSet := by
  refine ⟨fun e ↦ ?_⟩
  rcases e with ⟨e, he⟩
  -- Unpack the edge to one endpoint; that endpoint would have positive degree, contradicting
  -- `maxDegree = 0`.
  induction e using Sym2.inductionOn with
  | hf v w =>
      have hadj : G.Adj v w := (G.mem_edgeSet).1 he
      have hpos : 0 < G.degree v := hadj.degree_pos_left
      have hbound : G.degree v ≤ 0 := by
        simpa [hΔ] using G.degree_le_maxDegree v
      exact (Nat.not_lt_of_ge hbound) hpos

/-- Helper for Exercise 4.22: an equitable coloring already satisfies the row-balance bound for
all color pairs, with the diagonal case trivial. -/
lemma equitable_balance_all_pairs
    {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (κ : Fin n → Fin k) (hκ : equitable_k_coloring A κ) :
    ∀ c d : Fin k, ∀ i : Fin m,
      Int.natAbs (column_color_sum A κ c i - column_color_sum A κ d i) ≤ 1 := by
  intro c d i
  -- The source hypothesis only omits the diagonal case, which reduces to `0`.
  by_cases hcd : c = d
  · subst hcd
    simp
  · exact hκ c d hcd i

/-- Helper for Exercise 4.22: distinct label subgraphs have disjoint edge sets. -/
lemma edgeLabelSubgraph_edgeSet_disjoint {K : Type*} (C : G.EdgeLabeling K) {c d : K}
    (hcd : c ≠ d) :
    Disjoint (edgeLabelSubgraph G C c).edgeSet (edgeLabelSubgraph G C d).edgeSet := by
  -- The repaired subgraphs keep exactly the edges of the corresponding label graphs.
  rw [Set.disjoint_left]
  intro e hec hed
  induction e using Sym2.inductionOn with
  | hf v w =>
      have hvc : (C.labelGraph c).Adj v w := by
        simpa [edgeLabelSubgraph] using (Subgraph.mem_edgeSet.1 hec)
      have hvd : (C.labelGraph d).Adj v w := by
        simpa [edgeLabelSubgraph] using (Subgraph.mem_edgeSet.1 hed)
      exact (SimpleGraph.disjoint_left.1
        (EdgeLabeling.pairwise_disjoint_labelGraph (C := C) hcd) v w hvc) hvd

/-- Helper for Exercise 4.22: an equitable coloring of the reindexed edge-incidence matrix yields
an edge-labeling whose color classes are matchings. -/
lemma isProperEdgeLabeling_of_equitable_incidence_coloring
    {k : ℕ} (hk : 0 < k) (κ : Fin (Nat.card G.edgeSet) → Fin k)
    (hκ : equitable_k_coloring
      (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
        (G.edgeIncMatrix ℤ)) κ)
    (hdeg : ∀ v : V, G.degree v ≤ k) :
    IsProperEdgeLabeling G (fun e ↦ κ ((Finite.equivFin G.edgeSet) e)) := by
  let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
    Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)
  intro c
  intro v hv
  change ∃ w, (edgeLabelSubgraph G (fun e ↦ κ ((Finite.equivFin G.edgeSet) e)) c).Adj v w at hv
  rcases hv with ⟨w₀, hw₀⟩
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw
  let S : Finset G.edgeSet := Finset.univ.filter fun e : G.edgeSet ↦
    v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c
  let a : Fin k → ℤ := fun d ↦ column_color_sum A κ d ((Finite.equivFin V) v)
  -- The equitable row-balance plus the degree bound forces each incident color count to be at
  -- most `1`.
  have hcard_le_one : (S.card : ℤ) ≤ 1 := by
    have hnonneg : ∀ d, 0 ≤ a d := by
      intro d
      have hcount :
          a d =
            ((Finset.univ.filter fun e : G.edgeSet ↦
                v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = d).card : ℤ) := by
        dsimp [a]
        simpa [A] using
          (column_color_sum_edgeIncMatrix_eq_incident_color_count
            (G := G) (κ := κ) (c := d) (v := v))
      rw [hcount]
      exact_mod_cast Nat.zero_le
        ((Finset.univ.filter fun e : G.edgeSet ↦
          v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = d).card)
    have hbal : ∀ d d' : Fin k, Int.natAbs (a d - a d') ≤ 1 := by
      intro d d'
      simpa [a, A] using equitable_balance_all_pairs A κ hκ d d' ((Finite.equivFin V) v)
    have hsum : ∑ d, a d ≤ k := by
      calc
        ∑ d, a d = ∑ d : Fin k, column_color_sum A κ d ((Finite.equivFin V) v) := by
          rfl
        _ = ∑ j : Fin (Nat.card G.edgeSet), A ((Finite.equivFin V) v) j := by
          simpa using sum_column_color_sum_eq_row_sum A κ ((Finite.equivFin V) v)
        _ = G.degree v := by
          dsimp [A]
          exact reindexed_edgeIncMatrix_row_sum_eq_degree (G := G) v
        _ ≤ k := by
          exact_mod_cast hdeg v
    have hc_le_one : a c ≤ 1 :=
      pairwise_balanced_counts_le_one_of_sum_le_card
        (hk := hk) hnonneg hbal hsum c
    have hcount :
        a c =
          ((Finset.univ.filter fun e : G.edgeSet ↦
              v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c).card : ℤ) := by
      dsimp [a]
      simpa [A] using
        (column_color_sum_edgeIncMatrix_eq_incident_color_count
          (G := G) (κ := κ) (c := c) (v := v))
    rw [hcount] at hc_le_one
    simpa [S] using hc_le_one
  have hcard_le_one_nat : S.card ≤ 1 := by
    exact_mod_cast hcard_le_one
  have huniq : ∀ {e e' : G.edgeSet}, e ∈ S → e' ∈ S → e = e' :=
    Finset.card_le_one_iff.mp hcard_le_one_nat
  rw [edgeLabelSubgraph_adj_iff] at hw₀ hw
  rcases hw₀ with ⟨hadj₀, hcolor₀⟩
  rcases hw with ⟨hadj, hcolor⟩
  let e₀ : G.edgeSet := ⟨s(v, w₀), (G.mem_edgeSet).2 hadj₀⟩
  let e : G.edgeSet := ⟨s(v, w), (G.mem_edgeSet).2 hadj⟩
  have hmem₀ : e₀ ∈ S := by
    dsimp [S]
    rw [Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    constructor
    · simp [e₀, hadj₀.ne]
    · simpa [e₀] using hcolor₀
  have hmem : e ∈ S := by
    dsimp [S]
    rw [Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    constructor
    · simp [e, hadj.ne]
    · simpa [e] using hcolor
  have hedge : e₀ = e := huniq hmem₀ hmem
  -- Equality of the two incident edges identifies the opposite endpoints.
  have hsym2 : s(v, w₀) = s(v, w) := by
    simpa [e₀, e] using congrArg (fun x : G.edgeSet ↦ (x : Sym2 V)) hedge
  exact
    (eq_of_incident_sym2_eq (G := G) (v := v) (w₁ := w₀) (w₂ := w) hadj₀ hadj hsym2).symm

/-- Helper for Exercise 4.22: an equitable coloring of the reindexed edge-incidence matrix yields
an edge cover in each fixed color class, provided every degree is at least the number of colors. -/
lemma isEdgeCover_edgeLabelSubgraph_of_equitable_incidence_coloring
    {k : ℕ} (hk : 0 < k) (κ : Fin (Nat.card G.edgeSet) → Fin k)
    (hκ : equitable_k_coloring
      (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
        (G.edgeIncMatrix ℤ)) κ)
    (hdeg : ∀ v : V, k ≤ G.degree v) (c : Fin k) :
    (edgeLabelSubgraph G (fun e ↦ κ ((Finite.equivFin G.edgeSet) e)) c).IsEdgeCover := by
  let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
    Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)
  rw [Subgraph.IsEdgeCover]
  ext v
  constructor
  · intro hv
    simp
  · intro _
    rw [Subgraph.mem_support]
    let S : Finset G.edgeSet := Finset.univ.filter fun e : G.edgeSet ↦
      v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c
    let a : Fin k → ℤ := fun d ↦ column_color_sum A κ d ((Finite.equivFin V) v)
    -- The same balanced-count argument, now with the lower degree bound, forces the chosen color
    -- to appear at least once at the fixed vertex.
    have hone_le_card : (1 : ℤ) ≤ S.card := by
      have hnonneg : ∀ d, 0 ≤ a d := by
        intro d
        have hcount :
            a d =
              ((Finset.univ.filter fun e : G.edgeSet ↦
                  v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = d).card : ℤ) := by
          dsimp [a]
          simpa [A] using
            (column_color_sum_edgeIncMatrix_eq_incident_color_count
              (G := G) (κ := κ) (c := d) (v := v))
        rw [hcount]
        exact_mod_cast Nat.zero_le
          ((Finset.univ.filter fun e : G.edgeSet ↦
            v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = d).card)
      have hbal : ∀ d d' : Fin k, Int.natAbs (a d - a d') ≤ 1 := by
        intro d d'
        simpa [a, A] using equitable_balance_all_pairs A κ hκ d d' ((Finite.equivFin V) v)
      have hsum : (k : ℤ) ≤ ∑ d, a d := by
        calc
          (k : ℤ) ≤ G.degree v := by
            exact_mod_cast hdeg v
          _ = ∑ j : Fin (Nat.card G.edgeSet), A ((Finite.equivFin V) v) j := by
            dsimp [A]
            exact (reindexed_edgeIncMatrix_row_sum_eq_degree (G := G) v).symm
          _ = ∑ d : Fin k, column_color_sum A κ d ((Finite.equivFin V) v) := by
            symm
            simpa using sum_column_color_sum_eq_row_sum A κ ((Finite.equivFin V) v)
          _ = ∑ d, a d := by
            rfl
      have hc_ge_one : 1 ≤ a c :=
        one_le_pairwise_balanced_counts_of_card_le_sum
          (hk := hk) hnonneg hbal hsum c
      have hcount :
          a c =
            ((Finset.univ.filter fun e : G.edgeSet ↦
                v ∈ (e : Sym2 V) ∧ κ ((Finite.equivFin G.edgeSet) e) = c).card : ℤ) := by
        dsimp [a]
        simpa [A] using
          (column_color_sum_edgeIncMatrix_eq_incident_color_count
            (G := G) (κ := κ) (c := c) (v := v))
      rw [hcount] at hc_ge_one
      simpa [S] using hc_ge_one
    have hone_le_card_nat : 1 ≤ S.card := by
      exact_mod_cast hone_le_card
    rcases Finset.card_pos.mp (Nat.succ_le_iff.mp hone_le_card_nat) with ⟨e, heS⟩
    rcases Finset.mem_filter.mp heS with ⟨-, hmem, hcolor⟩
    let w : V := Sym2.Mem.other hmem
    have he_symm : (e : Sym2 V) = s(v, w) := by
      simp [w]
    have hadj : G.Adj v w := by
      have hEdge : s(v, w) ∈ G.edgeSet := by
        rw [← he_symm]
        exact e.2
      exact (G.mem_edgeSet).1 hEdge
    let e' : G.edgeSet := ⟨s(v, w), (G.mem_edgeSet).2 hadj⟩
    have hedge : e' = e := by
      apply Subtype.ext
      exact he_symm.symm
    have hcolor' : κ ((Finite.equivFin G.edgeSet) e') = c := by
      simpa [e', hedge] using hcolor
    -- Use the chosen incident edge to witness that `v` lies in the support of the fixed color
    -- class.
    refine ⟨w, ?_⟩
    rw [edgeLabelSubgraph_adj_iff]
    exact ⟨hadj, hcolor'⟩

/-- Helper for Exercise 4.22: once every label class is an edge cover, the family of label
subgraphs forms a packing whose cardinality is the number of labels. -/
lemma edge_cover_packing_of_edge_labeling
    {k : ℕ} [Nonempty V] (C : G.EdgeLabeling (Fin k))
    (hcover : ∀ c, (edgeLabelSubgraph G C c).IsEdgeCover) :
    edge_cover_packing G (Finset.univ.image (fun c => edgeLabelSubgraph G C c)) ∧
      (Finset.univ.image (fun c => edgeLabelSubgraph G C c)).card = k := by
  classical
  let F : Finset G.Subgraph := Finset.univ.image (fun c => edgeLabelSubgraph G C c)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro H hH
      -- Every member of the image family is one of the declared edge-cover color classes.
      rcases Finset.mem_image.1 hH with ⟨c, -, rfl⟩
      exact hcover c
    · intro H hH H' hH' hne
      -- Distinct members come from distinct colors, hence their edge sets are disjoint.
      rcases Finset.mem_image.1 hH with ⟨c, -, rfl⟩
      rcases Finset.mem_image.1 hH' with ⟨d, -, rfl⟩
      by_cases hcd : c = d
      · subst hcd
        exact False.elim (hne rfl)
      · exact edgeLabelSubgraph_edgeSet_disjoint (G := G) C hcd
  · have hInj : Function.Injective (fun c : Fin k ↦ edgeLabelSubgraph G C c) := by
      intro c d hEq
      by_contra hcd
      let v : V := Classical.choice ‹Nonempty V›
      have hvSupport : v ∈ (edgeLabelSubgraph G C c).support := by
        rw [hcover c]
        simp
      rw [Subgraph.mem_support] at hvSupport
      rcases hvSupport with ⟨w, hvw⟩
      have hmem_c : s(v, w) ∈ (edgeLabelSubgraph G C c).edgeSet := Subgraph.mem_edgeSet.2 hvw
      have hmem_d : s(v, w) ∈ (edgeLabelSubgraph G C d).edgeSet := by
        simpa [hEq] using hmem_c
      have hdisj :
          Disjoint (edgeLabelSubgraph G C c).edgeSet (edgeLabelSubgraph G C d).edgeSet :=
        edgeLabelSubgraph_edgeSet_disjoint (G := G) C hcd
      exact Set.disjoint_left.1 hdisj hmem_c hmem_d
    -- Equality of two color classes would contradict disjointness once a support witness is
    -- extracted from the edge-cover property.
    simpa [F] using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin k)))
        (f := fun c : Fin k ↦ edgeLabelSubgraph G C c) hInj)

/-- Helper for Exercise 4.22: the bipartite case reduces to constructing a family of
`G.maxDegree` colors whose label classes are matchings. -/
lemma exists_isProper_edgeLabeling_of_isBipartite
    (hG : G.IsBipartite) :
    ∃ C : G.EdgeLabeling (Fin G.maxDegree), IsProperEdgeLabeling G C := by
  -- Route correction: the remaining gap is the source-faithful equitable edge-labeling
  -- construction coming from Theorem 4.18 and Exercise 4.10.
  by_cases hΔ : G.maxDegree = 0
  · have hEdgeEmpty : IsEmpty G.edgeSet := edgeSet_isEmpty_of_maxDegree_eq_zero (G := G) hΔ
    refine ⟨fun e ↦ False.elim (hEdgeEmpty.false e), ?_⟩
    intro c
    -- In the zero-degree branch there are no colors and no edges, so matchingness is vacuous.
    rw [hΔ] at c
    exact Fin.elim0 c
  · let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
      Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)
    have hk : 0 < G.maxDegree := Nat.pos_of_ne_zero hΔ
    have hTU0 : (G.edgeIncMatrix ℤ).IsTotallyUnimodular :=
      (edge_incidence_matrix_isTotallyUnimodular_iff_isBipartite (G := G)).2 hG
    have hTU : A.IsTotallyUnimodular := by
      -- Reindex the TU incidence matrix to the `Fin`-indexed form required by Exercise 4.10.
      simpa [A] using hTU0.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
    obtain ⟨κ, hκ⟩ := exists_equitable_k_coloring_of_is_totally_unimodular A hTU hk
    refine ⟨fun e ↦ κ ((Finite.equivFin G.edgeSet) e), ?_⟩
    -- The equitable row counts force each fixed color class to contain at most one incident edge
    -- at every vertex, hence each class is a matching.
    exact isProperEdgeLabeling_of_equitable_incidence_coloring (G := G) hk κ hκ
      (fun v ↦ G.degree_le_maxDegree v)

/-- Helper for Exercise 4.22: the bipartite case reduces to constructing a packing of
`G.minDegree` pairwise edge-disjoint edge-covers. -/
lemma exists_edge_cover_packing_card_eq_minDegree_of_isBipartite
    [Nonempty V] (hG : G.IsBipartite) :
    ∃ F : Finset G.Subgraph, edge_cover_packing G F ∧ F.card = G.minDegree := by
  classical
  -- Route correction: this uses the same equitable edge-labeling skeleton as part (1), but now
  -- with `k = G.minDegree` so every color appears at least once at each vertex.
  by_cases hδ : G.minDegree = 0
  · refine ⟨∅, ?_, ?_⟩
    · -- The empty family is a valid packing when the target cardinality is zero.
      simp [edge_cover_packing]
    · simp [hδ]
  · let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
      Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)
    have hk : 0 < G.minDegree := Nat.pos_of_ne_zero hδ
    have hTU0 : (G.edgeIncMatrix ℤ).IsTotallyUnimodular :=
      (edge_incidence_matrix_isTotallyUnimodular_iff_isBipartite (G := G)).2 hG
    have hTU : A.IsTotallyUnimodular := by
      -- The same TU witness is reused, now with `k = G.minDegree`.
      simpa [A] using hTU0.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
    obtain ⟨κ, hκ⟩ := exists_equitable_k_coloring_of_is_totally_unimodular A hTU hk
    let C : G.EdgeLabeling (Fin G.minDegree) := fun e ↦ κ ((Finite.equivFin G.edgeSet) e)
    have hcover : ∀ c : Fin G.minDegree, (edgeLabelSubgraph G C c).IsEdgeCover := by
      intro c
      -- The lower degree bound forces every color to appear at least once at each vertex.
      simpa [C] using
        isEdgeCover_edgeLabelSubgraph_of_equitable_incidence_coloring
          (G := G) hk κ hκ (fun v ↦ G.minDegree_le_degree v) c
    obtain ⟨hpacking, hCard⟩ := edge_cover_packing_of_edge_labeling (G := G) C hcover
    refine ⟨_, hpacking, ?_⟩
    -- Package the color classes as the desired family of pairwise disjoint edge covers.
    simpa [C] using hCard

/-- Exercise 4.22 (1): if `G` is bipartite, then the chromatic number of its line graph, i.e. the
edge-chromatic number of `G`, equals its maximum degree. -/
theorem edge_chromatic_number_eq_maxDegree_of_isBipartite
    (hG : G.IsBipartite) :
    G.lineGraph.chromaticNumber = G.maxDegree := by
  obtain ⟨C, hC⟩ := exists_isProper_edgeLabeling_of_isBipartite G hG
  refine le_antisymm ?_ ?_
  · -- The constructed proper edge-labeling gives a coloring of the line graph.
    rw [chromaticNumber_le_iff_colorable]
    exact (lineGraph_colorable_iff_exists_isProperEdgeLabeling G).2 ⟨C, hC⟩
  · -- Every coloring of the line graph gives a proper edge-labeling using at least `Δ(G)` colors.
    refine (le_chromaticNumber_iff_colorable).2 ?_
    intro m hm
    rcases (lineGraph_colorable_iff_exists_isProperEdgeLabeling G).1 hm with ⟨C', hC'⟩
    simpa using maxDegree_le_card_of_isProper G C' hC'

/-- Exercise 4.22 (2): if `G` is bipartite, then the maximum number of pairwise edge-disjoint
edge-covers equals the minimum degree. -/
theorem maximum_disjoint_edge_covers_eq_minDegree_of_isBipartite
    [Nonempty V] (hG : G.IsBipartite) :
    maximum_disjoint_edge_covers G = G.minDegree := by
  classical
  obtain ⟨F, hF, hCard⟩ :=
    exists_edge_cover_packing_card_eq_minDegree_of_isBipartite G hG
  rw [maximum_disjoint_edge_covers]
  have hNonempty :
      ({k : ℕ | ∃ F : Finset G.Subgraph, edge_cover_packing G F ∧ F.card = k}).Nonempty := by
    exact ⟨G.minDegree, ⟨F, hF, hCard⟩⟩
  have hBdd :
      BddAbove {k : ℕ | ∃ F : Finset G.Subgraph, edge_cover_packing G F ∧ F.card = k} := by
    refine ⟨G.minDegree, ?_⟩
    intro k hk
    rcases hk with ⟨F', hF', hCard'⟩
    rw [← hCard']
    exact edge_cover_packing_card_le_minDegree G F' hF'
  refine le_antisymm ?_ ?_
  · -- Any admissible packing is bounded above by the minimum degree.
    exact csSup_le hNonempty fun k hk ↦ by
      rcases hk with ⟨F', hF', hCard'⟩
      rw [← hCard']
      exact edge_cover_packing_card_le_minDegree G F' hF'
  · -- The constructed packing witnesses the lower bound for the supremum.
    exact le_csSup hBdd ⟨F, hF, hCard⟩

end Exercise_4_22

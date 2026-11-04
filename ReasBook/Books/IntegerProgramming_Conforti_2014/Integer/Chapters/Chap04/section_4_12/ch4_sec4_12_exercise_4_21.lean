/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_theorem_4_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_3.ch4_sec4_4_3_definition_4_4_3_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open SimpleGraph

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file reuses
-- the chapter owner `edgeFamilySubgraph` together with mathlib's `SimpleGraph.edgeSet_fromEdgeSet`,
-- `SimpleGraph.Subgraph.support`, and `SimpleGraph.completeGraph` APIs.

universe u

section Exercise_4_21

variable {V : Type u} {G : SimpleGraph V}

namespace SimpleGraph.Subgraph

/-- A subgraph of `G` is an edge cover when every vertex of `G` is incident to one of its edges. -/
def IsEdgeCover (H : G.Subgraph) : Prop :=
  H.support = Set.univ

/-- In a finite graph, an edge cover has minimum cardinality when no other edge cover of `G` uses
fewer edges. -/
@[mk_iff]
structure IsMinimumCardinalityEdgeCover [Finite V] (H : G.Subgraph) : Prop where
  isEdgeCover : H.IsEdgeCover
  minimum (H' : G.Subgraph) (_ : H'.IsEdgeCover) : H.edgeSet.ncard ≤ H'.edgeSet.ncard

/-- Every edge cover leaves no vertex isolated in the ambient graph. -/
lemma IsEdgeCover.exists_adj {H : G.Subgraph} (hH : H.IsEdgeCover) (v : V) :
    ∃ w : V, G.Adj v w := by
  have hv : v ∈ H.support := by
    rw [hH]
    simp
  rw [Subgraph.mem_support] at hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, H.adj_sub hvw⟩

/-- Completing a matching by adjoining an incident edge for every uncovered vertex produces an
edge cover. -/
lemma IsMatching.isEdgeCover_of_completion {M C : G.Subgraph} (hM : M.IsMatching)
    {f : {v // v ∉ M.verts} → G.edgeSet}
    (hincident : ∀ u, (u : V) ∈ ((f u : G.edgeSet) : Sym2 V))
    (hC : C.edgeSet = M.edgeSet ∪ Set.range fun u ↦ ((f u : G.edgeSet) : Sym2 V)) :
    C.IsEdgeCover := by
  rw [SimpleGraph.Subgraph.IsEdgeCover]
  apply Set.eq_univ_of_forall
  intro v
  rw [SimpleGraph.Subgraph.mem_support]
  by_cases hv : v ∈ M.verts
  · obtain ⟨w, hvw, -⟩ := hM hv
    refine ⟨w, ?_⟩
    apply (SimpleGraph.Subgraph.mem_edgeSet).mp
    rw [hC]
    exact Or.inl <| (SimpleGraph.Subgraph.mem_edgeSet).2 hvw
  · let u : {v // v ∉ M.verts} := ⟨v, hv⟩
    let w := Sym2.Mem.other (hincident u)
    refine ⟨w, ?_⟩
    apply (SimpleGraph.Subgraph.mem_edgeSet).mp
    rw [hC]
    refine Or.inr ?_
    refine ⟨u, ?_⟩
    simp [u, w, Sym2.other_spec (hincident u)]

end SimpleGraph.Subgraph

/-- A finite edge family covers `G` exactly when its generated subgraph is an edge cover. -/
lemma edgeFamilySubgraph_isEdgeCover_iff (F : Finset G.edgeSet) :
    (edgeFamilySubgraph G (F : Set G.edgeSet)).IsEdgeCover ↔
      ∀ v : V, ∃ e ∈ F, v ∈ (e : Sym2 V) := by
  constructor
  · intro hF v
    have hv : v ∈ (edgeFamilySubgraph G (F : Set G.edgeSet)).support := by
      rw [hF]
      simp
    rw [Subgraph.mem_support] at hv
    rcases hv with ⟨w, hvw⟩
    have hmem : s(v, w) ∈ (edgeFamilySubgraph G (F : Set G.edgeSet)).edgeSet :=
      (Subgraph.mem_edgeSet).2 hvw
    rw [edgeFamilySubgraph_edgeSet G (F : Set G.edgeSet)] at hmem
    rcases hmem with ⟨e, heF, heq⟩
    exact ⟨e, heF, by simp [heq]⟩
  · intro hF
    refine Set.eq_univ_iff_forall.mpr fun v ↦ ?_
    rw [Subgraph.mem_support]
    rcases hF v with ⟨e, heF, hv⟩
    refine ⟨Sym2.Mem.other hv, ?_⟩
    apply (Subgraph.mem_edgeSet).mp
    rw [edgeFamilySubgraph_edgeSet G (F : Set G.edgeSet)]
    exact ⟨e, heF, by simp [Sym2.other_spec hv]⟩

/-- The generated subgraph has exactly as many edges as the finite family that defines it. -/
lemma edgeFamilySubgraph_edgeSet_ncard_finset (F : Finset G.edgeSet) :
    (edgeFamilySubgraph G (F : Set G.edgeSet)).edgeSet.ncard = F.card := by
  rw [edgeFamilySubgraph_edgeSet G (F : Set G.edgeSet)]
  rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  simp

private lemma vertexCoverNum_eq_ncard_compl_of_isMaximumIndepSet [Finite V] (S : Finset V)
    (hS : G.IsMaximumIndepSet S) :
    G.vertexCoverNum = (((↑S : Set V)ᶜ).ncard : ℕ∞) := by
  have hCover : G.IsVertexCover ((↑S : Set V)ᶜ) := by
    simpa using hS.isIndepSet
  refine le_antisymm ?_ ?_
  · simpa using hCover.vertexCoverNum_le
  · obtain ⟨C, hCcard, hCcover⟩ := SimpleGraph.vertexCoverNum_exists G
    have hCindep : G.IsIndepSet (Cᶜ : Set V) := by
      simpa using
        SimpleGraph.isIndepSet_compl_iff_isVertexCover.2 hCcover
    have hTc : Cᶜ.ncard ≤ S.card := by
      let T : Finset V := Cᶜ.toFinite.toFinset
      have hTindep : G.IsIndepSet T := by
        simpa [T, Set.toFinite_toFinset] using hCindep
      letI : Fintype ↥(Cᶜ) := Fintype.ofFinite ↥(Cᶜ)
      have hTle : T.card ≤ S.card := hS.maximum T hTindep
      simpa [T, Set.ncard_eq_toFinset_card, Set.toFinite_toFinset] using hTle
    have hNat : ((↑S : Set V)ᶜ).ncard ≤ C.ncard := by
      have hAddS : S.card + ((↑S : Set V)ᶜ).ncard = Nat.card V := by
        simpa [Nat.add_comm] using Set.ncard_add_ncard_compl (↑S : Set V)
      have hAddC : C.ncard + Cᶜ.ncard = Nat.card V := by
        simpa [Nat.add_comm] using Set.ncard_add_ncard_compl C
      omega
    have hEncard : (((↑S : Set V)ᶜ).ncard : ℕ∞) ≤ C.encard := by
      have hNatEnat : ((((↑S : Set V)ᶜ).ncard : ℕ∞) ≤ (C.ncard : ℕ∞)) := by
        exact_mod_cast hNat
      simpa using hNatEnat
    simpa [hCcard] using hEncard

private lemma ncard_verts_eq_two_mul_ncard_edgeSet_of_isMatching_of_isBipartite [Finite V]
    (hG : G.IsBipartite) {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  rcases hG.exists_isBipartiteWith with ⟨U, W, hUW⟩
  have hLeft : (U ∩ M.verts).ncard = M.edgeSet.ncard := by
    have hEncard :
        (U ∩ M.verts).encard = M.edgeSet.encard :=
      Set.encard_congr (Equiv.ofBijective _ (matching_side_bijective hUW hM))
    have hNat : ((U ∩ M.verts).ncard : ℕ∞) = (M.edgeSet.ncard : ℕ∞) := by
      simpa using hEncard
    exact_mod_cast hNat
  have hRight : (W ∩ M.verts).ncard = M.edgeSet.ncard := by
    have hEncard :
        (W ∩ M.verts).encard = M.edgeSet.encard :=
      Set.encard_congr (Equiv.ofBijective _ (matching_side_bijective hUW.symm hM))
    have hNat : ((W ∩ M.verts).ncard : ℕ∞) = (M.edgeSet.ncard : ℕ∞) := by
      simpa using hEncard
    exact_mod_cast hNat
  have hUnion : (U ∩ M.verts) ∪ (W ∩ M.verts) = M.verts := by
    ext v
    constructor
    · rintro (⟨-, hvM⟩ | ⟨-, hvM⟩)
      · exact hvM
      · exact hvM
    · intro hvM
      have hvSupport : v ∈ M.support := by
        simpa [hM.support_eq_verts] using hvM
      rcases (Subgraph.mem_support M).1 hvSupport with ⟨w, hvw⟩
      rcases hUW.mem_of_adj (M.adj_sub hvw) with hU | hW
      · exact Or.inl ⟨hU.1, hvM⟩
      · exact Or.inr ⟨hW.1, hvM⟩
  have hDisjoint : Disjoint (U ∩ M.verts) (W ∩ M.verts) := by
    rw [Set.disjoint_left]
    intro v hvU hvW
    exact (Set.disjoint_left.mp hUW.disjoint hvU.1 hvW.1)
  have hfinU : (U ∩ M.verts).Finite := Set.toFinite (U ∩ M.verts)
  have hfinW : (W ∩ M.verts).Finite := Set.toFinite (W ∩ M.verts)
  calc
    M.verts.ncard = ((U ∩ M.verts) ∪ (W ∩ M.verts)).ncard := by rw [hUnion]
    _ = (U ∩ M.verts).ncard + (W ∩ M.verts).ncard := by
      simpa using Set.ncard_union_eq hDisjoint hfinU hfinW
    _ = 2 * M.edgeSet.ncard := by omega

private def matchingEdgeFamily (M : G.Subgraph) : Set G.edgeSet :=
  ((↑) : G.edgeSet → Sym2 V) ⁻¹' M.edgeSet

private lemma ncard_matchingEdgeFamily (M : G.Subgraph) :
    (matchingEdgeFamily M).ncard = M.edgeSet.ncard := by
  have hsubset : M.edgeSet ⊆ Set.range ((↑) : G.edgeSet → Sym2 V) := by
    intro e he
    exact ⟨⟨e, M.edgeSet_subset he⟩, rfl⟩
  simpa [matchingEdgeFamily] using
    (Set.ncard_preimage_of_injective_subset_range
      Subtype.val_injective hsubset)

private noncomputable def completionEdge (M : G.Subgraph)
    (hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w) :
    {v // v ∉ M.verts} → G.edgeSet := fun u ↦
  let w := Classical.choose (hNoIsolated u)
  ⟨s((u : V), w), (G.mem_edgeSet).2 (Classical.choose_spec (hNoIsolated u))⟩

private lemma mem_completionEdge (M : G.Subgraph)
    {hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w} (u : {v // v ∉ M.verts}) :
    (u : V) ∈ ((completionEdge M hNoIsolated u : G.edgeSet) : Sym2 V) := by
  simp [completionEdge]

private def completionEdgeFamily (M : G.Subgraph)
    (hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w) : Set G.edgeSet :=
  matchingEdgeFamily M ∪
    Set.range (fun u : {v // v ∉ M.verts} ↦ completionEdge M hNoIsolated u)

private lemma completionEdgeFamily_isEdgeCover (M : G.Subgraph) (hM : M.IsMatching)
    (hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w) :
    (edgeFamilySubgraph G (completionEdgeFamily M hNoIsolated)).IsEdgeCover := by
  refine Set.eq_univ_iff_forall.mpr fun v ↦ ?_
  rw [Subgraph.mem_support]
  by_cases hv : v ∈ M.verts
  · obtain ⟨w, hvw, -⟩ := hM hv
    refine ⟨w, ?_⟩
    apply (Subgraph.mem_edgeSet).mp
    rw [edgeFamilySubgraph_edgeSet G (completionEdgeFamily M hNoIsolated)]
    refine ⟨⟨s(v, w), M.edgeSet_subset ((Subgraph.mem_edgeSet).2 hvw)⟩, ?_, rfl⟩
    change ⟨s(v, w), M.edgeSet_subset ((Subgraph.mem_edgeSet).2 hvw)⟩ ∈
        completionEdgeFamily M hNoIsolated
    simp [completionEdgeFamily, matchingEdgeFamily, hvw]
  · let u : {v // v ∉ M.verts} := ⟨v, hv⟩
    let w : V := Classical.choose (hNoIsolated u)
    refine ⟨w, ?_⟩
    apply (Subgraph.mem_edgeSet).mp
    rw [edgeFamilySubgraph_edgeSet G (completionEdgeFamily M hNoIsolated)]
    refine ⟨completionEdge M hNoIsolated u, Or.inr ⟨u, rfl⟩, ?_⟩
    change ((completionEdge M hNoIsolated u : G.edgeSet) : Sym2 V) = s(v, w)
    simp [completionEdge, u, w]

private lemma completionEdgeFamily_ncard_le [Finite V] (M : G.Subgraph) (hG : G.IsBipartite)
    (hM : M.IsMatching) (hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w) :
    (completionEdgeFamily M hNoIsolated).ncard ≤ Nat.card V - M.edgeSet.ncard := by
  have hUnion :
      (completionEdgeFamily M hNoIsolated).ncard ≤
        (matchingEdgeFamily M).ncard + (Set.range (completionEdge M hNoIsolated)).ncard := by
    simpa [completionEdgeFamily] using
      Set.ncard_union_le (matchingEdgeFamily M) (Set.range (completionEdge M hNoIsolated))
  have hRange :
      (Set.range (completionEdge M hNoIsolated)).ncard ≤ Nat.card {v // v ∉ M.verts} := by
    have hImage :
        ((completionEdge M hNoIsolated) '' (Set.univ : Set {v // v ∉ M.verts})).ncard ≤
          (Set.univ : Set {v // v ∉ M.verts}).ncard := by
      exact Set.ncard_image_le
    simpa [Set.image_univ, Nat.card_coe_set_eq] using hImage
  have hVerts : M.verts.ncard = 2 * M.edgeSet.ncard :=
    ncard_verts_eq_two_mul_ncard_edgeSet_of_isMatching_of_isBipartite hG hM
  have hMatch : (matchingEdgeFamily M).ncard = M.edgeSet.ncard :=
    ncard_matchingEdgeFamily M
  have hStep :
      (matchingEdgeFamily M).ncard + (Set.range (completionEdge M hNoIsolated)).ncard ≤
        M.edgeSet.ncard + Nat.card {v // v ∉ M.verts} := by
    exact add_le_add (by simp [hMatch]) hRange
  have hFinal :
      M.edgeSet.ncard + Nat.card {v // v ∉ M.verts} ≤ Nat.card V - M.edgeSet.ncard := by
    have hFinal' : M.edgeSet.ncard + (M.vertsᶜ).ncard ≤ Nat.card V - M.edgeSet.ncard := by
      have hVertsLe : 2 * M.edgeSet.ncard ≤ Nat.card V := by
        have hVertsLe' : M.verts.ncard ≤ Nat.card V := by
          simpa using Set.ncard_le_ncard M.verts.subset_univ
        rw [← hVerts]
        exact hVertsLe'
      have hEdgeLe : M.edgeSet.ncard ≤ Nat.card V - M.edgeSet.ncard := by
        omega
      rw [Set.ncard_compl, hVerts]
      omega
    change M.edgeSet.ncard + (M.vertsᶜ).ncard ≤ Nat.card V - M.edgeSet.ncard
    exact hFinal'
  calc
    (completionEdgeFamily M hNoIsolated).ncard ≤
        (matchingEdgeFamily M).ncard + (Set.range (completionEdge M hNoIsolated)).ncard := hUnion
    _ ≤ M.edgeSet.ncard + Nat.card {v // v ∉ M.verts} := hStep
    _ ≤ Nat.card V - M.edgeSet.ncard := hFinal

/-- Exercise 4.21 (1): if `S` is a stable set of `G` and `F` is an edge cover of `G`, then
`|S| ≤ |F|`. -/
theorem indepSet_card_le_card_of_is_edge_cover (S : Finset V) (F : Finset G.edgeSet)
    (hS : G.IsIndepSet S) (hF : (edgeFamilySubgraph G (F : Set G.edgeSet)).IsEdgeCover) :
    S.card ≤ F.card := by
  classical
  have hF' := (edgeFamilySubgraph_isEdgeCover_iff F).mp hF
  let edgeOf : V → G.edgeSet := fun v ↦ Classical.choose (hF' v)
  have edgeOf_mem : Set.MapsTo edgeOf S F := by
    intro v hv
    exact (Classical.choose_spec (hF' v)).1
  have edgeOf_incident (v : V) : v ∈ ((edgeOf v : G.edgeSet) : Sym2 V) := by
    exact (Classical.choose_spec (hF' v)).2
  have edgeOf_injective : Set.InjOn edgeOf (S : Set V) := by
    intro v hv w hw hEq
    by_contra hne
    -- If two distinct vertices of the independent set chose the same covering edge,
    -- that edge would witness an adjacency inside `S`, contradicting independence.
    have hAdj : G.Adj v w := by
      refine (G.adj_iff_exists_edge).2 ?_
      refine ⟨hne, edgeOf v, (edgeOf v).property, edgeOf_incident v, ?_⟩
      simpa [hEq] using edgeOf_incident w
    exact (hS hv hw hne) hAdj
  -- Inject the independent-set vertices into the covering edges they choose.
  exact Finset.card_le_card_of_injOn edgeOf edgeOf_mem edgeOf_injective

/-- Exercise 4.21 (2): if `S` is a maximum-cardinality stable set of a bipartite graph `G` and
`F` is a minimum-cardinality edge cover of `G`, then `|S| = |F|`. -/
theorem card_maximumIndepSet_eq_card_minimumEdgeCover_of_isBipartite [Finite V]
    (hG : G.IsBipartite) (S : Finset V) (F : Finset G.edgeSet)
    (hS : G.IsMaximumIndepSet S)
    (hF : (edgeFamilySubgraph G (F : Set G.edgeSet)).IsMinimumCardinalityEdgeCover) :
    S.card = F.card := by
  classical
  have h_le : S.card ≤ F.card :=
    indepSet_card_le_card_of_is_edge_cover S F hS.isIndepSet hF.isEdgeCover
  have hNoIsolated : ∀ v : V, ∃ w : V, G.Adj v w := fun v ↦
    hF.isEdgeCover.exists_adj v
  obtain ⟨M, hM⟩ : ∃ M : G.Subgraph, M.IsMaximumCardinalityMatching :=
    Subgraph.exists_isMaximumCardinalityMatching
  have hCandidateCover :
      (edgeFamilySubgraph G (completionEdgeFamily M hNoIsolated)).IsEdgeCover :=
    completionEdgeFamily_isEdgeCover M hM.isMatching hNoIsolated
  have hF_le_candidate :
      F.card ≤ (edgeFamilySubgraph G (completionEdgeFamily M hNoIsolated)).edgeSet.ncard := by
    rw [← edgeFamilySubgraph_edgeSet_ncard_finset F]
    exact hF.minimum _ hCandidateCover
  have hCandidateCard :
      (edgeFamilySubgraph G (completionEdgeFamily M hNoIsolated)).edgeSet.ncard =
        (completionEdgeFamily M hNoIsolated).ncard := by
    rw [edgeFamilySubgraph_edgeSet G (completionEdgeFamily M hNoIsolated)]
    simpa using
      Set.ncard_image_of_injective
        (completionEdgeFamily M hNoIsolated) Subtype.val_injective
  have hVertexCoverNum :
      G.vertexCoverNum = (((↑S : Set V)ᶜ).ncard : ℕ∞) := by
    exact vertexCoverNum_eq_ncard_compl_of_isMaximumIndepSet S hS
  have hMatchingCard :
      M.edgeSet.ncard = Nat.card V - S.card := by
    have hEncard :
        M.edgeSet.encard = (((↑S : Set V)ᶜ).ncard : ℕ∞) := by
      calc
        M.edgeSet.encard = G.vertexCoverNum :=
          hM.encard_edgeSet_eq_vertexCoverNum_of_isBipartite hG
        _ = (((↑S : Set V)ᶜ).ncard : ℕ∞) := hVertexCoverNum
    have hNat : M.edgeSet.ncard = ((↑S : Set V)ᶜ).ncard := by
      have hNatEnat : (M.edgeSet.ncard : ℕ∞) = (((↑S : Set V)ᶜ).ncard : ℕ∞) := by
        rw [(Set.toFinite M.edgeSet).cast_ncard_eq]
        exact hEncard
      exact_mod_cast hNatEnat
    calc
      M.edgeSet.ncard = ((↑S : Set V)ᶜ).ncard := hNat
      _ = Nat.card V - S.card := by simpa using Set.ncard_compl (↑S : Set V)
  have hCandidate_le_S :
      (edgeFamilySubgraph G (completionEdgeFamily M hNoIsolated)).edgeSet.ncard ≤ S.card := by
    rw [hCandidateCard]
    have hFamily : (completionEdgeFamily M hNoIsolated).ncard ≤ Nat.card V - M.edgeSet.ncard :=
      completionEdgeFamily_ncard_le M hG hM.isMatching hNoIsolated
    have hBound : (completionEdgeFamily M hNoIsolated).ncard ≤ S.card := by
      have hGap : Nat.card V - M.edgeSet.ncard = S.card := by
        omega
      exact hFamily.trans_eq hGap
    exact hBound
  have h_ge : F.card ≤ S.card := hF_le_candidate.trans hCandidate_le_S
  exact le_antisymm h_le h_ge

/-- Exercise 4.21 (3): the complete graph on three vertices provides a graph whose maximum stable
set has smaller cardinality than a minimum edge cover. -/
theorem completeGraph_fin3_maximumIndepSet_card_lt_minimumEdgeCover_card :
    ∃ S : Finset (Fin 3),
      (SimpleGraph.completeGraph (Fin 3)).IsMaximumIndepSet S ∧
      ∃ F : Finset (SimpleGraph.completeGraph (Fin 3)).edgeSet,
        (edgeFamilySubgraph
            (SimpleGraph.completeGraph (Fin 3))
            (F : Set _)).IsMinimumCardinalityEdgeCover ∧
          S.card < F.card := by
  let G : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)
  let e01 : G.edgeSet := ⟨s(0, 1), by decide⟩
  let e12 : G.edgeSet := ⟨s(1, 2), by decide⟩
  let F : Finset G.edgeSet := {e01, e12}
  have hmin :
      (edgeFamilySubgraph G (F : Set G.edgeSet)).IsMinimumCardinalityEdgeCover := by
    refine ⟨?_, ?_⟩
    · refine (edgeFamilySubgraph_isEdgeCover_iff F).2 ?_
      intro v
      fin_cases v
      · refine ⟨e01, ?_, by simp [e01]⟩
        change e01 ∈ ({e01, e12} : Finset G.edgeSet)
        simp
      · refine ⟨e01, ?_, by simp [e01]⟩
        change e01 ∈ ({e01, e12} : Finset G.edgeSet)
        simp
      · refine ⟨e12, ?_, by simp [e12]⟩
        change e12 ∈ ({e01, e12} : Finset G.edgeSet)
        simp
    · intro H' hH'
      rw [edgeFamilySubgraph_edgeSet_ncard_finset F]
      have hincident (v : Fin 3) : ∃ e ∈ H'.edgeSet, v ∈ (e : Sym2 (Fin 3)) := by
        have hv : v ∈ H'.support := by
          rw [hH']
          simp
        rw [Subgraph.mem_support] at hv
        rcases hv with ⟨w, hvw⟩
        exact ⟨s(v, w), Subgraph.mem_edgeSet.2 hvw, by simp⟩
      obtain ⟨e0, he0, hv0⟩ := hincident 0
      obtain ⟨e1, he1, hv1⟩ := hincident 1
      obtain ⟨e2, he2, hv2⟩ := hincident 2
      by_contra hlt
      have hle1 : H'.edgeSet.ncard ≤ 1 := Nat.lt_succ_iff.mp (lt_of_not_ge hlt)
      rw [Set.ncard_le_one_iff] at hle1
      have hsingle : ∀ {a b}, a ∈ H'.edgeSet → b ∈ H'.edgeSet → a = b := hle1
      have h01 : e0 = s(0, 1) := by
        refine (Sym2.mem_and_mem_iff (show (0 : Fin 3) ≠ 1 by decide)).mp ?_
        exact ⟨hv0, by simpa [hsingle he0 he1] using hv1⟩
      have hv2' : (2 : Fin 3) ∈ e0 := by
        simpa [hsingle he0 he2] using hv2
      have : ¬ (2 : Fin 3) ∈ e0 := by
        simp [h01]
      exact this hv2'
  have hlt : ({0} : Finset (Fin 3)).card < F.card := by
    decide
  refine ⟨({0} : Finset (Fin 3)), ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro v hv w hw hne
      have hv0 : v = 0 := by simpa using hv
      have hw0 : w = 0 := by simpa using hw
      exact (hne (hv0.trans hw0.symm)).elim
    · intro T hT
      have hcard : T.card ≤ 1 := Finset.card_le_one_iff.mpr fun {a b} ha hb ↦ by
        by_contra hne
        exact (hT ha hb hne <| by simpa [G] using (SimpleGraph.top_adj a b).2 hne).elim
      simpa using hcard
  · refine ⟨F, ?_, ?_⟩
    · simpa [G, F] using hmin
    · simpa [F] using hlt

end Exercise_4_21

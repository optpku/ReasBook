/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19

noncomputable section

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Theorem_4_23

universe u

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- Helper for Theorem 4.23: evaluating a finite weighted sum of edge-vectors at one edge turns
the functional convex-combination identity into an ordinary scalar identity. -/
private lemma weightedSumApply {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → G.edgeSet → ℝ)
    {x : G.edgeSet → ℝ} (hx : ∑ i, w i • z i = x) (e : G.edgeSet) :
    ∑ i, w i * z i e = x e := by
  -- Apply the vector identity at a single edge coordinate.
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx e

/-- Helper for Theorem 4.23: incidence vectors of subgraphs have nonnegative edge coordinates. -/
private lemma subgraphIncidenceVectorNonneg (M : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ M e := by
  intro e
  -- Each edge coordinate is the `0/1` indicator of membership in `M.edgeSet`.
  by_cases h : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Theorem 4.23: if a vertex is not covered by a subgraph, then its incidence sum in
the subgraph incidence vector is `0`. -/
private lemma subgraphIncidenceSumEqZeroOfNotMemVerts {M : G.Subgraph} {v : V}
    (hv : v ∉ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 0 := by
  -- Any incident edge with positive coordinate would force `v` into the support subgraph.
  refine Finset.sum_eq_zero ?_
  intro e he
  have hv_mem : v ∈ (e : Sym2 V) := by
    have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using he_inc
  by_cases heM : e.1 ∈ M.edgeSet
  · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Theorem 4.23: at a covered vertex of a matching, the matching incidence sum is
exactly `1`. -/
private lemma matchingIncidenceSumEqOneOfMemVerts {M : G.Subgraph} (hM : M.IsMatching)
    {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge at `v` lies in the incidence filter at `v`.
    simp [e₀, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have he₀_val : G.subgraphIncidenceVector ℝ M e₀ = 1 := by
    have he₀_edge : e₀.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
    simp [SimpleGraph.subgraphIncidenceVector, he₀_edge]
  calc
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = G.subgraphIncidenceVector ℝ M e₀ := by
          refine Finset.sum_eq_single_of_mem e₀ he₀_mem ?_
          intro e he he_ne
          by_cases heM : e.1 ∈ M.edgeSet
          · have hv_e : v ∈ (e : Sym2 V) := by
              have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
              simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
                using he_inc
            have hAdj_e : M.Adj v (Sym2.Mem.other hv_e) := by
              exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hv_e] using heM)
            have he_eq : e.1 = e₀.1 := by
              calc
                e.1 = s(v, Sym2.Mem.other hv_e) := by
                  symm
                  exact Sym2.other_spec hv_e
                _ = s(v, w) := by rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Theorem 4.23: every matching incidence sum at a vertex is bounded by `1`. -/
private lemma matchingIncidenceSumLeOne {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- A matching contributes `1` on covered vertices and `0` on uncovered vertices.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSumEqOneOfMemVerts (G := G) hM hv
    linarith
  · rw [subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) hv]
    norm_num

/-- Helper for Theorem 4.23: a perfect matching contributes exactly one incident edge at every
vertex. -/
private lemma perfectMatchingIncidenceSumEqOne {M : G.Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Perfect matchings are matchings that cover every vertex.
  simpa using matchingIncidenceSumEqOneOfMemVerts (G := G) hM.1 (hM.2 v)

/-- Helper for Theorem 4.23: every odd cut contains at least one edge of a perfect matching. -/
private lemma perfectMatchingCutLowerBound {M : G.Subgraph} (hM : M.IsPerfectMatching)
    {S : Set V} (hS : Odd S.ncard) :
    1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
  classical
  by_contra hcut
  have hcut_lt : (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) < 1 := by
    linarith
  have hno_cut :
      ∀ {e : G.edgeSet}, e.1 ∈ M.edgeSet → e ∉ δ[G] S := by
    intro e heM heCut
    -- A cut edge of the perfect matching already forces the cut sum to be at least `1`.
    have hsum_ge :
        1 ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
      calc
        1 = G.subgraphIncidenceVector ℝ M e := by
              simp [SimpleGraph.subgraphIncidenceVector, heM]
        _ ≤ (δ[G] S).sum (G.subgraphIncidenceVector ℝ M) := by
              exact Finset.single_le_sum
                (fun e' _ ↦ subgraphIncidenceVectorNonneg (G := G) M e') heCut
    linarith
  have hinduced_match : (M.induce S).IsMatching := by
    intro v hv
    have hvS : v ∈ S := by
      simpa [Subgraph.induce_verts, hM.2.verts_eq_univ] using hv
    obtain ⟨w, hvw, huniq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) v
    have hwS : w ∈ S := by
      by_contra hwS
      let e : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
      have heCut : e ∈ δ[G] S := by
        exact (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).2 ⟨v, hvS, w, hwS, rfl⟩
      have heM : e.1 ∈ M.edgeSet := Subgraph.mem_edgeSet.2 hvw
      exact hno_cut heM heCut
    -- Once no matching edge crosses the cut, the matched neighbor stays inside `S`.
    refine ⟨w, ?_, ?_⟩
    · exact ⟨hvS, hwS, hvw⟩
    · intro x hx
      exact huniq x hx.2.2
  letI : Fintype ↑((M.induce S).verts) := Fintype.ofFinite _
  have hEven : Even S.ncard := by
    -- The induced matching covers exactly the odd-set vertices, so the odd set has even size.
    simpa [Subgraph.induce_verts, hM.2.verts_eq_univ, Set.inter_univ,
      Set.ncard_eq_toFinset_card'] using hinduced_match.even_card
  exact (Nat.not_even_iff_odd.mpr hS) hEven

/-- Helper for Theorem 4.23: every perfect-matching incidence vector satisfies the Chapter 4.19
constraint system. -/
private lemma subgraphIncidenceVector_mem_perfectMatchingConstraintSet {M : G.Subgraph}
    (hM : M.IsPerfectMatching) :
    G.subgraphIncidenceVector ℝ M ∈ perfectMatchingConstraintSet G := by
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact subgraphIncidenceVectorNonneg (G := G) M
  · intro v
    -- Perfect matchings contribute one incident edge at each vertex.
    exact perfectMatchingIncidenceSumEqOne (G := G) hM v
  · intro S hS
    -- Every odd cut of a perfect matching is hit by at least one matching edge.
    exact perfectMatchingCutLowerBound (G := G) hM hS

/-- Helper for Theorem 4.23: the edges with at least one endpoint in a finite set `S`, viewed as
edge coordinates of `G`. -/
private def oddSetIncidentEdgeFinset (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet ↦ ∃ v ∈ S, (e : Sym2 V) ∈ G.incidenceFinset v

/-- Helper for Theorem 4.23: summing over `G.edgeSet` with an indicator `if` rewrites to the
corresponding filtered edge sum. -/
private lemma edgeSetSumIteEqSumFilter
    (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-coordinate form of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Theorem 4.23: the endpoint finset of an edge-coordinate is its unordered pair of
canonical `Sym2.out` endpoints. -/
private lemma edgeToFinsetEqPairFinset (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Theorem 4.23: filtering `{a, b}` by membership in `S` has size `2`, `1`, or `0`
according as both, one, or neither endpoint lies in `S`. -/
private lemma pairFilterCardOfNeFinset
    (a b : V) (hab : a ≠ b) (S : Finset V) :
    (((({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      if a ∈ (S : Set V) ∧ b ∈ (S : Set V) then 2
      else if a ∈ (S : Set V) ∨ b ∈ (S : Set V) then 1 else 0 := by
  -- Split into the four endpoint-membership cases and let `simp` normalize the filtered pair.
  by_cases ha : a ∈ (S : Set V)
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a, b} : Finset V) := by
          ext v
          constructor
          · intro hv
            simpa using (Finset.mem_filter.mp hv).1
          · intro hv
            refine Finset.mem_filter.mpr ⟨hv, ?_⟩
            rcases Finset.mem_insert.mp hv with rfl | hvb
            · simpa using ha
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              simpa using hb
      rw [hfilter]
      simp [ha, hb, hab]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({a} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with rfl | hvb
            · rfl
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            have hv' : v = a := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp
            · simpa using ha
      rw [hfilter]
      simp [ha, hb]
  · by_cases hb : b ∈ (S : Set V)
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = ({b} : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rw [Finset.mem_singleton]
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · simpa using hvb
          · intro hv
            have hv' : v = b := by simpa using hv
            subst hv'
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · simp [hab]
            · simpa using hb
      rw [hfilter]
      simp [ha, hb]
    · have hfilter :
          (({a, b} : Finset V).filter fun v ↦ v ∈ (S : Set V)) = (∅ : Finset V) := by
          ext v
          constructor
          · intro hv
            rcases Finset.mem_filter.mp hv with ⟨hvpair, hvS⟩
            rcases Finset.mem_insert.mp hvpair with hva | hvb
            · subst hva
              exact (ha (by simpa using hvS)).elim
            · have hvb' : v = b := by simpa using hvb
              subst hvb'
              exact (hb (by simpa using hvS)).elim
          · intro hv
            simpa using hv
      rw [hfilter]
      simp [ha, hb]

/-- Helper for Theorem 4.23: an induced edge is characterized by both canonical endpoints lying
in the chosen vertex set. -/
private lemma memInducedEdgeFinsetEndpointsIff
    (S : Set V) (e : G.edgeSet) :
    e ∈ E[G] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Theorem 4.23: a cut edge is characterized by its canonical endpoints lying on
opposite sides of the chosen vertex set. -/
private lemma memCutEdgeFinsetEndpointsIff
    (S : Set V) (e : G.edgeSet) :
    e ∈ δ[G] S ↔
      (e.1.out.1 ∈ S ∧ e.1.out.2 ∉ S) ∨ (e.1.out.2 ∈ S ∧ e.1.out.1 ∉ S) := by
  constructor
  · intro he
    rcases (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).1 he with ⟨u, hu, v, hv, huv⟩
    -- Normalize the witness edge equality to the canonical endpoints of `e`.
    rw [← e.1.out_eq] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.1, h₁, e.1.out.2, h₂, e.1.out_eq⟩
    · exact (mem_cutEdgeFinset_iff (G := G) (S := S) (e := e)).2
        ⟨e.1.out.2, h₁, e.1.out.1, h₂, Sym2.eq_swap.trans e.1.out_eq⟩

/-- Helper for Theorem 4.23: an induced edge cannot simultaneously lie in the cut of the same
vertex set. -/
private lemma notMemCutEdgeFinsetOfMemInducedEdgeFinset
    {S : Set V} {e : G.edgeSet} (he : e ∈ E[G] S) :
    e ∉ δ[G] S := by
  rcases (memInducedEdgeFinsetEndpointsIff (G := G) S e).1 he with ⟨h₁, h₂⟩
  intro hcut
  rcases (memCutEdgeFinsetEndpointsIff (G := G) S e).1 hcut with
    (⟨_, h₂'⟩ | ⟨_, h₁'⟩)
  · exact h₂' h₂
  · exact h₁' h₁

/-- Helper for Theorem 4.23: an edge belongs to `oddSetIncidentEdgeFinset S` exactly when one of
its two canonical endpoints lies in `S`. -/
private lemma memOddSetIncidentEdgeFinsetIff
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e.1.out.1 ∈ (S : Set V) ∨ e.1.out.2 ∈ (S : Set V) := by
  rw [oddSetIncidentEdgeFinset, Finset.mem_filter]
  constructor
  · rintro ⟨_, v, hvS, hvInc⟩
    have hvMem : v ∈ (e : Sym2 V) := by
      exact
        (G.edge_mem_incidenceSet_iff (a := v) (e := e)).1
          ((G.mem_incidenceFinset (v := v) (e := (e : Sym2 V))).1 hvInc)
    rw [← e.1.out_eq] at hvMem
    rw [Sym2.mem_iff] at hvMem
    rcases hvMem with rfl | rfl
    · exact Or.inl (by simpa using hvS)
    · exact Or.inr (by simpa using hvS)
  · intro h
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases h with h₁ | h₂
    · refine ⟨e.1.out.1, by simpa using h₁, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.1) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.1) (e := e)).2 (Sym2.out_fst_mem _))
    · refine ⟨e.1.out.2, by simpa using h₂, ?_⟩
      exact
        (G.mem_incidenceFinset (v := e.1.out.2) (e := (e : Sym2 V))).2
          ((G.edge_mem_incidenceSet_iff (a := e.1.out.2) (e := e)).2 (Sym2.out_snd_mem _))

/-- Helper for Theorem 4.23: an edge incident to `S` is either internal to `S` or crosses the
cut of `S`. -/
private lemma memOddSetIncidentEdgeFinsetIffMemInducedOrCut
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e ∈ E[G] (S : Set V) ∨ e ∈ δ[G] (S : Set V) := by
  constructor
  · intro he
    rcases (memOddSetIncidentEdgeFinsetIff (G := G) S e).1 he with h₁ | h₂
    · by_cases h₂S : e.1.out.2 ∈ (S : Set V)
      · exact Or.inl <|
          (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 ⟨h₁, h₂S⟩
      · exact Or.inr <|
          (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 (Or.inl ⟨h₁, h₂S⟩)
    · by_cases h₁S : e.1.out.1 ∈ (S : Set V)
      · exact Or.inl <|
          (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 ⟨h₁S, h₂⟩
      · exact Or.inr <|
          (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).2 (Or.inr ⟨h₂, h₁S⟩)
  · intro he
    rcases he with hind | hcut
    · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2
        (Or.inl ((memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 hind).1)
    · rcases (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 hcut with
        (⟨h₁, _⟩ | ⟨h₂, _⟩)
      · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2 (Or.inl h₁)
      · exact (memOddSetIncidentEdgeFinsetIff (G := G) S e).2 (Or.inr h₂)

/-- Helper for Theorem 4.23: the edges incident to `S` split disjointly into the edges induced by
`S` and the cut edges of `S`. -/
private lemma oddSetIncidentEdgeFinsetSumEqInducedAddCut
    (S : Finset V) (x : G.edgeSet → ℝ) :
    (oddSetIncidentEdgeFinset (G := G) S).sum x =
      (E[G] (S : Set V)).sum x + (δ[G] (S : Set V)).sum x := by
  have hUnion :
      oddSetIncidentEdgeFinset (G := G) S = E[G] (S : Set V) ∪ δ[G] (S : Set V) := by
    ext e
    simp [memOddSetIncidentEdgeFinsetIffMemInducedOrCut]
  have hDisj : Disjoint (E[G] (S : Set V)) (δ[G] (S : Set V)) := by
    rw [Finset.disjoint_left]
    intro e he hind
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) he hind
  -- Split the incident-edge sum along the induced/cut partition.
  rw [hUnion, Finset.sum_union hDisj]

/-- Helper for Theorem 4.23: filtering the vertices of `S` that lie on an edge agrees with
filtering the endpoint finset of that edge by membership in `S`. -/
private lemma edgeFilterEqEndpointFilter
    (S : Finset V) (e : G.edgeSet) :
    S.filter (fun v ↦ v ∈ (e : Sym2 V)) =
      ((e : Sym2 V).toFinset.filter fun v ↦ v ∈ (S : Set V)) := by
  -- Both sides describe the finite intersection `S ∩ ((e : Sym2 V).toFinset)`.
  ext v
  simpa [Finset.mem_filter, and_comm] using
    (show v ∈ S.filter (fun w ↦ w ∈ (e : Sym2 V)) ↔
      v ∈ ((e : Sym2 V).toFinset.filter fun w ↦ w ∈ (S : Set V)) by
        simp [Finset.mem_filter, Sym2.mem_toFinset])

/-- Helper for Theorem 4.23: the filtered endpoint cardinality of an edge is the sum of the
incident-edge indicator and the induced-edge indicator. -/
private lemma endpointFilterCardEqIncidentAddInduced
    (S : Finset V) (e : G.edgeSet) :
    ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) =
      (if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
        if e ∈ E[G] (S : Set V) then 1 else 0 := by
  have hne : e.1.out.1 ≠ e.1.out.2 := by
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        simpa [e.1.out_eq] using e.prop
      exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
    exact G.ne_of_adj hadj
  -- Compute the filtered endpoint cardinality by splitting on the two endpoints.
  rw [edgeToFinsetEqPairFinset (G := G) e, pairFilterCardOfNeFinset _ _ hne]
  by_cases h₁ : e.1.out.1 ∈ (S : Set V)
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]
    · norm_num [h₁, h₂, memOddSetIncidentEdgeFinsetIff, memInducedEdgeFinsetEndpointsIff]

/-- Helper for Theorem 4.23: summing the vertex-incidence equations on `S` counts each edge
incident to `S` once, plus one extra copy for each edge internal to `S`. -/
private lemma sumIncidenceOnFinsetEqOddSetIncidentAddInduced
    (S : Finset V) (x : G.edgeSet → ℝ) :
    Finset.sum S
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
  calc
    Finset.sum S
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        Finset.sum S
          (fun v ↦ ∑ e : G.edgeSet, if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0) := by
            -- Rewrite each incidence-filter sum as a full edge-set sum with an indicator.
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [Finset.sum_filter]
    _ = Finset.sum Finset.univ
          (fun e : G.edgeSet ↦
            Finset.sum S (fun v ↦ if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0)) := by
          -- Swap the vertex and edge summations.
          rw [Finset.sum_comm]
    _ = ∑ e : G.edgeSet,
          (S.filter fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (fun _ ↦ x e) := by
          -- Repackage the inner indicator sum as a filtered sum over the chosen vertices.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Finset.sum_filter]
    _ = ∑ e : G.edgeSet,
          ((((e : Sym2 V).toFinset.filter fun v : V ↦ v ∈ (S : Set V)).card : ℕ) : ℝ) * x e := by
          -- Replace the filtered vertex set by the filtered endpoint set of `e`.
          refine Finset.sum_congr rfl ?_
          intro e he
          have hfilter :
              S.filter (fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
                S.filter (fun v ↦ v ∈ (e : Sym2 V)) := by
            ext v
            simp [G.edge_mem_incidenceSet_iff]
          rw [hfilter, edgeFilterEqEndpointFilter (G := G) S e, Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = ∑ e : G.edgeSet,
          (((if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
              if e ∈ E[G] (S : Set V) then 1 else 0) * x e) := by
          -- Replace the endpoint multiplicity by the incident-plus-induced decomposition.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [endpointFilterCardEqIncidentAddInduced (G := G) S e]
    _ = ∑ e : G.edgeSet,
          ((if e ∈ oddSetIncidentEdgeFinset (G := G) S then x e else 0) +
            if e ∈ E[G] (S : Set V) then x e else 0) := by
          -- Each `0/1` coefficient turns into the corresponding indicator term.
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases hOdd : e ∈ oddSetIncidentEdgeFinset (G := G) S <;>
            by_cases hInd : e ∈ E[G] (S : Set V) <;>
            simp [hOdd, hInd, add_mul]
    _ = (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S).sum x +
          (Finset.univ.filter fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)).sum x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · exact edgeSetSumIteEqSumFilter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S) x
          · exact edgeSetSumIteEqSumFilter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)) x
    _ = (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
          simp

/-- Helper for Theorem 4.23: summing the incidence equations on `S` counts each internal edge
twice and each cut edge once. -/
private lemma sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum
    (S : Set V) (x : G.edgeSet → ℝ) :
    Finset.sum S.toFinset
      (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      2 * (E[G] S).sum x + (δ[G] S).sum x := by
  calc
    Finset.sum S.toFinset
        (fun v ↦ (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (oddSetIncidentEdgeFinset (G := G) S.toFinset).sum x + (E[G] S).sum x := by
          simpa using sumIncidenceOnFinsetEqOddSetIncidentAddInduced (G := G) S.toFinset x
    _ = ((E[G] (S.toFinset : Set V)).sum x + (δ[G] (S.toFinset : Set V)).sum x) + (E[G] S).sum x := by
          rw [oddSetIncidentEdgeFinsetSumEqInducedAddCut (G := G) S.toFinset x]
    _ = ((E[G] S).sum x + (δ[G] S).sum x) + (E[G] S).sum x := by
          simp
    _ = 2 * (E[G] S).sum x + (δ[G] S).sum x := by
          ring

/-- Helper for Theorem 4.23: summing the degree-one equations over a finite vertex set gives the
cardinality of that set. -/
private lemma incidenceSum_eq_card_of_eq_one {x : G.edgeSet → ℝ}
    (hx_deg : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1)
    (S : Set V) :
    Finset.sum S.toFinite.toFinset
      (fun v ↦
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (S.ncard : ℝ) := by
  -- Replace each incidence sum by the degree-one value and evaluate the constant finite sum.
  calc
    Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        Finset.sum S.toFinite.toFinset (fun _ : V ↦ (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact hx_deg v
    _ = (S.toFinite.toFinset.card : ℝ) := by
          simp
    _ = (S.ncard : ℝ) := by
          have hcard : S.toFinite.toFinset.card = S.ncard := by
            simpa [Set.toFinite_toFinset] using (Set.ncard_eq_toFinset_card' S).symm
          exact_mod_cast hcard

/-- Helper for Theorem 4.23: any point satisfying the perfect-matching constraints also satisfies
the matching constraints. -/
private lemma mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) :
    x ∈ matchingConstraintSet G := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  rw [SimpleGraph.mem_matchingConstraintSet_iff]
  refine ⟨hx_nonneg, ?_, ?_⟩
  · intro v
    linarith [hx_deg v]
  · intro S hS
    have hdegreeSum :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          (S.ncard : ℝ) :=
      incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
    have hsplit :
        Finset.sum S.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          2 * (E[G] S).sum x + (δ[G] S).sum x := by
      simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
    have hcut_lb : 1 ≤ (δ[G] S).sum x := hx_cut S hS
    linarith

/-- Helper for Theorem 4.23: inside `matchingConstraintSet G`, the degree equations `= 1`
recover the full perfect-matching constraint system. -/
private lemma mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
    {x : G.edgeSet → ℝ}
    (hxMatch : x ∈ matchingConstraintSet G)
    (hx_deg : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1) :
    x ∈ perfectMatchingConstraintSet G := by
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hxMatch with
    ⟨hx_nonneg, -, hx_odd⟩
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨hx_nonneg, hx_deg, ?_⟩
  intro S hS
  have hdegreeSum :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (S.ncard : ℝ) :=
    incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
  have hsplit :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        2 * (E[G] S).sum x + (δ[G] S).sum x := by
    simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
  have hinduced : (E[G] S).sum x ≤ ((S.ncard : ℝ) - 1) / 2 := hx_odd S hS
  linarith

/-- Helper for Theorem 4.23: once an odd-set inequality is tight inside the degree-one face, the
corresponding odd cut has total weight exactly `1`. -/
private lemma tightOddCut_eq_one_of_mem_perfectMatchingConstraintSet_of_tightOddSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) {S : Set V}
    (hTight : (E[G] S).sum x = ((S.ncard : ℝ) - 1) / 2) :
    (δ[G] S).sum x = 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, hx_deg, -⟩
  -- Sum the degree equations on `S`, then rewrite the resulting incidence count by induced
  -- edges plus the cut. Tightness of the odd-set inequality forces the cut weight to be `1`.
  have hdegreeSum :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        (S.ncard : ℝ) :=
    incidenceSum_eq_card_of_eq_one (G := G) hx_deg S
  have hsplit :
      Finset.sum S.toFinite.toFinset
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
        2 * (E[G] S).sum x + (δ[G] S).sum x := by
    simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
  linarith

/-- Helper for Theorem 4.23: `perfectMatchingConstraintSet G` is the degree-one extreme slice of
`matchingConstraintSet G`. -/
private lemma perfectMatchingConstraintSet_isExtremeIn_matchingConstraintSet :
    IsExtreme ℝ (matchingConstraintSet G) (perfectMatchingConstraintSet G) := by
  refine ⟨fun x hx ↦
    mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := G) hx, ?_⟩
  intro x hxMatch y hyMatch z hzPerfect hzSeg
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hxMatch with
    ⟨-, hx_deg_le, -⟩
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := y)).1 hyMatch with
    ⟨-, hy_deg_le, -⟩
  rw [openSegment_eq_image₂ ℝ x y] at hzSeg
  rcases hzSeg with ⟨p, hp, hzEq⟩
  let a : ℝ := p.1
  let b : ℝ := p.2
  have ha : 0 < a := hp.1
  have hb_pos : 0 < b := hp.2.1
  have hab : a + b = 1 := hp.2.2
  have hzPerfect' : a • x + b • y ∈ perfectMatchingConstraintSet G := by
    simpa [a, b, hzEq] using hzPerfect
  rcases
      (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := a • x + b • y)).1
        hzPerfect' with
    ⟨-, hz_deg, -⟩
  have hxDegreeEqOne :
      ∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1 := by
    intro v
    have havg :
        a *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
          b *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y =
        1 := by
      calc
        a *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
          b *
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y =
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (a • x + b • y) := by
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
                  Finset.sum_add_distrib]
        _ = 1 := hz_deg v
    nlinarith [havg, hx_deg_le v, hy_deg_le v, ha, hb_pos]
  exact mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
    (G := G) hxMatch hxDegreeEqOne

/-- Helper for Theorem 4.23: extreme points of `perfectMatchingConstraintSet G` remain extreme in
the larger owner `matchingConstraintSet G`. -/
private lemma mem_extremePoints_matchingConstraintSet_of_mem_extremePoints_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ) :
    x ∈ (matchingConstraintSet G).extremePoints ℝ := by
  exact IsExtreme.extremePoints_subset_extremePoints
    (perfectMatchingConstraintSet_isExtremeIn_matchingConstraintSet (G := G)) hx

/-- Helper for Theorem 4.23: `perfectMatchingConstraintSet G` is convex. -/
private lemma convexPerfectMatchingConstraintSet :
    Convex ℝ (perfectMatchingConstraintSet G) := by
  intro x hx y hy a b ha hb hab
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := y)).1 hy with
    ⟨hy_nonneg, hy_deg, hy_cut⟩
  refine (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := a • x + b • y)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro e
    -- Nonnegativity is preserved coordinatewise under convex combinations.
    have hcoord : (a • x + b • y) e = a * x e + b * y e := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoord]
    nlinarith [hx_nonneg e, hy_nonneg e, ha, hb]
  · intro v
    -- The degree equations are affine, so the convex combination still sums to `1`.
    calc
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum (a • x + b • y)
          = a *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
            b *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y := by
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
                  Finset.sum_add_distrib]
      _ = a * 1 + b * 1 := by rw [hx_deg v, hy_deg v]
      _ = 1 := by nlinarith
  · intro S hS
    -- Odd-cut lower bounds are preserved because the coefficients are nonnegative and sum to `1`.
    calc
      1 = a * 1 + b * 1 := by nlinarith
      _ ≤ a * (δ[G] S).sum x + b * (δ[G] S).sum y := by
            nlinarith [hx_cut S hS, hy_cut S hS, ha, hb]
      _ = (δ[G] S).sum (a • x + b • y) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
              Finset.sum_add_distrib]

/-- Helper for Theorem 4.23: in a weighted average of numbers in `[0, 1]` with total weight `1`,
every positive-weight support term must already equal `1` if the average is `1`. -/
private lemma eqOneOfWeightedAverageEqOne {ι : Type*} [Fintype ι] {w a : ι → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (ha_le_one : ∀ i, a i ≤ 1)
    (hw_sum : ∑ i, w i = 1)
    (havg : ∑ i, w i * a i = 1) :
    ∀ i, w i ≠ 0 → a i = 1 := by
  have hterm_nonneg : ∀ i, 0 ≤ w i * (1 - a i) := by
    intro i
    exact mul_nonneg (hw_nonneg i) (sub_nonneg.mpr (ha_le_one i))
  have hterm_sum : ∑ i, w i * (1 - a i) = 0 := by
    calc
      ∑ i, w i * (1 - a i) = ∑ i, (w i - w i * a i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = (∑ i, w i) - ∑ i, w i * a i := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by
            nlinarith [hw_sum, havg]
  have hzero : ∀ i, w i * (1 - a i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _hj ↦ hterm_nonneg j)).1 hterm_sum i
      (Finset.mem_univ i)
  intro i hwi
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hslack_nonneg : 0 ≤ 1 - a i := sub_nonneg.mpr (ha_le_one i)
  have hslack_zero : 1 - a i = 0 := by
    nlinarith [hzero i, hwi_pos, hslack_nonneg]
  nlinarith [hslack_zero]

/-- Helper for Theorem 4.23: a convex decomposition by matchings upgrades to one by perfect
matchings once the barycenter already satisfies the perfect-matching degree equations. -/
private lemma perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx_matchingPolytope : x ∈ matchingPolytope G)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingPolytope G := by
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx_matchingPolytope
  rcases hx_matchingPolytope with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMatch hVec using hz'
  have hx_sum_match :
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x := by
    calc
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hVec i]
      _ = x := hx_sum
  have hsupport_perfect :
      ∀ i, w i ≠ 0 → (M i).IsPerfectMatching := by
    rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hxPerfect with
      ⟨-, hx_deg, -⟩
    intro i hwi
    refine ⟨hMatch i, ?_⟩
    intro v
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    have hterm :
        ∀ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
          Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
      intro j
      rw [Finset.mul_sum]
    have havg :
        ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) = 1 := by
      calc
        ∑ j, w j * I.sum (G.subgraphIncidenceVector ℝ (M j)) =
            ∑ j, Finset.sum I (fun e ↦ w j * G.subgraphIncidenceVector ℝ (M j) e) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact hterm j
        _ = Finset.sum I (fun e ↦ ∑ j, w j * G.subgraphIncidenceVector ℝ (M j) e) := by
              rw [Finset.sum_comm]
        _ = Finset.sum I x := by
              refine Finset.sum_congr rfl ?_
              intro e he
              simpa using
                weightedSumApply (G := G) w (fun j ↦ G.subgraphIncidenceVector ℝ (M j))
                  hx_sum_match e
        _ = 1 := by
              exact hx_deg v
    have hle :
        ∀ j, I.sum (G.subgraphIncidenceVector ℝ (M j)) ≤ 1 := by
      intro j
      simpa [I] using matchingIncidenceSumLeOne (G := G) (hMatch j) v
    have hi_sum_eq_one :
        I.sum (G.subgraphIncidenceVector ℝ (M i)) = 1 :=
      eqOneOfWeightedAverageEqOne hw_nonneg hle hw_sum havg i hwi
    by_contra hv
    have hi_sum_eq_zero :
        I.sum (G.subgraphIncidenceVector ℝ (M i)) = 0 := by
      simpa [I] using subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) (M := M i) hv
    linarith
  have hweight_nonzero : ∑ i, w i ≠ 0 := by
    rw [hw_sum]
    norm_num
  obtain ⟨i₀, -, hi₀_nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero hweight_nonzero
  have hM₀_perfect : (M i₀).IsPerfectMatching := hsupport_perfect i₀ hi₀_nonzero
  let zPerfect : ι → G.edgeSet → ℝ :=
    fun i ↦ if hwi : w i = 0 then G.subgraphIncidenceVector ℝ (M i₀) else z i
  have hzPerfect :
      ∀ i, ∃ N : G.Subgraph, N.IsPerfectMatching ∧ zPerfect i = G.subgraphIncidenceVector ℝ N := by
    intro i
    by_cases hwi : w i = 0
    · refine ⟨M i₀, hM₀_perfect, ?_⟩
      simp [zPerfect, hwi]
    · refine ⟨M i, hsupport_perfect i hwi, ?_⟩
      simp [zPerfect, hwi, hVec i]
  have hx_sum_perfect : ∑ i, w i • zPerfect i = x := by
    calc
      ∑ i, w i • zPerfect i = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hwi : w i = 0
        · ext e
          simp [zPerfect, hwi]
        · ext e
          simp [zPerfect, hwi]
      _ = x := hx_sum
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype]
  refine ⟨ι, inferInstance, w, zPerfect, hw_nonneg, hw_sum, ?_, hx_sum_perfect⟩
  intro i
  rcases hzPerfect i with ⟨N, hN, hzN⟩
  exact ⟨N, hN, hzN⟩

/-- Helper for Theorem 4.23: every perfect-matching generator already satisfies the perfect
constraint system, so the whole perfect matching polytope lies in the constraint set. -/
private lemma perfectMatchingPolytope_subset_perfectMatchingConstraintSet :
    perfectMatchingPolytope G ⊆ perfectMatchingConstraintSet G := by
  intro x hx
  -- The generator feasibility check extends from perfect matchings to their convex hull.
  rw [SimpleGraph.perfectMatchingPolytope] at hx
  refine convexHull_min ?_ (convexPerfectMatchingConstraintSet (G := G)) hx
  intro y hy
  rcases hy with ⟨M, hM, rfl⟩
  exact subgraphIncidenceVector_mem_perfectMatchingConstraintSet (G := G) hM

/-- Helper for Theorem 4.23: every perfect-matching generator is already a matching generator, so
the perfect matching polytope sits inside the ambient matching polytope. -/
private lemma perfectMatchingPolytope_subset_matchingPolytope :
    perfectMatchingPolytope G ⊆ matchingPolytope G := by
  -- Rewrite both owners as convex hulls and use the inclusion of perfect-matchings into
  -- matchings generatorwise.
  rw [SimpleGraph.perfectMatchingPolytope, SimpleGraph.matchingPolytope]
  exact convexHull_mono <| by
    intro x hx
    rcases hx with ⟨M, hM, rfl⟩
    exact ⟨M, hM.1, rfl⟩

/-- Helper for Theorem 4.23: every feasible edge coordinate of `perfectMatchingConstraintSet G`
is bounded above by `1`. -/
private lemma edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) (e : G.edgeSet) :
    x e ≤ 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset e.1.out.1
  have heI : e ∈ I := by
    simp [I, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff,
      Sym2.out_fst_mem]
  have hsingle : x e ≤ I.sum x := by
    exact Finset.single_le_sum (fun f _ ↦ hx_nonneg f) heI
  have hsum_eq : I.sum x = 1 := by
    simpa [I] using hx_deg e.1.out.1
  linarith

/-- Helper for Theorem 4.23: if a feasible perfect-matching point avoids the reducible `0/1`
coordinates, then every edge coordinate lies strictly between `0` and `1`. -/
private lemma edgeCoordinateStrictBounds_of_mem_perfectMatchingConstraintSet_of_ne_zero_ne_one
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_ne_zero : ∀ e : G.edgeSet, x e ≠ 0)
    (hx_ne_one : ∀ e : G.edgeSet, x e ≠ 1) :
    ∀ e : G.edgeSet, 0 < x e ∧ x e < 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  intro e
  constructor
  · -- Without a zero coordinate, nonnegativity upgrades to strict positivity.
    exact lt_of_le_of_ne (hx_nonneg e) (by
      intro h
      exact hx_ne_zero e h.symm)
  · -- Without a unit coordinate, the degree-one upper bound upgrades to strict inequality.
    exact lt_of_le_of_ne
      (edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e)
      (hx_ne_one e)

/-- Helper for Theorem 4.23: if one incident edge already has weight `1`, then every other edge
incident to the same vertex must have weight `0`. -/
private lemma eqZeroOfOtherIncidentEdge_of_incidenceSumEqOne
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) {v : V}
    {e f : G.edgeSet}
    (heI : e ∈ Finset.univ.filter
      fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v)
    (hxe : x e = 1)
    (hfI : f ∈ Finset.univ.filter
      fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v)
    (hf_ne : f ≠ e) :
    x f = 0 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun g : G.edgeSet ↦ (g : Sym2 V) ∈ G.incidenceFinset v
  have hsum_eq : I.sum x = 1 := by
    -- The Chapter 4.23 degree equation fixes the whole incidence sum at `v`.
    simpa [I] using hx_deg v
  have hdecomp : x e + (I.erase e).sum x = I.sum x := by
    exact Finset.add_sum_erase I x (by simpa [I] using heI)
  have hfErase : f ∈ I.erase e := by
    simpa [I] using Finset.mem_erase.mpr ⟨hf_ne, hfI⟩
  have hsingle : x f ≤ (I.erase e).sum x := by
    -- Any second incident edge is bounded by the residual incidence mass at `v`.
    exact Finset.single_le_sum (fun g _ ↦ hx_nonneg g) hfErase
  have hrest_zero : (I.erase e).sum x = 0 := by
    linarith
  have hxf_le_zero : x f ≤ 0 := by
    simpa [hrest_zero] using hsingle
  linarith [hx_nonneg f, hxf_le_zero]

/-- Helper for Theorem 4.23: an integer point of `perfectMatchingConstraintSet G` has only `0/1`
edge coordinates. -/
private lemma edgeCoordinateEqZeroOrOneOfMemPerfectMatchingConstraintSetOfInteger
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  rcases hx_int with ⟨z, rfl⟩
  have hz_nonneg : (0 : ℤ) ≤ z e := by
    have hreal : (0 : ℝ) ≤ (z e : ℝ) := by simpa using hx_nonneg e
    exact_mod_cast hreal
  have hz_le_one : z e ≤ 1 := by
    have hreal : ((z e : ℝ) ≤ 1) := by
      simpa using edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet
        (G := G) (x := Int.cast ∘ z) hx e
    exact_mod_cast hreal
  have hz_cases : z e = 0 ∨ z e = 1 := by
    omega
  rcases hz_cases with hzero | hone
  · left
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hzero
  · right
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hone

/-- Helper for Theorem 4.23: an integer point of `perfectMatchingConstraintSet G` is already the
incidence vector of a perfect matching. -/
private lemma integerPoint_eq_subgraphIncidenceVector_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, -⟩
  have hx_zero_one : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
    intro e
    exact edgeCoordinateEqZeroOrOneOfMemPerfectMatchingConstraintSetOfInteger
      (G := G) hx hx_int e
  let M : G.Subgraph :=
    { verts := {v : V | ∃ w, ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1}
      Adj := fun v w ↦ ∃ h : G.Adj v w, x ⟨s(v, w), G.mem_edgeSet.2 h⟩ = 1
      adj_sub := fun h ↦ h.1
      edge_vert := fun h ↦ ⟨_, h⟩
      symm := by
        intro v w h
        rcases h with ⟨hvw, hxvw⟩
        refine ⟨hvw.symm, ?_⟩
        simpa [Sym2.eq_swap] using hxvw }
  have hMemEdge :
      ∀ e : G.edgeSet, e.1 ∈ M.edgeSet ↔ x e = 1 := by
    intro e
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      rw [← G.mem_edgeSet]
      simpa [e.1.out_eq] using e.2
    rw [← e.1.out_eq, Subgraph.mem_edgeSet]
    constructor
    · rintro ⟨hG, hxG⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hG⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hxG
    · intro hx1
      refine ⟨hadj, ?_⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hx1
  have hAllVerts : ∀ v : V, v ∈ M.verts := by
    intro v
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    have hsum_ne_zero : I.sum x ≠ 0 := by
      rw [hx_deg v]
      norm_num
    obtain ⟨e, heI, hxe_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne_zero
    have hxe_one : x e = 1 := by
      rcases hx_zero_one e with hxe_zero | hxe_one
      · exact (hxe_ne hxe_zero).elim
      · exact hxe_one
    have hvMem : v ∈ (e : Sym2 V) := by
      have heInc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp heI).2
      simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using heInc
    let w : V := Sym2.Mem.other hvMem
    have hAdj : G.Adj v w := by
      exact (SimpleGraph.mem_edgeSet (G := G) (v := v) (w := w)).1
        (by simpa [w, Sym2.other_spec hvMem] using e.prop)
    have hSubtype : (⟨s(v, w), G.mem_edgeSet.2 hAdj⟩ : G.edgeSet) = e := by
      apply Subtype.ext
      simpa [w] using Sym2.other_spec hvMem
    -- A nonzero incidence term at `v` provides a support edge through `v`.
    refine ⟨w, hAdj, ?_⟩
    simpa [hSubtype] using hxe_one
  have hMatching : M.IsMatching := by
    intro v hv
    rcases hv with ⟨w, hvw, hxvw⟩
    refine ⟨w, ⟨hvw, hxvw⟩, ?_⟩
    intro u hu
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v
    let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
    let f : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.2 hu.1⟩
    have heI : e ∈ I := by
      simp [I, e, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have hfI : f ∈ I := by
      simp [I, f, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have hxe_one : x e = 1 := by simpa [e] using hxvw
    have hxf_one : x f = 1 := by simpa [f] using hu.2
    by_contra hwu
    have hfe : f ≠ e := by
      intro hfeEq
      apply hwu
      have hs : s(v, u) = s(v, w) := by
        simpa [f, e] using congrArg Subtype.val hfeEq
      exact Sym2.congr_right.mp hs
    have hfErase : f ∈ I.erase e := Finset.mem_erase.mpr ⟨hfe, hfI⟩
    have hsum_erase_ge_one : 1 ≤ (I.erase e).sum x := by
      have hsingle : x f ≤ (I.erase e).sum x := by
        exact Finset.single_le_sum (fun g _ ↦ hx_nonneg g) hfErase
      linarith
    have hsum_eq_one : I.sum x = 1 := by
      simpa [I] using hx_deg v
    have hdecomp : x e + (I.erase e).sum x = I.sum x := by
      exact Finset.add_sum_erase I x heI
    linarith
  have hPerfect : M.IsPerfectMatching := by
    refine ⟨hMatching, ?_⟩
    intro v
    exact hAllVerts v
  refine ⟨M, hPerfect, ?_⟩
  funext e
  by_cases hxe : x e = 1
  · have heM : e.1 ∈ M.edgeSet := (hMemEdge e).2 hxe
    simp [SimpleGraph.subgraphIncidenceVector, heM, hxe]
  · have hxe_zero : x e = 0 := by
      rcases hx_zero_one e with hzero | hone
      · exact hzero
      · exact (hxe hone).elim
    have heM : e.1 ∉ M.edgeSet := by
      intro heM
      exact hxe ((hMemEdge e).1 heM)
    simp [SimpleGraph.subgraphIncidenceVector, heM, hxe_zero]

/-- Helper for Theorem 4.23: a subgraph incidence vector is an integer lattice point in the edge
coordinate space. -/
private lemma subgraphIncidenceVector_memIntegerRange (M : G.Subgraph) :
    G.subgraphIncidenceVector ℝ M ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) := by
  refine ⟨fun e : G.edgeSet ↦ if e.1 ∈ M.edgeSet then 1 else 0, ?_⟩
  -- Evaluate the coordinatewise `0/1` witness at each edge.
  funext e
  by_cases heM : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, heM]
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Theorem 4.23: a nonintegral point of the perfect-matching constraint set has a
truly fractional edge coordinate. -/
private lemma exists_fractionalEdge_of_mem_perfectMatchingConstraintSet_of_not_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ e : G.edgeSet, 0 < x e ∧ x e < 1 := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  by_contra hfrac
  have hzero_one : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1 := by
    intro e
    by_cases hpos : 0 < x e
    · right
      have hone_le : 1 ≤ x e := by
        by_contra hone_lt
        exact hfrac ⟨e, hpos, lt_of_not_ge hone_lt⟩
      linarith [edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e, hone_le]
    · left
      linarith [hx_nonneg e]
  let z : G.edgeSet → ℤ := fun e ↦ if x e = 0 then 0 else 1
  have hz : x = Int.cast ∘ z := by
    -- Every coordinate is already forced into the `0/1` integer range.
    funext e
    rcases hzero_one e with hzero | hone
    · simp [z, hzero]
    · simp [z, hone]
  exact hx_not_int ⟨z, hz.symm⟩

/-- Helper for Theorem 4.23: a nonintegral extreme point of the perfect-matching constraint set
cannot come from the bipartite case, because there the constraint set already equals the perfect
matching polytope. -/
private lemma not_isBipartite_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ¬ G.IsBipartite := by
  intro hG
  have hxExtremePoly :
      x ∈ (perfectMatchingPolytope G).extremePoints ℝ := by
    -- In the bipartite case both owners share the same matrix description.
    simpa [SimpleGraph.perfectMatchingConstraintSet_eq_setOf_mulVec_eq_one,
      SimpleGraph.perfectMatchingPolytope_eq_setOf_mulVec_eq_one, hG] using hx
  rw [SimpleGraph.perfectMatchingPolytope] at hxExtremePoly
  rcases extremePoints_convexHull_subset hxExtremePoly with ⟨M, hM, rfl⟩
  -- A perfect-matching generator is visibly integer-valued, contradicting nonintegrality.
  exact hx_not_int (subgraphIncidenceVector_memIntegerRange (G := G) M)

/-- Helper for Theorem 4.23: every edge surviving deletion is still an edge of the original
graph. -/
private lemma memEdgeSetOfMemDeleteEdges (s : Set (Sym2 V)) {f : Sym2 V}
    (hf : f ∈ (G.deleteEdges s).edgeSet) : f ∈ G.edgeSet := by
  -- Deletion only removes edges from the original edge set.
  rw [SimpleGraph.edgeSet_deleteEdges] at hf
  exact hf.1

/-- Helper for Theorem 4.23: after deleting an edge on which `x` vanishes, every filtered sum of
the restricted coordinates agrees with the corresponding sum on the original graph. -/
private lemma sumDeleteEdgeRestrictionEq
    (x : G.edgeSet → ℝ) (e : G.edgeSet) (he : x e = 0)
    [DecidableRel (G.deleteEdges ({e.1} : Set (Sym2 V))).Adj]
    (pG : G.edgeSet → Prop) [DecidablePred pG]
    (pH : (G.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet → Prop) [DecidablePred pH]
    (hp : ∀ f, pH f ↔ pG ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩) :
    (Finset.univ.filter pH).sum
        (fun f ↦ x ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩) =
      (Finset.univ.filter pG).sum x := by
  let H := G.deleteEdges ({e.1} : Set (Sym2 V))
  let liftEdge : H.edgeSet → G.edgeSet :=
    fun f ↦ ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩
  let kept : Finset G.edgeSet :=
    Finset.univ.filter fun f ↦ f.1 ∈ H.edgeSet ∧ pG f
  have hrestricted :
      (Finset.univ.filter pH).sum (fun f ↦ x (liftEdge f)) = kept.sum x := by
    -- The inclusion of the deleted graph's edge type bijects its filtered coordinates with the
    -- original filtered coordinates that survive deletion.
    refine Finset.sum_bij (fun f _ ↦ liftEdge f) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [kept, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, f.2, (hp f).1 (Finset.mem_filter.mp hf).2⟩
    · intro f₁ hf₁ f₂ hf₂ hEq
      apply Subtype.ext
      simpa [liftEdge] using congrArg Subtype.val hEq
    · intro f hf
      have hf' := (Finset.mem_filter.mp hf).2
      let fH : H.edgeSet := ⟨f.1, hf'.1⟩
      refine ⟨fH, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hp fH).2 hf'.2⟩
      · apply Subtype.ext
        rfl
    · intro f hf
      rfl
  have hkept_subset : kept ⊆ Finset.univ.filter pG := by
    intro f hf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2.2⟩
  have hsum_kept : kept.sum x = (Finset.univ.filter pG).sum x := by
    -- The only omitted original edge is `e`, whose coordinate is zero.
    refine Finset.sum_subset hkept_subset ?_
    intro f hfG hfKept
    have hf_not_H : f.1 ∉ H.edgeSet := by
      intro hfH
      exact hfKept <| Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hfH, (Finset.mem_filter.mp hfG).2⟩
    have hf_mem_deleted : f.1 ∈ ({e.1} : Set (Sym2 V)) := by
      by_contra hf_not_deleted
      apply hf_not_H
      simpa [H, SimpleGraph.edgeSet_deleteEdges] using And.intro f.2 hf_not_deleted
    have hf_eq : f = e := by
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp hf_mem_deleted
    simpa [hf_eq] using he
  -- First identify the surviving coordinates, then restore the deleted zero coordinate.
  exact hrestricted.trans hsum_kept

/-- Helper for Theorem 4.23: mapping a subgraph of an edge-deleted graph back into the original
graph preserves every surviving incidence-vector coordinate. -/
private lemma subgraphIncidenceVectorMapDeleteEdges_apply
    (s : Set (Sym2 V))
    (M : (G.deleteEdges s).Subgraph) (f : (G.deleteEdges s).edgeSet) :
    G.subgraphIncidenceVector ℝ (M.map (Hom.ofLE (G.deleteEdges_le s)))
        ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) s f.2⟩ =
      (G.deleteEdges s).subgraphIncidenceVector ℝ M f := by
  -- The inclusion homomorphism is the identity on endpoints, so it preserves edge membership.
  simp [SimpleGraph.subgraphIncidenceVector, Subgraph.edgeSet_map, Sym2.map_id']

/-- Helper for Theorem 4.23: a subgraph lifted from the graph with `e` deleted has zero incidence
coordinate at `e`. -/
private lemma subgraphIncidenceVectorMapDeleteEdge_eq_zero
    (e : G.edgeSet) (M : (G.deleteEdges ({e.1} : Set (Sym2 V))).Subgraph) :
    G.subgraphIncidenceVector ℝ
        (M.map (Hom.ofLE (G.deleteEdges_le ({e.1} : Set (Sym2 V))))) e = 0 := by
  have he_not_mem : e.1 ∉ M.edgeSet := by
    intro heM
    have heDeleted : e.1 ∈ (G.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet :=
      M.edgeSet_subset heM
    rw [SimpleGraph.edgeSet_deleteEdges] at heDeleted
    exact heDeleted.2 (Set.mem_singleton e.1)
  -- The mapped edge set is unchanged as a set of unordered endpoint pairs.
  simp [SimpleGraph.subgraphIncidenceVector, Subgraph.edgeSet_map, he_not_mem]

/-- Helper for Theorem 4.23: a zero edge coordinate can be deleted, solved by the smaller-graph
hypothesis, and then lifted back to the original perfect matching polytope. -/
private lemma memPerfectMatchingPolytopeOfZeroCoordinate
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G)
    (e : G.edgeSet) (he : x e = 0) :
    x ∈ perfectMatchingPolytope G := by
  let H := G.deleteEdges ({e.1} : Set (Sym2 V))
  -- Local instance justification (definitional alignment): the induction hypothesis quantifies
  -- over this canonical graph-decidability instance, while deletion supplies a different one.
  letI : DecidableRel H.Adj := _root_.instDecidableRelAdj_integer H
  let xH : H.edgeSet → ℝ :=
    fun f ↦ x ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_degree, hx_cut⟩
  have hxH : xH ∈ perfectMatchingConstraintSet H := by
    rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact hx_nonneg ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩
    · intro v
      have hpred : ∀ f : H.edgeSet,
          ((f : Sym2 V) ∈ H.incidenceFinset v) ↔
            ((⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩ : G.edgeSet) : Sym2 V) ∈
              G.incidenceFinset v := by
        intro f
        simp only [SimpleGraph.mem_incidenceFinset,
          SimpleGraph.edge_mem_incidenceSet_iff]
        exact (G.edge_mem_incidenceSet_iff
          (a := v) (e := ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩)).symm
      have hsum := sumDeleteEdgeRestrictionEq (G := G) x e he
        (fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v)
        (fun f : H.edgeSet ↦ (f : Sym2 V) ∈ H.incidenceFinset v) hpred
      have hsum' :
          (Finset.univ.filter fun f : H.edgeSet ↦
              (f : Sym2 V) ∈ H.incidenceFinset v).sum xH =
            (Finset.univ.filter fun f : G.edgeSet ↦
              (f : Sym2 V) ∈ G.incidenceFinset v).sum x := by
        simpa [xH, H] using hsum
      exact hsum'.trans (hx_degree v)
    · intro S hS
      have hpred : ∀ f : H.edgeSet,
          f ∈ δ[H] S ↔
            (⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩ : G.edgeSet) ∈ δ[G] S := by
        intro f
        rw [SimpleGraph.mem_cutEdgeFinset_iff, SimpleGraph.mem_cutEdgeFinset_iff]
      have hsum := sumDeleteEdgeRestrictionEq (G := G) x e he
        (fun f : G.edgeSet ↦ f ∈ δ[G] S)
        (fun f : H.edgeSet ↦ f ∈ δ[H] S) hpred
      rw [show (δ[H] S).sum xH = (δ[G] S).sum x by simpa [xH, H] using hsum]
      exact hx_cut S hS
  have hcard :
      Fintype.card V + Fintype.card H.edgeSet <
        Fintype.card V + Fintype.card G.edgeSet := by
    have hedge : Fintype.card H.edgeSet < Fintype.card G.edgeSet := by
      let liftEdge : H.edgeSet → G.edgeSet :=
        fun f ↦ ⟨f.1, memEdgeSetOfMemDeleteEdges (G := G) _ f.2⟩
      have hlift_injective : Function.Injective liftEdge := by
        intro f₁ f₂ hEq
        apply Subtype.ext
        simpa [liftEdge] using congrArg Subtype.val hEq
      have hlift_not_surjective : ¬Function.Surjective liftEdge := by
        intro hsurj
        rcases hsurj e with ⟨f, hf⟩
        have hfDeleted : f.1 ∈ G.edgeSet \ ({e.1} : Set (Sym2 V)) := by
          simpa [H, SimpleGraph.edgeSet_deleteEdges] using f.2
        have hval : f.1 = e.1 := by
          simpa [liftEdge] using congrArg Subtype.val hf
        exact hfDeleted.2 (by simpa [hval])
      exact Fintype.card_lt_of_injective_not_surjective
        liftEdge hlift_injective hlift_not_surjective
    omega
  have hxPolyH : xH ∈ perfectMatchingPolytope H := hsmaller H hcard hxH
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype] at hxPolyH ⊢
  rcases hxPolyH with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
  have hz' : ∀ i, ∃ M : H.Subgraph,
      M.IsPerfectMatching ∧ z i = H.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hM hVec using hz'
  let liftM : ι → G.Subgraph :=
    fun i ↦ (M i).map (Hom.ofLE (G.deleteEdges_le ({e.1} : Set (Sym2 V))))
  have hLiftPerfect : ∀ i, (liftM i).IsPerfectMatching := by
    intro i
    refine ⟨(hM i).1.map_ofLE (G.deleteEdges_le _), ?_⟩
    intro v
    simp [liftM, Subgraph.map_verts, (hM i).2 v]
  refine ⟨ι, inferInstance, w,
    fun i ↦ G.subgraphIncidenceVector ℝ (liftM i), hw_nonneg, hw_sum, ?_, ?_⟩
  · intro i
    exact ⟨liftM i, hLiftPerfect i, rfl⟩
  · -- Verify the lifted barycenter separately on the deleted coordinate and every surviving one.
    funext f
    by_cases hf : f = e
    · subst f
      have hzero : ∀ i,
          G.subgraphIncidenceVector ℝ (liftM i) e = 0 := by
        intro i
        simpa [liftM, H] using
          subgraphIncidenceVectorMapDeleteEdge_eq_zero (G := G) e (M i)
      calc
        (∑ i, w i • G.subgraphIncidenceVector ℝ (liftM i)) e =
            ∑ i, w i * G.subgraphIncidenceVector ℝ (liftM i) e := by
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        _ = 0 := Finset.sum_eq_zero fun i hi ↦ by rw [hzero i, mul_zero]
        _ = x e := he.symm
    · have hfH : f.1 ∈ H.edgeSet := by
        change f.1 ∈ (G.deleteEdges ({e.1} : Set (Sym2 V))).edgeSet
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨f.2, by simpa [Set.mem_singleton_iff, Subtype.ext_iff] using hf⟩
      let fH : H.edgeSet := ⟨f.1, hfH⟩
      have hfLift :
          (⟨fH.1, memEdgeSetOfMemDeleteEdges (G := G) _ fH.2⟩ : G.edgeSet) = f := by
        apply Subtype.ext
        rfl
      calc
        (∑ i, w i • G.subgraphIncidenceVector ℝ (liftM i)) f =
            ∑ i, w i * H.subgraphIncidenceVector ℝ (M i) fH := by
              simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcoord := subgraphIncidenceVectorMapDeleteEdges_apply
                (G := G) ({e.1} : Set (Sym2 V)) (M i) fH
              simpa [liftM, H, hfLift] using congrArg (fun a ↦ w i * a) hcoord
        _ = ∑ i, w i * z i fH := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hVec i]
        _ = xH fH := weightedSumApply (G := H) w z hx_sum fH
        _ = x f := rfl

/-- Helper for Theorem 4.23: the canonical shore projection retains vertices of `S` and sends
the complementary shore to one collapsed vertex. -/
private def shoreProjection (S : Finset V) : V → Option S :=
  fun v ↦ if hv : v ∈ S then some ⟨v, hv⟩ else none

/-- Helper for Theorem 4.23: a vertex in the retained shore is fixed by the shore projection. -/
@[simp] private lemma shoreProjection_apply_of_mem (S : Finset V) {v : V} (hv : v ∈ S) :
    shoreProjection S v = some ⟨v, hv⟩ := by
  -- The membership branch of the projection keeps the vertex and its shore certificate.
  simp [shoreProjection, hv]

/-- Helper for Theorem 4.23: a vertex outside the retained shore maps to the collapsed vertex. -/
@[simp] private lemma shoreProjection_apply_of_notMem (S : Finset V) {v : V} (hv : v ∉ S) :
    shoreProjection S v = none := by
  -- The complementary branch of the projection is definitionally the collapsed vertex.
  simp [shoreProjection, hv]

/-- Helper for Theorem 4.23: the shore projection is injective on the retained shore. -/
private lemma shoreProjection_injOn (S : Finset V) :
    Set.InjOn (shoreProjection S) (S : Set V) := by
  intro v hv w hw hvw
  -- On the retained shore both images are `some`, so equality remembers the original vertices.
  have hsome : (some ⟨v, hv⟩ : Option S) = some ⟨w, hw⟩ := by
    rw [← shoreProjection_apply_of_mem S hv, ← shoreProjection_apply_of_mem S hw]
    exact hvw
  exact congrArg Subtype.val (Option.some.inj hsome)

/-- Helper for Theorem 4.23: a vertex projects to `some u` exactly when it is the retained
vertex underlying `u`. -/
private lemma shoreProjection_eq_some_iff (S : Finset V) {v : V} {u : S} :
    shoreProjection S v = some u ↔ v = u.1 := by
  constructor
  · intro hv
    -- Any `some` image comes from the retained branch, so equality recovers the underlying
    -- original vertex.
    by_cases hmem : v ∈ S
    · rw [shoreProjection_apply_of_mem (G := G) S hmem] at hv
      exact congrArg Subtype.val (Option.some.inj hv)
    · rw [shoreProjection_apply_of_notMem (G := G) S hmem] at hv
      simp at hv
  · intro hv
    -- Conversely, a retained vertex projects back to its own `some` representative.
    subst hv
    rw [shoreProjection_apply_of_mem (G := G) S u.2]
    rfl

/-- Helper for Theorem 4.23: the graph obtained by retaining `S` and collapsing its complement. -/
private def shoreContraction (S : Finset V) : SimpleGraph (Option S) :=
  G.map (shoreProjection S)

/-- Helper for Theorem 4.23: push an edge vector forward to a shore contraction by summing all
original coordinates with the same projected unordered pair. -/
private def shorePushforward (S : Finset V) (x : G.edgeSet → ℝ) :
    (shoreContraction G S).edgeSet → ℝ :=
  fun f ↦ ∑ e : G.edgeSet,
    if Sym2.map (shoreProjection S) e.1 = f.1 then x e else 0

/-- Helper for Theorem 4.23: the original edges mapping into a finite family of contracted
edges. -/
private def shorePreimageEdgeFinset (S : Finset V)
    (A : Finset (shoreContraction G S).edgeSet) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦
    ∃ f ∈ A, Sym2.map (shoreProjection S) e.1 = f.1

/-- Helper for Theorem 4.23: summing a shore pushforward over contracted edges equals the sum
over precisely their original-edge preimage. -/
private lemma shorePushforward_sum_preimage (S : Finset V) (x : G.edgeSet → ℝ)
    (A : Finset (shoreContraction G S).edgeSet) :
    A.sum (shorePushforward G S x) =
      (shorePreimageEdgeFinset G S A).sum x := by
  classical
  -- Swap the two finite sums, then use uniqueness of a contracted edge with a fixed value.
  simp only [shorePushforward]
  rw [shorePreimageEdgeFinset, Finset.sum_filter, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e he
  by_cases hpre : ∃ f ∈ A, Sym2.map (shoreProjection S) e.1 = f.1
  · obtain ⟨f, hfA, hmap⟩ := hpre
    rw [if_pos ⟨f, hfA, hmap⟩]
    refine Finset.sum_eq_single f ?_ ?_
    · intro g hgA hgf
      have hval_ne : f.1 ≠ g.1 := by
        intro hval
        exact hgf (Subtype.ext hval)
      simp [hmap, hval_ne]
    · exact hfA
  · rw [if_neg hpre]
    refine Finset.sum_eq_zero ?_
    intro f hfA
    have hmap_ne : Sym2.map (shoreProjection S) e.1 ≠ f.1 := by
      intro hmap
      exact hpre ⟨f, hfA, hmap⟩
    simp [hmap_ne]

/-- Helper for Theorem 4.23: every edge of a shore contraction has an original edge mapping to
it. -/
private lemma shoreContractionEdge_exists_preimage (S : Finset V)
    (f : (shoreContraction G S).edgeSet) :
    ∃ e : G.edgeSet, Sym2.map (shoreProjection S) e.1 = f.1 := by
  have hfAdj : (shoreContraction G S).Adj f.1.out.1 f.1.out.2 := by
    rw [← (shoreContraction G S).mem_edgeSet]
    simpa [f.1.out_eq] using f.2
  rcases (SimpleGraph.map_adj' (shoreProjection S) G _ _).1 hfAdj with
    ⟨-, v, w, hvw, hv, hw⟩
  let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
  refine ⟨e, ?_⟩
  -- The chosen original endpoints map to the canonical endpoints of the contracted edge.
  calc
    Sym2.map (shoreProjection S) e.1 = s(shoreProjection S v, shoreProjection S w) := by
      simp [e]
    _ = s(f.1.out.1, f.1.out.2) := by rw [hv, hw]
    _ = f.1 := f.1.out_eq

/-- Helper for Theorem 4.23: choose one original edge above each contracted edge. -/
private noncomputable def shoreOriginalEdge (S : Finset V)
    (f : (shoreContraction G S).edgeSet) : G.edgeSet :=
  Classical.choose (shoreContractionEdge_exists_preimage (G := G) S f)

/-- Helper for Theorem 4.23: the chosen original edge maps back to its contracted edge. -/
private lemma shoreOriginalEdge_map (S : Finset V)
    (f : (shoreContraction G S).edgeSet) :
    Sym2.map (shoreProjection S) (shoreOriginalEdge G S f).1 = f.1 := by
  -- This is the specification of the chosen preimage edge.
  exact Classical.choose_spec (shoreContractionEdge_exists_preimage (G := G) S f)

/-- Helper for Theorem 4.23: choosing one original edge above each contracted edge gives an
injection. -/
private lemma shoreOriginalEdge_injective (S : Finset V) :
    Function.Injective (shoreOriginalEdge G S) := by
  intro f g hfg
  -- Mapping an equality of chosen preimages recovers equality of contracted edge values.
  apply Subtype.ext
  calc
    f.1 = Sym2.map (shoreProjection S) (shoreOriginalEdge G S f).1 :=
      (shoreOriginalEdge_map (G := G) S f).symm
    _ = Sym2.map (shoreProjection S) (shoreOriginalEdge G S g).1 := by rw [hfg]
    _ = g.1 := shoreOriginalEdge_map (G := G) S g

/-- Helper for Theorem 4.23: collapsing a complementary shore of size at least two strictly
decreases the vertex-plus-edge induction measure. -/
private lemma shoreContraction_measure_lt (S : Finset V)
    (hcompl : 1 < (Finset.univ \ S).card) :
    Fintype.card (Option S) + Fintype.card (shoreContraction G S).edgeSet <
      Fintype.card V + Fintype.card G.edgeSet := by
  have hvertices : Fintype.card (Option S) < Fintype.card V := by
    have hpartition := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ] at hpartition
    simp only [Fintype.card_option, Fintype.card_coe]
    omega
  have hedges : Fintype.card (shoreContraction G S).edgeSet ≤ Fintype.card G.edgeSet :=
    Fintype.card_le_of_injective (shoreOriginalEdge G S)
      (shoreOriginalEdge_injective (G := G) S)
  omega

/-- Helper for Theorem 4.23: the preimage of a cut in a shore contraction is the cut of the
vertex-set preimage in the original graph. -/
private lemma shorePreimageEdgeFinset_cut (S : Finset V) (U : Set (Option S)) :
    shorePreimageEdgeFinset G S (δ[shoreContraction G S] U) =
      δ[G] (shoreProjection S ⁻¹' U) := by
  classical
  ext e
  simp only [shorePreimageEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hfCut, hmap⟩
    rcases (SimpleGraph.mem_cutEdgeFinset_iff
      (G := shoreContraction G S) (S := U) (e := f)).1 hfCut with
      ⟨a, ha, b, hb, hab⟩
    have hpair :
        s(shoreProjection S e.1.out.1, shoreProjection S e.1.out.2) = s(a, b) := by
      calc
        s(shoreProjection S e.1.out.1, shoreProjection S e.1.out.2) =
            Sym2.map (shoreProjection S) e.1 := by
              exact (Sym2.map_mk _ _ _).symm.trans
                (congrArg (Sym2.map (shoreProjection S)) e.1.out_eq)
        _ = f.1 := hmap
        _ = s(a, b) := hab.symm
    rw [Sym2.eq_iff] at hpair
    rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).2
        ⟨e.1.out.1, by simpa [h₁] using ha, e.1.out.2, by simpa [h₂] using hb,
          e.1.out_eq⟩
    · exact (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).2
        ⟨e.1.out.2, by simpa [h₂] using ha, e.1.out.1, by simpa [h₁] using hb,
          Sym2.eq_swap.trans e.1.out_eq⟩
  · intro heCut
    rcases (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).1 heCut with
      ⟨v, hv, w, hw, hvw⟩
    have hproj_ne : shoreProjection S v ≠ shoreProjection S w := by
      intro hEq
      exact hw (by simpa [hEq] using hv)
    have hAdj : G.Adj v w := by
      rw [← G.mem_edgeSet]
      simpa [hvw] using e.2
    have hMapAdj :
        (shoreContraction G S).Adj (shoreProjection S v) (shoreProjection S w) := by
      exact (SimpleGraph.map_adj' (shoreProjection S) G _ _).2
        ⟨hproj_ne, v, w, hAdj, rfl, rfl⟩
    let f : (shoreContraction G S).edgeSet :=
      ⟨s(shoreProjection S v, shoreProjection S w),
        (shoreContraction G S).mem_edgeSet.2 hMapAdj⟩
    refine ⟨f, ?_, ?_⟩
    · exact (SimpleGraph.mem_cutEdgeFinset_iff (G := shoreContraction G S)).2
        ⟨shoreProjection S v, hv, shoreProjection S w, hw, rfl⟩
    · calc
        Sym2.map (shoreProjection S) e.1 =
            Sym2.map (shoreProjection S) s(v, w) := by rw [hvw]
        _ = f.1 := rfl

/-- Helper for Theorem 4.23: a singleton cut is the edge-coordinate incidence filter at its
vertex. -/
private lemma cutSingleton_eq_incidenceFilter (v : V) :
    δ[G] ({v} : Set V) =
      Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
  ext e
  have hmem : (∃ w : V, w ≠ v ∧ s(v, w) = (e : Sym2 V)) ↔ v ∈ (e : Sym2 V) := by
    constructor
    · rintro ⟨w, -, hEq⟩
      rw [← hEq]
      simp
    · intro he
      refine ⟨Sym2.Mem.other he, Sym2.other_ne (G.not_isDiag_of_mem_edgeSet e.2) he, ?_⟩
      exact Sym2.other_spec he
  -- Both descriptions say that the edge has `v` as exactly one of its endpoints.
  simp [SimpleGraph.mem_cutEdgeFinset_iff, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.edge_mem_incidenceSet_iff, hmem]

/-- Helper for Theorem 4.23: pulling back a retained singleton along the shore projection gives
the corresponding original singleton. -/
private lemma shoreProjection_preimage_singleton_some (S : Finset V) (v : S) :
    shoreProjection S ⁻¹' ({some v} : Set (Option S)) = ({v.1} : Set V) := by
  ext w
  by_cases hw : w ∈ S
  · simp [shoreProjection, hw, Subtype.ext_iff]
  · have hwne : w ≠ v.1 := by
      intro hwv
      exact hw (hwv ▸ v.2)
    simp [shoreProjection, hw, hwne]

/-- Helper for Theorem 4.23: pulling back the collapsed singleton is the complementary shore. -/
private lemma shoreProjection_preimage_singleton_none (S : Finset V) :
    shoreProjection S ⁻¹' ({none} : Set (Option S)) = (S : Set V)ᶜ := by
  ext v
  by_cases hv : v ∈ S
  · simp [shoreProjection, hv]
  · simp [shoreProjection, hv]

/-- Helper for Theorem 4.23: a cut is unchanged when its two shores are exchanged. -/
private lemma cutEdgeFinset_compl (S : Set V) :
    δ[G] Sᶜ = δ[G] S := by
  ext e
  rw [memCutEdgeFinsetEndpointsIff (G := G), memCutEdgeFinsetEndpointsIff (G := G)]
  simp only [Set.mem_compl_iff]
  tauto

/-- Helper for Theorem 4.23: the preimage of incidence at a retained vertex is its original
incidence filter. -/
private lemma shorePreimageEdgeFinset_incidence_some (S : Finset V) (v : S) :
    shorePreimageEdgeFinset G S
        (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
          (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset (some v)) =
      Finset.univ.filter fun e : G.edgeSet ↦
        (e : Sym2 V) ∈ G.incidenceFinset v.1 := by
  -- Rewrite incidence as a singleton cut and pull that cut back through the contraction.
  calc
    shorePreimageEdgeFinset G S
        (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
          (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset (some v)) =
        shorePreimageEdgeFinset G S
          (δ[shoreContraction G S] ({some v} : Set (Option S))) := by
            exact congrArg
              (fun A : Finset (shoreContraction G S).edgeSet ↦
                shorePreimageEdgeFinset G S A)
              (cutSingleton_eq_incidenceFilter
                (V := Option S) (G := shoreContraction G S) (some v)).symm
    _ = δ[G] (shoreProjection S ⁻¹' ({some v} : Set (Option S))) :=
      shorePreimageEdgeFinset_cut (G := G) S _
    _ = δ[G] ({v.1} : Set V) := by rw [shoreProjection_preimage_singleton_some]
    _ = Finset.univ.filter fun e : G.edgeSet ↦
        (e : Sym2 V) ∈ G.incidenceFinset v.1 :=
      cutSingleton_eq_incidenceFilter (G := G) v.1

/-- Helper for Theorem 4.23: the preimage of incidence at the collapsed vertex is the original
shore cut. -/
private lemma shorePreimageEdgeFinset_incidence_none (S : Finset V) :
    shorePreimageEdgeFinset G S
        (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
          (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) =
      δ[G] (S : Set V) := by
  -- The collapsed singleton pulls back to the complementary shore, whose cut is the same cut.
  calc
    shorePreimageEdgeFinset G S
        (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
          (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) =
        shorePreimageEdgeFinset G S
          (δ[shoreContraction G S] ({none} : Set (Option S))) := by
            exact congrArg
              (fun A : Finset (shoreContraction G S).edgeSet ↦
                shorePreimageEdgeFinset G S A)
              (cutSingleton_eq_incidenceFilter
                (V := Option S) (G := shoreContraction G S) none).symm
    _ = δ[G] (shoreProjection S ⁻¹' ({none} : Set (Option S))) :=
      shorePreimageEdgeFinset_cut (G := G) S _
    _ = δ[G] (S : Set V)ᶜ := by rw [shoreProjection_preimage_singleton_none]
    _ = δ[G] (S : Set V) := cutEdgeFinset_compl (G := G) (S : Set V)

/-- Helper for Theorem 4.23: a shore pushforward preserves the incidence sum at every retained
vertex. -/
private lemma shorePushforward_incidenceSum_some (S : Finset V) (x : G.edgeSet → ℝ)
    (v : S) :
    (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
        (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset (some v)).sum
          (shorePushforward G S x) =
      (Finset.univ.filter fun e : G.edgeSet ↦
        (e : Sym2 V) ∈ G.incidenceFinset v.1).sum x := by
  -- Normalize the pushed-forward sum once, then identify its incidence preimage.
  rw [shorePushforward_sum_preimage,
    shorePreimageEdgeFinset_incidence_some]

/-- Helper for Theorem 4.23: the incidence sum at the collapsed vertex is the weight of the
original shore cut. -/
private lemma shorePushforward_incidenceSum_none (S : Finset V) (x : G.edgeSet → ℝ) :
    (Finset.univ.filter fun f : (shoreContraction G S).edgeSet ↦
        (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none).sum
          (shorePushforward G S x) =
      (δ[G] (S : Set V)).sum x := by
  -- Normalize the pushed-forward sum once, then identify the collapsed incidence preimage.
  rw [shorePushforward_sum_preimage,
    shorePreimageEdgeFinset_incidence_none]

/-- Helper for Theorem 4.23: a contracted perfect matching uses exactly one edge incident to the
collapsed vertex, so it determines a unique retained boundary vertex. -/
private lemma existsUniqueBoundaryVertex_of_isPerfectMatching_shoreContraction
    {S : Finset V} {M : (shoreContraction G S).Subgraph} (hM : M.IsPerfectMatching) :
    ∃! v : S, M.Adj none (some v) := by
  -- Evaluate the perfect-matching adjacency uniqueness at the collapsed vertex `none`.
  obtain ⟨q, hq, huniqq⟩ := (Subgraph.isPerfectMatching_iff.mp hM) none
  cases q with
  | none =>
      -- Simple graphs are loopless, so the unique neighbor of `none` cannot be `none` itself.
      exact ((shoreContraction G S).ne_of_adj hq rfl).elim
  | some v =>
      refine ⟨v, hq, ?_⟩
      intro w hw
      exact Option.some.inj (huniqq (some w) hw)

/-- Helper for Theorem 4.23: any contracted edge incident to `none` lifts back to a genuine cut
edge of the retained shore in the original graph. -/
private lemma shoreOriginalEdge_memCut_of_incidence_none
    {S : Finset V} {f : (shoreContraction G S).edgeSet}
    (hf : (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) :
    shoreOriginalEdge G S f ∈ δ[G] (S : Set V) := by
  -- Put the chosen original preimage into the incidence preimage finset and rewrite that preimage
  -- as the original cut.
  have hmem :
      shoreOriginalEdge G S f ∈
        shorePreimageEdgeFinset G S
          (Finset.univ.filter fun g : (shoreContraction G S).edgeSet ↦
            (g : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩,
      shoreOriginalEdge_map (G := G) S f⟩
  simpa [shorePreimageEdgeFinset_incidence_none (G := G) S] using hmem

/-- Helper for Theorem 4.23: a cut edge of `G` projects to a genuine edge of the shore
contraction. -/
private lemma projectedCutEdge_mem_edgeSet
    {S : Finset V} {e : G.edgeSet} (he : e ∈ δ[G] (S : Set V)) :
    Sym2.map (shoreProjection S) e.1 ∈ (shoreContraction G S).edgeSet := by
  rcases (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he with
    (⟨huS, hvS⟩ | ⟨hvS, huS⟩)
  · have hAdj : G.Adj e.1.out.1 e.1.out.2 := by
      rw [← G.mem_edgeSet]
      simpa [e.1.out_eq] using e.2
    have hMapAdj :
        (shoreContraction G S).Adj (some ⟨e.1.out.1, huS⟩) none := by
      exact (SimpleGraph.map_adj' (shoreProjection S) G _ _).2
        ⟨by simp, e.1.out.1, e.1.out.2, hAdj,
          shoreProjection_apply_of_mem (G := G) S huS,
          shoreProjection_apply_of_notMem (G := G) S hvS⟩
    -- Normalize the projected cut edge to the `some-none` boundary form.
    have hrepr :
        Sym2.map (shoreProjection S) e.1 = s (some ⟨e.1.out.1, huS⟩) none := by
      calc
        Sym2.map (shoreProjection S) e.1 =
            Sym2.map (shoreProjection S) (s (e.1.out.1, e.1.out.2)) := by
              rw [e.1.out_eq]
        _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
              simp
        _ = s (some ⟨e.1.out.1, huS⟩) none := by
              rw [shoreProjection_apply_of_mem (G := G) S huS,
                shoreProjection_apply_of_notMem (G := G) S hvS]
    rw [hrepr]
    exact (shoreContraction G S).mem_edgeSet.2 hMapAdj
  · have hAdj : G.Adj e.1.out.1 e.1.out.2 := by
      rw [← G.mem_edgeSet]
      simpa [e.1.out_eq] using e.2
    have hMapAdj :
        (shoreContraction G S).Adj none (some ⟨e.1.out.1, hvS⟩) := by
      exact (SimpleGraph.map_adj' (shoreProjection S) G _ _).2
        ⟨by simp, e.1.out.2, e.1.out.1, hAdj.symm,
          shoreProjection_apply_of_mem (G := G) S huS,
          shoreProjection_apply_of_notMem (G := G) S hvS⟩
    -- The swapped cut orientation still gives the same boundary edge in the contraction.
    have hrepr :
        Sym2.map (shoreProjection S) e.1 = s none (some ⟨e.1.out.1, hvS⟩) := by
      calc
        Sym2.map (shoreProjection S) e.1 =
            Sym2.map (shoreProjection S) (s (e.1.out.2, e.1.out.1)) := by
              rw [Sym2.eq_swap, e.1.out_eq]
        _ = s (shoreProjection S e.1.out.2) (shoreProjection S e.1.out.1) := by
              simp
        _ = s none (some ⟨e.1.out.1, hvS⟩) := by
              rw [shoreProjection_apply_of_notMem (G := G) S huS,
                shoreProjection_apply_of_mem (G := G) S hvS]
    rw [hrepr]
    exact (shoreContraction G S).mem_edgeSet.2 hMapAdj

/-- Helper for Theorem 4.23: package the projection of a cut edge as a boundary edge in the
shore contraction. -/
private def projectedCutEdge
    (S : Finset V) (e : G.edgeSet) (he : e ∈ δ[G] (S : Set V)) :
    (shoreContraction G S).edgeSet :=
  ⟨Sym2.map (shoreProjection S) e.1, projectedCutEdge_mem_edgeSet (G := G) he⟩

/-- Helper for Theorem 4.23: the canonical projected cut edge has the expected underlying
unordered pair. -/
@[simp] private lemma projectedCutEdge_val
    {S : Finset V} {e : G.edgeSet} (he : e ∈ δ[G] (S : Set V)) :
    (projectedCutEdge (G := G) S e he).1 = Sym2.map (shoreProjection S) e.1 := rfl

/-- Helper for Theorem 4.23: the projection of a cut edge is incident to the collapsed vertex
`none`. -/
private lemma projectedCutEdge_mem_incidence_none_of_mem_cutEdgeFinset
    {S : Finset V} {e : G.edgeSet}
    (he : e ∈ δ[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none := by
  rcases (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he with
    (⟨hleft, hright⟩ | ⟨hright, hleft⟩)
  · have hrepr :
        f.1 =
          s (some ⟨e.1.out.1, hleft⟩) none := by
      -- Normalize the projected cut edge to its `some-none` endpoint presentation.
      calc
        f.1 = Sym2.map (shoreProjection S) e.1 := hf.symm
        _ = Sym2.map (shoreProjection S) (s(e.1.out.1, e.1.out.2)) := by
              rw [e.1.out_eq]
        _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
              simp
        _ = s (some ⟨e.1.out.1, hleft⟩) none := by
              rw [shoreProjection_apply_of_mem (G := G) S hleft,
                shoreProjection_apply_of_notMem (G := G) S hright]
    -- Incidence at `none` is now immediate from the explicit `some-none` form.
    have hnone : none ∈ (f : Sym2 (Option S)) := by
      rw [hrepr]
      simp
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hnone
  · have hrepr :
        f.1 =
          s none (some ⟨e.1.out.1, hleft⟩) := by
      -- Normalize the swapped cut orientation in the same way.
      calc
        f.1 = Sym2.map (shoreProjection S) e.1 := hf.symm
        _ = Sym2.map (shoreProjection S) (s(e.1.out.2, e.1.out.1)) := by
              rw [Sym2.eq_swap, e.1.out_eq]
        _ = s (shoreProjection S e.1.out.2) (shoreProjection S e.1.out.1) := by
              simp
        _ = s none (some ⟨e.1.out.1, hleft⟩) := by
              rw [shoreProjection_apply_of_notMem (G := G) S hright,
                shoreProjection_apply_of_mem (G := G) S hleft]
    -- The swapped normal form still contains `none` as an endpoint.
    have hnone : none ∈ (f : Sym2 (Option S)) := by
      rw [hrepr]
      simp
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hnone

/-- Helper for Theorem 4.23: any original edge that projects to a contracted boundary edge lies
in the corresponding original shore cut. -/
private lemma memCutEdgeFinset_of_eq_projectedEdge_of_memIncidenceNone
    {S : Finset V} {e : G.edgeSet} {f : (shoreContraction G S).edgeSet}
    (hfnone : (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none)
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    e ∈ δ[G] (S : Set V) := by
  have hmem :
      e ∈ shorePreimageEdgeFinset G S
        (Finset.univ.filter fun g : (shoreContraction G S).edgeSet ↦
          (g : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfnone⟩, hf⟩
  simpa [shorePreimageEdgeFinset_incidence_none (G := G) S] using hmem

/-- Helper for Theorem 4.23: on a contracted boundary edge, the shore pushforward is exactly the
sum of the original cut-edge weights in that projection fiber. -/
private lemma shorePushforward_apply_of_memIncidenceNone
    {S : Finset V} {x : G.edgeSet → ℝ} {f : (shoreContraction G S).edgeSet}
    (hfnone : (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) :
    shorePushforward G S x f =
      ∑ e : G.edgeSet,
        if he : e ∈ δ[G] (S : Set V) then
          if projectedCutEdge (G := G) S e he = f then x e else 0
        else 0 := by
  -- A projected edge can equal a boundary edge only when the original edge crosses the shore cut.
  unfold shorePushforward
  refine Finset.sum_congr rfl ?_
  intro e he
  by_cases hproj : Sym2.map (shoreProjection S) e.1 = f.1
  · have heCut :
        e ∈ δ[G] (S : Set V) :=
      memCutEdgeFinset_of_eq_projectedEdge_of_memIncidenceNone (G := G) hfnone hproj
    have hEq : projectedCutEdge (G := G) S e heCut = f := by
      apply Subtype.ext
      simpa [projectedCutEdge]
        using hproj
    simp [hproj, heCut, hEq]
  · by_cases heCut : e ∈ δ[G] (S : Set V)
    · have hEq :
          projectedCutEdge (G := G) S e heCut ≠ f := by
        intro hEq
        apply hproj
        simpa [projectedCutEdge] using congrArg Subtype.val hEq
      simp [hproj, heCut, hEq]
    · simp [hproj, heCut]

/-- Helper for Theorem 4.23: a projected edge coordinate is positive whenever one of its original
preimage edges has positive weight. -/
private lemma shorePushforward_pos_of_eq_projectedEdge
    {S : Finset V} {x : G.edgeSet → ℝ} (hx_pos : ∀ e : G.edgeSet, 0 < x e)
    {e : G.edgeSet} {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    0 < shorePushforward G S x f := by
  -- Keep the positive summand indexed by `e` and bound the remaining summands below by `0`.
  unfold shorePushforward
  have hterm : 0 < (if Sym2.map (shoreProjection S) e.1 = f.1 then x e else 0) := by
    simp [hf, hx_pos e]
  have hle :
      (if Sym2.map (shoreProjection S) e.1 = f.1 then x e else 0) ≤
        ∑ e' : G.edgeSet, if Sym2.map (shoreProjection S) e'.1 = f.1 then x e' else 0 := by
    refine Finset.single_le_sum ?_ ?_
    · intro e' _
      by_cases hmap : Sym2.map (shoreProjection S) e'.1 = f.1
      · exact (hx_pos e').le
      · simp [hmap]
    · simp
  exact lt_of_lt_of_le hterm hle

/-- Helper for Theorem 4.23: an internal edge of `S` is the unique original preimage of its
projected contracted edge, so the shore pushforward keeps that coordinate unchanged. -/
private lemma shorePushforward_apply_of_mem_inducedEdgeFinset
    {S : Finset V} {x : G.edgeSet → ℝ} {e : G.edgeSet}
    (he : e ∈ E[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    shorePushforward G S x f = x e := by
  let u : S := ⟨e.1.out.1, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.1⟩
  let v : S := ⟨e.1.out.2, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.2⟩
  -- Expand the pushforward sum and show every surviving summand comes from the same original edge.
  unfold shorePushforward
  refine Finset.sum_eq_single e ?_ ?_
  · -- The target edge contributes exactly `x e`.
    simp [hf]
  · intro e' _ he'
    by_cases hmap : Sym2.map (shoreProjection S) e'.1 = f.1
    · have hpair :
          s (shoreProjection S e'.1.out.1) (shoreProjection S e'.1.out.2) =
            s (some u) (some v) := by
        -- Compare the two projected endpoint pairs through the common contracted edge `f`.
        calc
          s (shoreProjection S e'.1.out.1) (shoreProjection S e'.1.out.2) =
              Sym2.map (shoreProjection S) e'.1 := by
                exact (Sym2.map_mk _ _ _).symm.trans
                  (congrArg (Sym2.map (shoreProjection S)) e'.1.out_eq)
          _ = f.1 := hmap
          _ = Sym2.map (shoreProjection S) e.1 := hf.symm
          _ = s (some u) (some v) := by
                calc
                  Sym2.map (shoreProjection S) e.1 =
                      Sym2.map (shoreProjection S) (s(e.1.out.1, e.1.out.2)) := by
                        rw [e.1.out_eq]
                  _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
                        simp
                  _ = s (some u) (some v) := by
                        simp [u, v]
      rw [Sym2.eq_iff] at hpair
      have hEqVal : e'.1 = e.1 := by
        rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · -- In the direct orientation both projected endpoints match componentwise.
          calc
            e'.1 = s (e'.1.out.1, e'.1.out.2) := e'.1.out_eq.symm
            _ = s (u.1, v.1) := by
                  rw [(shoreProjection_eq_some_iff (G := G) S).1 h₁,
                    (shoreProjection_eq_some_iff (G := G) S).1 h₂]
            _ = e.1 := by
                  simpa [u, v] using e.1.out_eq
        · -- In the swapped orientation the same argument recovers the flipped endpoint pair.
          calc
            e'.1 = s (e'.1.out.1, e'.1.out.2) := e'.1.out_eq.symm
            _ = s (v.1, u.1) := by
                  rw [(shoreProjection_eq_some_iff (G := G) S).1 h₁,
                    (shoreProjection_eq_some_iff (G := G) S).1 h₂]
            _ = e.1 := by
                  simpa [u, v] using Sym2.eq_swap.trans e.1.out_eq
      exact (he' (Subtype.ext hEqVal)).elim
    · simp [hmap]
  · simp

/-- Helper for Theorem 4.23: pushing forward a nonnegative edge vector preserves
nonnegativity. -/
private lemma shorePushforward_nonneg (S : Finset V) {x : G.edgeSet → ℝ}
    (hx : ∀ e, 0 ≤ x e) :
    ∀ f, 0 ≤ shorePushforward G S x f := by
  intro f
  -- Every contracted coordinate is a finite sum of nonnegative original coordinates.
  exact Finset.sum_nonneg fun e _ ↦ by
    by_cases hmap : Sym2.map (shoreProjection S) e.1 = f.1
    · simp [shorePushforward, hmap, hx e]
    · simp [shorePushforward, hmap]

/-- Helper for Theorem 4.23: away from the collapsed vertex, the shore projection bijects a
set-preimage with the corresponding set of contracted vertices. -/
private lemma shoreProjection_bijOn_preimage_of_none_notMem (S : Finset V)
    (U : Set (Option S)) (hnone : none ∉ U) :
    Set.BijOn (shoreProjection S) (shoreProjection S ⁻¹' U) U := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact hv
  · intro v hv w hw hvw
    have hvS : v ∈ S := by
      by_contra hvS
      exact hnone (by simpa [shoreProjection, hvS] using hv)
    have hwS : w ∈ S := by
      by_contra hwS
      exact hnone (by simpa [shoreProjection, hwS] using hw)
    exact shoreProjection_injOn S hvS hwS hvw
  · intro a ha
    cases a with
    | none => exact (hnone ha).elim
    | some v =>
        refine ⟨v.1, ?_, ?_⟩
        · simpa [shoreProjection, v.2] using ha
        · simp [shoreProjection, v.2]

/-- Helper for Theorem 4.23: an odd contracted vertex set avoiding the collapsed vertex has an
odd original preimage. -/
private lemma odd_ncard_shoreProjection_preimage_of_none_notMem (S : Finset V)
    {U : Set (Option S)} (hU : Odd U.ncard) (hnone : none ∉ U) :
    Odd (shoreProjection S ⁻¹' U).ncard := by
  have hcard :=
    (shoreProjection_bijOn_preimage_of_none_notMem S U hnone).ncard_eq
  -- The projection bijection identifies the two finite cardinalities.
  rw [hcard]
  exact hU

/-- Helper for Theorem 4.23: cut sums of a shore pushforward are original cut sums on the
vertex-set preimage. -/
private lemma shorePushforward_cutSum (S : Finset V) (x : G.edgeSet → ℝ)
    (U : Set (Option S)) :
    (δ[shoreContraction G S] U).sum (shorePushforward G S x) =
      (δ[G] (shoreProjection S ⁻¹' U)).sum x := by
  -- Apply the common fiber-sum interface and then identify the cut preimage.
  rw [shorePushforward_sum_preimage, shorePreimageEdgeFinset_cut]

/-- Helper for Theorem 4.23: a tight odd shore pushes a perfect-constraint point to a
perfect-constraint point of its contraction. -/
private lemma shorePushforward_memPerfectMatchingConstraintSet
    (S : Finset V) {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) (hS : Odd S.card)
    (hcut : (δ[G] (S : Set V)).sum x = 1) :
    shorePushforward G S x ∈ perfectMatchingConstraintSet (shoreContraction G S) := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_degree, hx_oddCut⟩
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨shorePushforward_nonneg (G := G) S hx_nonneg, ?_, ?_⟩
  · intro v
    cases v with
    | none =>
        -- The collapsed degree equation is exactly tightness of the original shore cut.
        exact (shorePushforward_incidenceSum_none (G := G) S x).trans hcut
    | some v =>
        -- Retained vertices inherit their original degree equations unchanged.
        exact (shorePushforward_incidenceSum_some (G := G) S x v).trans (hx_degree v.1)
  · intro U hU
    by_cases hnone : none ∈ U
    · have htotalEven : Even (Nat.card (Option S)) := by
        simpa using hS.add_one
      have hUcompl : Odd Uᶜ.ncard :=
        (Set.odd_ncard_compl_iff htotalEven U).2 hU
      have hnoneCompl : none ∉ Uᶜ := by simp [hnone]
      have hpreOdd : Odd (shoreProjection S ⁻¹' Uᶜ).ncard :=
        odd_ncard_shoreProjection_preimage_of_none_notMem S hUcompl hnoneCompl
      -- Exchange the two contracted shores, then pull the cut back to the original graph.
      rw [← cutEdgeFinset_compl (G := shoreContraction G S) U,
        shorePushforward_cutSum]
      exact hx_oddCut _ hpreOdd
    · have hpreOdd : Odd (shoreProjection S ⁻¹' U).ncard :=
        odd_ncard_shoreProjection_preimage_of_none_notMem S hU hnone
      -- A cut avoiding the apex pulls back directly to an odd original cut.
      rw [shorePushforward_cutSum]
      exact hx_oddCut _ hpreOdd

/-- Helper for Theorem 4.23: contraction along a proper tight odd shore simultaneously preserves
perfect feasibility and decreases the induction measure. -/
private lemma shorePushforward_memPerfectConstraintAndMeasureLt
    (S : Finset V) {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G) (hS : Odd S.card)
    (hcompl : 1 < (Finset.univ \ S).card)
    (hcut : (δ[G] (S : Set V)).sum x = 1) :
    shorePushforward G S x ∈ perfectMatchingConstraintSet (shoreContraction G S) ∧
      Fintype.card (Option S) + Fintype.card (shoreContraction G S).edgeSet <
        Fintype.card V + Fintype.card G.edgeSet := by
  -- Feasibility follows from the pushforward identities, while properness lowers the measure.
  exact ⟨shorePushforward_memPerfectMatchingConstraintSet (G := G) S hx hS hcut,
    shoreContraction_measure_lt (G := G) S hcompl⟩

/-- Helper for Theorem 4.23: feasibility of the perfect-matching constraints forces the graph to
have an even number of vertices. -/
private lemma even_card_of_memPerfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) :
    Even (Fintype.card V) := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, -, hx_oddCut⟩
  rw [← Nat.not_odd_iff_even]
  intro hOdd
  have hUnivOdd : Odd (Set.univ : Set V).ncard := by
    simpa using hOdd
  have hcut := hx_oddCut Set.univ hUnivOdd
  -- The cut of the whole vertex set is empty, contradicting its required lower bound.
  norm_num [SimpleGraph.cutEdgeFinset] at hcut

/-- Helper for Theorem 4.23: in an even finite vertex set, the complement of an odd shore is
odd. -/
private lemma odd_compl_card_of_even_card (S : Finset V)
    (hV : Even (Fintype.card V)) (hS : Odd S.card) :
    Odd (Finset.univ \ S).card := by
  have hcompl : Odd ((S : Set V)ᶜ.ncard) := by
    have hV' : Even (Nat.card V) := by simpa using hV
    exact (Set.odd_ncard_compl_iff hV' (S : Set V)).2 (by simpa using hS)
  -- Convert the set-complement cardinality back to the finite complement used by induction.
  have hcard : (Finset.univ \ S).card = ((S : Set V)ᶜ).ncard := by
    have hcoe : ((Finset.univ \ S : Finset V) : Set V) = (S : Set V)ᶜ := by
      ext v
      simp
    rw [← hcoe]
    simpa using
      (Set.ncard_eq_toFinset_card' ((Finset.univ \ S : Finset V) : Set V)).symm
  rw [hcard]
  exact hcompl

/-- Helper for Theorem 4.23: two proper tight odd shores are both solved by the smaller-graph
induction hypothesis after pushforward. -/
private lemma shorePushforwards_memPerfectMatchingPolytope
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    (S T : Finset V) {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hS : Odd S.card) (hT : Odd T.card)
    (hcomplS : 1 < (Finset.univ \ S).card)
    (hcomplT : 1 < (Finset.univ \ T).card)
    (hcutS : (δ[G] (S : Set V)).sum x = 1)
    (hcutT : (δ[G] (T : Set V)).sum x = 1) :
    shorePushforward G S x ∈ perfectMatchingPolytope (shoreContraction G S) ∧
      shorePushforward G T x ∈ perfectMatchingPolytope (shoreContraction G T) := by
  have hleft := shorePushforward_memPerfectConstraintAndMeasureLt
    (G := G) S hx hS hcomplS hcutS
  have hright := shorePushforward_memPerfectConstraintAndMeasureLt
    (G := G) T hx hT hcomplT hcutT
  -- Each contraction is strictly smaller, so the induction hypothesis supplies its decomposition.
  exact ⟨hsmaller (shoreContraction G S) hleft.2 hleft.1,
    hsmaller (shoreContraction G T) hright.2 hright.1⟩

/-- Helper for Theorem 4.23: a proper tight odd shore and its complement yield the two smaller
perfect-matching decompositions needed for gluing. -/
private lemma complementaryShorePushforwards_memPerfectMatchingPolytope
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G)
    (hV : Even (Fintype.card V)) (S : Finset V)
    (hS : Odd S.card) (hSproper : 1 < S.card)
    (hcomplProper : 1 < (Finset.univ \ S).card)
    (hcut : (δ[G] (S : Set V)).sum x = 1) :
    shorePushforward G S x ∈ perfectMatchingPolytope (shoreContraction G S) ∧
      shorePushforward G (Finset.univ \ S) x ∈
        perfectMatchingPolytope (shoreContraction G (Finset.univ \ S)) := by
  let T : Finset V := Finset.univ \ S
  have hT : Odd T.card := by
    simpa [T] using odd_compl_card_of_even_card S hV hS
  have hcomplT : 1 < (Finset.univ \ T).card := by
    simpa [T] using hSproper
  have hTset : (T : Set V) = (S : Set V)ᶜ := by
    ext v
    simp [T]
  have hcutT : (δ[G] (T : Set V)).sum x = 1 := by
    rw [hTset, cutEdgeFinset_compl]
    exact hcut
  -- Apply the two-shore induction package to `S` and its literal finite complement.
  simpa [T] using shorePushforwards_memPerfectMatchingPolytope
    (G := G) hsmaller S T hx hS hT hcomplProper hcomplT hcut hcutT

/-- Helper for Theorem 4.23: the unsigned edge-incidence matrix acts by summing the coordinates
of the edges incident to each vertex. -/
private lemma edgeIncMatrix_mulVec_apply (d : G.edgeSet → ℝ) (v : V) :
    ((G.edgeIncMatrix ℝ).mulVec d) v =
      (Finset.univ.filter fun e : G.edgeSet ↦
        (e : Sym2 V) ∈ G.incidenceFinset v).sum d := by
  -- Expand the restricted incidence matrix and turn its `0/1` entries into a filter.
  rw [SimpleGraph.edgeIncMatrix, Matrix.mulVec, dotProduct, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro e _
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · simp [G.incMatrix_of_mem_incidenceSet (R := ℝ) h, h]
  · simp [G.incMatrix_of_notMem_incidenceSet (R := ℝ) h, h]

/-- Helper for Theorem 4.23: a zero unsigned-incidence direction has zero total on every
singleton cut. -/
private lemma cutSum_eq_zero_of_edgeIncMatrix_mulVec_eq_zero
    (d : G.edgeSet → ℝ) (hd : (G.edgeIncMatrix ℝ).mulVec d = 0)
    {U : Set V} (hU : U.ncard = 1) :
    (δ[G] U).sum d = 0 := by
  obtain ⟨v, rfl⟩ := Set.ncard_eq_one.mp hU
  -- A singleton cut is precisely the incidence filter of its unique vertex.
  rw [cutSingleton_eq_incidenceFilter, ← edgeIncMatrix_mulVec_apply]
  exact congrFun hd v

/-- Helper for Theorem 4.23: the cut of the vertex set of a connected component is empty. -/
private lemma cutEdgeFinset_connectedComponentSupp_eq_empty
    (C : G.ConnectedComponent) :
    δ[G] C.supp = ∅ := by
  ext e
  constructor
  · intro he
    rcases (SimpleGraph.mem_cutEdgeFinset_iff (G := G)).1 he with
      ⟨v, hv, w, hw, hevw⟩
    have hvw : G.Adj v w := by
      rw [← G.mem_edgeSet]
      simpa [hevw] using e.2
    -- Adjacency cannot cross between two distinct connected components.
    exact (hw ((C.mem_supp_congr_adj hvw).1 hv)).elim
  · simp

/-- Helper for Theorem 4.23: every connected-component shore has even cardinality whenever the
perfect-matching constraint system is feasible. -/
private lemma connectedComponentSupp_even_of_memPerfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G)
    (C : G.ConnectedComponent) :
    Even C.supp.ncard := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, -, hxCut⟩
  rw [← Nat.not_odd_iff_even]
  intro hOdd
  have hLower := hxCut C.supp hOdd
  -- The odd-cut inequality contradicts the empty component cut.
  rw [cutEdgeFinset_connectedComponentSupp_eq_empty (G := G) C] at hLower
  norm_num at hLower

/-- Helper for Theorem 4.23: the original-graph shore underlying a connected component of the
graph obtained by deleting `U`. -/
private def deleteVertsComponentShore (U : Set V)
    (C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent) : Set V :=
  Subtype.val '' (C : Set ((⊤ : G.Subgraph).deleteVerts U).verts)

/-- Helper for Theorem 4.23: every vertex coming from a deleted-graph component lies outside the
deleted vertex set. -/
private lemma mem_deleteVertsComponentShore_notMem
    {U : Set V} {C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent} {v : V}
    (hv : v ∈ deleteVertsComponentShore (G := G) U C) :
    v ∉ U := by
  -- Unpack the component-image witness and read off the `deleteVerts` vertex condition.
  rcases hv with ⟨v', hv', rfl⟩
  simpa [deleteVertsComponentShore, Subgraph.deleteVerts_verts] using v'.2

/-- Helper for Theorem 4.23: an edge in the cut of a deleted connected component meets `U` on the
opposite endpoint. -/
private lemma memCut_deleteVertsComponentShore
    {U : Set V} (C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent)
    {e : G.edgeSet} (he : e ∈ δ[G] (deleteVertsComponentShore (G := G) U C)) :
    (e.1.out.1 ∈ deleteVertsComponentShore (G := G) U C ∧ e.1.out.2 ∈ U) ∨
      (e.1.out.2 ∈ deleteVertsComponentShore (G := G) U C ∧ e.1.out.1 ∈ U) := by
  rcases (memCutEdgeFinsetEndpointsIff (G := G)
      (deleteVertsComponentShore (G := G) U C) e).1 he with
    (⟨h₁C, h₂C⟩ | ⟨h₂C, h₁C⟩)
  · by_cases h₂U : e.1.out.2 ∈ U
    · exact Or.inl ⟨h₁C, h₂U⟩
    · exfalso
      have h₂verts : e.1.out.2 ∈ ((⊤ : G.Subgraph).deleteVerts U).verts := by
        simpa [Subgraph.deleteVerts_verts] using h₂U
      rcases h₁C with ⟨v, hv, hvEq⟩
      have hAdjG : G.Adj v.1 e.1.out.2 := by
        rw [← G.mem_edgeSet]
        simpa [hvEq, e.1.out_eq] using e.2
      have hAdjDelete :
          ((⊤ : G.Subgraph).deleteVerts U).Adj v.1 e.1.out.2 := by
        rw [Subgraph.deleteVerts_adj]
        exact ⟨by simp, by simpa [Subgraph.deleteVerts_verts] using v.2, by simp, h₂U, hAdjG⟩
      have h₂shore :
          e.1.out.2 ∈ deleteVertsComponentShore (G := G) U C :=
        ConnectedComponent.mem_coe_supp_of_adj (G := G)
          (H := (⊤ : G.Subgraph).deleteVerts U) (c := C) h₁C h₂verts hAdjDelete
      exact h₂C h₂shore
  · by_cases h₁U : e.1.out.1 ∈ U
    · exact Or.inr ⟨h₂C, h₁U⟩
    · exfalso
      have h₁verts : e.1.out.1 ∈ ((⊤ : G.Subgraph).deleteVerts U).verts := by
        simpa [Subgraph.deleteVerts_verts] using h₁U
      rcases h₂C with ⟨v, hv, hvEq⟩
      have hAdjG : G.Adj e.1.out.1 v.1 := by
        rw [← G.mem_edgeSet]
        simpa [hvEq, e.1.out_eq, Sym2.eq_swap] using e.2
      have hAdjDelete :
          ((⊤ : G.Subgraph).deleteVerts U).Adj e.1.out.1 v.1 := by
        rw [Subgraph.deleteVerts_adj]
        exact ⟨by simp, h₁U, by simp, by simpa [Subgraph.deleteVerts_verts] using v.2, hAdjG⟩
      have h₁shore :
          e.1.out.1 ∈ deleteVertsComponentShore (G := G) U C :=
        ConnectedComponent.mem_coe_supp_of_adj (G := G)
          (H := (⊤ : G.Subgraph).deleteVerts U) (c := C) h₂C h₁verts hAdjDelete.symm
      exact h₁C h₁shore

/-- Helper for Theorem 4.23: every deleted-component cut is part of the cut of the deleted
vertex set itself. -/
private lemma deleteVertsComponentCut_subset_cut
    {U : Set V} (C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent) :
    δ[G] (deleteVertsComponentShore (G := G) U C) ⊆ δ[G] U := by
  intro e he
  rcases memCut_deleteVertsComponentShore (G := G) C he with
    (⟨h₁C, h₂U⟩ | ⟨h₂C, h₁U⟩)
  · exact (memCutEdgeFinsetEndpointsIff (G := G) U e).2 <|
      Or.inr ⟨h₂U, mem_deleteVertsComponentShore_notMem (G := G) h₁C⟩
  · exact (memCutEdgeFinsetEndpointsIff (G := G) U e).2 <|
      Or.inl ⟨h₁U, mem_deleteVertsComponentShore_notMem (G := G) h₂C⟩

/-- Helper for Theorem 4.23: the deleted-component cuts are pairwise disjoint because each cut
edge remembers the unique surviving endpoint outside `U`. -/
private lemma deleteVertsComponentCuts_disjoint
    {U : Set V} {C D : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent}
    (hCD : C ≠ D) :
    Disjoint (δ[G] (deleteVertsComponentShore (G := G) U C))
      (δ[G] (deleteVertsComponentShore (G := G) U D)) := by
  -- Compare the unique endpoint outside `U` provided by both component cuts.
  refine Finset.disjoint_left.2 ?_
  intro e heC heD
  rcases memCut_deleteVertsComponentShore (G := G) C heC with
    (⟨h₁C, h₂U⟩ | ⟨h₂C, h₁U⟩)
  · have h₁D : e.1.out.1 ∈ deleteVertsComponentShore (G := G) U D := by
      rcases memCut_deleteVertsComponentShore (G := G) D heD with
        (⟨h₁D, -⟩ | ⟨h₂D, h₁U'⟩)
      · exact h₁D
      · exact (mem_deleteVertsComponentShore_notMem (G := G) h₂D h₂U).elim
    rcases h₁C with ⟨vC, hvC, hvCEq⟩
    rcases h₁D with ⟨vD, hvD, hvDEq⟩
    have hvEq : vC = vD := by
      apply Subtype.ext
      simpa [hvCEq, hvDEq]
    exact hCD (ConnectedComponent.eq_of_common_vertex hvC (hvEq ▸ hvD))
  · have h₂D : e.1.out.2 ∈ deleteVertsComponentShore (G := G) U D := by
      rcases memCut_deleteVertsComponentShore (G := G) D heD with
        (⟨h₁D, h₂U'⟩ | ⟨h₂D, -⟩)
      · exact (mem_deleteVertsComponentShore_notMem (G := G) h₁D h₁U).elim
      · exact h₂D
    rcases h₂C with ⟨vC, hvC, hvCEq⟩
    rcases h₂D with ⟨vD, hvD, hvDEq⟩
    have hvEq : vC = vD := by
      apply Subtype.ext
      simpa [hvCEq, hvDEq]
    exact hCD (ConnectedComponent.eq_of_common_vertex hvC (hvEq ▸ hvD))

/-- Helper for Theorem 4.23: the deleted-set cut is the disjoint union of the cuts of all
connected components of the deleted graph. -/
private lemma deleteVertsComponentCuts_biUnion_eq_cut
    (U : Set V) :
    (Finset.univ :
        Finset (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent).biUnion
        (fun C ↦ δ[G] (deleteVertsComponentShore (G := G) U C)) =
      δ[G] U := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_biUnion.mp he with ⟨C, -, heC⟩
    exact deleteVertsComponentCut_subset_cut (G := G) C heC
  · intro he
    rcases (memCutEdgeFinsetEndpointsIff (G := G) U e).1 he with
      (⟨h₁U, h₂U⟩ | ⟨h₂U, h₁U⟩)
    · have h₂verts : e.1.out.2 ∈ ((⊤ : G.Subgraph).deleteVerts U).verts := by
        simpa [Subgraph.deleteVerts_verts] using h₂U
      let C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent :=
        ((⊤ : G.Subgraph).deleteVerts U).coe.connectedComponentMk ⟨e.1.out.2, h₂verts⟩
      have h₂shore : e.1.out.2 ∈ deleteVertsComponentShore (G := G) U C := by
        refine ⟨⟨e.1.out.2, h₂verts⟩, ?_, rfl⟩
        exact ConnectedComponent.connectedComponentMk_mem
      have h₁not_shore : e.1.out.1 ∉ deleteVertsComponentShore (G := G) U C := by
        intro h₁shore
        exact mem_deleteVertsComponentShore_notMem (G := G) h₁shore h₁U
      have heC : e ∈ δ[G] (deleteVertsComponentShore (G := G) U C) := by
        exact (memCutEdgeFinsetEndpointsIff (G := G)
          (deleteVertsComponentShore (G := G) U C) e).2 (Or.inr ⟨h₂shore, h₁not_shore⟩)
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, heC⟩
    · have h₁verts : e.1.out.1 ∈ ((⊤ : G.Subgraph).deleteVerts U).verts := by
        simpa [Subgraph.deleteVerts_verts] using h₁U
      let C : (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent :=
        ((⊤ : G.Subgraph).deleteVerts U).coe.connectedComponentMk ⟨e.1.out.1, h₁verts⟩
      have h₁shore : e.1.out.1 ∈ deleteVertsComponentShore (G := G) U C := by
        refine ⟨⟨e.1.out.1, h₁verts⟩, ?_, rfl⟩
        exact ConnectedComponent.connectedComponentMk_mem
      have h₂not_shore : e.1.out.2 ∉ deleteVertsComponentShore (G := G) U C := by
        intro h₂shore
        exact mem_deleteVertsComponentShore_notMem (G := G) h₂shore h₂U
      have heC : e ∈ δ[G] (deleteVertsComponentShore (G := G) U C) := by
        exact (memCutEdgeFinsetEndpointsIff (G := G)
          (deleteVertsComponentShore (G := G) U C) e).2 (Or.inl ⟨h₁shore, h₂not_shore⟩)
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_univ _, heC⟩

/-- Helper for Theorem 4.23: the total cut mass of the odd deleted components is bounded by the
number of deleted vertices. -/
private lemma oddComponentsCutMass_le_deletedCard
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) (U : Set V) :
    (((((⊤ : G.Subgraph).deleteVerts U).coe).oddComponents.ncard : ℝ)) ≤ U.ncard := by
  classical
  let K : G.Subgraph := (⊤ : G.Subgraph).deleteVerts U
  let oddCuts :
      Finset (((⊤ : G.Subgraph).deleteVerts U).coe).ConnectedComponent :=
    Finset.univ.filter fun C : K.coe.ConnectedComponent ↦ Odd C.supp.ncard
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_cut⟩
  have hoddCount_le :
      ((((K.coe).oddComponents.ncard : ℝ))) ≤
        ∑ C in oddCuts, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x := by
    calc
      ((((K.coe).oddComponents.ncard : ℝ))) = ∑ C in oddCuts, (1 : ℝ) := by
        simp [K, oddCuts, SimpleGraph.oddComponents]
      _ ≤ ∑ C in oddCuts, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x := by
        refine Finset.sum_le_sum ?_
        intro C hC
        have hcard :
            (deleteVertsComponentShore (G := G) U C).ncard = C.supp.ncard := by
          simpa [deleteVertsComponentShore] using
            (Set.ncard_image_of_injective (f := (↑) : K.verts → V) Subtype.val_injective
              (s := (C : Set K.verts)))
        have hOddC : Odd (deleteVertsComponentShore (G := G) U C).ncard := by
          rw [hcard]
          exact C.property
        exact hx_cut _ hOddC
  have hoddCuts_le_all :
      (∑ C in oddCuts, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x) ≤
        ∑ C : K.coe.ConnectedComponent, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x := by
    calc
      (∑ C in oddCuts, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x) =
          ∑ C : K.coe.ConnectedComponent,
            if Odd C.supp.ncard then (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x else 0 := by
              simp [K, oddCuts, SimpleGraph.oddComponents]
      _ ≤ ∑ C : K.coe.ConnectedComponent,
            (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x := by
              refine Finset.sum_le_sum ?_
              intro C hC
              by_cases hOddC : Odd C.supp.ncard
              · simp [hOddC]
              · have hnonneg :
                    0 ≤ (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x :=
                  Finset.sum_nonneg fun e _ ↦ hx_nonneg e
                simp [hOddC, hnonneg]
  have hallCuts_eq :
      (∑ C : K.coe.ConnectedComponent, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x) =
        (δ[G] U).sum x := by
    have hpairwise :
        Set.PairwiseDisjoint
          (↑(Finset.univ : Finset K.coe.ConnectedComponent))
          (fun C ↦ δ[G] (deleteVertsComponentShore (G := G) U C)) := by
      intro C _ D _ hCD
      exact deleteVertsComponentCuts_disjoint (G := G) (U := U) hCD
    calc
      (∑ C : K.coe.ConnectedComponent, (δ[G] (deleteVertsComponentShore (G := G) U C)).sum x) =
          (((Finset.univ : Finset K.coe.ConnectedComponent).biUnion
              (fun C ↦ δ[G] (deleteVertsComponentShore (G := G) U C))).sum x) := by
              symm
              simpa using
                (Finset.sum_biUnion (s := (Finset.univ : Finset K.coe.ConnectedComponent))
                  (t := fun C ↦ δ[G] (deleteVertsComponentShore (G := G) U C))
                  (f := x) hpairwise)
      _ = (δ[G] U).sum x := by
            rw [deleteVertsComponentCuts_biUnion_eq_cut (G := G) U]
  have hcut_le :
      (δ[G] U).sum x ≤ U.ncard := by
    have hdegreeSum :
        Finset.sum U.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          (U.ncard : ℝ) :=
      incidenceSum_eq_card_of_eq_one (G := G) hx_deg U
    have hsplit :
        Finset.sum U.toFinite.toFinset
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
          2 * (E[G] U).sum x + (δ[G] U).sum x := by
      simpa using sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) U x
    have hinduced_nonneg : 0 ≤ (E[G] U).sum x :=
      Finset.sum_nonneg fun e _ ↦ hx_nonneg e
    linarith
  exact le_trans hoddCount_le (le_trans hoddCuts_le_all (by simpa [hallCuts_eq] using hcut_le))

/-- Helper for Theorem 4.23: every feasible perfect-matching constraint point rules out Tutte
violators. -/
private lemma not_isTutteViolator_of_memPerfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) :
    ∀ U : Set V, ¬ G.IsTutteViolator U := by
  intro U hU
  rw [SimpleGraph.IsTutteViolator] at hU
  have hbound :
      ((((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard : ℝ)) ≤ U.ncard :=
    oddComponentsCutMass_le_deletedCard (G := G) hx U
  exact not_lt_of_ge hbound (by exact_mod_cast hU)

/-- Helper for Theorem 4.23: if all proper odd shores have positive slack, extremality forces the
unsigned degree map to be injective. -/
private lemma degreeMapInjectiveOfNoProperTightOddShore
    {x : G.edgeSet → ℝ}
    (hx : x ∈ perfectMatchingConstraintSet G)
    (hxExtreme : x ∈ (matchingConstraintSet G).extremePoints ℝ)
    (hxPos : ∀ e : G.edgeSet, 0 < x e)
    (hV : Even (Fintype.card V))
    (hNoTight : ∀ S : Finset V, Odd S.card → 1 < S.card →
      1 < (Finset.univ \ S).card → (δ[G] (S : Set V)).sum x ≠ 1) :
    Function.Injective (G.edgeIncMatrix ℝ).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro d hd
  have hdMul : (G.edgeIncMatrix ℝ).mulVec d = 0 := by
    simpa [Matrix.mulVecLin_apply] using hd
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨-, hxDegree, hxCut⟩
  let strictFeasible : Set (G.edgeSet → ℝ) :=
    (⋂ e : G.edgeSet, {y | 0 < y e}) ∩
      ⋂ S : Finset V,
        if Odd S.card ∧ 1 < S.card ∧ 1 < (Finset.univ \ S).card then
          {y | 1 < (δ[G] (S : Set V)).sum y}
        else Set.univ
  have hOpenCoordinates :
      IsOpen (⋂ e : G.edgeSet, {y : G.edgeSet → ℝ | 0 < y e}) := by
    exact isOpen_iInter_of_finite fun e ↦
      isOpen_lt continuous_const (continuous_apply e)
  have hOpenCuts :
      IsOpen (⋂ S : Finset V,
        if Odd S.card ∧ 1 < S.card ∧ 1 < (Finset.univ \ S).card then
          {y : G.edgeSet → ℝ | 1 < (δ[G] (S : Set V)).sum y}
        else Set.univ) := by
    refine isOpen_iInter_of_finite fun S ↦ ?_
    by_cases hProper : Odd S.card ∧ 1 < S.card ∧ 1 < (Finset.univ \ S).card
    · rw [if_pos hProper]
      exact isOpen_lt continuous_const <|
        continuous_finsetSum (δ[G] (S : Set V)) fun e _ ↦ continuous_apply e
    · rw [if_neg hProper]
      exact isOpen_univ
  have hOpen : IsOpen strictFeasible := by
    exact hOpenCoordinates.inter hOpenCuts
  have hxStrict : x ∈ strictFeasible := by
    refine ⟨?_, ?_⟩
    · rw [Set.mem_iInter]
      exact hxPos
    · rw [Set.mem_iInter]
      intro S
      by_cases hProper : Odd S.card ∧ 1 < S.card ∧ 1 < (Finset.univ \ S).card
      · rw [if_pos hProper]
        have hLower : 1 ≤ (δ[G] (S : Set V)).sum x := by
          exact hxCut (S : Set V) (by simpa using hProper.1)
        exact lt_of_le_of_ne hLower (hNoTight S hProper.1 hProper.2.1 hProper.2.2).symm
      · rw [if_neg hProper]
        exact Set.mem_univ x
  have hCurve : Continuous (fun t : ℝ ↦ x + t • d) := by
    fun_prop
  have hZeroPreimage :
      (0 : ℝ) ∈ (fun t : ℝ ↦ x + t • d) ⁻¹' strictFeasible := by
    simpa using hxStrict
  have hPreimageNhds :
      (fun t : ℝ ↦ x + t • d) ⁻¹' strictFeasible ∈ nhds (0 : ℝ) :=
    (hOpen.preimage hCurve).mem_nhds hZeroPreimage
  obtain ⟨r, hrPos, hrBall⟩ := Metric.mem_nhds_iff.mp hPreimageNhds
  let ε : ℝ := r / 2
  have hεPos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεBall : ε ∈ Metric.ball (0 : ℝ) r := by
    rw [Real.mem_ball_zero_iff]
    simpa [ε, abs_of_pos hεPos] using (half_lt_self hrPos)
  have hnegεBall : -ε ∈ Metric.ball (0 : ℝ) r := by
    rw [Real.mem_ball_zero_iff, abs_neg]
    simpa [ε, abs_of_pos hεPos] using (half_lt_self hrPos)
  have hplusStrict : x + ε • d ∈ strictFeasible := by
    exact hrBall hεBall
  have hminusStrict : x + (-ε) • d ∈ strictFeasible := by
    exact hrBall hnegεBall
  have hdDegree : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦
        (e : Sym2 V) ∈ G.incidenceFinset v).sum d = 0 := by
    intro v
    rw [← edgeIncMatrix_mulVec_apply]
    exact congrFun hdMul v
  have hV' : Even (Nat.card V) := by
    simpa using hV
  have hperturbedPerfect (t : ℝ) (ht : x + t • d ∈ strictFeasible) :
      x + t • d ∈ perfectMatchingConstraintSet G := by
    rcases ht with ⟨htPos, htCuts⟩
    rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      exact (Set.mem_iInter.mp htPos e).le
    · intro v
      -- Kernel directions preserve every degree equation.
      calc
        (Finset.univ.filter fun e : G.edgeSet ↦
            (e : Sym2 V) ∈ G.incidenceFinset v).sum (x + t • d) =
            (Finset.univ.filter fun e : G.edgeSet ↦
              (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
              t * (Finset.univ.filter fun e : G.edgeSet ↦
                (e : Sym2 V) ∈ G.incidenceFinset v).sum d := by
                  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                    Finset.mul_sum]
        _ = 1 := by rw [hxDegree v, hdDegree v, mul_zero, add_zero]
    · intro U hUOdd
      by_cases hUProper : 1 < U.ncard
      · have hUComplOdd : Odd Uᶜ.ncard :=
          (Set.odd_ncard_compl_iff hV' U).2 hUOdd
        by_cases hUComplProper : 1 < Uᶜ.ncard
        · let S : Finset V := U.toFinite.toFinset
          have hScoe : (S : Set V) = U := by
            simp [S, Set.Finite.coe_toFinset]
          have hScard : S.card = U.ncard := by
            simpa [S, Set.toFinite_toFinset] using (Set.ncard_eq_toFinset_card' U).symm
          have hScomplCard : (Finset.univ \ S).card = Uᶜ.ncard := by
            have hcoe : ((Finset.univ \ S : Finset V) : Set V) = Uᶜ := by
              ext v
              simp [S]
            rw [← Set.ncard_coe_Finset, hcoe]
          have hStrict := Set.mem_iInter.mp htCuts S
          have hProper : Odd S.card ∧ 1 < S.card ∧ 1 < (Finset.univ \ S).card := by
            simpa [hScard, hScomplCard] using ⟨hUOdd, hUProper, hUComplProper⟩
          rw [if_pos hProper] at hStrict
          simpa [hScoe] using hStrict.le
        · have hUComplCard : Uᶜ.ncard = 1 := by
            have hpos : 0 < Uᶜ.ncard := hUComplOdd.pos
            omega
          have hxCutOne : (δ[G] Uᶜ).sum x = 1 := by
            obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hUComplCard
            rw [hv, cutSingleton_eq_incidenceFilter]
            exact hxDegree v
          have hdCutZero : (δ[G] Uᶜ).sum d = 0 :=
            cutSum_eq_zero_of_edgeIncMatrix_mulVec_eq_zero (G := G) d hdMul hUComplCard
          -- A co-singleton cut is the same cut as its singleton complement.
          rw [← cutEdgeFinset_compl (G := G) U]
          calc
            (δ[G] Uᶜ).sum (x + t • d) =
                (δ[G] Uᶜ).sum x + t * (δ[G] Uᶜ).sum d := by
                  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                    Finset.mul_sum]
            _ = 1 := by rw [hxCutOne, hdCutZero, mul_zero, add_zero]
      · have hUCard : U.ncard = 1 := by
          have hpos : 0 < U.ncard := hUOdd.pos
          omega
        have hxCutOne : (δ[G] U).sum x = 1 := by
          obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hUCard
          rw [hv, cutSingleton_eq_incidenceFilter]
          exact hxDegree v
        have hdCutZero : (δ[G] U).sum d = 0 :=
          cutSum_eq_zero_of_edgeIncMatrix_mulVec_eq_zero (G := G) d hdMul hUCard
        -- Singleton cuts are degree equations and hence do not move along `d`.
        calc
          (δ[G] U).sum (x + t • d) =
              (δ[G] U).sum x + t * (δ[G] U).sum d := by
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                  Finset.mul_sum]
          _ = 1 := by rw [hxCutOne, hdCutZero, mul_zero, add_zero]
  have hplusMatch : x + ε • d ∈ matchingConstraintSet G :=
    mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet
      (G := G) (hperturbedPerfect ε hplusStrict)
  have hminusMatch : x + (-ε) • d ∈ matchingConstraintSet G :=
    mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet
      (G := G) (hperturbedPerfect (-ε) hminusStrict)
  have hmidpoint : x ∈ openSegment ℝ (x + ε • d) (x + (-ε) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    -- The two opposite perturbations have `x` as their strict midpoint.
    ext e
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hplusEq : x + ε • d = x :=
    (mem_extremePoints_iff_left.mp hxExtreme).2
      (x + ε • d) hplusMatch (x + (-ε) • d) hminusMatch hmidpoint
  ext e
  have heq := congrFun hplusEq e
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq
  nlinarith

/-- Helper for Theorem 4.23: any dependency-closed bridge
`matchingConstraintSet G ⊆ matchingPolytope G` immediately solves the positive branch, because the
perfect-matching constraints already imply the ordinary matching constraints. -/
private lemma memMatchingPolytopeOfMatchingConstraintBridge
    (hbridge : matchingConstraintSet G ⊆ matchingPolytope G)
    {x : G.edgeSet → ℝ} (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ matchingPolytope G := by
  -- Forget the degree equalities down to the ambient matching constraints, then apply the bridge.
  exact hbridge (mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := G) hxPerfect)

/-- Helper for Theorem 4.23: a feasible perfect-matching constraint point would give a perfect
matching once every Tutte violator is ruled out. -/
private lemma exists_isPerfectMatching_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  -- Route correction: the positive branch only needs a perfect matching witness, so isolate the
  -- Tutte-existence step from the later degree-map injectivity contradiction.
  have hNoViolator : ∀ U : Set V, ¬ G.IsTutteViolator U := by
    -- Summing the odd-component cut lower bounds across the deleted graph bounds the number of
    -- odd components by the deleted-set cut, and the degree equations bound that cut by `|U|`.
    exact not_isTutteViolator_of_memPerfectMatchingConstraintSet (G := G) hx
  exact (SimpleGraph.tutte (G := G)).2 hNoViolator

/-- Helper for Theorem 4.23: a positive nonintegral extreme point of the perfect-matching
constraint set admits a proper tight odd shore. -/
private lemma existsProperTightOddShoreOfPositiveNonintegralExtremePoint
    {x : G.edgeSet → ℝ}
    (hxPerfect : x ∈ perfectMatchingConstraintSet G)
    (hxExtreme : x ∈ (matchingConstraintSet G).extremePoints ℝ)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_pos : ∀ e : G.edgeSet, 0 < x e) :
    ∃ S : Finset V,
      Odd S.card ∧
        1 < S.card ∧
          1 < (Finset.univ \ S).card ∧
            (δ[G] (S : Set V)).sum x = 1 := by
  have hV : Even (Fintype.card V) :=
    even_card_of_memPerfectMatchingConstraintSet (G := G) hxPerfect
  by_contra hNoTightExists
  push_neg at hNoTightExists
  -- A feasible perfect-constraint point gives a genuine perfect matching once Tutte violators are
  -- excluded, so the remaining contradiction is purely degree-map injectivity.
  rcases exists_isPerfectMatching_of_mem_perfectMatchingConstraintSet
      (G := G) hxPerfect with ⟨M, hM⟩
  have hInjective :
      Function.Injective (G.edgeIncMatrix ℝ).mulVecLin :=
    degreeMapInjectiveOfNoProperTightOddShore
      (G := G) hxPerfect hxExtreme hx_pos hV hNoTightExists
  have hxDegree :
      (G.edgeIncMatrix ℝ).mulVecLin x = (1 : V → ℝ) := by
    ext v
    -- The perfect-matching constraints force the unsigned degree map to be the constant-one
    -- vector.
    rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hxPerfect with
      ⟨-, hxDeg, -⟩
    simpa [Matrix.mulVecLin_apply] using (edgeIncMatrix_mulVec_apply (G := G) x v).trans (hxDeg v)
  have hMDegree :
      (G.edgeIncMatrix ℝ).mulVecLin (G.subgraphIncidenceVector ℝ M) = (1 : V → ℝ) := by
    ext v
    -- Perfect-matching incidence vectors satisfy the same degree-one equations.
    simpa [Matrix.mulVecLin_apply] using
      (edgeIncMatrix_mulVec_apply (G := G) (G.subgraphIncidenceVector ℝ M) v).trans
        (perfectMatchingIncidenceSumEqOne (G := G) hM v)
  have hxEq :
      x = G.subgraphIncidenceVector ℝ M := by
    apply hInjective
    simpa [hxDegree, hMDegree]
  have hInt :
      x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) := by
    simpa [hxEq] using subgraphIncidenceVector_memIntegerRange (G := G) M
  exact hx_not_int hInt

/-- Helper for Theorem 4.23: deleting the two endpoints of one matched edge preserves the
matching property on the remaining vertices. -/
private lemma isMatching_deleteVerts_toEdge
    {H : G.Subgraph} (hH : H.IsMatching) (v : H.verts) :
    (H.deleteVerts ((((hH.toEdge v : H.edgeSet) : Sym2 V) : Set V))).IsMatching := by
  intro u hu
  have hu_mem :
      u ∈ H.verts ∧
        u ∉ ((((hH.toEdge v : H.edgeSet) : Sym2 V) : Set V)) := by
    simpa [Subgraph.deleteVerts_verts, Set.mem_diff] using hu
  obtain ⟨w, huw, huniqw⟩ := hH hu_mem.1
  have hw_not_mem :
      w ∉ ((((hH.toEdge v : H.edgeSet) : Sym2 V) : Set V)) := by
    intro hw_mem
    let e₀ : H.edgeSet := hH.toEdge v
    let w' : V := Sym2.Mem.other hw_mem
    have hw_adj : H.Adj w w' := by
      -- The deleted edge still witnesses the unique partner of any endpoint it contains.
      exact Subgraph.mem_edgeSet.1 (by simpa [e₀, w', Sym2.other_spec hw_mem] using e₀.2)
    have hu_eq : u = w' := by
      -- Both `u` and the opposite endpoint of the deleted edge are adjacent to `w`.
      exact hH.eq_of_adj_left huw.symm hw_adj
    exact hu_mem.2 (by
      simpa [w', hu_eq] using Sym2.other_mem hw_mem)
  refine ⟨w, ?_, ?_⟩
  · -- The original partner survives because otherwise `u` would lie on the deleted edge too.
    rw [Subgraph.deleteVerts_adj]
    exact ⟨hu_mem.1, hu_mem.2, huw.snd_mem, hw_not_mem, huw⟩
  · intro y huy
    -- Uniqueness is inherited from the original matching.
    rw [Subgraph.deleteVerts_adj] at huy
    exact huniqw y huy.2.2.2

/-- Helper for Theorem 4.23: deleting the unique boundary edge of a contracted perfect matching
does not change any internal contracted edge coordinate. -/
private lemma deleteBoundaryPerfectMatchingIncidence_eq_of_notMemIncidenceNone
    {S : Finset V} {M : (shoreContraction G S).Subgraph} (hM : M.IsPerfectMatching)
    {f : (shoreContraction G S).edgeSet}
    (hfnone : none ∉ (f : Sym2 (Option S))) :
    (shoreContraction G S).subgraphIncidenceVector ℝ
        (M.deleteVerts
          ((((hM.1.toEdge ⟨none, hM.2 none⟩ : M.edgeSet) : Sym2 (Option S)) :
            Set (Option S)))) f =
      (shoreContraction G S).subgraphIncidenceVector ℝ M f := by
  let e₀ : M.edgeSet := hM.1.toEdge ⟨none, hM.2 none⟩
  let U : Set (Option S) := (((e₀ : M.edgeSet) : Sym2 (Option S)) : Set (Option S))
  have hnone_e₀ : none ∈ ((e₀ : M.edgeSet) : Sym2 (Option S)) := by
    -- The boundary edge chosen from `none` still contains `none` as one endpoint.
    simpa [e₀] using hM.1.mem_coe_toEdge (hM.2 none)
  by_cases hfM : f.1 ∈ M.edgeSet
  · have hendpoint_not_mem :
        ∀ x : Option S, x ∈ (f : Sym2 (Option S)) → x ∉ U := by
      intro x hxF hxU
      have hxAdjF : M.Adj x (Sym2.Mem.other hxF) := by
        exact Subgraph.mem_edgeSet.1 (by simpa [Sym2.other_spec hxF] using hfM)
      have hxAdj₀ : M.Adj x (Sym2.Mem.other hxU) := by
        exact Subgraph.mem_edgeSet.1 (by simpa [e₀, Sym2.other_spec hxU] using e₀.2)
      have hother_eq : Sym2.Mem.other hxF = Sym2.Mem.other hxU := by
        exact hM.1.eq_of_adj_left hxAdjF hxAdj₀
      have hval_eq : f.1 = ((e₀ : M.edgeSet) : (shoreContraction G S).edgeSet).1 := by
        calc
          f.1 = s (x, Sym2.Mem.other hxF) := by
            symm
            exact Sym2.other_spec hxF
          _ = s (x, Sym2.Mem.other hxU) := by rw [hother_eq]
          _ = ((e₀ : M.edgeSet) : (shoreContraction G S).edgeSet).1 := by
            exact Sym2.other_spec hxU
      have hnone_f : none ∈ (f : Sym2 (Option S)) := by
        rw [hval_eq]
        simpa using hnone_e₀
      exact hfnone hnone_f
    have hfDelete : f.1 ∈ (M.deleteVerts U).edgeSet := by
      have hAdjF : M.Adj f.1.out.1 f.1.out.2 := Subgraph.mem_edgeSet.1 hfM
      rw [Subgraph.mem_edgeSet, Subgraph.deleteVerts_adj]
      refine ⟨hAdjF.fst_mem, ?_, hAdjF.snd_mem, ?_, hAdjF⟩
      · exact hendpoint_not_mem _ (Sym2.out_fst_mem _)
      · exact hendpoint_not_mem _ (Sym2.out_snd_mem _)
    -- Internal edges survive the deletion because neither endpoint lies on the boundary edge.
    simp [SimpleGraph.subgraphIncidenceVector, hfM, hfDelete]
  · have hfDelete : f.1 ∉ (M.deleteVerts U).edgeSet := by
      intro hfDelete
      have hAdjF : M.Adj f.1.out.1 f.1.out.2 := by
        rw [Subgraph.mem_edgeSet, Subgraph.deleteVerts_adj] at hfDelete
        exact hfDelete.2.2.2
      exact hfM (Subgraph.mem_edgeSet.2 hAdjF)
    -- If `f` was absent before deletion, it is absent afterwards as well.
    simp [SimpleGraph.subgraphIncidenceVector, hfM, hfDelete]

/-- Helper for Theorem 4.23: evaluating a contracted perfect-matching decomposition at one edge
incident to `none` recovers the total weight of the terms whose unique `none`-edge is that edge. -/
private lemma boundaryEdgeWeightSum_eq_shorePushforward_apply
    {S : Finset V} {x : G.edgeSet → ℝ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (M : ι → (shoreContraction G S).Subgraph)
    (hPerfect : ∀ i, (M i).IsPerfectMatching)
    (hsum :
      ∑ i, w i • (shoreContraction G S).subgraphIncidenceVector ℝ (M i) =
        shorePushforward G S x)
    {f : (shoreContraction G S).edgeSet}
    (hf : (f : Sym2 (Option S)) ∈ (shoreContraction G S).incidenceFinset none) :
    (Finset.univ.filter
        (fun i ↦
          (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
              (M i).edgeSet) : (shoreContraction G S).edgeSet) = f)).sum w =
      shorePushforward G S x f := by
  let boundaryEdge : ι → (shoreContraction G S).edgeSet :=
    fun i ↦ (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
        (M i).edgeSet) : (shoreContraction G S).edgeSet)
  have hboundary_incidence :
      ∀ i,
        (shoreContraction G S).subgraphIncidenceVector ℝ (M i) f =
          if boundaryEdge i = f then 1 else 0 := by
    intro i
    by_cases hEq : boundaryEdge i = f
    · have hf_mem : f.1 ∈ (M i).edgeSet := by
        simpa [boundaryEdge, hEq] using
          (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
              (M i).edgeSet)).2
      simp [SimpleGraph.subgraphIncidenceVector, hEq, hf_mem]
    · have hf_not_mem : f.1 ∉ (M i).edgeSet := by
        intro hf_mem
        have hnone_mem : none ∈ (f : Sym2 (Option S)) := by
          simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using hf
        let other : Option S := Sym2.Mem.other hnone_mem
        have hf_adj : (M i).Adj none other := by
          exact Subgraph.mem_edgeSet.1 (by
            simpa [other, Sym2.other_spec hnone_mem] using hf_mem)
        have hto :
            boundaryEdge i = ⟨s(none, other), hf_adj⟩ := by
          apply Subtype.ext
          simpa [boundaryEdge, other] using
            congrArg Subtype.val ((hPerfect i).1.toEdge_eq_of_adj hf_adj)
        have hcanon : (⟨s(none, other), hf_adj⟩ :
            (shoreContraction G S).edgeSet) = f := by
          apply Subtype.ext
          simpa [other] using Sym2.other_spec hnone_mem
        exact hEq (hto.trans hcanon)
      simp [SimpleGraph.subgraphIncidenceVector, hEq, hf_not_mem]
  have hcoord :=
    weightedSumApply (G := shoreContraction G S) w
      (fun i ↦ (shoreContraction G S).subgraphIncidenceVector ℝ (M i)) hsum f
  calc
    (Finset.univ.filter (fun i ↦ boundaryEdge i = f)).sum w =
        ∑ i, if boundaryEdge i = f then w i else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ i, w i * (shoreContraction G S).subgraphIncidenceVector ℝ (M i) f := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hboundary_incidence i]
          by_cases hEq : boundaryEdge i = f <;> simp [hEq]
    _ = shorePushforward G S x f := hcoord

/-- Helper for Theorem 4.23: on retained vertices, adjacency in the shore contraction is exactly
the original adjacency. -/
private lemma shoreContraction_adj_some_some_iff (S : Finset V) {u v : S} :
    (shoreContraction G S).Adj (some u) (some v) ↔ G.Adj u.1 v.1 := by
  constructor
  · intro h
    -- Unpack the mapped adjacency and use that `shoreProjection` is injective on `S`.
    rcases (SimpleGraph.map_adj' (shoreProjection S) G (some u) (some v)).1 h with
      ⟨-, a, b, hab, ha, hb⟩
    have haS : a ∈ S := by
      by_contra haS
      rw [shoreProjection_apply_of_notMem (G := G) S haS] at ha
      simp at ha
    have hbS : b ∈ S := by
      by_contra hbS
      rw [shoreProjection_apply_of_notMem (G := G) S hbS] at hb
      simp at hb
    rw [shoreProjection_apply_of_mem (G := G) S haS] at ha
    rw [shoreProjection_apply_of_mem (G := G) S hbS] at hb
    have hau : a = u.1 := by
      exact congrArg Subtype.val (Option.some.inj ha)
    have hbv : b = v.1 := by
      exact congrArg Subtype.val (Option.some.inj hb)
    simpa [hau, hbv] using hab
  · intro h
    -- Push the original adjacency forward through the shore projection.
    exact (SimpleGraph.map_adj' (shoreProjection S) G (some u) (some v)).2
      ⟨by simpa using h.ne, u.1, v.1, h,
        shoreProjection_apply_of_mem (G := G) S u.2,
        shoreProjection_apply_of_mem (G := G) S v.2⟩

/-- Helper for Theorem 4.23: an edge internal to `S` projects to a genuine retained edge of the
shore contraction. -/
private lemma projectedInducedEdge_mem_edgeSet
    {S : Finset V} {e : G.edgeSet} (he : e ∈ E[G] (S : Set V)) :
    Sym2.map (shoreProjection S) e.1 ∈ (shoreContraction G S).edgeSet := by
  let u : S := ⟨e.1.out.1, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.1⟩
  let v : S := ⟨e.1.out.2, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.2⟩
  have hAdj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.out_eq] using e.2
  have hMapAdj : (shoreContraction G S).Adj (some u) (some v) := by
    exact (shoreContraction_adj_some_some_iff (G := G) S).2 (by simpa [u, v] using hAdj)
  -- Normalize the projected internal edge to the canonical `some-some` edge of the contraction.
  have hrepr :
      Sym2.map (shoreProjection S) e.1 = s (some u) (some v) := by
    calc
      Sym2.map (shoreProjection S) e.1 =
          Sym2.map (shoreProjection S) (s (e.1.out.1, e.1.out.2)) := by
            rw [e.1.out_eq]
      _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
            simp
      _ = s (some u) (some v) := by
            simp [u, v]
  rw [hrepr]
  exact (shoreContraction G S).mem_edgeSet.2 hMapAdj

/-- Helper for Theorem 4.23: package the projection of an internal edge as an edge of the shore
contraction. -/
private def projectedInducedEdge
    (S : Finset V) (e : G.edgeSet) (he : e ∈ E[G] (S : Set V)) :
    (shoreContraction G S).edgeSet :=
  ⟨Sym2.map (shoreProjection S) e.1, projectedInducedEdge_mem_edgeSet (G := G) he⟩

/-- Helper for Theorem 4.23: the canonical projected internal edge has the expected underlying
unordered pair. -/
@[simp] private lemma projectedInducedEdge_val
    {S : Finset V} {e : G.edgeSet} (he : e ∈ E[G] (S : Set V)) :
    (projectedInducedEdge (G := G) S e he).1 = Sym2.map (shoreProjection S) e.1 := rfl

/-- Helper for Theorem 4.23: the lifted adjacency predicate from a retained shore subgraph really
lands back in the original graph. -/
private lemma shoreInternalLift_adj_sub (S : Finset V) {D : (shoreContraction G S).Subgraph}
    {u v : V}
    (h :
      ∃ hu : u ∈ S, ∃ hv : v ∈ S,
        D.Adj (some ⟨u, hu⟩) (some ⟨v, hv⟩)) :
    G.Adj u v := by
  rcases h with ⟨hu, hv, hAdj⟩
  -- Strip the contraction edge back to an ordinary edge on the retained shore.
  exact
    (shoreContraction_adj_some_some_iff (G := G) S
      (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)).1 (D.adj_sub hAdj)

/-- Helper for Theorem 4.23: the lifted adjacency predicate records the left endpoint as a lifted
vertex. -/
private lemma shoreInternalLift_edge_vert (S : Finset V) {D : (shoreContraction G S).Subgraph}
    {u v : V}
    (h :
      ∃ hu : u ∈ S, ∃ hv : v ∈ S,
        D.Adj (some ⟨u, hu⟩) (some ⟨v, hv⟩)) :
    u ∈ {w : V | ∃ hw : w ∈ S, (some ⟨w, hw⟩ : Option S) ∈ D.verts} := by
  rcases h with ⟨hu, hv, hAdj⟩
  -- The lifted edge still certifies that its first endpoint is present.
  exact ⟨hu, D.edge_vert hAdj⟩

/-- Helper for Theorem 4.23: the lifted adjacency predicate is symmetric. -/
private lemma shoreInternalLift_symm (S : Finset V) (D : (shoreContraction G S).Subgraph) :
    Symmetric
      (fun u v : V ↦
        ∃ hu : u ∈ S, ∃ hv : v ∈ S,
          D.Adj (some ⟨u, hu⟩) (some ⟨v, hv⟩)) := by
  intro u v h
  -- Reverse the contracted adjacency and swap the shore witnesses.
  rcases h with ⟨hu, hv, hAdj⟩
  exact ⟨hv, hu, D.symm hAdj⟩

/-- Helper for Theorem 4.23: a contracted subgraph supported on retained `some`-vertices lifts to
an original-graph subgraph on the same shore. -/
private def shoreInternalLift (S : Finset V) (D : (shoreContraction G S).Subgraph) : G.Subgraph :=
  { verts := {v : V | ∃ hv : v ∈ S, (some ⟨v, hv⟩ : Option S) ∈ D.verts}
    Adj := fun u v ↦
      ∃ hu : u ∈ S, ∃ hv : v ∈ S,
        D.Adj (some ⟨u, hu⟩) (some ⟨v, hv⟩)
    adj_sub := shoreInternalLift_adj_sub (G := G) S
    edge_vert := shoreInternalLift_edge_vert (G := G) S
    symm := shoreInternalLift_symm (G := G) S D }

/-- Helper for Theorem 4.23: every lifted vertex of `shoreInternalLift S D` still lies on the
retained shore `S`. -/
private lemma shoreInternalLift_verts_subset (S : Finset V)
    (D : (shoreContraction G S).Subgraph) :
    (shoreInternalLift (G := G) S D).verts ⊆ (S : Set V) := by
  intro v hv
  exact hv.choose

/-- Helper for Theorem 4.23: if a deleted contracted subgraph no longer contains `none`, then its
lift is a matching on the original shore. -/
private lemma shoreInternalLift_isMatching {S : Finset V}
    {D : (shoreContraction G S).Subgraph} (hD : D.IsMatching)
    (hnone : (none : Option S) ∉ D.verts) :
    (shoreInternalLift (G := G) S D).IsMatching := by
  intro u hu
  rcases hu with ⟨huS, huD⟩
  obtain ⟨t, htAdj, htUnique⟩ := hD huD
  have ht_ne_none : t ≠ none := by
    intro ht
    apply hnone
    simpa [ht] using D.edge_vert htAdj.symm
  -- The unique neighbor of a lifted vertex cannot be `none`, so it is another retained vertex.
  cases ht : t with
  | none =>
      exact (ht_ne_none rfl).elim
  | some v =>
      refine ⟨v.1, ⟨huS, v.2, ?_⟩, ?_⟩
      · simpa [shoreInternalLift, ht] using htAdj
      · intro w huw
        rcases huw with ⟨-, hwS, hwAdj⟩
        have hEq : (some v : Option S) = some ⟨w, hwS⟩ := by
          exact htUnique _ (by simpa [ht] using hwAdj)
        exact congrArg Subtype.val (Option.some.inj hEq)

/-- Helper for Theorem 4.23: if the contracted vertex `some v` was deleted, then the shore lift
omits `v` as well. -/
private lemma shoreInternalLift_not_mem_verts_of_notMem {S : Finset V}
    {D : (shoreContraction G S).Subgraph} {v : V} (hv : v ∈ S)
    (hnot : (some ⟨v, hv⟩ : Option S) ∉ D.verts) :
    v ∉ (shoreInternalLift (G := G) S D).verts := by
  intro hvLift
  rcases hvLift with ⟨hv', hvD⟩
  have hEq : (⟨v, hv⟩ : S) = ⟨v, hv'⟩ := Subtype.ext rfl
  exact hnot (hEq ▸ hvD)

/-- Helper for Theorem 4.23: gluing two shore matchings with a cut edge stays a matching provided
the supports lie on complementary shores and omit the cut endpoints. -/
private lemma gluedMatchingOfSplitSupports_isMatching
    {S : Finset V} {u v : V} (huS : u ∈ S) (hvS : v ∉ S) (hGuv : G.Adj u v)
    {L R : G.Subgraph} (hL : L.IsMatching) (hR : R.IsMatching)
    (hLS : L.support ⊆ (S : Set V)) (hRS : R.support ⊆ ((S : Set V)ᶜ))
    (huL : u ∉ L.verts) (hvR : v ∉ R.verts) :
    (L ⊔ R ⊔ G.subgraphOfAdj hGuv).IsMatching := by
  have hLR : Disjoint L.support R.support := by
    rw [Set.disjoint_left]
    intro x hxL hxR
    exact (hRS hxR) (hLS hxL)
  have hLRMatch : (L ⊔ R).IsMatching := hL.sup hR hLR
  have hCutDisj : Disjoint (L ⊔ R).support (G.subgraphOfAdj hGuv).support := by
    rw [Set.disjoint_left, SimpleGraph.support_subgraphOfAdj]
    intro x hxLR hxCut
    rcases hxCut with rfl | rfl
    · have hxL : x ∉ L.support := by
        intro hxL
        exact huL ((hL.support_eq_verts ▸ hxL))
      have hxR : x ∉ R.support := by
        intro hxR
        exact (hvS (hRS hxR))
      rcases hxLR with hxL | hxR
      · exact (hxL hxL).elim
      · exact (hxR hxR).elim
    · have hxL : x ∉ L.support := by
        intro hxL
        exact (hvS (hLS hxL))
      have hxR : x ∉ R.support := by
        intro hxR
        exact hvR ((hR.support_eq_verts ▸ hxR))
      rcases hxLR with hxL | hxR
      · exact (hxL hxL).elim
      · exact (hxR hxR).elim
  -- First glue the two shore matchings, then add the singleton cut edge.
  exact hLRMatch.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hGuv) hCutDisj

/-- Helper for Theorem 4.23: normalizing the weights over one projected boundary-edge fiber gives
total mass `1`. -/
private lemma boundaryFiberWeightSum_eq_one
    {S : Finset V} {x : G.edgeSet → ℝ} {ι : Type*} [Fintype ι]
    (hx_pos : ∀ e : G.edgeSet, 0 < x e)
    (w : ι → ℝ) (M : ι → (shoreContraction G S).Subgraph)
    (hPerfect : ∀ i, (M i).IsPerfectMatching)
    (hsum :
      ∑ i, w i • (shoreContraction G S).subgraphIncidenceVector ℝ (M i) =
        shorePushforward G S x)
    {e : G.edgeSet} (he : e ∈ δ[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    ∑ i, (if (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
          (M i).edgeSet) : (shoreContraction G S).edgeSet) = f
        then w i / shorePushforward G S x f else 0) = 1 := by
  -- Rewrite the conditional fiber sum through the filtered boundary weights, then divide by the
  -- positive projected boundary coordinate.
  have hpos : 0 < shorePushforward G S x f :=
    shorePushforward_pos_of_eq_projectedEdge (G := G) hx_pos hf
  have hboundary :
      (Finset.univ.filter
          (fun i ↦
            (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
                (M i).edgeSet) : (shoreContraction G S).edgeSet) = f)).sum w =
        shorePushforward G S x f :=
    boundaryEdgeWeightSum_eq_shorePushforward_apply (G := G) w M hPerfect hsum
      (projectedCutEdge_mem_incidence_none_of_mem_cutEdgeFinset (G := G) he hf)
  calc
    ∑ i, (if (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
            (M i).edgeSet) : (shoreContraction G S).edgeSet) = f
          then w i / shorePushforward G S x f else 0) =
        ((Finset.univ.filter
            (fun i ↦
              (((hPerfect i).1.toEdge ⟨none, (hPerfect i).2 none⟩ :
                  (M i).edgeSet) : (shoreContraction G S).edgeSet) = f)).sum w) /
          shorePushforward G S x f := by
            rw [Finset.sum_filter]
            rw [div_eq_mul_inv]
            rw [Finset.sum_mul]
    _ = shorePushforward G S x f / shorePushforward G S x f := by rw [hboundary]
    _ = 1 := by exact div_self (ne_of_gt hpos)

/-- Helper for Theorem 4.23: lifting a contracted shore subgraph back to `G` preserves the
coordinate of every internal shore edge. -/
private lemma shoreInternalLift_incidence_eq_of_memInducedEdgeFinset
    {S : Finset V} {D : (shoreContraction G S).Subgraph} {e : G.edgeSet}
    (he : e ∈ E[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    G.subgraphIncidenceVector ℝ (shoreInternalLift (G := G) S D) e =
      (shoreContraction G S).subgraphIncidenceVector ℝ D f := by
  let u : S :=
    ⟨e.1.out.1, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.1⟩
  let v : S :=
    ⟨e.1.out.2, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.2⟩
  have hrepr : f.1 = s (some u) (some v) := by
    -- Normalize the projected internal edge to the retained `some-some` form.
    calc
      f.1 = Sym2.map (shoreProjection S) e.1 := hf.symm
      _ = Sym2.map (shoreProjection S) (s(e.1.out.1, e.1.out.2)) := by
            rw [e.1.out_eq]
      _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
            simp
      _ = s (some u) (some v) := by
            simp [u, v]
  by_cases hfD : f.1 ∈ D.edgeSet
  · have hAdjD : D.Adj (some u) (some v) := by
      -- Reinterpret membership of `f` in `D` through the normalized endpoint form.
      simpa [hrepr] using (Subgraph.mem_edgeSet.1 hfD)
    have heLift : e.1 ∈ (shoreInternalLift (G := G) S D).edgeSet := by
      -- The lifted subgraph keeps exactly the `some-some` contracted edges.
      exact Subgraph.mem_edgeSet.2 ⟨u.2, v.2, hAdjD⟩
    simp [SimpleGraph.subgraphIncidenceVector, hfD, heLift]
  · have heLift : e.1 ∉ (shoreInternalLift (G := G) S D).edgeSet := by
      intro heLift
      rcases (Subgraph.mem_edgeSet.1 heLift) with ⟨hu, hv, hAdjD⟩
      have hAdjCanon :
          D.Adj (some u) (some v) := by
        simpa [u, v] using hAdjD
      have hfD' : f.1 ∈ D.edgeSet := by
        simpa [hrepr] using (Subgraph.mem_edgeSet.2 hAdjCanon)
      exact hfD hfD'
    simp [SimpleGraph.subgraphIncidenceVector, hfD, heLift]

/-- Helper for Theorem 4.23: deleting the unique boundary edge of a contracted perfect matching
and then lifting back preserves every internal shore-edge coordinate. -/
private lemma shoreInternalLift_deleteBoundary_incidence_eq_of_memInducedEdgeFinset
    {S : Finset V} {M : (shoreContraction G S).Subgraph} (hM : M.IsPerfectMatching)
    {e : G.edgeSet} (he : e ∈ E[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) e.1 = f.1) :
    G.subgraphIncidenceVector ℝ
        (shoreInternalLift (G := G) S
          (M.deleteVerts
            ((((hM.1.toEdge ⟨none, hM.2 none⟩ : M.edgeSet) : Sym2 (Option S)) :
              Set (Option S))))) e =
      (shoreContraction G S).subgraphIncidenceVector ℝ M f := by
  let u : S :=
    ⟨e.1.out.1, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.1⟩
  let v : S :=
    ⟨e.1.out.2, (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he |>.2⟩
  have hfnone : none ∉ (f : Sym2 (Option S)) := by
    -- An internal edge projects to a `some-some` edge, so it avoids the collapsed vertex.
    have hrepr : f.1 = s (some u) (some v) := by
      calc
        f.1 = Sym2.map (shoreProjection S) e.1 := hf.symm
        _ = Sym2.map (shoreProjection S) (s(e.1.out.1, e.1.out.2)) := by
              rw [e.1.out_eq]
        _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
              simp
        _ = s (some u) (some v) := by
              simp [u, v]
    intro hnone
    rw [hrepr] at hnone
    simp at hnone
  calc
    G.subgraphIncidenceVector ℝ
        (shoreInternalLift (G := G) S
          (M.deleteVerts
            ((((hM.1.toEdge ⟨none, hM.2 none⟩ : M.edgeSet) : Sym2 (Option S)) :
              Set (Option S))))) e =
      (shoreContraction G S).subgraphIncidenceVector ℝ
        (M.deleteVerts
          ((((hM.1.toEdge ⟨none, hM.2 none⟩ : M.edgeSet) : Sym2 (Option S)) :
            Set (Option S)))) f := by
              exact shoreInternalLift_incidence_eq_of_memInducedEdgeFinset
                (G := G) he hf
    _ = (shoreContraction G S).subgraphIncidenceVector ℝ M f := by
          exact deleteBoundaryPerfectMatchingIncidence_eq_of_notMemIncidenceNone
            (G := G) hM hfnone

/-- Helper for Theorem 4.23: glue the two deleted shore lifts back to `G` and restore one
original cut edge. -/
private def gluedShoreMatching
    (S : Finset V) (e : G.edgeSet)
    (ML : (shoreContraction G S).Subgraph) (hML : ML.IsPerfectMatching)
    (MR : (shoreContraction G (Finset.univ \ S)).Subgraph) (hMR : MR.IsPerfectMatching) :
    G.Subgraph :=
  shoreInternalLift (G := G) S
      (ML.deleteVerts
        ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
          Set (Option S))))
    ⊔ shoreInternalLift (G := G) (Finset.univ \ S)
      (MR.deleteVerts
        ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
            Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S)))))
    ⊔ G.subgraphOfAdj e.2

/-- Helper for Theorem 4.23: the glued shore construction is a matching once the two deleted
boundary edges agree with the chosen original cut edge on each contracted shore. -/
private lemma gluedShoreMatching_isMatching
    {S : Finset V} {e : G.edgeSet}
    {ML : (shoreContraction G S).Subgraph} (hML : ML.IsPerfectMatching)
    {MR : (shoreContraction G (Finset.univ \ S)).Subgraph} (hMR : MR.IsPerfectMatching)
    (he : e ∈ δ[G] (S : Set V))
    (hfL :
      (((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) :
          (shoreContraction G S).edgeSet)).1 =
        Sym2.map (shoreProjection S) e.1)
    (hfR :
      (((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
          (shoreContraction G (Finset.univ \ S)).edgeSet)).1 =
        Sym2.map (shoreProjection (Finset.univ \ S)) e.1) :
    (gluedShoreMatching (G := G) S e ML hML MR hMR).IsMatching := by
  rcases (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) e).1 he with
    (⟨huS, hvS⟩ | ⟨hvS, huS⟩)
  · let DL : (shoreContraction G S).Subgraph :=
      ML.deleteVerts
        ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
          Set (Option S)))
    let DR : (shoreContraction G (Finset.univ \ S)).Subgraph :=
      MR.deleteVerts
        ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
            Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S))))
    let L : G.Subgraph := shoreInternalLift (G := G) S DL
    let R : G.Subgraph := shoreInternalLift (G := G) (Finset.univ \ S) DR
    have hnoneL : (none : Option S) ∉ DL.verts := by
      -- Deleting the boundary edge removes the collapsed vertex on the left shore.
      simp [DL, Subgraph.deleteVerts_verts]
    have hnoneR : (none : Option (Finset.univ \ S)) ∉ DR.verts := by
      -- Deleting the boundary edge removes the collapsed vertex on the right shore.
      simp [DR, Subgraph.deleteVerts_verts]
    have hL : L.IsMatching := by
      -- Each deleted shore lift is a matching away from the collapsed vertex.
      simpa [L, DL] using
        shoreInternalLift_isMatching (G := G) (S := S) (D := DL)
          (hD := isMatching_deleteVerts_toEdge (G := shoreContraction G S) hML.1
            ⟨none, hML.2 none⟩)
          hnoneL
    have hR : R.IsMatching := by
      -- The complementary deleted shore lift is handled identically.
      simpa [R, DR] using
        shoreInternalLift_isMatching (G := G) (S := Finset.univ \ S) (D := DR)
          (hD := isMatching_deleteVerts_toEdge
            (G := shoreContraction G (Finset.univ \ S)) hMR.1 ⟨none, hMR.2 none⟩)
          hnoneR
    have hLS : L.support ⊆ (S : Set V) := by
      -- The left deleted lift stays entirely on the retained shore `S`.
      intro x hx
      exact shoreInternalLift_verts_subset (G := G) S DL (hL.support_eq_verts ▸ hx)
    have hRS : R.support ⊆ ((S : Set V)ᶜ) := by
      -- The right deleted lift stays entirely on the complementary shore.
      intro x hx
      have hxT :
          x ∈ (((Finset.univ \ S : Finset V) : Set V)) := by
        exact shoreInternalLift_verts_subset (G := G) (Finset.univ \ S) DR
          (hR.support_eq_verts ▸ hx)
      simpa using hxT
    have huBoundary :
        (some ⟨e.1.out.1, huS⟩ : Option S) ∈
          ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
            Set (Option S))) := by
      -- The left deleted boundary edge is exactly the projected image of `e`.
      have hrepr :
          (((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) :
              (shoreContraction G S).edgeSet)).1 =
            s (some ⟨e.1.out.1, huS⟩) none := by
        calc
          (((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) :
              (shoreContraction G S).edgeSet)).1 =
              Sym2.map (shoreProjection S) e.1 := hfL
          _ = Sym2.map (shoreProjection S) (s (e.1.out.1, e.1.out.2)) := by
                rw [e.1.out_eq]
          _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
                simp
          _ = s (some ⟨e.1.out.1, huS⟩) none := by
                rw [shoreProjection_apply_of_mem (G := G) S huS,
                  shoreProjection_apply_of_notMem (G := G) S hvS]
      rw [hrepr]
      simp
    have hvBoundary :
        (some ⟨e.1.out.2, by simpa using hvS⟩ :
            Option (Finset.univ \ S)) ∈
          ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              Sym2 (Option (Finset.univ \ S))) :
            Set (Option (Finset.univ \ S)))) := by
      -- The right deleted boundary edge is the complementary projected image of `e`.
      have hrepr :
          (((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              (shoreContraction G (Finset.univ \ S)).edgeSet)).1 =
            s none (some ⟨e.1.out.2, by simpa using hvS⟩) := by
        calc
          (((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              (shoreContraction G (Finset.univ \ S)).edgeSet)).1 =
              Sym2.map (shoreProjection (Finset.univ \ S)) e.1 := hfR
          _ = Sym2.map (shoreProjection (Finset.univ \ S)) (s (e.1.out.1, e.1.out.2)) := by
                rw [e.1.out_eq]
          _ = s (shoreProjection (Finset.univ \ S) e.1.out.1)
                (shoreProjection (Finset.univ \ S) e.1.out.2) := by
                simp
          _ = s none (some ⟨e.1.out.2, by simpa using hvS⟩) := by
                rw [shoreProjection_apply_of_notMem (G := G) (Finset.univ \ S) (by simpa using huS),
                  shoreProjection_apply_of_mem (G := G) (Finset.univ \ S) (by simpa using hvS)]
      rw [hrepr]
      simp
    have huL :
        e.1.out.1 ∉ L.verts := by
      -- The left endpoint of the glued cut edge was deleted from the left shore lift.
      apply shoreInternalLift_not_mem_verts_of_notMem (G := G) (S := S) (D := DL) huS
      simpa [DL, Subgraph.deleteVerts_verts] using huBoundary
    have hvR :
        e.1.out.2 ∉ R.verts := by
      -- The right endpoint of the glued cut edge was deleted from the right shore lift.
      apply shoreInternalLift_not_mem_verts_of_notMem
        (G := G) (S := Finset.univ \ S) (D := DR) (by simpa using hvS)
      simpa [DR, Subgraph.deleteVerts_verts] using hvBoundary
    -- Route correction: use the dedicated split-support gluing lemma instead of unfolding the
    -- whole `sup` construction in the final matching proof.
    simpa [gluedShoreMatching, L, R, DL, DR] using
      gluedMatchingOfSplitSupports_isMatching (G := G) huS hvS e.2 hL hR hLS hRS huL hvR
  · let DL : (shoreContraction G S).Subgraph :=
      ML.deleteVerts
        ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
          Set (Option S)))
    let DR : (shoreContraction G (Finset.univ \ S)).Subgraph :=
      MR.deleteVerts
        ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
            Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S))))
    let L : G.Subgraph := shoreInternalLift (G := G) S DL
    let R : G.Subgraph := shoreInternalLift (G := G) (Finset.univ \ S) DR
    have hnoneL : (none : Option S) ∉ DL.verts := by
      simp [DL, Subgraph.deleteVerts_verts]
    have hnoneR : (none : Option (Finset.univ \ S)) ∉ DR.verts := by
      simp [DR, Subgraph.deleteVerts_verts]
    have hL : L.IsMatching := by
      simpa [L, DL] using
        shoreInternalLift_isMatching (G := G) (S := S) (D := DL)
          (hD := isMatching_deleteVerts_toEdge (G := shoreContraction G S) hML.1
            ⟨none, hML.2 none⟩)
          hnoneL
    have hR : R.IsMatching := by
      simpa [R, DR] using
        shoreInternalLift_isMatching (G := G) (S := Finset.univ \ S) (D := DR)
          (hD := isMatching_deleteVerts_toEdge
            (G := shoreContraction G (Finset.univ \ S)) hMR.1 ⟨none, hMR.2 none⟩)
          hnoneR
    have hLS : L.support ⊆ (S : Set V) := by
      intro x hx
      exact shoreInternalLift_verts_subset (G := G) S DL (hL.support_eq_verts ▸ hx)
    have hRS : R.support ⊆ ((S : Set V)ᶜ) := by
      intro x hx
      have hxT :
          x ∈ (((Finset.univ \ S : Finset V) : Set V)) := by
        exact shoreInternalLift_verts_subset (G := G) (Finset.univ \ S) DR
          (hR.support_eq_verts ▸ hx)
      simpa using hxT
    have huBoundary :
        (some ⟨e.1.out.2, hvS⟩ : Option S) ∈
          ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
            Set (Option S))) := by
      have hrepr :
          (((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) :
              (shoreContraction G S).edgeSet)).1 =
            s none (some ⟨e.1.out.2, hvS⟩) := by
        calc
          (((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) :
              (shoreContraction G S).edgeSet)).1 =
              Sym2.map (shoreProjection S) e.1 := hfL
          _ = Sym2.map (shoreProjection S) (s (e.1.out.1, e.1.out.2)) := by
                rw [e.1.out_eq]
          _ = s (shoreProjection S e.1.out.1) (shoreProjection S e.1.out.2) := by
                simp
          _ = s none (some ⟨e.1.out.2, hvS⟩) := by
                rw [shoreProjection_apply_of_notMem (G := G) S huS,
                  shoreProjection_apply_of_mem (G := G) S hvS]
      rw [hrepr]
      simp
    have hvBoundary :
        (some ⟨e.1.out.1, by simpa using huS⟩ :
            Option (Finset.univ \ S)) ∈
          ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              Sym2 (Option (Finset.univ \ S))) :
            Set (Option (Finset.univ \ S)))) := by
      have hrepr :
          (((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              (shoreContraction G (Finset.univ \ S)).edgeSet)).1 =
            s (some ⟨e.1.out.1, by simpa using huS⟩) none := by
        calc
          (((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
              (shoreContraction G (Finset.univ \ S)).edgeSet)).1 =
              Sym2.map (shoreProjection (Finset.univ \ S)) e.1 := hfR
          _ = Sym2.map (shoreProjection (Finset.univ \ S)) (s (e.1.out.1, e.1.out.2)) := by
                rw [e.1.out_eq]
          _ = s (shoreProjection (Finset.univ \ S) e.1.out.1)
                (shoreProjection (Finset.univ \ S) e.1.out.2) := by
                simp
          _ = s (some ⟨e.1.out.1, by simpa using huS⟩) none := by
                rw [shoreProjection_apply_of_mem (G := G) (Finset.univ \ S) (by simpa using huS),
                  shoreProjection_apply_of_notMem (G := G) (Finset.univ \ S) (by simpa using hvS)]
      rw [hrepr]
      simp
    have huL :
        e.1.out.2 ∉ L.verts := by
      apply shoreInternalLift_not_mem_verts_of_notMem (G := G) (S := S) (D := DL) hvS
      simpa [DL, Subgraph.deleteVerts_verts] using huBoundary
    have hvR :
        e.1.out.1 ∉ R.verts := by
      apply shoreInternalLift_not_mem_verts_of_notMem
        (G := G) (S := Finset.univ \ S) (D := DR) (by simpa using huS)
      simpa [DR, Subgraph.deleteVerts_verts] using hvBoundary
    simpa [gluedShoreMatching, L, R, DL, DR] using
      gluedMatchingOfSplitSupports_isMatching (G := G) hvS huS e.2.symm hL hR hLS hRS huL hvR

/-- Helper for Theorem 4.23: on an edge internal to `S`, the glued shore matching keeps exactly
the left deleted-lift coordinate. -/
private lemma gluedShoreMatching_incidenceLeft
    {S : Finset V} {e g : G.edgeSet}
    {ML : (shoreContraction G S).Subgraph} (hML : ML.IsPerfectMatching)
    {MR : (shoreContraction G (Finset.univ \ S)).Subgraph} (hMR : MR.IsPerfectMatching)
    (he : e ∈ δ[G] (S : Set V))
    (hg : g ∈ E[G] (S : Set V))
    {f : (shoreContraction G S).edgeSet}
    (hf : Sym2.map (shoreProjection S) g.1 = f.1) :
    G.subgraphIncidenceVector ℝ (gluedShoreMatching (G := G) S e ML hML MR hMR) g =
      (shoreContraction G S).subgraphIncidenceVector ℝ ML f := by
  let DL : (shoreContraction G S).Subgraph :=
    ML.deleteVerts
      ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
        Set (Option S)))
  let DR : (shoreContraction G (Finset.univ \ S)).Subgraph :=
    MR.deleteVerts
      ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
          Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S))))
  let R : G.Subgraph := shoreInternalLift (G := G) (Finset.univ \ S) DR
  have hRnot :
      g.1 ∉ R.edgeSet := by
    -- An edge internal to `S` cannot lie in the complementary lifted shore.
    intro hgR
    have hgVert : g.1.out.1 ∈ R.verts :=
      Subgraph.mem_verts_of_mem_edge hgR (Sym2.out_fst_mem _)
    have hgT :
        g.1.out.1 ∈ (((Finset.univ \ S : Finset V) : Set V)) := by
      exact shoreInternalLift_verts_subset (G := G) (Finset.univ \ S) DR hgVert
    exact (by simpa using hgT) ((memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) g).1 hg).1
  have hEnot :
      g.1 ∉ (G.subgraphOfAdj e.2).edgeSet := by
    -- The glued singleton cut edge is not internal to `S`.
    intro hgE
    have hge : g = e := by
      apply Subtype.ext
      simpa [SimpleGraph.edgeSet_subgraphOfAdj] using hgE
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) hg (hge ▸ he)
  calc
    G.subgraphIncidenceVector ℝ (gluedShoreMatching (G := G) S e ML hML MR hMR) g =
        G.subgraphIncidenceVector ℝ (shoreInternalLift (G := G) S DL) g := by
          -- Once the other two pieces vanish on `g`, only the left deleted lift remains.
          simp [gluedShoreMatching, DL, DR, R, SimpleGraph.subgraphIncidenceVector,
            SimpleGraph.Subgraph.edgeSet_sup, hRnot, hEnot]
    _ = (shoreContraction G S).subgraphIncidenceVector ℝ ML f := by
          exact shoreInternalLift_deleteBoundary_incidence_eq_of_memInducedEdgeFinset
            (G := G) (M := ML) hML hg hf

/-- Helper for Theorem 4.23: on an edge internal to the complementary shore, the glued shore
matching keeps exactly the right deleted-lift coordinate. -/
private lemma gluedShoreMatching_incidenceRight
    {S : Finset V} {e g : G.edgeSet}
    {ML : (shoreContraction G S).Subgraph} (hML : ML.IsPerfectMatching)
    {MR : (shoreContraction G (Finset.univ \ S)).Subgraph} (hMR : MR.IsPerfectMatching)
    (he : e ∈ δ[G] (S : Set V))
    (hg : g ∈ E[G] (((Finset.univ \ S : Finset V) : Set V)))
    {f : (shoreContraction G (Finset.univ \ S)).edgeSet}
    (hf : Sym2.map (shoreProjection (Finset.univ \ S)) g.1 = f.1) :
    G.subgraphIncidenceVector ℝ (gluedShoreMatching (G := G) S e ML hML MR hMR) g =
      (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ MR f := by
  let DL : (shoreContraction G S).Subgraph :=
    ML.deleteVerts
      ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
        Set (Option S)))
  let DR : (shoreContraction G (Finset.univ \ S)).Subgraph :=
    MR.deleteVerts
      ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
          Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S))))
  let L : G.Subgraph := shoreInternalLift (G := G) S DL
  have hLnot :
      g.1 ∉ L.edgeSet := by
    -- An edge internal to the complementary shore cannot lie in the left lifted shore.
    intro hgL
    have hgVert : g.1.out.1 ∈ L.verts :=
      Subgraph.mem_verts_of_mem_edge hgL (Sym2.out_fst_mem _)
    have hgS :
        g.1.out.1 ∈ (S : Set V) := by
      exact shoreInternalLift_verts_subset (G := G) S DL hgVert
    exact ((memInducedEdgeFinsetEndpointsIff
      (G := G) (((Finset.univ \ S : Finset V) : Set V)) g).1 hg).1.2 hgS
  have hEnot :
      g.1 ∉ (G.subgraphOfAdj e.2).edgeSet := by
    -- The glued singleton cut edge is not internal to the complementary shore either.
    intro hgE
    have hge : g = e := by
      apply Subtype.ext
      simpa [SimpleGraph.edgeSet_subgraphOfAdj] using hgE
    have heCompl : e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := by
      simpa using he
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) hg (hge ▸ heCompl)
  calc
    G.subgraphIncidenceVector ℝ (gluedShoreMatching (G := G) S e ML hML MR hMR) g =
        G.subgraphIncidenceVector ℝ (shoreInternalLift (G := G) (Finset.univ \ S) DR) g := by
          -- Once the left lift and the singleton cut vanish, the right deleted lift remains.
          simp [gluedShoreMatching, DL, DR, L, SimpleGraph.subgraphIncidenceVector,
            SimpleGraph.Subgraph.edgeSet_sup, hLnot, hEnot]
    _ = (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ MR f := by
          exact shoreInternalLift_deleteBoundary_incidence_eq_of_memInducedEdgeFinset
            (G := G) (M := MR) hMR hg hf

/-- Helper for Theorem 4.23: on a cut edge, the glued shore matching contributes exactly the
indicator of the chosen glued edge. -/
private lemma gluedShoreMatching_incidenceCut
    {S : Finset V} {e g : G.edgeSet}
    {ML : (shoreContraction G S).Subgraph} (hML : ML.IsPerfectMatching)
    {MR : (shoreContraction G (Finset.univ \ S)).Subgraph} (hMR : MR.IsPerfectMatching)
    (hg : g ∈ δ[G] (S : Set V)) :
    G.subgraphIncidenceVector ℝ (gluedShoreMatching (G := G) S e ML hML MR hMR) g =
      if g = e then 1 else 0 := by
  let DL : (shoreContraction G S).Subgraph :=
    ML.deleteVerts
      ((((hML.1.toEdge ⟨none, hML.2 none⟩ : ML.edgeSet) : Sym2 (Option S)) :
        Set (Option S)))
  let DR : (shoreContraction G (Finset.univ \ S)).Subgraph :=
    MR.deleteVerts
      ((((hMR.1.toEdge ⟨none, hMR.2 none⟩ : MR.edgeSet) :
          Sym2 (Option (Finset.univ \ S))) : Set (Option (Finset.univ \ S))))
  have hLnot :
      g.1 ∉ (shoreInternalLift (G := G) S DL).edgeSet := by
    -- The left deleted lift only contains edges internal to `S`.
    intro hgL
    have hgInd :
        g ∈ E[G] (S : Set V) := by
      rcases (Subgraph.mem_edgeSet.1 hgL) with ⟨hu, hv, _⟩
      exact (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) g).2 ⟨hu, hv⟩
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) hgInd hg
  have hRnot :
      g.1 ∉ (shoreInternalLift (G := G) (Finset.univ \ S) DR).edgeSet := by
    -- The right deleted lift only contains edges internal to the complementary shore.
    intro hgR
    have hgInd :
        g ∈ E[G] (((Finset.univ \ S : Finset V) : Set V)) := by
      rcases (Subgraph.mem_edgeSet.1 hgR) with ⟨hu, hv, _⟩
      exact (memInducedEdgeFinsetEndpointsIff
        (G := G) (((Finset.univ \ S : Finset V) : Set V)) g).2 ⟨hu, hv⟩
    have hgCompl : g ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := by
      simpa using hg
    exact notMemCutEdgeFinsetOfMemInducedEdgeFinset (G := G) hgInd hgCompl
  by_cases hge : g = e
  · subst hge
    -- On the glued edge itself, only the singleton cut piece survives.
    simp [gluedShoreMatching, DL, DR, SimpleGraph.subgraphIncidenceVector,
      SimpleGraph.Subgraph.edgeSet_sup, hLnot, hRnot]
  · have hEnot : g.1 ∉ (G.subgraphOfAdj e.2).edgeSet := by
      intro hgE
      apply hge
      apply Subtype.ext
      simpa [SimpleGraph.edgeSet_subgraphOfAdj] using hgE
    -- Away from the glued edge, all three pieces vanish on the cut.
    simp [gluedShoreMatching, DL, DR, SimpleGraph.subgraphIncidenceVector,
      SimpleGraph.Subgraph.edgeSet_sup, hLnot, hRnot, hEnot, hge]

/-- Helper for Theorem 4.23: once both complementary shore contractions are decomposed into
perfect matchings, one can glue them back along the original cut to obtain a matching
decomposition of `x`. -/
private lemma memMatchingPolytopeOfComplementaryShorePushforwards
    {x : G.edgeSet → ℝ}
    (hxPerfect : x ∈ perfectMatchingConstraintSet G)
    (hx_pos : ∀ e : G.edgeSet, 0 < x e)
    (S : Finset V)
    (hcut : (δ[G] (S : Set V)).sum x = 1)
    (hleft : shorePushforward G S x ∈ perfectMatchingPolytope (shoreContraction G S))
    (hright : shorePushforward G (Finset.univ \ S) x ∈
      perfectMatchingPolytope (shoreContraction G (Finset.univ \ S))) :
    x ∈ matchingPolytope G := by
  -- Expand both contraction decompositions into finite convex combinations of perfect matchings.
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype] at hleft hright
  rcases hleft with ⟨ιL, _, wL, zL, hwL_nonneg, hwL_sum, hzL, hsumL⟩
  rcases hright with ⟨ιR, _, wR, zR, hwR_nonneg, hwR_sum, hzR, hsumR⟩
  have hzL' :
      ∀ i, ∃ M : (shoreContraction G S).Subgraph,
        M.IsPerfectMatching ∧ zL i = (shoreContraction G S).subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hzL i
  have hzR' :
      ∀ j, ∃ M : (shoreContraction G (Finset.univ \ S)).Subgraph,
        M.IsPerfectMatching ∧
          zR j = (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ M := by
    intro j
    simpa using hzR j
  choose ML hMLPerfect hMLVec using hzL'
  choose MR hMRPerfect hMRVec using hzR'
  have hsumL' :
      ∑ i, wL i • (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) =
        shorePushforward G S x := by
    -- Rewrite the left barycenter through the chosen perfect-matching generators.
    calc
      ∑ i, wL i • (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) =
          ∑ i, wL i • zL i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hMLVec i]
      _ = shorePushforward G S x := hsumL
  have hsumR' :
      ∑ j, wR j • (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) =
        shorePushforward G (Finset.univ \ S) x := by
    -- Rewrite the right barycenter through the chosen perfect-matching generators.
    calc
      ∑ j, wR j • (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) =
          ∑ j, wR j • zR j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hMRVec j]
      _ = shorePushforward G (Finset.univ \ S) x := hsumR
  obtain ⟨M0, hM0Perfect⟩ := exists_isPerfectMatching_of_mem_perfectMatchingConstraintSet
    (G := G) hxPerfect
  classical
  let boundaryLeft : ιL → (shoreContraction G S).edgeSet := fun i ↦
    (((hMLPerfect i).1.toEdge ⟨none, (hMLPerfect i).2 none⟩ : (ML i).edgeSet) :
      (shoreContraction G S).edgeSet)
  let boundaryRight : ιR → (shoreContraction G (Finset.univ \ S)).edgeSet := fun j ↦
    (((hMRPerfect j).1.toEdge ⟨none, (hMRPerfect j).2 none⟩ : (MR j).edgeSet) :
      (shoreContraction G (Finset.univ \ S)).edgeSet)
  let compatLeft : ιL → G.edgeSet → ℝ := fun i e ↦
    if he : e ∈ δ[G] (S : Set V) then
      if boundaryLeft i = projectedCutEdge (G := G) S e he then
        wL i / shorePushforward G S x (boundaryLeft i)
      else 0
    else 0
  let compatRight : ιR → G.edgeSet → ℝ := fun j e ↦
    if he : e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) then
      if boundaryRight j = projectedCutEdge (G := G) (Finset.univ \ S) e he then
        wR j / shorePushforward G (Finset.univ \ S) x (boundaryRight j)
      else 0
    else 0
  let μ : G.edgeSet × ιL × ιR → ℝ := fun a ↦
    compatLeft a.2.1 a.1 * x a.1 * compatRight a.2.2 a.1
  have hcutCompl :
      ∀ {e : G.edgeSet}, e ∈ δ[G] (S : Set V) →
        e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := by
    intro e he
    simpa using he
  let z : G.edgeSet × ιL × ιR → G.edgeSet → ℝ := fun a ↦
    if he : a.1 ∈ δ[G] (S : Set V) then
      if hLi : boundaryLeft a.2.1 = projectedCutEdge (G := G) S a.1 he then
        if hRj : boundaryRight a.2.2 =
            projectedCutEdge (G := G) (Finset.univ \ S) a.1 (hcutCompl he) then
          G.subgraphIncidenceVector ℝ
            (gluedShoreMatching (G := G) S a.1 (ML a.2.1) (hMLPerfect a.2.1)
              (MR a.2.2) (hMRPerfect a.2.2))
        else
          G.subgraphIncidenceVector ℝ M0
      else
        G.subgraphIncidenceVector ℝ M0
    else
      G.subgraphIncidenceVector ℝ M0
  have hboundaryLeftNone :
      ∀ i, ((boundaryLeft i : (shoreContraction G S).edgeSet) : Sym2 (Option S)) ∈
        (shoreContraction G S).incidenceFinset none := by
    intro i
    -- The distinguished boundary edge of a contracted perfect matching is incident to `none`.
    simpa [boundaryLeft, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
      using (hMLPerfect i).1.mem_coe_toEdge ((hMLPerfect i).2 none)
  have hboundaryRightNone :
      ∀ j,
        ((boundaryRight j : (shoreContraction G (Finset.univ \ S)).edgeSet) :
          Sym2 (Option (Finset.univ \ S))) ∈
          (shoreContraction G (Finset.univ \ S)).incidenceFinset none := by
    intro j
    -- The complementary distinguished boundary edge is also incident to its collapsed vertex.
    simpa [boundaryRight, SimpleGraph.mem_incidenceFinset,
      SimpleGraph.edge_mem_incidenceSet_iff]
      using (hMRPerfect j).1.mem_coe_toEdge ((hMRPerfect j).2 none)
  have hcompatLeftFiber :
      ∀ e : G.edgeSet, ∑ i, compatLeft i e = if e ∈ δ[G] (S : Set V) then 1 else 0 := by
    intro e
    by_cases he : e ∈ δ[G] (S : Set V)
    · have hfiber :
          ∑ i, (if boundaryLeft i = projectedCutEdge (G := G) S e he
            then wL i / shorePushforward G S x (projectedCutEdge (G := G) S e he)
            else 0) = 1 := by
        simpa [boundaryLeft] using
          boundaryFiberWeightSum_eq_one (G := G) (S := S) (x := x) (ι := ιL) hx_pos
            wL ML hMLPerfect hsumL' (e := e) he
            (f := projectedCutEdge (G := G) S e he) rfl
      calc
        ∑ i, compatLeft i e =
            ∑ i, (if boundaryLeft i = projectedCutEdge (G := G) S e he
              then wL i / shorePushforward G S x (projectedCutEdge (G := G) S e he)
              else 0) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hEq : boundaryLeft i = projectedCutEdge (G := G) S e he
                · simp [compatLeft, he, hEq]
                · simp [compatLeft, he, hEq]
        _ = 1 := hfiber
        _ = if e ∈ δ[G] (S : Set V) then 1 else 0 := by simp [he]
    · simp [compatLeft, he]
  have hcompatRightFiber :
      ∀ e : G.edgeSet, ∑ j, compatRight j e = if e ∈ δ[G] (S : Set V) then 1 else 0 := by
    intro e
    by_cases he : e ∈ δ[G] (S : Set V)
    · have heR :
          e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := hcutCompl he
      have hfiber :
          ∑ j, (if boundaryRight j =
              projectedCutEdge (G := G) (Finset.univ \ S) e heR
            then wR j /
              shorePushforward G (Finset.univ \ S) x (projectedCutEdge (G := G)
                (Finset.univ \ S) e heR)
            else 0) = 1 := by
        simpa [boundaryRight] using
          boundaryFiberWeightSum_eq_one (G := G) (S := Finset.univ \ S) (x := x)
            (ι := ιR) hx_pos wR MR hMRPerfect hsumR' (e := e) heR
            (f := projectedCutEdge (G := G) (Finset.univ \ S) e heR) rfl
      calc
        ∑ j, compatRight j e =
            ∑ j, (if boundaryRight j =
                projectedCutEdge (G := G) (Finset.univ \ S) e heR
              then wR j / shorePushforward G (Finset.univ \ S) x (projectedCutEdge (G := G)
                (Finset.univ \ S) e heR)
              else 0) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases hEq : boundaryRight j =
                    projectedCutEdge (G := G) (Finset.univ \ S) e heR
                · simp [compatRight, heR, hEq]
                · simp [compatRight, heR, hEq]
        _ = 1 := hfiber
        _ = if e ∈ δ[G] (S : Set V) then 1 else 0 := by simp [he]
    · have heR :
          e ∉ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := by
        simpa using he
      simp [compatRight, heR, he]
  have hcompatLeftTotal : ∀ i, ∑ e : G.edgeSet, x e * compatLeft i e = wL i := by
    intro i
    have hpush :
        shorePushforward G S x (boundaryLeft i) =
          ∑ e : G.edgeSet,
            if he : e ∈ δ[G] (S : Set V) then
              if projectedCutEdge (G := G) S e he = boundaryLeft i then x e else 0
            else 0 :=
      shorePushforward_apply_of_memIncidenceNone (G := G) (S := S) (x := x)
        (f := boundaryLeft i) (hboundaryLeftNone i)
    have hpos :
        0 < shorePushforward G S x (boundaryLeft i) :=
      shorePushforward_pos_of_eq_projectedEdge (G := G) (S := S) (x := x) hx_pos
        (e := shoreOriginalEdge G S (boundaryLeft i)) (f := boundaryLeft i)
        (shoreOriginalEdge_map (G := G) S (boundaryLeft i))
    calc
      ∑ e : G.edgeSet, x e * compatLeft i e =
          (wL i / shorePushforward G S x (boundaryLeft i)) *
            ∑ e : G.edgeSet,
              if he : e ∈ δ[G] (S : Set V) then
                if projectedCutEdge (G := G) S e he = boundaryLeft i then x e else 0
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro e he
                by_cases heCut : e ∈ δ[G] (S : Set V)
                · by_cases hEq : projectedCutEdge (G := G) S e heCut = boundaryLeft i
                  · simp [compatLeft, heCut, hEq]
                    ring
                  · simp [compatLeft, heCut, hEq]
                · simp [compatLeft, heCut]
      _ = (wL i / shorePushforward G S x (boundaryLeft i)) *
            shorePushforward G S x (boundaryLeft i) := by
              rw [hpush]
      _ = wL i * ((shorePushforward G S x (boundaryLeft i)) /
            (shorePushforward G S x (boundaryLeft i))) := by
              ring
      _ = wL i := by
            rw [div_self (ne_of_gt hpos), mul_one]
  have hcompatRightTotal :
      ∀ j, ∑ e : G.edgeSet, x e * compatRight j e = wR j := by
    intro j
    have hpush :
        shorePushforward G (Finset.univ \ S) x (boundaryRight j) =
          ∑ e : G.edgeSet,
            if he : e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) then
              if projectedCutEdge (G := G) (Finset.univ \ S) e he = boundaryRight j
              then x e else 0
            else 0 :=
      shorePushforward_apply_of_memIncidenceNone (G := G) (S := Finset.univ \ S) (x := x)
        (f := boundaryRight j) (hboundaryRightNone j)
    have hpos :
        0 < shorePushforward G (Finset.univ \ S) x (boundaryRight j) :=
      shorePushforward_pos_of_eq_projectedEdge (G := G) (S := Finset.univ \ S) (x := x) hx_pos
        (e := shoreOriginalEdge G (Finset.univ \ S) (boundaryRight j)) (f := boundaryRight j)
        (shoreOriginalEdge_map (G := G) (Finset.univ \ S) (boundaryRight j))
    calc
      ∑ e : G.edgeSet, x e * compatRight j e =
          (wR j / shorePushforward G (Finset.univ \ S) x (boundaryRight j)) *
            ∑ e : G.edgeSet,
              if he : e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V)) then
                if projectedCutEdge (G := G) (Finset.univ \ S) e he = boundaryRight j
                then x e else 0
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro e he
                by_cases heCut : e ∈ δ[G] (((Finset.univ \ S : Finset V) : Set V))
                · by_cases hEq :
                    projectedCutEdge (G := G) (Finset.univ \ S) e heCut = boundaryRight j
                  · simp [compatRight, heCut, hEq]
                    ring
                  · simp [compatRight, heCut, hEq]
                · simp [compatRight, heCut]
      _ = (wR j / shorePushforward G (Finset.univ \ S) x (boundaryRight j)) *
            shorePushforward G (Finset.univ \ S) x (boundaryRight j) := by
              rw [hpush]
      _ = wR j * ((shorePushforward G (Finset.univ \ S) x (boundaryRight j)) /
            (shorePushforward G (Finset.univ \ S) x (boundaryRight j))) := by
              ring
      _ = wR j := by
            rw [div_self (ne_of_gt hpos), mul_one]
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype]
  refine ⟨G.edgeSet × ιL × ιR, inferInstance, μ, z, ?_, ?_, ?_, ?_⟩
  · intro a
    rcases a with ⟨e, i, j⟩
    by_cases he : e ∈ δ[G] (S : Set V)
    · by_cases hLi : boundaryLeft i = projectedCutEdge (G := G) S e he
      · by_cases hRj : boundaryRight j =
          projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)
        · have hposL :
            0 < shorePushforward G S x (boundaryLeft i) :=
          shorePushforward_pos_of_eq_projectedEdge (G := G) (S := S) (x := x) hx_pos
            (e := e) (f := boundaryLeft i) (by
              simpa [hLi] using
                (projectedCutEdge_val (G := G) (S := S) (e := e) he).symm)
          have hposR :
              0 < shorePushforward G (Finset.univ \ S) x (boundaryRight j) :=
            shorePushforward_pos_of_eq_projectedEdge (G := G) (S := Finset.univ \ S) (x := x)
              hx_pos (e := e) (f := boundaryRight j) (by
                simpa [hRj] using
                  (projectedCutEdge_val (G := G) (S := Finset.univ \ S) (e := e)
                    (hcutCompl he)).symm)
          have hleft_nonneg : 0 ≤ compatLeft i e := by
            simp [compatLeft, he, hLi, hposL.le, hwL_nonneg i]
          have hright_nonneg : 0 ≤ compatRight j e := by
            simp [compatRight, hcutCompl he, hRj, hposR.le, hwR_nonneg j]
          exact mul_nonneg (mul_nonneg hleft_nonneg (le_of_lt (hx_pos e))) hright_nonneg
        · simp [μ, compatLeft, compatRight, he, hLi, hRj]
      · simp [μ, compatLeft, compatRight, he, hLi]
    · simp [μ, compatLeft, compatRight, he]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR, μ (e, i, j) =
          ∑ e : G.edgeSet, x e * ((∑ i : ιL, compatLeft i e) * (∑ j : ιR, compatRight j e)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            calc
              ∑ i : ιL, ∑ j : ιR, μ (e, i, j) =
                  ∑ i : ιL, ∑ j : ιR, compatLeft i e * x e * compatRight j e := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    simp [μ]
              _ = x e * ((∑ i : ιL, compatLeft i e) * (∑ j : ιR, compatRight j e)) := by
                    calc
                      ∑ i : ιL, ∑ j : ιR, compatLeft i e * x e * compatRight j e =
                          ∑ i : ιL, x e * compatLeft i e * ∑ j : ιR, compatRight j e := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            rw [← Finset.mul_sum]
                            refine Finset.sum_congr rfl ?_
                            intro j hj
                            ring
                      _ = x e * ∑ i : ιL, compatLeft i e * ∑ j : ιR, compatRight j e := by
                            rw [← Finset.mul_sum]
                      _ = x e * ((∑ i : ιL, compatLeft i e) * (∑ j : ιR, compatRight j e)) := by
                            congr 1
                            rw [Finset.sum_mul]
      _ = ∑ e : G.edgeSet, if e ∈ δ[G] (S : Set V) then x e else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases heCut : e ∈ δ[G] (S : Set V)
            · simp [hcompatLeftFiber, hcompatRightFiber, heCut]
            · simp [hcompatLeftFiber, hcompatRightFiber, heCut]
      _ = (δ[G] (S : Set V)).sum x := by
            exact (edgeSetSumIteEqSumFilter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ δ[G] (S : Set V)) x).symm
      _ = 1 := hcut
  · intro a
    rcases a with ⟨e, i, j⟩
    by_cases he : e ∈ δ[G] (S : Set V)
    · by_cases hLi : boundaryLeft i = projectedCutEdge (G := G) S e he
      · by_cases hRj : boundaryRight j =
          projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)
        · have hfL :
            (boundaryLeft i).1 = Sym2.map (shoreProjection S) e.1 := by
            calc
              (boundaryLeft i).1 = (projectedCutEdge (G := G) S e he).1 := by
                exact congrArg Subtype.val hLi
              _ = Sym2.map (shoreProjection S) e.1 := by
                simp [projectedCutEdge]
          have hfR :
            (boundaryRight j).1 =
              Sym2.map (shoreProjection (Finset.univ \ S)) e.1 := by
            calc
              (boundaryRight j).1 =
                  (projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)).1 := by
                    exact congrArg Subtype.val hRj
              _ = Sym2.map (shoreProjection (Finset.univ \ S)) e.1 := by
                    simp [projectedCutEdge]
          refine ⟨gluedShoreMatching (G := G) S e (ML i) (hMLPerfect i) (MR j) (hMRPerfect j),
            gluedShoreMatching_isMatching (G := G) (hML := hMLPerfect i) (hMR := hMRPerfect j)
              he hfL hfR, ?_⟩
          -- In the compatible branch, `z` is exactly the glued matching incidence vector.
          simp [z, he, hLi, hRj]
        · exact ⟨M0, hM0Perfect.1, by simp [z, he, hLi, hRj]⟩
      · exact ⟨M0, hM0Perfect.1, by simp [z, he, hLi]⟩
    · exact ⟨M0, hM0Perfect.1, by simp [z, he]⟩
  · ext g
    by_cases hgLeft₁ : g.1.out.1 ∈ (S : Set V)
    · by_cases hgLeft₂ : g.1.out.2 ∈ (S : Set V)
      · have hgLeft : g ∈ E[G] (S : Set V) :=
          (memInducedEdgeFinsetEndpointsIff (G := G) (S : Set V) g).2 ⟨hgLeft₁, hgLeft₂⟩
        let fg : (shoreContraction G S).edgeSet := projectedInducedEdge (G := G) S g hgLeft
        have hzCoord :
            ∀ e : G.edgeSet, ∀ i : ιL, ∀ j : ιR,
              μ (e, i, j) * z (e, i, j) g =
                μ (e, i, j) *
                  (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
          intro e i j
          by_cases he : e ∈ δ[G] (S : Set V)
          · by_cases hLi : boundaryLeft i = projectedCutEdge (G := G) S e he
            · by_cases hRj : boundaryRight j =
                projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)
              · have hglue :
                  G.subgraphIncidenceVector ℝ
                      (gluedShoreMatching (G := G) S e (ML i) (hMLPerfect i)
                        (MR j) (hMRPerfect j)) g =
                    (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
                  exact gluedShoreMatching_incidenceLeft (G := G) (hML := hMLPerfect i)
                    (hMR := hMRPerfect j) he hgLeft (by
                      simpa [fg] using
                        (projectedInducedEdge_val (G := G) (S := S) (e := g) hgLeft).symm)
                simp [z, he, hLi, hRj, μ, hglue]
              · simp [z, he, hLi, hRj, μ]
            · simp [z, he, hLi, μ]
          · simp [z, he, μ]
        have hfg :
            shorePushforward G S x fg = x g := by
          exact shorePushforward_apply_of_mem_inducedEdgeFinset (G := G) (x := x) hgLeft
            (by
              simpa [fg] using
                (projectedInducedEdge_val (G := G) (S := S) (e := g) hgLeft).symm)
        -- On internal left edges, the glued barycenter collapses to the left contracted barycenter.
        calc
          ∑ a : G.edgeSet × ιL × ιR, μ a * z a g =
              ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR, μ (e, i, j) * z (e, i, j) g := by
                rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
          _ = ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR,
                μ (e, i, j) * (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  exact hzCoord e i j
          _ = ∑ e : G.edgeSet, ∑ i : ιL,
                compatLeft i e * x e *
                  (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg *
                    (∑ j : ιR, compatRight j e) := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [← Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simp [μ]
                  ring
          _ = ∑ e : G.edgeSet, ∑ i : ιL,
                compatLeft i e * x e *
                  (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  by_cases heCut : e ∈ δ[G] (S : Set V)
                  · simp [hcompatRightFiber, heCut]
                  · simp [compatLeft, hcompatRightFiber, heCut]
          _ = ∑ i : ιL, ∑ e : G.edgeSet,
                compatLeft i e * x e *
                  (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
                  rw [Finset.sum_comm]
          _ = ∑ i : ιL,
                (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg *
                  (∑ e : G.edgeSet, x e * compatLeft i e) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  rw [← Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  ring
          _ = ∑ i : ιL,
                (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg * wL i := by
                  simp [hcompatLeftTotal]
          _ = ∑ i : ιL,
                wL i * (shoreContraction G S).subgraphIncidenceVector ℝ (ML i) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  ring
          _ = shorePushforward G S x fg := by
                exact weightedSumApply (G := shoreContraction G S) wL
                  (fun i ↦ (shoreContraction G S).subgraphIncidenceVector ℝ (ML i)) hsumL' fg
          _ = x g := hfg
      · have hgCut :
          g ∈ δ[G] (S : Set V) :=
          (memCutEdgeFinsetEndpointsIff (G := G) (S : Set V) g).2 (Or.inl ⟨hgLeft₁, hgLeft₂⟩)
        have hzCoord :
            ∀ e : G.edgeSet, ∀ i : ιL, ∀ j : ιR,
              μ (e, i, j) * z (e, i, j) g = μ (e, i, j) * (if g = e then 1 else 0) := by
          intro e i j
          by_cases he : e ∈ δ[G] (S : Set V)
          · by_cases hLi : boundaryLeft i = projectedCutEdge (G := G) S e he
            · by_cases hRj : boundaryRight j =
                projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)
              · have hglue :
                  G.subgraphIncidenceVector ℝ
                      (gluedShoreMatching (G := G) S e (ML i) (hMLPerfect i)
                        (MR j) (hMRPerfect j)) g =
                    if g = e then 1 else 0 := by
                  exact gluedShoreMatching_incidenceCut (G := G) (hML := hMLPerfect i)
                    (hMR := hMRPerfect j) hgCut
                simp [z, he, hLi, hRj, μ, hglue]
              · simp [z, he, hLi, hRj, μ]
            · simp [z, he, hLi, μ]
          · simp [z, he, μ]
        -- On a cut edge, only the slice indexed by that same original cut edge survives.
        calc
          ∑ a : G.edgeSet × ιL × ιR, μ a * z a g =
              ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR, μ (e, i, j) * z (e, i, j) g := by
                rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
          _ = ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR, μ (e, i, j) * (if g = e then 1 else 0) := by
                refine Finset.sum_congr rfl ?_
                intro e he
                refine Finset.sum_congr rfl ?_
                intro i hi
                refine Finset.sum_congr rfl ?_
                intro j hj
                exact hzCoord e i j
          _ = ∑ e : G.edgeSet,
                if g = e then x e * (∑ i : ιL, compatLeft i e) * (∑ j : ιR, compatRight j e)
                else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  by_cases hge : g = e
                  · subst hge
                    calc
                      ∑ i : ιL, ∑ j : ιR, μ (g, i, j) * (if g = g then 1 else 0) =
                          ∑ i : ιL, ∑ j : ιR, μ (g, i, j) := by simp
                      _ = x g * ((∑ i : ιL, compatLeft i g) * (∑ j : ιR, compatRight j g)) := by
                            calc
                              ∑ i : ιL, ∑ j : ιR, μ (g, i, j) =
                                  ∑ i : ιL, ∑ j : ιR, compatLeft i g * x g * compatRight j g := by
                                    refine Finset.sum_congr rfl ?_
                                    intro i hi
                                    refine Finset.sum_congr rfl ?_
                                    intro j hj
                                    simp [μ]
                              _ = x g * ((∑ i : ιL, compatLeft i g) * (∑ j : ιR, compatRight j g)) := by
                                    calc
                                      ∑ i : ιL, ∑ j : ιR, compatLeft i g * x g * compatRight j g =
                                          ∑ i : ιL, x g * compatLeft i g * ∑ j : ιR, compatRight j g := by
                                            refine Finset.sum_congr rfl ?_
                                            intro i hi
                                            rw [← Finset.mul_sum]
                                            refine Finset.sum_congr rfl ?_
                                            intro j hj
                                            ring
                                      _ = x g * ∑ i : ιL, compatLeft i g * ∑ j : ιR, compatRight j g := by
                                            rw [← Finset.mul_sum]
                                      _ = x g * ((∑ i : ιL, compatLeft i g) * (∑ j : ιR, compatRight j g)) := by
                                            congr 1
                                            rw [Finset.sum_mul]
                    simp
                  · simp [hge]
          _ = x g * (∑ i : ιL, compatLeft i g) * (∑ j : ιR, compatRight j g) := by
                refine Finset.sum_eq_single g ?_ ?_
                · simp
                · intro e he hne
                  simp [hne]
                · simp
          _ = x g := by
                simp [hcompatLeftFiber, hcompatRightFiber, hgCut]
      · have hgRight :
          g ∈ E[G] (((Finset.univ \ S : Finset V) : Set V)) :=
          (memInducedEdgeFinsetEndpointsIff
            (G := G) (((Finset.univ \ S : Finset V) : Set V)) g).2
            ⟨by simpa using hgLeft₁, by simpa using hgLeft₂⟩
        let fg : (shoreContraction G (Finset.univ \ S)).edgeSet :=
          projectedInducedEdge (G := G) (Finset.univ \ S) g hgRight
        have hzCoord :
            ∀ e : G.edgeSet, ∀ i : ιL, ∀ j : ιR,
              μ (e, i, j) * z (e, i, j) g =
                μ (e, i, j) *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
          intro e i j
          by_cases he : e ∈ δ[G] (S : Set V)
          · by_cases hLi : boundaryLeft i = projectedCutEdge (G := G) S e he
            · by_cases hRj : boundaryRight j =
                projectedCutEdge (G := G) (Finset.univ \ S) e (hcutCompl he)
              · have hglue :
                  G.subgraphIncidenceVector ℝ
                      (gluedShoreMatching (G := G) S e (ML i) (hMLPerfect i)
                        (MR j) (hMRPerfect j)) g =
                    (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
                  exact gluedShoreMatching_incidenceRight (G := G) (hML := hMLPerfect i)
                    (hMR := hMRPerfect j) he hgRight (by
                      simpa [fg] using
                        (projectedInducedEdge_val (G := G) (S := Finset.univ \ S) (e := g)
                          hgRight).symm)
                simp [z, he, hLi, hRj, μ, hglue]
              · simp [z, he, hLi, hRj, μ]
            · simp [z, he, hLi, μ]
          · simp [z, he, μ]
        have hfg :
            shorePushforward G (Finset.univ \ S) x fg = x g := by
          exact shorePushforward_apply_of_mem_inducedEdgeFinset (G := G) (x := x) hgRight
            (by
              simpa [fg] using
                (projectedInducedEdge_val (G := G) (S := Finset.univ \ S) (e := g) hgRight).symm)
        -- On internal right edges, the barycenter collapses to the right contracted barycenter.
        calc
          ∑ a : G.edgeSet × ιL × ιR, μ a * z a g =
              ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR, μ (e, i, j) * z (e, i, j) g := by
                rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
          _ = ∑ e : G.edgeSet, ∑ i : ιL, ∑ j : ιR,
                μ (e, i, j) *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  exact hzCoord e i j
          _ = ∑ e : G.edgeSet, ∑ j : ιR,
                compatRight j e * x e *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg *
                    (∑ i : ιL, compatLeft i e) := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [← Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  simp [μ]
                  ring
          _ = ∑ e : G.edgeSet, ∑ j : ιR,
                compatRight j e * x e *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  by_cases heCut : e ∈ δ[G] (S : Set V)
                  · simp [hcompatLeftFiber, heCut]
                  · have heCutR :
                      e ∉ δ[G] (((Finset.univ \ S : Finset V) : Set V)) := by simpa using heCut
                    simp [compatRight, hcompatLeftFiber, heCut, heCutR]
          _ = ∑ j : ιR, ∑ e : G.edgeSet,
                compatRight j e * x e *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
                  rw [Finset.sum_comm]
          _ = ∑ j : ιR,
                (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg *
                  (∑ e : G.edgeSet, x e * compatRight j e) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [← Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro e he
                  ring
          _ = ∑ j : ιR,
                (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg * wR j := by
                  simp [hcompatRightTotal]
          _ = ∑ j : ιR,
                wR j *
                  (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j) fg := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
          _ = shorePushforward G (Finset.univ \ S) x fg := by
                exact weightedSumApply (G := shoreContraction G (Finset.univ \ S)) wR
                  (fun j ↦ (shoreContraction G (Finset.univ \ S)).subgraphIncidenceVector ℝ (MR j))
                  hsumR' fg
          _ = x g := hfg

/-- Helper for Theorem 4.23: a positive nonintegral extreme point of the perfect-matching
constraint set belongs to the matching polytope, assuming the perfect theorem for smaller
graphs. -/
private lemma memMatchingPolytopeOfPositiveNonintegralExtremePoint
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_pos : ∀ e : G.edgeSet, 0 < x e) :
    x ∈ matchingPolytope G := by
  have hxPerfect : x ∈ perfectMatchingConstraintSet G := extremePoints_subset hx
  have hxExtremeMatch :
      x ∈ (matchingConstraintSet G).extremePoints ℝ :=
    mem_extremePoints_matchingConstraintSet_of_mem_extremePoints_perfectMatchingConstraintSet
      (G := G) hx
  have hV : Even (Fintype.card V) :=
    even_card_of_memPerfectMatchingConstraintSet (G := G) hxPerfect
  -- Route correction: move back to the theorem-local contraction route instead of a global
  -- matching-constraint bridge. First extract a proper tight odd shore from the positive branch.
  rcases existsProperTightOddShoreOfPositiveNonintegralExtremePoint
      (G := G) hxPerfect hxExtremeMatch hx_not_int hx_pos with
    ⟨S, hSodd, hSproper, hScompl, hScut⟩
  -- The smaller-graph induction hypothesis solves both complementary contractions of that shore.
  have hpush :
      shorePushforward G S x ∈ perfectMatchingPolytope (shoreContraction G S) ∧
        shorePushforward G (Finset.univ \ S) x ∈
          perfectMatchingPolytope (shoreContraction G (Finset.univ \ S)) :=
    complementaryShorePushforwards_memPerfectMatchingPolytope
      (G := G) hsmaller hxPerfect hV S hSodd hSproper hScompl hScut
  -- The remaining frontier is the gluing argument that turns the two contraction decompositions
  -- back into a matching decomposition of the original point `x`.
  exact memMatchingPolytopeOfComplementaryShorePushforwards
    (G := G) hxPerfect hx_pos S hScut hpush.1 hpush.2

/-- Helper for Theorem 4.23: the matching-polytope theorem upgrades feasible perfect-matching
constraint points to points of `matchingPolytope G`. -/
private lemma mem_matchingPolytope_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer_of_smaller
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ)
    (hx_not_int : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ matchingPolytope G := by
  have hxPerfect : x ∈ perfectMatchingConstraintSet G := extremePoints_subset hx
  by_cases hzero : ∃ e : G.edgeSet, x e = 0
  · rcases hzero with ⟨e, he⟩
    -- A zero coordinate is removed by the proved deletion interface and the resulting perfect
    -- decomposition is also a matching decomposition in `G`.
    exact perfectMatchingPolytope_subset_matchingPolytope (G := G) <|
      memPerfectMatchingPolytopeOfZeroCoordinate (G := G) hsmaller hxPerfect e he
  · have hx_pos : ∀ e : G.edgeSet, 0 < x e := by
      rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hxPerfect with
        ⟨hx_nonneg, -, -⟩
      intro e
      exact lt_of_le_of_ne (hx_nonneg e) fun h ↦ hzero ⟨e, h.symm⟩
    -- With all coordinates positive, only the tight-odd-set contraction/perturbation branch
    -- remains.
    exact memMatchingPolytopeOfPositiveNonintegralExtremePoint
      (G := G) hsmaller hx hx_not_int hx_pos

/-- Helper for Theorem 4.23: every extreme point of `perfectMatchingConstraintSet G` is one of the
perfect-matching generators. -/
private lemma exists_isPerfectMatching_of_mem_extremePoints_perfectMatchingConstraintSet_of_smaller
    (hsmaller :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet < Fintype.card V + Fintype.card G.edgeSet →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H)
    {x : G.edgeSet → ℝ} (hx : x ∈ (perfectMatchingConstraintSet G).extremePoints ℝ) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  by_cases hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)
  · -- Integer extreme points are reconstructed directly from their `0/1` support.
    exact integerPoint_eq_subgraphIncidenceVector_of_mem_perfectMatchingConstraintSet
      (G := G) (extremePoints_subset hx) hx_int
  · have hxMatch :
        x ∈ matchingPolytope G :=
      mem_matchingPolytope_of_mem_extremePoints_perfectMatchingConstraintSet_of_not_integer_of_smaller
        (G := G) hsmaller hx hx_int
    have hxPerfect : x ∈ perfectMatchingConstraintSet G := extremePoints_subset hx
    have hxPerfectPoly : x ∈ perfectMatchingPolytope G :=
      perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
        (G := G) hxMatch hxPerfect
    have hxExtremePerfect :
        x ∈ (perfectMatchingPolytope G).extremePoints ℝ := by
      -- Extremality in the larger perfect-constraint owner restricts to the smaller polytope.
      exact inter_extremePoints_subset_extremePoints_of_subset
        (perfectMatchingPolytope_subset_perfectMatchingConstraintSet (G := G))
        ⟨hxPerfectPoly, hx⟩
    rw [SimpleGraph.perfectMatchingPolytope] at hxExtremePerfect
    have hxGenerator :
        x ∈ {y : G.edgeSet → ℝ |
          ∃ M : G.Subgraph, M.IsPerfectMatching ∧ y = G.subgraphIncidenceVector ℝ M} :=
      extremePoints_convexHull_subset hxExtremePerfect
    exact hxGenerator

/-- Helper for Theorem 4.23: the perfect-matching constraint set is compact. -/
private lemma perfectMatchingConstraintSet_isCompact :
    IsCompact (perfectMatchingConstraintSet G) := by
  have hclosed : IsClosed (perfectMatchingConstraintSet G) := by
    have hrepr :
        perfectMatchingConstraintSet G =
          ((⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) ∩
              ⋂ v : V,
                {x : G.edgeSet → ℝ |
                  (Finset.univ.filter
                    fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1}) ∩
            ⋂ S : Set V, {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} := by
      ext x
      simp [SimpleGraph.mem_perfectMatchingConstraintSet_iff, and_assoc]
    rw [hrepr]
    have hcoordClosed :
        IsClosed (⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) := by
      refine isClosed_iInter fun e : G.edgeSet ↦ ?_
      -- Each coordinate nonnegativity constraint is a closed halfspace.
      simpa using isClosed_le continuous_const
        (continuous_apply e : Continuous fun x : G.edgeSet → ℝ ↦ x e)
    have hdegClosed :
        IsClosed (⋂ v : V,
          {x : G.edgeSet → ℝ |
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1}) := by
      refine isClosed_iInter fun v : V ↦ ?_
      let incidenceMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x ↦
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x
          map_add' := by
            intro x y
            simp [Finset.sum_add_distrib]
          map_smul' := by
            intro a x
            simp [smul_eq_mul, Finset.mul_sum] }
      -- Each degree equation cuts out a closed affine hyperplane.
      change IsClosed (incidenceMap ⁻¹' ({1} : Set ℝ))
      exact isClosed_singleton.preimage incidenceMap.continuous_of_finiteDimensional
    have hcutClosed :
        IsClosed (⋂ S : Set V, {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x}) := by
      refine isClosed_iInter fun S : Set V ↦ ?_
      by_cases hS : Odd S.ncard
      · let cutMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
          { toFun := fun x ↦ (δ[G] S).sum x
            map_add' := by
              intro x y
              simp [Finset.sum_add_distrib]
            map_smul' := by
              intro a x
              simp [smul_eq_mul, Finset.mul_sum] }
        have hEq :
            {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} =
              {x : G.edgeSet → ℝ | 1 ≤ (δ[G] S).sum x} := by
          ext x
          simp [hS]
        rw [hEq]
        -- Each odd-cut inequality is a closed halfspace.
        change IsClosed (cutMap ⁻¹' Set.Ici (1 : ℝ))
        exact isClosed_Ici.preimage cutMap.continuous_of_finiteDimensional
      · have hEq :
            {x : G.edgeSet → ℝ | Odd S.ncard → 1 ≤ (δ[G] S).sum x} = Set.univ := by
          ext x
          simp [hS]
        rw [hEq]
        exact isClosed_univ
    simpa [Set.inter_assoc] using hcoordClosed.inter (hdegClosed.inter hcutClosed)
  have hsubset_cube : perfectMatchingConstraintSet G ⊆ Set.Icc (0 : G.edgeSet → ℝ) 1 := by
    intro x hx
    rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
      ⟨hx_nonneg, -, -⟩
    refine ⟨hx_nonneg, ?_⟩
    intro e
    exact edgeCoordinateLeOneOfMemPerfectMatchingConstraintSet (G := G) hx e
  -- The feasible region is a closed subset of the compact edge-coordinate cube.
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hsubset_cube

/-- Helper for Theorem 4.23: the perfect matching polytope is compact because it is the convex
hull of finitely many perfect-matching generators. -/
private lemma perfectMatchingPolytope_isCompact :
    IsCompact (perfectMatchingPolytope G) := by
  let perfectGenerators : Set (G.edgeSet → ℝ) :=
    Set.range fun M : {M : G.Subgraph // M.IsPerfectMatching} ↦
      G.subgraphIncidenceVector ℝ M.1
  have hgenerators :
      {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M} =
        perfectGenerators := by
    ext x
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨⟨M, hM⟩, rfl⟩
    · rintro ⟨M, rfl⟩
      exact ⟨M.1, M.2, rfl⟩
  have hfinite : perfectGenerators.Finite := by
    -- The subtype of perfect matchings is finite, so its incidence-vector image is finite.
    exact Set.finite_range _
  -- Rewrite the polytope as a convex hull of a finite family of generators.
  rw [SimpleGraph.perfectMatchingPolytope, hgenerators]
  simpa [perfectGenerators] using hfinite.isCompact_convexHull ℝ

/-- Helper for Theorem 4.23: the reverse inclusion is best organized as strong induction on
`|V| + |E|`, so smaller contractions can call the theorem itself instead of re-proving a closed
world bridge. -/
private theorem perfectMatchingConstraintSet_subset_perfectMatchingPolytope_byCard :
    ∀ n : ℕ,
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        Fintype.card W + Fintype.card H.edgeSet = n →
          perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro W _ H hcard x hx
  let _ : DecidableEq W := Classical.decEq W
  let _ : DecidableRel H.Adj := Classical.decRel H.Adj
  have hsmaller :
      ∀ {W' : Type u} [Fintype W'] (H' : SimpleGraph W'),
        Fintype.card W' + Fintype.card H'.edgeSet < Fintype.card W + Fintype.card H.edgeSet →
          perfectMatchingConstraintSet H' ⊆ perfectMatchingPolytope H' := by
    intro W' _ H' hlt
    let _ : DecidableEq W' := Classical.decEq W'
    let _ : DecidableRel H'.Adj := Classical.decRel H'.Adj
    have hlt' : Fintype.card W' + Fintype.card H'.edgeSet < n := by
      simpa [← hcard] using hlt
    exact ih (Fintype.card W' + Fintype.card H'.edgeSet) hlt' H' rfl
  have hclosure :
      closure (convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ)) =
        perfectMatchingConstraintSet H := by
    exact closure_convexHull_extremePoints
      (perfectMatchingConstraintSet_isCompact (G := H))
      (convexPerfectMatchingConstraintSet (G := H))
  have hxClosure :
      x ∈ closure (convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ)) := by
    -- Krein-Milman rewrites the compact convex owner as the closure of the convex hull of its
    -- extreme points.
    simpa [hclosure] using hx
  have hExtremeSubset :
      (perfectMatchingConstraintSet H).extremePoints ℝ ⊆ perfectMatchingPolytope H := by
    intro y hy
    -- Route correction: classify extreme points using the smaller-graph inclusion owner, rather
    -- than asking one closed-world bridge to synthesize the whole recursion.
    rcases exists_isPerfectMatching_of_mem_extremePoints_perfectMatchingConstraintSet_of_smaller
        (G := H) hsmaller hy with ⟨M, hM, rfl⟩
    rw [SimpleGraph.perfectMatchingPolytope]
    exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩
  have hHullSubset :
      convexHull ℝ ((perfectMatchingConstraintSet H).extremePoints ℝ) ⊆ perfectMatchingPolytope H := by
    -- The convex hull stays inside the perfect matching polytope because the latter is convex.
    refine convexHull_min hExtremeSubset ?_
    rw [SimpleGraph.perfectMatchingPolytope]
    exact convex_convexHull ℝ _
  have hxClosurePerfect : x ∈ closure (perfectMatchingPolytope H) := by
    -- Once every extreme point is a perfect-matching generator, the same holds for their convex
    -- hull and hence for its closure.
    exact (closure_mono hHullSubset) hxClosure
  -- The perfect matching polytope is compact, hence closed, so the closure can be removed.
  simpa [(perfectMatchingPolytope_isCompact (G := H)).isClosed.closure_eq] using hxClosurePerfect

/-- Helper for Theorem 4.23: the reverse inclusion is the specialization of the strong-induction
owner to the current graph `G`. -/
lemma perfectMatchingConstraintSet_subset_perfectMatchingPolytope :
    perfectMatchingConstraintSet G ⊆ perfectMatchingPolytope G := by
  -- Route correction: the theorem-level induction owner now carries the smaller-graph calls.
  exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope_byCard
    (n := Fintype.card V + Fintype.card G.edgeSet) (H := G) rfl

/-- Theorem 4.23 (Perfect Matching Polytope Theorem). The perfect matching polytope of a finite
graph `G` is exactly the set of edge-vectors that are nonnegative and satisfy the degree
equations and odd-cut inequalities. -/
theorem perfectMatchingPolytope_eq_perfectMatchingConstraintSet :
    perfectMatchingPolytope G = perfectMatchingConstraintSet G := by
  refine le_antisymm ?_ ?_
  · -- The forward inclusion is the generator-feasibility half of the theorem.
    exact perfectMatchingPolytope_subset_perfectMatchingConstraintSet (G := G)
  · -- Route correction: the reverse inclusion is not reduced by unfolding; it needs the native
    -- extreme-point bridge into `matchingPolytope G` before the matching-to-perfect upgrade.
    exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope (G := G)

end Theorem_4_23

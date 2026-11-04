/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_4.ch4_sec4_4_4_theorem_4_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Theorem_4_24

universe u

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-!
The reverse inclusion is organized through compactness and extreme points, mirroring the stable
Krein-Milman skeleton used elsewhere in Chapter 4. The doubled-cover combinatorics in this file is
now paired with the exported reverse inclusion from Theorem 4.23, so the remaining local work is
only the nonintegral extreme-point classification and the doubled projection bridge.
-/

/-- Helper for Theorem 4.24: membership in `matchingConstraintSet G` already contains the
incident-edge upper bound at each vertex. -/
private lemma matchingConstraintSetIncidentSum_le_one
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1 := by
  -- This is the degree-inequality component of the constraint owner.
  exact (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx |>.2.1 v

/-- Helper for Theorem 4.24: every feasible edge coordinate of `matchingConstraintSet G` is at
most `1`. -/
private lemma edgeCoordinateLeOneOfMemMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) (e : G.edgeSet) :
    x e ≤ 1 := by
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset e.1.out.1
  have heI : e ∈ I := by
    simp [I, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff,
      Sym2.out_fst_mem]
  have hsingle : x e ≤ I.sum x := by
    exact Finset.single_le_sum (fun f _ ↦ hx_nonneg f) heI
  have hsum_le : I.sum x ≤ 1 := by
    simpa [I] using matchingConstraintSetIncidentSum_le_one (G := G) hx e.1.out.1
  exact hsingle.trans hsum_le

/-- Helper for Theorem 4.24: incidence vectors of subgraphs have nonnegative edge coordinates. -/
private lemma subgraphIncidenceVectorNonneg (M : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ M e := by
  intro e
  -- Each edge coordinate is the `0/1` indicator of membership in `M.edgeSet`.
  by_cases h : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Theorem 4.24: the edges with at least one endpoint in `S`, regarded as a finset of
edge coordinates of `G`. -/
private def oddSetIncidentEdgeFinset (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet ↦ ∃ v ∈ S, (e : Sym2 V) ∈ G.incidenceFinset v

/-- Helper for Theorem 4.24: summing over `G.edgeSet` with an indicator `if` rewrites to the
corresponding filtered edge sum. -/
private lemma edgeSetSumIteEqSumFilter
    (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-coordinate form of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Theorem 4.24: the endpoint finset of an edge-coordinate is its unordered pair of
canonical `Sym2.out` endpoints. -/
private lemma edgeToFinsetEqPairFinset (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Theorem 4.24: filtering `{a, b}` by membership in `S` has size `2`, `1`, or `0`
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

/-- Helper for Theorem 4.24: an induced edge is characterized by both canonical endpoints lying
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

/-- Helper for Theorem 4.24: a cut edge is characterized by its canonical endpoints lying on
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

/-- Helper for Theorem 4.24: an induced edge cannot simultaneously lie in the cut of the same
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

/-- Helper for Theorem 4.24: an edge belongs to `oddSetIncidentEdgeFinset S` exactly when one of
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

/-- Helper for Theorem 4.24: an edge incident to `S` is either internal to `S` or crosses the
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

/-- Helper for Theorem 4.24: the edges incident to `S` split disjointly into the edges induced by
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

/-- Helper for Theorem 4.24: filtering the vertices of `S` that lie on an edge agrees with
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

/-- Helper for Theorem 4.24: the filtered endpoint cardinality of an edge is the sum of the
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

/-- Helper for Theorem 4.24: summing the vertex-incidence equations on `S` counts each edge
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

/-- Helper for Theorem 4.24: summing the incidence equations on `S` counts each internal edge
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

/-- Helper for Theorem 4.24: summing degree-one equations over a finite vertex set produces the
cardinality of that set. -/
private lemma incidenceSum_eq_card_of_eq_one {x : G.edgeSet → ℝ}
    (hx_deg : ∀ v : V,
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1)
    (S : Set V) :
    Finset.sum S.toFinite.toFinset
      (fun v ↦
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
      (S.ncard : ℝ) := by
  -- Replace each incidence sum by `1` and evaluate the resulting constant finite sum.
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

/-- Helper for Theorem 4.24: inside `matchingConstraintSet G`, degree equations `= 1` upgrade the
owner to `perfectMatchingConstraintSet G`. -/
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
  -- Convert the matching odd-set upper bound into the perfect-matching odd-cut lower bound.
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

/-- Helper for Theorem 4.24: if a vertex is not covered by a subgraph, then its incidence sum in
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

/-- Helper for Theorem 4.24: at a covered vertex of a matching, the matching incidence sum is
exactly `1`. -/
private lemma matchingIncidenceSumEqOneOfMemVerts {M : G.Subgraph} (hM : M.IsMatching)
    {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge at `v` lies in the incidence filter.
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

/-- Helper for Theorem 4.24: every matching incidence sum at a vertex is bounded by `1`. -/
private lemma matchingIncidenceSumLeOne {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- A matching contributes `1` on covered vertices and `0` on uncovered vertices.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSumEqOneOfMemVerts (G := G) hM hv
    linarith
  · rw [subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) hv]
    norm_num

/-- Helper for Theorem 4.24: every matching incidence vector satisfies the Chapter 4.19
constraint system. -/
private lemma subgraphIncidenceVector_mem_matchingConstraintSet_of_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈ matchingConstraintSet G := by
  rw [SimpleGraph.mem_matchingConstraintSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · -- Matching generators are coordinatewise `0/1`, hence nonnegative.
    exact subgraphIncidenceVectorNonneg (G := G) M
  · intro v
    -- A matching contributes at most one incident edge at each vertex.
    exact matchingIncidenceSumLeOne (G := G) hM v
  · intro U hU
    -- Rewrite the induced-edge sum as an edge count, then use the degree decomposition.
    let m : ℕ := ((E[G] U).filter fun e : G.edgeSet ↦ e.1 ∈ M.edgeSet).card
    have hsum_card :
        (E[G] U).sum (G.subgraphIncidenceVector ℝ M) = (m : ℝ) := by
      simp [m, SimpleGraph.subgraphIncidenceVector]
    have hdegree_le :
        Finset.sum U.toFinset
            (fun v ↦
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
                (G.subgraphIncidenceVector ℝ M)) ≤ (U.ncard : ℝ) := by
      calc
        Finset.sum U.toFinset
            (fun v ↦
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
                (G.subgraphIncidenceVector ℝ M)) ≤
            Finset.sum U.toFinset (fun _ ↦ (1 : ℝ)) := by
              refine Finset.sum_le_sum ?_
              intro v hv
              exact matchingIncidenceSumLeOne (G := G) hM v
        _ = (U.ncard : ℝ) := by
            simp [Set.ncard_eq_toFinset_card']
    have hcut_nonneg :
        0 ≤ (δ[G] U).sum (G.subgraphIncidenceVector ℝ M) := by
      exact Finset.sum_nonneg fun e _ ↦ subgraphIncidenceVectorNonneg (G := G) M e
    have htwo_le_real :
        2 * (E[G] U).sum (G.subgraphIncidenceVector ℝ M) ≤ (U.ncard : ℝ) := by
      rw [sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum
          (G := G) (S := U) (x := G.subgraphIncidenceVector ℝ M)] at hdegree_le
      nlinarith
    have htwo_le_nat : 2 * m ≤ U.ncard := by
      have hreal : (2 : ℝ) * m ≤ (U.ncard : ℝ) := by
        simpa [hsum_card, two_mul] using htwo_le_real
      exact_mod_cast hreal
    rcases hU with ⟨k, hk⟩
    have hm_le_nat : m ≤ k := by
      omega
    have hm_le_real : (m : ℝ) ≤ ((U.ncard : ℝ) - 1) / 2 := by
      rw [hk]
      norm_num
      exact_mod_cast hm_le_nat
    simpa [hsum_card] using hm_le_real

/-- Helper for Theorem 4.24: the matching-constraint owner is convex. -/
private lemma convexMatchingConstraintSet :
    Convex ℝ (matchingConstraintSet G) := by
  intro x hx y hy a b ha hb hab
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_odd⟩
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := y)).1 hy with
    ⟨hy_nonneg, hy_deg, hy_odd⟩
  refine (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := a • x + b • y)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro e
    -- Coordinatewise nonnegativity is preserved by convex combinations.
    change 0 ≤ a * x e + b * y e
    nlinarith [hx_nonneg e, hy_nonneg e, ha, hb]
  · intro v
    -- The incident-edge sums are affine in the ambient edge coordinates.
    have hxv := hx_deg v
    have hyv := hy_deg v
    calc
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
          (a • x + b • y) =
          a *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x +
            b *
              (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum y := by
            simp [Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum,
              mul_comm, mul_left_comm, mul_assoc]
      _ ≤ a * 1 + b * 1 := by
            nlinarith [hxv, hyv, ha, hb]
      _ = 1 := by nlinarith [hab]
  · intro U hU
    -- The odd-set inequalities are also affine.
    have hxU := hx_odd U hU
    have hyU := hy_odd U hU
    calc
      (E[G] U).sum (a • x + b • y) = a * (E[G] U).sum x + b * (E[G] U).sum y := by
        simp [Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum,
          mul_comm, mul_left_comm, mul_assoc]
      _ ≤ a * (((U.ncard : ℝ) - 1) / 2) + b * (((U.ncard : ℝ) - 1) / 2) := by
            nlinarith [hxU, hyU, ha, hb]
      _ = ((U.ncard : ℝ) - 1) / 2 := by
            rw [← add_mul, hab, one_mul]

/-- Helper for Theorem 4.24: the matching-constraint owner is compact because it is closed inside
the edge-coordinate cube `[0,1]^E`. -/
private lemma matchingConstraintSet_isCompact :
    IsCompact (matchingConstraintSet G) := by
  have hclosed : IsClosed (matchingConstraintSet G) := by
    have hrepr :
        matchingConstraintSet G =
          ((⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) ∩
              ⋂ v : V,
                {x : G.edgeSet → ℝ |
                  (Finset.univ.filter
                    fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1}) ∩
            ⋂ U : Set V,
              {x : G.edgeSet → ℝ |
                Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2} := by
      ext x
      simp [SimpleGraph.mem_matchingConstraintSet_iff, and_assoc]
    rw [hrepr]
    have hcoordClosed :
        IsClosed (⋂ e : G.edgeSet, {x : G.edgeSet → ℝ | 0 ≤ x e}) := by
      refine isClosed_iInter fun e : G.edgeSet ↦ ?_
      change IsClosed ((ContinuousLinearMap.proj e : StrongDual ℝ (G.edgeSet → ℝ)) ⁻¹'
        Set.Ici (0 : ℝ))
      exact isClosed_Ici.preimage (ContinuousLinearMap.proj e).continuous
    have hdegClosed :
        IsClosed
          (⋂ v : V,
            {x : G.edgeSet → ℝ |
              (Finset.univ.filter
                fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1}) := by
      refine isClosed_iInter fun v : V ↦ ?_
      let incidenceMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun x ↦
            (Finset.univ.filter
              fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x
          map_add' := by
            intro x y
            simp [Finset.sum_add_distrib]
          map_smul' := by
            intro c x
            simp [smul_eq_mul, Finset.mul_sum] }
      change IsClosed (incidenceMap ⁻¹' Set.Iic (1 : ℝ))
      exact isClosed_Iic.preimage incidenceMap.continuous_of_finiteDimensional
    have hoddClosed :
        IsClosed
          (⋂ U : Set V,
            {x : G.edgeSet → ℝ |
              Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2}) := by
      refine isClosed_iInter fun U : Set V ↦ ?_
      by_cases hU : Odd U.ncard
      · let oddMap : (G.edgeSet → ℝ) →ₗ[ℝ] ℝ :=
          { toFun := fun x ↦ (E[G] U).sum x
            map_add' := by
              intro x y
              simp [Finset.sum_add_distrib]
            map_smul' := by
              intro c x
              simp [smul_eq_mul, Finset.mul_sum] }
        have hEq :
            {x : G.edgeSet → ℝ |
              Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2} =
              {x : G.edgeSet → ℝ | (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2} := by
          ext x
          simp [hU]
        rw [hEq]
        change IsClosed (oddMap ⁻¹' Set.Iic ((((U.ncard : ℝ) - 1) / 2)))
        exact isClosed_Iic.preimage oddMap.continuous_of_finiteDimensional
      · have hEq :
            {x : G.edgeSet → ℝ |
              Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2} = Set.univ := by
          ext x
          simp [hU]
        rw [hEq]
        exact isClosed_univ
    simpa [Set.inter_assoc] using hcoordClosed.inter (hdegClosed.inter hoddClosed)
  have hsubset_cube : matchingConstraintSet G ⊆ Set.Icc (0 : G.edgeSet → ℝ) 1 := by
    intro x hx
    rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
      ⟨hx_nonneg, -, -⟩
    refine ⟨hx_nonneg, ?_⟩
    intro e
    exact edgeCoordinateLeOneOfMemMatchingConstraintSet (G := G) hx e
  -- The feasible owner is closed and every coordinate lies in `[0,1]`.
  exact IsCompact.of_isClosed_subset isCompact_Icc hclosed hsubset_cube

/-- Helper for Theorem 4.24: the matching polytope is compact because it is the convex hull of
the finite family of matching-incidence generators. -/
private lemma matchingPolytope_isCompact :
    IsCompact (matchingPolytope G) := by
  let matchingGenerators : Set (G.edgeSet → ℝ) :=
    Set.range fun M : {M : G.Subgraph // M.IsMatching} ↦ G.subgraphIncidenceVector ℝ M.1
  have hgenerators :
      {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M} =
        matchingGenerators := by
    ext x
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact ⟨⟨M, hM⟩, rfl⟩
    · rintro ⟨M, rfl⟩
      exact ⟨M.1, M.2, rfl⟩
  have hfinite : matchingGenerators.Finite := by
    -- The subtype of matchings is finite, so its image under the incidence-vector map is finite.
    exact Set.finite_range _
  rw [SimpleGraph.matchingPolytope, hgenerators]
  simpa [matchingGenerators] using hfinite.isCompact_convexHull ℝ

/-- Helper for Theorem 4.24: every integral feasible point of `matchingConstraintSet G` is the
incidence vector of a matching. -/
private lemma integerPoint_eq_subgraphIncidenceVector_of_mem_matchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx : x ∈ matchingConstraintSet G)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  rcases hxInt with ⟨z, rfl⟩
  rcases (SimpleGraph.mem_matchingConstraintSet_iff
      (G := G) (x := fun f ↦ (z f : ℝ))).1 hx with ⟨hx_nonneg, hx_deg, -⟩
  have hz01 : ∀ e : G.edgeSet, ((z e : ℝ) = 0 ∨ (z e : ℝ) = 1) := by
    intro e
    have hz_nonneg : (0 : ℤ) ≤ z e := by
      exact_mod_cast hx_nonneg e
    have hz_le_one : z e ≤ 1 := by
      have hreal : ((z e : ℝ) ≤ 1) := by
        simpa using edgeCoordinateLeOneOfMemMatchingConstraintSet
          (G := G) (x := fun f ↦ (z f : ℝ)) hx e
      exact_mod_cast hreal
    interval_cases z e <;> simp
  let M : G.Subgraph :=
    { verts := {v : V | ∃ w, ∃ h : G.Adj v w, (z ⟨s(v, w), G.mem_edgeSet.2 h⟩ : ℝ) = 1}
      Adj := fun v w ↦ ∃ h : G.Adj v w, (z ⟨s(v, w), G.mem_edgeSet.2 h⟩ : ℝ) = 1
      adj_sub := fun h ↦ h.1
      edge_vert := by
        intro v w h
        exact ⟨w, h⟩
      symm := by
        intro v w h
        rcases h with ⟨hvw, hxvw⟩
        refine ⟨hvw.symm, ?_⟩
        simpa [Sym2.eq_swap] using hxvw }
  have hM_edge_iff (e : G.edgeSet) : e.1 ∈ M.edgeSet ↔ (z e : ℝ) = 1 := by
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      rw [← G.mem_edgeSet]
      simpa [e.1.out_eq] using e.2
    rw [← e.1.out_eq, Subgraph.mem_edgeSet]
    constructor
    · rintro ⟨hG, hz⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hG⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hz
    · intro hz
      refine ⟨hadj, ?_⟩
      have hSubtype :
          (⟨s(e.1.out.1, e.1.out.2), G.mem_edgeSet.2 hadj⟩ : G.edgeSet) = e := by
        apply Subtype.ext
        exact e.1.out_eq
      simpa [hSubtype] using hz
  have hM_matching : M.IsMatching := by
    intro v hv
    rcases hv with ⟨w, hvw, hvw_one⟩
    refine ⟨w, ⟨hvw, hvw_one⟩, ?_⟩
    intro w' hw'
    by_contra hneq
    let e : G.edgeSet := ⟨s(v, w), hvw⟩
    let e' : G.edgeSet := ⟨s(v, w'), hw'.1⟩
    have he_mem :
        e ∈ Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v := by
      simp [e, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have he'_mem :
        e' ∈ Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v := by
      simp [e', SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
    have he_ne : e ≠ e' := by
      intro heq
      apply hneq
      have hsymm : s(v, w) = s(v, w') := congrArg Subtype.val heq
      rcases Sym2.eq_iff.mp hsymm with hpair | hpair
      · exact hpair.2.symm
      · exact (hw'.1.ne hpair.1).elim
    let I : Finset G.edgeSet :=
      Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v
    have hsum_le :
        I.sum (fun f ↦ (z f : ℝ)) ≤ 1 := by
      simpa [I] using hx_deg v
    have hsum_split :
        (z e : ℝ) + (I.erase e).sum (fun f ↦ (z f : ℝ)) = I.sum (fun f ↦ (z f : ℝ)) := by
      exact Finset.add_sum_erase I (fun f ↦ (z f : ℝ)) he_mem
    have hrest_nonneg :
        0 ≤ (I.erase e).sum (fun f ↦ (z f : ℝ)) := by
      exact Finset.sum_nonneg fun f hf ↦ hx_nonneg f
    have hrest_eq_zero :
        (I.erase e).sum (fun f ↦ (z f : ℝ)) = 0 := by
      have hsum_le' := hsum_le
      rw [← hsum_split] at hsum_le'
      have hz_e_one : (z e : ℝ) = 1 := by
        simpa [e] using hvw_one
      have hrest_le_zero :
          (I.erase e).sum (fun f ↦ (z f : ℝ)) ≤ 0 := by
        linarith
      exact le_antisymm hrest_le_zero hrest_nonneg
    have he'_erase : e' ∈ I.erase e := by
      exact Finset.mem_erase.mpr ⟨he_ne.symm, by simpa [I] using he'_mem⟩
    have hz_e'_le :
        (z e' : ℝ) ≤ (I.erase e).sum (fun f ↦ (z f : ℝ)) := by
      exact Finset.single_le_sum (fun f _ ↦ hx_nonneg f) he'_erase
    have : (z e' : ℝ) = 0 := by
      have hz_e'_nonneg : 0 ≤ (z e' : ℝ) := hx_nonneg e'
      rw [hrest_eq_zero] at hz_e'_le
      exact le_antisymm hz_e'_le hz_e'_nonneg
    rw [hw'.2] at this
    norm_num at this
  refine ⟨M, hM_matching, ?_⟩
  -- The reconstructed support subgraph matches the original `0/1` edge coordinates exactly.
  funext e
  rcases hz01 e with he0 | he1
  · rw [SimpleGraph.subgraphIncidenceVector]
    rw [hM_edge_iff]
    simp [he0]
  · rw [SimpleGraph.subgraphIncidenceVector]
    rw [hM_edge_iff]
    simp [he1]

/-- Helper for Theorem 4.24: integral extreme points of the matching-constraint owner are already
matching generators, hence lie in the matching polytope. -/
private lemma mem_matchingPolytope_of_mem_extremePoints_matchingConstraintSet_of_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (matchingConstraintSet G).extremePoints ℝ)
    (hxInt : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ matchingPolytope G := by
  rcases integerPoint_eq_subgraphIncidenceVector_of_mem_matchingConstraintSet
      (G := G) (extremePoints_subset hx) hxInt with ⟨M, hM, rfl⟩
  rw [SimpleGraph.matchingPolytope]
  exact subset_convexHull ℝ _ ⟨M, hM, rfl⟩

/-- Helper for Theorem 4.24: once every nonintegral extreme point of `matchingConstraintSet G`
has been sent into `matchingPolytope G`, compact convexity upgrades the whole owner. -/
private lemma matchingConstraintSet_subset_matchingPolytope_of_nonintegerExtremeBridge
    (hNonInt :
      ∀ {x : G.edgeSet → ℝ},
        x ∈ (matchingConstraintSet G).extremePoints ℝ →
          x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) →
            x ∈ matchingPolytope G) :
    matchingConstraintSet G ⊆ matchingPolytope G := by
  intro x hx
  have hclosure :
      closure (convexHull ℝ ((matchingConstraintSet G).extremePoints ℝ)) =
        matchingConstraintSet G := by
    exact closure_convexHull_extremePoints
      (matchingConstraintSet_isCompact (G := G))
      (convexMatchingConstraintSet (G := G))
  have hxClosure :
      x ∈ closure (convexHull ℝ ((matchingConstraintSet G).extremePoints ℝ)) := by
    -- Krein-Milman rewrites the compact convex owner as the closure of the convex hull of its
    -- extreme points.
    simpa [hclosure] using hx
  have hExtremeSubset :
      (matchingConstraintSet G).extremePoints ℝ ⊆ matchingPolytope G := by
    intro y hy
    by_cases hyInt : y ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)
    · exact mem_matchingPolytope_of_mem_extremePoints_matchingConstraintSet_of_integer
        (G := G) hy hyInt
    · exact hNonInt hy hyInt
  have hHullSubset :
      convexHull ℝ ((matchingConstraintSet G).extremePoints ℝ) ⊆ matchingPolytope G := by
    -- The matching polytope is convex by construction as a convex hull.
    refine convexHull_min hExtremeSubset ?_
    rw [SimpleGraph.matchingPolytope]
    exact convex_convexHull ℝ _
  have hxClosurePoly : x ∈ closure (matchingPolytope G) := by
    exact (closure_mono hHullSubset) hxClosure
  -- Compactness of the matching polytope removes the closure at the end of the argument.
  simpa [(matchingPolytope_isCompact (G := G)).isClosed.closure_eq] using hxClosurePoly

/-- Helper for Theorem 4.24: every perfect-matching constraint point already satisfies the
matching-constraint inequalities. -/
private lemma mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ perfectMatchingConstraintSet G) :
    x ∈ matchingConstraintSet G := by
  rcases (SimpleGraph.mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, hx_deg, hx_odd⟩
  rw [SimpleGraph.mem_matchingConstraintSet_iff]
  refine ⟨hx_nonneg, ?_, ?_⟩
  · intro v
    -- The perfect-matching degree equation is stronger than the matching degree inequality.
    linarith [hx_deg v]
  · intro U hU
    -- The odd-cut lower bound implies the textbook odd-set upper bound after the incidence split.
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
    have hcut : 1 ≤ (δ[G] U).sum x := hx_odd U hU
    linarith

/-- Helper for Theorem 4.24: evaluating a finite weighted sum of edge-vectors at one edge turns
the vector identity into the corresponding scalar identity. -/
private lemma weightedSumApply
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → G.edgeSet → ℝ)
    {x : G.edgeSet → ℝ} (hx : ∑ i, w i • z i = x) (e : G.edgeSet) :
    ∑ i, w i * z i e = x e := by
  -- Apply the convex-combination identity at the chosen edge coordinate.
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx e

/-- Helper for Theorem 4.24: in a weighted average of numbers in `[0, 1]`, every positive-weight
support term must already equal `1` if the average is `1`. -/
private lemma eqOneOfWeightedAverageEqOne
    {ι : Type*} [Fintype ι] {w a : ι → ℝ}
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
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _hj ↦ hterm_nonneg j).1 hterm_sum i
      (Finset.mem_univ i)
  intro i hwi
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hslack_nonneg : 0 ≤ 1 - a i := sub_nonneg.mpr (ha_le_one i)
  have hslack_zero : 1 - a i = 0 := by
    nlinarith [hzero i, hwi_pos, hslack_nonneg]
  nlinarith [hslack_zero]

/-- Helper for Theorem 4.24: a positive-weight support matching in a convex decomposition of a
point of `perfectMatchingConstraintSet G` is already perfect. -/
private lemma supportMatchingIsPerfectOfConvexCombinationDegreeOne
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (M : ι → G.Subgraph) {x : G.edgeSet → ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hMatch : ∀ i, (M i).IsMatching)
    (hx : ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
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
    -- Evaluate the barycenter identity through the vertex-incidence functional at `v`.
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
              weightedSumApply (G := G) w (fun j ↦ G.subgraphIncidenceVector ℝ (M j)) hx e
      _ = 1 := by
            simpa [I] using hx_deg v
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

/-- Helper for Theorem 4.24: any point that is simultaneously in `matchingPolytope G` and
`perfectMatchingConstraintSet G` already lies in `perfectMatchingPolytope G`. -/
private lemma perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hxMatching : x ∈ matchingPolytope G)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingPolytope G := by
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hxMatching
  rcases hxMatching with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
  have hz' : ∀ i, ∃ M : G.Subgraph, M.IsMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hMatch hVec using hz'
  have hx_sum_match :
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x := by
    -- Rewrite the convex-combination witness so its generators are explicit matchings.
    calc
      ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = ∑ i, w i • z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hVec i]
      _ = x := hx_sum
  have hsupport_perfect :
      ∀ i, w i ≠ 0 → (M i).IsPerfectMatching :=
    supportMatchingIsPerfectOfConvexCombinationDegreeOne (G := G) w M
      hw_nonneg hw_sum hMatch hx_sum_match hxPerfect
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
    · exact ⟨M i₀, hM₀_perfect, by simp [zPerfect, hwi]⟩
    · exact ⟨M i, hsupport_perfect i hwi, by simp [zPerfect, hwi, hVec i]⟩
  have hx_sum_perfect : ∑ i, w i • zPerfect i = x := by
    -- Replacing zero-weight support points by a fixed perfect matching leaves the barycenter
    -- unchanged while making every generator perfect.
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

/-- Helper for Theorem 4.24: the source doubled graph has two copies of `G`, together with a
vertical edge joining each vertex to its copy. -/
private def doubleCoverAdj : (V ⊕ V) → (V ⊕ V) → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inr u, Sum.inr v => G.Adj u v
  | Sum.inl u, Sum.inr v => u = v
  | Sum.inr u, Sum.inl v => u = v

/-- Helper for Theorem 4.24: the doubled-graph adjacency is symmetric. -/
private lemma doubleCoverAdj_symm : Symmetric (doubleCoverAdj (G := G)) := by
  intro a b hab
  cases a <;> cases b <;> simpa [doubleCoverAdj] using hab.symm

/-- Helper for Theorem 4.24: the doubled-graph adjacency has no loops. -/
private lemma doubleCoverAdj_loopless : Std.Irrefl (doubleCoverAdj (G := G)) := by
  refine ⟨fun a ↦ ?_⟩
  cases a <;> simp [doubleCoverAdj]

/-- Helper for Theorem 4.24: this is the doubled graph used in the textbook reduction. -/
private def doubleCoverGraph : SimpleGraph (V ⊕ V) :=
  { Adj := doubleCoverAdj (G := G)
    symm := doubleCoverAdj_symm (G := G)
    loopless := doubleCoverAdj_loopless (G := G) }

/-- Helper for Theorem 4.24: the source incidence mass at a vertex for an edge vector on `G`. -/
private def sourceIncidenceSum (x : G.edgeSet → ℝ) (v : V) : ℝ :=
  (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x

/-- Helper for Theorem 4.24: on the incidence vector of a matching, the source incidence sum at
`v` is the indicator that `v` is covered by the matching. -/
private lemma sourceIncidenceSum_subgraphIncidenceVector_eq_indicator
    {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    sourceIncidenceSum (G := G) (G.subgraphIncidenceVector ℝ M) v =
      if v ∈ M.verts then 1 else 0 := by
  -- Covered vertices contribute one matching edge, while uncovered vertices contribute none.
  by_cases hv : v ∈ M.verts
  · rw [sourceIncidenceSum, if_pos hv]
    exact matchingIncidenceSumEqOneOfMemVerts (G := G) hM hv
  · rw [sourceIncidenceSum, if_neg hv]
    exact subgraphIncidenceSumEqZeroOfNotMemVerts (G := G) (M := M) hv

/-- Helper for Theorem 4.24: the lower horizontal copy of a source edge is an edge of the doubled
graph. -/
private lemma mem_doubleCoverGraph_edgeSet_lower (e : G.edgeSet) :
    s(Sum.inl e.1.out.1, Sum.inl e.1.out.2) ∈ (doubleCoverGraph G).edgeSet := by
  have hSource : G.Adj e.1.out.1 e.1.out.2 := by
    exact
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
        simpa [e.1.out_eq] using e.2
  exact
    (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G)
      (v := Sum.inl e.1.out.1) (w := Sum.inl e.1.out.2)).2 <| by
        simpa [doubleCoverGraph, doubleCoverAdj] using hSource

/-- Helper for Theorem 4.24: the upper horizontal copy of a source edge is an edge of the doubled
graph. -/
private lemma mem_doubleCoverGraph_edgeSet_upper (e : G.edgeSet) :
    s(Sum.inr e.1.out.1, Sum.inr e.1.out.2) ∈ (doubleCoverGraph G).edgeSet := by
  have hSource : G.Adj e.1.out.1 e.1.out.2 := by
    exact
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
        simpa [e.1.out_eq] using e.2
  exact
    (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G)
      (v := Sum.inr e.1.out.1) (w := Sum.inr e.1.out.2)).2 <| by
        simpa [doubleCoverGraph, doubleCoverAdj] using hSource

/-- Helper for Theorem 4.24: the vertical edge joining a vertex to its copy is an edge of the
doubled graph. -/
private lemma mem_doubleCoverGraph_edgeSet_vertical (v : V) :
    s(Sum.inl v, Sum.inr v) ∈ (doubleCoverGraph G).edgeSet := by
  exact
    (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inl v) (w := Sum.inr v)).2 <| by
      simp [doubleCoverGraph, doubleCoverAdj]

/-- Helper for Theorem 4.24: the lower horizontal source edge, regarded inside the doubled
graph. -/
private def doubleCoverLowerEdge (e : G.edgeSet) : (doubleCoverGraph G).edgeSet :=
  ⟨s(Sum.inl e.1.out.1, Sum.inl e.1.out.2), mem_doubleCoverGraph_edgeSet_lower (G := G) e⟩

/-- Helper for Theorem 4.24: the upper horizontal source edge, regarded inside the doubled
graph. -/
private def doubleCoverUpperEdge (e : G.edgeSet) : (doubleCoverGraph G).edgeSet :=
  ⟨s(Sum.inr e.1.out.1, Sum.inr e.1.out.2), mem_doubleCoverGraph_edgeSet_upper (G := G) e⟩

/-- Helper for Theorem 4.24: the vertical source edge, regarded inside the doubled graph. -/
private def doubleCoverVerticalEdge (v : V) : (doubleCoverGraph G).edgeSet :=
  ⟨s(Sum.inl v, Sum.inr v), mem_doubleCoverGraph_edgeSet_vertical (G := G) v⟩

/-- Helper for Theorem 4.24: the lower-copy edge constructor is exactly `Sym2.map Sum.inl` on
the underlying source edge. -/
private lemma coe_doubleCoverLowerEdge_eq_map (e : G.edgeSet) :
    ((doubleCoverLowerEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
      Sym2.map Sum.inl (e : Sym2 V) := by
  -- Rewrite the named lower edge through the canonical endpoint presentation of `e`.
  calc
    ((doubleCoverLowerEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        s(Sum.inl e.1.out.1, Sum.inl e.1.out.2) := by
          rfl
    _ = Sym2.map Sum.inl (s(e.1.out.1, e.1.out.2)) := by
          rw [Sym2.map_mk]
    _ = Sym2.map Sum.inl (e : Sym2 V) := by
          exact congrArg (fun z : Sym2 V ↦ Sym2.map Sum.inl z) e.1.out_eq

/-- Helper for Theorem 4.24: the upper-copy edge constructor is exactly `Sym2.map Sum.inr` on
the underlying source edge. -/
private lemma coe_doubleCoverUpperEdge_eq_map (e : G.edgeSet) :
    ((doubleCoverUpperEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
      Sym2.map Sum.inr (e : Sym2 V) := by
  -- Rewrite the named upper edge through the canonical endpoint presentation of `e`.
  calc
    ((doubleCoverUpperEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        s(Sum.inr e.1.out.1, Sum.inr e.1.out.2) := by
          rfl
    _ = Sym2.map Sum.inr (s(e.1.out.1, e.1.out.2)) := by
          rw [Sym2.map_mk]
    _ = Sym2.map Sum.inr (e : Sym2 V) := by
          exact congrArg (fun z : Sym2 V ↦ Sym2.map Sum.inr z) e.1.out_eq

/-- Helper for Theorem 4.24: the named vertical doubled edge agrees with the raw mixed doubled
edge built from a source vertex and its copy. -/
private lemma doubleCoverVerticalEdge_eq_mk (v : V) :
    doubleCoverVerticalEdge (G := G) v =
      (⟨s(Sum.inl v, Sum.inr v), mem_doubleCoverGraph_edgeSet_vertical (G := G) v⟩ :
        (doubleCoverGraph G).edgeSet) := by
  -- The named vertical edge is definitionally the raw mixed edge above `v`.
  rfl

/-- Helper for Theorem 4.24: the named lower doubled edge agrees with the raw horizontal doubled
edge built from the same adjacent source endpoints. -/
private lemma doubleCoverLowerEdge_eq_mk {u v : V} (h : G.Adj u v) :
    doubleCoverLowerEdge (G := G)
        (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩ : G.edgeSet) =
      (⟨s(Sum.inl u, Sum.inl v),
        (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inl u) (w := Sum.inl v)).2
          (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
        (doubleCoverGraph G).edgeSet) := by
  let e : G.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩
  -- Compare the two doubled edges on their underlying `Sym2` values.
  apply Subtype.ext
  calc
    ((doubleCoverLowerEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        Sym2.map Sum.inl (e : Sym2 V) := by
          exact coe_doubleCoverLowerEdge_eq_map (G := G) e
    _ = s(Sum.inl u, Sum.inl v) := by
          simp [e, Sym2.map_mk]
    _ =
        ((⟨s(Sum.inl u, Sum.inl v),
            (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inl u)
              (w := Sum.inl v)).2 (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
            (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) := by
          rfl

/-- Helper for Theorem 4.24: the named upper doubled edge agrees with the raw horizontal doubled
edge built from the same adjacent source endpoints. -/
private lemma doubleCoverUpperEdge_eq_mk {u v : V} (h : G.Adj u v) :
    doubleCoverUpperEdge (G := G)
        (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩ : G.edgeSet) =
      (⟨s(Sum.inr u, Sum.inr v),
        (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inr u) (w := Sum.inr v)).2
          (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
        (doubleCoverGraph G).edgeSet) := by
  let e : G.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩
  -- Compare the two doubled edges on their underlying `Sym2` values.
  apply Subtype.ext
  calc
    ((doubleCoverUpperEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        Sym2.map Sum.inr (e : Sym2 V) := by
          exact coe_doubleCoverUpperEdge_eq_map (G := G) e
    _ = s(Sum.inr u, Sum.inr v) := by
          simp [e, Sym2.map_mk]
    _ =
        ((⟨s(Sum.inr u, Sum.inr v),
            (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inr u)
              (w := Sum.inr v)).2 (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
            (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) := by
          rfl

/-- Helper for Theorem 4.24: every edge of the doubled graph is either a lower copy, an upper
copy, or the vertical edge above some source vertex. -/
private lemma eq_doubleCoverLowerEdge_or_eq_doubleCoverUpperEdge_or_eq_doubleCoverVerticalEdge
    (e : (doubleCoverGraph G).edgeSet) :
    (∃ e₀ : G.edgeSet, e = doubleCoverLowerEdge (G := G) e₀) ∨
      (∃ e₀ : G.edgeSet, e = doubleCoverUpperEdge (G := G) e₀) ∨
      (∃ v : V, e = doubleCoverVerticalEdge (G := G) v) := by
  rcases e with ⟨e, he⟩
  have heAdj : (doubleCoverGraph G).Adj e.out.1 e.out.2 := by
    exact
      (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := e.out.1) (w := e.out.2)).1 <| by
        simpa [e.out_eq] using he
  -- Split by the two doubled endpoints; each adjacency pattern gives one of the three edge types.
  cases h₁ : e.out.1 with
  | inl u =>
      cases h₂ : e.out.2 with
      | inl v =>
          left
          refine ⟨⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 ?_⟩, ?_⟩
          · simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj
          · apply Subtype.ext
            calc
              e = s(e.out.1, e.out.2) := by
                exact e.out_eq.symm
              _ = s(Sum.inl u, Sum.inl v) := by
                rw [h₁, h₂]
              _ = ((doubleCoverLowerEdge (G := G)
                    (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2
                      (by simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj)⟩ :
                      G.edgeSet) : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) := by
                    simpa using congrArg
                      (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V)))
                      (doubleCoverLowerEdge_eq_mk (G := G)
                        (h := by simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj)).symm
      | inr v =>
          right
          right
          have huv : u = v := by
            simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj
          subst huv
          refine ⟨u, ?_⟩
          apply Subtype.ext
          calc
            e = s(e.out.1, e.out.2) := by
              exact e.out_eq.symm
            _ = s(Sum.inl u, Sum.inr u) := by
              rw [h₁, h₂]
            _ = ((doubleCoverVerticalEdge (G := G) u : (doubleCoverGraph G).edgeSet) :
                  Sym2 (V ⊕ V)) := by
                  rfl
  | inr u =>
      cases h₂ : e.out.2 with
      | inl v =>
          right
          right
          have huv : u = v := by
            simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj
          subst huv
          refine ⟨u, ?_⟩
          apply Subtype.ext
          calc
            e = s(e.out.1, e.out.2) := by
              exact e.out_eq.symm
            _ = s(Sum.inr u, Sum.inl u) := by
              rw [h₁, h₂]
            _ = s(Sum.inl u, Sum.inr u) := by
              rw [Sym2.eq_swap]
            _ = ((doubleCoverVerticalEdge (G := G) u : (doubleCoverGraph G).edgeSet) :
                  Sym2 (V ⊕ V)) := by
                  rfl
      | inr v =>
          right
          left
          refine ⟨⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 ?_⟩, ?_⟩
          · simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj
          · apply Subtype.ext
            calc
              e = s(e.out.1, e.out.2) := by
                exact e.out_eq.symm
              _ = s(Sum.inr u, Sum.inr v) := by
                rw [h₁, h₂]
              _ = ((doubleCoverUpperEdge (G := G)
                    (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2
                      (by simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj)⟩ :
                      G.edgeSet) : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) := by
                    simpa using congrArg
                      (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V)))
                      (doubleCoverUpperEdge_eq_mk (G := G)
                        (h := by simpa [doubleCoverGraph, doubleCoverAdj, h₁, h₂] using heAdj)).symm

/-- Helper for Theorem 4.24: if a doubled edge has lower-copy endpoints `u` and `v`, then
`u` and `v` are adjacent in the source graph. -/
private lemma sourceAdj_of_doubleCover_out_inl (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hfst : e.1.out.1 = Sum.inl u) (hsnd : e.1.out.2 = Sum.inl v) :
    G.Adj u v := by
  have hEdge : (doubleCoverGraph G).Adj e.1.out.1 e.1.out.2 :=
    (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
      simpa [e.1.out_eq] using e.2
  have hDouble : (doubleCoverGraph G).Adj (Sum.inl u) (Sum.inl v) := by
    simpa [hfst, hsnd] using hEdge
  simpa [doubleCoverGraph, doubleCoverAdj] using hDouble

/-- Helper for Theorem 4.24: if a doubled edge has upper-copy endpoints `u` and `v`, then
`u` and `v` are adjacent in the source graph. -/
private lemma sourceAdj_of_doubleCover_out_inr (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hfst : e.1.out.1 = Sum.inr u) (hsnd : e.1.out.2 = Sum.inr v) :
    G.Adj u v := by
  have hEdge : (doubleCoverGraph G).Adj e.1.out.1 e.1.out.2 :=
    (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
      simpa [e.1.out_eq] using e.2
  have hDouble : (doubleCoverGraph G).Adj (Sum.inr u) (Sum.inr v) := by
    simpa [hfst, hsnd] using hEdge
  simpa [doubleCoverGraph, doubleCoverAdj] using hDouble

/-- Helper for Theorem 4.24: a doubled edge whose `Sym2.out` pair lies in the lower copy
comes from the corresponding source edge of `G`. -/
private lemma sourceAdj_of_doubleCover_out_eq_inl (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inl u, Sum.inl v)) :
    G.Adj u v := by
  exact
    sourceAdj_of_doubleCover_out_inl (G := G) e
      (by simpa using congrArg Prod.fst hout)
      (by simpa using congrArg Prod.snd hout)

/-- Helper for Theorem 4.24: a doubled edge whose `Sym2.out` pair lies in the upper copy
comes from the corresponding source edge of `G`. -/
private lemma sourceAdj_of_doubleCover_out_eq_inr (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inr u, Sum.inr v)) :
    G.Adj u v := by
  exact
    sourceAdj_of_doubleCover_out_inr (G := G) e
      (by simpa using congrArg Prod.fst hout)
      (by simpa using congrArg Prod.snd hout)

/-- Helper for Theorem 4.24: the textbook doubled-cover lift copies source edges to both
horizontal layers and places the residual degree on the vertical edge above each vertex. -/
private def doubleCoverLift (x : G.edgeSet → ℝ) : (doubleCoverGraph G).edgeSet → ℝ :=
  fun e =>
    match hout : e.1.out with
    | (Sum.inl u, Sum.inl v) =>
        x ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 <|
            sourceAdj_of_doubleCover_out_eq_inl (G := G) e hout⟩
    | (Sum.inr u, Sum.inr v) =>
        x ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 <|
            sourceAdj_of_doubleCover_out_eq_inr (G := G) e hout⟩
    | (Sum.inl u, Sum.inr _) => 1 - sourceIncidenceSum (G := G) x u
    | (Sum.inr _, Sum.inl v) => 1 - sourceIncidenceSum (G := G) x v

/-- Helper for Theorem 4.24: `doubleCoverLift` reads a lower-copy edge by the corresponding
source coordinate when the `Sym2.out` pair is fixed. -/
private lemma doubleCoverLift_eq_of_out_eq_inl
    (x : G.edgeSet → ℝ) (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inl u, Sum.inl v)) :
    doubleCoverLift (G := G) x e =
      x ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 <|
          sourceAdj_of_doubleCover_out_eq_inl (G := G) e hout⟩ := by
  -- Collapse the dependent `match` in `doubleCoverLift` by fixing the `Sym2.out` pair.
  cases hout
  -- The lower-copy branch is now definitionally the claimed source coordinate.
  simp [doubleCoverLift]

/-- Helper for Theorem 4.24: `doubleCoverLift` reads an upper-copy edge by the corresponding
source coordinate when the `Sym2.out` pair is fixed. -/
private lemma doubleCoverLift_eq_of_out_eq_inr
    (x : G.edgeSet → ℝ) (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inr u, Sum.inr v)) :
    doubleCoverLift (G := G) x e =
      x ⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 <|
          sourceAdj_of_doubleCover_out_eq_inr (G := G) e hout⟩ := by
  -- Collapse the dependent `match` in `doubleCoverLift` by fixing the `Sym2.out` pair.
  cases hout
  -- The upper-copy branch is now definitionally the claimed source coordinate.
  simp [doubleCoverLift]

/-- Helper for Theorem 4.24: on a mixed edge whose `Sym2.out` pair starts in the lower copy,
`doubleCoverLift` stores the residual slack at that lower vertex. -/
private lemma doubleCoverLift_eq_of_out_eq_mixed_left
    (x : G.edgeSet → ℝ) (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inl u, Sum.inr v)) :
    doubleCoverLift (G := G) x e = 1 - sourceIncidenceSum (G := G) x u := by
  -- Collapse the dependent `match` to the mixed-left branch selected by `hout`.
  cases hout
  -- The mixed-left branch is definitionally the residual slack at `u`.
  simp [doubleCoverLift]

/-- Helper for Theorem 4.24: on a mixed edge whose `Sym2.out` pair starts in the upper copy,
`doubleCoverLift` stores the residual slack at that lower endpoint. -/
private lemma doubleCoverLift_eq_of_out_eq_mixed_right
    (x : G.edgeSet → ℝ) (e : (doubleCoverGraph G).edgeSet) {u v : V}
    (hout : e.1.out = (Sum.inr u, Sum.inl v)) :
    doubleCoverLift (G := G) x e = 1 - sourceIncidenceSum (G := G) x v := by
  -- Collapse the dependent `match` to the mixed-right branch selected by `hout`.
  cases hout
  -- The mixed-right branch is definitionally the residual slack at the lower endpoint.
  simp [doubleCoverLift]

/-- Helper for Theorem 4.24: if a `Sym2` value is written as `s(a, b)`, then its canonical
`out` pair is either `(a, b)` or `(b, a)`. -/
private lemma sym2Out_eq_pair_or_swap {α : Type*} [DecidableEq α]
    (z : Sym2 α) (a b : α) (hz : z = s(a, b)) :
    z.out = (a, b) ∨ z.out = (b, a) := by
  have hz' : s(z.out.1, z.out.2) = s(a, b) := by
    calc
      s(z.out.1, z.out.2) = z := z.out_eq
      _ = s(a, b) := hz
  rw [Sym2.eq_iff] at hz'
  rcases hz' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

/-- Helper for Theorem 4.24: the doubled lift on a raw lower horizontal doubled edge is the
source coordinate of the corresponding source edge. -/
private lemma doubleCoverLift_lowerEdge_eq_mk (x : G.edgeSet → ℝ) {u v : V} (h : G.Adj u v) :
    doubleCoverLift (G := G) x
      (⟨s(Sum.inl u, Sum.inl v),
        (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inl u) (w := Sum.inl v)).2
          (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
        (doubleCoverGraph G).edgeSet) =
      x (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩ : G.edgeSet) := by
  let eDouble : (doubleCoverGraph G).edgeSet :=
    (⟨s(Sum.inl u, Sum.inl v),
      (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inl u) (w := Sum.inl v)).2
        (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
      (doubleCoverGraph G).edgeSet)
  have hout :
      ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inl u, Sum.inl v) ∨
        ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inl v, Sum.inl u) := by
    -- The canonical `Sym2.out` pair of the raw lower edge can only differ by swapping endpoints.
    simpa [eDouble] using
      sym2Out_eq_pair_or_swap (z := ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)))
        (a := Sum.inl u) (b := Sum.inl v) rfl
  -- Reduce `doubleCoverLift` in the two possible endpoint orders delivered by `Sym2.out`.
  rcases hout with hpair | hswap
  · simpa [eDouble] using
      doubleCoverLift_eq_of_out_eq_inl (G := G) (x := x) (e := eDouble) (u := u) (v := v) hpair
  · simpa [eDouble, Sym2.eq_swap] using
      doubleCoverLift_eq_of_out_eq_inl (G := G) (x := x) (e := eDouble) (u := v) (v := u) hswap

/-- Helper for Theorem 4.24: the doubled lift on a raw upper horizontal doubled edge is the
source coordinate of the corresponding source edge. -/
private lemma doubleCoverLift_upperEdge_eq_mk (x : G.edgeSet → ℝ) {u v : V} (h : G.Adj u v) :
    doubleCoverLift (G := G) x
      (⟨s(Sum.inr u, Sum.inr v),
        (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inr u) (w := Sum.inr v)).2
          (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
        (doubleCoverGraph G).edgeSet) =
      x (⟨s(u, v), (SimpleGraph.mem_edgeSet (G := G) (v := u) (w := v)).2 h⟩ : G.edgeSet) := by
  let eDouble : (doubleCoverGraph G).edgeSet :=
    (⟨s(Sum.inr u, Sum.inr v),
      (SimpleGraph.mem_edgeSet (G := doubleCoverGraph G) (v := Sum.inr u) (w := Sum.inr v)).2
        (by simpa [doubleCoverGraph, doubleCoverAdj] using h)⟩ :
      (doubleCoverGraph G).edgeSet)
  have hout :
      ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inr u, Sum.inr v) ∨
        ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inr v, Sum.inr u) := by
    -- The canonical `Sym2.out` pair of the raw upper edge can only differ by swapping endpoints.
    simpa [eDouble] using
      sym2Out_eq_pair_or_swap (z := ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)))
        (a := Sum.inr u) (b := Sum.inr v) rfl
  -- Reduce `doubleCoverLift` in the two possible endpoint orders delivered by `Sym2.out`.
  rcases hout with hpair | hswap
  · simpa [eDouble] using
      doubleCoverLift_eq_of_out_eq_inr (G := G) (x := x) (e := eDouble) (u := u) (v := v) hpair
  · simpa [eDouble, Sym2.eq_swap] using
      doubleCoverLift_eq_of_out_eq_inr (G := G) (x := x) (e := eDouble) (u := v) (v := u) hswap

/-- Helper for Theorem 4.24: on the lower horizontal copy of a source edge, the doubled lift
recovers the original source coordinate. -/
private lemma doubleCoverLift_lowerEdge
    (x : G.edgeSet → ℝ) (e : G.edgeSet) :
    doubleCoverLift (G := G) x (doubleCoverLowerEdge (G := G) e) = x e := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    -- The canonical endpoints of `e` are adjacent in the source graph.
    exact
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
        simpa [e.1.out_eq] using e.2
  have hsource :
      (⟨s(e.1.out.1, e.1.out.2), (SimpleGraph.mem_edgeSet (G := G)
        (v := e.1.out.1) (w := e.1.out.2)).2 hadj⟩ : G.edgeSet) = e := by
    -- The raw source edge above the canonical endpoints is exactly `e`.
    apply Subtype.ext
    exact e.1.out_eq
  -- Reduce the named lower edge to the explicit raw lower edge above the canonical endpoints.
  rw [← hsource]
  simpa [doubleCoverLowerEdge_eq_mk (G := G) hadj] using
    doubleCoverLift_lowerEdge_eq_mk (G := G) (x := x) hadj

/-- Helper for Theorem 4.24: on the upper horizontal copy of a source edge, the doubled lift
again recovers the original source coordinate. -/
private lemma doubleCoverLift_upperEdge
    (x : G.edgeSet → ℝ) (e : G.edgeSet) :
    doubleCoverLift (G := G) x (doubleCoverUpperEdge (G := G) e) = x e := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    -- The canonical endpoints of `e` are adjacent in the source graph.
    exact
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 <| by
        simpa [e.1.out_eq] using e.2
  have hsource :
      (⟨s(e.1.out.1, e.1.out.2), (SimpleGraph.mem_edgeSet (G := G)
        (v := e.1.out.1) (w := e.1.out.2)).2 hadj⟩ : G.edgeSet) = e := by
    -- The raw source edge above the canonical endpoints is exactly `e`.
    apply Subtype.ext
    exact e.1.out_eq
  -- Reduce the named upper edge to the explicit raw upper edge above the canonical endpoints.
  rw [← hsource]
  simpa [doubleCoverUpperEdge_eq_mk (G := G) hadj] using
    doubleCoverLift_upperEdge_eq_mk (G := G) (x := x) hadj

/-- Helper for Theorem 4.24: the raw mixed doubled edge `⟨s(Sum.inl v, Sum.inr v), _⟩` evaluates
under `doubleCoverLift` to the residual source incidence slack at `v`. -/
private lemma doubleCoverLift_verticalEdge_rawEval
    (x : G.edgeSet → ℝ) (v : V) :
    doubleCoverLift (G := G) x
      (⟨s(Sum.inl v, Sum.inr v), mem_doubleCoverGraph_edgeSet_vertical (G := G) v⟩ :
        (doubleCoverGraph G).edgeSet) =
      1 - sourceIncidenceSum (G := G) x v := by
  let eDouble : (doubleCoverGraph G).edgeSet :=
    (⟨s(Sum.inl v, Sum.inr v), mem_doubleCoverGraph_edgeSet_vertical (G := G) v⟩ :
      (doubleCoverGraph G).edgeSet)
  have hout :
      ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inl v, Sum.inr v) ∨
        ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)).out = (Sum.inr v, Sum.inl v) := by
    -- The mixed vertical edge again has only the two endpoint orders allowed by `Sym2.out`.
    simpa [eDouble] using
      sym2Out_eq_pair_or_swap (z := ((eDouble : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)))
        (a := Sum.inl v) (b := Sum.inr v) rfl
  -- Both endpoint orders fall into the residual-slack branches of `doubleCoverLift`.
  rcases hout with hpair | hswap
  · simpa [eDouble] using
      doubleCoverLift_eq_of_out_eq_mixed_left (G := G) (x := x) (e := eDouble) (u := v) (v := v)
        hpair
  · simpa [eDouble] using
      doubleCoverLift_eq_of_out_eq_mixed_right (G := G) (x := x) (e := eDouble) (u := v) (v := v)
        hswap

/-- Helper for Theorem 4.24: on a vertical doubled edge, the lift stores the residual slack of
the source incidence equation at that vertex. -/
private lemma doubleCoverLift_verticalEdge
    (x : G.edgeSet → ℝ) (v : V) :
    doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v) =
      1 - sourceIncidenceSum (G := G) x v := by
  -- Rewrite the named vertical edge to the raw mixed edge handled by the dedicated adapter.
  rw [doubleCoverVerticalEdge_eq_mk (G := G) v]
  exact doubleCoverLift_verticalEdge_rawEval (G := G) x v

/-- Helper for Theorem 4.24: on the incidence vector of a matching, the lifted vertical edge at
`v` records exactly whether `v` is unmatched. -/
private lemma doubleCoverLift_verticalEdge_subgraphIncidenceVector_eq_indicator
    {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    doubleCoverLift (G := G) (G.subgraphIncidenceVector ℝ M)
        (doubleCoverVerticalEdge (G := G) v) =
      if v ∈ M.verts then 0 else 1 := by
  -- Rewrite the vertical coordinate as `1` minus the source incidence indicator of `M` at `v`.
  rw [doubleCoverLift_verticalEdge (G := G) (x := G.subgraphIncidenceVector ℝ M) v]
  rw [sourceIncidenceSum_subgraphIncidenceVector_eq_indicator (G := G) hM v]
  by_cases hv : v ∈ M.verts
  · -- Covered vertices have residual slack `0`.
    simp [hv]
  · -- Uncovered vertices have residual slack `1`.
    simp [hv]

/-- Helper for Theorem 4.24: the lower horizontal doubled edge is induced by `Utilde` exactly
when both lower-copy endpoints lie in `Utilde`. -/
private lemma mem_inducedEdgeFinset_doubleCoverLowerEdge_iff
    (Utilde : Set (V ⊕ V)) (e : G.edgeSet) :
    doubleCoverLowerEdge (G := G) e ∈ E[doubleCoverGraph G] Utilde ↔
      Sum.inl e.1.out.1 ∈ Utilde ∧ Sum.inl e.1.out.2 ∈ Utilde := by
  have hadj : (doubleCoverGraph G).Adj (Sum.inl e.1.out.1) (Sum.inl e.1.out.2) := by
    simpa [doubleCoverGraph, doubleCoverAdj] using
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1
        (by simpa [e.1.out_eq] using e.2)
  -- Rewrite the lower doubled edge to the explicit horizontal pair and unfold induced membership.
  rw [mem_inducedEdgeFinset_iff]
  change s(Sum.inl e.1.out.1, Sum.inl e.1.out.2) ∈
    ((⊤ : (doubleCoverGraph G).Subgraph).induce Utilde).edgeSet ↔ _
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Theorem 4.24: the upper horizontal doubled edge is induced by `Utilde` exactly
when both upper-copy endpoints lie in `Utilde`. -/
private lemma mem_inducedEdgeFinset_doubleCoverUpperEdge_iff
    (Utilde : Set (V ⊕ V)) (e : G.edgeSet) :
    doubleCoverUpperEdge (G := G) e ∈ E[doubleCoverGraph G] Utilde ↔
      Sum.inr e.1.out.1 ∈ Utilde ∧ Sum.inr e.1.out.2 ∈ Utilde := by
  have hadj : (doubleCoverGraph G).Adj (Sum.inr e.1.out.1) (Sum.inr e.1.out.2) := by
    simpa [doubleCoverGraph, doubleCoverAdj] using
      (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1
        (by simpa [e.1.out_eq] using e.2)
  -- Rewrite the upper doubled edge to the explicit horizontal pair and unfold induced membership.
  rw [mem_inducedEdgeFinset_iff]
  change s(Sum.inr e.1.out.1, Sum.inr e.1.out.2) ∈
    ((⊤ : (doubleCoverGraph G).Subgraph).induce Utilde).edgeSet ↔ _
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Theorem 4.24: the vertical doubled edge is induced by `Utilde` exactly when
`Utilde` contains both copies of `v`. -/
private lemma mem_inducedEdgeFinset_doubleCoverVerticalEdge_iff
    (Utilde : Set (V ⊕ V)) (v : V) :
    doubleCoverVerticalEdge (G := G) v ∈ E[doubleCoverGraph G] Utilde ↔
      Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde := by
  have hadj : (doubleCoverGraph G).Adj (Sum.inl v) (Sum.inr v) := by
    simp [doubleCoverGraph, doubleCoverAdj]
  -- The vertical edge is the explicit mixed pair `(Sum.inl v, Sum.inr v)`.
  rw [mem_inducedEdgeFinset_iff]
  change s(Sum.inl v, Sum.inr v) ∈
    ((⊤ : (doubleCoverGraph G).Subgraph).induce Utilde).edgeSet ↔ _
  rw [SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Theorem 4.24: the lower horizontal doubled edge lies in the cut of `Utilde`
exactly when the two lower-copy endpoints lie on opposite sides of `Utilde`. -/
private lemma mem_cutEdgeFinset_doubleCoverLowerEdge_iff
    (Utilde : Set (V ⊕ V)) (e : G.edgeSet) :
    doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde ↔
      (Sum.inl e.1.out.1 ∈ Utilde) ≠ (Sum.inl e.1.out.2 ∈ Utilde) := by
  constructor
  · intro h
    rcases (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverLowerEdge (G := G) e)).1 h with ⟨u, hu, v, hv, huv⟩
    rw [show (((doubleCoverLowerEdge (G := G) e : (doubleCoverGraph G).edgeSet) :
        Sym2 (V ⊕ V)) = s(Sum.inl e.1.out.1, Sum.inl e.1.out.2)) by rfl] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hu, hv]
  · intro h
    by_cases h₁ : Sum.inl e.1.out.1 ∈ Utilde
    · have h₂ : Sum.inl e.1.out.2 ∉ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverLowerEdge (G := G) e)).2
          ⟨Sum.inl e.1.out.1, h₁, Sum.inl e.1.out.2, h₂, by rfl⟩
    · have h₂ : Sum.inl e.1.out.2 ∈ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverLowerEdge (G := G) e)).2
          ⟨Sum.inl e.1.out.2, h₂, Sum.inl e.1.out.1, h₁,
            by simpa [doubleCoverLowerEdge, Sym2.eq_swap]⟩

/-- Helper for Theorem 4.24: the upper horizontal doubled edge lies in the cut of `Utilde`
exactly when the two upper-copy endpoints lie on opposite sides of `Utilde`. -/
private lemma mem_cutEdgeFinset_doubleCoverUpperEdge_iff
    (Utilde : Set (V ⊕ V)) (e : G.edgeSet) :
    doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde ↔
      (Sum.inr e.1.out.1 ∈ Utilde) ≠ (Sum.inr e.1.out.2 ∈ Utilde) := by
  constructor
  · intro h
    rcases (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverUpperEdge (G := G) e)).1 h with ⟨u, hu, v, hv, huv⟩
    rw [show (((doubleCoverUpperEdge (G := G) e : (doubleCoverGraph G).edgeSet) :
        Sym2 (V ⊕ V)) = s(Sum.inr e.1.out.1, Sum.inr e.1.out.2)) by rfl] at huv
    rw [Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hu, hv]
  · intro h
    by_cases h₁ : Sum.inr e.1.out.1 ∈ Utilde
    · have h₂ : Sum.inr e.1.out.2 ∉ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverUpperEdge (G := G) e)).2
          ⟨Sum.inr e.1.out.1, h₁, Sum.inr e.1.out.2, h₂, by rfl⟩
    · have h₂ : Sum.inr e.1.out.2 ∈ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverUpperEdge (G := G) e)).2
          ⟨Sum.inr e.1.out.2, h₂, Sum.inr e.1.out.1, h₁,
            by simpa [doubleCoverUpperEdge, Sym2.eq_swap]⟩

/-- Helper for Theorem 4.24: the vertical doubled edge lies in the cut of `Utilde` exactly when
`Utilde` contains exactly one copy of `v`. -/
private lemma mem_cutEdgeFinset_doubleCoverVerticalEdge_iff
    (Utilde : Set (V ⊕ V)) (v : V) :
    doubleCoverVerticalEdge (G := G) v ∈ δ[doubleCoverGraph G] Utilde ↔
      (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde) := by
  constructor
  · intro h
    rcases (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverVerticalEdge (G := G) v)).1 h with ⟨u, hu, w, hw, huw⟩
    rw [show (((doubleCoverVerticalEdge (G := G) v : (doubleCoverGraph G).edgeSet) :
        Sym2 (V ⊕ V)) = s(Sum.inl v, Sum.inr v)) by rfl] at huw
    rw [Sym2.eq_iff] at huw
    rcases huw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hu, hw]
  · intro h
    by_cases h₁ : Sum.inl v ∈ Utilde
    · have h₂ : Sum.inr v ∉ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverVerticalEdge (G := G) v)).2
          ⟨Sum.inl v, h₁, Sum.inr v, h₂, by rfl⟩
    · have h₂ : Sum.inr v ∈ Utilde := by
        simpa [h₁] using h
      exact (mem_cutEdgeFinset_iff (G := doubleCoverGraph G) (S := Utilde)
        (e := doubleCoverVerticalEdge (G := G) v)).2
          ⟨Sum.inr v, h₂, Sum.inl v, h₁, by simpa [doubleCoverVerticalEdge, Sym2.eq_swap]⟩

/-- Helper for Theorem 4.24: the lower-copy edge constructor on source edges is injective. -/
private lemma doubleCoverLowerEdge_injective :
    Function.Injective (doubleCoverLowerEdge (G := G)) := by
  intro e₁ e₂ h
  have hvals :
      Sym2.map (fun x : V ↦ (Sum.inl x : V ⊕ V)) (e₁ : Sym2 V) =
        Sym2.map (fun x : V ↦ (Sum.inl x : V ⊕ V)) (e₂ : Sym2 V) := by
    -- Push the equality down to `Sym2` and rewrite both sides through the map description.
    have hcoe :
        (((doubleCoverLowerEdge (G := G) e₁ : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V))) =
          (((doubleCoverLowerEdge (G := G) e₂ : (doubleCoverGraph G).edgeSet) :
            Sym2 (V ⊕ V))) := by
      exact congrArg (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V))) h
    rw [coe_doubleCoverLowerEdge_eq_map, coe_doubleCoverLowerEdge_eq_map] at hcoe
    exact hcoe
  have hinl : Function.Injective (fun x : V ↦ (Sum.inl x : V ⊕ V)) := by
    intro a b hab
    exact Sum.inl.inj hab
  -- `Sym2.map` reflects equality because `Sum.inl` is injective.
  exact Subtype.ext ((Sym2.map.injective hinl) hvals)

/-- Helper for Theorem 4.24: the upper-copy edge constructor on source edges is injective. -/
private lemma doubleCoverUpperEdge_injective :
    Function.Injective (doubleCoverUpperEdge (G := G)) := by
  intro e₁ e₂ h
  have hvals :
      Sym2.map (fun x : V ↦ (Sum.inr x : V ⊕ V)) (e₁ : Sym2 V) =
        Sym2.map (fun x : V ↦ (Sum.inr x : V ⊕ V)) (e₂ : Sym2 V) := by
    -- Push the equality down to `Sym2` and rewrite both sides through the map description.
    have hcoe :
        (((doubleCoverUpperEdge (G := G) e₁ : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V))) =
          (((doubleCoverUpperEdge (G := G) e₂ : (doubleCoverGraph G).edgeSet) :
            Sym2 (V ⊕ V))) := by
      exact congrArg (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V))) h
    rw [coe_doubleCoverUpperEdge_eq_map, coe_doubleCoverUpperEdge_eq_map] at hcoe
    exact hcoe
  have hinr : Function.Injective (fun x : V ↦ (Sum.inr x : V ⊕ V)) := by
    intro a b hab
    exact Sum.inr.inj hab
  -- `Sym2.map` reflects equality because `Sum.inr` is injective.
  exact Subtype.ext ((Sym2.map.injective hinr) hvals)

/-- Helper for Theorem 4.24: the vertical edge constructor on source vertices is injective. -/
private lemma doubleCoverVerticalEdge_injective :
    Function.Injective (doubleCoverVerticalEdge (G := G)) := by
  intro v w h
  have hvals : s(Sum.inl v, Sum.inr v) = s(Sum.inl w, Sum.inr w) := by
    -- The named vertical edges are definitionally the mixed doubled edges.
    simpa [doubleCoverVerticalEdge] using
      congrArg (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V))) h
  rw [Sym2.eq_iff] at hvals
  rcases hvals with ⟨hleft, _⟩ | ⟨hswap, _⟩
  · exact Sum.inl.inj hleft
  · cases hswap

/-- Helper for Theorem 4.24: a lower horizontal doubled edge is incident to `Sum.inl v` exactly
when the source edge is incident to `v`. -/
private lemma mem_incidenceFinset_doubleCoverLowerEdge_left_iff
    (v : V) (e : G.edgeSet) :
    (doubleCoverLowerEdge (G := G) e : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inl v) ↔
      (e : Sym2 V) ∈ G.incidenceFinset v := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [coe_doubleCoverLowerEdge_eq_map]
  constructor
  · intro h
    rcases (Sym2.mem_map).1 h with ⟨w, hw, hwv⟩
    have hwv' : w = v := Sum.inl.inj hwv
    simpa [hwv'] using hw
  · intro h
    exact (Sym2.mem_map).2 ⟨v, h, rfl⟩

/-- Helper for Theorem 4.24: an upper horizontal doubled edge is never incident to `Sum.inl v`.
-/
private lemma mem_incidenceFinset_doubleCoverUpperEdge_left_iff
    (v : V) (e : G.edgeSet) :
    (doubleCoverUpperEdge (G := G) e : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inl v) ↔ False := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [coe_doubleCoverUpperEdge_eq_map]
  constructor
  · intro h
    rcases (Sym2.mem_map).1 h with ⟨w, -, hw⟩
    cases hw
  · intro h
    cases h

/-- Helper for Theorem 4.24: the vertical doubled edge above `w` is incident to `Sum.inl v`
exactly when `w = v`. -/
private lemma mem_incidenceFinset_doubleCoverVerticalEdge_left_iff
    (v w : V) :
    (doubleCoverVerticalEdge (G := G) w : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inl v) ↔
      w = v := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  change Sum.inl v ∈ s(Sum.inl w, Sum.inr w) ↔ w = v
  rw [Sym2.mem_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact (Sum.inl.inj h).symm
    · cases h
  · intro h
    subst h
    simp [Sym2.mem_iff]

/-- Helper for Theorem 4.24: a lower horizontal doubled edge is never incident to `Sum.inr v`.
-/
private lemma mem_incidenceFinset_doubleCoverLowerEdge_right_iff
    (v : V) (e : G.edgeSet) :
    (doubleCoverLowerEdge (G := G) e : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inr v) ↔ False := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [coe_doubleCoverLowerEdge_eq_map]
  constructor
  · intro h
    rcases (Sym2.mem_map).1 h with ⟨w, -, hw⟩
    cases hw
  · intro h
    cases h

/-- Helper for Theorem 4.24: an upper horizontal doubled edge is incident to `Sum.inr v` exactly
when the source edge is incident to `v`. -/
private lemma mem_incidenceFinset_doubleCoverUpperEdge_right_iff
    (v : V) (e : G.edgeSet) :
    (doubleCoverUpperEdge (G := G) e : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inr v) ↔
      (e : Sym2 V) ∈ G.incidenceFinset v := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  rw [coe_doubleCoverUpperEdge_eq_map]
  constructor
  · intro h
    rcases (Sym2.mem_map).1 h with ⟨w, hw, hwv⟩
    have hwv' : w = v := Sum.inr.inj hwv
    simpa [hwv'] using hw
  · intro h
    exact (Sym2.mem_map).2 ⟨v, h, rfl⟩

/-- Helper for Theorem 4.24: the vertical doubled edge above `w` is incident to `Sum.inr v`
exactly when `w = v`. -/
private lemma mem_incidenceFinset_doubleCoverVerticalEdge_right_iff
    (v w : V) :
    (doubleCoverVerticalEdge (G := G) w : Sym2 (V ⊕ V)) ∈
        (doubleCoverGraph G).incidenceFinset (Sum.inr v) ↔
      w = v := by
  rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  change Sum.inr v ∈ s(Sum.inl w, Sum.inr w) ↔ w = v
  rw [Sym2.mem_iff]
  constructor
  · intro h
    rcases h with h | h
    · cases h
    · exact (Sum.inr.inj h).symm
  · intro h
    subst h
    simp [Sym2.mem_iff]

/-- Helper for Theorem 4.24: the edges incident to `Sum.inl v` are exactly the lower horizontal
copies of the source edges incident to `v`, together with the vertical edge at `v`. -/
private lemma incidenceFinset_lower_eq_insert_image (v : V) :
    (Finset.univ.filter
      (fun e : (doubleCoverGraph G).edgeSet ↦
        (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset (Sum.inl v))) =
      insert (doubleCoverVerticalEdge (G := G) v)
        ((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
          (doubleCoverLowerEdge (G := G))) := by
  -- Compare both finsets pointwise using the doubled-edge classification.
  ext e
  constructor
  · intro he
    have heInc :
        (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset (Sum.inl v) :=
      (Finset.mem_filter.mp he).2
    rw [Finset.mem_insert, Finset.mem_image]
    rcases eq_doubleCoverLowerEdge_or_eq_doubleCoverUpperEdge_or_eq_doubleCoverVerticalEdge
        (G := G) e with
      (⟨e₀, rfl⟩ | ⟨e₀, rfl⟩ | ⟨w, rfl⟩)
    · right
      refine ⟨e₀, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (mem_incidenceFinset_doubleCoverLowerEdge_left_iff (G := G) v e₀).1 heInc
    · exact False.elim
        ((mem_incidenceFinset_doubleCoverUpperEdge_left_iff (G := G) v e₀).1 heInc)
    · left
      have hw : w = v :=
        (mem_incidenceFinset_doubleCoverVerticalEdge_left_iff (G := G) v w).1 heInc
      subst hw
      rfl
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (mem_incidenceFinset_doubleCoverVerticalEdge_left_iff (G := G) v v).2 rfl
    · rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
      have he₀Inc : (e₀ : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he₀).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
      rw [coe_doubleCoverLowerEdge_eq_map]
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] at he₀Inc
      exact (Sym2.mem_map).2 ⟨v, he₀Inc, rfl⟩

/-- Helper for Theorem 4.24: the edges incident to `Sum.inr v` are exactly the upper horizontal
copies of the source edges incident to `v`, together with the vertical edge at `v`. -/
private lemma incidenceFinset_upper_eq_insert_image (v : V) :
    (Finset.univ.filter
      (fun e : (doubleCoverGraph G).edgeSet ↦
        (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset (Sum.inr v))) =
      insert (doubleCoverVerticalEdge (G := G) v)
        ((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
          (doubleCoverUpperEdge (G := G))) := by
  -- Compare both finsets pointwise using the doubled-edge classification.
  ext e
  constructor
  · intro he
    have heInc :
        (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset (Sum.inr v) :=
      (Finset.mem_filter.mp he).2
    rw [Finset.mem_insert, Finset.mem_image]
    rcases eq_doubleCoverLowerEdge_or_eq_doubleCoverUpperEdge_or_eq_doubleCoverVerticalEdge
        (G := G) e with
      (⟨e₀, rfl⟩ | ⟨e₀, rfl⟩ | ⟨w, rfl⟩)
    · exact False.elim
        ((mem_incidenceFinset_doubleCoverLowerEdge_right_iff (G := G) v e₀).1 heInc)
    · right
      refine ⟨e₀, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (mem_incidenceFinset_doubleCoverUpperEdge_right_iff (G := G) v e₀).1 heInc
    · left
      have hw : w = v :=
        (mem_incidenceFinset_doubleCoverVerticalEdge_right_iff (G := G) v w).1 heInc
      subst hw
      rfl
  · intro he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (mem_incidenceFinset_doubleCoverVerticalEdge_right_iff (G := G) v v).2 rfl
    · rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
      have he₀Inc : (e₀ : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he₀).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
      rw [coe_doubleCoverUpperEdge_eq_map]
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] at he₀Inc
      exact (Sym2.mem_map).2 ⟨v, he₀Inc, rfl⟩

/-- Helper for Theorem 4.24: the vertical edge at `v` is not one of the lower horizontal copies
appearing in the lower-incidence decomposition. -/
private lemma doubleCoverVerticalEdge_not_mem_lowerImage (v : V) :
    doubleCoverVerticalEdge (G := G) v ∉
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
        (doubleCoverLowerEdge (G := G)) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨e, -, heq⟩
  have hval :
      ((doubleCoverLowerEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        s(Sum.inl v, Sum.inr v) := by
    -- Translate the image equality to the underlying unordered pairs.
    simpa [doubleCoverVerticalEdge] using
      congrArg (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V))) heq
  have hmemRight : Sum.inr v ∈ Sym2.map Sum.inl (e : Sym2 V) := by
    -- The vertical edge contains `Sum.inr v`, so the equal lower edge would as well.
    rw [← coe_doubleCoverLowerEdge_eq_map (G := G) e, hval]
    simp [Sym2.mem_iff]
  rcases (Sym2.mem_map).1 hmemRight with ⟨w, -, hw⟩
  cases hw

/-- Helper for Theorem 4.24: the vertical edge at `v` is not one of the upper horizontal copies
appearing in the upper-incidence decomposition. -/
private lemma doubleCoverVerticalEdge_not_mem_upperImage (v : V) :
    doubleCoverVerticalEdge (G := G) v ∉
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
        (doubleCoverUpperEdge (G := G)) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨e, -, heq⟩
  have hval :
      ((doubleCoverUpperEdge (G := G) e : (doubleCoverGraph G).edgeSet) : Sym2 (V ⊕ V)) =
        s(Sum.inl v, Sum.inr v) := by
    -- Translate the image equality to the underlying unordered pairs.
    simpa [doubleCoverVerticalEdge] using
      congrArg (fun z : (doubleCoverGraph G).edgeSet ↦ (z : Sym2 (V ⊕ V))) heq
  have hmemLeft : Sum.inl v ∈ Sym2.map Sum.inr (e : Sym2 V) := by
    -- The vertical edge contains `Sum.inl v`, so the equal upper edge would as well.
    rw [← coe_doubleCoverUpperEdge_eq_map (G := G) e, hval]
    simp [Sym2.mem_iff]
  rcases (Sym2.mem_map).1 hmemLeft with ⟨w, -, hw⟩
  cases hw

/-- Helper for Theorem 4.24: every doubled vertex sees total incident weight `1` under the named
double-cover lift. -/
private lemma doubleCoverLift_incidenceSum_eq_one
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    ∀ w : V ⊕ V,
      (Finset.univ.filter
        fun e : (doubleCoverGraph G).edgeSet ↦
          (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset w).sum
            (doubleCoverLift (G := G) x) = 1 := by
  intro w
  cases w with
  | inl v =>
      rw [incidenceFinset_lower_eq_insert_image (G := G) v]
      rw [Finset.sum_insert (doubleCoverVerticalEdge_not_mem_lowerImage (G := G) v)]
      have hImageSum :
          (((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
              (doubleCoverLowerEdge (G := G))).sum (doubleCoverLift (G := G) x)) =
            sourceIncidenceSum (G := G) x v := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl ?_
          intro e he
          exact doubleCoverLift_lowerEdge (G := G) x e
        · intro e he e' he' hEq
          exact doubleCoverLowerEdge_injective (G := G) hEq
      -- The lower horizontal weights contribute the source incidence sum, and the vertical edge
      -- contributes the residual slack.
      calc
        doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v) +
            ((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
              (doubleCoverLowerEdge (G := G))).sum (doubleCoverLift (G := G) x) =
          (1 - sourceIncidenceSum (G := G) x v) + sourceIncidenceSum (G := G) x v := by
            rw [doubleCoverLift_verticalEdge, hImageSum]
        _ = 1 := by ring
  | inr v =>
      rw [incidenceFinset_upper_eq_insert_image (G := G) v]
      rw [Finset.sum_insert (doubleCoverVerticalEdge_not_mem_upperImage (G := G) v)]
      have hImageSum :
          (((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
              (doubleCoverUpperEdge (G := G))).sum (doubleCoverLift (G := G) x)) =
            sourceIncidenceSum (G := G) x v := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl ?_
          intro e he
          exact doubleCoverLift_upperEdge (G := G) x e
        · intro e he e' he' hEq
          exact doubleCoverUpperEdge_injective (G := G) hEq
      -- The upper horizontal weights contribute the source incidence sum, and the vertical edge
      -- contributes the residual slack.
      calc
        doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v) +
            ((Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).image
              (doubleCoverUpperEdge (G := G))).sum (doubleCoverLift (G := G) x) =
          (1 - sourceIncidenceSum (G := G) x v) + sourceIncidenceSum (G := G) x v := by
            rw [doubleCoverLift_verticalEdge, hImageSum]
        _ = 1 := by ring

/-- Helper for Theorem 4.24: the doubled lift is coordinatewise nonnegative because horizontal
coordinates reuse `x`, while each vertical coordinate is the residual slack in a degree
inequality of `matchingConstraintSet G`. -/
private lemma doubleCoverLift_nonneg
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    ∀ e : (doubleCoverGraph G).edgeSet, 0 ≤ doubleCoverLift (G := G) x e := by
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, -⟩
  intro e
  rcases eq_doubleCoverLowerEdge_or_eq_doubleCoverUpperEdge_or_eq_doubleCoverVerticalEdge
      (G := G) e with
    (⟨e₀, rfl⟩ | ⟨e₀, rfl⟩ | ⟨v, rfl⟩)
  · -- Lower horizontal coordinates are copied directly from the source vector.
    rw [doubleCoverLift_lowerEdge]
    exact hx_nonneg e₀
  · -- Upper horizontal coordinates are copied directly from the source vector.
    rw [doubleCoverLift_upperEdge]
    exact hx_nonneg e₀
  · -- Vertical coordinates are residual slacks in the source degree inequalities.
    rw [doubleCoverLift_verticalEdge]
    have hdeg := matchingConstraintSetIncidentSum_le_one (G := G) hx v
    simpa [sourceIncidenceSum] using sub_nonneg.mpr hdeg

/-- Helper for Theorem 4.24: summing the vertical coordinates of the doubled lift over a source
vertex set produces the textbook `|T| - 2 x(E[T]) - x(δ(T))` expression. -/
private lemma doubleCoverLift_verticalSum_eq
    (x : G.edgeSet → ℝ) (T : Set V) :
    Finset.sum T.toFinite.toFinset
      (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) =
        (T.ncard : ℝ) - 2 * (E[G] T).sum x - (δ[G] T).sum x := by
  -- Rewrite each vertical coordinate to the residual slack `1 - sourceIncidenceSum`.
  calc
    Finset.sum T.toFinite.toFinset
        (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) =
      Finset.sum T.toFinite.toFinset (fun v ↦ (1 : ℝ) - sourceIncidenceSum (G := G) x v) := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        rw [doubleCoverLift_verticalEdge]
    _ = (T.ncard : ℝ) -
          Finset.sum T.toFinite.toFinset (fun v ↦ sourceIncidenceSum (G := G) x v) := by
        rw [Finset.sum_sub_distrib]
        simp [Set.ncard_eq_toFinset_card']
    _ = (T.ncard : ℝ) - (2 * (E[G] T).sum x + (δ[G] T).sum x) := by
        congr 1
        simpa [sourceIncidenceSum, Set.toFinite_toFinset] using
          sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) T x
    _ = (T.ncard : ℝ) - 2 * (E[G] T).sum x - (δ[G] T).sum x := by
        ring

/-- Helper for Theorem 4.24: the vertices of an odd doubled set split into the source vertices
with exactly one copy in the set, together with paired source vertices whose two copies both lie
in the set. -/
private lemma doubleCoverSplitCard_eq
    (Utilde : Set (V ⊕ V)) :
    Utilde.ncard =
      ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard +
        2 * ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard := by
  let F : Finset (V ⊕ V) := Utilde.toFinite.toFinset
  let L : Finset V := Finset.univ.filter fun v : V ↦ Sum.inl v ∈ Utilde
  let R : Finset V := Finset.univ.filter fun v : V ↦ Sum.inr v ∈ Utilde
  let U : Finset V := Finset.univ.filter
    fun v : V ↦ (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)
  let T : Finset V := Finset.univ.filter
    fun v : V ↦ Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde
  let isLower : V ⊕ V → Prop := fun w ↦ ∃ v : V, w = Sum.inl v
  let inlEmb : V ↪ V ⊕ V := ⟨Sum.inl, by
    intro a b h
    exact Sum.inl.inj h⟩
  let inrEmb : V ↪ V ⊕ V := ⟨Sum.inr, by
    intro a b h
    exact Sum.inr.inj h⟩
  have hleftFilter :
      Finset.filter isLower F = Finset.map inlEmb L := by
    -- The lower-copy points of `Utilde` are exactly the `Sum.inl` image of the left source set.
    ext w
    cases w with
    | inl v =>
        constructor
        · intro hw
          refine Finset.mem_map.2 ⟨v, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa [F] using (Finset.mem_filter.mp hw).1
        · intro hmap
          rcases Finset.mem_map.mp hmap with ⟨a, ha, haEq⟩
          have ha' : a = v := Sum.inl.inj haEq
          subst ha'
          refine Finset.mem_filter.mpr ⟨?_, by simp [isLower]⟩
          simpa [F] using (Finset.mem_filter.mp ha).2
    | inr v =>
        constructor
        · intro hw
          rcases (Finset.mem_filter.mp hw).2 with ⟨a, ha⟩
          cases ha
        · intro hmap
          rcases Finset.mem_map.mp hmap with ⟨a, -, haEq⟩
          cases haEq
  have hrightFilter :
      Finset.filter (fun w : V ⊕ V ↦ ¬ isLower w) F = Finset.map inrEmb R := by
    -- The complement of the lower-copy points is the upper-copy image.
    ext w
    cases w with
    | inl v =>
        constructor
        · intro hw
          exact False.elim ((Finset.mem_filter.mp hw).2 ⟨v, rfl⟩)
        · intro hmap
          rcases Finset.mem_map.mp hmap with ⟨a, -, haEq⟩
          cases haEq
    | inr v =>
        constructor
        · intro hw
          refine Finset.mem_map.2 ⟨v, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa [F] using (Finset.mem_filter.mp hw).1
        · intro hmap
          rcases Finset.mem_map.mp hmap with ⟨a, ha, haEq⟩
          have ha' : a = v := Sum.inr.inj haEq
          subst ha'
          exact Finset.mem_filter.mpr
            ⟨by simpa [F] using (Finset.mem_filter.mp ha).2, by simp [isLower]⟩
  have hpartition :
      Finset.filter isLower F ∪ Finset.filter (fun w : V ⊕ V ↦ ¬ isLower w) F = F := by
    -- Every vertex of the doubled graph is either a lower copy or an upper copy.
    ext w
    by_cases hw : isLower w
    · simp [hw]
    · simp [hw]
  have hcardLR : F.card = L.card + R.card := by
    have hdisj :
        Disjoint (Finset.filter isLower F)
          (Finset.filter (fun w : V ⊕ V ↦ ¬ isLower w) F) := by
      exact Finset.disjoint_filter_filter_not F F isLower
    calc
      F.card = (Finset.filter isLower F ∪ Finset.filter (fun w : V ⊕ V ↦ ¬ isLower w) F).card := by
        rw [hpartition]
      _ = (Finset.filter isLower F).card +
            (Finset.filter (fun w : V ⊕ V ↦ ¬ isLower w) F).card := by
        rw [Finset.card_union]
        rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
        simp
      _ = (Finset.map inlEmb L).card + (Finset.map inrEmb R).card := by
        rw [hleftFilter, hrightFilter]
      _ = L.card + R.card := by
        simp
  have hcardUT : L.card + R.card = U.card + 2 * T.card := by
    -- Count each source vertex by the number of its two copies lying in `Utilde`.
    calc
      L.card + R.card =
          (∑ v ∈ Finset.univ, if Sum.inl v ∈ Utilde then 1 else 0) +
            ∑ v ∈ Finset.univ, if Sum.inr v ∈ Utilde then 1 else 0 := by
              dsimp [L, R]
              rw [Finset.card_filter, Finset.card_filter]
      _ =
          ∑ v ∈ Finset.univ,
            ((if Sum.inl v ∈ Utilde then 1 else 0) +
              (if Sum.inr v ∈ Utilde then 1 else 0)) := by
              rw [← Finset.sum_add_distrib]
      _ =
          ∑ v ∈ Finset.univ,
            ((if (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde) then 1 else 0) +
              2 * (if Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde then 1 else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              by_cases hL : Sum.inl v ∈ Utilde <;> by_cases hR : Sum.inr v ∈ Utilde <;>
                norm_num [hL, hR]
      _ =
          (∑ v ∈ Finset.univ,
            if (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde) then 1 else 0) +
            ∑ v ∈ Finset.univ,
              2 * (if Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ =
          (∑ v ∈ Finset.univ,
            if (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde) then 1 else 0) +
            2 * (∑ v ∈ Finset.univ,
              if Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde then 1 else 0) := by
              rw [← Finset.mul_sum]
      _ = U.card + 2 * T.card := by
        rw [show U.card =
            ∑ v ∈ Finset.univ, if (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde) then 1 else 0 by
              dsimp [U]
              rw [Finset.card_filter]]
        rw [show T.card =
            ∑ v ∈ Finset.univ, if Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde then 1 else 0 by
              dsimp [T]
              rw [Finset.card_filter]]
  have hUcard :
      ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard = U.card := by
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext v
    simp [U]
  have hTcard :
      ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard = T.card := by
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext v
    simp [T]
  -- Combine the doubled-vertex partition with the pointwise source-vertex count identity.
  calc
    Utilde.ncard = F.card := by
      simp [F, Set.ncard_eq_toFinset_card']
    _ = L.card + R.card := hcardLR
    _ = U.card + 2 * T.card := hcardUT
    _ = ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard +
          2 * ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard := by
      rw [← hUcard, ← hTcard]

/-- Helper for Theorem 4.24: if a doubled vertex set has odd cardinality, then the source
vertices with exactly one copy in that set also have odd cardinality. -/
private lemma odd_sourceSplitSet_of_doubleCoverOdd
    (Utilde : Set (V ⊕ V)) (hOdd : Odd Utilde.ncard) :
    Odd ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard := by
  rcases hOdd with ⟨k, hk⟩
  refine ⟨k - ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard, ?_⟩
  -- The paired source vertices contribute an even term, so the split set inherits odd parity.
  have hsplit :
      ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard +
          2 * ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard =
        2 * k + 1 := by
    calc
      ({v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}).ncard +
          2 * ({v : V | Sum.inl v ∈ Utilde ∧ Sum.inr v ∈ Utilde}).ncard =
        Utilde.ncard := by
          rw [doubleCoverSplitCard_eq (Utilde := Utilde)]
      _ = 2 * k + 1 := hk
  omega

/-- Helper for Theorem 4.24: a source cut edge for the split set contributes to at least one
horizontal doubled cut edge. -/
private lemma horizontalCutWitness_of_sourceSplitCut
    (Utilde : Set (V ⊕ V)) (e : G.edgeSet) :
    let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
    e ∈ δ[G] U →
      doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde ∨
        doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde := by
  intro U hcut
  -- Rewrite the source cut and both doubled cuts to pure endpoint-membership propositions.
  rw [memCutEdgeFinsetEndpointsIff (G := G) (S := U) (e := e)] at hcut
  rw [mem_cutEdgeFinset_doubleCoverLowerEdge_iff (G := G) Utilde e]
  rw [mem_cutEdgeFinset_doubleCoverUpperEdge_iff (G := G) Utilde e]
  dsimp [U] at hcut ⊢
  by_cases h₁l : Sum.inl e.1.out.1 ∈ Utilde <;>
    by_cases h₁r : Sum.inr e.1.out.1 ∈ Utilde <;>
    by_cases h₂l : Sum.inl e.1.out.2 ∈ Utilde <;>
    by_cases h₂r : Sum.inr e.1.out.2 ∈ Utilde <;>
    simp [h₁l, h₁r, h₂l, h₂r] at hcut ⊢

/-- Helper for Theorem 4.24: the two horizontal doubled cut indicators dominate the source cut
indicator for the split-vertex set `U := {v | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}`. -/
private lemma doubleCoverHorizontalCutWeight_ge_sourceCutWeight
    (Utilde : Set (V ⊕ V)) {x : G.edgeSet → ℝ}
    (hx_nonneg : ∀ e : G.edgeSet, 0 ≤ x e) (e : G.edgeSet) :
    let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
    (if doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0) +
        (if doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0) ≥
      if e ∈ δ[G] U then x e else 0 := by
  let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
  change
    (if e ∈ δ[G] U then x e else 0) ≤
      (if doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0) +
        (if doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0)
  -- Route correction: the arithmetic comparison is now reduced to the boolean cut witness above.
  by_cases hcut : e ∈ δ[G] U
  ·
    have hWitness :
        e ∈ δ[G] U →
          doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde ∨
            doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde := by
      simpa [U] using
        (horizontalCutWitness_of_sourceSplitCut (G := G) (Utilde := Utilde) (e := e))
    rcases hWitness hcut with
      hlower | hupper
    · by_cases hupperCut : doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde
      · have hxsum : x e ≤ x e + x e := by
          linarith [hx_nonneg e]
        simpa [hcut, hlower, hupperCut, add_comm, add_left_comm, add_assoc] using hxsum
      · simp [hcut, hlower, hupperCut]
    · by_cases hlowerCut : doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde
      · have hxsum : x e ≤ x e + x e := by
          linarith [hx_nonneg e]
        simpa [hcut, hlowerCut, hupper, add_comm, add_left_comm, add_assoc] using hxsum
      · simp [hcut, hlowerCut, hupper]
  · have hcut' :
        e ∉ δ[G] {v : V | ¬(Sum.inl v ∈ Utilde ↔ Sum.inr v ∈ Utilde)} := by
      simpa [U] using hcut
    by_cases hlowerCut : doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde
    · by_cases hupperCut : doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde
      · have hxsum : 0 ≤ x e + x e := by
          linarith [hx_nonneg e]
        simpa [hcut, hcut', hlowerCut, hupperCut, add_comm, add_left_comm, add_assoc] using hxsum
      · simpa [hcut, hcut', hlowerCut, hupperCut] using hx_nonneg e
    · by_cases hupperCut : doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde
      · simpa [hcut, hcut', hlowerCut, hupperCut] using hx_nonneg e
      · simp [hcut, hcut', hlowerCut, hupperCut]

/-- Helper for Theorem 4.24: once the doubled lift satisfies the doubled matching constraints and
the doubled degree equations, the generic Chapter 4.23 upgrade turns it into a point of
`perfectMatchingConstraintSet (doubleCoverGraph G)`. -/
private lemma doubleCoverLift_mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
    {x : G.edgeSet → ℝ}
    (hxMatch : doubleCoverLift (G := G) x ∈ matchingConstraintSet (doubleCoverGraph G))
    (hx_deg : ∀ w : V ⊕ V,
      (Finset.univ.filter
        fun e : (doubleCoverGraph G).edgeSet ↦
          (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset w).sum
            (doubleCoverLift (G := G) x) = 1) :
    doubleCoverLift (G := G) x ∈ perfectMatchingConstraintSet (doubleCoverGraph G) := by
  -- This is exactly the generic matching-to-perfect upgrade, specialized to the doubled graph.
  exact
    mem_perfectMatchingConstraintSet_of_mem_matchingConstraintSet_of_incidenceEqOne
      (G := doubleCoverGraph G) (x := doubleCoverLift (G := G) x) hxMatch (by
        intro w
        simpa using hx_deg w)

/-- Helper for Theorem 4.24: the doubled cut across `Utilde` dominates the source cut across the
split-set `U := {v | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}` together with the vertical
cut edges above `U`. -/
private lemma doubleCoverCutWeight_ge_sourceCutAddSplitVertical
    (Utilde : Set (V ⊕ V)) {x : G.edgeSet → ℝ}
    (hx_nonneg : ∀ e : G.edgeSet, 0 ≤ x e) :
    let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
    (δ[doubleCoverGraph G] Utilde).sum (doubleCoverLift (G := G) x) ≥
      (δ[G] U).sum x +
        Finset.sum U.toFinite.toFinset
          (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) := by
  let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
  change
    (δ[doubleCoverGraph G] Utilde).sum (doubleCoverLift (G := G) x) ≥
      (δ[G] U).sum x +
        Finset.sum U.toFinite.toFinset
          (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v))
  let lowerCutEdges : Finset (doubleCoverGraph G).edgeSet :=
    (Finset.univ.filter fun e : G.edgeSet ↦
      doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).image
        (doubleCoverLowerEdge (G := G))
  let upperCutEdges : Finset (doubleCoverGraph G).edgeSet :=
    (Finset.univ.filter fun e : G.edgeSet ↦
      doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).image
        (doubleCoverUpperEdge (G := G))
  let verticalCutEdges : Finset (doubleCoverGraph G).edgeSet :=
    (Finset.univ.filter fun v : V ↦
      doubleCoverVerticalEdge (G := G) v ∈ δ[doubleCoverGraph G] Utilde).image
        (doubleCoverVerticalEdge (G := G))
  have hLowerUpperDisj : Disjoint lowerCutEdges upperCutEdges := by
    -- Lower and upper horizontal copies live on different sides of the doubled graph.
    rw [Finset.disjoint_left]
    intro de hdeLower hdeUpper
    rcases Finset.mem_image.mp hdeLower with ⟨eLower, -, hdeLowerEq⟩
    rcases Finset.mem_image.mp hdeUpper with ⟨eUpper, -, hdeUpperEq⟩
    have hEq :
        doubleCoverLowerEdge (G := G) eLower = doubleCoverUpperEdge (G := G) eUpper :=
      hdeLowerEq.trans hdeUpperEq.symm
    have hmem :
        Sum.inl eLower.1.out.1 ∈
          Sym2.map (fun v : V ↦ (Sum.inr v : V ⊕ V)) (eUpper : Sym2 V) := by
      rw [← coe_doubleCoverUpperEdge_eq_map (G := G) eUpper]
      rw [← hEq]
      rw [coe_doubleCoverLowerEdge_eq_map (G := G) eLower]
      exact (Sym2.mem_map).2 ⟨eLower.1.out.1, Sym2.out_fst_mem _, rfl⟩
    rcases (Sym2.mem_map).1 hmem with ⟨w, -, hw⟩
    cases hw
  have hLowerVerticalDisj : Disjoint lowerCutEdges verticalCutEdges := by
    -- A lower horizontal edge cannot be a mixed vertical edge.
    rw [Finset.disjoint_left]
    intro de hdeLower hdeVertical
    rcases Finset.mem_image.mp hdeLower with ⟨eLower, -, hdeLowerEq⟩
    rcases Finset.mem_image.mp hdeVertical with ⟨v, -, hdeVerticalEq⟩
    have hEq :
        doubleCoverLowerEdge (G := G) eLower = doubleCoverVerticalEdge (G := G) v :=
      hdeLowerEq.trans hdeVerticalEq.symm
    have hmem :
        Sum.inr v ∈ Sym2.map (fun w : V ↦ (Sum.inl w : V ⊕ V)) (eLower : Sym2 V) := by
      rw [← coe_doubleCoverLowerEdge_eq_map (G := G) eLower]
      rw [hEq]
      simp [doubleCoverVerticalEdge, Sym2.mem_iff]
    rcases (Sym2.mem_map).1 hmem with ⟨w, -, hw⟩
    cases hw
  have hUpperVerticalDisj : Disjoint upperCutEdges verticalCutEdges := by
    -- An upper horizontal edge cannot be a mixed vertical edge.
    rw [Finset.disjoint_left]
    intro de hdeUpper hdeVertical
    rcases Finset.mem_image.mp hdeUpper with ⟨eUpper, -, hdeUpperEq⟩
    rcases Finset.mem_image.mp hdeVertical with ⟨v, -, hdeVerticalEq⟩
    have hEq :
        doubleCoverUpperEdge (G := G) eUpper = doubleCoverVerticalEdge (G := G) v :=
      hdeUpperEq.trans hdeVerticalEq.symm
    have hmem :
        Sum.inl v ∈ Sym2.map (fun w : V ↦ (Sum.inr w : V ⊕ V)) (eUpper : Sym2 V) := by
      rw [← coe_doubleCoverUpperEdge_eq_map (G := G) eUpper]
      rw [hEq]
      simp [doubleCoverVerticalEdge, Sym2.mem_iff]
    rcases (Sym2.mem_map).1 hmem with ⟨w, -, hw⟩
    cases hw
  have hLowerUpperVerticalDisj : Disjoint (lowerCutEdges ∪ upperCutEdges) verticalCutEdges := by
    rw [Finset.disjoint_left]
    intro de hdeHorizontal hdeVertical
    rcases Finset.mem_union.mp hdeHorizontal with hdeLower | hdeUpper
    · exact (Finset.disjoint_left.1 hLowerVerticalDisj) hdeLower hdeVertical
    · exact (Finset.disjoint_left.1 hUpperVerticalDisj) hdeUpper hdeVertical
  have hCutPartition :
      δ[doubleCoverGraph G] Utilde = (lowerCutEdges ∪ upperCutEdges) ∪ verticalCutEdges := by
    -- Every doubled cut edge is lower, upper, or vertical by the global doubled-edge
    -- classification.
    ext de
    constructor
    · intro hde
      rcases eq_doubleCoverLowerEdge_or_eq_doubleCoverUpperEdge_or_eq_doubleCoverVerticalEdge
          (G := G) de with
        (⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨v, rfl⟩)
      · refine Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl ?_
        exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hde⟩, rfl⟩
      · refine Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr ?_
        exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hde⟩, rfl⟩
      · refine Finset.mem_union.mpr <| Or.inr ?_
        exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hde⟩, rfl⟩
    · intro hde
      rcases Finset.mem_union.mp hde with hdeHorizontal | hdeVertical
      · rcases Finset.mem_union.mp hdeHorizontal with hdeLower | hdeUpper
        · rcases Finset.mem_image.mp hdeLower with ⟨e, he, hEq⟩
          have hcut :
              doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde :=
            (Finset.mem_filter.mp he).2
          simpa [hEq] using hcut
        · rcases Finset.mem_image.mp hdeUpper with ⟨e, he, hEq⟩
          have hcut :
              doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde :=
            (Finset.mem_filter.mp he).2
          simpa [hEq] using hcut
      · rcases Finset.mem_image.mp hdeVertical with ⟨v, hv, hEq⟩
        have hcut :
            doubleCoverVerticalEdge (G := G) v ∈ δ[doubleCoverGraph G] Utilde :=
          (Finset.mem_filter.mp hv).2
        simpa [hEq] using hcut
  have hLowerSum :
      lowerCutEdges.sum (doubleCoverLift (G := G) x) =
        (Finset.univ.filter fun e : G.edgeSet ↦
          doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x := by
    -- Each lower horizontal cut edge contributes the source coordinate on the same source edge.
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro e he
      rw [doubleCoverLift_lowerEdge]
    · intro e he e' he' hEq
      exact doubleCoverLowerEdge_injective (G := G) hEq
  have hUpperSum :
      upperCutEdges.sum (doubleCoverLift (G := G) x) =
        (Finset.univ.filter fun e : G.edgeSet ↦
          doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x := by
    -- Each upper horizontal cut edge contributes the same source coordinate.
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro e he
      rw [doubleCoverLift_upperEdge]
    · intro e he e' he' hEq
      exact doubleCoverUpperEdge_injective (G := G) hEq
  have hVerticalSum :
      verticalCutEdges.sum (doubleCoverLift (G := G) x) =
        (Finset.univ.filter fun v : V ↦
          doubleCoverVerticalEdge (G := G) v ∈ δ[doubleCoverGraph G] Utilde).sum
          (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) := by
    -- The vertical part keeps the original mixed-edge coordinates.
    rw [Finset.sum_image]
    · intro v hv w hw hEq
      exact doubleCoverVerticalEdge_injective (G := G) hEq
  have hVerticalFilter :
      (Finset.univ.filter fun v : V ↦
        doubleCoverVerticalEdge (G := G) v ∈ δ[doubleCoverGraph G] Utilde) =
        U.toFinite.toFinset := by
    -- The vertical cut edges are exactly the source vertices with exactly one chosen copy.
    ext v
    simp [U, mem_cutEdgeFinset_doubleCoverVerticalEdge_iff]
  have hHorizontalBound :
      (δ[G] U).sum x ≤
        (Finset.univ.filter fun e : G.edgeSet ↦
          doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x +
        (Finset.univ.filter fun e : G.edgeSet ↦
          doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x := by
    -- Sum the pointwise horizontal dominance inequality over the source edge set.
    calc
      (δ[G] U).sum x = ∑ e : G.edgeSet, if e ∈ δ[G] U then x e else 0 := by
        symm
        simpa using
          (edgeSetSumIteEqSumFilter (G := G) (p := fun e : G.edgeSet ↦ e ∈ δ[G] U) x)
      _ ≤ ∑ e : G.edgeSet,
            ((if doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0) +
              (if doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde then x e else 0)) := by
          refine Finset.sum_le_sum ?_
          intro e he
          simpa [U] using
            (doubleCoverHorizontalCutWeight_ge_sourceCutWeight
              (G := G) (Utilde := Utilde) (hx_nonneg := hx_nonneg) (e := e))
      _ =
          (Finset.univ.filter fun e : G.edgeSet ↦
            doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x +
          (Finset.univ.filter fun e : G.edgeSet ↦
            doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x := by
          rw [Finset.sum_add_distrib]
          rw [edgeSetSumIteEqSumFilter (G := G)
            (p := fun e : G.edgeSet ↦
              doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde) x]
          rw [edgeSetSumIteEqSumFilter (G := G)
            (p := fun e : G.edgeSet ↦
              doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde) x]
  -- Assemble the exact lower/upper/vertical cut partition and compare the horizontal part to the
  -- source cut.
  calc
    (δ[doubleCoverGraph G] Utilde).sum (doubleCoverLift (G := G) x) =
        lowerCutEdges.sum (doubleCoverLift (G := G) x) +
          upperCutEdges.sum (doubleCoverLift (G := G) x) +
            verticalCutEdges.sum (doubleCoverLift (G := G) x) := by
          rw [hCutPartition]
          rw [Finset.sum_union hLowerUpperVerticalDisj]
          rw [Finset.sum_union hLowerUpperDisj]
    _ =
        (Finset.univ.filter fun e : G.edgeSet ↦
          doubleCoverLowerEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x +
          (Finset.univ.filter fun e : G.edgeSet ↦
            doubleCoverUpperEdge (G := G) e ∈ δ[doubleCoverGraph G] Utilde).sum x +
            Finset.sum U.toFinite.toFinset
              (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) := by
          rw [hLowerSum, hUpperSum, hVerticalSum, hVerticalFilter]
    _ ≥
        (δ[G] U).sum x +
          Finset.sum U.toFinite.toFinset
            (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) := by
          linarith [hHorizontalBound]

/-- Helper for Theorem 4.24: every odd doubled vertex set cuts at least one unit of the lifted
weight. -/
private lemma doubleCoverLift_cutLowerBound_of_odd
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G)
    (Utilde : Set (V ⊕ V)) (hOdd : Odd Utilde.ncard) :
    1 ≤ (δ[doubleCoverGraph G] Utilde).sum (doubleCoverLift (G := G) x) := by
  let U : Set V := {v : V | (Sum.inl v ∈ Utilde) ≠ (Sum.inr v ∈ Utilde)}
  rcases (SimpleGraph.mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
    ⟨hx_nonneg, -, hx_odd⟩
  have hUOdd : Odd U.ncard := by
    simpa [U] using odd_sourceSplitSet_of_doubleCoverOdd Utilde hOdd
  have hSourceOdd :
      (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2 := hx_odd U hUOdd
  have hCutDom :
      (δ[G] U).sum x +
          Finset.sum U.toFinite.toFinset
            (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) ≤
        (δ[doubleCoverGraph G] Utilde).sum (doubleCoverLift (G := G) x) := by
    simpa [U] using
      (doubleCoverCutWeight_ge_sourceCutAddSplitVertical
        (G := G) (Utilde := Utilde) (x := x) hx_nonneg)
  have hSourceBound :
      1 ≤
        (δ[G] U).sum x +
          Finset.sum U.toFinite.toFinset
            (fun v ↦ doubleCoverLift (G := G) x (doubleCoverVerticalEdge (G := G) v)) := by
    -- Rewrite the vertical contribution to the textbook `|U| - 2 x(E[U]) - x(δ(U))` formula.
    rw [doubleCoverLift_verticalSum_eq (G := G) x U]
    linarith
  linarith

/-- Helper for Theorem 4.24: the local doubled-cover cut package already proves that the lifted
point satisfies the perfect-matching constraints of the doubled graph. -/
private lemma doubleCoverLift_mem_perfectMatchingConstraintSetAux
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    doubleCoverLift (G := G) x ∈ perfectMatchingConstraintSet (doubleCoverGraph G) := by
  have hnonneg : ∀ e : (doubleCoverGraph G).edgeSet, 0 ≤ doubleCoverLift (G := G) x e :=
    doubleCoverLift_nonneg (G := G) hx
  have hdeg :
      ∀ w : V ⊕ V,
        (Finset.univ.filter
          fun e : (doubleCoverGraph G).edgeSet ↦
            (e : Sym2 (V ⊕ V)) ∈ (doubleCoverGraph G).incidenceFinset w).sum
              (doubleCoverLift (G := G) x) = 1 :=
    doubleCoverLift_incidenceSum_eq_one (G := G) hx
  rw [SimpleGraph.mem_perfectMatchingConstraintSet_iff]
  refine ⟨hnonneg, ?_, ?_⟩
  · intro w
    simpa using hdeg w
  intro Utilde hOdd
  -- The odd-cut lower bound is exactly the remaining doubled perfect-feasibility condition.
  exact doubleCoverLift_cutLowerBound_of_odd (G := G) hx Utilde hOdd

/-- Helper for Theorem 4.24: the doubled lift of a point in `matchingConstraintSet G` again
satisfies the matching constraints on the doubled graph. -/
private lemma doubleCoverLift_mem_matchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    doubleCoverLift (G := G) x ∈ matchingConstraintSet (doubleCoverGraph G) := by
  -- Forget the doubled perfect-matching degree equations down to ordinary matching constraints.
  exact mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := doubleCoverGraph G)
    (doubleCoverLift_mem_perfectMatchingConstraintSetAux (G := G) hx)

/-- Helper for Theorem 4.24: once the doubled matching constraints are proved locally, the
existing Chapter 4.23 upgrade turns them into doubled perfect-matching constraints. -/
private lemma doubleCoverLift_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    doubleCoverLift (G := G) x ∈ perfectMatchingConstraintSet (doubleCoverGraph G) := by
  -- Reuse the local perfect-feasibility package instead of rebuilding the doubled argument.
  exact doubleCoverLift_mem_perfectMatchingConstraintSetAux (G := G) hx

/-- Helper for Theorem 4.24: once the doubled perfect-constraint bridge
`perfectMatchingConstraintSet (doubleCoverGraph G) ⊆ perfectMatchingPolytope (doubleCoverGraph G)`
is available, the doubled lift of any `x ∈ matchingConstraintSet G` already lands in the doubled
perfect matching polytope. -/
private lemma doubleCoverLift_mem_perfectMatchingPolytope_of_perfectConstraintBridge
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G)
    (hbridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G)) :
    doubleCoverLift (G := G) x ∈ perfectMatchingPolytope (doubleCoverGraph G) := by
  -- The doubled-cover work in this file stops at perfect-matching constraints; the remaining step
  -- is exactly the Chapter 4.23 owner bridge on the doubled graph.
  exact hbridge (doubleCoverLift_mem_perfectMatchingConstraintSet (G := G) hx)

/-- Helper for Theorem 4.24: lower-copy adjacency in a doubled subgraph projects to adjacency in
the original graph. -/
private lemma lowerCopySubgraphAdj_sub {M : (doubleCoverGraph G).Subgraph} {u v : V}
    (h : M.Adj (Sum.inl u) (Sum.inl v)) :
    G.Adj u v := by
  simpa [doubleCoverGraph, doubleCoverAdj] using M.adj_sub h

/-- Helper for Theorem 4.24: the lower copy of a doubled subgraph is a subgraph of `G`. -/
private def lowerCopySubgraph (M : (doubleCoverGraph G).Subgraph) : G.Subgraph :=
  { verts := {v : V | ∃ w : V, M.Adj (Sum.inl v) (Sum.inl w)}
    Adj := fun u v ↦ M.Adj (Sum.inl u) (Sum.inl v)
    adj_sub := fun h ↦ lowerCopySubgraphAdj_sub (G := G) (M := M) h
    edge_vert := fun h ↦ ⟨_, h⟩
    symm := fun _ _ h ↦ M.symm h }

/-- Helper for Theorem 4.24: projecting a matching on the doubled graph to the lower copy keeps
the matching property. -/
private lemma lowerCopySubgraph_isMatching_of_isMatching
    {M : (doubleCoverGraph G).Subgraph} (hM : M.IsMatching) :
    (lowerCopySubgraph (G := G) M).IsMatching := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  have hv_mem : Sum.inl v ∈ M.verts := by
    exact Subgraph.mem_verts_of_mem_edge (Subgraph.mem_edgeSet.2 hvw) (by simp)
  obtain ⟨q, hvq, huniq⟩ := hM hv_mem
  refine ⟨w, hvw, ?_⟩
  intro w' hw'
  have hwq : Sum.inl w' = q := huniq _ hw'
  have hwq' : Sum.inl w = q := huniq _ hvw
  exact Sum.inl.inj (hwq.trans hwq'.symm)

/-- Helper for Theorem 4.24: evaluating a doubled subgraph incidence vector on a lower horizontal
edge is exactly the source incidence coordinate of the projected lower-copy subgraph. -/
private lemma lowerCopySubgraph_subgraphIncidenceVector_lowerEdge
    (M : (doubleCoverGraph G).Subgraph) (e : G.edgeSet) :
    (doubleCoverGraph G).subgraphIncidenceVector ℝ M (doubleCoverLowerEdge (G := G) e) =
      G.subgraphIncidenceVector ℝ (lowerCopySubgraph (G := G) M) e := by
  -- Both sides are the `0/1` indicator of the same lower-horizontal edge membership.
  by_cases h :
      (doubleCoverLowerEdge (G := G) e).1 ∈ M.edgeSet
  · have hLower : e.1 ∈ (lowerCopySubgraph (G := G) M).edgeSet := by
      rw [← e.1.out_eq, Subgraph.mem_edgeSet]
      simpa [lowerCopySubgraph, doubleCoverLowerEdge] using h
    simp [SimpleGraph.subgraphIncidenceVector, h, hLower]
  · have hLower : e.1 ∉ (lowerCopySubgraph (G := G) M).edgeSet := by
      rw [← e.1.out_eq, Subgraph.mem_edgeSet]
      simpa [lowerCopySubgraph, doubleCoverLowerEdge] using h
    simp [SimpleGraph.subgraphIncidenceVector, h, hLower]

/-- Helper for Theorem 4.24: any convex decomposition of `doubleCoverLift x` by perfect matchings
of the doubled graph projects to a convex decomposition of `x` by matchings of `G`. -/
private lemma mem_matchingPolytope_of_mem_doubleCoverLift_perfectMatchingPolytope
    {x : G.edgeSet → ℝ}
    (hxDouble : doubleCoverLift (G := G) x ∈ perfectMatchingPolytope (doubleCoverGraph G)) :
    x ∈ matchingPolytope G := by
  rw [SimpleGraph.perfectMatchingPolytope, mem_convexHull_iff_exists_fintype] at hxDouble
  rcases hxDouble with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hz_sum⟩
  have hz' :
      ∀ i, ∃ M : (doubleCoverGraph G).Subgraph,
        M.IsPerfectMatching ∧ z i = (doubleCoverGraph G).subgraphIncidenceVector ℝ M := by
    intro i
    simpa using hz i
  choose M hM hVec using hz'
  let zLower : ι → G.edgeSet → ℝ :=
    fun i ↦ G.subgraphIncidenceVector ℝ (lowerCopySubgraph (G := G) (M i))
  have hz_sum_lower : ∑ i, w i • zLower i = x := by
    -- Compare the projected barycenter at each source edge with the doubled barycenter on the
    -- corresponding lower horizontal edge.
    ext e
    calc
      (∑ i, w i • zLower i) e =
          (∑ i, w i • z i) (doubleCoverLowerEdge (G := G) e) := by
            calc
              (∑ i, w i • zLower i) e =
                  ∑ i, w i * zLower i e := by
                    simp [zLower, Pi.smul_apply, smul_eq_mul]
              _ =
                  ∑ i,
                    w i *
                      ((doubleCoverGraph G).subgraphIncidenceVector ℝ (M i)
                        (doubleCoverLowerEdge (G := G) e)) := by
                          refine Finset.sum_congr rfl ?_
                          intro i hi
                          rw [lowerCopySubgraph_subgraphIncidenceVector_lowerEdge
                            (G := G) (M := M i) e]
              _ = ∑ i, w i * z i (doubleCoverLowerEdge (G := G) e) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    rw [hVec i]
              _ = (∑ i, w i • z i) (doubleCoverLowerEdge (G := G) e) := by
                    simp [Pi.smul_apply, smul_eq_mul]
      _ = doubleCoverLift (G := G) x (doubleCoverLowerEdge (G := G) e) := by
            simpa using congrFun hz_sum (doubleCoverLowerEdge (G := G) e)
      _ = x e := doubleCoverLift_lowerEdge (G := G) x e
  rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype]
  refine ⟨ι, inferInstance, w, zLower, hw_nonneg, hw_sum, ?_, hz_sum_lower⟩
  intro i
  refine ⟨lowerCopySubgraph (G := G) (M i), ?_, rfl⟩
  -- Projecting a doubled perfect matching to the lower copy preserves the matching property.
  exact lowerCopySubgraph_isMatching_of_isMatching (G := G) (M := M i) (hM i).1

/-- Helper for Theorem 4.24: any equality
`perfectMatchingPolytope H = perfectMatchingConstraintSet H` immediately yields the reverse
inclusion `perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H`. -/
private lemma perfectMatchingConstraintSet_subset_perfectMatchingPolytope_of_eq
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hEq : perfectMatchingPolytope H = perfectMatchingConstraintSet H) :
    perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H := by
  intro y hy
  -- Rewrite the target owner through the equality theorem and keep the original membership.
  rw [hEq]
  exact hy

/-- Helper for Theorem 4.24: any bridge
`matchingConstraintSet H ⊆ matchingPolytope H` upgrades perfect-matching constraints to the
perfect-matching polytope. -/
private lemma perfectMatchingConstraintSet_subset_perfectMatchingPolytope_of_matchingConstraintBridge
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hMatchingBridge : matchingConstraintSet H ⊆ matchingPolytope H) :
    perfectMatchingConstraintSet H ⊆ perfectMatchingPolytope H := by
  intro y hy
  -- First forget the perfect degree equalities down to ordinary matching constraints.
  have hyMatching : y ∈ matchingConstraintSet H :=
    mem_matchingConstraintSet_of_mem_perfectMatchingConstraintSet (G := H) hy
  -- Then combine the matching-polytope bridge with the local perfect-upgrade lemma.
  exact
    perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
      (G := H) (hMatchingBridge hyMatching) hy

/-- Helper for Theorem 4.24: specializing the doubled perfect-matching equality theorem produces
exactly the doubled reverse inclusion consumed by the projection argument. -/
private lemma doubleCoverPerfectConstraintSet_subset_polytope_of_eq
    (hEqDouble :
      perfectMatchingPolytope (doubleCoverGraph G) =
        perfectMatchingConstraintSet (doubleCoverGraph G)) :
    perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
      perfectMatchingPolytope (doubleCoverGraph G) := by
  -- Specialize the generic equality-to-subset bridge at the doubled graph.
  exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope_of_eq
    (H := doubleCoverGraph G) hEqDouble

/-- Helper for Theorem 4.24: once the perfect-matching theorem is available on the doubled graph,
the existing doubled-feasibility package upgrades a source matching-constraint point to the doubled
perfect-matching polytope. -/
private lemma doubleCoverLift_mem_perfectMatchingPolytope_of_perfectPolytopeEq
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G)
    (hEq :
      perfectMatchingPolytope (doubleCoverGraph G) =
        perfectMatchingConstraintSet (doubleCoverGraph G)) :
    doubleCoverLift (G := G) x ∈ perfectMatchingPolytope (doubleCoverGraph G) := by
  -- First turn the equality theorem into the required doubled perfect-constraint bridge.
  have hdoubleBridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G) :=
    doubleCoverPerfectConstraintSet_subset_polytope_of_eq (G := G) hEq
  -- Then feed that bridge into the already-verified doubled-cover feasibility theorem.
  simpa using
    doubleCoverLift_mem_perfectMatchingPolytope_of_perfectConstraintBridge
      (G := G) (x := x) hx hdoubleBridge

/-- Helper for Theorem 4.24: the doubled-cover projection only needs the reverse inclusion
`perfectMatchingConstraintSet (doubleCoverGraph G) ⊆ perfectMatchingPolytope (doubleCoverGraph G)`;
the full equality theorem is stronger than necessary. -/
private lemma mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectBridge
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G)
    (hdoubleBridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G)) :
    x ∈ matchingPolytope G := by
  let xDouble : (doubleCoverGraph G).edgeSet → ℝ := doubleCoverLift (G := G) x
  have hxDouble_poly : xDouble ∈ perfectMatchingPolytope (doubleCoverGraph G) := by
    -- The local doubled-cover package already lands in doubled perfect constraints; the only
    -- upstream input still needed is the bridge into the doubled perfect-matching polytope.
    simpa [xDouble] using
      doubleCoverLift_mem_perfectMatchingPolytope_of_perfectConstraintBridge
        (G := G) (x := x) hx hdoubleBridge
  -- Project the doubled perfect-matching decomposition back along the lower copy of `G`.
  simpa [xDouble] using
    mem_matchingPolytope_of_mem_doubleCoverLift_perfectMatchingPolytope
      (G := G) (x := x) hxDouble_poly

/-- Helper for Theorem 4.24: once the doubled graph satisfies the perfect-matching polytope
theorem, the entire doubled-cover argument is complete and projects back to `matchingPolytope G`.
-/
private lemma mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectEq
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G)
    (hEqDouble :
      perfectMatchingPolytope (doubleCoverGraph G) =
        perfectMatchingConstraintSet (doubleCoverGraph G)) :
    x ∈ matchingPolytope G := by
  -- First weaken the doubled equality theorem to the only bridge consumed by the projection step.
  have hdoubleBridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G) :=
    doubleCoverPerfectConstraintSet_subset_polytope_of_eq (G := G) hEqDouble
  -- Then invoke the bridge-based projection lemma.
  exact mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectBridge
    (G := G) hx hdoubleBridge

/-- Helper for Theorem 4.24: the doubled-cover projection only needs the reverse inclusion
`perfectMatchingConstraintSet (doubleCoverGraph G) ⊆ perfectMatchingPolytope (doubleCoverGraph G)`
at the doubled graph. -/
private lemma matchingConstraintSet_subset_matchingPolytope_of_doubleCoverPerfectBridge
    (hdoubleBridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G)) :
    matchingConstraintSet G ⊆ matchingPolytope G := by
  intro x hx
  -- Apply the already-assembled doubled-cover projection to each feasible source point.
  exact mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectBridge
    (G := G) hx hdoubleBridge

/-- Helper for Theorem 4.24: the remaining hard step is to classify nonintegral extreme points of
`matchingConstraintSet G` via the blossom/tight-odd-set contraction route. -/
private lemma mem_matchingPolytope_of_mem_matchingConstraintSet_viaDoubleCover
    {x : G.edgeSet → ℝ} (hx : x ∈ matchingConstraintSet G) :
    x ∈ matchingPolytope G := by
  -- Route correction: now that Theorem 4.23 exports the perfect-constraint reverse inclusion
  -- acyclically, the doubled-cover step reduces to one specialization of that theorem.
  have hdoubleBridge :
      perfectMatchingConstraintSet (doubleCoverGraph G) ⊆
        perfectMatchingPolytope (doubleCoverGraph G) := by
    -- Specialize Theorem 4.23 at the doubled graph and reuse its reverse inclusion directly.
    exact perfectMatchingConstraintSet_subset_perfectMatchingPolytope
      (G := doubleCoverGraph G)
  -- Once the doubled reverse inclusion is available, the existing projection lemma closes the
  -- matching-polytope membership without reopening any local doubled-cover combinatorics.
  exact mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectBridge
    (G := G) hx hdoubleBridge

/-- Helper for Theorem 4.24: once the direct doubled-graph bridge is available, the nonintegral
extreme-point case is immediate from `extremePoints_subset`. -/
private lemma mem_matchingPolytope_of_mem_extremePoints_matchingConstraintSet_of_not_integer
    {x : G.edgeSet → ℝ}
    (hx : x ∈ (matchingConstraintSet G).extremePoints ℝ)
    (_hxNotInt : x ∉ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ matchingPolytope G := by
  -- The compact/extreme-point skeleton only needs a feasible-point-to-polytope bridge here.
  exact mem_matchingPolytope_of_mem_matchingConstraintSet_viaDoubleCover
    (G := G) (extremePoints_subset hx)

/-- Helper for Theorem 4.24: the reverse inclusion is reduced to the compact/extreme-point bridge,
leaving only the nonintegral extreme-point classification frontier. -/
private lemma matchingConstraintSet_subset_matchingPolytope :
    matchingConstraintSet G ⊆ matchingPolytope G := by
  exact matchingConstraintSet_subset_matchingPolytope_of_nonintegerExtremeBridge
    (G := G)
    (fun hx hxNotInt ↦
      mem_matchingPolytope_of_mem_extremePoints_matchingConstraintSet_of_not_integer
        (G := G) hx hxNotInt)

/-- Helper for Theorem 4.24: every matching generator should satisfy the degree and odd-set
inequalities, so the whole matching polytope lies in `matchingConstraintSet G`. -/
private lemma matchingPolytope_subset_matchingConstraintSet :
    matchingPolytope G ⊆ matchingConstraintSet G := by
  rw [SimpleGraph.matchingPolytope]
  -- The convex hull stays in the feasible owner once every matching generator is feasible.
  refine convexHull_min ?_ (convexMatchingConstraintSet (G := G))
  rintro x ⟨M, hM, rfl⟩
  exact subgraphIncidenceVector_mem_matchingConstraintSet_of_isMatching (G := G) hM

/-- Helper for Theorem 4.24: once the doubled graph satisfies the perfect-matching polytope
theorem, every feasible point of `matchingConstraintSet G` projects to `matchingPolytope G`. -/
private lemma matchingConstraintSet_subset_matchingPolytope_of_doubleCoverPerfectEq
    (hEqDouble :
      perfectMatchingPolytope (doubleCoverGraph G) =
        perfectMatchingConstraintSet (doubleCoverGraph G)) :
    matchingConstraintSet G ⊆ matchingPolytope G := by
  intro x hx
  -- Package the doubled-cover projection at subset level so later consumers only need the
  -- doubled equality theorem itself.
  exact mem_matchingPolytope_of_mem_matchingConstraintSet_of_doubleCoverPerfectEq
    (G := G) hx hEqDouble

/-- Helper for Theorem 4.24: once the doubled graph satisfies the perfect-matching polytope
theorem, the doubled-cover projection gives the full matching-polytope theorem for `G`. -/
private lemma matchingPolytope_eq_matchingConstraintSet_of_doubleCoverPerfectEq
    (hEqDouble :
      perfectMatchingPolytope (doubleCoverGraph G) =
        perfectMatchingConstraintSet (doubleCoverGraph G)) :
    matchingPolytope G = matchingConstraintSet G := by
  refine le_antisymm ?_ ?_
  · -- The forward inclusion is independent of the doubled-cover reduction.
    exact matchingPolytope_subset_matchingConstraintSet (G := G)
  · -- Reuse the subset-level projection bridge to avoid duplicating the doubled-cover wiring.
    exact matchingConstraintSet_subset_matchingPolytope_of_doubleCoverPerfectEq
      (G := G) hEqDouble

/-- Theorem 4.24 (Matching Polytope Theorem). The matching polytope of a finite graph `G` is
exactly the set of edge-vectors that are nonnegative and satisfy the degree inequalities and the
odd-set inequalities. -/
theorem matchingPolytope_eq_matchingConstraintSet :
    matchingPolytope G = matchingConstraintSet G := by
  refine le_antisymm ?_ ?_
  · -- The forward inclusion is the generator-feasibility half of the theorem.
    exact matchingPolytope_subset_matchingConstraintSet (G := G)
  · -- Route correction: the reverse inclusion is organized through compact convexity and extreme
    -- points, isolating the remaining contraction step in a single helper lemma.
    exact matchingConstraintSet_subset_matchingPolytope (G := G)

end Theorem_4_24

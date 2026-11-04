/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_2.ch4_sec4_2_theorem_4_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_corollary_4_19.Cuts
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4.ch4_sec4_4_theorem_4_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

-- Semantic search note: `lean_leansearch` was unavailable in this runner; this file reuses the
-- canonical Chapter 4.18 owner `SimpleGraph.edgeIncMatrix`, together with
-- `SimpleGraph.Subgraph.IsMatching` and `SimpleGraph.Subgraph.IsPerfectMatching`.

namespace SimpleGraph

section Corollary_4_19

universe u

variable {V : Type u}
variable (G : SimpleGraph V)

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- The `0,1` incidence vector of a subgraph of `G`, viewed in the edge coordinates of `G` with
values in `R`. -/
def subgraphIncidenceVector (R : Type*) [Zero R] [One R] (M : G.Subgraph) : G.edgeSet → R :=
  fun e ↦ if e.1 ∈ M.edgeSet then 1 else 0

/-- The matching polytope of `G`, defined as the convex hull of the incidence vectors of the
matchings of `G`. -/
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M}

/-- The perfect matching polytope of `G`, defined as the convex hull of the incidence vectors of
the perfect matchings of `G`. -/
def perfectMatchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = G.subgraphIncidenceVector ℝ M}

section Finite

variable [Fintype V]

/-- The edges of the induced subgraph on `U`, regarded as a finset of edge coordinates of `G`. -/
def inducedEdgeFinset (U : Set V) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ (e : Sym2 V) ∈ ((⊤ : G.Subgraph).induce U).edgeSet

/-- The induced edge set `E[G] U` in the edge coordinates of `G`. -/
notation "E[" G "] " U:arg => inducedEdgeFinset G U

/-- An edge-coordinate belongs to `E[G] U` exactly when it lies in the induced subgraph on `U`. -/
theorem mem_inducedEdgeFinset_iff {U : Set V} {e : G.edgeSet} :
    e ∈ E[G] U ↔ (e : Sym2 V) ∈ ((⊤ : G.Subgraph).induce U).edgeSet := by
  simp [inducedEdgeFinset]

/-- The degree/odd-set description of the matching polytope of `G`. -/
def matchingConstraintSet : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
      (∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1) ∧
      ∀ U : Set V, Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2}

/-- A point belongs to `matchingConstraintSet G` exactly when it satisfies the nonnegativity,
degree, and odd-set inequalities. -/
theorem mem_matchingConstraintSet_iff {x : G.edgeSet → ℝ} :
    x ∈ matchingConstraintSet G ↔
      (∀ e, 0 ≤ x e) ∧
      (∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x ≤ 1) ∧
      (∀ U : Set V, Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2) := Iff.rfl

/-- The degree/odd-cut description of the perfect matching polytope of `G`. -/
def perfectMatchingConstraintSet : Set (G.edgeSet → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧
      (∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1) ∧
      ∀ S : Set V, Odd S.ncard → 1 ≤ (δ[G] S).sum x}

/-- A point belongs to `perfectMatchingConstraintSet G` exactly when it satisfies the
nonnegativity inequalities, the degree equations, and the odd-cut inequalities. -/
theorem mem_perfectMatchingConstraintSet_iff {x : G.edgeSet → ℝ} :
    x ∈ perfectMatchingConstraintSet G ↔
      (∀ e, 0 ≤ x e) ∧
      (∀ v : V,
        (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x = 1) ∧
      (∀ S : Set V, Odd S.ncard → 1 ≤ (δ[G] S).sum x) := Iff.rfl

/-- Helper for Corollary 4.19: evaluating `A_G x` at a vertex is the incidence-filter sum at that
vertex. -/
private lemma edgeIncMatrix_mulVec_apply
    (x : G.edgeSet → ℝ) (v : V) :
    ((G.edgeIncMatrix ℝ).mulVec x) v =
      (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x := by
  -- Expand the restricted incidence matrix and rewrite each entry as a `0/1` indicator.
  rw [SimpleGraph.edgeIncMatrix, Matrix.mulVec, dotProduct, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro e he
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · simp [G.incMatrix_of_mem_incidenceSet (R := ℝ) h, h]
  · simp [G.incMatrix_of_notMem_incidenceSet (R := ℝ) h, h]

/-- Helper for Corollary 4.19: reindex native edge-coordinate vectors by the canonical
enumeration of `G.edgeSet`. -/
private noncomputable def graphEdgeCoordinates
    (x : G.edgeSet → ℝ) : Fin (Nat.card G.edgeSet) → ℝ :=
  fun j ↦ x ((Finite.equivFin G.edgeSet).symm j)

/-- Helper for Corollary 4.19: the inverse coordinate reindexing sends `Fin`-indexed vectors back
to the native `G.edgeSet` coordinates. -/
private noncomputable abbrev graphEdgeCoordinateReindex :
    (Fin (Nat.card G.edgeSet) → ℝ) ≃ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Finite.equivFin G.edgeSet)

/-- Helper for Corollary 4.19: evaluating the reindexed coordinate vector at an edge recovers the
corresponding finite coordinate. -/
@[simp] private theorem graphEdgeCoordinateReindex_apply
    (y : Fin (Nat.card G.edgeSet) → ℝ) (e : G.edgeSet) :
    graphEdgeCoordinateReindex (G := G) y e = y ((Finite.equivFin G.edgeSet) e) := by
  -- This is the defining formula of `LinearEquiv.funCongrLeft`.
  rw [graphEdgeCoordinateReindex, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

/-- Helper for Corollary 4.19: reindexing native edge coordinates to `Fin` and back is the
identity. -/
@[simp] private theorem graphEdgeCoordinateReindex_graphEdgeCoordinates
    (x : G.edgeSet → ℝ) :
    graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) = x := by
  -- This is the `apply_symm_apply` identity for the canonical coordinate equivalence.
  change graphEdgeCoordinateReindex (G := G)
      ((graphEdgeCoordinateReindex (G := G)).symm x) = x
  exact LinearEquiv.apply_symm_apply (graphEdgeCoordinateReindex (G := G)) x

/-- Helper for Corollary 4.19: reindexing integer lattice points along a coordinate equivalence
preserves the integer-point owner. -/
private theorem funCongrLeftSymmImage_integerPoints
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

/-- Helper for Corollary 4.19: coordinate reindexing commutes with intersections of ambient
function-space subsets. -/
private theorem funCongrLeftSymmImage_inter
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

/-- Helper for Corollary 4.19: transporting an integral `Fin`-indexed owner through the canonical
coordinate equivalence preserves integrality. -/
private theorem isIntegralFunCongrLeftSymmImage
    {α β : Type*} [Finite α] [Finite β] (e : α ≃ β)
    {P : Set (α → ℝ)} (hP : is_integral P) :
    is_integral ((LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P) := by
  rw [is_integral_iff] at hP ⊢
  calc
    (LinearEquiv.funCongrLeft ℝ ℝ e.symm) '' P =
        (LinearEquiv.funCongrLeft ℝ ℝ e.symm) ''
          convexHull ℝ (P ∩ Set.range (fun z : α → ℤ ↦ Int.cast ∘ z)) := by
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
          -- The image of the integral owner is exactly the reindexed integer lattice.
          rw [funCongrLeftSymmImage_inter, funCongrLeftSymmImage_integerPoints]

/-- Helper for Corollary 4.19: incidence vectors of subgraphs have nonnegative edge
coordinates. -/
private lemma subgraphIncidenceVector_nonneg (M : G.Subgraph) :
    ∀ e : G.edgeSet, 0 ≤ G.subgraphIncidenceVector ℝ M e := by
  intro e
  -- Each coordinate is an indicator value, so it is either `0` or `1`.
  by_cases h : e.1 ∈ M.edgeSet
  · simp [SimpleGraph.subgraphIncidenceVector, h]
  · simp [SimpleGraph.subgraphIncidenceVector, h]

/-- Helper for Corollary 4.19: the edges with at least one endpoint in `S`, regarded as a finset
of edge coordinates of `G`. -/
private def oddSetIncidentEdgeFinset (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e : G.edgeSet ↦ ∃ v ∈ S, (e : Sym2 V) ∈ G.incidenceFinset v

/-- Helper for Corollary 4.19: summing over `G.edgeSet` with an indicator `if` rewrites to the
corresponding filtered edge sum. -/
private lemma edgeSet_sum_ite_eq_sum_filter
    (p : G.edgeSet → Prop) [DecidablePred p] (f : G.edgeSet → ℝ) :
    (∑ e : G.edgeSet, if p e then f e else 0) = (Finset.univ.filter p).sum f := by
  -- This is the edge-coordinate version of `Finset.sum_filter`.
  rw [Finset.sum_filter]

/-- Helper for Corollary 4.19: the endpoint finset of an edge-coordinate is its unordered pair of
canonical `Sym2.out` endpoints. -/
private lemma edge_toFinset_eq_pair (e : G.edgeSet) :
    ((e : Sym2 V).toFinset) = {e.1.out.1, e.1.out.2} := by
  -- Rewrite the edge through its canonical `Sym2.out` endpoints.
  calc
    ((e : Sym2 V).toFinset) = (s(e.1.out.1, e.1.out.2)).toFinset := by
      simpa [e.1.out_eq]
    _ = {e.1.out.1, e.1.out.2} := Sym2.toFinset_mk_eq

/-- Helper for Corollary 4.19: filtering the two-point endpoint finset `{a, b}` by membership in
`S` has cardinality `2`, `1`, or `0` according as both, one, or none of the endpoints lie in `S`.
-/
private lemma pair_filter_card_of_ne
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

/-- Helper for Corollary 4.19: an induced edge is characterized by both canonical endpoints lying
in the chosen vertex set. -/
private lemma mem_inducedEdgeFinset_endpoints_iff
    (S : Set V) (e : G.edgeSet) :
    e ∈ E[G] S ↔ e.1.out.1 ∈ S ∧ e.1.out.2 ∈ S := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    have he : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
      simpa [e.1.out_eq] using e.prop
    exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he
  -- Rewrite induced-edge membership through the canonical endpoint presentation of `e`.
  rw [mem_inducedEdgeFinset_iff, ← e.1.out_eq, SimpleGraph.Subgraph.mem_edgeSet]
  simp [SimpleGraph.Subgraph.induce, hadj]

/-- Helper for Corollary 4.19: a cut edge is characterized by the two canonical endpoints lying on
opposite sides of the chosen vertex set. -/
private lemma mem_cutEdgeFinset_endpoints_iff
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

/-- Helper for Corollary 4.19: an induced edge cannot simultaneously lie in the cut of the same
vertex set. -/
private lemma not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset
    {S : Set V} {e : G.edgeSet} (he : e ∈ E[G] S) :
    e ∉ δ[G] S := by
  rcases (mem_inducedEdgeFinset_endpoints_iff (G := G) S e).1 he with ⟨h₁, h₂⟩
  intro hcut
  rcases (mem_cutEdgeFinset_endpoints_iff (G := G) S e).1 hcut with
    (⟨_, h₂'⟩ | ⟨_, h₁'⟩)
  · exact h₂' h₂
  · exact h₁' h₁

/-- Helper for Corollary 4.19: an edge belongs to `oddSetIncidentEdgeFinset S` exactly when one of
its two concrete endpoints lies in `S`. -/
private lemma mem_oddSetIncidentEdgeFinset_iff
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

/-- Helper for Corollary 4.19: an edge incident to `S` is either internal to `S` or crosses the
cut of `S`. -/
private lemma mem_oddSetIncidentEdgeFinset_iff_mem_induced_or_cut
    (S : Finset V) (e : G.edgeSet) :
    e ∈ oddSetIncidentEdgeFinset (G := G) S ↔
      e ∈ E[G] (S : Set V) ∨ e ∈ δ[G] (S : Set V) := by
  constructor
  · intro he
    rcases (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).1 he with h₁ | h₂
    · by_cases h₂S : e.1.out.2 ∈ (S : Set V)
      · exact Or.inl <|
          (mem_inducedEdgeFinset_endpoints_iff (G := G) (S : Set V) e).2 ⟨h₁, h₂S⟩
      · exact Or.inr <|
          (mem_cutEdgeFinset_endpoints_iff (G := G) (S : Set V) e).2 (Or.inl ⟨h₁, h₂S⟩)
    · by_cases h₁S : e.1.out.1 ∈ (S : Set V)
      · exact Or.inl <|
          (mem_inducedEdgeFinset_endpoints_iff (G := G) (S : Set V) e).2 ⟨h₁S, h₂⟩
      · exact Or.inr <|
          (mem_cutEdgeFinset_endpoints_iff (G := G) (S : Set V) e).2 (Or.inr ⟨h₂, h₁S⟩)
  · intro he
    rcases he with hind | hcut
    · exact
        (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2
          (Or.inl ((mem_inducedEdgeFinset_endpoints_iff (G := G) (S : Set V) e).1 hind).1)
    · rcases (mem_cutEdgeFinset_endpoints_iff (G := G) (S : Set V) e).1 hcut with
        (⟨h₁, _⟩ | ⟨h₂, _⟩)
      · exact (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inl h₁)
      · exact (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inr h₂)

/-- Helper for Corollary 4.19: the edges incident to `S` split disjointly into the edges induced
by `S` and the cut edges of `S`. -/
private lemma oddSetIncidentEdgeFinset_sum_eq_induced_add_cut
    (S : Finset V) (x : G.edgeSet → ℝ) :
    (oddSetIncidentEdgeFinset (G := G) S).sum x =
      (E[G] (S : Set V)).sum x + (δ[G] (S : Set V)).sum x := by
  have hUnion :
      oddSetIncidentEdgeFinset (G := G) S = E[G] (S : Set V) ∪ δ[G] (S : Set V) := by
    ext e
    simp [mem_oddSetIncidentEdgeFinset_iff_mem_induced_or_cut]
  have hDisj : Disjoint (E[G] (S : Set V)) (δ[G] (S : Set V)) := by
    rw [Finset.disjoint_left]
    intro e he hind
    exact not_mem_cutEdgeFinset_of_mem_inducedEdgeFinset (G := G) he hind
  -- Split the incident-edge sum along the disjoint induced/cut partition.
  rw [hUnion, Finset.sum_union hDisj]

/-- Helper for Corollary 4.19: filtering the vertices of `S` that lie on an edge agrees with
filtering the endpoint finset of that edge by membership in `S`. -/
private lemma edge_filter_eq_endpoint_filter
    (S : Finset V) (e : G.edgeSet) :
    S.filter (fun v ↦ v ∈ (e : Sym2 V)) =
      ((e : Sym2 V).toFinset.filter fun v ↦ v ∈ (S : Set V)) := by
  -- Both sides describe the finite intersection `S ∩ ((e : Sym2 V).toFinset)`.
  ext v
  simpa [Finset.mem_filter, and_comm] using
    (show v ∈ S.filter (fun w ↦ w ∈ (e : Sym2 V)) ↔
      v ∈ ((e : Sym2 V).toFinset.filter fun w ↦ w ∈ (S : Set V)) by
        simp [Finset.mem_filter, Sym2.mem_toFinset])

/-- Helper for Corollary 4.19: the filtered endpoint cardinality of an edge is the sum of the
incident-edge indicator and the induced-edge indicator. -/
private lemma endpoint_filter_card_eq_incident_add_induced
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
  -- Compute the filtered endpoint cardinality by case-splitting on the two endpoints.
  rw [edge_toFinset_eq_pair (G := G) e, pair_filter_card_of_ne _ _ hne]
  by_cases h₁ : e.1.out.1 ∈ (S : Set V)
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff, mem_inducedEdgeFinset_endpoints_iff]
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff, mem_inducedEdgeFinset_endpoints_iff]
  · by_cases h₂ : e.1.out.2 ∈ (S : Set V)
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff, mem_inducedEdgeFinset_endpoints_iff]
    · norm_num [h₁, h₂, mem_oddSetIncidentEdgeFinset_iff, mem_inducedEdgeFinset_endpoints_iff]

/-- Helper for Corollary 4.19: summing the vertex-incidence equations on `S` counts each edge
incident to `S` once, plus one extra copy for each edge internal to `S`. -/
private lemma sumIncidenceOnFinset_eq_oddSetIncident_add_induced
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
          (fun e : G.edgeSet ↦ Finset.sum S (fun v ↦ if (e : Sym2 V) ∈ G.incidenceFinset v then x e else 0)) := by
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
          -- The filtered vertex set is exactly the filtered endpoint set of `e`.
          refine Finset.sum_congr rfl ?_
          intro e he
          have hfilter :
              S.filter (fun v ↦ (e : Sym2 V) ∈ G.incidenceFinset v) =
                S.filter (fun v ↦ v ∈ (e : Sym2 V)) := by
            ext v
            simp [G.edge_mem_incidenceSet_iff]
          rw [hfilter, edge_filter_eq_endpoint_filter (G := G) S e, Finset.sum_const]
          simp [nsmul_eq_mul]
    _ = ∑ e : G.edgeSet,
          (((if e ∈ oddSetIncidentEdgeFinset (G := G) S then 1 else 0) +
              if e ∈ E[G] (S : Set V) then 1 else 0) * x e) := by
          -- Replace the endpoint multiplicity by the incident-plus-induced decomposition.
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [endpoint_filter_card_eq_incident_add_induced (G := G) S e]
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
          · exact edgeSet_sum_ite_eq_sum_filter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ oddSetIncidentEdgeFinset (G := G) S) x
          · exact edgeSet_sum_ite_eq_sum_filter
              (G := G) (p := fun e : G.edgeSet ↦ e ∈ E[G] (S : Set V)) x
    _ = (oddSetIncidentEdgeFinset (G := G) S).sum x + (E[G] (S : Set V)).sum x := by
          simp

/-- Helper for Corollary 4.19: summing the incidence equations on `S` counts each internal edge
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
          simpa using sumIncidenceOnFinset_eq_oddSetIncident_add_induced (G := G) S.toFinset x
    _ = ((E[G] (S.toFinset : Set V)).sum x + (δ[G] (S.toFinset : Set V)).sum x) + (E[G] S).sum x := by
          rw [oddSetIncidentEdgeFinset_sum_eq_induced_add_cut (G := G) S.toFinset x]
    _ = ((E[G] S).sum x + (δ[G] S).sum x) + (E[G] S).sum x := by
          simp
    _ = 2 * (E[G] S).sum x + (δ[G] S).sum x := by
          ring

/-- Helper for Corollary 4.19: the induced-edge sum on `U` is bounded by either slice of a
compatible bipartition, because summing the degree bounds on that slice counts every induced edge
at least once. -/
private lemma inducedEdgeSum_le_bipartitionSlice
    {L R U : Set V} (hLR : G.IsBipartiteWith L R) {x : G.edgeSet → ℝ}
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1) :
    (E[G] U).sum x ≤ ((U ∩ L).ncard : ℝ) := by
  let S : Finset V := U.toFinset.filter fun v ↦ v ∈ L
  have hSset : (S : Set V) = U ∩ L := by
    -- The chosen finset slice is exactly the `U ∩ L` vertex set.
    ext v
    simp [S]
  have hsubset :
      E[G] U ⊆ oddSetIncidentEdgeFinset (G := G) S := by
    intro e he
    have hEnds : e.1.out.1 ∈ U ∧ e.1.out.2 ∈ U :=
      (mem_inducedEdgeFinset_endpoints_iff (G := G) U e).1 he
    have hadj : G.Adj e.1.out.1 e.1.out.2 := by
      have he' : s(e.1.out.1, e.1.out.2) ∈ G.edgeSet := by
        simpa [e.1.out_eq] using e.prop
      exact (SimpleGraph.mem_edgeSet (G := G) (v := e.1.out.1) (w := e.1.out.2)).1 he'
    -- Every induced edge has one endpoint in the chosen bipartition slice.
    rcases hLR.mem_of_adj hadj with hLeftRight | hRightLeft
    · refine (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inl ?_)
      rw [hSset]
      exact ⟨hEnds.1, hLeftRight.1⟩
    · refine (mem_oddSetIncidentEdgeFinset_iff (G := G) S e).2 (Or.inr ?_)
      rw [hSset]
      exact ⟨hEnds.2, hRightLeft.2⟩
  have hInduced_le_incident :
      (E[G] U).sum x ≤ (oddSetIncidentEdgeFinset (G := G) S).sum x := by
    -- Enlarging the edge owner preserves the sum because all edge weights are nonnegative.
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun e _ _ ↦ hx_nonneg e
  have hIncident_le_degreeSum :
      (oddSetIncidentEdgeFinset (G := G) S).sum x ≤
        Finset.sum S
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) :=
      by
        have hsplit := sumIncidenceOnFinset_eq_oddSetIncident_add_induced (G := G) S x
        have hnonneg_slice : 0 ≤ (E[G] ((S : Set V))).sum x := by
          -- The induced slice sum is nonnegative because each edge weight is nonnegative.
          exact Finset.sum_nonneg fun e _ ↦ hx_nonneg e
        linarith
  have hDegreeSum_le_card :
      Finset.sum S
        (fun v ↦
          (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) ≤
        ((U ∩ L).ncard : ℝ) := by
    calc
      Finset.sum S
          (fun v ↦
            (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) ≤
          Finset.sum S (fun _ ↦ (1 : ℝ)) := by
            -- Sum the pointwise row bounds over the chosen slice.
            refine Finset.sum_le_sum ?_
            intro v hv
            simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using hx_deg v
      _ = (S.card : ℝ) := by
            simp
      _ = (((S : Set V).ncard : ℕ) : ℝ) := by
            simp
      _ = ((U ∩ L).ncard : ℝ) := by
            rw [hSset]
  exact hInduced_le_incident.trans (hIncident_le_degreeSum.trans hDegreeSum_le_card)

/-- Helper for Corollary 4.19: on a bipartite graph, the odd-set inequalities follow from
nonnegativity and the incidence-matrix degree upper bounds. -/
private lemma bipartiteOddSetBound_of_degreeUpperBounds
    (hG : G.IsBipartite) {x : G.edgeSet → ℝ}
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1) :
    ∀ U : Set V, Odd U.ncard → (E[G] U).sum x ≤ ((U.ncard : ℝ) - 1) / 2 := by
  intro U hUodd
  rcases hG.exists_isBipartiteWith with ⟨L, R, hLR⟩
  -- Route correction: use the new slice bound twice and then finish with odd-cardinality
  -- arithmetic on the two bipartition slices of `U`.
  have hLeftSlice :
      (E[G] U).sum x ≤ ((U ∩ L).ncard : ℝ) :=
    inducedEdgeSum_le_bipartitionSlice (G := G) (L := L) (R := R) (U := U) hLR
      hx_nonneg hx_deg
  have hRightSlice :
      (E[G] U).sum x ≤ ((U ∩ R).ncard : ℝ) :=
    inducedEdgeSum_le_bipartitionSlice (G := G) (L := R) (R := L) (U := U) hLR.symm
      hx_nonneg hx_deg
  have hdisj : Disjoint (U ∩ L) (U ∩ R) := by
    -- The two slices are disjoint because the ambient bipartition is disjoint.
    rw [Set.disjoint_left]
    intro v hvL hvR
    exact (Set.disjoint_left.mp hLR.disjoint) hvL.2 hvR.2
  have hSliceSum :
      (U ∩ L).ncard + (U ∩ R).ncard ≤ U.ncard := by
    -- The two slices form a disjoint subset of `U`.
    calc
      (U ∩ L).ncard + (U ∩ R).ncard = ((U ∩ L) ∪ (U ∩ R)).ncard := by
        symm
        exact Set.ncard_union_eq hdisj
      _ ≤ U.ncard := by
        refine Set.ncard_le_ncard ?_
        intro v hv
        rcases hv with hv | hv
        · exact hv.1
        · exact hv.1
  have hMinNat : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ (U.ncard - 1) / 2 := by
    rcases hUodd with ⟨k, hk⟩
    have hSliceSum' : (U ∩ L).ncard + (U ∩ R).ncard ≤ 2 * k + 1 := by
      simpa [hk] using hSliceSum
    have hMinLe : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ k := by
      have hMinLeLeft : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ (U ∩ L).ncard :=
        Nat.min_le_left _ _
      have hMinLeRight : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ (U ∩ R).ncard :=
        Nat.min_le_right _ _
      omega
    simpa [hk] using hMinLe
  have hMinReal :
      (Nat.min (U ∩ L).ncard (U ∩ R).ncard : ℝ) ≤ ((U.ncard : ℝ) - 1) / 2 := by
    rcases hUodd with ⟨k, hk⟩
    have hMinLe : (Nat.min (U ∩ L).ncard (U ∩ R).ncard : ℝ) ≤ k := by
      have hMinLeNat : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ k := by
        have hSliceSum' : (U ∩ L).ncard + (U ∩ R).ncard ≤ 2 * k + 1 := by
          simpa [hk] using hSliceSum
        have hMinLeLeft : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ (U ∩ L).ncard :=
          Nat.min_le_left _ _
        have hMinLeRight : Nat.min (U ∩ L).ncard (U ∩ R).ncard ≤ (U ∩ R).ncard :=
          Nat.min_le_right _ _
        omega
      exact_mod_cast hMinLeNat
    have hkReal : ((U.ncard : ℝ) - 1) / 2 = k := by
      norm_num [hk]
    rw [hkReal]
    exact hMinLe
  have hMinSlice :
      (E[G] U).sum x ≤ (Nat.min (U ∩ L).ncard (U ∩ R).ncard : ℝ) := by
    -- The induced-edge sum is bounded by both slices, hence by their minimum.
    simpa [Nat.cast_min] using (le_min hLeftSlice hRightSlice)
  exact hMinSlice.trans hMinReal

/-- For a bipartite graph, the full matching constraint system reduces to its incidence-matrix
formulation. -/
theorem matchingConstraintSet_eq_setOf_mulVec_le_one
    (hG : G.IsBipartite) :
    matchingConstraintSet G = {x | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
  ext x
  constructor
  · intro hx
    rcases (mem_matchingConstraintSet_iff (G := G) (x := x)).1 hx with
      ⟨hx_nonneg, hx_deg, _⟩
    refine ⟨?_, hx_nonneg⟩
    intro v
    simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using hx_deg v
  · rintro ⟨hx_deg, hx_nonneg⟩
    refine (mem_matchingConstraintSet_iff (G := G) (x := x)).2 ?_
    refine ⟨hx_nonneg, ?_, ?_⟩
    · intro v
      simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using hx_deg v
    · intro U hUodd
      exact bipartiteOddSetBound_of_degreeUpperBounds (G := G) hG hx_nonneg hx_deg U hUodd

/-- For a bipartite graph, the full perfect-matching constraint system reduces to its
incidence-matrix formulation. -/
theorem perfectMatchingConstraintSet_eq_setOf_mulVec_eq_one
    (hG : G.IsBipartite) :
    perfectMatchingConstraintSet G = {x | (G.edgeIncMatrix ℝ).mulVec x = 1 ∧ ∀ e, 0 ≤ x e} :=
  by
    ext x
    constructor
    · intro hx
      rcases (mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).1 hx with
        ⟨hx_nonneg, hx_deg, hx_cut⟩
      refine ⟨?_, hx_nonneg⟩
      funext v
      -- Rewrite each degree equation as the corresponding incidence-matrix row equation.
      simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using hx_deg v
    · rintro ⟨hx_eq, hx_nonneg⟩
      refine (mem_perfectMatchingConstraintSet_iff (G := G) (x := x)).2 ?_
      refine ⟨hx_nonneg, ?_, ?_⟩
      · intro v
        -- Read the coordinatewise matrix equation back as the degree equation at `v`.
        simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using congrFun hx_eq v
      · intro S hSodd
        have hx_deg_le : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1 := by
          intro v
          -- Equality with the all-ones vector implies the weaker degree upper bound.
          simpa using le_of_eq (congrFun hx_eq v)
        have hinduced :
            (E[G] S).sum x ≤ ((S.ncard : ℝ) - 1) / 2 :=
          bipartiteOddSetBound_of_degreeUpperBounds (G := G) hG hx_nonneg hx_deg_le S hSodd
        have hsum_rows :
            Finset.sum S.toFinset
              (fun v ↦
                (Finset.univ.filter
                  fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
              (S.ncard : ℝ) := by
          -- Summing the degree equations over the odd set counts one unit at each vertex.
          calc
            Finset.sum S.toFinset
                (fun v ↦
                  (Finset.univ.filter
                    fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum x) =
                Finset.sum S.toFinset (fun _ : V ↦ (1 : ℝ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro v hv
                  simpa [edgeIncMatrix_mulVec_apply (G := G) x v] using congrFun hx_eq v
            _ = (S.toFinset.card : ℝ) := by simp
            _ = (S.ncard : ℝ) := by rw [← Set.ncard_eq_toFinset_card']
        have hcut :
            1 ≤ (δ[G] S).sum x := by
          -- Combine the row-sum decomposition with the odd-set upper bound on the induced edges.
          have hdecomp :=
            sumIncidenceOn_eq_twice_inducedEdgeSum_addCutSum (G := G) S x
          linarith
        exact hcut

/-- Helper for Corollary 4.19: every feasible edge coordinate is bounded above by `1`. -/
private lemma edge_coordinate_le_one_of_nonneg_mulVec_le_one
    {x : G.edgeSet → ℝ}
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1)
    (e : G.edgeSet) :
    x e ≤ 1 := by
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset e.1.out.1
  have heI : e ∈ I := by
    simp [I, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff,
      Sym2.out_fst_mem]
  have hsingle : x e ≤ I.sum x := by
    exact Finset.single_le_sum (fun f _ ↦ hx_nonneg f) heI
  have hsum_le : I.sum x ≤ 1 := by
    simpa [I, edgeIncMatrix_mulVec_apply (G := G) x e.1.out.1] using hx_deg e.1.out.1
  exact hsingle.trans hsum_le

/-- Helper for Corollary 4.19: an integral feasible edge coordinate is either `0` or `1`. -/
private lemma edge_coordinate_eq_zero_or_one_of_nonneg_mulVec_le_one_of_integer
    {x : G.edgeSet → ℝ}
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1)
    (e : G.edgeSet) :
    x e = 0 ∨ x e = 1 := by
  rcases hx_int with ⟨z, rfl⟩
  have hz_nonneg : (0 : ℤ) ≤ z e := by
    have hreal : (0 : ℝ) ≤ (z e : ℝ) := by simpa using hx_nonneg e
    exact_mod_cast hreal
  have hz_le_one : z e ≤ 1 := by
    have hreal : ((z e : ℝ) ≤ 1) := by
      simpa using edge_coordinate_le_one_of_nonneg_mulVec_le_one (G := G)
        (x := Int.cast ∘ z) hx_nonneg hx_deg e
    exact_mod_cast hreal
  have hz_cases : z e = 0 ∨ z e = 1 := by
    omega
  rcases hz_cases with hzero | hone
  · left
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hzero
  · right
    simpa using congrArg (fun n : ℤ ↦ (n : ℝ)) hone

/-- Helper for Corollary 4.19: the support subgraph of a `0,1` edge vector, with only the covered
vertices retained. -/
private abbrev integralSupportSubgraph (x : G.edgeSet → ℝ) : G.Subgraph where
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

/-- Helper for Corollary 4.19: adjacency in the support subgraph means the corresponding edge
coordinate is `1`. -/
private theorem integralSupportSubgraph_adj_iff (x : G.edgeSet → ℝ) {u v : V} :
    (integralSupportSubgraph (G := G) x).Adj u v ↔
      ∃ h : G.Adj u v, x ⟨s(u, v), G.mem_edgeSet.2 h⟩ = 1 := by
  rfl

/-- Helper for Corollary 4.19: an ambient edge lies in the support subgraph exactly when its
coordinate is `1`. -/
private lemma integralSupportSubgraph_mem_edgeSet_iff
    (x : G.edgeSet → ℝ) (e : G.edgeSet) :
    e.1 ∈ (integralSupportSubgraph (G := G) x).edgeSet ↔ x e = 1 := by
  have hadj : G.Adj e.1.out.1 e.1.out.2 := by
    rw [← G.mem_edgeSet]
    simpa [e.1.out_eq] using e.2
  rw [← e.1.out_eq, Subgraph.mem_edgeSet, integralSupportSubgraph_adj_iff]
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

/-- Helper for Corollary 4.19: every covered vertex of an integral feasible point has a unique
support neighbor. -/
private lemma existsUnique_supportNeighbor_of_nonneg_mulVec_le_one_of_integer
    {x : G.edgeSet → ℝ}
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1)
    {v : V} (hv : v ∈ (integralSupportSubgraph (G := G) x).verts) :
    ∃! w : V, (integralSupportSubgraph (G := G) x).Adj v w := by
  rcases hv with ⟨w, hAdj_vw⟩
  rcases hAdj_vw with ⟨hvw, hxe⟩
  let I : Finset G.edgeSet :=
    Finset.univ.filter fun f : G.edgeSet ↦ (f : Sym2 V) ∈ G.incidenceFinset v
  let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.2 hvw⟩
  have heI : e ∈ I := by
    simp [I, e, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  have hsum_le : x e + (I.erase e).sum x ≤ 1 := by
    calc
      x e + (I.erase e).sum x = I.sum x := by
        exact Finset.add_sum_erase I x heI
      _ ≤ 1 := by
        simpa [I, edgeIncMatrix_mulVec_apply (G := G) x v] using hx_deg v
  have hxe_one : x e = 1 := by
    simpa [e] using hxe
  refine ⟨w, ⟨hvw, hxe⟩, ?_⟩
  intro u hu
  rcases hu with ⟨hvu, hxf⟩
  let f : G.edgeSet := ⟨s(v, u), G.mem_edgeSet.2 hvu⟩
  have hfI : f ∈ I := by
    simp [I, f, SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff]
  by_contra hwu
  have hfe : f ≠ e := by
    intro hfeEq
    apply hwu
    have hs : s(v, u) = s(v, w) := by
      simpa [f, e] using congrArg Subtype.val hfeEq
    exact Sym2.congr_right.mp hs
  have hf_erase : f ∈ I.erase e := Finset.mem_erase.mpr ⟨hfe, hfI⟩
  have hsum_erase_ge_one : 1 ≤ (I.erase e).sum x := by
    have hsingle : x f ≤ (I.erase e).sum x := by
      exact Finset.single_le_sum (fun g _ ↦ hx_nonneg g) hf_erase
    calc
      1 = x f := by simpa [f] using hxf.symm
      _ ≤ (I.erase e).sum x := hsingle
  linarith

/-- Helper for Corollary 4.19: the support subgraph of an integral feasible point is a matching. -/
private lemma integralSupportSubgraph_isMatching_of_nonneg_mulVec_le_one_of_integer
    {x : G.edgeSet → ℝ}
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1) :
    (integralSupportSubgraph (G := G) x).IsMatching := by
  intro v hv
  -- The matching API asks for a unique support neighbor at each covered vertex.
  exact existsUnique_supportNeighbor_of_nonneg_mulVec_le_one_of_integer
    (G := G) hx_int hx_nonneg hx_deg hv

/-- Helper for Corollary 4.19: every integral feasible point is the incidence vector of a
matching. -/
private lemma integerPoint_eq_subgraphIncidenceVector_of_nonneg_mulVec_le_one
    {x : G.edgeSet → ℝ}
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z))
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1) :
    ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M := by
  let M : G.Subgraph := integralSupportSubgraph (G := G) x
  have hM : M.IsMatching :=
    integralSupportSubgraph_isMatching_of_nonneg_mulVec_le_one_of_integer
      (G := G) hx_int hx_nonneg hx_deg
  refine ⟨M, hM, ?_⟩
  funext e
  by_cases he : x e = 1
  · have heM : e.1 ∈ M.edgeSet := by
      simpa [M] using (integralSupportSubgraph_mem_edgeSet_iff (G := G) x e).2 he
    -- On the support, both the reconstructed vector and `x` equal `1`.
    simp [M, SimpleGraph.subgraphIncidenceVector, heM, he]
  · have hx0 : x e = 0 := by
      -- Off the support, integrality collapses the coordinate to `0`.
      rcases edge_coordinate_eq_zero_or_one_of_nonneg_mulVec_le_one_of_integer
          (G := G) hx_int hx_nonneg hx_deg e with hzero | hone
      · exact hzero
      · exact (he hone).elim
    have heM : e.1 ∉ M.edgeSet := by
      intro heM
      exact he ((integralSupportSubgraph_mem_edgeSet_iff (G := G) x e).1 (by simpa [M] using heM))
    -- Off the support, both the reconstructed vector and `x` vanish.
    simp [M, SimpleGraph.subgraphIncidenceVector, heM, hx0]

/-- Helper for Corollary 4.19: every integral feasible point is already one of the matching
polytope generators. -/
private lemma integerPoint_mem_matchingPolytope_of_nonneg_mulVec_le_one
    {x : G.edgeSet → ℝ}
    (hx_deg : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1)
    (hx_nonneg : ∀ e, 0 ≤ x e)
    (hx_int : x ∈ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) :
    x ∈ matchingPolytope G := by
  rcases integerPoint_eq_subgraphIncidenceVector_of_nonneg_mulVec_le_one
      (G := G) hx_int hx_nonneg hx_deg with ⟨M, hM, rfl⟩
  -- The reconstructed matching is one of the convex-hull generators.
  rw [SimpleGraph.matchingPolytope]
  exact subset_convexHull ℝ
    {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = G.subgraphIncidenceVector ℝ M}
    ⟨M, hM, rfl⟩

/-- Helper for Corollary 4.19: casting the integral incidence matrix to `ℝ` recovers the real
incidence matrix. -/
private lemma edgeIncMatrix_intCast :
    (G.edgeIncMatrix ℤ).map (Int.castRingHom ℝ) = G.edgeIncMatrix ℝ := by
  -- Both matrices encode the same `0,1` incidence pattern after coercion to `ℝ`.
  ext v e
  by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
  · simp [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply,
      G.incMatrix_of_mem_incidenceSet (R := ℤ) h,
      G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
  · simp [SimpleGraph.edgeIncMatrix, Matrix.submatrix_apply,
      G.incMatrix_of_notMem_incidenceSet (R := ℤ) h,
      G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]

/-- Helper for Corollary 4.19: the `Fin`-reindexed incidence matrix computes the same row sums as
the native `G.edgeSet`-indexed incidence matrix after coordinate transport. -/
private lemma reindexedEdgeIncMatrix_mulVec_apply
    (y : Fin (Nat.card G.edgeSet) → ℝ) (v : V) :
    ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)).map
        (Int.castRingHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) =
      ((G.edgeIncMatrix ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v := by
  -- Expand the reindexed matrix-vector product and reindex the finite column sum back to
  -- `G.edgeSet`.
  calc
    ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)).map
        (Int.castRingHom ℝ)) *ᵥ y) ((Finite.equivFin V) v)) =
        ∑ j : Fin (Nat.card G.edgeSet),
          ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)).map
              (Int.castRingHom ℝ)) ((Finite.equivFin V) v) j) * y j) := by
          simp [Matrix.mulVec, dotProduct]
    _ = ∑ e : G.edgeSet, (((G.edgeIncMatrix ℤ) v e : ℝ) * y ((Finite.equivFin G.edgeSet) e)) := by
          refine Fintype.sum_equiv (Finite.equivFin G.edgeSet).symm _ _ ?_
          intro e
          rw [Equiv.apply_symm_apply]
          rw [Matrix.reindex_apply]
          simp [SimpleGraph.edgeIncMatrix]
    _ = ∑ e : G.edgeSet, (G.edgeIncMatrix ℝ) v e * graphEdgeCoordinateReindex (G := G) y e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          by_cases h : (e : Sym2 V) ∈ G.incidenceSet v
          · rw [graphEdgeCoordinateReindex_apply]
            simp [SimpleGraph.edgeIncMatrix, G.incMatrix_of_mem_incidenceSet (R := ℤ) h,
              G.incMatrix_of_mem_incidenceSet (R := ℝ) h]
          · rw [graphEdgeCoordinateReindex_apply]
            simp [SimpleGraph.edgeIncMatrix, G.incMatrix_of_notMem_incidenceSet (R := ℤ) h,
              G.incMatrix_of_notMem_incidenceSet (R := ℝ) h]
    _ = ((G.edgeIncMatrix ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v := by
          simp [Matrix.mulVec, dotProduct]

/-- Helper for Corollary 4.19: the canonical edge-coordinate reindexing identifies the native
matching-feasible owner with the `Fin`-indexed nonnegative matrix polyhedron from Theorem 4.4. -/
private theorem graphEdgeCoordinateReindex_mem_nonnegativeMatrixPolyhedron_iff
    {y : Fin (Nat.card G.edgeSet) → ℝ} :
    graphEdgeCoordinateReindex (G := G) y ∈
        {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} ↔
      y ∈ nonnegative_matrix_polyhedron
        (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ))
        (fun _ : Fin (Nat.card V) ↦ (1 : ℤ)) := by
  -- Translate the `Fin`-indexed polyhedron membership into the native row inequalities and
  -- coordinatewise nonnegativity constraints.
  rw [mem_nonnegative_matrix_polyhedron_iff]
  constructor
  · rintro ⟨hx_deg, hx_nonneg⟩
    refine ⟨?_, ?_⟩
    · intro i
      let v : V := (Finite.equivFin V).symm i
      -- Evaluate the native row inequality at the vertex corresponding to `i`.
      have hv : ((G.edgeIncMatrix ℝ).mulVec (graphEdgeCoordinateReindex (G := G) y)) v ≤ 1 :=
        hx_deg v
      have hv' :
          ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
              (G.edgeIncMatrix ℤ)).map (Int.castRingHom ℝ)) *ᵥ y)
              ((Finite.equivFin V) v)) ≤ 1 := by
        rw [reindexedEdgeIncMatrix_mulVec_apply (G := G) y v]
        exact hv
      simpa [v, Matrix.mulVec, dotProduct] using hv'
    · intro j
      -- The edge-coordinate nonnegativity rewrites directly through the coordinate equivalence.
      have hj : 0 ≤ graphEdgeCoordinateReindex (G := G) y ((Finite.equivFin G.edgeSet).symm j) :=
        hx_nonneg ((Finite.equivFin G.edgeSet).symm j)
      have hj' : 0 ≤ y ((Finite.equivFin G.edgeSet) ((Finite.equivFin G.edgeSet).symm j)) := by
        simpa [graphEdgeCoordinateReindex_apply] using hj
      exact (Equiv.apply_symm_apply (Finite.equivFin G.edgeSet) j) ▸ hj'
  · rintro ⟨hy_deg, hy_nonneg⟩
    refine ⟨?_, ?_⟩
    · intro v
      -- Read the `Fin`-row inequality back as the native incidence-matrix inequality at `v`.
      have hv :
          ∑ j, (((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
              (G.edgeIncMatrix ℤ)) ((Finite.equivFin V) v) j : ℝ) * y j) ≤ (1 : ℝ) := by
        simpa using hy_deg ((Finite.equivFin V) v)
      have hv' :
          ((((Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
              (G.edgeIncMatrix ℤ)).map (Int.castRingHom ℝ)) *ᵥ y)
              ((Finite.equivFin V) v)) ≤ 1 := by
        simpa [Matrix.mulVec, dotProduct] using hv
      rw [reindexedEdgeIncMatrix_mulVec_apply (G := G) y v] at hv'
      simpa
        using hv'
    · intro e
      -- Read the `Fin`-coordinate nonnegativity back in native edge coordinates.
      have he : 0 ≤ y ((Finite.equivFin G.edgeSet) e) :=
        hy_nonneg ((Finite.equivFin G.edgeSet) e)
      rw [graphEdgeCoordinateReindex_apply]
      exact he

/-- Helper for Corollary 4.19: reindexing the totally unimodular edge-incidence matrix along the
canonical finite enumerations preserves total unimodularity. -/
private lemma reindexedEdgeIncMatrix_isTotallyUnimodular_of_isBipartite
    (hG : G.IsBipartite) :
    (Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)
      (G.edgeIncMatrix ℤ)).IsTotallyUnimodular := by
  -- Apply Theorem 4.18 in native coordinates and transport the TU witness to the `Fin` model.
  have hTU0 : (G.edgeIncMatrix ℤ).IsTotallyUnimodular :=
    (edge_incidence_matrix_isTotallyUnimodular_iff_isBipartite (G := G)).2 hG
  simpa using hTU0.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet)

/-- Helper for Corollary 4.19: the incidence-matrix feasible set is integral on a bipartite
graph because its `Fin`-indexed presentation is totally unimodular. -/
private lemma matchingFeasibleSet_isIntegral
    (hG : G.IsBipartite) :
    is_integral {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} :=
  by
    let A : Matrix (Fin (Nat.card V)) (Fin (Nat.card G.edgeSet)) ℤ :=
      Matrix.reindex (Finite.equivFin V) (Finite.equivFin G.edgeSet) (G.edgeIncMatrix ℤ)
    let P : Set (Fin (Nat.card G.edgeSet) → ℝ) :=
      nonnegative_matrix_polyhedron A (fun _ : Fin (Nat.card V) ↦ (1 : ℤ))
    have hIntegralP : is_integral P := by
      -- Route correction: Theorem 4.18 is available, so apply Theorem 4.4 to the reindexed
      -- incidence matrix and keep all coordinate transport inside the existing `_iff` lemma.
      exact
        nonnegative_matrix_polyhedron_is_integral_of_isTotallyUnimodular A
          (fun _ : Fin (Nat.card V) ↦ (1 : ℤ))
          (reindexedEdgeIncMatrix_isTotallyUnimodular_of_isBipartite (G := G) hG)
    have hIntegralImage :
        is_integral (graphEdgeCoordinateReindex (G := G) '' P) := by
      -- The edge-coordinate equivalence preserves the integer-point owner.
      simpa [graphEdgeCoordinateReindex, P] using
        isIntegralFunCongrLeftSymmImage
          ((Finite.equivFin G.edgeSet).symm) hIntegralP
    -- Identify the native feasible owner with the image of the `Fin`-indexed polyhedron.
    convert hIntegralImage using 1
    ext x
    constructor
    · intro hx
      refine ⟨graphEdgeCoordinates (G := G) x, ?_, ?_⟩
      · -- Reindex the native feasible point into the `Fin` presentation.
        have hx' :
            graphEdgeCoordinateReindex (G := G) (graphEdgeCoordinates (G := G) x) ∈
              {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
          exact (graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x).symm ▸ hx
        exact (graphEdgeCoordinateReindex_mem_nonnegativeMatrixPolyhedron_iff (G := G)).1 hx'
      · exact graphEdgeCoordinateReindex_graphEdgeCoordinates (G := G) x
    · rintro ⟨y, hy, rfl⟩
      -- Read the `Fin`-indexed feasibility conditions back in native coordinates.
      exact (graphEdgeCoordinateReindex_mem_nonnegativeMatrixPolyhedron_iff (G := G)).2 hy

/-- Helper for Corollary 4.19: the matching-feasible owner `{x | A_G x ≤ 1, x ≥ 0}` is convex. -/
private lemma convex_matchingFeasibleSet :
    Convex ℝ {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_deg, hx_nonneg⟩
  rcases hy with ⟨hy_deg, hy_nonneg⟩
  refine ⟨?_, ?_⟩
  · intro v
    -- Each row inequality is affine, so convex combinations preserve the upper bound `1`.
    have hmulVec :
        (G.edgeIncMatrix ℝ).mulVec (a • x + b • y) =
          a • (G.edgeIncMatrix ℝ).mulVec x + b • (G.edgeIncMatrix ℝ).mulVec y := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    calc
      ((G.edgeIncMatrix ℝ).mulVec (a • x + b • y)) v =
          a * (((G.edgeIncMatrix ℝ).mulVec x) v) + b * (((G.edgeIncMatrix ℝ).mulVec y) v) := by
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hmulVec v
      _ ≤ a * 1 + b * 1 := by
            have hxa : a * (((G.edgeIncMatrix ℝ).mulVec x) v) ≤ a * 1 :=
              mul_le_mul_of_nonneg_left (hx_deg v) ha
            have hyb : b * (((G.edgeIncMatrix ℝ).mulVec y) v) ≤ b * 1 :=
              mul_le_mul_of_nonneg_left (hy_deg v) hb
            exact add_le_add hxa hyb
      _ = 1 := by
            nlinarith
  · intro e
    -- Coordinatewise nonnegativity is preserved by convex combinations.
    have hx' := hx_nonneg e
    have hy' := hy_nonneg e
    have hcoord : (a • x + b • y) e = a * x e + b * y e := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoord]
    nlinarith

/-- Helper for Corollary 4.19: the perfect-feasible owner `{x | A_G x = 1, x ≥ 0}` is convex. -/
private lemma convex_perfectFeasibleSet :
    Convex ℝ {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x = 1 ∧ ∀ e, 0 ≤ x e} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_deg, hx_nonneg⟩
  rcases hy with ⟨hy_deg, hy_nonneg⟩
  refine ⟨?_, ?_⟩
  · funext v
    -- The row equations are affine, so the convex combination still gives the all-ones vector.
    have hmulVec :
        (G.edgeIncMatrix ℝ).mulVec (a • x + b • y) =
          a • (G.edgeIncMatrix ℝ).mulVec x + b • (G.edgeIncMatrix ℝ).mulVec y := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hxv : ((G.edgeIncMatrix ℝ).mulVec x) v = 1 := by
      simpa using congrFun hx_deg v
    have hyv : ((G.edgeIncMatrix ℝ).mulVec y) v = 1 := by
      simpa using congrFun hy_deg v
    calc
      ((G.edgeIncMatrix ℝ).mulVec (a • x + b • y)) v =
          a * (((G.edgeIncMatrix ℝ).mulVec x) v) + b * (((G.edgeIncMatrix ℝ).mulVec y) v) := by
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hmulVec v
      _ = a * 1 + b * 1 := by
            rw [hxv, hyv]
      _ = 1 := by
            nlinarith
  · intro e
    -- Coordinatewise nonnegativity is preserved exactly as in the matching-feasible owner.
    have hx' := hx_nonneg e
    have hy' := hy_nonneg e
    have hcoord : (a • x + b • y) e = a * x e + b * y e := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoord]
    nlinarith

/-- Helper for Corollary 4.19: if a vertex is not covered by a subgraph, its incidence-vector sum
at that vertex is `0`. -/
private lemma subgraphIncidenceSum_eq_zero_of_notMem_verts
    {M : G.Subgraph} {v : V} (hv : v ∉ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 0 := by
  -- Any positive incident coordinate would force the vertex into `M.verts`.
  refine Finset.sum_eq_zero ?_
  intro e he
  have hv_mem : v ∈ (e : Sym2 V) := by
    have he_inc : (e : Sym2 V) ∈ G.incidenceFinset v := (Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_incidenceFinset, SimpleGraph.edge_mem_incidenceSet_iff] using he_inc
  by_cases heM : e.1 ∈ M.edgeSet
  · exact (hv (Subgraph.mem_verts_of_mem_edge heM hv_mem)).elim
  · simp [SimpleGraph.subgraphIncidenceVector, heM]

/-- Helper for Corollary 4.19: at a covered vertex of a matching, the incidence-vector sum is
exactly `1`. -/
private lemma matchingIncidenceSum_eq_one_of_mem_verts
    {M : G.Subgraph} (hM : M.IsMatching) {v : V} (hv : v ∈ M.verts) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  obtain ⟨w, hvw, huniq⟩ := hM hv
  let e₀ : G.edgeSet := ⟨s(v, w), M.adj_sub hvw⟩
  have he₀_mem :
      e₀ ∈ Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v := by
    -- The unique matching edge at `v` belongs to the incidence filter.
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
                e.1 = s(v, Sym2.Mem.other hv_e) := by symm; exact Sym2.other_spec hv_e
                _ = s(v, w) := by rw [huniq _ hAdj_e]
                _ = e₀.1 := rfl
            exact (he_ne (Subtype.ext he_eq)).elim
          · simp [SimpleGraph.subgraphIncidenceVector, heM]
    _ = 1 := he₀_val

/-- Helper for Corollary 4.19: every matching incidence sum at a vertex is bounded by `1`. -/
private lemma matchingIncidenceSum_le_one
    {M : G.Subgraph} (hM : M.IsMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) ≤ 1 := by
  -- A matching contributes `1` on covered vertices and `0` on uncovered ones.
  by_cases hv : v ∈ M.verts
  · have hsum_eq_one := matchingIncidenceSum_eq_one_of_mem_verts (G := G) hM hv
    linarith
  · rw [subgraphIncidenceSum_eq_zero_of_notMem_verts (G := G) hv]
    norm_num

/-- Helper for Corollary 4.19: a perfect matching contributes exactly one incident edge at every
vertex. -/
private lemma perfectMatchingIncidenceSum_eq_one
    {M : G.Subgraph} (hM : M.IsPerfectMatching) (v : V) :
    (Finset.univ.filter fun e : G.edgeSet ↦ (e : Sym2 V) ∈ G.incidenceFinset v).sum
        (G.subgraphIncidenceVector ℝ M) = 1 := by
  -- Perfect matchings are matchings that cover every vertex.
  simpa using matchingIncidenceSum_eq_one_of_mem_verts (G := G) hM.1 (hM.2 v)

/-- Helper for Corollary 4.19: the incidence vector of a matching satisfies the bipartite
incidence-matrix feasibility inequalities. -/
private lemma subgraphIncidenceVector_mem_matchingFeasibleSet_of_isMatching
    {M : G.Subgraph} (hM : M.IsMatching) :
    G.subgraphIncidenceVector ℝ M ∈
      {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} := by
  refine ⟨?_, subgraphIncidenceVector_nonneg (G := G) M⟩
  intro v
  -- Matching incidence sums are exactly the row bounds `A_G x ≤ 1`.
  simpa [edgeIncMatrix_mulVec_apply (G := G) (x := G.subgraphIncidenceVector ℝ M) v] using
    matchingIncidenceSum_le_one (G := G) hM v

/-- Helper for Corollary 4.19: the incidence vector of a perfect matching satisfies the
incidence-matrix equality formulation. -/
private lemma subgraphIncidenceVector_mem_perfectFeasibleSet_of_isPerfectMatching
    {M : G.Subgraph} (hM : M.IsPerfectMatching) :
    G.subgraphIncidenceVector ℝ M ∈
      {x : G.edgeSet → ℝ | (G.edgeIncMatrix ℝ).mulVec x = 1 ∧ ∀ e, 0 ≤ x e} := by
  refine ⟨?_, subgraphIncidenceVector_nonneg (G := G) M⟩
  funext v
  -- Perfect matching incidence sums give the row equalities `A_G x = 1`.
  simpa [edgeIncMatrix_mulVec_apply (G := G) (x := G.subgraphIncidenceVector ℝ M) v] using
    perfectMatchingIncidenceSum_eq_one (G := G) hM v

/-- Helper for Corollary 4.19: evaluating a finite weighted sum of edge vectors at one edge turns
the vector identity into the corresponding scalar identity. -/
private lemma weighted_sum_apply
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → G.edgeSet → ℝ)
    {x : G.edgeSet → ℝ} (hx : ∑ i, w i • z i = x) (e : G.edgeSet) :
    ∑ i, w i * z i e = x e := by
  -- Apply the vector identity at the chosen edge coordinate.
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx e

/-- Helper for Corollary 4.19: in a weighted average of numbers in `[0,1]` with total weight `1`,
every positive-weight support term must already equal `1` if the average is `1`. -/
private lemma eq_one_of_weightedAverage_eq_one
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
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _hj ↦ hterm_nonneg j)).1 hterm_sum i
      (Finset.mem_univ i)
  intro i hwi
  have hwi_pos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hslack_nonneg : 0 ≤ 1 - a i := sub_nonneg.mpr (ha_le_one i)
  have hslack_zero : 1 - a i = 0 := by
    nlinarith [hzero i, hwi_pos, hslack_nonneg]
  nlinarith [hslack_zero]

/-- Helper for Corollary 4.19: a positive-weight support matching in a convex decomposition of a
point of `perfectMatchingConstraintSet G` is already perfect. -/
private lemma supportMatching_isPerfect_of_convexCombination_degree_one
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
              weighted_sum_apply (G := G) w (fun j ↦ G.subgraphIncidenceVector ℝ (M j)) hx e
      _ = 1 := by
            simpa [I] using hx_deg v
  have hle :
      ∀ j, I.sum (G.subgraphIncidenceVector ℝ (M j)) ≤ 1 := by
    intro j
    simpa [I] using matchingIncidenceSum_le_one (G := G) (hMatch j) v
  have hi_sum_eq_one :
      I.sum (G.subgraphIncidenceVector ℝ (M i)) = 1 :=
    eq_one_of_weightedAverage_eq_one hw_nonneg hle hw_sum havg i hwi
  by_contra hv
  have hi_sum_eq_zero :
      I.sum (G.subgraphIncidenceVector ℝ (M i)) = 0 := by
    simpa [I] using subgraphIncidenceSum_eq_zero_of_notMem_verts (G := G) (M := M i) hv
  linarith

/-- Helper for Corollary 4.19: any point that is simultaneously in the matching polytope and the
perfect-matching constraint system already lies in the perfect matching polytope. -/
private lemma perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
    {x : G.edgeSet → ℝ}
    (hx_matchingPolytope : x ∈ matchingPolytope G)
    (hxPerfect : x ∈ perfectMatchingConstraintSet G) :
    x ∈ perfectMatchingPolytope G :=
  by
    rw [SimpleGraph.matchingPolytope, mem_convexHull_iff_exists_fintype] at hx_matchingPolytope
    rcases hx_matchingPolytope with ⟨ι, _, w, z, hw_nonneg, hw_sum, hz, hx_sum⟩
    have hz' : ∀ i, ∃ M : G.Subgraph, M.IsMatching ∧ z i = G.subgraphIncidenceVector ℝ M := by
      intro i
      simpa using hz i
    choose M hMatch hVec using hz'
    have hx_sum_match :
        ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = x := by
      -- Rewrite the witness so the convex-combination generators are explicit matchings.
      calc
        ∑ i, w i • G.subgraphIncidenceVector ℝ (M i) = ∑ i, w i • z i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hVec i]
        _ = x := hx_sum
    have hsupport_perfect :
        ∀ i, w i ≠ 0 → (M i).IsPerfectMatching :=
      supportMatching_isPerfect_of_convexCombination_degree_one (G := G) w M
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
      -- Zero-weight terms can be replaced by any perfect-matching generator without moving the
      -- barycenter.
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

/-- Corollary 4.19 (1). If `G` is bipartite, then the matching polytope of `G` is the set
`{x ∈ ℝ^E : A_G x ≤ 1, x ≥ 0}`. -/
theorem matchingPolytope_eq_setOf_mulVec_le_one
    (hG : G.IsBipartite) :
    matchingPolytope G = {x | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e} :=
  by
    let F : Set (G.edgeSet → ℝ) := {x | (G.edgeIncMatrix ℝ).mulVec x ≤ 1 ∧ ∀ e, 0 ≤ x e}
    apply le_antisymm
    · rw [SimpleGraph.matchingPolytope]
      -- The matching generators already satisfy the incidence-matrix formulation, so the whole
      -- convex hull stays inside the feasible owner.
      refine convexHull_min ?_ (convex_matchingFeasibleSet (G := G))
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      exact subgraphIncidenceVector_mem_matchingFeasibleSet_of_isMatching (G := G) hM
    · intro x hx
      have hIntegral : is_integral F := by
        simpa [F] using matchingFeasibleSet_isIntegral (G := G) hG
      rw [is_integral_iff] at hIntegral
      have hxHull :
          x ∈ convexHull ℝ (F ∩ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z)) := by
        rw [← hIntegral]
        exact hx
      have hIntegerSubset :
          F ∩ Set.range (fun z : G.edgeSet → ℤ ↦ Int.cast ∘ z) ⊆ matchingPolytope G := by
        intro y hy
        rcases hy with ⟨hyF, hyInt⟩
        exact integerPoint_mem_matchingPolytope_of_nonneg_mulVec_le_one
          (G := G) hyF.1 hyF.2 hyInt
      -- Once the feasible owner is the convex hull of its integer points, the reconstructed
      -- matching generators give the reverse inclusion.
      exact (convexHull_min hIntegerSubset (convex_convexHull ℝ _)) hxHull

/-- Corollary 4.19 (2). If `G` is bipartite, then the perfect matching polytope of `G` is the set
`{x ∈ ℝ^E : A_G x = 1, x ≥ 0}`. -/
theorem perfectMatchingPolytope_eq_setOf_mulVec_eq_one
    (hG : G.IsBipartite) :
    perfectMatchingPolytope G = {x | (G.edgeIncMatrix ℝ).mulVec x = 1 ∧ ∀ e, 0 ≤ x e} :=
  by
    apply le_antisymm
    · rw [SimpleGraph.perfectMatchingPolytope]
      -- Perfect matching generators satisfy the equality formulation vertexwise.
      refine convexHull_min ?_ (convex_perfectFeasibleSet (G := G))
      intro x hx
      rcases hx with ⟨M, hM, rfl⟩
      exact subgraphIncidenceVector_mem_perfectFeasibleSet_of_isPerfectMatching (G := G) hM
    · intro x hx
      have hxPerfect : x ∈ perfectMatchingConstraintSet G := by
        rw [perfectMatchingConstraintSet_eq_setOf_mulVec_eq_one (G := G) hG]
        exact hx
      have hxMatching : x ∈ matchingPolytope G := by
        have hx_deg_le : ∀ v : V, ((G.edgeIncMatrix ℝ).mulVec x) v ≤ 1 := by
          intro v
          simpa using le_of_eq (congrFun hx.1 v)
        rw [matchingPolytope_eq_setOf_mulVec_le_one (G := G) hG]
        exact ⟨hx_deg_le, hx.2⟩
      -- Rewrite through the perfect-constraint owner, then upgrade the matching decomposition.
      exact
        perfectMatchingPolytope_of_mem_matchingPolytope_of_mem_perfectMatchingConstraintSet
          (G := G) hxMatching hxPerfect

end Finite

end Corollary_4_19

end SimpleGraph

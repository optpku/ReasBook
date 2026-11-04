/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_proposition_2_6.StableSetPolytope
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped BigOperators
open Finset

-- Domain sampling for this exercise:
-- * primary domain: stable-set polytopes and facet-defining inequalities on finite graphs
-- * core owners reused here:
--   `stableSetIndicator`, `stableSetVertices`, `stableSetPolytope`, `IsFacetOf`,
--   `SimpleGraph.indepNum`
-- * source-facing data kept here:
--   the notation `α(G)`, alpha-critical edges, the alpha-critical graph, and the connectedness
--   hypothesis from Exercise 7.20

section Exercise_7_20

variable {V : Type}
variable (G : SimpleGraph V)

/-- Source-facing notation for the stability number `SimpleGraph.indepNum G` of a graph. -/
notation "α(" G ")" => SimpleGraph.indepNum G

/-- An edge of `G` is alpha-critical when deleting it increases the stability number by one. -/
def isAlphaCriticalEdge (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ α(G.deleteEdges {e}) = α(G) + 1

/-- The graph on `V` whose edges are exactly the alpha-critical edges of `G`. -/
def alphaCriticalGraph : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | isAlphaCriticalEdge G e}

/-- The edge set of `alphaCriticalGraph G` is exactly the set of alpha-critical edges of `G`. -/
@[simp] theorem mem_alphaCriticalGraph_edgeSet_iff (e : Sym2 V) :
    e ∈ (alphaCriticalGraph G).edgeSet ↔ isAlphaCriticalEdge G e := by
  constructor
  · intro he
    rw [alphaCriticalGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  · intro he
    rw [alphaCriticalGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he, G.not_isDiag_of_mem_edgeSet he.1⟩

section Fintype

variable [Fintype V]

private noncomputable instance : DecidableEq V := Classical.decEq V

/-- The equality face of `STAB(G)` cut out by the stability-number inequality. -/
def stableSetCardinalityFace : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∧ ∑ i, x i = (α(G) : ℝ)}

/-- Membership in `stableSetCardinalityFace G` means belonging to `STAB(G)` and saturating the
stability-number inequality. -/
theorem mem_stableSetCardinalityFace_iff (x : V → ℝ) :
    x ∈ stableSetCardinalityFace G ↔ x ∈ STAB(G) ∧ ∑ i, x i = (α(G) : ℝ) :=
  Iff.rfl

/-- The face equation in `stableSetCardinalityFace G` can be read as the all-ones dot product. -/
theorem mem_stableSetCardinalityFace_iff_one_dotProduct (x : V → ℝ) :
    x ∈ stableSetCardinalityFace G ↔
      x ∈ STAB(G) ∧ (1 : V → ℝ) ⬝ᵥ x = (α(G) : ℝ) := by
  rw [mem_stableSetCardinalityFace_iff]
  simp [one_dotProduct]

/-- Helper for Exercise 7.20: summing the coordinates of a stable-set indicator counts its
support. -/
private lemma sum_stableSetIndicator_eq_card (s : Finset V) :
    (∑ v, stableSetIndicator s v) = s.card := by
  classical
  -- Each active coordinate contributes `1`, and each inactive coordinate contributes `0`.
  simp [stableSetIndicator]

/-- Helper for Exercise 7.20: the empty stable set has zero indicator vector. -/
private lemma stableSetIndicatorEmpty :
    stableSetIndicator (∅ : Finset V) = 0 := by
  classical
  -- The empty stable set contributes no active coordinates.
  ext v
  simp [stableSetIndicator]

/-- Helper for Exercise 7.20: singleton stable sets give coordinate unit vectors. -/
private lemma stableSetIndicatorSingleton (v : V) :
    stableSetIndicator ({v} : Finset V) = Pi.single v 1 := by
  classical
  -- A singleton indicator is exactly the standard basis vector at that vertex.
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator]
  · simp [stableSetIndicator, huv]

/-- Helper for Exercise 7.20: `0` together with the coordinate unit vectors is affinely
independent in `ℝ^V`. -/
private lemma affineIndependentNoneOrSingle :
    AffineIndependent ℝ
      (fun o : Option V ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))) := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))
  let e : {o : Option V // o ≠ none} → V := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some v, _⟩ => v
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some va =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some vb =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  -- Affine independence reduces to linear independence of the standard basis.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option V // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option V // o ≠ none} ↦ Pi.single (e i) (1 : ℝ) := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some v =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp e he_injective

/-- Helper for Exercise 7.20: the stable-set polytope spans the full ambient space. -/
private theorem stableSetPolytopeAffineSpanEqTop [Finite V] :
    affineSpan ℝ STAB(G) = ⊤ := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v (1 : ℝ))
  have hp : Set.range p ⊆ STAB(G) := by
    intro x hx
    rcases hx with ⟨o, rfl⟩
    cases o with
    | none =>
        -- The origin comes from the empty stable set.
        have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope G
            (by simp : G.IsIndepSet (∅ : Finset V))
        simpa [p, stableSetIndicatorEmpty] using h0
    | some v =>
        -- Each singleton indicator is a stable-set vertex.
        have hv : stableSetIndicator ({v} : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope G
            (by simp : G.IsIndepSet ({v} : Finset V))
        simpa [p, stableSetIndicatorSingleton] using hv
  have hp_affine : AffineIndependent ℝ p := by
    -- The chosen family is the origin together with the coordinate unit vectors.
    simpa [p] using
      (affineIndependentNoneOrSingle (V := V))
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    -- The family has `|V| + 1` points in an ambient space of dimension `|V|`.
    have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by
      simp
    exact hp_affine.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hcard)
  have hmono : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ STAB(G) :=
    affineSpan_mono ℝ hp
  -- A superset of a spanning affine family has full affine span.
  exact top_unique (by simpa [htop] using hmono)

/-- Helper for Exercise 7.20: a nonzero linear functional on `ℝ^V` has codimension-one kernel. -/
private lemma finrankKerEqCardSubOne {L : (V → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = Fintype.card V - 1 := by
  let f : Module.Dual ℝ (V → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = Fintype.card V := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using
      f.finrank_ker_add_one_of_ne_zero hf
  exact Nat.eq_sub_of_add_eq hker_add_one

/-- Helper for Exercise 7.20: a tight valid equality set is the exposed set of its defining linear
functional. -/
private lemma eqSetEqToExposedOfMem [Finite V]
    {P : Set (V → ℝ)} {L : (V → ℝ) →ₗ[ℝ] ℝ} {δ : ℝ} {x₀ : V → ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → L x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : L x₀ = δ) :
    {x : V → ℝ | x ∈ P ∧ L x = δ} =
      (⟨L, L.continuous_of_finiteDimensional⟩ : (V → ℝ) →L[ℝ] ℝ).toExposed P := by
  let _ : Fintype V := Fintype.ofFinite V
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      L y ≤ δ := hvalid hyP
      _ = L x := hxEq.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hx₀_le : L x₀ ≤ L x := hx.2 x₀ hx₀
    have hx_le : L x ≤ L x₀ := by
      simpa [hx₀_eq] using hvalid hx.1
    exact (le_antisymm hx_le hx₀_le).trans hx₀_eq

/-- Helper for Exercise 7.20: the coordinate vector `c` defines the dot-product functional
`x ↦ c ⬝ᵥ x`. -/
private def dotProductLinearMap (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v, c v • LinearMap.proj v

/-- Helper for Exercise 7.20: `dotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private lemma dotProductLinearMap_apply (c x : V → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  -- The linear map was defined coordinatewise as the dot product with `c`.
  simp [dotProductLinearMap, dotProduct]

/-- Helper for Exercise 7.20: every nonempty tight equality set of a valid inequality is exposed.
-/
private lemma equalitySetIsExposed
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ)
    (hx₀ : x₀ ∈ P) (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    IsExposed ℝ P {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} := by
  have hvalid' : ∀ ⦃x : V → ℝ⦄, x ∈ P → dotProductLinearMap c x ≤ δ := by
    intro x hx
    simpa [dotProductLinearMap_apply] using hvalid hx
  have hEq :
      {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} =
        {x : V → ℝ | x ∈ P ∧ dotProductLinearMap c x = δ} := by
    -- Rewrite the equality face into the spelling used by the generic exposed-set helper.
    ext x
    simp [dotProductLinearMap_apply]
  -- The equality slice is the exposed set of the dot-product functional.
  rw [hEq, eqSetEqToExposedOfMem (L := dotProductLinearMap c) hvalid' hx₀]
  · exact ContinuousLinearMap.toExposed.isExposed
  · simpa [dotProductLinearMap_apply] using hx₀_eq

/-- Helper for Exercise 7.20: the direction of a tight equality face lies in the kernel of its
defining linear functional. -/
private lemma equalitySetDirectionLeKer
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    (affineSpan ℝ {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}).direction ≤
      LinearMap.ker (dotProductLinearMap c) := by
  let F : Set (V → ℝ) := {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}
  let H : AffineSubspace ℝ (V → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (dotProductLinearMap c))
  have hF_le_H : F ⊆ H := by
    intro x hx
    -- Points in the equality set differ by a kernel vector because the functional is constant
    -- on the face.
    change x ∈ H
    rw [AffineSubspace.mem_mk']
    refine LinearMap.mem_ker.2 ?_
    rcases hx with ⟨-, hx_eq⟩
    simp [dotProductLinearMap_apply, vsub_eq_sub, hx_eq, hx₀_eq]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing to directions identifies the ambient affine subspace with the kernel.
  simpa [H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ F).direction ≤ H.direction)

/-- Helper for Exercise 7.20: a dot-product inequality that holds on every stable-set vertex holds
on the full stable-set polytope. -/
private lemma dotProductLeOfMemStableSetPolytope
    {c : V → ℝ} {δ : ℝ}
    (hvertex : ∀ s : Finset V, G.IsIndepSet s → c ⬝ᵥ stableSetIndicator s ≤ δ)
    {x : V → ℝ} (hx : x ∈ STAB(G)) :
    c ⬝ᵥ x ≤ δ := by
  classical
  let H : Set (V → ℝ) := {y : V → ℝ | c ⬝ᵥ y ≤ δ}
  have hconvex : Convex ℝ H := by
    -- A dot-product inequality cuts out a linear halfspace.
    simpa [H, dotProductLinearMap_apply] using
      convex_halfSpace_le (dotProductLinearMap c).isLinear δ
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hvertex s hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.20: if a deleted-edge independent set misses `u`, then the deleted edge
cannot be responsible for any new adjacency obstruction, so the set is already independent in
`G`. -/
private lemma indepSetOfDeleteEdgeIndepSetOfNotMemLeft {u v : V} {s : Finset V}
    (hs : (G.deleteEdges {s(u, v)}).IsIndepSet s) (hu : u ∉ s) :
    G.IsIndepSet s := by
  classical
  rw [SimpleGraph.isIndepSet_iff] at hs ⊢
  intro a ha b hb hab habG
  have hab_ne : s(a, b) ≠ s(u, v) := by
    intro hEq
    have hu_mem : u ∈ s(a, b) := by
      exact hEq ▸ (Sym2.mem_iff'.2 (Or.inl rfl))
    rcases Sym2.mem_iff'.1 hu_mem with rfl | rfl
    · exact hu ha
    · exact hu hb
  have habDelete : (G.deleteEdges {s(u, v)}).Adj a b := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨habG, by simp [hab_ne]⟩
  exact hs ha hb hab habDelete

/-- Helper for Exercise 7.20: a maximum independent set in the deleted graph of an α-critical edge
must contain the left endpoint. -/
private lemma left_mem_of_deleteEdgeWitness {u v : V} {s : Finset V}
    (hs : (G.deleteEdges {s(u, v)}).IsNIndepSet (α(G) + 1) s) :
    u ∈ s := by
  classical
  by_contra hu
  have hsG : G.IsIndepSet s :=
    indepSetOfDeleteEdgeIndepSetOfNotMemLeft (G := G) hs.isIndepSet hu
  have hcard_le : s.card ≤ α(G) := hsG.card_le_indepNum
  rw [hs.card_eq] at hcard_le
  exact Nat.not_succ_le_self (α(G)) hcard_le

/-- Helper for Exercise 7.20: a maximum independent set in the deleted graph of an α-critical edge
must contain the right endpoint. -/
private lemma right_mem_of_deleteEdgeWitness {u v : V} {s : Finset V}
    (hs : (G.deleteEdges {s(u, v)}).IsNIndepSet (α(G) + 1) s) :
    v ∈ s := by
  classical
  have hs' : (G.deleteEdges {s(v, u)}).IsNIndepSet (α(G) + 1) s := by
    simpa [Sym2.eq_swap] using hs
  exact left_mem_of_deleteEdgeWitness (G := G) (u := v) (v := u) hs'

/-- Helper for Exercise 7.20: deleting one endpoint from the indicator witness and deleting the
other endpoint differ by the corresponding singleton difference. -/
private lemma stableSetIndicator_erase_sub_erase_eq_single_sub_single
    {s : Finset V} {u v : V} (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    (stableSetIndicator (s.erase u) - stableSetIndicator (s.erase v) : V → ℝ) =
      Pi.single v 1 - Pi.single u 1 := by
  classical
  -- Compare the two sparse vectors coordinatewise.
  ext w
  by_cases hwu : w = u
  · subst w
    simp [stableSetIndicator, hu, huv]
  · by_cases hwv : w = v
    · subst w
      simp [stableSetIndicator, hv, hwu]
    · by_cases hw : w ∈ s
      · simp [stableSetIndicator, hwu, hwv, hw]
      · simp [stableSetIndicator, hwu, hwv, hw]

/-- Helper for Exercise 7.20: the all-ones inequality is valid on `STAB(G)`. -/
private lemma allOnes_valid_on_stableSetPolytope {x : V → ℝ} (hx : x ∈ STAB(G)) :
    (1 : V → ℝ) ⬝ᵥ x ≤ (α(G) : ℝ) := by
  -- It is enough to check the inequality on stable-set vertices and then use convexity.
  refine dotProductLeOfMemStableSetPolytope (G := G) ?_ hx
  intro s hs
  calc
    (1 : V → ℝ) ⬝ᵥ stableSetIndicator s = (∑ v, stableSetIndicator s v) := by
      simp [dotProduct]
    _ = (s.card : ℝ) := by
      norm_num [sum_stableSetIndicator_eq_card]
    _ ≤ (α(G) : ℝ) := by
      exact_mod_cast hs.card_le_indepNum

/-- Helper for Exercise 7.20: an α-critical edge gives a singleton-difference generator in the
direction of the tight face. -/
private lemma alphaCriticalEdgeDifference_mem_faceDirection {u v : V}
    (hcrit : (alphaCriticalGraph G).Adj u v) :
    (Pi.single v (1 : ℝ) - Pi.single u 1 : V → ℝ) ∈
      (affineSpan ℝ (stableSetCardinalityFace G)).direction := by
  classical
  have hedge : s(u, v) ∈ (alphaCriticalGraph G).edgeSet := by
    rwa [SimpleGraph.mem_edgeSet]
  have hedgeCrit : isAlphaCriticalEdge G (s(u, v)) :=
    (mem_alphaCriticalGraph_edgeSet_iff (G := G) _).1 hedge
  have huv : u ≠ v := by
    exact hcrit.ne
  let H := G.deleteEdges {s(u, v)}
  have hHalpha : α(H) = α(G) + 1 := hedgeCrit.2
  obtain ⟨S, hS⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := H)
  have hS' : H.IsNIndepSet (α(G) + 1) S := by
    rw [hHalpha] at hS
    exact hS
  have huS : u ∈ S := left_mem_of_deleteEdgeWitness (G := G) hS'
  have hvS : v ∈ S := right_mem_of_deleteEdgeWitness (G := G) hS'
  have hS_erase_u_H : H.IsIndepSet (S.erase u) := by
    -- Erasing vertices preserves independence in the deleted graph.
    exact hS'.isIndepSet.mono (by
      intro x hx
      exact Finset.mem_of_mem_erase hx)
  have hS_erase_v_H : H.IsIndepSet (S.erase v) := by
    -- The same restriction works after erasing `v`.
    exact hS'.isIndepSet.mono (by
      intro x hx
      exact Finset.mem_of_mem_erase hx)
  have hSuG : G.IsIndepSet (S.erase u) :=
    indepSetOfDeleteEdgeIndepSetOfNotMemLeft
      (G := G) (u := u) (v := v) (s := S.erase u) hS_erase_u_H (by
        show u ∉ S.erase u
        simp)
  have hS_erase_v_H' : (G.deleteEdges {s(v, u)}).IsIndepSet (S.erase v) := by
    simpa [Sym2.eq_swap] using hS_erase_v_H
  have hSvG : G.IsIndepSet (S.erase v) :=
    indepSetOfDeleteEdgeIndepSetOfNotMemLeft
      (G := G) (u := v) (v := u) (s := S.erase v) hS_erase_v_H' (by
        show v ∉ S.erase v
        simp [huv])
  have hcard_erase_u : (S.erase u).card = α(G) := by
    rw [Finset.card_erase_of_mem huS, hS'.card_eq]
    simpa using Nat.add_sub_cancel (α(G)) 1
  have hcard_erase_v : (S.erase v).card = α(G) := by
    rw [Finset.card_erase_of_mem hvS, hS'.card_eq]
    simpa using Nat.add_sub_cancel (α(G)) 1
  have hxu : stableSetIndicator (S.erase u) ∈ stableSetCardinalityFace G := by
    rw [mem_stableSetCardinalityFace_iff]
    refine ⟨stableSetIndicator_mem_stableSetPolytope G hSuG, ?_⟩
    rw [sum_stableSetIndicator_eq_card, hcard_erase_u]
  have hxv : stableSetIndicator (S.erase v) ∈ stableSetCardinalityFace G := by
    rw [mem_stableSetCardinalityFace_iff]
    refine ⟨stableSetIndicator_mem_stableSetPolytope G hSvG, ?_⟩
    rw [sum_stableSetIndicator_eq_card, hcard_erase_v]
  have hdir :
      stableSetIndicator (S.erase u) - stableSetIndicator (S.erase v) ∈
        (affineSpan ℝ (stableSetCardinalityFace G)).direction := by
    -- The difference of two face points lies in the face direction.
    exact AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ hxu) (mem_affineSpan ℝ hxv)
  simpa [stableSetIndicator_erase_sub_erase_eq_single_sub_single (hu := huS) (hv := hvS) huv]
    using hdir

/-- Helper for Exercise 7.20: connectedness of the α-critical graph transports the edge
generators to a fixed root vertex. -/
private lemma connectedSingleDifference_mem_faceDirection (root : V)
    (hconnected : (alphaCriticalGraph G).Connected) :
    ∀ v : V,
      (Pi.single v (1 : ℝ) - Pi.single root 1 : V → ℝ) ∈
        (affineSpan ℝ (stableSetCardinalityFace G)).direction := by
  intro v
  classical
  have hreach : Relation.ReflTransGen (alphaCriticalGraph G).Adj root v := by
    simpa [SimpleGraph.reachable_iff_reflTransGen] using (hconnected root v)
  induction hreach with
  | refl =>
      simp
  | @tail b c hreach hbc ih =>
      -- Append one critical edge difference to the already-transported root difference.
      have hbc' :
          (Pi.single c (1 : ℝ) - Pi.single b 1 : V → ℝ) ∈
            (affineSpan ℝ (stableSetCardinalityFace G)).direction :=
        alphaCriticalEdgeDifference_mem_faceDirection (G := G) hbc
      have hsum :
          (Pi.single c (1 : ℝ) - Pi.single root 1 : V → ℝ) =
            (Pi.single c (1 : ℝ) - Pi.single b 1) +
              (Pi.single b (1 : ℝ) - Pi.single root 1) := by
        ext x
        simp [Pi.single_apply, sub_eq_add_neg]
      rw [hsum]
      exact Submodule.add_mem _ hbc' ih

/-- Helper for Exercise 7.20: every zero-sum vector lies in the direction of the tight face. -/
private lemma zeroSum_mem_faceDirection (root : V)
    (hconnected : (alphaCriticalGraph G).Connected) {x : V → ℝ}
    (hx : ∑ i, x i = 0) :
    x ∈ (affineSpan ℝ (stableSetCardinalityFace G)).direction := by
  classical
  have hdecomp :
      x = Finset.sum (Finset.univ.erase root) fun v =>
        x v • (Pi.single v (1 : ℝ) - Pi.single root 1 : V → ℝ) := by
    ext w
    by_cases hw : w = root
    · subst w
      have hxroot : x root = - Finset.sum (Finset.univ.erase root) x := by
        have hsum_root :
            x root + Finset.sum (Finset.univ.erase root) x = 0 := by
          have hx' := hx
          rw [← Finset.sum_erase_add (s := Finset.univ) (f := x) (by simp : root ∈ Finset.univ)]
            at hx'
          simpa [add_comm] using hx'
        linarith
      have hroot_eval :
          (Finset.sum (Finset.univ.erase root) fun v =>
            x v • (Pi.single v (1 : ℝ) - Pi.single root 1 : V → ℝ)) root =
              - Finset.sum (Finset.univ.erase root) x := by
        calc
          (Finset.sum (Finset.univ.erase root) fun v =>
              x v • (Pi.single v (1 : ℝ) - Pi.single root 1 : V → ℝ)) root
              =
              Finset.sum (Finset.univ.erase root) fun v =>
                x v * ((Pi.single v (1 : ℝ) - Pi.single root 1 : V → ℝ) root) := by
            simp
          _ = Finset.sum (Finset.univ.erase root) (fun v => -x v) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            have hvroot : v ≠ root := by
              simpa [Finset.mem_erase] using hv
            simp [Pi.single_apply, hvroot]
          _ = - Finset.sum (Finset.univ.erase root) x := by
            simp
      exact hxroot.trans hroot_eval.symm
    · have hw_mem : w ∈ Finset.univ.erase root := by
        simp [hw]
      simpa [Pi.single_apply, hw, hw_mem]
  rw [hdecomp]
  exact Submodule.sum_mem _ fun v hv =>
    Submodule.smul_mem _
      _ (connectedSingleDifference_mem_faceDirection (G := G) root hconnected v)

/-- Exercise 7.20. If the graph on `V` whose edges are the alpha-critical edges of `G` is
connected, then the inequality `∑ i, x i ≤ α(G)` defines a facet of `STAB(G)`. -/
theorem exercise_7_20_stability_number_inequality_defines_facet
    (hconnected : (alphaCriticalGraph G).Connected) :
    IsFacetOf STAB(G) (stableSetCardinalityFace G) :=
  by
    classical
    let F : Set (V → ℝ) := stableSetCardinalityFace G
    let c : V → ℝ := 1
    let δ : ℝ := α(G)
    obtain ⟨root⟩ := hconnected.nonempty
    obtain ⟨s₀, hs₀⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
    have hx₀_mem : stableSetIndicator s₀ ∈ F := by
      -- A maximum stable set of `G` gives a tight witness on the face.
      rw [mem_stableSetCardinalityFace_iff]
      refine ⟨stableSetIndicator_mem_stableSetPolytope G hs₀.isIndepSet, ?_⟩
      rw [sum_stableSetIndicator_eq_card, hs₀.card_eq]
    have hF_eq :
        F = {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = δ} := by
      ext x
      simp [F, c, δ, mem_stableSetCardinalityFace_iff_one_dotProduct]
    have hx₀_eq : c ⬝ᵥ stableSetIndicator s₀ = δ := by
      -- The all-ones dot product reads the cardinality equation on the indicator witness.
      exact (show c ⬝ᵥ stableSetIndicator s₀ = δ from by
        simpa [hF_eq] using ((show stableSetIndicator s₀ ∈ {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = δ}
          from by simpa [hF_eq] using hx₀_mem)).2)
    have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → c ⬝ᵥ x ≤ δ := by
      intro x hx
      simpa [c, δ] using allOnes_valid_on_stableSetPolytope (G := G) hx
    have hF_exposed : IsExposed ℝ STAB(G) F := by
      -- The equality slice of a valid inequality is exposed once it is nonempty.
      rw [hF_eq]
      exact equalitySetIsExposed (P := STAB(G)) (c := c) (x₀ := stableSetIndicator s₀) (δ := δ)
        hvalid
        (by simpa [hF_eq] using hx₀_mem.1)
        hx₀_eq
    have hdir_le :
        (affineSpan ℝ F).direction ≤ LinearMap.ker (dotProductLinearMap c) := by
      -- Any direction vector between tight points preserves the defining equality.
      rw [hF_eq]
      exact equalitySetDirectionLeKer
        (P := STAB(G)) (c := c) (x₀ := stableSetIndicator s₀) (δ := δ) hx₀_eq
    have hker_le :
        LinearMap.ker (dotProductLinearMap c) ≤ (affineSpan ℝ F).direction := by
      intro x hx
      -- Kernel vectors are exactly the zero-sum vectors, and connectedness generates all of them.
      have hxsum : ∑ i, x i = 0 := by
        simpa [c, dotProductLinearMap_apply, one_dotProduct] using (LinearMap.mem_ker.1 hx)
      apply zeroSum_mem_faceDirection (G := G) root hconnected
      exact hxsum
    have hdir_eq :
        (affineSpan ℝ F).direction = LinearMap.ker (dotProductLinearMap c) :=
      le_antisymm hdir_le hker_le
    have hL_ne : dotProductLinearMap c ≠ 0 := by
      -- The all-ones functional does not vanish on a coordinate unit vector.
      intro hzero
      have hEval := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ => L (Pi.single root 1)) hzero
      simpa [c, dotProductLinearMap_apply] using hEval
    have hdim_face :
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
          Fintype.card V := by
      have hker_dim :
          Module.finrank ℝ (LinearMap.ker (dotProductLinearMap c)) =
            Fintype.card V - 1 :=
        finrankKerEqCardSubOne (V := V) hL_ne
      rw [hdir_eq, hker_dim]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr hconnected.nonempty))
    have hdim_stab :
        Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
      rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
        finrank_top, Module.finrank_fintype_fun_eq_card]
    -- The equality face is nonempty, exposed, and has codimension one in the full-dimensional
    -- stable-set polytope.
    rw [isFacetOf_iff]
    refine ⟨?_, hF_exposed, ?_⟩
    · exact ⟨stableSetIndicator s₀, hx₀_mem⟩
    · calc
        Module.finrank ℝ (affineSpan ℝ (stableSetCardinalityFace G)).direction + 1
            = Module.finrank ℝ (affineSpan ℝ F).direction + 1 := by simp [F]
        _ = Fintype.card V := hdim_face
        _ = Module.finrank ℝ (affineSpan ℝ STAB(G)).direction := hdim_stab.symm

end Fintype

end Exercise_7_20

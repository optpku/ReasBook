/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_theorem_4_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_2.ch4_sec4_4_2_algorithm_4_4_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SimpleGraph

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file reuses
-- mathlib's `SimpleGraph.IsVertexCover`, `SimpleGraph.vertexCoverNum`,
-- `SimpleGraph.Subgraph.IsMatching`, and the chapter owner
-- `SimpleGraph.Subgraph.IsMaximumCardinalityMatching`.

universe u

section Exercise_4_20

variable {V : Type u} {G : SimpleGraph V}

/-- Part (1) of Exercise 4.20: every matching of `G` has cardinality at most the cardinality of
every vertex cover of `G`. -/
theorem encard_edgeSet_le_encard_of_isMatching_isVertexCover
    (M : G.Subgraph) (U : Set V) (hM : M.IsMatching) (hU : G.IsVertexCover U) :
    M.edgeSet.encard ≤ U.encard := by
  classical
  let coverEndpoint : M.edgeSet → V := fun e ↦
    if hx : e.1.out.1 ∈ U then e.1.out.1 else Sym2.Mem.other (Sym2.out_fst_mem e.1)
  have coverEndpoint_mem_edge : ∀ e : M.edgeSet, coverEndpoint e ∈ (e : Sym2 V) := by
    intro e
    -- The chosen endpoint is always one of the two endpoints of the edge.
    by_cases hx : e.1.out.1 ∈ U
    · simpa [coverEndpoint, hx] using Sym2.out_fst_mem e.1
    · simpa [coverEndpoint, hx] using Sym2.other_mem (Sym2.out_fst_mem e.1)
  have coverEndpoint_mem_cover : ∀ e : M.edgeSet, coverEndpoint e ∈ U := by
    intro e
    have hxyM :
        M.Adj e.1.out.1 (Sym2.Mem.other (Sym2.out_fst_mem e.1)) := by
      have he :
          s(e.1.out.1, Sym2.Mem.other (Sym2.out_fst_mem e.1)) ∈ M.edgeSet := by
        rw [Sym2.other_spec (Sym2.out_fst_mem e.1)]
        exact e.property
      exact (SimpleGraph.Subgraph.mem_edgeSet).1 he
    -- A vertex cover contains at least one endpoint of each matching edge.
    by_cases hx : e.1.out.1 ∈ U
    · simp [coverEndpoint, hx]
    · rcases hU (M.adj_sub hxyM) with hxU | hyU
      · exact (hx hxU).elim
      · simpa [coverEndpoint, hx] using hyU
  have coverEndpoint_injective : Function.Injective coverEndpoint := by
    intro e₁ e₂ hEq
    have hz₁ : coverEndpoint e₁ ∈ (e₁ : Sym2 V) := coverEndpoint_mem_edge e₁
    have hz₂ : coverEndpoint e₁ ∈ (e₂ : Sym2 V) := by
      simpa [hEq] using coverEndpoint_mem_edge e₂
    let y₁ := Sym2.Mem.other hz₁
    let y₂ := Sym2.Mem.other hz₂
    have hadj₁ : M.Adj (coverEndpoint e₁) y₁ := by
      have he : s(coverEndpoint e₁, y₁) ∈ M.edgeSet := by
        have hy₁ : s(coverEndpoint e₁, y₁) = e₁.1 := Sym2.other_spec hz₁
        rw [hy₁]
        exact e₁.property
      exact (SimpleGraph.Subgraph.mem_edgeSet).1 he
    have hadj₂ : M.Adj (coverEndpoint e₁) y₂ := by
      have he : s(coverEndpoint e₁, y₂) ∈ M.edgeSet := by
        have hy₂ : s(coverEndpoint e₁, y₂) = e₂.1 := Sym2.other_spec hz₂
        rw [hy₂]
        exact e₂.property
      exact (SimpleGraph.Subgraph.mem_edgeSet).1 he
    have hy : y₁ = y₂ := hM.eq_of_adj_left hadj₁ hadj₂
    apply Subtype.ext
    calc
      e₁.1 = s(coverEndpoint e₁, y₁) := (Sym2.other_spec hz₁).symm
      _ = s(coverEndpoint e₁, y₂) := by rw [hy]
      _ = e₂.1 := Sym2.other_spec hz₂
  have hImage :
      (coverEndpoint '' (Set.univ : Set M.edgeSet)).encard = M.edgeSet.encard := by
    simpa using coverEndpoint_injective.encard_image (Set.univ : Set M.edgeSet)
  have hSubset : coverEndpoint '' (Set.univ : Set M.edgeSet) ⊆ U := by
    intro v hv
    rcases hv with ⟨e, -, rfl⟩
    exact coverEndpoint_mem_cover e
  -- Inject the matching edges into the cover by choosing one covered endpoint on each edge.
  calc
    M.edgeSet.encard = (coverEndpoint '' (Set.univ : Set M.edgeSet)).encard := hImage.symm
    _ ≤ U.encard := Set.encard_le_encard hSubset

namespace SimpleGraph.Subgraph.IsMaximumCardinalityMatching

/-- Helper for Exercise 4.20: the auxiliary-reachable vertices are those reached by a simple
`G.Walk` that starts at an uncovered vertex of `U` and follows the matching auxiliary digraph. -/
private def alternatingReachableSet (G : SimpleGraph V) (U W : Set V) (M : G.Subgraph) : Set V :=
  {x | ∃ u : V, u ∈ U \ M.support ∧ ∃ p : G.Walk u x, p.IsPath ∧
      ∀ i, i < p.length →
        (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1))}

/-- Helper for Exercise 4.20: the König cover attached to the auxiliary-reachable set `Z` is
`(U \ Z) ∪ (W ∩ Z)`. -/
private def konigCover (U W Z : Set V) : Set V :=
  (U \ Z) ∪ (W ∩ Z)

/-- Helper for Exercise 4.20: every uncovered vertex on the left side belongs to the broader
auxiliary-reachable set via the trivial walk. -/
private lemma mem_alternatingReachableSet_of_uncovered_left
    {U W : Set V} {M : G.Subgraph} {u : V} (hu : u ∈ U \ M.support) :
    u ∈ alternatingReachableSet G U W M := by
  -- The empty walk is already a valid witness from an uncovered left vertex to itself.
  refine ⟨u, hu, Walk.nil, Walk.IsPath.nil, ?_⟩
  intro i hi
  cases hi

/-- Helper for Exercise 4.20: every support vertex of an auxiliary witness remains
auxiliary-reachable after truncating the witness at that support vertex. -/
private lemma alternatingReachableSet_of_mem_support_witness
    {U W : Set V} {M : G.Subgraph} {u x y : V}
    (hu : u ∈ U \ M.support) {p : G.Walk u x} (hp : p.IsPath)
    (haux : ∀ i, i < p.length →
      (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1)))
    (hy : y ∈ p.support) :
    y ∈ alternatingReachableSet G U W M := by
  classical
  -- Truncating the witness at `y` preserves both simplicity and the auxiliary-arc condition.
  refine ⟨u, hu, p.takeUntil y hy, hp.takeUntil hy, ?_⟩
  intro i hi
  have hi' : i < p.length := lt_of_lt_of_le hi (p.length_takeUntil_le hy)
  -- The prefix walk has the same consecutive vertices as the original witness up to its length.
  simpa [p.getVert_takeUntil hy hi.le, p.getVert_takeUntil hy (Nat.succ_le_of_lt hi)] using
    haux i hi'

/-- Helper for Exercise 4.20: the broader auxiliary-reachable set is closed under one additional
auxiliary arc. -/
private lemma alternatingReachableSet_closed_under_auxiliaryArc
    {U W : Set V} {M : G.Subgraph} {x y : V}
    (hx : x ∈ alternatingReachableSet G U W M)
    (hxy : (matching_auxiliary_digraph G U W M).Adj x y) :
    y ∈ alternatingReachableSet G U W M := by
  rcases hx with ⟨u, hu, p, hp, haux⟩
  by_cases hy : y ∈ p.support
  · -- If `y` already appears on the witness path, truncate the witness at its first occurrence.
    exact alternatingReachableSet_of_mem_support_witness (G := G) hu hp haux hy
  · rcases hxy with hxy | hxy
    · -- Otherwise append the new unmatched `U → W` auxiliary arc to the witness.
      refine ⟨u, hu, p.concat hxy.2.2.1, hp.concat hy hxy.2.2.1, ?_⟩
      intro i hi
      have hi' : i < p.length + 1 := by
        simpa [SimpleGraph.Walk.length_concat] using hi
      have hi_cases : i < p.length ∨ i = p.length := by
        exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi')
      rcases hi_cases with hip | rfl
      · by_cases hip' : i + 1 < p.length
        · simpa [SimpleGraph.Walk.concat, Walk.getVert_append, hip, hip'] using haux i hip
        · have hi_eq : i + 1 = p.length := by omega
          simpa [SimpleGraph.Walk.concat, Walk.getVert_append, hip, hip', hi_eq] using haux i hip
      · simpa [SimpleGraph.Walk.concat, Walk.getVert_append] using
          (Or.inl hxy :
            (matching_auxiliary_digraph G U W M).Adj x y)
    · -- The same append step works for a matched `W → U` auxiliary arc.
      refine ⟨u, hu, p.concat hxy.2.2.adj_sub, hp.concat hy hxy.2.2.adj_sub, ?_⟩
      intro i hi
      have hi' : i < p.length + 1 := by
        simpa [SimpleGraph.Walk.length_concat] using hi
      have hi_cases : i < p.length ∨ i = p.length := by
        exact Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi')
      rcases hi_cases with hip | rfl
      · by_cases hip' : i + 1 < p.length
        · simpa [SimpleGraph.Walk.concat, Walk.getVert_append, hip, hip'] using haux i hip
        · have hi_eq : i + 1 = p.length := by omega
          simpa [SimpleGraph.Walk.concat, Walk.getVert_append, hip, hip', hi_eq] using haux i hip
      · simpa [SimpleGraph.Walk.concat, Walk.getVert_append] using
          (Or.inr hxy :
            (matching_auxiliary_digraph G U W M).Adj x y)

/-- Helper for Exercise 4.20: an auxiliary-reachable vertex on the right side must already be
matched, otherwise the auxiliary path would certify an augmenting path. -/
private lemma reachableRight_mem_support [Finite V]
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W)
    (hM : M.IsMaximumCardinalityMatching) {w : V} (hwW : w ∈ W)
    (hwZ : w ∈ alternatingReachableSet G U W M) :
    w ∈ M.support := by
  by_contra hwNot
  rcases hwZ with ⟨u, hu, p, hp, haux⟩
  have hpAux : matching_auxiliary_digraph_path G U W M p := by
    -- The witness path is now an auxiliary path between uncovered endpoints.
    exact ⟨hp, hu, ⟨hwW, hwNot⟩, haux⟩
  have hNoAug :
      ¬ ∃ (u v : V) (p : G.Walk u v), Walk.IsMatchingAugmenting M p :=
    (SimpleGraph.Subgraph.matching_has_maximum_cardinality_iff_no_augmenting_path
      (M := M) hM.isMatching).mp hM
  have hAug :
      ∃ (u v : V) (p : G.Walk u v), Walk.IsMatchingAugmenting M p := by
    rcases (exists_augmenting_path_iff_exists_auxiliary_digraph_path
      (G := G) hUW).mpr ⟨u, w, p, hpAux⟩ with ⟨u', v', p', hp', -, -⟩
    exact ⟨u', v', p', hp'⟩
  exact hNoAug hAug

/-- Helper for Exercise 4.20: along a matched edge crossing the bipartition, the two endpoints are
either both auxiliary-reachable or both not auxiliary-reachable. -/
private lemma matchedEdge_reachable_iff [Finite V]
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W)
    (hM : M.IsMaximumCardinalityMatching) {u w : V}
    (huwM : M.Adj u w) (huU : u ∈ U) (hwW : w ∈ W) :
    u ∈ alternatingReachableSet G U W M ↔
      w ∈ alternatingReachableSet G U W M := by
  constructor
  · intro huZ
    rcases huZ with ⟨x, hx, p, hp, haux⟩
    have huSupport : u ∈ M.support := (SimpleGraph.Subgraph.mem_support M).2 ⟨w, huwM⟩
    have hpn : ¬ p.Nil := by
      -- A nil witness would start at `u`, contradicting that the start is uncovered by `M`.
      intro hpnil
      exact hx.2 (hpnil.eq ▸ huSupport)
    have hpen_mem : p.penultimate ∈ p.support := by
      exact List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hpn)
    have hlastMatched : M.Adj p.penultimate u := by
      have hlast :
          (matching_auxiliary_digraph G U W M).Adj (p.penultimate) u := by
        have hlen : 0 < p.length := by
          rw [Nat.pos_iff_ne_zero]
          intro hzero
          exact hpn ((SimpleGraph.Walk.length_eq_zero_iff.mp hzero))
        simpa [SimpleGraph.Walk.penultimate, Nat.sub_add_cancel hlen] using
          haux (p.length - 1) (by omega)
      -- Since the last vertex lies in `U`, the final auxiliary arc must be a matched `W → U` arc.
      rcases hlast with hlast | hlast
      · exact (Set.disjoint_left.mp hUW.disjoint huU hlast.2.1).elim
      · exact hlast.2.2
    have hw_pen : w = p.penultimate :=
      hM.isMatching.eq_of_adj_right huwM.symm hlastMatched
    -- Prefix the witness at the penultimate vertex and identify that vertex with `w`.
    rw [hw_pen]
    exact alternatingReachableSet_of_mem_support_witness (G := G) hx hp haux hpen_mem
  · intro hwZ
    -- Route correction: the easy direction is the one-step closure under the matched arc `w → u`.
    exact alternatingReachableSet_closed_under_auxiliaryArc
      (G := G) hwZ (Or.inr ⟨hwW, huU, huwM.symm⟩)

/-- Helper for Exercise 4.20: the canonical König set `(U \ Z) ∪ (W ∩ Z)` is a vertex cover. -/
private lemma alternatingReachable_isVertexCover [Finite V]
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W)
    (hM : M.IsMaximumCardinalityMatching) :
    G.IsVertexCover (konigCover U W (alternatingReachableSet G U W M)) := by
  -- Every edge meets the canonical cover after orienting it across the bipartition.
  intro u w huwG
  let Z : Set V := alternatingReachableSet G U W M
  let C : Set V := konigCover U W Z
  have horiented :
      ∀ ⦃a b : V⦄, G.Adj a b → a ∈ U → b ∈ W → a ∈ C ∨ b ∈ C := by
    intro a b hab haU hbW
    by_cases haZ : a ∈ Z
    · have hbZ : b ∈ Z := by
        by_cases habM : M.Adj a b
        · exact (matchedEdge_reachable_iff (G := G) hUW hM habM haU hbW).mp haZ
        · exact alternatingReachableSet_closed_under_auxiliaryArc
            (G := G) haZ (Or.inl ⟨haU, hbW, hab, habM⟩)
      right
      simp [C, konigCover, Z, hbW, hbZ]
    · left
      simp [C, konigCover, Z, haU, haZ]
  rcases hUW.mem_of_adj huwG with hleft | hright
  · exact horiented huwG hleft.1 hleft.2
  · simpa [or_comm] using horiented huwG.symm hright.2 hright.1

/-- Helper for Exercise 4.20: the canonical König cover consists only of vertices matched by `M`. -/
private lemma alternatingReachableCover_subset_support [Finite V]
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W)
    (hM : M.IsMaximumCardinalityMatching) :
    konigCover U W (alternatingReachableSet G U W M) ⊆ M.support := by
  -- Left vertices outside `Z` must be matched, and right vertices inside `Z` are matched by
  -- `reachableRight_mem_support`.
  intro x hx
  rcases hx with hx | hx
  · by_contra hxNot
    exact hx.2 (mem_alternatingReachableSet_of_uncovered_left
      (G := G) ⟨hx.1, hxNot⟩)
  · exact reachableRight_mem_support (G := G) hUW hM hx.1 hx.2

/-- Helper for Exercise 4.20: every matched edge in the bipartite graph has a unique endpoint in
the canonical König cover. -/
private lemma existsUnique_konigCover_endpoint_of_matching_adj [Finite V]
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W)
    (hM : M.IsMaximumCardinalityMatching) {u w : V}
    (huwM : M.Adj u w) (huU : u ∈ U) (hwW : w ∈ W) :
    ∃! x : V,
      x ∈ (s(u, w) : Sym2 V) ∧
        x ∈ konigCover U W (alternatingReachableSet G U W M) := by
  let Z : Set V := alternatingReachableSet G U W M
  let C : Set V := konigCover U W Z
  by_cases huZ : u ∈ Z
  · have hwZ : w ∈ Z := (matchedEdge_reachable_iff (G := G) hUW hM huwM huU hwW).mp huZ
    refine ⟨w, ?_, ?_⟩
    · -- In the reachable case, the right endpoint is exactly the covered one.
      constructor
      · simp [Sym2.mem_iff]
      · simp [konigCover, Z, hwW, hwZ]
    · intro x hx
      rcases (Sym2.mem_iff.mp hx.1) with hxu | hxw
      · have hxC : u ∈ C := by simpa [hxu] using hx.2
        have huNotW : u ∉ W := Set.disjoint_left.mp hUW.disjoint huU
        have : u ∉ C := by simp [C, konigCover, Z, huU, huZ, huNotW]
        exact (this hxC).elim
      · exact hxw
  · have hwZ : w ∉ Z := by
      intro hwZ
      exact huZ ((matchedEdge_reachable_iff (G := G) hUW hM huwM huU hwW).mpr hwZ)
    refine ⟨u, ?_, ?_⟩
    · -- In the non-reachable case, the left endpoint is exactly the covered one.
      constructor
      · simp [Sym2.mem_iff]
      · simp [konigCover, Z, huU, huZ]
    · intro x hx
      rcases (Sym2.mem_iff.mp hx.1) with hxu | hxw
      · exact hxu
      · have hxC : w ∈ C := by simpa [hxw] using hx.2
        have hwNotU : w ∉ U := Set.disjoint_right.mp hUW.disjoint hwW
        have : w ∉ C := by simp [C, konigCover, Z, hwW, hwZ, hwNotU]
        exact (this hxC).elim

/-- Helper for Exercise 4.20: a maximum matching in a finite bipartite graph admits a vertex cover
whose cardinality is at most the size of the matching. -/
private lemma exists_vertexCover_encard_le_edgeSet_of_isMaximumCardinalityMatching_of_isBipartite
    [Finite V] {M : G.Subgraph} (hM : M.IsMaximumCardinalityMatching) (hG : G.IsBipartite) :
    ∃ C : Set V, G.IsVertexCover C ∧ C.encard ≤ M.edgeSet.encard := by
  classical
  rcases hG.exists_isBipartiteWith with ⟨U, W, hUW⟩
  let Z : Set V := alternatingReachableSet G U W M
  let C : Set V := konigCover U W Z
  have hCcover : G.IsVertexCover C := alternatingReachable_isVertexCover (G := G) hUW hM
  have hCsubset : C ⊆ M.support := alternatingReachableCover_subset_support (G := G) hUW hM
  have mem_support_of_mem_cover : ∀ x : C, x.1 ∈ M.support := by
    intro x
    exact hCsubset x.2
  have mem_verts_of_mem_cover : ∀ x : C, x.1 ∈ M.verts := by
    intro x
    simpa [hM.isMatching.support_eq_verts] using mem_support_of_mem_cover x
  let coverToEdge : C → M.edgeSet := fun x ↦
    hM.isMatching.toEdge ⟨x.1, mem_verts_of_mem_cover x⟩
  have hCoverToEdge_injective : Function.Injective coverToEdge := by
    intro x y hxy
    let e : M.edgeSet := coverToEdge x
    have hx_mem_edge : x.1 ∈ (e : Sym2 V) := by
      change x.1 ∈ ((coverToEdge x : M.edgeSet) : Sym2 V)
      have hx_support : x.1 ∈ M.support := mem_support_of_mem_cover x
      exact hM.isMatching.mem_coe_toEdge (by
        simpa [hM.isMatching.support_eq_verts] using hx_support)
    have hy_mem_edge : y.1 ∈ (e : Sym2 V) := by
      change y.1 ∈ ((coverToEdge x : M.edgeSet) : Sym2 V)
      simpa [hxy] using
        (hM.isMatching.mem_coe_toEdge
          (by simpa [hM.isMatching.support_eq_verts] using hCsubset y.2))
    let u := e.1.out.1
    let w := Sym2.Mem.other (Sym2.out_fst_mem e.1)
    have hEdge : (s(u, w) : Sym2 V) = e.1 := by
      exact Sym2.other_spec (Sym2.out_fst_mem e.1)
    have huwM : M.Adj u w := by
      exact (SimpleGraph.Subgraph.mem_edgeSet).1 (by
        rw [hEdge]
        exact e.property)
    have hx_mem_uw : x.1 ∈ (s(u, w) : Sym2 V) := by
      rw [hEdge]
      exact hx_mem_edge
    have hy_mem_uw : y.1 ∈ (s(u, w) : Sym2 V) := by
      rw [hEdge]
      exact hy_mem_edge
    rcases hUW.mem_of_adj huwM.adj_sub with hleft | hright
    · rcases existsUnique_konigCover_endpoint_of_matching_adj
        (G := G) hUW hM huwM hleft.1 hleft.2 with ⟨z, hz, huniq⟩
      have hxz : x.1 = z := huniq x.1 ⟨hx_mem_uw, x.2⟩
      have hyz : y.1 = z := huniq y.1 ⟨hy_mem_uw, y.2⟩
      exact Subtype.ext (hxz.trans hyz.symm)
    · rcases existsUnique_konigCover_endpoint_of_matching_adj
        (G := G) hUW hM huwM.symm hright.2 hright.1 with ⟨z, hz, huniq⟩
      have hxz : x.1 = z := huniq x.1 ⟨by simpa [Sym2.eq_swap] using hx_mem_uw, x.2⟩
      have hyz : y.1 = z := huniq y.1 ⟨by simpa [Sym2.eq_swap] using hy_mem_uw, y.2⟩
      exact Subtype.ext (hxz.trans hyz.symm)
  have hImage :
      (coverToEdge '' (Set.univ : Set C)).encard = C.encard := by
    simpa [C] using hCoverToEdge_injective.encard_image (Set.univ : Set C)
  have hImageLe :
      (coverToEdge '' (Set.univ : Set C)).encard ≤ M.edgeSet.encard := by
    -- The image lives inside the full matching edge set.
    calc
      (coverToEdge '' (Set.univ : Set C)).encard = (Set.range coverToEdge).encard := by
        simp [Set.image_univ]
      _ ≤ (Set.univ : Set M.edgeSet).encard := by
        exact Set.encard_le_encard (by
          intro e he
          simp)
      _ = M.edgeSet.encard := by
        simpa using
          (Subtype.val_injective.encard_image (Set.univ : Set M.edgeSet)).symm
  refine ⟨C, hCcover, ?_⟩
  -- Count the cover by injecting each covered vertex into its unique matching edge.
  calc
    C.encard = (coverToEdge '' (Set.univ : Set C)).encard := hImage.symm
    _ ≤ M.edgeSet.encard := hImageLe

/-- Exercise 4.20 (2): if `G` is bipartite and finite, then every maximum-cardinality matching of
`G` has cardinality equal to the minimum cardinality of a vertex cover.

Exercise 4.20 (3) asks for the same equality using Theorem 4.15 (the max-flow/min-cut theorem) as
the proof route, so the public statement remains this canonical theorem rather than a second
duplicate declaration. -/
theorem encard_edgeSet_eq_vertexCoverNum_of_isBipartite [Finite V]
    {M : G.Subgraph} (hM : M.IsMaximumCardinalityMatching) (hG : G.IsBipartite) :
    M.edgeSet.encard = G.vertexCoverNum := by
  -- Every vertex cover bounds the size of the matching from above.
  have hLower : M.edgeSet.encard ≤ G.vertexCoverNum := by
    obtain ⟨C, hCcard, hCcover⟩ := SimpleGraph.vertexCoverNum_exists G
    calc
      M.edgeSet.encard ≤ C.encard :=
        encard_edgeSet_le_encard_of_isMatching_isVertexCover M C hM.isMatching hCcover
      _ = G.vertexCoverNum := hCcard
  have hUpper : G.vertexCoverNum ≤ M.edgeSet.encard := by
    -- Route correction: package the alternating-reachability construction into one witness cover
    -- before returning to the min-max comparison in the main theorem.
    obtain ⟨C, hCcover, hCcard⟩ :=
      exists_vertexCover_encard_le_edgeSet_of_isMaximumCardinalityMatching_of_isBipartite
        (G := G) hM hG
    exact hCcover.vertexCoverNum_le.trans hCcard
  exact le_antisymm hLower hUpper

end SimpleGraph.Subgraph.IsMaximumCardinalityMatching

/-- Counterexample for Exercise 4.20 (4): the statement from Exercise 4.20 (2) does not extend to
arbitrary non-bipartite graphs; the triangle gives a counterexample. -/
theorem completeGraph_fin3_not_isBipartite_and_exists_maximumCardinalityMatching_ne_vertexCoverNum :
    ¬ (SimpleGraph.completeGraph (Fin 3)).IsBipartite ∧
      ∃ M : (SimpleGraph.completeGraph (Fin 3)).Subgraph,
        M.IsMaximumCardinalityMatching ∧
          M.edgeSet.encard ≠
        (SimpleGraph.completeGraph (Fin 3)).vertexCoverNum := by
  let G : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)
  have hNotBip : ¬ G.IsBipartite := by
    -- `K₃` is the standard odd-cycle obstruction to bipartiteness.
    intro hBip
    rcases hBip.exists_isBipartiteWith with ⟨U, W, hUW⟩
    have h01 : G.Adj 0 1 := by simp [G]
    have h02 : G.Adj 0 2 := by simp [G]
    have h12 : G.Adj 1 2 := by simp [G]
    rcases hUW.mem_of_adj h01 with h01UW | h01WU
    · have h2U : (2 : Fin 3) ∈ U := hUW.mem_of_mem_adj' h01UW.2 h12.symm
      have h2W : (2 : Fin 3) ∈ W := hUW.mem_of_mem_adj h01UW.1 h02
      exact (Set.disjoint_left.mp hUW.disjoint h2U h2W).elim
    · have h2U : (2 : Fin 3) ∈ U := hUW.mem_of_mem_adj' h01WU.1 h02.symm
      have h2W : (2 : Fin 3) ∈ W := hUW.mem_of_mem_adj h01WU.2 h12
      exact (Set.disjoint_left.mp hUW.disjoint h2U h2W).elim
  refine ⟨by simpa [G] using hNotBip, ?_⟩
  have h01 : G.Adj 0 1 := by
    simp [G]
  let M : G.Subgraph := G.subgraphOfAdj h01
  have hMmatching : M.IsMatching := SimpleGraph.Subgraph.IsMatching.subgraphOfAdj h01
  have hMone : M.edgeSet.ncard = 1 := by
    -- The witness matching consists of exactly one edge.
    simp [M, SimpleGraph.edgeSet_subgraphOfAdj]
  have hMmaximum : M.IsMaximumCardinalityMatching := by
    refine ⟨hMmatching, ?_⟩
    intro N hN
    -- Any matching in `K₃` covers `2 * |N.edgeSet|` vertices, and `K₃` has only three vertices.
    have hCount :
        2 * N.edgeSet.ncard = N.verts.ncard := by
      simpa using
        (SimpleGraph.Subgraph.matching_verts_ncard_eq_two_mul_edgeSet_ncard (K := N) hN).symm
    have hVertsLe : N.verts.ncard ≤ Nat.card (Fin 3) := by
      simpa using Set.ncard_le_ncard N.verts.subset_univ
    have hEdgeLe : 2 * N.edgeSet.ncard ≤ 3 := by
      calc
        2 * N.edgeSet.ncard = N.verts.ncard := hCount
        _ ≤ Nat.card (Fin 3) := hVertsLe
        _ = 3 := by simp
    have hNle1 : N.edgeSet.ncard ≤ 1 := by
      omega
    simpa [hMone] using hNle1
  refine ⟨M, hMmaximum, ?_⟩
  have hMcard : M.edgeSet.encard = 1 := by
    -- The witness matching is a single edge of the triangle.
    simp [M, SimpleGraph.edgeSet_subgraphOfAdj]
  have hCoverNum : G.vertexCoverNum = 2 := by
    -- A complete graph on three vertices has minimum vertex cover of size `3 - 1`.
    rw [show G = SimpleGraph.completeGraph (Fin 3) by rfl]
    rw [SimpleGraph.vertexCoverNum_top]
    rw [ENat.card_eq_coe_natCard]
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hMcard, hCoverNum]
  norm_num

end Exercise_4_20

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_4_1.ch4_sec4_4_1_definition_4_4_1_extra_1

-- Declarations for this item reuse the Chapter 4.4.1 augmenting-path owner
-- `SimpleGraph.Walk.IsMatchingAugmenting` together with mathlib's
-- `SimpleGraph.IsBipartiteWith`, `SimpleGraph.IsAlternating`, `SimpleGraph.Walk.IsPath`,
-- and `Digraph` APIs.

universe u

open SimpleGraph
open SimpleGraph.Walk

section Algorithm442Extra1

variable {V : Type u}
variable (G : SimpleGraph V)

/-- The auxiliary digraph obtained by orienting unmatched edges from `U` to `W` and matched edges
from `W` to `U`. -/
def matching_auxiliary_digraph (U W : Set V) (M : G.Subgraph) : Digraph V where
  Adj x y :=
    (x ∈ U ∧ y ∈ W ∧ G.Adj x y ∧ ¬ M.Adj x y) ∨
      x ∈ W ∧ y ∈ U ∧ M.Adj x y

/-- A walk is a directed `U \ M.support`-to-`W \ M.support` path in the auxiliary digraph when it
is simple and each consecutive edge follows the auxiliary orientation. -/
def matching_auxiliary_digraph_path
    (U W : Set V) (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧
    u ∈ U \ M.support ∧
    v ∈ W \ M.support ∧
    ∀ i, i < p.length →
      (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1))

/-- In a bipartite graph, endpoints on opposite sides cannot be joined by the nil walk. -/
lemma not_nil_of_mem_bipartition
    {U W : Set V} {u v : V} (p : G.Walk u v) (hUW : G.IsBipartiteWith U W)
    (hu : u ∈ U) (hv : v ∈ W) :
    ¬ p.Nil := by
  intro hp_nil
  have huv : u = v := Nil.eq hp_nil
  exact (Set.disjoint_left.mp hUW.disjoint hu (huv ▸ hv)).elim

/-- Helper for Algorithm 4.4.2-extra-1: the first edge of an augmenting path is an auxiliary arc. -/
lemma first_auxiliary_arc_of_is_matching_augmenting
    {U W : Set V} {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hUW : G.IsBipartiteWith U W) (hp : IsMatchingAugmenting M p)
    (hu : u ∈ U) :
    (matching_auxiliary_digraph G U W M).Adj u p.snd := by
  have hu_uncovered := hp.start_uncovered
  have hpn := hp.not_nil
  have husnd : G.Adj u p.snd := p.adj_snd hpn
  have hsndW : p.snd ∈ W := hUW.mem_of_mem_adj hu husnd
  have hnotM : ¬ M.Adj u p.snd := by
    intro husndM
    exact hu_uncovered (M.mem_support.2 ⟨p.snd, husndM⟩)
  exact Or.inl ⟨hu, hsndW, husnd, hnotM⟩

/-- Helper for Algorithm 4.4.2-extra-1: at an internal vertex of an alternating path, consecutive
path edges have opposite matching status. -/
lemma alternating_switches_matching_status {u v : V} {M : G.Subgraph} {p : G.Walk u v}
    (hp : p.IsPath) (halt : (p.toSubgraph.spanningCoe).IsAlternating M.spanningCoe)
    {i : ℕ} (hi : i + 1 < p.length) :
    M.Adj (p.getVert i) (p.getVert (i + 1)) ↔
      ¬ M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
  have hne : p.getVert i ≠ p.getVert (i + 2) := by
    intro hEq
    apply hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; lia)
      (by simp only [Set.mem_setOf_eq]; lia) at hEq
    lia
  have hprev : p.toSubgraph.Adj (p.getVert (i + 1)) (p.getVert i) := by
    simpa using (p.toSubgraph_adj_getVert (by lia : i < p.length)).symm
  have hnext : p.toSubgraph.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
    simpa using p.toSubgraph_adj_getVert hi
  have hAlt :
      M.Adj (p.getVert (i + 1)) (p.getVert i) ↔
        ¬ M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
    simpa [SimpleGraph.Subgraph.spanningCoe] using halt hne hprev hnext
  constructor
  · intro him
    exact hAlt.mp him.symm
  · intro hiNext
    by_contra him
    have hnotPrev : ¬ M.Adj (p.getVert (i + 1)) (p.getVert i) := by
      intro h
      exact him h.symm
    exact hnotPrev (hAlt.mpr hiNext)

/-- Helper for Algorithm 4.4.2-extra-1: every edge of an augmenting path follows the auxiliary
orientation. -/
lemma auxiliary_arcs_of_is_matching_augmenting
    {U W : Set V} {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hUW : G.IsBipartiteWith U W) (hp : IsMatchingAugmenting M p)
    (hu : u ∈ U) :
    ∀ i, i < p.length →
      (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1)) := by
  have hp_alt : IsMatchingAlternating M p := hp.toIsMatchingAlternating
  have hp_alt' := isMatchingAlternating_iff.mp hp_alt
  rcases hp_alt' with ⟨hp_path, hp_alt⟩
  intro i hi
  induction i with
  | zero =>
      simpa [SimpleGraph.Walk.getVert_zero] using
        first_auxiliary_arc_of_is_matching_augmenting G hUW hp hu
  | succ i ih =>
      have hcur : (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1)) :=
        ih (by lia)
      have hnextG : G.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
        exact (p.toSubgraph_adj_getVert hi).adj_sub
      have hswitch := alternating_switches_matching_status G hp_path hp_alt hi
      rcases hcur with hcur | hcur
      · have hnextMatched : M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
          by_contra hnot
          exact hcur.2.2.2 (hswitch.mpr hnot)
        exact Or.inr ⟨hcur.2.1, hUW.mem_of_mem_adj' hcur.2.1 hnextG.symm, hnextMatched⟩
      · have hnextUnmatched : ¬ M.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) :=
          hswitch.mp hcur.2.2
        exact Or.inl ⟨hcur.2.1, hUW.mem_of_mem_adj hcur.2.1 hnextG, hnextG, hnextUnmatched⟩

/-- Helper for Algorithm 4.4.2-extra-1: two consecutive auxiliary arcs around an internal vertex
force the matching status required by alternation. -/
lemma auxiliary_arcs_force_internal_matching_iff
    {U W : Set V} {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hUW : G.IsBipartiteWith U W)
    (haux : ∀ i, i < p.length →
      (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1)))
    {i : ℕ} (hi0 : 0 < i) (hil : i < p.length) :
    M.Adj (p.getVert i) (p.getVert (i - 1)) ↔
      ¬ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
  have hprev :
      (matching_auxiliary_digraph G U W M).Adj (p.getVert (i - 1)) (p.getVert i) := by
    have hpred : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_iff.mp hi0)
    simpa [hpred] using haux (i - 1) (by lia)
  have hnext := haux i hil
  rcases hprev with hprev | hprev
  · have hnotU : p.getVert i ∉ U := Set.disjoint_right.mp hUW.disjoint hprev.2.1
    have hnextMatched : M.Adj (p.getVert i) (p.getVert (i + 1)) := by
      rcases hnext with hnext | hnext
      · exact (hnotU hnext.1).elim
      · exact hnext.2.2
    constructor
    · intro him1 _
      exact hprev.2.2.2 him1.symm
    · intro hiNext
      exact (hiNext hnextMatched).elim
  · have hnotW : p.getVert i ∉ W := Set.disjoint_left.mp hUW.disjoint hprev.2.1
    have hnextUnmatched : ¬ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
      rcases hnext with hnext | hnext
      · exact hnext.2.2.2
      · exact (hnotW hnext.1).elim
    constructor
    · intro _
      exact hnextUnmatched
    · intro _
      exact hprev.2.2.symm

/-- Helper for Algorithm 4.4.2-extra-1: a path vertex with two distinct path neighbors occurs at an
internal index of the walk. -/
lemma internal_index_of_two_path_neighbors
    {u v x y z : V} {p : G.Walk u v} (hp : p.IsPath) (hpn : ¬ p.Nil)
    (hxy : p.toSubgraph.Adj x y) (hxz : p.toSubgraph.Adj x z) (hyz : y ≠ z) :
    ∃ i, 0 < i ∧ i < p.length ∧ x = p.getVert i := by
  have hx_support : x ∈ p.support := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy)
  have hx_ne_start : x ≠ u := by
    intro hxu
    have hy_mem : y ∈ p.toSubgraph.neighborSet u := by
      exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxu] using hxy
    have hz_mem : z ∈ p.toSubgraph.neighborSet u := by
      exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxu] using hxz
    rw [hp.neighborSet_toSubgraph_startpoint hpn] at hy_mem hz_mem
    exact hyz (hy_mem.trans hz_mem.symm)
  have hx_ne_end : x ≠ v := by
    intro hxv
    have hy_mem : y ∈ p.toSubgraph.neighborSet v := by
      exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxv] using hxy
    have hz_mem : z ∈ p.toSubgraph.neighborSet v := by
      exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxv] using hxz
    rw [hp.neighborSet_toSubgraph_endpoint hpn] at hy_mem hz_mem
    exact hyz (hy_mem.trans hz_mem.symm)
  obtain ⟨i, hxi, hi_le⟩ := mem_support_iff_exists_getVert.mp hx_support
  have hi0 : 0 < i := by
    have hi_ne_zero : i ≠ 0 := by
      intro hi_zero
      apply hx_ne_start
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert 0 := by simp [hi_zero]
        _ = u := p.getVert_zero
    exact Nat.pos_iff_ne_zero.mpr hi_ne_zero
  have hil : i < p.length := by
    have hi_ne_length : i ≠ p.length := by
      intro hi_length
      apply hx_ne_end
      calc
        x = p.getVert i := hxi.symm
        _ = p.getVert p.length := by simp [hi_length]
        _ = v := p.getVert_length
    exact lt_of_le_of_ne hi_le hi_ne_length
  exact ⟨i, hi0, hil, hxi.symm⟩

/-- A path in a bipartite graph with endpoints on the two sides is `M`-augmenting exactly when the
same ordered walk is a directed path in the auxiliary digraph associated with `M`. -/
theorem is_matching_augmenting_iff_auxiliary_digraph_path
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W) {u v : V} (p : G.Walk u v) :
    (IsMatchingAugmenting M p ∧ u ∈ U ∧ v ∈ W) ↔
      matching_auxiliary_digraph_path G U W M p := by
  constructor
  · rintro ⟨hp, hu, hv⟩
    have hp' := isMatchingAugmenting_iff.mp hp
    rcases hp' with ⟨hp_alt, _, hu_uncovered, hv_uncovered⟩
    have hp_alt' := isMatchingAlternating_iff.mp hp_alt
    rcases hp_alt' with ⟨hp_path, hp_alt⟩
    refine ⟨hp_path, ⟨hu, hu_uncovered⟩, ⟨hv, hv_uncovered⟩, ?_⟩
    exact auxiliary_arcs_of_is_matching_augmenting G hUW hp hu
  · intro hp
    have hp' :
        p.IsPath ∧
          u ∈ U \ M.support ∧
          v ∈ W \ M.support ∧
          ∀ i, i < p.length →
            (matching_auxiliary_digraph G U W M).Adj (p.getVert i) (p.getVert (i + 1)) := by
      simpa [matching_auxiliary_digraph_path] using hp
    rcases hp' with ⟨hp_path, hu, hv, haux⟩
    have hpn := not_nil_of_mem_bipartition G p hUW hu.1 hv.1
    have hp_alt : (p.toSubgraph.spanningCoe).IsAlternating M.spanningCoe := by
      intro x y z hyz hxy hxz
      have hxy' : p.toSubgraph.Adj x y := by
        simpa [SimpleGraph.Subgraph.spanningCoe] using hxy
      have hxz' : p.toSubgraph.Adj x z := by
        simpa [SimpleGraph.Subgraph.spanningCoe] using hxz
      change M.Adj x y ↔ ¬ M.Adj x z
      obtain ⟨i, hi0, hil, hxi⟩ :=
        internal_index_of_two_path_neighbors G hp_path hpn hxy' hxz' hyz
      have hy_mem : y ∈ p.toSubgraph.neighborSet (p.getVert i) := by
        exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxi] using hxy'
      have hz_mem : z ∈ p.toSubgraph.neighborSet (p.getVert i) := by
        exact (p.toSubgraph.mem_neighborSet _ _).2 <| by simpa [hxi] using hxz'
      rw [hp_path.neighborSet_toSubgraph_internal (by lia) hil] at hy_mem hz_mem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_mem hz_mem
      rcases hy_mem with rfl | rfl
      · rcases hz_mem with rfl | rfl
        · exact (hyz rfl).elim
        · simpa [hxi] using
            auxiliary_arcs_force_internal_matching_iff G hUW haux hi0 hil
      · rcases hz_mem with rfl | rfl
        · have hlocal :=
            auxiliary_arcs_force_internal_matching_iff G hUW haux hi0 hil
          constructor
          · intro hyMatched hzMatched
            have hnot : ¬ M.Adj (p.getVert i) (p.getVert (i + 1)) := by
              exact hlocal.mp (by simpa [hxi] using hzMatched)
            exact hnot (by simpa [hxi] using hyMatched)
          · intro hyNotMatched
            by_contra hzNotMatched
            have hprevMatched : M.Adj (p.getVert i) (p.getVert (i - 1)) := by
              exact hlocal.mpr (by simpa [hxi] using hzNotMatched)
            exact hyNotMatched (by simpa [hxi] using hprevMatched)
        · exact (hyz rfl).elim
    have hp_alt_class : IsMatchingAlternating M p :=
      isMatchingAlternating_iff.mpr ⟨hp_path, hp_alt⟩
    have hp_aug : IsMatchingAugmenting M p :=
      isMatchingAugmenting_iff.mpr ⟨hp_alt_class, hpn, hu.2, hv.2⟩
    exact ⟨hp_aug, hu.1, hv.1⟩

/-- Algorithm 4.4.2-extra-1. In a bipartite graph, there exists an `M`-augmenting path with
endpoints on `U` and `W` if and only if there exists a directed path in the auxiliary digraph from
an uncovered vertex of `U` to an uncovered vertex of `W`. -/
theorem exists_augmenting_path_iff_exists_auxiliary_digraph_path
    {U W : Set V} {M : G.Subgraph} (hUW : G.IsBipartiteWith U W) :
    (∃ (u v : V) (p : G.Walk u v), IsMatchingAugmenting M p ∧ u ∈ U ∧ v ∈ W) ↔
      ∃ (u v : V) (p : G.Walk u v), matching_auxiliary_digraph_path G U W M p := by
  constructor
  · rintro ⟨u, v, p, hp, hu, hv⟩
    exact ⟨u, v, p, (is_matching_augmenting_iff_auxiliary_digraph_path
      G hUW p).mp ⟨hp, hu, hv⟩⟩
  · rintro ⟨u, v, p, hp⟩
    exact ⟨u, v, p, (is_matching_augmenting_iff_auxiliary_digraph_path
      G hUW p).mpr hp⟩

end Algorithm442Extra1

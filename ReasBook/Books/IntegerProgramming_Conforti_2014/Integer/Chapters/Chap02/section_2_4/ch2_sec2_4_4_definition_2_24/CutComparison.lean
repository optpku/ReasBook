module

import Mathlib.Tactic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_24.OddCycleHittingSet

public section

universe u

namespace SimpleGraph.OddCycleHittingSet

/-- Helper for Definition 2.24: a cut containment witness for an edge set is equivalent to
bipartiteness of the simple graph with exactly those edges. -/
theorem existsCutContainingEdgeSetIffIsBipartiteFromEdgeSet {V : Type u} (G : SimpleGraph V)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    (∃ S : Set V, F ⊆ (G.between S Sᶜ).edgeSet) ↔ (SimpleGraph.fromEdgeSet F).IsBipartite := by
  constructor
  · rintro ⟨S, hS⟩
    -- A cut witness induces the same bipartition on the graph formed by the chosen edges.
    refine SimpleGraph.IsBipartiteWith.isBipartite
      (G := SimpleGraph.fromEdgeSet F) (s := S) (t := Sᶜ) ?_
    refine ⟨disjoint_compl_right, ?_⟩
    intro v w hvw
    have hvw' : s(v, w) ∈ F ∧ v ≠ w := by
      simpa [SimpleGraph.fromEdgeSet_adj] using hvw
    have hEdge : s(v, w) ∈ F := hvw'.1
    have hCutEdge : s(v, w) ∈ (G.between S Sᶜ).edgeSet := hS hEdge
    exact (SimpleGraph.between_adj.mp ((G.between S Sᶜ).mem_edgeSet.mp hCutEdge)).2
  · intro hBip
    rcases hBip.exists_isBipartiteWith with ⟨S, T, hST⟩
    refine ⟨S, ?_⟩
    intro e heF
    -- An edge of `F` is an edge of `G`, so bipartiteness forces it to cross from `S` to `Sᶜ`.
    induction e using Sym2.ind with
    | h v w =>
        have hGAdj : G.Adj v w := G.mem_edgeSet.mp (hF heF)
        have hFromAdj : (SimpleGraph.fromEdgeSet F).Adj v w := by
          rw [SimpleGraph.fromEdgeSet_adj]
          exact ⟨heF, G.ne_of_adj hGAdj⟩
        apply (G.between S Sᶜ).mem_edgeSet.mpr
        rw [SimpleGraph.between_adj]
        refine ⟨hGAdj, ?_⟩
        rcases hST.mem_of_adj hFromAdj with hCross | hCross
        · left
          have hwSc : w ∈ Sᶜ := by
            change w ∉ S
            intro hwS
            exact Set.disjoint_left.mp hST.disjoint hwS hCross.2
          exact ⟨hCross.1, hwSc⟩
        · right
          have hvSc : v ∈ Sᶜ := by
            change v ∉ S
            intro hvS
            exact Set.disjoint_left.mp hST.disjoint hvS hCross.1
          exact ⟨hvSc, hCross.2⟩

/-- Helper for Definition 2.24: if every cycle in a graph has even length, then every closed walk
in that graph has even length. -/
lemma evenLengthClosedWalkOfCycleEven {V : Type u} (H : SimpleGraph V)
    (hCycleEven : ∀ v : V, ∀ p : H.Walk v v, p.IsCycle → Even p.length) :
    ∀ v : V, ∀ p : H.Walk v v, Even p.length := by
  classical
  have hEven :
      ∀ n : ℕ, ∀ v : V, ∀ p : H.Walk v v, p.length = n → Even p.length := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih v p hpLen
    cases p with
    | nil =>
        -- The empty walk has length `0`.
        simp
    | @cons v w _ hvw q =>
        by_cases hshort : (SimpleGraph.Walk.cons hvw q).length < 3
        · -- A short closed walk is forced into the trivial even cases.
          cases q with
          | nil =>
              exact False.elim ((H.ne_of_adj hvw) rfl)
          | cons hwx r =>
              cases r with
              | nil =>
                  simp [SimpleGraph.Walk.length_cons]
              | cons hxy s =>
                  simp [SimpleGraph.Walk.length_cons] at hshort
                  omega
        · by_cases hpCycle : (SimpleGraph.Walk.cons hvw q).IsCycle
          · -- Cycles are even by the hypothesis supplied to the helper.
            simpa using hCycleEven v (SimpleGraph.Walk.cons hvw q) hpCycle
          · -- A non-cycle closed walk of length at least `3` contains a shorter nontrivial
            -- closed subwalk in its tail; apply induction to both pieces.
            have hlong : 3 ≤ (SimpleGraph.Walk.cons hvw q).length := by
              omega
            have hqNotPath : ¬ q.IsPath := by
              intro hqPath
              exact hpCycle <|
                (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2 <| by
                  simpa [SimpleGraph.Walk.length_cons] using And.intro hqPath hlong
            have hqHasSubwalk :
                ∃ x, ∃ r : H.Walk x x, r.IsSubwalk q ∧ ¬ r.Nil := by
              by_contra hNoSubwalk
              apply hqNotPath
              rw [SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil]
              intro x r hrSub
              by_contra hrNotNil
              exact hNoSubwalk ⟨x, r, hrSub, hrNotNil⟩
            rcases hqHasSubwalk with ⟨x, r, hrSub, hrNotNil⟩
            rcases hrSub with ⟨a, b, hqDecomp⟩
            let s : H.Walk v v := (SimpleGraph.Walk.cons hvw a).append b
            have hrLenWalk : r.length < (SimpleGraph.Walk.cons hvw q).length := by
              rw [hqDecomp]
              simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
                Nat.add_left_comm, Nat.add_comm]
              have hrPos : 0 < r.length := by
                simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hrNotNil
              omega
            have hsLenWalk : s.length < (SimpleGraph.Walk.cons hvw q).length := by
              dsimp [s]
              rw [hqDecomp]
              simp [SimpleGraph.Walk.length_append, Nat.add_left_comm, Nat.add_comm]
              have hrPos : 0 < r.length := by
                simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hrNotNil
              omega
            have hrEven : Even r.length :=
              ih r.length (by simpa [hpLen] using hrLenWalk) x r rfl
            have hsEven : Even s.length :=
              ih s.length (by simpa [hpLen] using hsLenWalk) v s rfl
            have hpSplit : (SimpleGraph.Walk.cons hvw q).length = r.length + s.length := by
              dsimp [s]
              rw [hqDecomp]
              simp [SimpleGraph.Walk.length_append, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm]
            rw [hpSplit]
            exact hrEven.add hsEven
  intro v p
  exact hEven p.length v p rfl

/-- Helper for Definition 2.24: an edge family is contained in a cut iff deleting it from
`G.edgeSet` yields a feasible odd-cycle hitting set. -/
theorem existsCutContainingEdgeSetIffFeasibleEdgeSetDiff {V : Type u}
    (G : SimpleGraph V) (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    (∃ S : Set V, F ⊆ (G.between S Sᶜ).edgeSet) ↔ feasible G (G.edgeSet \ F) := by
  constructor
  · intro hCut
    -- If all cycle edges lay in `F`, they would form an odd closed walk in the bipartite graph
    -- `fromEdgeSet F`, which is impossible.
    have hBip := (existsCutContainingEdgeSetIffIsBipartiteFromEdgeSet G F hF).mp hCut
    have hEven := (SimpleGraph.two_colorable_iff_forall_loop_even.mp hBip)
    rw [feasible_iff]
    constructor
    · exact Set.diff_subset
    · intro u p hpCycle hpOdd
      classical
      by_contra hNoEdge
      have hAllInF : ∀ e, e ∈ p.edges → e ∈ F := by
        intro e he
        by_contra heNotF
        exact hNoEdge ⟨e, he, ⟨p.edges_subset_edgeSet he, heNotF⟩⟩
      have hpInFrom : ∀ e, e ∈ p.edges → e ∈ (SimpleGraph.fromEdgeSet F).edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | h v w =>
            apply (SimpleGraph.fromEdgeSet F).mem_edgeSet.mpr
            rw [SimpleGraph.fromEdgeSet_adj]
            exact ⟨hAllInF _ he, G.ne_of_adj (p.edges_subset_edgeSet he)⟩
      let pF : (SimpleGraph.fromEdgeSet F).Walk u u :=
        p.transfer (SimpleGraph.fromEdgeSet F) hpInFrom
      have hpEven : Even pF.length := hEven u pF
      have hpOdd' : Odd pF.length := by
        simpa [pF, p.length_transfer hpInFrom] using hpOdd
      rcases hpEven with ⟨k, hk⟩
      rcases hpOdd' with ⟨l, hl⟩
      omega
  · intro hFeasible
    rw [feasible_iff] at hFeasible
    have hFromLe : SimpleGraph.fromEdgeSet F ≤ G := by
      rw [SimpleGraph.fromEdgeSet_le]
      exact Set.Subset.trans Set.diff_subset hF
    have hCycleEven :
        ∀ u : V, ∀ p : (SimpleGraph.fromEdgeSet F).Walk u u, p.IsCycle → Even p.length := by
      intro u p hpCycle
      -- Map a cycle in `fromEdgeSet F` back to `G`; feasibility forces an odd one to meet the
      -- complement `G.edgeSet \ F`, but all of its edges still lie in `F`.
      by_contra hpEven
      have hpOdd : Odd p.length := Nat.not_even_iff_odd.mp hpEven
      have hpLenMap : (p.mapLe hFromLe).length = p.length := by
        simpa [SimpleGraph.Walk.mapLe] using
          (SimpleGraph.Walk.length_map (f := SimpleGraph.Hom.ofLE hFromLe) (p := p))
      have hpOddMap : Odd (p.mapLe hFromLe).length := by
        rw [hpLenMap]
        exact hpOdd
      rcases hFeasible.2 u (p.mapLe hFromLe) (hpCycle.mapLe hFromLe) hpOddMap with
        ⟨e, heEdge, heDiff⟩
      have heEdge' : e ∈ p.edges := by
        simpa [p.edges_mapLe_eq_edges hFromLe] using heEdge
      have heFrom : e ∈ (SimpleGraph.fromEdgeSet F).edgeSet := p.edges_subset_edgeSet heEdge'
      have heInF : e ∈ F := by
        rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff] at heFrom
        exact heFrom.1
      exact heDiff.2 heInF
    have hEvenLoops :
        ∀ u : V, ∀ p : (SimpleGraph.fromEdgeSet F).Walk u u, Even p.length :=
      evenLengthClosedWalkOfCycleEven (SimpleGraph.fromEdgeSet F) hCycleEven
    have hBip : (SimpleGraph.fromEdgeSet F).IsBipartite :=
      (SimpleGraph.two_colorable_iff_forall_loop_even).2 hEvenLoops
    exact (existsCutContainingEdgeSetIffIsBipartiteFromEdgeSet G F hF).2 hBip

end SimpleGraph.OddCycleHittingSet

end

/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_24.CutComparison

public section

universe u

open SimpleGraph.OddCycleHittingSet

/-- Proposition 2.12. An edge subset `F` of an undirected graph `G` is contained in some cut
iff every odd cycle of `G` contains an edge outside `F`. -/
theorem existsCutContainingEdgeSetIffForallOddCycleHasEdgeOutside {V : Type u}
    (G : SimpleGraph V) (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    (∃ S : Set V, F ⊆ (G.between S Sᶜ).edgeSet) ↔
      ∀ u : V, ∀ p : G.Walk u u, p.IsCycle → Odd p.length → ∃ e, e ∈ p.edges ∧ e ∉ F := by
  rw [existsCutContainingEdgeSetIffFeasibleEdgeSetDiff G F hF, feasible_iff]
  constructor
  · intro h u p hpCycle hpOdd
    rcases h.2 u p hpCycle hpOdd with ⟨e, heEdge, heDiff⟩
    exact ⟨e, heEdge, heDiff.2⟩
  · intro h
    refine ⟨Set.diff_subset, ?_⟩
    intro u p hpCycle hpOdd
    rcases h u p hpCycle hpOdd with ⟨e, heEdge, heNotF⟩
    exact ⟨e, heEdge, ⟨p.edges_subset_edgeSet heEdge, heNotF⟩⟩

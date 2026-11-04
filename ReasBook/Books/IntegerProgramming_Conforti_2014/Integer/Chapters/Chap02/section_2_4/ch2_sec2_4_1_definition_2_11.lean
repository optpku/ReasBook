/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_1_proposition_2_5.SetPacking

public section

universe u

/- Definition 2.11 (1): a stable set of an undirected graph is modeled by
`SimpleGraph.IsIndepSet`. -/
#check SimpleGraph.IsIndepSet

namespace SimpleGraph

section

variable {V : Type u}

/-- Helper for Definition 2.11: a binary support is independent exactly when every edge has
coordinate sum at most one. -/
private lemma isIndepSet_support_iff_forall_adj_sum_le_one
    (G : SimpleGraph V) (x : V → ℤ) (hbin : ∀ v, x v = 0 ∨ x v = 1) :
    G.IsIndepSet (Function.support x) ↔
      ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1 := by
  constructor
  · intro hInd u v hAdj
    -- Split the binary endpoint values; only the one-one case can violate the bound.
    rcases hbin u with huZero | huOne
    · rcases hbin v with hvZero | hvOne
      · omega
      · omega
    · rcases hbin v with hvZero | hvOne
      · omega
      · have huMem : u ∈ Function.support x :=
          Function.mem_support.mpr (huOne.trans_ne one_ne_zero)
        have hvMem : v ∈ Function.support x :=
          Function.mem_support.mpr (hvOne.trans_ne one_ne_zero)
        -- Independence excludes an edge whose two endpoints both lie in the support.
        exact (hInd huMem hvMem hAdj.ne) hAdj |>.elim
  · intro hBound
    rw [SimpleGraph.isIndepSet_iff]
    intro u huMem v hvMem huv hAdj
    -- Nonzero binary support coordinates must both equal one.
    have huOne : x u = 1 := (hbin u).resolve_left huMem
    have hvOne : x v = 1 := (hbin v).resolve_left hvMem
    have hSum := hBound hAdj
    omega

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_1_definition_2_11.lean

Definition 2.11 (2): the stable set family `stab(G)` in characteristic-vector form consists of
the binary integer vectors satisfying `x u + x v ≤ 1` for every adjacent pair `u`, `v`. -/
theorem mem_stableSetFamily_iff_forall_adj
    {G : SimpleGraph V} {x : V → ℤ} :
    x ∈ G.stableSetFamily ↔
      (∀ v, x v = 0 ∨ x v = 1) ∧
        ∀ ⦃u v : V⦄, G.Adj u v → x u + x v ≤ 1 := by
  -- Use the imported membership API because the public family definition is opaque downstream.
  rw [mem_stableSetFamily_iff]
  -- Replace support independence by the edge-sum bridge while preserving binarity.
  apply and_congr_right
  intro hbin
  exact isIndepSet_support_iff_forall_adj_sum_le_one G x hbin

#print axioms mem_stableSetFamily_iff_forall_adj

end

end SimpleGraph

end

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

public section

universe u

namespace SimpleGraph

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_23.lean`: an odd closed
walk in a simple graph has at least three edges. -/
private lemma Walk.threeLeLengthOfOddLoop {V : Type u} {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hOdd : Odd w.length) : 3 ≤ w.length := by
  -- A one-edge closed walk would be a forbidden loop in a simple graph.
  have hLengthNeOne : w.length ≠ 1 := by
    intro hLength
    have hZeroLt : 0 < w.length := by omega
    have hLengthLe : w.length ≤ 1 := by omega
    have hAdj : G.Adj (w.getVert 0) (w.getVert 1) :=
      w.adj_getVert_succ hZeroLt
    have hSame : w.getVert 0 = w.getVert 1 := by
      rw [w.getVert_zero, w.getVert_of_length_le hLengthLe]
    exact hAdj.ne hSame
  -- Oddness excludes lengths zero and two, leaving the required lower bound.
  obtain ⟨k, hk⟩ := hOdd
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_23.lean`: if the tail of
a closed walk is not a path, a nonempty closed subwalk and its complement are both shorter. -/
private lemma Walk.existsShorterLoopsOfNotIsPathTail {V : Type u} {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hNotPath : ¬ w.tail.IsPath) :
    ∃ (u : V) (c : G.Walk u u) (r : G.Walk v v),
      c.length < w.length ∧ r.length < w.length ∧ c.length + r.length = w.length := by
  classical
  -- A nil walk has a path as its tail, so the original walk has a first edge.
  have hNotNil : ¬ w.Nil := by
    intro hNil
    cases hNil
    exact hNotPath Walk.IsPath.nil
  -- Failure of pathhood supplies a nonempty closed subwalk of the tail.
  rw [Walk.isPath_iff_isSubwalk_imp_nil] at hNotPath
  push Not at hNotPath
  obtain ⟨u, c, hcSubwalk, hcNotNil⟩ := hNotPath
  have hcLengthLe := Walk.length_le_of_isSubwalk hcSubwalk
  obtain ⟨left, right, hSplit⟩ := hcSubwalk
  let r : G.Walk v v := (left.append right).cons (w.adj_snd hNotNil)
  refine ⟨u, c, r, ?_, ?_, ?_⟩
  · -- The closed subwalk lies in the tail, which is strictly shorter than `w`.
    have hTailShort : w.tail.length < w.length := by
      have := w.length_tail_add_one hNotNil
      omega
    exact hcLengthLe.trans_lt hTailShort
  · -- Removing a nonempty subwalk strictly decreases the complementary loop's length.
    have hPositive : 0 < c.length := Walk.not_nil_iff_lt_length.mp hcNotNil
    have hLengths := congrArg Walk.length hSplit
    have hTailLength := w.length_tail_add_one hNotNil
    dsimp only [r]
    simp only [Walk.length_append, Walk.length_cons] at hLengths ⊢
    omega
  · -- The subwalk and complementary loop partition all edges of `w`.
    have hLengths := congrArg Walk.length hSplit
    have hTailLength := w.length_tail_add_one hNotNil
    dsimp only [r]
    simp only [Walk.length_append, Walk.length_cons] at hLengths ⊢
    omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_23.lean`: every odd
non-cycle closed walk contains a strictly shorter odd closed walk. -/
private lemma Walk.existsShorterOddLoopOfNotIsCycle {V : Type u} {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hOdd : Odd w.length) (hNotCycle : ¬ w.IsCycle) :
    ∃ (u : V) (q : G.Walk u u), Odd q.length ∧ q.length < w.length := by
  -- The cycle criterion reduces non-cyclicity to a repeated vertex in the tail.
  have hNotPath : ¬ w.tail.IsPath := by
    intro hPath
    exact hNotCycle (Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨hPath, w.threeLeLengthOfOddLoop hOdd⟩)
  obtain ⟨u, c, r, hcShort, hrShort, hLengths⟩ :=
    w.existsShorterLoopsOfNotIsPathTail hNotPath
  -- Since the two new lengths sum to an odd number, one of them is odd.
  by_cases hcOdd : Odd c.length
  · exact ⟨u, c, hcOdd, hcShort⟩
  · refine ⟨v, r, ?_, hrShort⟩
    have hSumOdd : Odd (c.length + r.length) := by
      rwa [hLengths]
    have hrNotEven : ¬ Even r.length := fun hrEven ↦
      hcOdd ((Nat.odd_add.mp hSumOdd).mpr hrEven)
    exact Nat.not_even_iff_odd.mp hrNotEven

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_23.lean`: every odd
closed walk contains an odd cycle. -/
private lemma Walk.existsOddCycleOfOddLoop {V : Type u} {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hOdd : Odd w.length) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length := by
  -- Strong induction repeatedly replaces a non-cycle by the shorter odd loop above.
  refine Nat.strong_induction_on w.length (p := fun n ↦
    ∀ {v : V} (q : G.Walk v v), q.length = n → Odd q.length →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ Odd c.length) ?_ w rfl hOdd
  intro n ih v q hLength hqOdd
  by_cases hqCycle : q.IsCycle
  · exact ⟨v, q, hqCycle, hqOdd⟩
  · obtain ⟨u, r, hrOdd, hrShort⟩ :=
      q.existsShorterOddLoopOfNotIsCycle hqOdd hqCycle
    have hrLength : r.length < n := by omega
    exact ih r.length hrLength r rfl hrOdd

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_23.lean.
Proposition 2.23. An undirected graph `G` is bipartite if and only if every cycle witness
`p : G.Walk v v` has non-odd length. -/
theorem isBipartite_iff_no_odd_cycle {V : Type u} (G : SimpleGraph V) :
    G.IsBipartite ↔ ∀ v : V, ∀ p : G.Walk v v, p.IsCycle → ¬ Odd p.length := by
  -- Use the all-closed-walk parity characterization of two-colorability.
  constructor
  · intro hBipartite v p _
    have hEven := two_colorable_iff_forall_loop_even.mp hBipartite
    exact Nat.not_odd_iff_even.mpr (hEven v p)
  · intro hNoOddCycle
    apply two_colorable_iff_forall_loop_even.mpr
    intro v p
    refine Nat.not_odd_iff_even.mp ?_
    intro hpOdd
    -- Extracting an odd cycle turns the assumed odd loop into an immediate contradiction.
    obtain ⟨u, c, hcCycle, hcOdd⟩ := p.existsOddCycleOfOddLoop hpOdd
    exact hNoOddCycle u c hcCycle hcOdd

end SimpleGraph

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_2_proposition_2_6.StableSetPolytope
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1

open scoped Matrix

section Proposition_2_6

variable {V : Type} (G : SimpleGraph V)

/- Proposition 2.6 (1) [Validity and characterization of clique inequalities]. If `K` is a
clique of `G`, then the inequality `∑ j ∈ K, x j ≤ 1` is valid for `STAB(G)`. -/
#check clique_sum_le_one_on_stableSetPolytope

/-- Proposition 2.6 (1), in the canonical valid-inequality owner: the clique inequality with
coefficient vector `stableSetIndicator K` is valid for `STAB(G)`. -/
theorem clique_indicator_valid_inequality_on_stableSetPolytope
    [Fintype V] {K : Finset V} (hK : G.IsClique K) :
    is_valid_inequality (STAB(G)) (stableSetIndicator K) 1 := by
  -- Reuse the canonical clique-sum validity theorem from the stable-set owner file.
  rw [is_valid_inequality_iff]
  intro x hx
  simpa [dotProduct, stableSetIndicator, Finset.sum_ite_mem] using
    clique_sum_le_one_on_stableSetPolytope G K hK x hx

/-- Helper for Proposition 2.6: a pair of distinct nonadjacent vertices forms an independent
set. -/
lemma isIndepSet_pair_of_not_adj [DecidableEq V] {u v : V} (huv : u ≠ v)
    (hNotAdj : ¬ G.Adj u v) :
    G.IsIndepSet ({u, v} : Finset V) := by
  rw [SimpleGraph.isIndepSet_iff]
  -- Check the only possible membership cases in the two-vertex finset.
  intro a ha b hb hab
  have ha' : a = u ∨ a = v := by
    simpa using ha
  have hb' : b = u ∨ b = v := by
    simpa using hb
  rcases ha' with rfl | rfl
  · rcases hb' with rfl | rfl
    · exact (hab rfl).elim
    · simpa [SimpleGraph.adj_comm] using hNotAdj
  · rcases hb' with rfl | rfl
    · simpa [SimpleGraph.adj_comm] using hNotAdj
    · exact (hab rfl).elim

/-- Helper for Proposition 2.6: the indicator of a distinct nonadjacent pair belongs to
`STAB(G)`. -/
theorem pairIndicator_mem_stableSetPolytope_of_not_adj [DecidableEq V] {u v : V} (huv : u ≠ v)
    (hNotAdj : ¬ G.Adj u v) :
    stableSetIndicator ({u, v} : Finset V) ∈ STAB(G) := by
  -- Package the graph-theoretic pair witness into the canonical stable-set vertex theorem.
  exact stableSetIndicator_mem_stableSetPolytope G <|
    isIndepSet_pair_of_not_adj G huv hNotAdj

/-- Helper for Proposition 2.6: if `Q` contains two distinct vertices, then summing the
indicator of that pair over `Q` is at least `2`. -/
lemma two_le_sum_stableSetIndicator_pair_of_mem [DecidableEq V] {Q : Finset V} {u v : V}
    (hu : u ∈ Q)
    (hv : v ∈ Q) (huv : u ≠ v) :
    (2 : ℝ) ≤ Q.sum (stableSetIndicator ({u, v} : Finset V)) := by
  have hsubset : ({u, v} : Finset V) ⊆ Q := by
    intro w hw
    have hw' : w = u ∨ w = v := by
      simpa using hw
    rcases hw' with rfl | rfl <;> assumption
  have hpairSum :
      ({u, v} : Finset V).sum (stableSetIndicator ({u, v} : Finset V)) =
        ({u, v} : Finset V).sum (fun _ ↦ (1 : ℝ)) := by
    -- Every point of the pair contributes `1` to its own indicator vector.
    refine Finset.sum_congr rfl ?_
    intro w hw
    simpa using stableSetIndicator_of_mem hw
  calc
    (2 : ℝ) = ({u, v} : Finset V).sum (fun _ ↦ (1 : ℝ)) := by
      simp [huv]
    _ = ({u, v} : Finset V).sum (stableSetIndicator ({u, v} : Finset V)) := by
      exact hpairSum.symm
    _ ≤ Q.sum (stableSetIndicator ({u, v} : Finset V)) := by
      -- Enlarging the summation set can only increase the sum because all indicator values are
      -- nonnegative.
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro w hwQ hwPair
      by_cases hmem : w ∈ ({u, v} : Finset V)
      · exact False.elim (hwPair hmem)
      · have hne : ¬ (w = u ∨ w = v) := by
          simpa using hmem
        simp [stableSetIndicator, hne]

/-- Proposition 2.6 (2) [Validity and characterization of clique inequalities]. If the
inequality `∑ j ∈ Q, x j ≤ 1` is valid for `STAB(G)`, then `Q` is a clique of `G`. -/
theorem isClique_of_clique_inequality_valid_on_stableSetPolytope
    {Q : Finset V}
    (hQ : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → Q.sum x ≤ 1) :
    G.IsClique Q := by
  classical
  by_contra hNotClique
  rw [SimpleGraph.not_isClique_iff] at hNotClique
  rcases hNotClique with ⟨u, v, huv, hNotAdj⟩
  have huv_val : u.1 ≠ v.1 := by
    exact fun h ↦ huv (Subtype.ext h)
  have hPairMem :
      stableSetIndicator ({u.1, v.1} : Finset V) ∈ STAB(G) :=
    pairIndicator_mem_stableSetPolytope_of_not_adj G huv_val (by simpa using hNotAdj)
  have hTwoLe :
      (2 : ℝ) ≤ Q.sum (stableSetIndicator ({u.1, v.1} : Finset V)) :=
    two_le_sum_stableSetIndicator_pair_of_mem u.2 v.2 huv_val
  have hOneGe :
      Q.sum (stableSetIndicator ({u.1, v.1} : Finset V)) ≤ 1 :=
    hQ hPairMem
  -- The pair indicator gives value at least `2` on `Q`, contradicting the assumed validity.
  exact (not_le_of_gt (show (2 : ℝ) > 1 from one_lt_two)) (le_trans hTwoLe hOneGe)

/-- Proposition 2.6 [Validity and characterization of clique inequalities]. A finite set `K` of
vertices is a clique of `G` if and only if `∑ j ∈ K, x j ≤ 1` holds for every `x ∈ STAB(G)`. -/
theorem isClique_iff_clique_sum_le_one_on_stableSetPolytope [Finite V] {K : Finset V} :
    G.IsClique K ↔ ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → K.sum x ≤ 1 := by
  constructor
  · intro hK x hx
    exact clique_sum_le_one_on_stableSetPolytope G K hK x hx
  · exact isClique_of_clique_inequality_valid_on_stableSetPolytope G

/-- Companion bridge for Proposition 2.6 in the canonical Chapter 3 owner
`is_valid_inequality`. -/
theorem isClique_iff_clique_indicator_valid_inequality_on_stableSetPolytope
    [Fintype V] {K : Finset V} :
    G.IsClique K ↔ is_valid_inequality (STAB(G)) (stableSetIndicator K) 1 := by
  rw [is_valid_inequality_iff]
  simpa [dotProduct, stableSetIndicator, Finset.sum_ite_mem] using
    (isClique_iff_clique_sum_le_one_on_stableSetPolytope G :
      G.IsClique K ↔ ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → K.sum x ≤ 1)

end Proposition_2_6

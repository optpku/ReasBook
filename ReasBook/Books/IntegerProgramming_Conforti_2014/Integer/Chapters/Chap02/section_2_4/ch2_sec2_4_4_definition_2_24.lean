/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Bounds.Defs
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_24.CutComparison
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_24.OddCycleHittingSet
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Weight

open scoped BigOperators

public section

universe u

/-!
Odd-cycle hitting-set formulation of weighted max-cut on an undirected graph.

The reusable owner is `SimpleGraph.OddCycleHittingSet`; the declarations below record the
textbook cut-complement bridge and optimization equivalence for Definition 2.24.
-/

/- The canonical owners for Definition 2.24 are the reusable odd-cycle hitting-set declarations
below. -/
#check SimpleGraph.OddCycleHittingSet.feasible
#check SimpleGraph.OddCycleHittingSet.objective
#check SimpleGraph.OddCycleHittingSet.objectiveValues

namespace SimpleGraph.OddCycleHittingSet

/-- Definition 2.24 (1). An edge set `H` is a feasible odd-cycle hitting set in `G` iff it is an
edge subset of `G` and its complement inside `G.edgeSet` is contained in a cut edge set. -/
theorem feasible_iff_edgeSet_diff_subset_cut {V : Type u}
    (G : SimpleGraph V) (H : Set (Sym2 V)) :
    feasible G H ↔
      H ⊆ G.edgeSet ∧ ∃ S : Set V, G.edgeSet \ H ⊆ (G.between S Sᶜ).edgeSet := by
  have hEdgeSetDiffDiff (hH : H ⊆ G.edgeSet) : G.edgeSet \ (G.edgeSet \ H) = H := by
    ext e
    constructor
    · intro he
      by_contra heH
      exact he.2 ⟨he.1, heH⟩
    · intro heH
      exact ⟨hH heH, fun heDiff ↦ heDiff.2 heH⟩
  constructor
  · intro hFeasible
    rcases feasible_iff.mp hFeasible with ⟨hH, hMeetOddCycles⟩
    refine ⟨hH, ?_⟩
    exact
      (existsCutContainingEdgeSetIffFeasibleEdgeSetDiff G (G.edgeSet \ H) Set.diff_subset).2
        (by
          simpa [hEdgeSetDiffDiff hH] using
            (feasible_iff.mpr ⟨hH, hMeetOddCycles⟩))
  · rintro ⟨hH, S, hDiffSubset⟩
    have hFeasibleDiff : feasible G (G.edgeSet \ (G.edgeSet \ H)) :=
      (existsCutContainingEdgeSetIffFeasibleEdgeSetDiff G (G.edgeSet \ H) Set.diff_subset).1
        ⟨S, hDiffSubset⟩
    simpa [hEdgeSetDiffDiff hH] using hFeasibleDiff

/-- In a finite graph, a set-valued cut witness can be replaced by a finset witness without
changing the cut containment statement. This helper remains private to the optimization bridge. -/
private theorem existsFinsetCutWitnessOfDiffSubset {V : Type u}
    (G : SimpleGraph V) [Finite V]
    {H : Set (Sym2 V)} {S : Set V}
    (hDiffSubset : G.edgeSet \ H ⊆ (G.between S Sᶜ).edgeSet) :
    ∃ Sfin : Finset V,
      G.edgeSet \ H ⊆ (G.between (Sfin : Set V) ((Sfin : Set V)ᶜ)).edgeSet := by
  classical
  let Sfin : Finset V := S.toFinite.toFinset
  refine ⟨Sfin, ?_⟩
  have hSfin : ((Sfin : Finset V) : Set V) = S := by
    simp [Sfin]
  -- Rewrite the cut determined by the finset witness back to the original set witness.
  simpa [hSfin] using hDiffSubset

/-- Helper for Definition 2.24: enlarging the chosen edge set can only increase the odd-cycle
hitting-set objective when all edge weights are nonnegative. -/
theorem objective_mono_of_nonneg {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e)
    {H K : Set (Sym2 V)} (hHK : H ⊆ K) :
    objective G w H ≤ objective G w K := by
  classical
  -- Compare the two filtered sums on `G.edgeSet` termwise.
  rw [objective_def, objective_def]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact hHK he
  · intro e _ heNotMem
    exact hw e

/-- Helper for Definition 2.24: if the omitted edges are contained in a cut edge set, then the
complementary cut hitting set has objective at most the objective of the original hitting set. -/
theorem objective_edgeSetDiff_le_of_diff_subset {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e)
    {H K : Set (Sym2 V)} (hDiffSubset : G.edgeSet \ H ⊆ K) :
    objective G w (G.edgeSet \ K) ≤ objective G w H := by
  -- Reverse the complement inclusion and reduce to monotonicity.
  have hSubset : G.edgeSet \ K ⊆ H := by
    intro e he
    by_contra heH
    exact he.2 (hDiffSubset ⟨he.1, heH⟩)
  simpa using objective_mono_of_nonneg G w hw hSubset

/-- Helper for Definition 2.24: the sum of the weights of the edges in the cut subgraph
`G.between (S : Set V) ((S : Set V)ᶜ)` agrees with `G.cutWeight w S`. -/
theorem cutEdgeSum_eq_cutWeight {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (S : Finset V) :
    (Finset.univ.filter
        fun e : G.edgeSet ↦
          (e : Sym2 V) ∈ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet).sum w =
      G.cutWeight w S := by
  classical
  -- Rewrite the cut-weight owner as a sum over ordered crossing pairs.
  rw [SimpleGraph.cutWeight_eq_sum_interedges, SimpleGraph.crossingPairs_eq_interedges]
  symm
  refine Finset.sum_bij
    (fun uv huv ↦
      ⟨s(uv.1, uv.2), by
        have huv' : uv.1 ∈ S ∧ uv.2 ∈ SimpleGraph.cutComplement S ∧ G.Adj uv.1 uv.2 := by
          simpa [SimpleGraph.mem_interedges_iff] using huv
        rw [SimpleGraph.mem_edgeSet]
        exact huv'.2.2⟩)
    ?_ ?_ ?_ ?_
  · intro uv huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply (G.between (S : Set V) ((S : Set V)ᶜ)).mem_edgeSet.mpr
    rw [SimpleGraph.between_adj]
    rcases (by
      simpa [SimpleGraph.mem_interedges_iff] using huv :
        uv.1 ∈ S ∧ uv.2 ∈ SimpleGraph.cutComplement S ∧ G.Adj uv.1 uv.2) with
      ⟨huS, hvSc, huvAdj⟩
    exact ⟨huvAdj, Or.inl ⟨huS, by simpa [SimpleGraph.cutComplement_eq_sdiff] using hvSc⟩⟩
  · intro uv₁ huv₁ uv₂ huv₂ hEq
    have hEqSym2 : s(uv₁.1, uv₁.2) = s(uv₂.1, uv₂.2) := by
      exact congrArg Subtype.val hEq
    rw [Sym2.eq_iff] at hEqSym2
    rcases (by
      simpa [SimpleGraph.mem_interedges_iff] using huv₁ :
        uv₁.1 ∈ S ∧ uv₁.2 ∈ SimpleGraph.cutComplement S ∧ G.Adj uv₁.1 uv₁.2) with
      ⟨hu₁S, hv₁Sc, _⟩
    rcases (by
      simpa [SimpleGraph.mem_interedges_iff] using huv₂ :
        uv₂.1 ∈ S ∧ uv₂.2 ∈ SimpleGraph.cutComplement S ∧ G.Adj uv₂.1 uv₂.2) with
      ⟨hu₂S, hv₂Sc, _⟩
    rcases hEqSym2 with hdir | hswap
    · exact Prod.ext hdir.1 hdir.2
    · exfalso
      have : uv₁.1 ∉ S := by
        simpa [SimpleGraph.cutComplement_eq_sdiff, hswap.1] using hv₂Sc
      exact this hu₁S
  · intro e he
    rcases e with ⟨e, heG⟩
    induction e using Sym2.ind with
    | h u v =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases (G.between (S : Set V) ((S : Set V)ᶜ)).mem_edgeSet.mp he with
          ⟨huvAdj, hCross | hCross⟩
        · refine ⟨(u, v), ?_, ?_⟩
          · rw [SimpleGraph.mk_mem_interedges_iff]
            refine ⟨hCross.1, ?_, huvAdj⟩
            simpa [SimpleGraph.cutComplement_eq_sdiff] using hCross.2
          · apply Subtype.ext
            rfl
        · refine ⟨(v, u), ?_, ?_⟩
          · rw [SimpleGraph.mk_mem_interedges_iff]
            refine ⟨hCross.2, ?_, huvAdj.symm⟩
            simpa [SimpleGraph.cutComplement_eq_sdiff] using hCross.1
          · apply Subtype.ext
            rw [Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
  · intro uv huv
    have huvAdj :
        G.Adj uv.1 uv.2 := by
      exact
        (by
          simpa [SimpleGraph.mem_interedges_iff] using huv :
            uv.1 ∈ S ∧ uv.2 ∈ SimpleGraph.cutComplement S ∧ G.Adj uv.1 uv.2).2.2
    simp [huvAdj]

/-- For a cut side `S`, the objective of the complementary odd-cycle hitting set equals the total
edge weight minus the weight of the cut determined by `S`. -/
theorem objective_edgeSet_diff_cut_eq_totalWeight_sub_cutWeight {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (S : Finset V) :
    objective G w (G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet) =
      (∑ e : G.edgeSet, w e) - G.cutWeight w S := by
  classical
  -- Split the total edge-weight sum into cut edges and non-cut edges.
  let p : G.edgeSet → Prop := fun e ↦
    (e : Sym2 V) ∈ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet
  have hSplit :
      (Finset.univ.filter p).sum w + (Finset.univ.filter fun e : G.edgeSet ↦ ¬ p e).sum w =
        ∑ e : G.edgeSet, w e := by
    simpa [p] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ p w)
  calc
    objective G w (G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet)
        = (Finset.univ.filter fun e : G.edgeSet ↦ ¬ p e).sum w := by
            -- On `G.edgeSet`, the complement objective is exactly the non-cut filtered sum.
            rw [objective_def]
            congr 1
            ext e
            simp [p, Set.mem_diff]
    _ = (∑ e : G.edgeSet, w e) - (Finset.univ.filter p).sum w := by
          rw [eq_sub_iff_add_eq, add_comm]
          exact hSplit
    _ = (∑ e : G.edgeSet, w e) - G.cutWeight w S := by
          simpa [p] using
            congrArg (fun x : ℝ ↦ (∑ e : G.edgeSet, w e) - x)
              (cutEdgeSum_eq_cutWeight G w S)

/-- Helper for Definition 2.24: if the omitted edges of a feasible hitting set lie inside the cut
defined by `S`, then the cut complement gives a lower objective bound. -/
theorem objective_ge_totalWeight_sub_cutWeight_of_feasible {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e)
    {H : Set (Sym2 V)} (S : Finset V)
    (hDiffSubset : G.edgeSet \ H ⊆ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet) :
    (∑ e : G.edgeSet, w e) - G.cutWeight w S ≤ objective G w H := by
  -- Compare `H` with the complementary hitting set produced by the cut witness `S`.
  calc
    (∑ e : G.edgeSet, w e) - G.cutWeight w S
        = objective G w (G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet) := by
            symm
            exact objective_edgeSet_diff_cut_eq_totalWeight_sub_cutWeight G w S
    _ ≤ objective G w H :=
      objective_edgeSetDiff_le_of_diff_subset G w hw hDiffSubset

/-- Helper for Definition 2.24: every cut determines an attained odd-cycle hitting-set objective
value obtained from the complementary edge family. -/
theorem totalWeight_sub_cutWeight_mem_objectiveValues {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (S : Finset V) :
    ((∑ e : G.edgeSet, w e) - G.cutWeight w S) ∈ objectiveValues G w := by
  have hFeasible :
      feasible G (G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet) := by
    refine
      (feasible_iff_edgeSet_diff_subset_cut
        G (G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet)).2 ?_
    refine ⟨Set.diff_subset, ?_⟩
    refine ⟨(S : Set V), ?_⟩
    intro e he
    by_contra heCut
    exact he.2 ⟨he.1, heCut⟩
  -- Package the complementary cut edge family as an attained objective value.
  refine mem_objectiveValues_iff.2 ?_
  refine ⟨G.edgeSet \ (G.between (S : Set V) ((S : Set V)ᶜ)).edgeSet, hFeasible, ?_⟩
  exact objective_edgeSet_diff_cut_eq_totalWeight_sub_cutWeight G w S

/-- Definition 2.24 (2). When the edge weights are nonnegative, minimizing the odd-cycle
hitting-set objective is equivalent to maximizing the cut weight: a real number `r` is the least
attained odd-cycle hitting-set objective value exactly when `(∑ e : G.edgeSet, w e) - r` is the
greatest attained cut weight. -/
theorem isLeast_objectiveValues_iff_isGreatest_cutWeight {V : Type u}
    (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e) {r : ℝ} :
    IsLeast (objectiveValues G w) r ↔
      IsGreatest {c : ℝ | ∃ S : Finset V, G.cutWeight w S = c} ((∑ e : G.edgeSet, w e) - r) := by
  classical
  constructor
  · intro hr
    rcases hr with ⟨hrMem, hrMin⟩
    rcases mem_objectiveValues_iff.1 hrMem with
      ⟨H, hFeasible, hObj⟩
    rcases (feasible_iff_edgeSet_diff_subset_cut G H).1 hFeasible with
      ⟨_, S, hDiffSubsetSet⟩
    rcases existsFinsetCutWitnessOfDiffSubset G hDiffSubsetSet with
      ⟨Sfin, hDiffSubset⟩
    have hCutObjectiveMem :
        ((∑ e : G.edgeSet, w e) - G.cutWeight w Sfin) ∈ objectiveValues G w :=
      totalWeight_sub_cutWeight_mem_objectiveValues G w Sfin
    have hLower :
        r ≤ (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin :=
      hrMin hCutObjectiveMem
    have hUpper :
        (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin ≤ r := by
      -- The cut witness from feasibility bounds the attained objective value from below.
      calc
        (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin ≤ objective G w H :=
          objective_ge_totalWeight_sub_cutWeight_of_feasible
            G w hw Sfin hDiffSubset
        _ = r := hObj
    have hEq : G.cutWeight w Sfin = (∑ e : G.edgeSet, w e) - r := by
      have hEq' : (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin = r := le_antisymm hUpper hLower
      exact eq_sub_iff_add_eq.mpr <| by
        simpa [add_comm] using (sub_eq_iff_eq_add.mp hEq').symm
    refine ⟨?_, ?_⟩
    · exact ⟨Sfin, hEq⟩
    · intro c hc
      rcases hc with ⟨S, hS⟩
      have hMem :
          ((∑ e : G.edgeSet, w e) - G.cutWeight w S) ∈ objectiveValues G w :=
        totalWeight_sub_cutWeight_mem_objectiveValues G w S
      have hBound : r ≤ (∑ e : G.edgeSet, w e) - G.cutWeight w S := hrMin hMem
      have hCutBound : G.cutWeight w S ≤ (∑ e : G.edgeSet, w e) - r := by
        refine (le_sub_iff_add_le).2 ?_
        simpa [add_comm] using (le_sub_iff_add_le).1 hBound
      simpa [hS] using hCutBound
  · intro hr
    rcases hr with ⟨hrMem, hrMax⟩
    rcases hrMem with ⟨S, hS⟩
    refine ⟨?_, ?_⟩
    · have hMem :
          ((∑ e : G.edgeSet, w e) - G.cutWeight w S) ∈ objectiveValues G w :=
        totalWeight_sub_cutWeight_mem_objectiveValues G w S
      have hEq : (∑ e : G.edgeSet, w e) - G.cutWeight w S = r := by
        exact sub_eq_iff_eq_add.mpr <| by
          simpa [add_comm] using (eq_sub_iff_add_eq.mp hS).symm
      simpa [hEq] using hMem
    · intro r' hr'
      rcases mem_objectiveValues_iff.1 hr' with
        ⟨H, hFeasible, hObj⟩
      rcases (feasible_iff_edgeSet_diff_subset_cut G H).1 hFeasible with
        ⟨_, S, hDiffSubsetSet⟩
      rcases existsFinsetCutWitnessOfDiffSubset G hDiffSubsetSet with
        ⟨Sfin, hDiffSubset⟩
      have hCutMem : G.cutWeight w Sfin ∈ {c : ℝ | ∃ S : Finset V, G.cutWeight w S = c} :=
        ⟨Sfin, rfl⟩
      have hCutBound : G.cutWeight w Sfin ≤ (∑ e : G.edgeSet, w e) - r := hrMax hCutMem
      have hObjBound :
          (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin ≤ r' := by
        -- The same cut witness comparison turns the greatest-cut bound into the least-objective
        -- bound after applying the affine involution `z ↦ totalWeight - z`.
        calc
          (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin ≤ objective G w H :=
            objective_ge_totalWeight_sub_cutWeight_of_feasible
              G w hw Sfin hDiffSubset
          _ = r' := hObj
      have hLower :
          r ≤ (∑ e : G.edgeSet, w e) - G.cutWeight w Sfin := by
        refine (le_sub_iff_add_le).2 ?_
        simpa [add_comm] using (le_sub_iff_add_le).1 hCutBound
      exact le_trans hLower hObjBound

end SimpleGraph.OddCycleHittingSet

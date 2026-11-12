/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_4

/- Exercise 10.5 is a `bridge/view` item. The canonical Chapter 10.6 max-cut owners are already
provided by Exercise 10.4 on weights `Sym2 V → ℝ`, so this file keeps only the source-facing
conversion from edge weights `G.edgeSet → ℝ` to that owner surface. -/

section Exercise105

universe u

variable {V : Type u}

variable (G : SimpleGraph V)

/-- Helper for Exercise 10.5: the indicator of one color class contributes exactly `1` on every
edge of a fixed bipartition. -/
lemma bipartiteIndicatorEdgeTerm_eq_one
    {L R : Set V} (hLR : G.IsBipartiteWith L R) {u v : V} (hadj : G.Adj u v) :
    Set.indicator R (fun _ ↦ (1 : ℝ)) u +
        Set.indicator R (fun _ ↦ (1 : ℝ)) v -
          2 * Set.indicator R (fun _ ↦ (1 : ℝ)) u * Set.indicator R (fun _ ↦ (1 : ℝ)) v =
      1 := by
  classical
  -- Use the bipartition to reduce to the two possible edge orientations across `L` and `R`.
  rcases hLR.mem_of_adj hadj with huv | huv
  · have hu_not_mem : u ∉ R := fun huR ↦ Set.disjoint_left.mp hLR.disjoint huv.1 huR
    simp [Set.indicator, hu_not_mem, huv.2]
  · have hv_not_mem : v ∉ R := fun hvR ↦ Set.disjoint_left.mp hLR.disjoint huv.2 hvR
    simp [Set.indicator, huv.1, hv_not_mem]

variable [DecidableRel G.Adj]

/-- Extend an edge-weight function on `G.edgeSet` to a weight on all unordered vertex pairs by
zero outside `G.edgeSet`. -/
def toSym2Weight (w : G.edgeSet → ℝ) : Sym2 V → ℝ :=
  fun e ↦ if h : e ∈ G.edgeSet then w ⟨e, h⟩ else 0

/-- On an actual edge of `G`, `toSym2Weight` recovers the original edge weight. -/
@[simp]
theorem toSym2Weight_apply (w : G.edgeSet → ℝ) (e : G.edgeSet) :
    toSym2Weight G w e = w e := by
  simp [toSym2Weight]

/-- Away from `G.edgeSet`, the bridge weight vanishes. -/
@[simp]
theorem toSym2Weight_eq_zero_of_not_mem (w : G.edgeSet → ℝ) {e : Sym2 V}
    (he : e ∉ G.edgeSet) :
    toSym2Weight G w e = 0 := by
  simp [toSym2Weight, he]

/-- Nonnegativity of the source edge weights transfers to the canonical `Sym2`-indexed weight
function. -/
theorem toSym2Weight_nonneg (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e) (e : Sym2 V) :
    0 ≤ toSym2Weight G w e := by
  by_cases he : e ∈ G.edgeSet
  · simpa [toSym2Weight, he] using hw ⟨e, he⟩
  · simp [toSym2Weight, he]

variable [Fintype V]

/-- Helper for Exercise 10.5: a bipartite cut attains the total bridged edge-weight sum in the
integral max-cut formulation. -/
lemma bipartiteIndicatorAttainsEdgeFinsetWeightSum
    (w : G.edgeSet → ℝ) (hG : G.IsBipartite) :
    ∃ χ : V → ℝ,
      max_cut_node_feasible χ ∧
        max_cut_node_objective G (toSym2Weight G w) χ =
          Finset.sum G.edgeFinset (fun e ↦ toSym2Weight G w e) := by
  classical
  rcases hG.exists_isBipartiteWith with ⟨L, R, hLR⟩
  let χ : V → ℝ := Set.indicator R (fun _ ↦ (1 : ℝ))
  refine ⟨χ, ?_, ?_⟩
  · -- The indicator of `R` is a `0/1` assignment.
    intro v
    by_cases hv : v ∈ R
    · right
      simp [χ, hv]
    · left
      simp [χ, hv]
  · -- Expand the objective edgewise and use that each bipartite edge term equals `1`.
    have hedgeFinset :
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj
         G.edgeFinset) =
          G.edgeFinset := by
      ext e
      simp [SimpleGraph.mem_edgeFinset]
    rw [max_cut_node_objective_eq_sum, hedgeFinset]
    refine Finset.sum_congr rfl ?_
    intro e he
    obtain ⟨p, rfl⟩ := Sym2.mk_surjective e
    rcases p with ⟨u, v⟩
    have hadj : G.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    simp [χ, Sym2.lift_mk, bipartiteIndicatorEdgeTerm_eq_one (G := G) hLR hadj]

/-- Helper for Exercise 10.5: the Goemans-Williamson value is bounded above by the total bridged
edge-weight sum when all edge weights are nonnegative. -/
lemma goemansWilliamsonValue_leEdgeFinsetWeightSum
    (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e) :
    goemans_williamson_value G (toSym2Weight G w) ≤
      Finset.sum G.edgeFinset (fun e ↦ toSym2Weight G w e) := by
  rw [goemans_williamson_value_eq_sSup]
  let a : V → ℝ := fun _ ↦ 1
  let X : Matrix V V ℝ := Matrix.vecMulVec a a
  have hnonempty : (goemans_williamson_objective_values G (toSym2Weight G w)).Nonempty := by
    -- The all-ones rank-one matrix is a feasible Goemans-Williamson witness.
    refine ⟨goemans_williamson_objective G (toSym2Weight G w) X, X, ?_, rfl⟩
    refine goemans_williamson_feasible.mk ?_ ?_
    · simpa [X, a] using Matrix.posSemidef_vecMulVec_self_star a
    · intro v
      simp [X, a, Matrix.vecMulVec_apply]
  refine csSup_le hnonempty ?_
  intro r hr
  rcases hr with ⟨X, hX, rfl⟩
  -- Compare each semidefinite edge term with `1`, then sum against the nonnegative weights.
  have hedgeFinset :
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       G.edgeFinset) =
        G.edgeFinset := by
    ext e
    simp [SimpleGraph.mem_edgeFinset]
  rw [goemans_williamson_objective_eq_sum, hedgeFinset]
  refine Finset.sum_le_sum (fun e he ↦ ?_)
  obtain ⟨p, rfl⟩ := Sym2.mk_surjective e
  rcases p with ⟨u, v⟩
  have hWeight : 0 ≤ toSym2Weight G w s(u, v) :=
    toSym2Weight_nonneg (G := G) w hw s(u, v)
  have hEdge := goemansWilliamsonEdgeTerm_mem_Icc_zero_one (hX := hX) u v
  have hTerm :
      toSym2Weight G w s(u, v) * (((2 : ℝ) - X u v - X v u) / 4) ≤
        toSym2Weight G w s(u, v) := by
    nlinarith [hWeight, hEdge.2]
  simpa [Sym2.lift_mk] using hTerm

/-- Exercise 10.5. Let `G = (V, E)` be a graph with nonnegative edge weights `w_e` for `e ∈ E`.
If `G` is bipartite, then the max-cut integer optimum `z_I` equals the standard max-cut
semidefinite optimum `z_sdp`, expressed here by the Chapter 10.6 canonical owners on the bridged
weight `toSym2Weight G w`. -/
theorem bipartite_max_cut_integer_value_eq_goemans_williamson_value
    (w : G.edgeSet → ℝ)
    (hw : ∀ e : G.edgeSet, 0 ≤ w e)
    (hG : G.IsBipartite) :
    max_cut_integer_value G (toSym2Weight G w) =
      goemans_williamson_value G (toSym2Weight G w) := by
  classical
  let W : ℝ := Finset.sum G.edgeFinset (fun e ↦ toSym2Weight G w e)
  have hNodeBdd :
      BddAbove (max_cut_node_objective_values G (toSym2Weight G w)) := by
    -- Reuse Exercise 10.4: the integral attainable values sit inside the bounded SDP value set.
    have hSdpBdd : BddAbove (max_cut_sdp'_objective_values G (toSym2Weight G w)) := by
      simpa [maxCutSdp'ObjectiveValues_eq_goemansWilliamsonObjectiveValues (G := G)
        (toSym2Weight G w)] using
        goemansWilliamsonObjectiveValues_bddAbove (G := G) (toSym2Weight G w)
    exact hSdpBdd.mono
      (maxCutNodeObjectiveValues_subset_maxCutSdp'ObjectiveValues (G := G) (toSym2Weight G w))
  have hWleInteger : W ≤ max_cut_integer_value G (toSym2Weight G w) := by
    -- The bipartite indicator cut attains `W`, so the integral optimum is at least `W`.
    rw [max_cut_integer_value_eq_sSup]
    rcases bipartiteIndicatorAttainsEdgeFinsetWeightSum (G := G) w hG with ⟨χ, hχ, hχW⟩
    exact le_csSup hNodeBdd ⟨χ, hχ, by simpa [W] using hχW⟩
  have hGwLeW : goemans_williamson_value G (toSym2Weight G w) ≤ W := by
    -- The semidefinite optimum is bounded termwise by the same total edge-weight sum.
    simpa [W] using goemansWilliamsonValue_leEdgeFinsetWeightSum (G := G) w hw
  have hIntegerLeGw :
      max_cut_integer_value G (toSym2Weight G w) ≤
        goemans_williamson_value G (toSym2Weight G w) := by
    -- Exercise 10.4 already identifies the standard SDP value with the lifted relaxation value.
    calc
      max_cut_integer_value G (toSym2Weight G w) ≤
          max_cut_sdp'_value G (toSym2Weight G w) :=
        max_cut_integer_value_le_max_cut_sdp'_value (G := G) (toSym2Weight G w)
      _ = goemans_williamson_value G (toSym2Weight G w) :=
        max_cut_sdp'_value_eq_goemans_williamson_value (G := G) (toSym2Weight G w)
  exact le_antisymm hIntegerLeGw (le_trans hGwLeW hWleInteger)

end Exercise105

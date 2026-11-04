/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_21.MinimumSTCut
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut.Bridge

public section

namespace SimpleGraph.MinimumSTCut

universe u

variable {V : Type u}

section

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut/Bridge.lean:
the cut indicator evaluates by membership in the cut-edge finset. -/
lemma cutIndicator_apply (S : Finset V) (e : G.edgeSet) :
    SimpleGraph.MinimumCut.cutIndicator G S e =
      if e ∈ SimpleGraph.MinimumCut.cutEdges G S then 1 else 0 := by
  classical
  -- Test the imported objective identity against the unit weight concentrated at `e`.
  have h := SimpleGraph.MinimumCut.objective_cutIndicator_eq_cutWeight
    (G := G) (fun e2 ↦ if e2 = e then 1 else 0) S
  rw [SimpleGraph.MinimumCut.objective_def,
    SimpleGraph.MinimumCut.cutWeight_eq_sum_cutEdges] at h
  simpa using h

/-- The cut indicator of an `s,t`-cut side meets every `s,t`-path in at least one edge, so its
`pathEdgeSum` is at least `1` on every `s,t`-path. -/
theorem pathEdgeSum_cutIndicator_ge_one_of_isSTCutSide
    {s t : V} {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) {p : G.Path s t} :
    1 ≤ pathEdgeSum G (SimpleGraph.MinimumCut.cutIndicator G S) p := by
  classical
  -- A path from inside the cut to outside it contains a boundary dart.
  rcases (SimpleGraph.isSTCutSide_iff (S := S)).1 hS with ⟨hsS, htS⟩
  obtain ⟨d, hdMem, hdIn, hdOut⟩ :=
    (p : G.Walk s t).exists_boundary_dart (S : Set V) hsS htS
  rcases d with ⟨⟨a, b⟩, hab⟩
  have heG : s(a, b) ∈ G.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hab
  let e : G.edgeSet := ⟨s(a, b), heG⟩
  have heSymm : e.1 = s(a, b) := rfl
  have heCut : e ∈ SimpleGraph.MinimumCut.cutEdges G S := by
    rw [SimpleGraph.MinimumCut.mem_cutEdges_iff]
    exact ⟨a, hdIn, b, hdOut, heSymm⟩
  have hePath : e.1 ∈ (p : G.Walk s t).edgeSet := by
    change s(a, b) ∈ (p : G.Walk s t).edges
    rw [SimpleGraph.Walk.edges]
    have hdEdge : (⟨⟨a, b⟩, hab⟩ : G.Dart).edge = s(a, b) := rfl
    exact List.mem_map.mpr ⟨⟨⟨a, b⟩, hab⟩, hdMem, hdEdge⟩
  have hnonneg :
      ∀ e2 : G.edgeSet,
        0 ≤ if e2.1 ∈ (p : G.Walk s t).edgeSet then
          SimpleGraph.MinimumCut.cutIndicator G S e2 else 0 := by
    intro e2
    by_cases he2 : e2.1 ∈ (p : G.Walk s t).edgeSet
    · by_cases heCut2 : e2 ∈ SimpleGraph.MinimumCut.cutEdges G S
      · simp [cutIndicator_apply, he2, heCut2]
      · simp [cutIndicator_apply, he2, heCut2]
    · simp [he2]
  -- The selected boundary edge contributes one, and all remaining summands are nonnegative.
  calc
    1 = if e.1 ∈ (p : G.Walk s t).edgeSet then
        SimpleGraph.MinimumCut.cutIndicator G S e else 0 := by
      simp [cutIndicator_apply, heCut, hePath]
    _ ≤ pathEdgeSum G (SimpleGraph.MinimumCut.cutIndicator G S) p := by
      rw [pathEdgeSum_def]
      have heUniv : e ∈ (Finset.univ : Finset G.edgeSet) := Finset.mem_univ e
      exact Finset.single_le_sum (fun e2 _ ↦ hnonneg e2) heUniv

/-- Every `s,t`-cut side yields a feasible binary edge assignment through its cut indicator. -/
theorem cutIndicator_feasible_of_isSTCutSide
    {s t : V} {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) :
    feasible G s t (SimpleGraph.MinimumCut.cutIndicator G S) := by
  -- The boundary-edge estimate supplies every path constraint.
  refine (feasible_iff (G := G)).2 ⟨?_, ?_⟩
  · intro p
    exact pathEdgeSum_cutIndicator_ge_one_of_isSTCutSide (G := G) hS
  · intro e
    -- The cut indicator is binary by its defining membership split.
    classical
    by_cases he : e ∈ SimpleGraph.MinimumCut.cutEdges G S
    · simp [cutIndicator_apply, he]
    · simp [cutIndicator_apply, he]

omit [DecidableEq V] in
/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut/Bridge.lean:
path-cover feasibility implies spanning-tree-cover feasibility. -/
lemma minimumCutFeasible_of_feasible
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) :
    SimpleGraph.MinimumCut.feasible G x := by
  refine (SimpleGraph.MinimumCut.feasible_iff (G := G)).2 ⟨?_, ?_⟩
  · intro T hT
    -- A spanning tree contains an `s,t`-path, which is lifted to `G`.
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath s t
    have hle : T.spanningCoe ≤ G := SimpleGraph.Subgraph.spanningCoe_le T
    have hMappedPath : (p.mapLe hle).IsPath := hp.mapLe hle
    let q : G.Path s t := ⟨p.mapLe hle, hMappedPath⟩
    have hxNonneg : ∀ e : G.edgeSet, 0 ≤ x e := by
      intro e
      rcases feasible_binary (G := G) hx e with hzero | hone
      · simp [hzero]
      · simp [hone]
    have hpathEdgeInTree :
        ∀ e : G.edgeSet, e.1 ∈ (q : G.Walk s t).edgeSet → e.1 ∈ T.edgeSet := by
      intro e hePath
      have hePathT : e.1 ∈ p.edgeSet := by
        simpa [q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hePath
      have heSpanning : e.1 ∈ T.spanningCoe.edgeSet :=
        p.edges_subset_edgeSet hePathT
      simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSpanning
    -- Nonnegativity lets the tree sum dominate the sum over its selected path.
    calc
      1 ≤ pathEdgeSum G x q := feasible_path_ge_one (G := G) hx q
      _ ≤ SimpleGraph.MinimumCut.treeEdgeSum G x T := by
        rw [pathEdgeSum_def, SimpleGraph.MinimumCut.treeEdgeSum_def]
        apply Finset.sum_le_sum
        intro e _
        by_cases hePath : e.1 ∈ (q : G.Walk s t).edgeSet
        · have heTree := hpathEdgeInTree e hePath
          simp [hePath, heTree]
        · by_cases heTree : e.1 ∈ T.edgeSet
          · simp [hePath, heTree, hxNonneg e]
          · simp [hePath, heTree]
  · intro e
    exact feasible_binary (G := G) hx e

omit [DecidableEq V] in
/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut/Bridge.lean:
a feasible path-cover edge lies in the zero-edge subgraph exactly when its coordinate is zero. -/
lemma mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) {e : G.edgeSet} :
    e.1 ∈ (SimpleGraph.MinimumCut.zeroEdgeSubgraph G x).edgeSet ↔ x e = 0 := by
  -- Reuse the owner module zero-edge interface after transporting feasibility.
  exact SimpleGraph.MinimumCut.mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible
    (G := G) (minimumCutFeasible_of_feasible (G := G) hx)

omit [DecidableEq V] in
/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut/Bridge.lean:
the zero-valued edges of a feasible path cover do not connect its terminals. -/
lemma zeroEdgeSubgraph_not_reachable_of_feasible
    {s t : V} {x : G.edgeSet → ℝ} (hx : feasible G s t x) :
    ¬ (SimpleGraph.MinimumCut.zeroEdgeSubgraph G x).spanningCoe.Reachable s t := by
  intro hreach
  let H0 := SimpleGraph.MinimumCut.zeroEdgeSubgraph G x
  -- Replace a hypothetical zero-edge walk by a path, then lift it to the ambient graph.
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hle : H0.spanningCoe ≤ G := SimpleGraph.Subgraph.spanningCoe_le H0
  have hMappedPath : (p.mapLe hle).IsPath := hp.mapLe hle
  let q : G.Path s t := ⟨p.mapLe hle, hMappedPath⟩
  have hsumZero : pathEdgeSum G x q = 0 := by
    rw [pathEdgeSum_def]
    apply Finset.sum_eq_zero
    intro e _
    by_cases hePath : e.1 ∈ (q : G.Walk s t).edgeSet
    · have hePathH0 : e.1 ∈ p.edgeSet := by
        simpa [q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hePath
      have heSpanning : e.1 ∈ H0.spanningCoe.edgeSet :=
        p.edges_subset_edgeSet hePathH0
      have heZero : e.1 ∈ H0.edgeSet := by
        simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heSpanning
      have hx0 : x e = 0 :=
        (mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible (G := G) hx).1 heZero
      simp [hePath, hx0]
    · simp [hePath]
  -- Feasibility requires the lifted path sum to be at least one, contradicting its zero sum.
  have hge : 1 ≤ pathEdgeSum G x q := feasible_path_ge_one (G := G) hx q
  have honeLeZero : (1 : ℝ) ≤ 0 := by
    simpa [hsumZero] using hge
  exact (not_le_of_gt zero_lt_one) honeLeZero

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_4_definition_2_21/MinimumSTCut/Bridge.lean: <!-- http -->
Every feasible binary edge assignment dominates the weight of some `s,t`-cut side. -/
theorem existsSTCutSide_le_objective_of_feasible
    {s t : V} (hG : G.Connected) (hst : s ≠ t) (w : G.edgeSet → ℝ)
    (hw : ∀ e : G.edgeSet, 0 ≤ w e) {x : G.edgeSet → ℝ} (hx : feasible G s t x) :
    ∃ S : Finset V, SimpleGraph.IsSTCutSide s t S ∧ G.cutWeight w S ≤ objective G w x := by
  classical
  let H0 := SimpleGraph.MinimumCut.zeroEdgeSubgraph G x
  let C := H0.spanningCoe.connectedComponentMk s
  let S : Finset V := C.supp.toFinset
  -- The component of `s` contains `s` and excludes `t` by zero-edge non-reachability.
  have hsS : s ∈ S := by
    simp [S, C]
  have htNotS : t ∉ S := by
    intro htS
    by_cases hsEqT : s = t
    · exact (hst hsEqT).elim
    · by_cases hstReach : G.Reachable s t
      · apply zeroEdgeSubgraph_not_reachable_of_feasible (G := G) hx
        have htComp : t ∈ C.supp := by
          simpa [S] using htS
        have htsReach : H0.spanningCoe.Reachable t s := by
          simpa [C, H0] using
            (SimpleGraph.ConnectedComponent.mem_supp_iff
              (C := H0.spanningCoe.connectedComponentMk s) (v := t)).1 htComp
        exact SimpleGraph.Reachable.symm htsReach
      · exact (hstReach (hG s t)).elim
  have hS : SimpleGraph.IsSTCutSide s t S := by
    exact (SimpleGraph.isSTCutSide_iff (S := S)).2 ⟨hsS, htNotS⟩
  -- Any edge leaving the zero-edge component must have coordinate one.
  have hcutOne :
      ∀ e ∈ SimpleGraph.MinimumCut.cutEdges G S, x e = 1 := by
    intro e heCut
    rw [SimpleGraph.MinimumCut.mem_cutEdges_iff] at heCut
    rcases heCut with ⟨u, huS, v, hvS, hEq⟩
    have huComp : u ∈ C.supp := by
      simpa [S, C] using huS
    by_cases hx0 : x e = 0
    · have heZero : e.1 ∈ H0.edgeSet :=
        (mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible (G := G) hx).2 hx0
      have hadjH0 : H0.spanningCoe.Adj u v := by
        have heZero2 : e.1 ∈ H0.spanningCoe.edgeSet := by
          simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heZero
        have huvEdge : s(u, v) ∈ H0.spanningCoe.edgeSet := by
          simpa [hEq] using heZero2
        rwa [SimpleGraph.mem_edgeSet] at huvEdge
      have hvComp : v ∈ C.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hadjH0).mp huComp
      have hvS2 : v ∈ S := by
        simpa [S, C] using hvComp
      exact False.elim (hvS hvS2)
    · rcases feasible_binary (G := G) hx e with hzero | hone
      · exact False.elim (hx0 hzero)
      · exact hone
  have hpointwise :
      ∀ e : G.edgeSet, SimpleGraph.MinimumCut.cutIndicator G S e ≤ x e := by
    intro e
    by_cases heCut : e ∈ SimpleGraph.MinimumCut.cutEdges G S
    · have hx1 := hcutOne e heCut
      simp [cutIndicator_apply, heCut, hx1]
    · rcases feasible_binary (G := G) hx e with hzero | hone
      · simp [cutIndicator_apply, heCut, hzero]
      · simp [cutIndicator_apply, heCut, hone]
  refine ⟨S, hS, ?_⟩
  -- Pointwise domination becomes the required weighted objective comparison.
  calc
    G.cutWeight w S = SimpleGraph.MinimumCut.objective G w
        (SimpleGraph.MinimumCut.cutIndicator G S) := by
      symm
      exact SimpleGraph.MinimumCut.objective_cutIndicator_eq_cutWeight (G := G) w S
    _ = ∑ e : G.edgeSet, w e * SimpleGraph.MinimumCut.cutIndicator G S e := by
      rw [SimpleGraph.MinimumCut.objective_def]
    _ ≤ ∑ e : G.edgeSet, w e * x e := by
      exact Finset.sum_le_sum fun e _ ↦
        mul_le_mul_of_nonneg_left (hpointwise e) (hw e)
    _ = objective G w x := by
      rw [objective_def]

end

end SimpleGraph.MinimumSTCut

end

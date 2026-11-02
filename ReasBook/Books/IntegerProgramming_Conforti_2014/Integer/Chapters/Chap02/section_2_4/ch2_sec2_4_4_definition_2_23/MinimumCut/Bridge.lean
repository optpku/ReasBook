module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open scoped BigOperators

public section

namespace SimpleGraph
namespace MinimumCut

universe u

section Bridge

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G` crossing the cut side `S`, viewed as a finset of ambient graph edges. -/
noncomputable def cutEdges (S : Finset V) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ ∃ u ∈ S, ∃ v ∉ S, e.1 = s(u, v)

/-- The `0`-`1` edge indicator of the cut determined by `S`. -/
noncomputable def cutIndicator (S : Finset V) : G.edgeSet → ℝ :=
  fun e ↦ if e ∈ cutEdges G S then 1 else 0

/-- Membership in `cutEdges G S` means that the edge has one endpoint in `S` and the other
endpoint outside `S`. -/
theorem mem_cutEdges_iff
    {S : Finset V} {e : G.edgeSet} :
    e ∈ cutEdges G S ↔ ∃ u ∈ S, ∃ v ∉ S, e.1 = s(u, v) := by
  simp [cutEdges]

/-- The cut weight is the sum of the edge weights over the cut edges in `cutEdges G S`. -/
theorem cutWeight_eq_sum_cutEdges
    (w : G.edgeSet → ℝ) (S : Finset V) :
    G.cutWeight w S = Finset.sum (cutEdges G S) w := by
  classical
  rw [SimpleGraph.cutWeight_eq_sum_interedges, SimpleGraph.crossingPairs_eq_interedges]
  refine Finset.sum_bij
    (fun uv huv ↦ ⟨s(uv.1, uv.2), by
      rw [SimpleGraph.mem_edgeSet]
      exact
        (SimpleGraph.mk_mem_interedges_iff
          (G := G)
          (s := S)
          (t := SimpleGraph.cutComplement S)
          (a := uv.1)
          (b := uv.2)).1 huv |>.2.2⟩)
    ?_ ?_ ?_ ?_
  · intro uv huv
    rw [mem_cutEdges_iff]
    rcases
      (SimpleGraph.mk_mem_interedges_iff
        (G := G) (s := S) (t := SimpleGraph.cutComplement S) (a := uv.1) (b := uv.2)).1 huv with
      ⟨huS, hvSc, _⟩
    refine ⟨uv.1, huS, uv.2, ?_, rfl⟩
    simpa [SimpleGraph.cutComplement_eq_sdiff] using hvSc
  · intro uv₁ huv₁ uv₂ huv₂ hEq
    have hEq' : s(uv₁.1, uv₁.2) = s(uv₂.1, uv₂.2) := congrArg Subtype.val hEq
    rw [Sym2.eq_iff] at hEq'
    rcases
      (SimpleGraph.mk_mem_interedges_iff
        (G := G) (s := S) (t := SimpleGraph.cutComplement S) (a := uv₁.1) (b := uv₁.2)).1 huv₁ with
      ⟨hu₁S, hv₁Sc, _⟩
    rcases
      (SimpleGraph.mk_mem_interedges_iff
        (G := G) (s := S) (t := SimpleGraph.cutComplement S) (a := uv₂.1) (b := uv₂.2)).1 huv₂ with
      ⟨hu₂S, hv₂Sc, _⟩
    rcases hEq' with hdir | hswap
    · exact Prod.ext hdir.1 hdir.2
    · exfalso
      have hv₂NotS : uv₂.2 ∉ S := by
        simpa [SimpleGraph.cutComplement_eq_sdiff] using hv₂Sc
      have : uv₁.1 ∉ S := by simpa [hswap.1] using hv₂NotS
      exact this hu₁S
  · intro e he
    rw [mem_cutEdges_iff] at he
    rcases he with ⟨u, huS, v, hvS, hEq⟩
    refine ⟨(u, v), ?_, ?_⟩
    · rw [SimpleGraph.mk_mem_interedges_iff]
      refine ⟨huS, ?_, ?_⟩
      · simpa [SimpleGraph.cutComplement_eq_sdiff] using hvS
      · rw [← SimpleGraph.mem_edgeSet, ← hEq]
        exact e.property
    · apply Subtype.ext
      exact hEq.symm
  · intro uv huv
    have huvAdj :
        G.Adj uv.1 uv.2 := by
      exact
        (SimpleGraph.mk_mem_interedges_iff
          (G := G) (s := S) (t := SimpleGraph.cutComplement S) (a := uv.1) (b := uv.2)).1 huv |>.2.2
    simp [huvAdj]

/-- The objective of the cut indicator is the weight of the corresponding cut. -/
theorem objective_cutIndicator_eq_cutWeight
    (w : G.edgeSet → ℝ) (S : Finset V) :
    objective G w (cutIndicator G S) = G.cutWeight w S := by
  rw [objective_def, cutWeight_eq_sum_cutEdges]
  symm
  simpa [cutIndicator, cutEdges, mul_ite, mul_one, mul_zero] using
    (Finset.sum_filter (s := Finset.univ)
      (p := fun e : G.edgeSet ↦ ∃ u ∈ S, ∃ v ∉ S, e.1 = s(u, v))
      (f := fun e : G.edgeSet ↦ w e))

/-- Every spanning tree contains a cut edge of every proper cut side, so the cut indicator
satisfies the spanning-tree covering inequality. -/
theorem treeEdgeSum_cutIndicator_ge_one_of_isProperCutSide
    {S : Finset V} (hS : SimpleGraph.IsProperCutSide S)
    {T : G.Subgraph} (hT : T.spanningCoe.IsTree) :
    1 ≤ treeEdgeSum G (cutIndicator G S) T := by
  classical
  rcases (SimpleGraph.isProperCutSide_iff (S := S)).1 hS with ⟨hSnonempty, hSproper⟩
  rcases hSnonempty with ⟨u, huS⟩
  have hnotAll : ¬ ∀ v : V, v ∈ S := by
    intro hAll
    apply hSproper
    ext v
    simp [hAll v]
  rcases not_forall.mp hnotAll with ⟨v, hvS⟩
  rcases hT.connected u v with ⟨p⟩
  obtain ⟨d, hdMem, hdIn, hdOut⟩ := p.exists_boundary_dart (S : Set V) huS hvS
  rcases d with ⟨⟨a, b⟩, hab⟩
  let e : G.edgeSet := ⟨s(a, b), by
    rw [SimpleGraph.mem_edgeSet]
    exact T.adj_sub (by simpa using hab)⟩
  have heCut : e ∈ cutEdges G S := by
    rw [mem_cutEdges_iff]
    exact ⟨a, hdIn, b, hdOut, rfl⟩
  have heT : e.1 ∈ T.edgeSet := by
    change s(a, b) ∈ T.edgeSet
    rw [← SimpleGraph.Subgraph.edgeSet_spanningCoe T, SimpleGraph.mem_edgeSet]
    exact hab
  have hnonneg :
      ∀ e' : G.edgeSet, 0 ≤ if e'.1 ∈ T.edgeSet then cutIndicator G S e' else 0 := by
    intro e'
    by_cases he' : e'.1 ∈ T.edgeSet
    · by_cases heCut' : e' ∈ cutEdges G S
      · simp [cutIndicator, he', heCut']
      · simp [cutIndicator, he', heCut']
    · simp [he']
  calc
    1 = if e.1 ∈ T.edgeSet then cutIndicator G S e else 0 := by
      simp [cutIndicator, heCut, heT]
    _ ≤ treeEdgeSum G (cutIndicator G S) T := by
      rw [treeEdgeSum_def]
      exact Finset.single_le_sum (fun e' _ ↦ hnonneg e') (by simp)

/-- A proper cut side yields a feasible `0`-`1` solution of the spanning-tree-cover
formulation. -/
theorem cutIndicator_feasible_of_isProperCutSide
    {S : Finset V} (hS : SimpleGraph.IsProperCutSide S) :
    feasible G (cutIndicator G S) := by
  refine (feasible_iff (G := G)).2 ?_
  refine ⟨?_, ?_⟩
  · intro T hT
    exact treeEdgeSum_cutIndicator_ge_one_of_isProperCutSide (G := G) hS hT
  · intro e
    by_cases he : e ∈ cutEdges G S
    · simp [cutIndicator, he]
    · simp [cutIndicator, he]

/-- The set of edges assigned value `1` by `x`. -/
def positiveEdges (x : G.edgeSet → ℝ) : Set (Sym2 V) :=
  ((↑) '' {e : G.edgeSet | x e = 1})

/-- The spanning subgraph of the edges assigned value `0` by `x`, realized by deleting the
positive edges from the top subgraph. -/
def zeroEdgeSubgraph (x : G.edgeSet → ℝ) : G.Subgraph :=
  (⊤ : G.Subgraph).deleteEdges (positiveEdges G x)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An ambient graph edge belongs to `positiveEdges G x` exactly when its coordinate under `x`
is `1`. -/
theorem mem_positiveEdges_iff
    {x : G.edgeSet → ℝ} {e : G.edgeSet} :
    e.1 ∈ positiveEdges G x ↔ x e = 1 := by
  constructor
  · intro he
    rcases he with ⟨e', he', hEq⟩
    have : e' = e := Subtype.ext hEq
    simpa [this] using he'
  · intro he
    exact ⟨e, he, rfl⟩

omit [DecidableEq V] in
/-- For a feasible `0`-`1` point, the edges of `zeroEdgeSubgraph G x` are exactly the edges with
coordinate `0`. -/
theorem mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible
    {x : G.edgeSet → ℝ} (hx : feasible G x) {e : G.edgeSet} :
    e.1 ∈ (zeroEdgeSubgraph G x).edgeSet ↔ x e = 0 := by
  rcases e with ⟨e, heG⟩
  revert heG
  refine Sym2.inductionOn e ?_
  intro u v heG
  have huv : G.Adj u v := by
    rw [← SimpleGraph.mem_edgeSet]
    exact heG
  let e' : G.edgeSet := ⟨s(u, v), by
    rw [SimpleGraph.mem_edgeSet]
    exact huv⟩
  have heq : e' = ⟨s(u, v), heG⟩ := by
    apply Subtype.ext
    rfl
  constructor
  · intro hmem
    have hnotPos : e'.1 ∉ positiveEdges G x := by
      rw [zeroEdgeSubgraph, Subgraph.mem_edgeSet, Subgraph.deleteEdges_adj,
        Subgraph.top_adj] at hmem
      exact hmem.2
    rcases feasible_binary (G := G) hx e' with hzero | hone
    · simpa [e', heq] using hzero
    · exfalso
      exact hnotPos ((mem_positiveEdges_iff (G := G) (x := x) (e := e')).2 hone)
  · intro hzero
    rw [zeroEdgeSubgraph, Subgraph.mem_edgeSet, Subgraph.deleteEdges_adj, Subgraph.top_adj]
    refine ⟨huv, ?_⟩
    intro hpos
    have hx1 : x e' = 1 := (mem_positiveEdges_iff (G := G) (x := x) (e := e')).1 hpos
    have hx0' : x e' = 0 := by simpa [e', heq] using hzero
    exact zero_ne_one (hx0'.symm.trans hx1)

omit [DecidableEq V] in
/-- A feasible `0`-`1` solution cannot leave a connected subgraph on the zero-valued edges,
because that subgraph would contain a spanning tree with tree sum `0`. -/
theorem zeroEdgeSubgraph_not_connected_of_feasible
    {x : G.edgeSet → ℝ} (hx : feasible G x) :
    ¬ (zeroEdgeSubgraph G x).spanningCoe.Connected := by
  intro hconn
  obtain ⟨T, hTle, hTtree⟩ := hconn.exists_isTree_le
  let T' : G.Subgraph := SimpleGraph.toSubgraph T <|
    le_trans hTle <| by
      simpa [zeroEdgeSubgraph] using
        (SimpleGraph.Subgraph.spanningCoe_deleteEdges_le (⊤ : G.Subgraph) (positiveEdges G x))
  have hTtree' : T'.spanningCoe.IsTree := by
    simpa [T'] using hTtree
  have hTsub : T' ≤ zeroEdgeSubgraph G x := by
    constructor
    · simp [T', zeroEdgeSubgraph]
    · intro u v huv
      exact hTle huv
  have hsumZero : treeEdgeSum G x T' = 0 := by
    rw [treeEdgeSum_def]
    apply Finset.sum_eq_zero
    intro e _
    by_cases heT : e.1 ∈ T'.edgeSet
    · have heZeroSub : e.1 ∈ (zeroEdgeSubgraph G x).edgeSet :=
        SimpleGraph.Subgraph.edgeSet_mono hTsub heT
      have hx0 : x e = 0 :=
        (mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible (G := G) hx).1 heZeroSub
      simp [heT, hx0]
    · simp [heT]
  have hge := feasible_tree_ge_one (G := G) hx hTtree'
  have : (1 : ℝ) ≤ 0 := by simpa [hsumZero] using hge
  exact (not_le_of_gt zero_lt_one) this

/-- Every feasible `0`-`1` point dominates the weight of some proper cut side. -/
theorem existsProperCutSide_le_objective_of_feasible
    (hG : G.Connected) (w : G.edgeSet → ℝ) (hw : ∀ e : G.edgeSet, 0 ≤ w e)
    {x : G.edgeSet → ℝ} (hx : feasible G x) :
    ∃ S : Finset V, SimpleGraph.IsProperCutSide S ∧ G.cutWeight w S ≤ objective G w x := by
  classical
  let H0 := zeroEdgeSubgraph G x
  have hnotConn : ¬ H0.spanningCoe.Connected :=
    zeroEdgeSubgraph_not_connected_of_feasible (G := G) hx
  obtain ⟨u, huReach⟩ := (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).mp hG
  have hnotAll : ¬ ∀ v : V, H0.spanningCoe.Reachable u v := by
    intro huAll
    apply hnotConn
    exact (SimpleGraph.connected_iff_exists_forall_reachable (G := H0.spanningCoe)).2 ⟨u, huAll⟩
  obtain ⟨v, hvNotReach⟩ := not_forall.mp hnotAll
  let C := H0.spanningCoe.connectedComponentMk u
  let S : Finset V := C.supp.toFinset
  have huS : u ∈ S := by
    simp [S, C]
  have hvNotS : v ∉ S := by
    intro hvS
    apply hvNotReach
    have hvSet : v ∈ C.supp := by
      simpa [S] using hvS
    exact SimpleGraph.Reachable.symm <|
      by simpa [C] using
        (SimpleGraph.ConnectedComponent.mem_supp_iff
          (C := H0.spanningCoe.connectedComponentMk u)
          (v := v)).1 hvSet
  have hS : SimpleGraph.IsProperCutSide S := by
    refine (SimpleGraph.isProperCutSide_iff (S := S)).2 ?_
    refine ⟨⟨u, huS⟩, ?_⟩
    intro hEq
    exact hvNotS (by simp [hEq])
  have hcutOne : ∀ e ∈ cutEdges G S, x e = 1 := by
    intro e heCut
    rw [mem_cutEdges_iff] at heCut
    rcases heCut with ⟨u', hu'S, v', hv'S, hEq⟩
    have hu'Comp : u' ∈ C.supp := by
      simpa [S, C] using hu'S
    by_cases hx0 : x e = 0
    · have heZero : e.1 ∈ H0.edgeSet :=
        (mem_zeroEdgeSubgraph_edgeSet_iff_of_feasible (G := G) hx).2 hx0
      have hadjH0 : H0.spanningCoe.Adj u' v' := by
        have heZero' : e.1 ∈ H0.spanningCoe.edgeSet := by
          simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe] using heZero
        have : s(u', v') ∈ H0.spanningCoe.edgeSet := by
          simpa [hEq] using heZero'
        rwa [SimpleGraph.mem_edgeSet] at this
      have hv'Comp : v' ∈ C.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_congr_adj C hadjH0).mp hu'Comp
      have : v' ∈ S := by simpa [S, C] using hv'Comp
      exact False.elim (hv'S this)
    · rcases feasible_binary (G := G) hx e with hzero | hone
      · exact False.elim (hx0 hzero)
      · exact hone
  have hpointwise : ∀ e : G.edgeSet, cutIndicator G S e ≤ x e := by
    intro e
    by_cases heCut : e ∈ cutEdges G S
    · have hx1 := hcutOne e heCut
      simp [cutIndicator, heCut, hx1]
    · rcases feasible_binary (G := G) hx e with hzero | hone
      · simp [cutIndicator, heCut, hzero]
      · simp [cutIndicator, heCut, hone]
  refine ⟨S, hS, ?_⟩
  calc
    G.cutWeight w S = objective G w (cutIndicator G S) := by
      symm
      exact objective_cutIndicator_eq_cutWeight (G := G) w S
    _ ≤ objective G w x := by
      rw [objective_def, objective_def]
      exact Finset.sum_le_sum fun e _ ↦
        mul_le_mul_of_nonneg_left (hpointwise e) (hw e)

end Bridge

end MinimumCut
end SimpleGraph

end

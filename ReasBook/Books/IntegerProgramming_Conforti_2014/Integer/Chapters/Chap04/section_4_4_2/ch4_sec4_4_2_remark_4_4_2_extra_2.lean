import Mathlib

open scoped BigOperators

-- Semantic search tool `lean_leansearch` was unavailable in this environment. The repository also
-- has no project-local max-flow API, so this file uses an explicit layered-network encoding of the
-- bipartite matching reduction together with mathlib's canonical `SimpleGraph.Subgraph.IsMatching`.

section Remark442Extra2

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
variable (adj : U → W → Prop) [DecidableRel adj]

/-- An edge of the original bipartite graph, recorded as a left-right pair together with the
adjacency proof. -/
abbrev bipartite_relation_edge :=
  { uw : U × W // adj uw.1 uw.2 }

/-- The arcs in the standard flow network attached to a bipartite graph: arcs from the source to
the left side, the original left-to-right edges, and arcs from the right side to the sink. -/
inductive BipartiteMatchingFlowArc where
  | source_left : U → BipartiteMatchingFlowArc
  | edge : bipartite_relation_edge adj → BipartiteMatchingFlowArc
  | right_sink : W → BipartiteMatchingFlowArc

/-- The capacity function on the flow network for bipartite matching: arcs incident to the source
or sink have capacity `1`, and the original graph edges have infinite capacity. -/
def bipartite_matching_flow_capacity :
    BipartiteMatchingFlowArc adj → WithTop ℕ
  | .source_left _ => 1
  | .edge _ => ⊤
  | .right_sink _ => 1

/-- The original graph edges incident to a fixed left vertex. -/
def left_incident_edges (u : U) : Finset (bipartite_relation_edge adj) :=
  Finset.univ.filter fun e ↦ e.1.1 = u

/-- The original graph edges incident to a fixed right vertex. -/
def right_incident_edges (w : W) : Finset (bipartite_relation_edge adj) :=
  Finset.univ.filter fun e ↦ e.1.2 = w

/-- An integral `s,t`-flow on the layered network associated with a bipartite graph, written
directly as a natural-valued arc function satisfying the capacity constraints and the flow-balance
equalities at the left and right vertices. -/
def IsBipartiteMatchingFlow (x : BipartiteMatchingFlowArc adj → ℕ) : Prop :=
  (∀ a, (x a : WithTop ℕ) ≤ bipartite_matching_flow_capacity adj a) ∧
    (∀ u, x (.source_left u) = Finset.sum (left_incident_edges adj u) fun e ↦ x (.edge e)) ∧
    (∀ w, (Finset.sum (right_incident_edges adj w) fun e ↦ x (.edge e)) = x (.right_sink w))

/-- Unfolding characterization of the integral flow predicate for the bipartite matching network. -/
theorem is_bipartite_matching_flow_iff (x : BipartiteMatchingFlowArc adj → ℕ) :
    IsBipartiteMatchingFlow adj x ↔
      (∀ a, (x a : WithTop ℕ) ≤ bipartite_matching_flow_capacity adj a) ∧
        (∀ u, x (.source_left u) = Finset.sum (left_incident_edges adj u) fun e ↦ x (.edge e)) ∧
        (∀ w,
          (Finset.sum (right_incident_edges adj w) fun e ↦
            x (.edge e)) = x (.right_sink w)) := by
  -- This theorem just unfolds the definition of feasible integral flow.
  rfl

/-- The value of a flow in the layered bipartite-matching network, computed as the total flow sent
out of the source. -/
def bipartite_matching_flow_value (x : BipartiteMatchingFlowArc adj → ℕ) : ℕ :=
  ∑ u, x (.source_left u)

/-- The set of original bipartite edges carrying one unit of flow. -/
def bipartite_matching_selected_edges
    (x : BipartiteMatchingFlowArc adj → ℕ) : Finset (bipartite_relation_edge adj) :=
  Finset.univ.filter fun e ↦ x (.edge e) = 1

omit [DecidableEq U] [DecidableEq W] in
/-- Membership in the selected-edge set means that the corresponding original edge carries one unit
of flow. -/
theorem mem_bipartite_matching_selected_edges_iff
    {x : BipartiteMatchingFlowArc adj → ℕ} {e : bipartite_relation_edge adj} :
    e ∈ bipartite_matching_selected_edges adj x ↔ x (.edge e) = 1 := by
  -- Membership is exactly the defining filter predicate.
  simp [bipartite_matching_selected_edges]

/-- The undirected graph on `U ⊕ W` obtained from the bipartite adjacency relation. -/
def bipartite_relation_graph : SimpleGraph (U ⊕ W) :=
  SimpleGraph.fromRel fun v w ↦
    match v, w with
    | Sum.inl u, Sum.inr w => adj u w
    | Sum.inr w, Sum.inl u => adj u w
    | _, _ => False

/-- The edges carrying one unit of flow form a subgraph of the original bipartite graph. -/
def bipartite_matching_from_flow
    (x : BipartiteMatchingFlowArc adj → ℕ) : (bipartite_relation_graph adj).Subgraph where
  verts
    | Sum.inl u => ∃ w, ∃ h : adj u w, x (.edge ⟨(u, w), h⟩) = 1
    | Sum.inr w => ∃ u, ∃ h : adj u w, x (.edge ⟨(u, w), h⟩) = 1
  Adj
    | Sum.inl u, Sum.inr w => ∃ h : adj u w, x (.edge ⟨(u, w), h⟩) = 1
    | Sum.inr w, Sum.inl u => ∃ h : adj u w, x (.edge ⟨(u, w), h⟩) = 1
    | _, _ => False
  adj_sub := by
    intro v w h
    rcases v with u | w'
    · rcases w with u' | w
      · cases h
      · rcases h with ⟨huw, _⟩
        simp [bipartite_relation_graph, SimpleGraph.fromRel_adj, huw]
    · rcases w with u | w
      · rcases h with ⟨huw, _⟩
        simp [bipartite_relation_graph, SimpleGraph.fromRel_adj, huw]
      · cases h
  edge_vert := by
    intro v w h
    rcases v with u | w'
    · rcases w with u' | w
      · cases h
      · rcases h with ⟨huw, hxuw⟩
        exact ⟨w, huw, hxuw⟩
    · rcases w with u | w
      · rcases h with ⟨huw, hxuw⟩
        exact ⟨u, huw, hxuw⟩
      · cases h
  symm := by
    intro v w h
    rcases v with u | w'
    · rcases w with u' | w
      · cases h
      · simpa using h
    · rcases w with u | w
      · simpa using h
      · cases h

omit [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W] [DecidableRel adj] in
/-- Unfolding characterization of adjacency in the matching subgraph extracted from a flow. -/
theorem bipartite_matching_from_flow_adj_iff
    {x : BipartiteMatchingFlowArc adj → ℕ} {u : U} {w : W} :
    (bipartite_matching_from_flow adj x).Adj (Sum.inl u) (Sum.inr w) ↔
      ∃ h : adj u w, x (.edge ⟨(u, w), h⟩) = 1 := by
  -- The subgraph adjacency field is exactly the selected-edge relation.
  rfl

/-- Helper for Remark 4.4.2-extra-2: every source-to-left arc of a feasible flow has value at
most `1`. -/
theorem source_left_flow_le_one
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x) (u : U) :
    x (.source_left u) ≤ 1 := by
  rcases hx with ⟨hcap, _, _⟩
  -- The capacity constraint reads exactly as an upper bound by `1` on these arcs.
  have hcap_u : ((x (.source_left u) : WithTop ℕ) ≤ (1 : WithTop ℕ)) := by
    simpa [bipartite_matching_flow_capacity] using hcap (.source_left u)
  exact WithTop.coe_le_coe.mp hcap_u

/-- Helper for Remark 4.4.2-extra-2: every right-to-sink arc of a feasible flow has value at most
`1`. -/
theorem right_sink_flow_le_one
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x) (w : W) :
    x (.right_sink w) ≤ 1 := by
  rcases hx with ⟨hcap, _, _⟩
  -- The same capacity bound holds on arcs entering the sink.
  have hcap_w : ((x (.right_sink w) : WithTop ℕ) ≤ (1 : WithTop ℕ)) := by
    simpa [bipartite_matching_flow_capacity] using hcap (.right_sink w)
  exact WithTop.coe_le_coe.mp hcap_w

/-- Helper for Remark 4.4.2-extra-2: the flow on an original edge is bounded by the source arc
entering its left endpoint. -/
theorem edge_flow_le_source_left
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x)
    (e : bipartite_relation_edge adj) :
    x (.edge e) ≤ x (.source_left e.1.1) := by
  rcases hx with ⟨_, hleft, _⟩
  -- Compare the chosen edge contribution with the full incident-edge sum on the left endpoint.
  have hle_sum :
      x (.edge e) ≤ Finset.sum (left_incident_edges adj (e.1.1)) (fun e' ↦ x (.edge e')) := by
    have hnonneg : ∀ e' ∈ left_incident_edges adj (e.1.1), 0 ≤ x (.edge e') := by
      intro e' he'
      exact Nat.zero_le _
    exact Finset.single_le_sum hnonneg (by simp [left_incident_edges])
  simpa [hleft e.1.1] using hle_sum

/-- Helper for Remark 4.4.2-extra-2: the flow on an original edge is bounded by the sink arc
leaving its right endpoint. -/
theorem edge_flow_le_right_sink
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x)
    (e : bipartite_relation_edge adj) :
    x (.edge e) ≤ x (.right_sink e.1.2) := by
  rcases hx with ⟨_, _, hright⟩
  -- Compare the edge with the full sum of edges entering its right endpoint.
  have hle_sum :
      x (.edge e) ≤ Finset.sum (right_incident_edges adj (e.1.2)) (fun e' ↦ x (.edge e')) := by
    have hnonneg : ∀ e' ∈ right_incident_edges adj (e.1.2), 0 ≤ x (.edge e') := by
      intro e' he'
      exact Nat.zero_le _
    exact Finset.single_le_sum hnonneg (by simp [right_incident_edges])
  simpa [hright e.1.2] using hle_sum

/-- Remark 4.4.2-extra-2 (1). Every integral `s,t`-flow in the layered network attached to a
bipartite graph is a `0,1`-vector on the arc set. -/
theorem bipartite_matching_flow_is_zero_one
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x) :
    ∀ a : BipartiteMatchingFlowArc adj, x a = 0 ∨ x a = 1 := by
  intro a
  -- Every arc is bounded by `1`, so a natural-valued flow can only be `0` or `1`.
  cases a with
  | source_left u =>
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp (source_left_flow_le_one adj x hx u)
  | right_sink w =>
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp (right_sink_flow_le_one adj x hx w)
  | edge e =>
      exact Nat.le_one_iff_eq_zero_or_eq_one.mp <|
        (edge_flow_le_source_left adj x hx e).trans (source_left_flow_le_one adj x hx e.1.1)

/-- Helper for Remark 4.4.2-extra-2: two selected edges sharing a left endpoint must have the same
right endpoint. -/
lemma selected_edges_share_left_implies_eq
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x)
    {u : U} {w₁ w₂ : W} (h₁ : adj u w₁) (h₂ : adj u w₂)
    (hx₁ : x (.edge ⟨(u, w₁), h₁⟩) = 1) (hx₂ : x (.edge ⟨(u, w₂), h₂⟩) = 1) :
    w₁ = w₂ := by
  by_contra hne
  have hsource_le_one := source_left_flow_le_one adj x hx u
  let e₁ : bipartite_relation_edge adj := ⟨(u, w₁), h₁⟩
  let e₂ : bipartite_relation_edge adj := ⟨(u, w₂), h₂⟩
  have he₁_mem : e₁ ∈ left_incident_edges adj u := by
    simp [left_incident_edges, e₁]
  have he₂_mem : e₂ ∈ left_incident_edges adj u := by
    simp [left_incident_edges, e₂]
  have he₂_ne : e₂ ≠ e₁ := by
    intro hEq
    apply hne
    exact (congrArg (fun e : bipartite_relation_edge adj ↦ e.1.2) hEq).symm
  have hx₁' : x (.edge e₁) = 1 := by
    simpa [e₁] using hx₁
  have hx₂' : x (.edge e₂) = 1 := by
    simpa [e₂] using hx₂
  -- Two distinct unit contributions force the left-incident sum above `1`.
  have hlt_sum :
      x (.edge e₁) < Finset.sum (left_incident_edges adj u) (fun e ↦ x (.edge e)) := by
    have hpos : 0 < x (.edge e₂) := by
      simp [hx₂']
    have hnonneg : ∀ e ∈ left_incident_edges adj u, e ≠ e₁ → 0 ≤ x (.edge e) := by
      intro e he _
      exact Nat.zero_le _
    exact Finset.single_lt_sum he₂_ne he₁_mem he₂_mem hpos hnonneg
  have hsum_le_one : Finset.sum (left_incident_edges adj u) (fun e ↦ x (.edge e)) ≤ 1 := by
    rcases hx with ⟨_, hleft, _⟩
    simpa [hleft u] using hsource_le_one
  have : 1 < Finset.sum (left_incident_edges adj u) (fun e ↦ x (.edge e)) := by
    simpa [hx₁'] using hlt_sum
  exact (Nat.not_lt_of_ge hsum_le_one) this

/-- Helper for Remark 4.4.2-extra-2: two selected edges sharing a right endpoint must have the
same left endpoint. -/
lemma selected_edges_share_right_implies_eq
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x)
    {u₁ u₂ : U} {w : W} (h₁ : adj u₁ w) (h₂ : adj u₂ w)
    (hx₁ : x (.edge ⟨(u₁, w), h₁⟩) = 1) (hx₂ : x (.edge ⟨(u₂, w), h₂⟩) = 1) :
    u₁ = u₂ := by
  by_contra hne
  have hsink_le_one := right_sink_flow_le_one adj x hx w
  let e₁ : bipartite_relation_edge adj := ⟨(u₁, w), h₁⟩
  let e₂ : bipartite_relation_edge adj := ⟨(u₂, w), h₂⟩
  have he₁_mem : e₁ ∈ right_incident_edges adj w := by
    simp [right_incident_edges, e₁]
  have he₂_mem : e₂ ∈ right_incident_edges adj w := by
    simp [right_incident_edges, e₂]
  have he₂_ne : e₂ ≠ e₁ := by
    intro hEq
    apply hne
    exact (congrArg (fun e : bipartite_relation_edge adj ↦ e.1.1) hEq).symm
  have hx₁' : x (.edge e₁) = 1 := by
    simpa [e₁] using hx₁
  have hx₂' : x (.edge e₂) = 1 := by
    simpa [e₂] using hx₂
  -- The same strict-sum argument works on the right side of the bipartition.
  have hlt_sum :
      x (.edge e₁) < Finset.sum (right_incident_edges adj w) (fun e ↦ x (.edge e)) := by
    have hpos : 0 < x (.edge e₂) := by
      simp [hx₂']
    have hnonneg : ∀ e ∈ right_incident_edges adj w, e ≠ e₁ → 0 ≤ x (.edge e) := by
      intro e he _
      exact Nat.zero_le _
    exact Finset.single_lt_sum he₂_ne he₁_mem he₂_mem hpos hnonneg
  have hsum_le_one : Finset.sum (right_incident_edges adj w) (fun e ↦ x (.edge e)) ≤ 1 := by
    rcases hx with ⟨_, _, hright⟩
    simpa [hright w] using hsink_le_one
  have : 1 < Finset.sum (right_incident_edges adj w) (fun e ↦ x (.edge e)) := by
    simpa [hx₁'] using hlt_sum
  exact (Nat.not_lt_of_ge hsum_le_one) this

/-- Remark 4.4.2-extra-2 (2). The original bipartite edges carrying one unit of flow form a
matching. -/
theorem bipartite_matching_from_flow_is_matching
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x) :
    (bipartite_matching_from_flow adj x).IsMatching := by
  intro v hv
  rcases v with u | w
  · rcases hv with ⟨w, huw, hxuw⟩
    refine ⟨Sum.inr w, ?_, ?_⟩
    · -- The selected edge gives the unique matched neighbor of this left vertex.
      exact (bipartite_matching_from_flow_adj_iff adj).2
        ⟨huw, hxuw⟩
    · intro y hy
      rcases y with u' | w'
      · cases hy
      · have hy' :
            ∃ h : adj u w', x (.edge ⟨(u, w'), h⟩) = 1 := by
          exact (bipartite_matching_from_flow_adj_iff adj).1 hy
        rcases hy' with ⟨huw', hxuw'⟩
        have hw' : w' = w :=
          selected_edges_share_left_implies_eq adj x hx huw' huw hxuw' hxuw
        simp [hw']
  · rcases hv with ⟨u, huw, hxuw⟩
    refine ⟨Sum.inl u, ?_, ?_⟩
    · -- Use symmetry to turn the chosen right-left adjacency into the left-right API.
      exact ((bipartite_matching_from_flow_adj_iff adj).2
        ⟨huw, hxuw⟩).symm
    · intro y hy
      rcases y with u' | w'
      · have hy' :
            ∃ h : adj u' w, x (.edge ⟨(u', w), h⟩) = 1 := by
          exact (bipartite_matching_from_flow_adj_iff adj).1 hy.symm
        rcases hy' with ⟨hu'w, hxu'w⟩
        have hu' : u' = u :=
          selected_edges_share_right_implies_eq adj x hx hu'w huw hxu'w hxuw
        simp [hu']
      · cases hy

omit [DecidableEq W] in
/-- Helper for Remark 4.4.2-extra-2: summing first over left vertices and then over their incident
original edges counts each original edge exactly once. -/
lemma sum_left_incident_edges_eq_sum_all_edges
    (f : bipartite_relation_edge adj → ℕ) :
    Finset.sum Finset.univ (fun u ↦ Finset.sum (left_incident_edges adj u) f) =
      Finset.sum Finset.univ f := by
  -- The left endpoint map partitions the original edges into disjoint fibers.
  simpa [left_incident_edges] using
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset (bipartite_relation_edge adj))
      (Finset.univ : Finset U)
      (fun e ↦ e.1.1)
      f)

/-- Remark 4.4.2-extra-2 (3). The value of an integral flow in the layered network equals the
number of original graph edges carrying one unit of flow. -/
theorem bipartite_matching_flow_value_eq_card_selected_edges
    (x : BipartiteMatchingFlowArc adj → ℕ) (hx : IsBipartiteMatchingFlow adj x) :
    bipartite_matching_flow_value adj x = (bipartite_matching_selected_edges adj x).card := by
  have hzeroone := bipartite_matching_flow_is_zero_one adj x hx
  rcases hx with ⟨_, hleft, _⟩
  -- Rewrite the flow value as a sum over all original edges via the left-balance equations.
  calc
    bipartite_matching_flow_value adj x
        = Finset.sum Finset.univ (fun u ↦
            Finset.sum (left_incident_edges adj u) (fun e ↦ x (.edge e))) := by
          simp [bipartite_matching_flow_value, hleft]
    _ = Finset.sum Finset.univ (fun e : bipartite_relation_edge adj ↦ x (.edge e)) := by
          exact sum_left_incident_edges_eq_sum_all_edges adj (fun e ↦ x (.edge e))
    _ = ∑ e : bipartite_relation_edge adj, if x (.edge e) = 1 then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rcases hzeroone (.edge e) with hx0 | hx1
          · simp [hx0]
          · simp [hx1]
    _ = (bipartite_matching_selected_edges adj x).card := by
          rw [Finset.card_eq_sum_ones]
          simp [bipartite_matching_selected_edges]

end Remark442Extra2

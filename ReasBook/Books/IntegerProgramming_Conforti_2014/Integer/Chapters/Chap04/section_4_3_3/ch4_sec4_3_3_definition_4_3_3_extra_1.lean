/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1

noncomputable section

open scoped BigOperators

section Definition_4_3_3_extra_1

variable {V A : Type} [Fintype A]

/-- The arcs entering the vertex `v`. -/
def incoming_arcs (head : A → V) (v : V) : Finset A :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq V := Classical.decEq V
  Finset.univ.filter fun e ↦ head e = v

/-- An arc lies in `incoming_arcs head v` exactly when its head is `v`. -/
@[simp] theorem mem_incoming_arcs_iff {head : A → V} {v : V} {e : A} :
    e ∈ incoming_arcs head v ↔ head e = v := by
  classical
  simp [incoming_arcs]

/-- The arcs leaving the vertex `v`. -/
def outgoing_arcs (tail : A → V) (v : V) : Finset A :=
  let _ : DecidableEq A := Classical.decEq A
  let _ : DecidableEq V := Classical.decEq V
  Finset.univ.filter fun e ↦ tail e = v

/-- An arc lies in `outgoing_arcs tail v` exactly when its tail is `v`. -/
@[simp] theorem mem_outgoing_arcs_iff {tail : A → V} {v : V} {e : A} :
    e ∈ outgoing_arcs tail v ↔ tail e = v := by
  classical
  simp [outgoing_arcs]

/-- The upstream total incoming-flow owner is the sum over the incoming arc fiber. -/
@[simp] theorem incoming_flow_eq_sum_incoming_arcs
    (head : A → V) (x : A → ℝ) (v : V) :
    incoming_flow head x v = Finset.sum (incoming_arcs head v) x := by
  classical
  unfold incoming_flow incoming_arcs
  refine congrArg (fun s : Finset A ↦ s.sum x) ?_
  ext e
  simp

/-- The upstream total outgoing-flow owner is the sum over the outgoing arc fiber. -/
@[simp] theorem outgoing_flow_eq_sum_outgoing_arcs
    (tail : A → V) (x : A → ℝ) (v : V) :
    outgoing_flow tail x v = Finset.sum (outgoing_arcs tail v) x := by
  classical
  unfold outgoing_flow outgoing_arcs
  refine congrArg (fun s : Finset A ↦ s.sum x) ?_
  ext e
  simp

/-- Definition 4.3.3-extra-1 (1). An `s,t`-flow is a nonnegative arc vector satisfying flow
conservation at every vertex other than `s` and `t`. -/
@[mk_iff isSTFlow_iff]
class IsSTFlow (tail head : A → V) (s t : V) (x : A → ℝ) : Prop where
  /-- Every arc value of an `s,t`-flow is nonnegative. -/
  nonneg (e : A) : 0 ≤ x e
  /-- Flow is conserved at every vertex other than `s` and `t`. -/
  conservation (v : V) (hs : v ≠ s) (ht : v ≠ t) :
    incoming_flow head x v = outgoing_flow tail x v

/-- Definition 4.3.3-extra-1 (2). The value of an `s,t`-flow is the net flow leaving the source
vertex `s`. -/
def st_flow_value (tail head : A → V) (s : V) (x : A → ℝ) : ℝ :=
  outgoing_flow tail x s - incoming_flow head x s

/-- Helper for Definition 4.3.3-extra-1: the net imbalance at a vertex is incoming flow minus
outgoing flow. -/
private def vertex_balance (tail head : A → V) (x : A → ℝ) (v : V) : ℝ :=
  incoming_flow head x v - outgoing_flow tail x v

/-- Helper for Definition 4.3.3-extra-1: the vertices incident to at least one arc. -/
private abbrev incident_vertex_support (tail head : A → V) : Finset V :=
  circuit_vertices tail head Finset.univ

/-- Helper for Definition 4.3.3-extra-1: a vertex with no incident arc has zero balance. -/
private lemma vertex_balance_eq_zero_of_not_incident {tail head : A → V} {x : A → ℝ} {v : V}
    (hv : v ∉ incident_vertex_support tail head) :
    vertex_balance tail head x v = 0 := by
  classical
  have h_incoming : incoming_arcs head v = ∅ := by
    ext e
    constructor
    · intro he
      have hev : head e = v := mem_incoming_arcs_iff.mp he
      have hmem : v ∈ incident_vertex_support tail head := by
        change v ∈ circuit_vertices tail head Finset.univ
        exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨e, by simp, hev⟩
      exact (hv hmem).elim
    · simp
  have h_outgoing : outgoing_arcs tail v = ∅ := by
    ext e
    constructor
    · intro he
      have hev : tail e = v := mem_outgoing_arcs_iff.mp he
      have hmem : v ∈ incident_vertex_support tail head := by
        change v ∈ circuit_vertices tail head Finset.univ
        exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨e, by simp, hev⟩
      exact (hv hmem).elim
    · simp
  simp [vertex_balance, h_incoming, h_outgoing]

/-- Helper for Definition 4.3.3-extra-1: summing incoming flow over the incident support counts
each arc exactly once, at its head. -/
private lemma sum_incoming_flow_over_incident_support_eq_total
    {tail head : A → V} {x : A → ℝ} :
    Finset.sum (incident_vertex_support tail head) (incoming_flow head x) = ∑ e, x e := by
  classical
  have hpair :
      Set.PairwiseDisjoint (↑(incident_vertex_support tail head)) (incoming_arcs head) := by
    intro v hv w hw hne
    refine Finset.disjoint_left.mpr ?_
    intro e hev hew
    have h_head_v : head e = v := mem_incoming_arcs_iff.mp hev
    have h_head_w : head e = w := mem_incoming_arcs_iff.mp hew
    exact hne (h_head_v.symm.trans h_head_w)
  have hunion :
      (incident_vertex_support tail head).biUnion (incoming_arcs head) = Finset.univ := by
    ext e
    constructor
    · intro _
      simp
    · intro _
      have hhead_mem : head e ∈ incident_vertex_support tail head := by
        change head e ∈ circuit_vertices tail head Finset.univ
        exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨e, by simp, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨head e, hhead_mem, by simp⟩
  -- Rewrite the vertexwise incoming total as a sum over head fibers.
  simp_rw [incoming_flow_eq_sum_incoming_arcs]
  -- Collapse the disjoint union of head fibers to the full arc set.
  calc
    Finset.sum (incident_vertex_support tail head)
        (fun v ↦ Finset.sum (incoming_arcs head v) x) =
        Finset.sum ((incident_vertex_support tail head).biUnion (incoming_arcs head)) x := by
          simpa using (Finset.sum_biUnion hpair (f := x)).symm
    _ = ∑ e, x e := by
      simp [hunion]

/-- Helper for Definition 4.3.3-extra-1: summing outgoing flow over the incident support counts
each arc exactly once, at its tail. -/
private lemma sum_outgoing_flow_over_incident_support_eq_total
    {tail head : A → V} {x : A → ℝ} :
    Finset.sum (incident_vertex_support tail head) (outgoing_flow tail x) = ∑ e, x e := by
  classical
  have hpair :
      Set.PairwiseDisjoint (↑(incident_vertex_support tail head)) (outgoing_arcs tail) := by
    intro v hv w hw hne
    refine Finset.disjoint_left.mpr ?_
    intro e hev hew
    have h_tail_v : tail e = v := mem_outgoing_arcs_iff.mp hev
    have h_tail_w : tail e = w := mem_outgoing_arcs_iff.mp hew
    exact hne (h_tail_v.symm.trans h_tail_w)
  have hunion :
      (incident_vertex_support tail head).biUnion (outgoing_arcs tail) = Finset.univ := by
    ext e
    constructor
    · intro _
      simp
    · intro _
      have htail_mem : tail e ∈ incident_vertex_support tail head := by
        change tail e ∈ circuit_vertices tail head Finset.univ
        exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_image.mpr ⟨e, by simp, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨tail e, htail_mem, by simp⟩
  -- Rewrite the vertexwise outgoing total as a sum over tail fibers.
  simp_rw [outgoing_flow_eq_sum_outgoing_arcs]
  -- Collapse the disjoint union of tail fibers to the full arc set.
  calc
    Finset.sum (incident_vertex_support tail head)
        (fun v ↦ Finset.sum (outgoing_arcs tail v) x) =
        Finset.sum ((incident_vertex_support tail head).biUnion (outgoing_arcs tail)) x := by
          simpa using (Finset.sum_biUnion hpair (f := x)).symm
    _ = ∑ e, x e := by
      simp [hunion]

/-- Helper for Definition 4.3.3-extra-1: the total vertex balance on the true incident support
vanishes. -/
private lemma sum_vertex_balance_over_incident_support_eq_zero
    {tail head : A → V} {x : A → ℝ} :
    Finset.sum (incident_vertex_support tail head) (vertex_balance tail head x) = 0 := by
  -- Rewrite the total balance as incoming total minus outgoing total.
  simp_rw [vertex_balance]
  rw [Finset.sum_sub_distrib,
    sum_incoming_flow_over_incident_support_eq_total,
    sum_outgoing_flow_over_incident_support_eq_total]
  simp

/-- Helper for Definition 4.3.3-extra-1: inserting `s` and `t` does not change the total balance
sum once nonincident vertices are discarded. -/
private lemma sum_vertex_balance_over_relevant_vertices_eq_sum_incident_support [DecidableEq V]
    {s t : V} {tail head : A → V} {x : A → ℝ} :
    Finset.sum (insert s (insert t (incident_vertex_support tail head)))
      (vertex_balance tail head x) =
      Finset.sum (incident_vertex_support tail head) (vertex_balance tail head x) := by
  classical
  -- Restrict the enlarged relevant set back to the actual incident support.
  refine (Finset.sum_subset ?_ ?_).symm
  · intro v hv
    simp [hv]
  · intro v hv_relevant hv_not_support
    exact vertex_balance_eq_zero_of_not_incident hv_not_support

/-- Helper for Definition 4.3.3-extra-1: the total vertex imbalance on the relevant finite support
vanishes. -/
private lemma sum_vertex_balance_over_relevant_vertices_eq_zero [DecidableEq V]
    {s t : V} {tail head : A → V} {x : A → ℝ} :
    Finset.sum (insert s (insert t (incident_vertex_support tail head)))
      (vertex_balance tail head x) = 0 := by
  -- First remove the vertices that were inserted only to cover the source and sink.
  rw [sum_vertex_balance_over_relevant_vertices_eq_sum_incident_support]
  -- Then apply the global conservation identity on the incident support itself.
  exact sum_vertex_balance_over_incident_support_eq_zero

/-- Definition 4.3.3-extra-1 (3). For an `s,t`-flow, the net flow leaving `s` equals the net flow
entering `t`. -/
theorem st_flow_value_eq_sink_balance {tail head : A → V} {s t : V} {x : A → ℝ}
    (hx : IsSTFlow tail head s t x) :
    st_flow_value tail head s x = incoming_flow head x t - outgoing_flow tail x t := by
  classical
  let b : V → ℝ := vertex_balance tail head x
  let R : Finset V := insert s (insert t (incident_vertex_support tail head))
  have h_total : Finset.sum R b = 0 := by
    have h : Finset.sum (insert s (insert t (incident_vertex_support tail head)))
        (vertex_balance tail head x) = 0 := sum_vertex_balance_over_relevant_vertices_eq_zero
    simpa [b, R] using h
  have h_source :
      st_flow_value tail head s x = -b s := by
    simp [st_flow_value, b, vertex_balance, sub_eq_add_neg]
  by_cases hst : s = t
  · subst hst
    have hs_mem : s ∈ R := by
      simp [R]
    have h_split :
        b s + Finset.sum (R.erase s) b = 0 := by
      rw [Finset.add_sum_erase R b hs_mem, h_total]
    have h_rest :
        Finset.sum (R.erase s) b = 0 := by
      refine Finset.sum_eq_zero fun v hv ↦ ?_
      have hv_ne_s : v ≠ s := (Finset.mem_erase.mp hv).1
      simpa [b, vertex_balance] using sub_eq_zero.mpr (hx.conservation v hv_ne_s hv_ne_s)
    have hb_source : b s = 0 := by
      simpa [h_rest] using h_split
    calc
      st_flow_value tail head s x = -b s := h_source
      _ = 0 := by simp [hb_source]
      _ = b s := by simp [hb_source]
      _ = incoming_flow head x s - outgoing_flow tail x s := by
            simp [b, vertex_balance]
  · have hs_mem : s ∈ R := by
      simp [R]
    have hts : t ≠ s := fun h ↦ hst h.symm
    have ht_mem : t ∈ R.erase s := by
      simp [R, hts]
    have h_split_source :
        b s + Finset.sum (R.erase s) b = 0 := by
      rw [Finset.add_sum_erase R b hs_mem, h_total]
    have h_middle :
        Finset.sum ((R.erase s).erase t) b = 0 := by
      refine Finset.sum_eq_zero fun v hv ↦ ?_
      have hv_ne_t : v ≠ t := (Finset.mem_erase.mp hv).1
      have hv_mem_erase_s : v ∈ R.erase s := (Finset.mem_erase.mp hv).2
      have hv_ne_s : v ≠ s := (Finset.mem_erase.mp hv_mem_erase_s).1
      simpa [b, vertex_balance] using sub_eq_zero.mpr (hx.conservation v hv_ne_s hv_ne_t)
    have h_split_sink :
        b t + Finset.sum ((R.erase s).erase t) b = Finset.sum (R.erase s) b :=
      Finset.add_sum_erase (R.erase s) b ht_mem
    have h_rest_as_sink :
        Finset.sum (R.erase s) b = b t := by
      simpa [h_middle] using h_split_sink.symm
    have hb_relation : -b s = b t := by
      have h_source_sink : b s + b t = 0 := by
        simpa [h_rest_as_sink] using h_split_source
      have ht_eq : b t = -b s := eq_neg_of_add_eq_zero_right h_source_sink
      simpa [eq_comm] using ht_eq
    calc
      st_flow_value tail head s x = -b s := h_source
      _ = b t := hb_relation
      _ = incoming_flow head x t - outgoing_flow tail x t := by
            simp [b, vertex_balance]

/-- Definition 4.3.3-extra-1 (4). A feasible `s,t`-flow with respect to capacities `c` is an
`s,t`-flow whose arc values stay between `0` and `c`. -/
@[mk_iff isFeasibleSTFlow_iff]
class IsFeasibleSTFlow (tail head : A → V) (s t : V) (c x : A → ℝ) : Prop
    extends IsSTFlow tail head s t x where
  /-- Every flow value is bounded above by the corresponding capacity. -/
  le_capacity (e : A) : x e ≤ c e

/-- A feasible `s,t`-flow forces the capacities to be nonnegative. -/
theorem IsFeasibleSTFlow.capacity_nonneg {tail head : A → V} {s t : V} {c x : A → ℝ}
    (hx : IsFeasibleSTFlow tail head s t c x) (e : A) :
    0 ≤ c e :=
  le_trans (hx.nonneg e) (hx.le_capacity e)

/-- Under source and sink conservation as well, an `s,t`-flow is an ordinary circulation. -/
theorem IsSTFlow.toIsCirculation {tail head : A → V} {s t : V} {x : A → ℝ}
    (hx : IsSTFlow tail head s t x)
    (hs : incoming_flow head x s = outgoing_flow tail x s)
    (ht : incoming_flow head x t = outgoing_flow tail x t) :
    IsCirculation tail head x := by
  refine
    { flow_conservation := ?_
      nonneg := hx.nonneg }
  intro v
  by_cases hvs : v = s
  · simpa [hvs] using hs
  · by_cases hvt : v = t
    · simpa [hvt] using ht
    · exact hx.conservation v hvs hvt

/-- Definition 4.3.3-extra-1 (5). An `s,t`-flow is integral when each arc value is an integer. -/
def IsIntegralSTFlow (x : A → ℝ) : Prop :=
  ∀ e, ∃ z : ℤ, x e = (z : ℝ)

/-- Definition 4.3.3-extra-1 (6). A vertex subset `S` determines an `s,t`-cut side when it
contains `s` and excludes `t`. -/
def IsSTCutSide (s t : V) (S : Set V) : Prop :=
  s ∈ S ∧ t ∉ S

/-- The incoming arcs of the cut determined by the vertex subset `S`. -/
def incoming_cut_arcs (tail head : A → V) (S : Set V) : Finset A :=
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  (Finset.univ.filter fun e ↦ tail e ∉ S).filter fun e ↦ head e ∈ S

/-- The incoming cut `δ⁻(S)` in the finite digraph with endpoint maps `tail` and `head`. -/
notation "δ⁻[" tail ", " head "] " S:arg => incoming_cut_arcs tail head S

/-- An arc lies in `δ⁻[tail, head] S` exactly when it enters `S` from its complement. -/
@[simp] theorem mem_incoming_cut_arcs_iff {tail head : A → V} {S : Set V} {e : A} :
    e ∈ δ⁻[tail, head] S ↔ tail e ∉ S ∧ head e ∈ S := by
  classical
  simp [incoming_cut_arcs]

/-- Definition 4.3.3-extra-1 (7). The arcs of the cut determined by `S` are the arcs leaving `S`
and entering its complement. -/
def outgoing_cut_arcs (tail head : A → V) (S : Set V) : Finset A :=
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  (Finset.univ.filter fun e ↦ tail e ∈ S).filter fun e ↦ head e ∉ S

/-- The outgoing cut `δ⁺(S)` in the finite digraph with endpoint maps `tail` and `head`. -/
notation "δ⁺[" tail ", " head "] " S:arg => outgoing_cut_arcs tail head S

/-- An arc lies in `δ⁺[tail, head] S` exactly when it leaves `S` and enters its
complement. -/
@[simp] theorem mem_outgoing_cut_arcs_iff {tail head : A → V} {S : Set V} {e : A} :
    e ∈ δ⁺[tail, head] S ↔ tail e ∈ S ∧ head e ∉ S := by
  classical
  simp [outgoing_cut_arcs]

/-- Definition 4.3.3-extra-1 (8). The capacity of the cut determined by `S` is the sum of the
capacities of the arcs in `δ⁺[tail, head] S`. -/
def cut_capacity (tail head : A → V) (c : A → ℝ) (S : Set V) : ℝ :=
  (δ⁺[tail, head] S).sum c

/-- A feasible `s,t`-flow is maximum when every other feasible `s,t`-flow has no larger value. -/
@[mk_iff isMaximumSTFlow_iff]
class IsMaximumSTFlow
    (tail head : A → V) (s t : V) (c x : A → ℝ) : Prop
    extends IsFeasibleSTFlow tail head s t c x where
  /-- Every feasible comparison flow has value at most the value of `x`. -/
  le_st_flow_value (y : A → ℝ) (hy : IsFeasibleSTFlow tail head s t c y) :
    st_flow_value tail head s y ≤ st_flow_value tail head s x

/-- A maximum `s,t`-flow is, in particular, feasible. -/
theorem IsMaximumSTFlow.isFeasibleSTFlow {tail head : A → V} {s t : V} {c x : A → ℝ}
    (hx : IsMaximumSTFlow tail head s t c x) :
    IsFeasibleSTFlow tail head s t c x :=
  hx.toIsFeasibleSTFlow

/-- An `s,t`-cut side is minimum when its capacity is at most the capacity of every other
`s,t`-cut side. -/
@[mk_iff isMinimumSTCut_iff]
class IsMinimumSTCut
    (tail head : A → V) (c : A → ℝ) (s t : V) (S : Set V) : Prop
    extends IsSTCutSide s t S where
  /-- Every comparison `s,t`-cut side has capacity at least the capacity of `S`. -/
  le_cut_capacity (T : Set V) (hT : IsSTCutSide s t T) :
    cut_capacity tail head c S ≤ cut_capacity tail head c T

/-- A minimum `s,t`-cut is, in particular, an `s,t`-cut side. -/
theorem IsMinimumSTCut.isSTCutSide {tail head : A → V} {c : A → ℝ} {s t : V} {S : Set V}
    (hS : IsMinimumSTCut tail head c s t S) :
    IsSTCutSide s t S := by
  exact hS.toAnd

end Definition_4_3_3_extra_1

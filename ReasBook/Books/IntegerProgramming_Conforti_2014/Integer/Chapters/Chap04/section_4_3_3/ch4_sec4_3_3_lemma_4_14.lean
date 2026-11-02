import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1

open scoped BigOperators

section MaxFlowMinCut

variable {V A : Type} [Fintype A]

/-- Helper for Lemma 4.14: the finite support of the cut side consists of the source together with
all incident vertices that lie in `S`. -/
private noncomputable abbrev cut_side_vertices (tail head : A → V) (s : V) (S : Set V) : Finset V :=
  let _ : DecidableEq V := Classical.decEq V
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  insert s ((circuit_vertices tail head Finset.univ).filter fun v ↦ v ∈ S)

/-- Helper for Lemma 4.14: among vertices incident to some arc, membership in the finite cut-side
support is equivalent to membership in `S`. -/
private lemma mem_cut_side_vertices_iff_of_incident
    {tail head : A → V} {s t : V} {S : Set V} (hS : IsSTCutSide s t S)
    {v : V} (hv : v ∈ circuit_vertices tail head Finset.univ) :
    v ∈ cut_side_vertices tail head s S ↔ v ∈ S := by
  classical
  constructor
  · intro hvCut
    have hvCut' : v ∈ insert s ((circuit_vertices tail head Finset.univ).filter fun w ↦ w ∈ S) := by
      simpa [cut_side_vertices] using hvCut
    rcases Finset.mem_insert.mp hvCut' with rfl | hvFilter
    · exact hS.1
    · exact (Finset.mem_filter.mp hvFilter).2
  · intro hvS
    by_cases hvs : v = s
    · subst hvs
      simp [cut_side_vertices, hS.1]
    · have hvCut' :
          v ∈ insert s ((circuit_vertices tail head Finset.univ).filter fun w ↦ w ∈ S) :=
        Finset.mem_insert.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hv, hvS⟩
      simpa [cut_side_vertices] using hvCut'

/-- Helper for Lemma 4.14: summing the vertex balances over the finite cut-side support leaves
only the source imbalance. -/
private lemma cut_side_balance_eq_neg_st_flow_value
    (tail head : A → V) (x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsSTFlow tail head s t x) (hS : IsSTCutSide s t S) :
    Finset.sum (cut_side_vertices tail head s S)
      (fun v ↦ incoming_flow head x v - outgoing_flow tail x v) =
        - st_flow_value tail head s x := by
  classical
  let R : Finset V := cut_side_vertices tail head s S
  have hs_mem : s ∈ R := by
    simp [R, cut_side_vertices]
  have h_rest :
      Finset.sum (R.erase s) (fun v ↦ incoming_flow head x v - outgoing_flow tail x v) = 0 := by
    -- Every remaining vertex lies in `S` and is distinct from `s`, so conservation applies.
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    have hv_mem : v ∈ R := Finset.mem_of_mem_erase hv
    have hv_ne_s : v ≠ s := (Finset.mem_erase.mp hv).1
    have hv_in_S : v ∈ S := by
      rcases Finset.mem_insert.mp hv_mem with hvs | hvFilter
      · exact (hv_ne_s hvs).elim
      · exact (Finset.mem_filter.mp hvFilter).2
    have hv_ne_t : v ≠ t := by
      intro hvt
      exact hS.2 (hvt ▸ hv_in_S)
    simpa using sub_eq_zero.mpr (hx.conservation v hv_ne_s hv_ne_t)
  -- Split off the source contribution from the finite balance sum.
  calc
    Finset.sum R (fun v ↦ incoming_flow head x v - outgoing_flow tail x v) =
        (incoming_flow head x s - outgoing_flow tail x s) +
          Finset.sum (R.erase s) (fun v ↦ incoming_flow head x v - outgoing_flow tail x v) := by
          rw [← Finset.add_sum_erase R
            (fun v ↦ incoming_flow head x v - outgoing_flow tail x v) hs_mem]
    _ = incoming_flow head x s - outgoing_flow tail x s := by
          rw [h_rest, add_zero]
    _ = - st_flow_value tail head s x := by
          simp [st_flow_value]

/-- Helper for Lemma 4.14: the value of an `s,t`-flow equals the total flow leaving the cut side
minus the total flow entering it. -/
private lemma st_flow_value_eq_outgoing_cut_flow_sub_incoming_cut_flow
    (tail head : A → V) (x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsSTFlow tail head s t x) (hS : IsSTCutSide s t S) :
    st_flow_value tail head s x =
      Finset.sum (δ⁺[tail, head] S) x - Finset.sum (δ⁻[tail, head] S) x := by
  classical
  let R : Finset V := cut_side_vertices tail head s S
  let internal : Finset A := Finset.univ.filter fun e ↦ tail e ∈ S ∧ head e ∈ S
  have hbalance :
      Finset.sum R (fun v ↦ incoming_flow head x v) -
          Finset.sum R (fun v ↦ outgoing_flow tail x v) =
        - st_flow_value tail head s x := by
    -- First separate incoming and outgoing totals, then reuse the balance identity.
    simpa [R, Finset.sum_sub_distrib] using
      cut_side_balance_eq_neg_st_flow_value tail head x s t S hx hS
  have hIncoming :
      Finset.sum R (fun v ↦ incoming_flow head x v) =
        Finset.sum (Finset.univ.filter fun e ↦ head e ∈ S) x := by
    -- Reindex the incoming vertex sum as a sum over the head fibers of the cut-side support.
    calc
      Finset.sum R (fun v ↦ incoming_flow head x v) =
          Finset.sum R (fun v ↦ Finset.sum (Finset.univ.filter fun e ↦ head e = v) x) := by
            simp [incoming_flow]
      _ = Finset.sum (Finset.univ.filter fun e ↦ head e ∈ R) x := by
            simpa using
              (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset A) R head x)
      _ = Finset.sum (Finset.univ.filter fun e ↦ head e ∈ S) x := by
            refine Finset.sum_congr ?_ ?_
            · ext e
              have hhead_mem : head e ∈ R ↔ head e ∈ S := by
                have hhead_inc : head e ∈ circuit_vertices tail head Finset.univ := by
                  exact Finset.mem_union.mpr <|
                    Or.inr <| Finset.mem_image.mpr ⟨e, by simp, rfl⟩
                simpa [R] using
                  (mem_cut_side_vertices_iff_of_incident (tail := tail) (head := head)
                    (s := s) (t := t) (S := S) hS hhead_inc)
              simp [hhead_mem]
            · intro e he
              rfl
  have hOutgoing :
      Finset.sum R (fun v ↦ outgoing_flow tail x v) =
        Finset.sum (Finset.univ.filter fun e ↦ tail e ∈ S) x := by
    -- Reindex the outgoing vertex sum as a sum over the tail fibers of the cut-side support.
    calc
      Finset.sum R (fun v ↦ outgoing_flow tail x v) =
          Finset.sum R (fun v ↦ Finset.sum (Finset.univ.filter fun e ↦ tail e = v) x) := by
            simp [outgoing_flow]
      _ = Finset.sum (Finset.univ.filter fun e ↦ tail e ∈ R) x := by
            simpa using
              (Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset A) R tail x)
      _ = Finset.sum (Finset.univ.filter fun e ↦ tail e ∈ S) x := by
            refine Finset.sum_congr ?_ ?_
            · ext e
              have htail_mem : tail e ∈ R ↔ tail e ∈ S := by
                have htail_inc : tail e ∈ circuit_vertices tail head Finset.univ := by
                  exact Finset.mem_union.mpr <|
                    Or.inl <| Finset.mem_image.mpr ⟨e, by simp, rfl⟩
                simpa [R] using
                  (mem_cut_side_vertices_iff_of_incident (tail := tail) (head := head)
                    (s := s) (t := t) (S := S) hS htail_inc)
              simp [htail_mem]
            · intro e he
              rfl
  have hIncoming_split :
      Finset.sum (Finset.univ.filter fun e ↦ head e ∈ S) x =
        Finset.sum internal x + Finset.sum (δ⁻[tail, head] S) x := by
    -- Split the arcs entering `S` into internal arcs and arcs that cross the cut into `S`.
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun e ↦ head e ∈ S)
      (p := fun e ↦ tail e ∈ S) (f := x)]
    simp [internal, incoming_cut_arcs, Finset.filter_filter, and_comm]
  have hOutgoing_split :
      Finset.sum (Finset.univ.filter fun e ↦ tail e ∈ S) x =
        Finset.sum internal x + Finset.sum (δ⁺[tail, head] S) x := by
    -- Split the arcs leaving vertices in `S` into internal arcs and arcs that cross the cut out.
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun e ↦ tail e ∈ S)
      (p := fun e ↦ head e ∈ S) (f := x)]
    simp [internal, outgoing_cut_arcs, Finset.filter_filter]
  have hcut :
      Finset.sum R (fun v ↦ incoming_flow head x v) -
          Finset.sum R (fun v ↦ outgoing_flow tail x v) =
        Finset.sum (δ⁻[tail, head] S) x - Finset.sum (δ⁺[tail, head] S) x := by
    -- The internal arc contributions cancel, leaving only the cut-crossing terms.
    rw [hIncoming, hOutgoing, hIncoming_split, hOutgoing_split]
    ring
  -- Compare the cut-balance formula with the source-balance formula.
  linarith [hbalance, hcut]

/-- Helper for Lemma 4.14: the gap between the cut capacity and the flow value is the sum of the
unused forward capacity and the backward flow entering the cut side. -/
private lemma cut_capacity_sub_st_flow_value_eq_cut_slack_sum
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) (hS : IsSTCutSide s t S) :
    cut_capacity tail head c S - st_flow_value tail head s x =
      Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) +
        Finset.sum (δ⁻[tail, head] S) x := by
  -- Rewrite the flow value by the cut-flow identity and regroup the resulting sums.
  calc
    cut_capacity tail head c S - st_flow_value tail head s x =
        Finset.sum (δ⁺[tail, head] S) c -
          (Finset.sum (δ⁺[tail, head] S) x - Finset.sum (δ⁻[tail, head] S) x) := by
          rw [cut_capacity,
            st_flow_value_eq_outgoing_cut_flow_sub_incoming_cut_flow tail head x s t S
              hx.toIsSTFlow hS]
    _ = (Finset.sum (δ⁺[tail, head] S) c - Finset.sum (δ⁺[tail, head] S) x) +
          Finset.sum (δ⁻[tail, head] S) x := by
          ring
    _ = Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) +
          Finset.sum (δ⁻[tail, head] S) x := by
          rw [Finset.sum_sub_distrib]

/-- Helper for Lemma 4.14: the nonnegative cut-slack sum vanishes exactly when every outgoing cut
arc is saturated and every incoming cut arc carries zero flow. -/
private lemma nonnegative_cut_slack_vanishes_iff
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) :
    Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) +
        Finset.sum (δ⁻[tail, head] S) x = 0 ↔
      (∀ e ∈ δ⁺[tail, head] S, x e = c e) ∧
        ∀ e ∈ δ⁻[tail, head] S, x e = 0 := by
  constructor
  · intro hslack
    have hOutNonneg :
        0 ≤ Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) := by
      exact Finset.sum_nonneg fun e he ↦ sub_nonneg.mpr (hx.le_capacity e)
    have hInNonneg :
        0 ≤ Finset.sum (δ⁻[tail, head] S) x := by
      exact Finset.sum_nonneg fun e he ↦ hx.nonneg e
    have hOutZero : Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) = 0 := by
      linarith
    have hInZero : Finset.sum (δ⁻[tail, head] S) x = 0 := by
      linarith
    constructor
    · intro e he
      have hTermZero :
          c e - x e = 0 := by
        have hzero_on_cut :
            ∀ a ∈ δ⁺[tail, head] S, c a - x a = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun a _ ↦ sub_nonneg.mpr (hx.le_capacity a))).1 hOutZero
        exact hzero_on_cut e he
      linarith
    · intro e he
      have hzero_on_cut :
          ∀ a ∈ δ⁻[tail, head] S, x a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun a _ ↦ hx.nonneg a)).1 hInZero
      exact hzero_on_cut e he
  · rintro ⟨hOut, hIn⟩
    -- Each slack term vanishes pointwise under the saturation and zero-flow hypotheses.
    have hOutZero : Finset.sum (δ⁺[tail, head] S) (fun e ↦ c e - x e) = 0 := by
      refine Finset.sum_eq_zero fun e he ↦ ?_
      rw [hOut e he]
      ring
    have hInZero : Finset.sum (δ⁻[tail, head] S) x = 0 := by
      refine Finset.sum_eq_zero fun e he ↦ ?_
      exact hIn e he
    simp [hOutZero, hInZero]

/-- Lemma 4.14 (1). Every feasible `s,t`-flow has value at most the capacity of any `s,t`-cut
side. -/
theorem flow_value_le_cut_capacity
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) (hS : IsSTCutSide s t S) :
    st_flow_value tail head s x ≤ cut_capacity tail head c S := by
  -- Express the cut-capacity gap as a sum of nonnegative slack terms.
  have hgap_nonneg : 0 ≤ cut_capacity tail head c S - st_flow_value tail head s x := by
    rw [cut_capacity_sub_st_flow_value_eq_cut_slack_sum tail head c x s t S hx hS]
    refine add_nonneg ?_ ?_
    · exact Finset.sum_nonneg fun e he ↦ sub_nonneg.mpr (hx.le_capacity e)
    · exact Finset.sum_nonneg fun e he ↦ hx.nonneg e
  exact sub_nonneg.mp hgap_nonneg

/-- Lemma 4.14 (2). Equality between the flow value and the cut capacity holds exactly when every
arc in `δ⁺(S)` is saturated and every arc in `δ⁻(S)` carries zero flow. -/
theorem flow_value_eq_cut_capacity_iff
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) (hS : IsSTCutSide s t S) :
    st_flow_value tail head s x = cut_capacity tail head c S ↔
      (∀ e ∈ δ⁺[tail, head] S, x e = c e) ∧
        ∀ e ∈ δ⁻[tail, head] S, x e = 0 := by
  constructor
  · intro heq
    -- Equality of value and cut capacity is equivalent to vanishing total cut slack.
    have hgap_zero : cut_capacity tail head c S - st_flow_value tail head s x = 0 := by
      linarith
    rw [cut_capacity_sub_st_flow_value_eq_cut_slack_sum tail head c x s t S hx hS] at hgap_zero
    exact (nonnegative_cut_slack_vanishes_iff tail head c x s t S hx).1 hgap_zero
  · intro hcut
    -- Vanishing slack collapses the cut-capacity gap to zero.
    have hgap_zero :
        cut_capacity tail head c S - st_flow_value tail head s x = 0 := by
      rw [cut_capacity_sub_st_flow_value_eq_cut_slack_sum tail head c x s t S hx hS]
      exact (nonnegative_cut_slack_vanishes_iff tail head c x s t S hx).2 hcut
    exact (sub_eq_zero.mp hgap_zero).symm

/-- Lemma 4.14 (3). If a feasible `s,t`-flow attains the capacity of an `s,t`-cut side, then it
is a maximum `s,t`-flow. -/
theorem flow_cut_eq_implies_isMaximumSTFlow
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) (hS : IsSTCutSide s t S)
    (heq : st_flow_value tail head s x = cut_capacity tail head c S) :
    IsMaximumSTFlow tail head s t c x := by
  refine
    { toIsFeasibleSTFlow := hx
      le_st_flow_value := ?_ }
  intro y hy
  calc
    st_flow_value tail head s y ≤ cut_capacity tail head c S :=
      flow_value_le_cut_capacity tail head c y s t S hy hS
    _ = st_flow_value tail head s x := by rw [← heq]

/-- Lemma 4.14 (4). If a feasible `s,t`-flow attains the capacity of an `s,t`-cut side, then that
cut side has minimum capacity among all `s,t`-cut sides. -/
theorem flow_cut_eq_implies_isMinimumSTCut
    (tail head : A → V) (c x : A → ℝ) (s t : V) (S : Set V)
    (hx : IsFeasibleSTFlow tail head s t c x) (hS : IsSTCutSide s t S)
    (heq : st_flow_value tail head s x = cut_capacity tail head c S) :
    IsMinimumSTCut tail head c s t S := by
  refine
    ⟨hS, ?_⟩
  intro T hT
  calc
    cut_capacity tail head c S = st_flow_value tail head s x := by rw [heq]
    _ ≤ cut_capacity tail head c T :=
      flow_value_le_cut_capacity tail head c x s t T hx hT

end MaxFlowMinCut

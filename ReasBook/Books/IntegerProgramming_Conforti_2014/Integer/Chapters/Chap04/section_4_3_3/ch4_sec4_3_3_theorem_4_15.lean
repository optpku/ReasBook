/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3.ch4_sec4_3_definition_4_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_lemma_4_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_theorem_4_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7

open scoped BigOperators Matrix

section MaxFlowMinCut

variable {V A : Type} [Fintype A]

/-- Helper for Theorem 4.15: the cut extraction argument follows the textbook zero-`z` reachability
relation on arcs whose integral dual slack vanishes. -/
private def zero_dual_arc_step (tail head : A → V) (z : A → ℤ) : V → V → Prop :=
  fun u v ↦ ∃ e, tail e = u ∧ head e = v ∧ z e = 0

omit [Fintype A] in
/-- Helper for Theorem 4.15: along a zero-`z` reachability chain, the integral dual potential is
monotone nondecreasing. -/
private lemma potential_mono_along_zero_dual_arc_reachability
    (tail head : A → V) (y : V → ℤ) (z : A → ℤ)
    (hyz : ∀ e, y (tail e) - y (head e) ≤ z e) :
    ∀ {u v}, Relation.ReflTransGen (zero_dual_arc_step tail head z) u v → y u ≤ y v := by
  intro u v huv
  -- Induct on the reachability chain so that each zero-`z` step contributes one monotonicity
  -- inequality, then compose them transitively.
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact le_rfl
  | @head a c hab hcv ih =>
      rcases hab with ⟨e, htail, hhead, hze⟩
      have hstep : y a ≤ y c := by
        have hle : y a - y c ≤ 0 := by
          simpa [htail, hhead, hze] using hyz e
        exact sub_nonpos.mp hle
      exact le_trans hstep ih

/-- Helper for Theorem 4.15: an integral dual certificate produces the textbook cut side of
vertices reachable from `s` by zero-`z` arcs, and every outgoing cut arc has positive integral
slack. -/
private lemma integral_dual_certificate_produces_cut
    (tail head : A → V) (s t : V) (y : V → ℤ) (z : A → ℤ)
    (hys : y s = 1) (hyt : y t = 0)
    (hz_nonneg : ∀ e, 0 ≤ z e)
    (hyz : ∀ e, y (tail e) - y (head e) ≤ z e) :
    let S : Set V := {v | Relation.ReflTransGen (zero_dual_arc_step tail head z) s v}
    IsSTCutSide s t S ∧ ∀ e ∈ δ⁺[tail, head] S, 1 ≤ z e := by
  classical
  let S : Set V := {v | Relation.ReflTransGen (zero_dual_arc_step tail head z) s v}
  have hs_mem : s ∈ S := by
    -- The zero-length path keeps the source on the reachable side.
    exact Relation.ReflTransGen.refl
  have ht_not_mem : t ∉ S := by
    intro ht_mem
    have hst_le : y s ≤ y t :=
      potential_mono_along_zero_dual_arc_reachability tail head y z hyz ht_mem
    have hnot : ¬ ((1 : ℤ) ≤ 0) := by
      decide
    rw [hys, hyt] at hst_le
    exact hnot hst_le
  have hcut_arc :
      ∀ e ∈ δ⁺[tail, head] S, 1 ≤ z e := by
    intro e he
    rcases mem_outgoing_cut_arcs_iff.mp he with ⟨htail_mem, hhead_not_mem⟩
    have hz_ne_zero : z e ≠ 0 := by
      intro hze
      have hhead_mem : head e ∈ S := by
        -- Appending one zero-`z` arc would keep the head reachable, contradicting the cut exit.
        exact htail_mem.tail ⟨e, rfl, rfl, hze⟩
      exact hhead_not_mem hhead_mem
    have hz_pos : 0 < z e := by
      exact lt_of_le_of_ne (hz_nonneg e) (by simpa using hz_ne_zero.symm)
    simpa using Int.add_one_le_iff.mpr hz_pos
  exact ⟨⟨hs_mem, ht_not_mem⟩, hcut_arc⟩

/-- Helper for Theorem 4.15: once every outgoing cut arc carries positive integral slack, the cut
capacity is bounded above by the dual objective `∑ c_e z_e`. -/
private lemma cut_capacity_le_dual_objective_of_integral_certificate
    (tail head : A → V) (c : A → ℝ) (S : Set V) (z : A → ℤ)
    (hcap : ∀ e, 0 ≤ c e)
    (hz_nonneg : ∀ e, 0 ≤ z e)
    (hcutpos : ∀ e ∈ δ⁺[tail, head] S, 1 ≤ z e) :
    cut_capacity tail head c S ≤ ∑ e, c e * (z e : ℝ) := by
  classical
  -- First compare termwise on the cut itself using `1 ≤ z e`, then enlarge from the cut arc set
  -- to the whole arc set using nonnegativity of every summand.
  calc
    cut_capacity tail head c S = (δ⁺[tail, head] S).sum c := rfl
    _ ≤ (δ⁺[tail, head] S).sum fun e ↦ c e * (z e : ℝ) := by
          refine Finset.sum_le_sum fun e he ↦ ?_
          have hz_one : (1 : ℝ) ≤ (z e : ℝ) := by
            exact_mod_cast hcutpos e he
          calc
            c e = c e * 1 := by ring
            _ ≤ c e * (z e : ℝ) := mul_le_mul_of_nonneg_left hz_one (hcap e)
    _ ≤ ∑ e, c e * (z e : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (by intro e he; simp) ?_
          intro e _ he_not_mem
          exact mul_nonneg (hcap e) (by exact_mod_cast hz_nonneg e)

/-- Helper for Theorem 4.15: multiplying the digraph incidence matrix by an arc vector records
incoming minus outgoing flow at each vertex. -/
private theorem digraph_incidence_matrix_mulVec_apply
    (tail head : A → V) (x : A → ℝ) (v : V) :
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v =
      incoming_flow head x v - outgoing_flow tail x v := by
  classical
  have hhead_sum :
      ∑ e, (if v = head e then x e else 0) = incoming_flow head x v := by
    -- The head-indicator part keeps exactly the arcs entering `v`.
    rw [incoming_flow_eq_sum_incoming_arcs]
    rw [incoming_arcs, Finset.sum_filter]
    simp [eq_comm]
  have htail_sum :
      ∑ e, (if v = tail e then x e else 0) = outgoing_flow tail x v := by
    -- The tail-indicator part keeps exactly the arcs leaving `v`.
    rw [outgoing_flow_eq_sum_outgoing_arcs]
    rw [outgoing_arcs, Finset.sum_filter]
    simp [eq_comm]
  -- Split the incidence entry into its head and tail parts, then rewrite each sum separately.
  calc
    (digraph_incidence_matrix ℝ tail head *ᵥ x) v
        = ∑ e, (((if v = head e then (1 : ℝ) else 0) -
            (if v = tail e then 1 else 0)) * x e) := by
            simp [Matrix.mulVec, dotProduct, digraph_incidence_matrix]
    _ = ∑ e, ((if v = head e then x e else 0) -
          (if v = tail e then x e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            by_cases hhead : v = head e
            · by_cases htail : v = tail e
              · have hend : head e = tail e := hhead.symm.trans htail
                simp [hhead, hend]
              · have hend : head e ≠ tail e := fun hend ↦ htail (hhead.trans hend)
                simp [hhead, hend]
            · by_cases htail : v = tail e
              · have hend : tail e ≠ head e := fun hend ↦ hhead (htail.trans hend)
                simp [htail, hend]
              · simp [hhead, htail]
    _ = (∑ e, (if v = head e then x e else 0)) -
          ∑ e, (if v = tail e then x e else 0) := by
            rw [Finset.sum_sub_distrib]
    _ = incoming_flow head x v - outgoing_flow tail x v := by
          rw [hhead_sum, htail_sum]

/-- Helper for Theorem 4.15: before adding the extra value arc, the incidence rows of a feasible
`s,t`-flow already have the textbook source/sink imbalance pattern. -/
private lemma incidence_row_balance_of_feasible_st_flow
    [DecidableEq V]
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x) :
    ∀ v,
      (digraph_incidence_matrix ℝ tail head *ᵥ x) v =
        if v = s then - st_flow_value tail head s x
        else if v = t then st_flow_value tail head s x
        else 0 := by
  intro v
  by_cases hvs : v = s
  · subst hvs
    -- The source row is the negative of the net flow leaving `s`.
    rw [digraph_incidence_matrix_mulVec_apply]
    simp [st_flow_value]
  · by_cases hvt : v = t
    · subst hvt
      -- The sink row is the flow value itself, via the source/sink balance identity.
      rw [digraph_incidence_matrix_mulVec_apply]
      simpa [hvs] using (st_flow_value_eq_sink_balance hx.toIsSTFlow).symm
    · -- Every other row vanishes by flow conservation away from `s` and `t`.
      rw [digraph_incidence_matrix_mulVec_apply]
      have hcons : incoming_flow head x v = outgoing_flow tail x v :=
        hx.toIsSTFlow.conservation v hvs hvt
      simpa [hvs, hvt] using (sub_eq_zero.mpr hcons)

/-- Helper for Theorem 4.15: the augmented max-flow LP adds one extra arc from `t` to `s`. -/
private def value_augmented_tail (tail : A → V) (t : V) : A ⊕ Unit → V :=
  Sum.elim tail (fun _ ↦ t)

/-- Helper for Theorem 4.15: the extra value arc of the augmented max-flow LP enters `s`. -/
private def value_augmented_head (head : A → V) (s : V) : A ⊕ Unit → V :=
  Sum.elim head (fun _ ↦ s)

/-- Helper for Theorem 4.15: the augmented arc vector keeps the original arc values and stores the
flow value on the extra `t → s` arc. -/
private def value_augmented_vector (x : A → ℝ) (v : ℝ) : A ⊕ Unit → ℝ :=
  Sum.elim x (fun _ ↦ v)

/-- Helper for Theorem 4.15: adding the extra `t → s` value arc changes each incidence row by
`+v` at `s` and `-v` at `t`, exactly as in the source LP proof. -/
private lemma value_augmented_row_balance
    [DecidableEq V]
    (tail head : A → V) (s t : V) (x : A → ℝ) (v : ℝ) (w : V) :
    (digraph_incidence_matrix ℝ (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
        value_augmented_vector x v) w =
      (digraph_incidence_matrix ℝ tail head *ᵥ x) w +
        (if w = s then v else 0) -
        (if w = t then v else 0) := by
  classical
  -- Rewrite both incidence products as incoming minus outgoing flow so the extra arc contributes
  -- exactly one incoming term at `s` and one outgoing term at `t`.
  rw [digraph_incidence_matrix_mulVec_apply
      (tail := value_augmented_tail tail t) (head := value_augmented_head head s)
      (x := value_augmented_vector x v) (v := w)]
  rw [digraph_incidence_matrix_mulVec_apply (tail := tail) (head := head) (x := x) (v := w)]
  have hin :
      incoming_flow (value_augmented_head head s) (value_augmented_vector x v) w =
        incoming_flow head x w + if w = s then v else 0 := by
    -- Split the sum over `A ⊕ Unit` into the original arcs and the single extra value arc.
    unfold incoming_flow
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type]
    simp [value_augmented_head, value_augmented_vector, eq_comm, add_comm]
  have hout :
      outgoing_flow (value_augmented_tail tail t) (value_augmented_vector x v) w =
        outgoing_flow tail x w + if w = t then v else 0 := by
    -- The same split shows that only the extra arc contributes the additional outgoing term at
    -- the sink-side endpoint `t`.
    unfold outgoing_flow
    rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type]
    simp [value_augmented_tail, value_augmented_vector, eq_comm, add_comm]
  calc
    incoming_flow (value_augmented_head head s) (value_augmented_vector x v) w -
        outgoing_flow (value_augmented_tail tail t) (value_augmented_vector x v) w
      = (incoming_flow head x w + if w = s then v else 0) -
          (outgoing_flow tail x w + if w = t then v else 0) := by rw [hin, hout]
    _ = (incoming_flow head x w - outgoing_flow tail x w) +
          (if w = s then v else 0) -
          (if w = t then v else 0) := by ring

/-- Helper for Theorem 4.15: once the extra `t → s` value arc is given the flow value, every
incidence row becomes zero, which is the source-faithful augmented primal balance equation. -/
private lemma value_augmented_zero_balance_of_feasible_st_flow
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x) :
    ∀ w,
      (digraph_incidence_matrix ℝ (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
          value_augmented_vector x (st_flow_value tail head s x)) w = 0 := by
  intro w
  classical
  -- Route correction: instead of pushing directly into the reindexed LP, first cancel the raw
  -- source/sink imbalance by the extra value arc on the original vertex owner.
  rw [value_augmented_row_balance tail head s t x (st_flow_value tail head s x) w]
  rw [incidence_row_balance_of_feasible_st_flow tail head c s t x hst hx w]
  by_cases hws : w = s
  · subst hws
    simp [hst]
  · by_cases hwt : w = t
    · subst hwt
      simp [hws]
    · simp [hws, hwt]

/-- Helper for Theorem 4.15: the finite vertex owner for the raw augmented LP is the source, the
sink, and every endpoint of an original arc. -/
private noncomputable abbrev relevant_value_augmented_vertices
    (tail head : A → V) (s t : V) : Finset V :=
  let _ : DecidableEq V := Classical.decEq V
  insert s (insert t (circuit_vertices tail head Finset.univ))

/-- Helper for Theorem 4.15: the raw augmented LP keeps its balance rows only on the finite
relevant vertex owner. -/
private abbrev RelevantValueAugmentedVertex
    (tail head : A → V) (s t : V) :=
  {v // v ∈ relevant_value_augmented_vertices tail head s t}

/-- Helper for Theorem 4.15: summing the source-indicator over the relevant augmented-vertex
owner collapses to the source term itself. -/
private lemma source_indicator_sum_over_relevant_vertices
    [DecidableEq V]
    (tail head : A → V) (s t : V) (g : V → ℝ) :
    ∑ v : RelevantValueAugmentedVertex tail head s t, (if v.1 = s then (1 : ℝ) else 0) * g v.1 =
      g s := by
  classical
  -- Rewrite the subtype sum as a sum over the attached relevant-vertex finset, then isolate the
  -- inserted source vertex and kill every remaining indicator term.
  change
    Finset.sum (relevant_value_augmented_vertices tail head s t).attach
      (fun v ↦ (if v.1 = s then (1 : ℝ) else 0) * g v.1) = g s
  have hattach :
      Finset.sum (relevant_value_augmented_vertices tail head s t).attach
          (fun v ↦ (if v.1 = s then (1 : ℝ) else 0) * g v.1) =
        Finset.sum (relevant_value_augmented_vertices tail head s t)
          (fun v ↦ (if v = s then (1 : ℝ) else 0) * g v) := by
    simpa using
      (Finset.sum_attach
        (s := relevant_value_augmented_vertices tail head s t)
        (f := fun v : V ↦ (if v = s then (1 : ℝ) else 0) * g v))
  rw [hattach]
  rw [Finset.sum_eq_single s]
  · simp
  · intro v hv hvs
    simp [hvs]
  · intro hs_not_mem
    exact (hs_not_mem (by simp [relevant_value_augmented_vertices])).elim

/-- Helper for Theorem 4.15: summing any vertex-indicator over the relevant augmented-vertex
owner collapses to that single relevant vertex term. -/
private lemma indicator_sum_over_relevant_vertices
    [DecidableEq V]
    (tail head : A → V) (s t w : V) (g : V → ℝ)
    (hw : w ∈ relevant_value_augmented_vertices tail head s t) :
    ∑ v : RelevantValueAugmentedVertex tail head s t, (if v.1 = w then (1 : ℝ) else 0) * g v.1 =
      g w := by
  classical
  -- Rewrite the subtype sum as a sum over the attached relevant-vertex finset, then isolate the
  -- single relevant vertex `w`.
  change
    Finset.sum (relevant_value_augmented_vertices tail head s t).attach
      (fun v ↦ (if v.1 = w then (1 : ℝ) else 0) * g v.1) = g w
  have hattach :
      Finset.sum (relevant_value_augmented_vertices tail head s t).attach
          (fun v ↦ (if v.1 = w then (1 : ℝ) else 0) * g v.1) =
        Finset.sum (relevant_value_augmented_vertices tail head s t)
          (fun v ↦ (if v = w then (1 : ℝ) else 0) * g v) := by
    simpa using
      (Finset.sum_attach
        (s := relevant_value_augmented_vertices tail head s t)
        (f := fun v : V ↦ (if v = w then (1 : ℝ) else 0) * g v))
  rw [hattach]
  rw [Finset.sum_eq_single w]
  · simp
  · intro v hv hvw
    simp [hvw]
  · intro hw_not_mem
    exact (hw_not_mem hw).elim

/-- Helper for Theorem 4.15: the unreindexed augmented primal LP has two balance blocks and the
usual capacity/nonnegativity blocks. -/
private abbrev RawValueAugmentedPrimalRow
    (tail head : A → V) (s t : V) :=
  (RelevantValueAugmentedVertex tail head s t ⊕ RelevantValueAugmentedVertex tail head s t) ⊕
    (A ⊕ A)

/-- Helper for Theorem 4.15: the raw augmented primal matrix on the original owners uses the
augmented incidence rows, then the capacity and nonnegativity rows. -/
private noncomputable def raw_value_augmented_primal_matrix
    (tail head : A → V) (s t : V) :
    Matrix (RawValueAugmentedPrimalRow tail head s t) (A ⊕ Unit) ℝ :=
  let _ : DecidableEq A := Classical.decEq A
  fun i j ↦
    match i with
    | Sum.inl (Sum.inl v) =>
        digraph_incidence_matrix ℝ (value_augmented_tail tail t) (value_augmented_head head s) v.1 j
    | Sum.inl (Sum.inr v) =>
        -digraph_incidence_matrix ℝ
          (value_augmented_tail tail t) (value_augmented_head head s) v.1 j
    | Sum.inr (Sum.inl a) =>
        match j with
        | Sum.inl e => if a = e then 1 else 0
        | Sum.inr _ => 0
    | Sum.inr (Sum.inr a) =>
        match j with
        | Sum.inl e => if a = e then -1 else 0
        | Sum.inr _ => 0

/-- Helper for Theorem 4.15: the raw augmented primal right-hand side is zero on both balance
blocks, equals `c` on the capacity block, and is zero on the nonnegativity block. -/
private noncomputable def raw_value_augmented_primal_rhs
    (tail head : A → V) (c : A → ℝ) (s t : V) :
    RawValueAugmentedPrimalRow tail head s t → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl a) => c a
  | Sum.inr (Sum.inr _) => 0

/-- Helper for Theorem 4.15: this is the single canonical `Fin` row owner used for the augmented
max-flow LP transport. -/
private noncomputable abbrev value_augmented_primal_row_equiv
    (tail head : A → V) (s t : V) :
    RawValueAugmentedPrimalRow tail head s t ≃
      Fin (Fintype.card (RawValueAugmentedPrimalRow tail head s t)) :=
  Fintype.equivFin (RawValueAugmentedPrimalRow tail head s t)

/-- Helper for Theorem 4.15: this is the single canonical `Fin` column owner used for the
augmented max-flow LP transport. -/
private noncomputable abbrev value_augmented_primal_col_equiv
    (A : Type) [Fintype A] :
    A ⊕ Unit ≃ Fin (Fintype.card (A ⊕ Unit)) :=
  Fintype.equivFin (A ⊕ Unit)

/-- Helper for Theorem 4.15: the textbook augmented primal matrix transported once to canonical
`Fin` owners. -/
private noncomputable abbrev value_augmented_primal_matrix_fin
    (tail head : A → V) (s t : V) :
    Matrix (Fin (Fintype.card (RawValueAugmentedPrimalRow tail head s t)))
      (Fin (Fintype.card (A ⊕ Unit))) ℝ :=
  Matrix.reindex
    (value_augmented_primal_row_equiv tail head s t)
    (value_augmented_primal_col_equiv (A := A))
    (raw_value_augmented_primal_matrix tail head s t)

/-- Helper for Theorem 4.15: the transported right-hand side is just the raw right-hand side
composed with the inverse row equivalence. -/
private noncomputable abbrev value_augmented_primal_rhs_fin
    (tail head : A → V) (c : A → ℝ) (s t : V) :
    Fin (Fintype.card (RawValueAugmentedPrimalRow tail head s t)) → ℝ :=
  raw_value_augmented_primal_rhs tail head c s t ∘
    (value_augmented_primal_row_equiv tail head s t).symm

/-- Helper for Theorem 4.15: the transported primal point keeps the original arc values and the
extra value coordinate after moving to the canonical `Fin` column owner. -/
private noncomputable abbrev value_augmented_primal_point_fin
    (x : A → ℝ) (v : ℝ) :
    Fin (Fintype.card (A ⊕ Unit)) → ℝ :=
  value_augmented_vector x v ∘ (value_augmented_primal_col_equiv (A := A)).symm

/-- Helper for Theorem 4.15: the primal objective on the transported owner is exactly the
indicator of the extra `Unit` column. -/
private noncomputable abbrev value_augmented_primal_objective_fin
    (A : Type) [Fintype A] :
    Fin (Fintype.card (A ⊕ Unit)) → ℝ :=
  let _ : DecidableEq (A ⊕ Unit) := Classical.decEq (A ⊕ Unit)
  fun j ↦
    if (value_augmented_primal_col_equiv (A := A)).symm j = Sum.inr () then (1 : ℝ) else 0

/-- Helper for Theorem 4.15: reindexing a finite matrix to canonical `Fin` owners commutes with
matrix-vector multiplication after composing the vector with the column equivalence. -/
private theorem reindexed_mulVec_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ)
    (eα : α ≃ Fin (Fintype.card α))
    (eβ : β ≃ Fin (Fintype.card β))
    (x : Fin (Fintype.card β) → ℝ) :
    Matrix.reindex eα eβ M *ᵥ x =
      fun i ↦ (M *ᵥ ((LinearEquiv.funCongrLeft ℝ ℝ eβ) x)) (eα.symm i) := by
  have hlin :=
    congrArg
      (fun T :
          (Fin (Fintype.card β) → ℝ) →ₗ[ℝ]
            Fin (Fintype.card α) → ℝ ↦
        T x)
      (Matrix.mulVecLin_reindex (R := ℝ) eα eβ M)
  -- Evaluate the canonical reindexing linear equivalence at the chosen vector.
  simpa using hlin

/-- Helper for Theorem 4.15: reindexing a finite matrix to canonical `Fin` owners also commutes
with row-vector multiplication after composing the row vector with the row equivalence. -/
private theorem reindexed_vecMul_apply
    {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α β ℝ)
    (eα : α ≃ Fin (Fintype.card α))
    (eβ : β ≃ Fin (Fintype.card β))
    (u : Fin (Fintype.card α) → ℝ) :
    u ᵥ* Matrix.reindex eα eβ M =
      fun j ↦ ((u ∘ eα) ᵥ* M) (eβ.symm j) := by
  -- Unfold the reindexing as a submatrix and then transport the row-vector product through the
  -- row and column equivalences in one step.
  ext j
  simpa [Matrix.reindex] using
    congrFun (Matrix.submatrix_vecMul_equiv M u eα.symm eβ.symm) j

/-- Helper for Theorem 4.15: a feasible `s,t`-flow gives a raw feasible augmented LP point before
the single finite reindexing step. -/
private lemma value_augmented_vector_mem_raw_primal_of_feasible_st_flow
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x) :
    raw_value_augmented_primal_matrix tail head s t *ᵥ
        value_augmented_vector x (st_flow_value tail head s x) ≤
      raw_value_augmented_primal_rhs tail head c s t := by
  classical
  have hbalance :
      ∀ v,
        (digraph_incidence_matrix ℝ (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
            value_augmented_vector x (st_flow_value tail head s x)) v = 0 :=
    value_augmented_zero_balance_of_feasible_st_flow tail head c s t x hst hx
  intro i
  rcases i with (i | i)
  · rcases i with (i | i)
    · -- The first balance block is exactly the augmented zero-balance equation on `R`.
      have hrow_nonpos :
          (digraph_incidence_matrix ℝ (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
              value_augmented_vector x (st_flow_value tail head s x)) i.1 ≤ 0 := by
        rw [hbalance i.1]
      simpa [raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
        Matrix.mulVec, dotProduct] using hrow_nonpos
    · -- The second balance block stores the negated balance equation, so the same zero row gives
      -- the required `≤ 0` inequality.
      have hrow_nonpos :
          -((digraph_incidence_matrix ℝ
                (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
              value_augmented_vector x (st_flow_value tail head s x)) i.1) ≤ 0 := by
        rw [hbalance i.1]
        simp
      simpa [raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
        Matrix.mulVec, dotProduct] using hrow_nonpos
  · rcases i with (i | i)
    · -- The capacity block reads off the original arc coordinate and compares it to `c`.
      simpa [raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
        Matrix.mulVec, dotProduct] using hx.le_capacity i
    · -- The nonnegativity block is `-x_e ≤ 0`, which is equivalent to `0 ≤ x_e`.
      simpa [raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
        Matrix.mulVec, dotProduct] using neg_nonpos.mpr (hx.toIsSTFlow.nonneg i)

/-- Helper for Theorem 4.15: the source-faithful augmented primal point remains feasible after the
single transport to the canonical `Fin` owner. -/
private lemma value_augmented_primal_fin_mem_of_feasible_st_flow
    (tail head : A → V) (c : A → ℝ) (s t : V) (x : A → ℝ)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x) :
    value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x) ∈
      primal_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_rhs_fin tail head c s t) := by
  rw [mem_primal_feasible_region_iff]
  have hraw :
      raw_value_augmented_primal_matrix tail head s t *ᵥ
          value_augmented_vector x (st_flow_value tail head s x) ≤
        raw_value_augmented_primal_rhs tail head c s t :=
    value_augmented_vector_mem_raw_primal_of_feasible_st_flow tail head c s t x hst hx
  intro i
  have hmul :
      (value_augmented_primal_matrix_fin tail head s t *ᵥ
          value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x)) i =
        (raw_value_augmented_primal_matrix tail head s t *ᵥ
          value_augmented_vector x (st_flow_value tail head s x))
          ((value_augmented_primal_row_equiv tail head s t).symm i) := by
    have htransport :
        (LinearEquiv.funCongrLeft ℝ ℝ (value_augmented_primal_col_equiv (A := A)))
            (value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x)) =
          value_augmented_vector x (st_flow_value tail head s x) := by
      -- Cancelling the column equivalence recovers the raw augmented vector.
      funext j
      simp [value_augmented_primal_point_fin, value_augmented_primal_col_equiv]
    calc
      (value_augmented_primal_matrix_fin tail head s t *ᵥ
          value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x)) i =
        (raw_value_augmented_primal_matrix tail head s t *ᵥ
          ((LinearEquiv.funCongrLeft ℝ ℝ (value_augmented_primal_col_equiv (A := A)))
            (value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x))))
          ((value_augmented_primal_row_equiv tail head s t).symm i) := by
            simpa [value_augmented_primal_matrix_fin, value_augmented_primal_row_equiv] using
              congrFun
                (reindexed_mulVec_apply
                  (raw_value_augmented_primal_matrix tail head s t)
                  (value_augmented_primal_row_equiv tail head s t)
                  (value_augmented_primal_col_equiv (A := A))
                  (value_augmented_primal_point_fin (A := A) x
                    (st_flow_value tail head s x))) i
      _ = (raw_value_augmented_primal_matrix tail head s t *ᵥ
            value_augmented_vector x (st_flow_value tail head s x))
            ((value_augmented_primal_row_equiv tail head s t).symm i) := by
              rw [htransport]
  -- Transport the raw row inequality across the row equivalence.
  rw [hmul]
  simpa [value_augmented_primal_rhs_fin, value_augmented_primal_row_equiv, Function.comp] using
    hraw ((value_augmented_primal_row_equiv tail head s t).symm i)

/-- Helper for Theorem 4.15: on the transported owner, the primal objective still reads the extra
value coordinate, so it equals the flow value. -/
private lemma value_augmented_primal_objective_fin_eq_flow_value
    (tail head : A → V) (s : V) (x : A → ℝ) :
    value_augmented_primal_objective_fin (A := A) ⬝ᵥ
        value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x) =
      st_flow_value tail head s x := by
  classical
  let eCol := value_augmented_primal_col_equiv (A := A)
  let j0 : Fin (Fintype.card (A ⊕ Unit)) := eCol (Sum.inr ())
  have hobjective :
      value_augmented_primal_objective_fin (A := A) =
        fun j : Fin (Fintype.card (A ⊕ Unit)) ↦ if j = j0 then (1 : ℝ) else 0 := by
    funext j
    by_cases hj : j = j0
    · subst hj
      simp [value_augmented_primal_objective_fin, j0, eCol]
    · have hsymm : eCol.symm j ≠ Sum.inr () := by
        intro hsum
        apply hj
        simpa [j0] using congrArg eCol hsum
      calc
        value_augmented_primal_objective_fin (A := A) j = 0 := by
          by_cases htest : (value_augmented_primal_col_equiv (A := A)).symm j = Sum.inr ()
          · exact (hsymm htest).elim
          · simp [value_augmented_primal_objective_fin, htest]
        _ = (if j = j0 then (1 : ℝ) else 0) := by
          simp [hj]
  have hvalue_coord :
      value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x) j0 =
        st_flow_value tail head s x := by
    -- The extra `Unit` column was defined to store the flow value itself.
    simp [value_augmented_primal_point_fin, value_augmented_vector, j0, eCol]
  -- Collapse the objective sum to the single extra `Unit` coordinate.
  rw [hobjective, dotProduct]
  rw [Finset.sum_eq_single j0]
  · simpa [hvalue_coord]
  · intro j _ hj
    simp [hj]
  · intro hj
    exact (hj (Finset.mem_univ j0)).elim

/-- Helper for Theorem 4.15: any feasible point on the transported canonical owner can be moved
back to the raw augmented owner without changing the primal inequalities. -/
private lemma raw_value_augmented_primal_mem_of_fin_mem
    (tail head : A → V) (c : A → ℝ) (s t : V)
    {ξfin : Fin (Fintype.card (A ⊕ Unit)) → ℝ}
    (hξfin :
      ξfin ∈ primal_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_rhs_fin tail head c s t)) :
    raw_value_augmented_primal_matrix tail head s t *ᵥ
        (ξfin ∘ value_augmented_primal_col_equiv (A := A)) ≤
      raw_value_augmented_primal_rhs tail head c s t := by
  rw [mem_primal_feasible_region_iff] at hξfin
  intro i
  have hmul :
      (value_augmented_primal_matrix_fin tail head s t *ᵥ ξfin)
          ((value_augmented_primal_row_equiv tail head s t) i) =
        (raw_value_augmented_primal_matrix tail head s t *ᵥ
          (ξfin ∘ value_augmented_primal_col_equiv (A := A))) i := by
    have htransport :
        (LinearEquiv.funCongrLeft ℝ ℝ (value_augmented_primal_col_equiv (A := A))) ξfin =
          ξfin ∘ value_augmented_primal_col_equiv (A := A) := by
      rfl
    calc
      (value_augmented_primal_matrix_fin tail head s t *ᵥ ξfin)
          ((value_augmented_primal_row_equiv tail head s t) i) =
        (raw_value_augmented_primal_matrix tail head s t *ᵥ
          ((LinearEquiv.funCongrLeft ℝ ℝ (value_augmented_primal_col_equiv (A := A))) ξfin)) i :=
            by
              simpa [value_augmented_primal_matrix_fin, value_augmented_primal_row_equiv] using
                congrFun
                  (reindexed_mulVec_apply
                    (raw_value_augmented_primal_matrix tail head s t)
                    (value_augmented_primal_row_equiv tail head s t)
                    (value_augmented_primal_col_equiv (A := A))
                    ξfin)
                  ((value_augmented_primal_row_equiv tail head s t) i)
      _ = (raw_value_augmented_primal_matrix tail head s t *ᵥ
            (ξfin ∘ value_augmented_primal_col_equiv (A := A))) i := by
              rw [htransport]
  -- Pull the canonical `Fin` inequality back to the raw owner.
  rw [← hmul]
  simpa [value_augmented_primal_rhs_fin, value_augmented_primal_row_equiv, Function.comp] using
    hξfin ((value_augmented_primal_row_equiv tail head s t) i)

/-- Helper for Theorem 4.15: a vertex outside the endpoint support of the digraph has neither
incoming nor outgoing arcs, so every arc vector has zero balance there. -/
private lemma incoming_and_outgoing_flow_eq_zero_of_not_circuit_vertex
    (tail head : A → V) (x : A → ℝ) {v : V}
    (hv : v ∉ circuit_vertices tail head Finset.univ) :
    incoming_flow head x v = 0 ∧ outgoing_flow tail x v = 0 := by
  classical
  have hIncoming : incoming_arcs head v = ∅ := by
    ext e
    constructor
    · intro he
      have hev : head e = v := mem_incoming_arcs_iff.mp he
      have hmem : v ∈ circuit_vertices tail head Finset.univ := by
        exact (mem_circuit_vertices_iff tail head Finset.univ v).2 ⟨e, by simp, Or.inr hev⟩
      exact (hv hmem).elim
    · simp
  have hOutgoing : outgoing_arcs tail v = ∅ := by
    ext e
    constructor
    · intro he
      have hev : tail e = v := mem_outgoing_arcs_iff.mp he
      have hmem : v ∈ circuit_vertices tail head Finset.univ := by
        exact (mem_circuit_vertices_iff tail head Finset.univ v).2 ⟨e, by simp, Or.inl hev⟩
      exact (hv hmem).elim
    · simp
  -- Both fiber sums vanish because the corresponding incoming and outgoing arc sets are empty.
  simp [incoming_flow_eq_sum_incoming_arcs, outgoing_flow_eq_sum_outgoing_arcs,
    hIncoming, hOutgoing]

/-- Helper for Theorem 4.15: a canonical primal feasible point yields a feasible `s,t`-flow, and
its LP objective is exactly the resulting flow value. -/
private lemma feasible_st_flow_of_primal_feasible_point
    (tail head : A → V) (c : A → ℝ) (s t : V)
    (hst : s ≠ t)
    {ξfin : Fin (Fintype.card (A ⊕ Unit)) → ℝ}
    (hξfin :
      ξfin ∈ primal_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_rhs_fin tail head c s t)) :
    ∃ x : A → ℝ,
      IsFeasibleSTFlow tail head s t c x ∧
        st_flow_value tail head s x =
          value_augmented_primal_objective_fin (A := A) ⬝ᵥ ξfin := by
  classical
  let ξraw : A ⊕ Unit → ℝ := ξfin ∘ value_augmented_primal_col_equiv (A := A)
  let x : A → ℝ := fun a ↦ ξraw (Sum.inl a)
  let v0 : ℝ := ξraw (Sum.inr ())
  have hraw :
      raw_value_augmented_primal_matrix tail head s t *ᵥ ξraw ≤
        raw_value_augmented_primal_rhs tail head c s t :=
    raw_value_augmented_primal_mem_of_fin_mem tail head c s t hξfin
  have haug_balance_zero :
      ∀ v : RelevantValueAugmentedVertex tail head s t,
        (digraph_incidence_matrix ℝ
            (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
          value_augmented_vector x v0) v.1 = 0 := by
    intro v
    have hrow_pos :
        (raw_value_augmented_primal_matrix tail head s t *ᵥ ξraw) (Sum.inl (Sum.inl v)) =
          (digraph_incidence_matrix ℝ
              (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
            value_augmented_vector x v0) v.1 := by
      simp [ξraw, x, v0, raw_value_augmented_primal_matrix, Matrix.mulVec, dotProduct,
        value_augmented_vector]
    have hrow_neg :
        (raw_value_augmented_primal_matrix tail head s t *ᵥ ξraw) (Sum.inl (Sum.inr v)) =
          -((digraph_incidence_matrix ℝ
                (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
              value_augmented_vector x v0) v.1) := by
      simp [ξraw, x, v0, raw_value_augmented_primal_matrix, Matrix.mulVec, dotProduct,
        value_augmented_vector]
    have hpos :
        (digraph_incidence_matrix ℝ
            (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
          value_augmented_vector x v0) v.1 ≤ 0 := by
      rw [← hrow_pos]
      simpa [raw_value_augmented_primal_rhs] using hraw (Sum.inl (Sum.inl v))
    have hneg :
        -((digraph_incidence_matrix ℝ
              (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
            value_augmented_vector x v0) v.1) ≤ 0 := by
      rw [← hrow_neg]
      simpa [raw_value_augmented_primal_rhs] using hraw (Sum.inl (Sum.inr v))
    linarith
  have hx_feasible : IsFeasibleSTFlow tail head s t c x := by
    refine
      { toIsSTFlow := ?_
        le_capacity := ?_ }
    · refine
        { nonneg := ?_
          conservation := ?_ }
      · intro e
        -- The nonnegativity block is `-x_e ≤ 0` on the raw augmented LP owner.
        have hnonpos : -(x e) ≤ 0 := by
          simpa [ξraw, x, raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
            Matrix.mulVec, dotProduct] using hraw (Sum.inr (Sum.inr e))
        exact neg_nonpos.mp hnonpos
      · intro v hs ht
        by_cases hv :
            v ∈ relevant_value_augmented_vertices tail head s t
        · have hbalance :
              (digraph_incidence_matrix ℝ tail head *ᵥ x) v = 0 := by
            have haug := haug_balance_zero ⟨v, hv⟩
            rw [value_augmented_row_balance tail head s t x v0 v] at haug
            simpa [hs, ht] using haug
          rw [digraph_incidence_matrix_mulVec_apply] at hbalance
          exact sub_eq_zero.mp hbalance
        · have hv_not_circuit : v ∉ circuit_vertices tail head Finset.univ := by
            intro hv_circuit
            exact hv (by simp [relevant_value_augmented_vertices, hv_circuit])
          rcases
              incoming_and_outgoing_flow_eq_zero_of_not_circuit_vertex tail head x hv_not_circuit
              with ⟨hin, hout⟩
          rw [hin, hout]
    · intro e
      -- The capacity block reads off the original arc coordinate of the primal point.
      simpa [ξraw, x, raw_value_augmented_primal_matrix, raw_value_augmented_primal_rhs,
        Matrix.mulVec, dotProduct] using hraw (Sum.inr (Sum.inl e))
  have hs_balance_zero :
      (digraph_incidence_matrix ℝ
          (value_augmented_tail tail t) (value_augmented_head head s) *ᵥ
        value_augmented_vector x v0) s = 0 :=
    haug_balance_zero ⟨s, by simp [relevant_value_augmented_vertices]⟩
  have hflow_eq_v0 : st_flow_value tail head s x = v0 := by
    -- At the source row, the extra `t → s` arc cancels the raw source imbalance exactly by the
    -- flow value.
    rw [value_augmented_row_balance tail head s t x v0 s] at hs_balance_zero
    rw [digraph_incidence_matrix_mulVec_apply] at hs_balance_zero
    have hs_ne_t : s ≠ t := hst
    have hsource :
        incoming_flow head x s - outgoing_flow tail x s + v0 = 0 := by
      simpa [st_flow_value, hs_ne_t] using hs_balance_zero
    have hsource' : outgoing_flow tail x s - incoming_flow head x s = v0 := by
      linarith [hsource]
    simpa [st_flow_value] using hsource'
  have hpoint :
      value_augmented_primal_point_fin (A := A) x v0 = ξfin := by
    funext j
    rcases hcol : (value_augmented_primal_col_equiv (A := A)).symm j with (a | u)
    · have hj : j = (value_augmented_primal_col_equiv (A := A)) (Sum.inl a) := by
        simpa using congrArg (value_augmented_primal_col_equiv (A := A)) hcol
      rw [hj]
      simp [value_augmented_primal_point_fin, ξraw, x, v0, value_augmented_vector]
    · cases u
      have hj : j = (value_augmented_primal_col_equiv (A := A)) (Sum.inr ()) := by
        simpa using congrArg (value_augmented_primal_col_equiv (A := A)) hcol
      rw [hj]
      simp [value_augmented_primal_point_fin, ξraw, x, v0, value_augmented_vector]
  refine ⟨x, hx_feasible, ?_⟩
  -- Rewrite the canonical primal point recovered from `ξfin`, then reuse the one-coordinate
  -- objective lemma already proved for augmented primal points.
  calc
    st_flow_value tail head s x =
        value_augmented_primal_objective_fin (A := A) ⬝ᵥ
          value_augmented_primal_point_fin (A := A) x (st_flow_value tail head s x) := by
            symm
            exact value_augmented_primal_objective_fin_eq_flow_value (A := A) tail head s x
    _ =
        value_augmented_primal_objective_fin (A := A) ⬝ᵥ
          value_augmented_primal_point_fin (A := A) x v0 := by
            rw [hflow_eq_v0]
    _ = value_augmented_primal_objective_fin (A := A) ⬝ᵥ ξfin := by
            rw [hpoint]

/-- Helper for Theorem 4.15: the zero arc vector is a feasible `s,t`-flow whenever the capacities
are nonnegative. -/
private lemma zero_st_flow_is_feasible
    (tail head : A → V) (c : A → ℝ) (s t : V)
    (hcap : ∀ e, 0 ≤ c e) :
    IsFeasibleSTFlow tail head s t c (fun _ ↦ 0) := by
  refine
    { toIsSTFlow := ?_
      le_capacity := ?_ }
  · refine
      { nonneg := ?_
        conservation := ?_ }
    · intro e
      simp
    · intro v hs ht
      -- Both balance terms vanish because every arc value is zero.
      simp [incoming_flow, outgoing_flow]
  · intro e
    simpa using hcap e

omit [Fintype A] in
/-- Helper for Theorem 4.15: before optimization, the textbook dual inequalities already admit a
normalized integral feasible point. -/
private lemma exists_normalized_integral_dual_slack
    (tail head : A → V) (s t : V) (hst : s ≠ t) :
    ∃ y : V → ℤ, ∃ z : A → ℤ,
      y s = 1 ∧
        y t = 0 ∧
        (∀ e, 0 ≤ z e) ∧
        (∀ e, y (tail e) - y (head e) ≤ z e) := by
  classical
  let y : V → ℤ := fun v ↦ if v = s then 1 else 0
  let z : A → ℤ := fun e ↦ max (y (tail e) - y (head e)) 0
  refine ⟨y, z, ?_, ?_, ?_, ?_⟩
  · -- The source normalization is built into the indicator potential.
    simp [y]
  · -- Distinctness of `s` and `t` forces the sink value to be zero.
    have hts : t ≠ s := fun h ↦ hst h.symm
    simp [y, hts]
  · intro e
    -- Each slack variable is the maximum of the arc difference and `0`.
    simp [z]
  · intro e
    -- Choosing `z e` as the positive part makes the dual inequality immediate.
    simp [z]

/-- Helper for Theorem 4.15: the primal and textbook dual systems are both nonempty before the
LP-duality and total-unimodularity optimization step. -/
private lemma exists_feasible_flow_and_normalized_integral_dual_slack
    (tail head : A → V) (c : A → ℝ) (s t : V)
    (hst : s ≠ t) (hcap : ∀ e, 0 ≤ c e) :
    ∃ x : A → ℝ, ∃ y : V → ℤ, ∃ z : A → ℤ,
      IsFeasibleSTFlow tail head s t c x ∧
        y s = 1 ∧
        y t = 0 ∧
        (∀ e, 0 ≤ z e) ∧
        (∀ e, y (tail e) - y (head e) ≤ z e) := by
  rcases exists_normalized_integral_dual_slack tail head s t hst with ⟨y, z, hys, hyt, hz, hyz⟩
  refine ⟨fun _ ↦ 0, y, z, ?_, hys, hyt, hz, hyz⟩
  -- The zero flow provides the source-faithful primal feasible base point.
  exact zero_st_flow_is_feasible tail head c s t hcap

/-- Helper for Theorem 4.15: the augmented primal dual region is nonempty, witnessed by the
source-indicator potential and its positive-part slack. -/
private lemma value_augmented_dual_feasible_nonempty
    (tail head : A → V) (s t : V) (hst : s ≠ t) :
    Set.Nonempty
      (dual_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_objective_fin (A := A))) := by
  classical
  let ySeed : V → ℝ := fun v ↦ if v = s then 1 else 0
  let zSeed : A → ℝ := fun e ↦ max (ySeed (tail e) - ySeed (head e)) 0
  let u0raw : RawValueAugmentedPrimalRow tail head s t → ℝ
    | Sum.inl (Sum.inl v) => ySeed v.1
    | Sum.inl (Sum.inr _) => 0
    | Sum.inr (Sum.inl a) => zSeed a
    | Sum.inr (Sum.inr a) => zSeed a - (ySeed (tail a) - ySeed (head a))
  let u0fin : Fin (Fintype.card (RawValueAugmentedPrimalRow tail head s t)) → ℝ :=
    u0raw ∘ (value_augmented_primal_row_equiv tail head s t).symm
  have hzSeed_nonneg : ∀ e, 0 ≤ zSeed e := by
    intro e
    exact le_max_right _ _
  have hraw_dual_nonneg : 0 ≤ u0raw := by
    intro i
    rcases i with ((i | i) | (i | i))
    · by_cases hs' : i.1 = s
      · simp [u0raw, ySeed, hs']
      · simp [u0raw, ySeed, hs']
    · simp [u0raw]
    · exact hzSeed_nonneg i
    · have hle : ySeed (tail i) - ySeed (head i) ≤ zSeed i := le_max_left _ _
      dsimp [u0raw]
      linarith
  have hraw_dual_eq :
      u0raw ᵥ* raw_value_augmented_primal_matrix tail head s t =
        fun j : A ⊕ Unit ↦ if j = Sum.inr () then (1 : ℝ) else 0 := by
    have hsource_arc :
        ∀ e : A,
          ∑ v : RelevantValueAugmentedVertex tail head s t,
              ySeed v.1 *
                digraph_incidence_matrix ℝ
                  (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inl e) =
            ySeed (head e) - ySeed (tail e) := by
      intro e
      calc
        ∑ v : RelevantValueAugmentedVertex tail head s t,
            ySeed v.1 *
              digraph_incidence_matrix ℝ
                (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inl e) =
          ∑ v : RelevantValueAugmentedVertex tail head s t,
              (if v.1 = s then (1 : ℝ) else 0) *
                digraph_incidence_matrix ℝ
                  (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inl e) := by
              simp [ySeed]
        _ = digraph_incidence_matrix ℝ
              (value_augmented_tail tail t) (value_augmented_head head s) s (Sum.inl e) := by
              simpa using
                source_indicator_sum_over_relevant_vertices tail head s t
                  (fun v ↦
                    digraph_incidence_matrix ℝ
                      (value_augmented_tail tail t) (value_augmented_head head s) v (Sum.inl e))
        _ = ((if s = head e then (1 : ℝ) else 0) - (if s = tail e then 1 else 0)) := by
              rfl
        _ = ySeed (head e) - ySeed (tail e) := by
              simp [ySeed, eq_comm]
    have hsource_unit :
        ∑ v : RelevantValueAugmentedVertex tail head s t,
            ySeed v.1 *
              digraph_incidence_matrix ℝ
                (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inr ()) =
          1 := by
      calc
        ∑ v : RelevantValueAugmentedVertex tail head s t,
            ySeed v.1 *
              digraph_incidence_matrix ℝ
                (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inr ()) =
          ∑ v : RelevantValueAugmentedVertex tail head s t,
              (if v.1 = s then (1 : ℝ) else 0) *
                digraph_incidence_matrix ℝ
                  (value_augmented_tail tail t) (value_augmented_head head s) v.1 (Sum.inr ()) := by
              simp [ySeed]
        _ = digraph_incidence_matrix ℝ
              (value_augmented_tail tail t) (value_augmented_head head s) s (Sum.inr ()) := by
              simpa using
                source_indicator_sum_over_relevant_vertices tail head s t
                  (fun v ↦
                    digraph_incidence_matrix ℝ
                      (value_augmented_tail tail t) (value_augmented_head head s) v (Sum.inr ()))
        _ = 1 := by
              simp [digraph_incidence_matrix, value_augmented_tail, value_augmented_head, hst]
    ext j
    cases j with
    | inl e =>
        calc
          (u0raw ᵥ* raw_value_augmented_primal_matrix tail head s t) (Sum.inl e) =
              (∑ v : RelevantValueAugmentedVertex tail head s t,
                  ySeed v.1 *
                    digraph_incidence_matrix ℝ
                      (value_augmented_tail tail t) (value_augmented_head head s) v.1
                        (Sum.inl e)) +
                (ySeed (tail e) - ySeed (head e)) := by
                  simp [Matrix.vecMul, dotProduct, u0raw, raw_value_augmented_primal_matrix,
                    Fintype.sum_sum_type]
          _ = 0 := by
                have hsum := hsource_arc e
                linarith
          _ = (if Sum.inl e = Sum.inr () then (1 : ℝ) else 0) := by
                simp
    | inr u =>
        cases u
        calc
          (u0raw ᵥ* raw_value_augmented_primal_matrix tail head s t) (Sum.inr ()) =
              ∑ v : RelevantValueAugmentedVertex tail head s t,
                ySeed v.1 *
                  digraph_incidence_matrix ℝ
                    (value_augmented_tail tail t) (value_augmented_head head s) v.1
                      (Sum.inr ()) := by
                        simp [Matrix.vecMul, dotProduct, u0raw, raw_value_augmented_primal_matrix,
                          Fintype.sum_sum_type]
          _ = 1 := hsource_unit
          _ = (if Sum.inr () = Sum.inr () then (1 : ℝ) else 0) := by
                simp
  have hfin_dual_feasible :
      u0fin ∈ dual_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_objective_fin (A := A)) := by
    rw [mem_dual_feasible_region_iff]
    refine ⟨?_, ?_⟩
    · ext j
      have hu0transport :
          u0fin ∘ value_augmented_primal_row_equiv tail head s t = u0raw := by
        funext i
        simp [u0fin]
      calc
        (u0fin ᵥ* value_augmented_primal_matrix_fin tail head s t) j =
            ((u0raw ᵥ* raw_value_augmented_primal_matrix tail head s t)
              ((value_augmented_primal_col_equiv (A := A)).symm j)) := by
              simpa [hu0transport] using
                congrFun
                  (reindexed_vecMul_apply
                    (raw_value_augmented_primal_matrix tail head s t)
                    (value_augmented_primal_row_equiv tail head s t)
                    (value_augmented_primal_col_equiv (A := A))
                    u0fin)
                  j
        _ = value_augmented_primal_objective_fin (A := A) j := by
              simp [hraw_dual_eq, value_augmented_primal_objective_fin]
    · intro i
      simpa [u0fin] using
        hraw_dual_nonneg ((value_augmented_primal_row_equiv tail head s t).symm i)
  exact ⟨u0fin, hfin_dual_feasible⟩

/-- Helper for Theorem 4.15: LP duality on the augmented primal system yields a maximum feasible
`s,t`-flow. -/
private theorem exists_maximum_st_flow
    (tail head : A → V) (c : A → ℝ) (s t : V)
    (hst : s ≠ t) (hcap : ∀ e, 0 ≤ c e) :
    ∃ x, IsMaximumSTFlow tail head s t c x := by
  classical
  let ξ0fin : Fin (Fintype.card (A ⊕ Unit)) → ℝ :=
    value_augmented_primal_point_fin (A := A) (fun _ ↦ 0)
      (st_flow_value tail head s (fun _ ↦ 0))
  have hx0 : IsFeasibleSTFlow tail head s t c (fun _ ↦ 0) :=
    zero_st_flow_is_feasible tail head c s t hcap
  have hfin_primal_feasible :
      ξ0fin ∈ primal_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_rhs_fin tail head c s t) := by
    simpa [ξ0fin] using
      value_augmented_primal_fin_mem_of_feasible_st_flow
        tail head c s t (fun _ ↦ 0) hst hx0
  have hfin_primal_nonempty :
      Set.Nonempty
        (primal_feasible_region
          (value_augmented_primal_matrix_fin tail head s t)
          (value_augmented_primal_rhs_fin tail head c s t)) :=
    ⟨ξ0fin, hfin_primal_feasible⟩
  have hfin_dual_nonempty :
      Set.Nonempty
        (dual_feasible_region
          (value_augmented_primal_matrix_fin tail head s t)
          (value_augmented_primal_objective_fin (A := A))) :=
    value_augmented_dual_feasible_nonempty tail head s t hst
  rcases linear_programming_duality_primal_optimum_exists
      (value_augmented_primal_matrix_fin tail head s t)
      (value_augmented_primal_rhs_fin tail head c s t)
      (value_augmented_primal_objective_fin (A := A))
      hfin_primal_nonempty hfin_dual_nonempty with
    ⟨ξStar, hξStar_mem, hξStar_opt⟩
  rcases feasible_st_flow_of_primal_feasible_point tail head c s t hst hξStar_mem with
    ⟨xStar, hxStar, hxStar_value⟩
  refine ⟨xStar, ?_⟩
  refine
    { toIsFeasibleSTFlow := hxStar
      le_st_flow_value := ?_ }
  intro y hy
  let ξy : Fin (Fintype.card (A ⊕ Unit)) → ℝ :=
    value_augmented_primal_point_fin (A := A) y (st_flow_value tail head s y)
  have hξy_mem :
      ξy ∈ primal_feasible_region
        (value_augmented_primal_matrix_fin tail head s t)
        (value_augmented_primal_rhs_fin tail head c s t) := by
    simpa [ξy] using
      value_augmented_primal_fin_mem_of_feasible_st_flow tail head c s t y hst hy
  have hξy_obj :
      value_augmented_primal_objective_fin (A := A) ⬝ᵥ ξy =
        st_flow_value tail head s y := by
    simpa [ξy] using
      value_augmented_primal_objective_fin_eq_flow_value (A := A) tail head s y
  have hy_mem :
      st_flow_value tail head s y ∈
        primal_objective_values
          (value_augmented_primal_matrix_fin tail head s t)
          (value_augmented_primal_rhs_fin tail head c s t)
          (value_augmented_primal_objective_fin (A := A)) :=
    ⟨ξy, hξy_mem, hξy_obj⟩
  have hy_le :
      st_flow_value tail head s y ≤
        value_augmented_primal_objective_fin (A := A) ⬝ᵥ ξStar :=
    hξStar_opt.2 hy_mem
  simpa [hxStar_value] using hy_le

/-- Helper for Theorem 4.15: the residual-reachable side of a maximum flow is a tight `s,t`-cut
side. -/
private lemma exists_tight_residual_reachable_cut_of_maximum_flow
    (tail head : A → V) (c : A → ℝ) (x : A → ℝ) (s t : V)
    (hst : s ≠ t) (hx : IsMaximumSTFlow tail head s t c x) :
    ∃ S : Set V,
      IsSTCutSide s t S ∧
        st_flow_value tail head s x = cut_capacity tail head c S := by
  classical
  let S : Set V := {v | Relation.ReflTransGen (ResidualStep tail head c x) s v}
  have hno : NoResidualSTPath tail head c x s t :=
    (isMaximumSTFlow_iff_noResidualSTPath tail head c x s t hst hx.isFeasibleSTFlow).1 hx
  have hS : IsSTCutSide s t S := by
    constructor
    · exact Relation.ReflTransGen.refl
    · intro ht
      have hpath : Relation.TransGen (ResidualStep tail head c x) s t := by
        rcases Relation.ReflTransGen.cases_head_iff.mp ht with rfl | ⟨u, hsu, hut⟩
        · exact False.elim (hst rfl)
        · exact Relation.TransGen.head' hsu hut
      exact hno hpath
  have hcut :
      (∀ e ∈ δ⁺[tail, head] S, x e = c e) ∧
        ∀ e ∈ δ⁻[tail, head] S, x e = 0 := by
    constructor
    · intro e he
      rcases mem_outgoing_cut_arcs_iff.mp he with ⟨htailS, hheadS⟩
      have hnot_forward : ¬ x e < c e := by
        intro hlt
        have hstep : ResidualStep tail head c x (tail e) (head e) := by
          exact (residualStep_iff tail head c x (tail e) (head e)).2
            (Or.inl ⟨e, rfl, rfl, hlt⟩)
        have hreach : head e ∈ S := htailS.tail hstep
        exact hheadS hreach
      linarith [hx.isFeasibleSTFlow.le_capacity e]
    · intro e he
      rcases mem_incoming_cut_arcs_iff.mp he with ⟨htailS, hheadS⟩
      have hnot_backward : ¬ 0 < x e := by
        intro hpos
        have hstep : ResidualStep tail head c x (head e) (tail e) := by
          exact (residualStep_iff tail head c x (head e) (tail e)).2
            (Or.inr ⟨e, rfl, rfl, hpos⟩)
        have hreach : tail e ∈ S := hheadS.tail hstep
        exact htailS hreach
      linarith [hx.isFeasibleSTFlow.nonneg e]
  refine ⟨S, hS, ?_⟩
  exact (flow_value_eq_cut_capacity_iff tail head c x s t S hx.isFeasibleSTFlow hS).2 hcut

/-- Theorem 4.15 (Max-Flow Min-Cut Theorem). Given a finite digraph with arc type `A`, endpoint
maps `tail`, `head`, two distinct nodes `s,t`, and nonnegative capacities `c` on the arcs, there
exist a feasible maximum `s,t`-flow and a minimum `s,t`-cut side whose value and capacity
coincide. -/
theorem max_flow_min_cut_theorem
    (tail head : A → V) (c : A → ℝ) (s t : V)
    (hst : s ≠ t) (hcap : ∀ e, 0 ≤ c e) :
    ∃ x, ∃ S : Set V,
      IsMaximumSTFlow tail head s t c x ∧
        IsMinimumSTCut tail head c s t S ∧
          st_flow_value tail head s x = cut_capacity tail head c S := by
  classical
  rcases exists_maximum_st_flow tail head c s t hst hcap with ⟨x, hx⟩
  rcases exists_tight_residual_reachable_cut_of_maximum_flow tail head c x s t hst hx with
    ⟨S, hS, heq⟩
  refine ⟨x, S, hx, ?_, heq⟩
  exact flow_cut_eq_implies_isMinimumSTCut tail head c x s t S hx.isFeasibleSTFlow hS heq

end MaxFlowMinCut

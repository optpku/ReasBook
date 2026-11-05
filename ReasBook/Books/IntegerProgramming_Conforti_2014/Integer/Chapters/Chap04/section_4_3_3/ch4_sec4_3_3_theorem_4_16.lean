/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_lemma_4_14

open scoped BigOperators

section MaxFlowResidualPaths

variable {V A : Type}

private abbrev HasForwardResidualArc
    (tail head : A → V) (c x : A → ℝ) (u v : V) : Prop :=
  ∃ e : A, tail e = u ∧ head e = v ∧ x e < c e

private abbrev HasPositiveFlowArc
    (tail head : A → V) (x : A → ℝ) (u v : V) : Prop :=
  ∃ e : A, tail e = u ∧ head e = v ∧ 0 < x e

/-- Helper for Theorem 4.16: the vertices reachable from `s` in the endpoint residual digraph. -/
private def residualReachableSet
    (tail head : A → V) (c x : A → ℝ) (s : V) : Set V :=
  {v | Relation.ReflTransGen (ResidualStep tail head c x) s v}

/-- A realized residual `s,t`-path is a nonempty chain of active residual arcs whose first
residual tail is `s` and whose last residual head is `t`. -/
def IsResidualSTPath
    (tail head : A → V) (c x : A → ℝ) (s t : V) (P : List (ResidualArc A)) : Prop :=
  P ≠ [] ∧
    (∀ a ∈ P, IsActiveResidualArc c x a) ∧
    P.head?.map (ResidualArc.tail tail head) = some s ∧
    P.getLast?.map (ResidualArc.head tail head) = some t ∧
    P.IsChain (fun a b ↦ ResidualArc.head tail head a = ResidualArc.tail tail head b)

/-- The residual digraph contains no directed `s,t`-path exactly when `t` is not reachable from
`s` in the transitive closure of the chapter's canonical residual-step relation. -/
noncomputable def NoResidualSTPath
    (tail head : A → V) (c x : A → ℝ) (s t : V) : Prop :=
  ¬ Relation.TransGen (ResidualStep tail head c x) s t

variable [Fintype A]

/-- Helper for Theorem 4.16: every residual step can be realized by an active residual arc witness
with matching endpoints. -/
private lemma exists_residual_arc_of_step
    (tail head : A → V) (c x : A → ℝ) {u v : V}
    (hstep : ResidualStep tail head c x u v) :
    ∃ a : ResidualArc A,
      ResidualArc.tail tail head a = u ∧
        ResidualArc.head tail head a = v ∧
        IsActiveResidualArc c x a := by
  -- Split the residual step into the forward and backward cases from the residual-digraph API.
  have hstep' :
      HasForwardResidualArc tail head c x u v ∨ HasPositiveFlowArc tail head x v u := by
    simpa [HasForwardResidualArc, HasPositiveFlowArc] using
      (residualStep_iff tail head c x u v).1 hstep
  rcases hstep' with hforward | hbackward
  · rcases hforward with ⟨e, he_tail, he_head, hlt⟩
    refine ⟨⟨e, .forward⟩, ?_, ?_, ?_⟩
    · simpa [ResidualArc.tail, he_tail]
    · simpa [ResidualArc.head, he_head]
    · simpa [IsActiveResidualArc, residual_arc_capacity] using sub_pos.mpr hlt
  · rcases hbackward with ⟨e, he_tail, he_head, hpos⟩
    refine ⟨⟨e, .backward⟩, ?_, ?_, ?_⟩
    · simpa [ResidualArc.tail, he_head]
    · simpa [ResidualArc.head, he_tail]
    · simpa [IsActiveResidualArc, residual_arc_capacity] using hpos

/-- Helper for Theorem 4.16: a residual `TransGen` witness can be realized as a concrete nonempty
list of active residual arc witnesses with matching consecutive endpoints. -/
private lemma realized_residual_path_of_transgen
    (tail head : A → V) (c x : A → ℝ) {s t : V}
    (hpath : Relation.TransGen (ResidualStep tail head c x) s t) :
    ∃ P : List (ResidualArc A), IsResidualSTPath tail head c x s t P := by
  -- Build the realized path by following the transitive-closure proof one step at a time.
  induction hpath using Relation.TransGen.head_induction_on with
  | single hstep =>
      rcases exists_residual_arc_of_step tail head c x hstep with ⟨a, ha_tail, ha_head, ha_active⟩
      refine ⟨[a], ?_⟩
      -- A single residual step gives a singleton active residual path from `s` to `t`.
      refine ⟨by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
      · intro b hb
        simpa using (List.mem_singleton.mp hb ▸ ha_active)
      · simpa [ha_tail]
      · simpa [ha_head]
  | head hstep htail ih =>
      rcases exists_residual_arc_of_step tail head c x hstep with ⟨a, ha_tail, ha_head, ha_active⟩
      rcases ih with ⟨P, hP⟩
      rcases hP with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
      cases P with
      | nil =>
          exact False.elim (hP_ne rfl)
      | cons b P' =>
          have hP_head' :
              some (ResidualArc.tail tail head b) = some (ResidualArc.head tail head a) := by
            simpa [ha_head] using hP_head
          have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            injection hP_head' with hEq
            exact hEq.symm
          refine ⟨a :: b :: P', ?_⟩
          -- Prepending the realized first step preserves activeness, endpoints, and chain adjacency.
          refine ⟨by simp, ?_, ?_, ?_, ?_⟩
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact ha_active
            · exact hP_active z hz
          · simpa [ha_tail]
          · simpa using hP_last
          · exact hP_chain.cons_cons hlink

/-- Helper for Theorem 4.16: the residual-reachable side from `s` is an `s,t`-cut side when there
is no residual `s,t`-path. -/
private lemma reachable_residual_cut_isSTCutSide
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    (hst : s ≠ t) (hno : NoResidualSTPath tail head c x s t) :
    IsSTCutSide s t (residualReachableSet tail head c x s) := by
  constructor
  · -- The source is reachable from itself by the reflexive closure.
    exact Relation.ReflTransGen.refl
  · intro ht
    -- Any reachability proof to `t` yields the forbidden residual `TransGen` path.
    have hpath : Relation.TransGen (ResidualStep tail head c x) s t := by
      rcases Relation.ReflTransGen.cases_head_iff.mp ht with rfl | ⟨u, hsu, hut⟩
      · exact False.elim (hst rfl)
      · exact Relation.TransGen.head' hsu hut
    exact hno hpath

/-- Helper for Theorem 4.16: the cut determined by the residual-reachable side is tight for the
current feasible flow, so the flow value equals that cut capacity. -/
private lemma reachable_residual_cut_value_eq_capacity
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    (hx : IsFeasibleSTFlow tail head s t c x)
    (hst : s ≠ t) (hno : NoResidualSTPath tail head c x s t) :
    st_flow_value tail head s x =
      cut_capacity tail head c (residualReachableSet tail head c x s) := by
  let S : Set V := residualReachableSet tail head c x s
  have hS : IsSTCutSide s t S := reachable_residual_cut_isSTCutSide tail head c x s t hst hno
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
      linarith [hx.le_capacity e]
    · intro e he
      rcases mem_incoming_cut_arcs_iff.mp he with ⟨htailS, hheadS⟩
      have hnot_backward : ¬ 0 < x e := by
        intro hpos
        have hstep : ResidualStep tail head c x (head e) (tail e) := by
          exact (residualStep_iff tail head c x (head e) (tail e)).2
            (Or.inr ⟨e, rfl, rfl, hpos⟩)
        have hreach : tail e ∈ S := hheadS.tail hstep
        exact htailS hreach
      linarith [hx.nonneg e]
  -- Invoke Lemma 4.14 on the reachable cut once every crossing arc is forced tight.
  exact (flow_value_eq_cut_capacity_iff tail head c x s t S hx hS).2 hcut

section Augmentation

variable [DecidableEq A] [DecidableEq V]

/-- The number of forward traversals of an original arc along a realized residual path. -/
def residual_forward_use_count (P : List (ResidualArc A)) (e : A) : ℕ :=
  P.countP fun a ↦ a.edge = e ∧ a.orientation = .forward

/-- The number of backward traversals of an original arc along a realized residual path. -/
def residual_backward_use_count (P : List (ResidualArc A)) (e : A) : ℕ :=
  P.countP fun a ↦ a.edge = e ∧ a.orientation = .backward

/-- Helper for Theorem 4.16: augmenting a flow along one realized residual step changes only the
underlying original arc, adding `ε` in the forward case and subtracting `ε` in the backward case. -/
private def augment_residual_arc_flow
    (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) : A → ℝ :=
  fun e ↦ x e + if a.edge = e then
    match a.orientation with
    | .forward => ε
    | .backward => -ε
  else 0

/-- Augmenting along a realized residual path adds `ε` once for each forward use of an original
arc and subtracts `ε` once for each backward use. -/
def augment_flow
    (x : A → ℝ) (ε : ℝ) (P : List (ResidualArc A)) : A → ℝ :=
  fun e ↦ x e + ε * ((residual_forward_use_count P e : ℝ) - residual_backward_use_count P e)

/-- Helper for Theorem 4.16: the signed incidence of a vertex along a realized residual path is
the number of path departures from that vertex minus the number of path arrivals. -/
private def path_incidence
    (tail head : A → V) (P : List (ResidualArc A)) (v : V) : ℝ :=
  ((P.countP fun a ↦ ResidualArc.tail tail head a = v : ℕ) : ℝ) -
    (((P.countP fun a ↦ ResidualArc.head tail head a = v : ℕ) : ℝ))

/-- Helper for Theorem 4.16: every nonempty finite list of positive residual capacities has a
positive common lower bound. -/
private lemma exists_positive_residual_capacity_lower_bound
    (c x : A → ℝ) (P : List (ResidualArc A))
    (hP_ne : P ≠ [])
    (hP_pos : ∀ a ∈ P, 0 < residual_arc_capacity c x a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ P, δ ≤ residual_arc_capacity c x a := by
  -- Induct on the path and keep the minimum lower bound seen so far.
  revert hP_ne hP_pos
  induction P with
  | nil =>
      intro hP_ne _
      exact False.elim (hP_ne rfl)
  | cons a P ih =>
      intro _ hP_pos
      cases P with
      | nil =>
          refine ⟨residual_arc_capacity c x a, hP_pos a (by simp), ?_⟩
          intro b hb
          rcases List.mem_singleton.mp hb with rfl
          exact le_rfl
      | cons b P' =>
          have htail_pos : ∀ z ∈ b :: P', 0 < residual_arc_capacity c x z := by
            intro z hz
            exact hP_pos z (by simp [hz])
          rcases ih (by simp) htail_pos with ⟨δ, hδ_pos, hδ_le⟩
          refine ⟨min (residual_arc_capacity c x a) δ, by
            exact lt_min (hP_pos a (by simp)) hδ_pos, ?_⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact min_le_left _ _
          · exact le_trans (min_le_right _ _) (hδ_le z hz')

/-- Helper for Theorem 4.16: a residual path admits a positive augmentation amount `ε` whose
product with the path length is bounded by every residual capacity on the path. -/
private lemma scaled_bottleneck_exists_of_residual_path
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x s t P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ P, (P.length : ℝ) * ε ≤ residual_arc_capacity c x a := by
  rcases hP with ⟨hP_ne, hP_active, _, _, _⟩
  rcases exists_positive_residual_capacity_lower_bound c x P hP_ne
      (by
        intro a ha
        exact hP_active a ha) with ⟨δ, hδ_pos, hδ_le⟩
  have hlen_nat : 0 < P.length := by
    cases P with
    | nil =>
        exact False.elim (hP_ne rfl)
    | cons _ _ =>
        simp
  have hlen_pos : 0 < (P.length : ℝ) := by
    exact_mod_cast hlen_nat
  have hlen_ne : (P.length : ℝ) ≠ 0 := ne_of_gt hlen_pos
  refine ⟨δ / P.length, div_pos hδ_pos hlen_pos, ?_⟩
  intro a ha
  have hmul : (P.length : ℝ) * (δ / P.length) = δ := by
    field_simp [hlen_ne]
  calc
    (P.length : ℝ) * (δ / P.length) = δ := hmul
    _ ≤ residual_arc_capacity c x a := hδ_le a ha

/-- Helper for Theorem 4.16: the forward-use count of an arc is bounded by the total path
length. -/
private lemma residual_forward_use_count_le_length
    (P : List (ResidualArc A)) (e : A) :
    residual_forward_use_count P e ≤ P.length := by
  -- The forward-use count is a `countP`, so the generic list bound applies directly.
  simpa [residual_forward_use_count] using
    (List.countP_le_length (p := fun a ↦ a.edge = e ∧ a.orientation = .forward) (l := P))

/-- Helper for Theorem 4.16: the backward-use count of an arc is bounded by the total path
length. -/
private lemma residual_backward_use_count_le_length
    (P : List (ResidualArc A)) (e : A) :
    residual_backward_use_count P e ≤ P.length := by
  -- The backward-use count is another `countP`, so it satisfies the same length bound.
  simpa [residual_backward_use_count] using
    (List.countP_le_length (p := fun a ↦ a.edge = e ∧ a.orientation = .backward) (l := P))

/-- Helper for Theorem 4.16: a positive forward-use count yields a concrete forward traversal of
the corresponding original arc on the path. -/
private lemma exists_forward_residual_use_of_count_pos
    {P : List (ResidualArc A)} {e : A}
    (hcount : 0 < residual_forward_use_count P e) :
    ∃ a ∈ P, a.edge = e ∧ a.orientation = .forward := by
  -- Convert the list count to the multiset positivity criterion to recover a witness.
  have hcount' :
      0 < Multiset.countP (fun a : ResidualArc A ↦ a.edge = e ∧ a.orientation = .forward)
        (P : Multiset (ResidualArc A)) := by
    simpa [residual_forward_use_count] using hcount
  rcases Multiset.countP_pos.mp hcount' with ⟨a, haP, hae, haori⟩
  exact ⟨a, by simpa using haP, hae, haori⟩

/-- Helper for Theorem 4.16: a positive backward-use count yields a concrete backward traversal of
the corresponding original arc on the path. -/
private lemma exists_backward_residual_use_of_count_pos
    {P : List (ResidualArc A)} {e : A}
    (hcount : 0 < residual_backward_use_count P e) :
    ∃ a ∈ P, a.edge = e ∧ a.orientation = .backward := by
  -- Convert the list count to the multiset positivity criterion to recover a witness.
  have hcount' :
      0 < Multiset.countP (fun a : ResidualArc A ↦ a.edge = e ∧ a.orientation = .backward)
        (P : Multiset (ResidualArc A)) := by
    simpa [residual_backward_use_count] using hcount
  rcases Multiset.countP_pos.mp hcount' with ⟨a, haP, hae, haori⟩
  exact ⟨a, by simpa using haP, hae, haori⟩

/-- Helper for Theorem 4.16: the whole-path augmentation can be peeled into the first realized
residual step followed by augmentation along the remaining suffix. -/
private lemma augment_flow_cons
    (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (P : List (ResidualArc A)) :
    augment_flow x ε (a :: P) = augment_flow (augment_residual_arc_flow x ε a) ε P := by
  -- Expand the head counts on both sides and compare the resulting per-edge formulas.
  cases a with
  | mk edge orientation =>
      ext e
      by_cases he : edge = e
      · subst he
        cases orientation <;>
          simp [augment_flow, augment_residual_arc_flow, residual_forward_use_count,
            residual_backward_use_count, List.countP_cons]
          <;> ring_nf
      · cases orientation <;>
          simp [augment_flow, augment_residual_arc_flow, residual_forward_use_count,
            residual_backward_use_count, he]

/-- Helper for Theorem 4.16: the signed path incidence splits into the first residual step plus
the signed incidence of the remaining suffix. -/
private lemma path_incidence_cons
    (tail head : A → V) (a : ResidualArc A) (P : List (ResidualArc A)) (v : V) :
    path_incidence tail head (a :: P) v =
      (((if ResidualArc.tail tail head a = v then (1 : ℝ) else 0) -
          (if ResidualArc.head tail head a = v then (1 : ℝ) else 0))) +
        path_incidence tail head P v := by
  -- Expand the two `countP` terms at the head of the list and regroup the resulting arithmetic.
  by_cases htail : ResidualArc.tail tail head a = v
  · by_cases hhead : ResidualArc.head tail head a = v
    · simp [path_incidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
      ring_nf
    · simp [path_incidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
      ring_nf
  · by_cases hhead : ResidualArc.head tail head a = v
    · simp [path_incidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
    · simp [path_incidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]

/-- Helper for Theorem 4.16: summing a single-point delta over a finite arc set isolates that one
changed arc when it lies in the set and otherwise gives zero. -/
private lemma sum_single_edge_delta
    (S : Finset A) (a : A) (δ : ℝ) :
    Finset.sum S (fun e ↦ if a = e then δ else (0 : ℝ)) = if a ∈ S then δ else 0 := by
  -- Only the summand indexed by `a` can be nonzero, so the finite sum collapses to an indicator.
  by_cases ha : a ∈ S
  · rw [if_pos ha]
    rw [Finset.sum_eq_single_of_mem a ha]
    · simp
    · intro e heS hne
      have hne' : a ≠ e := by
        intro hae
        exact hne hae.symm
      simp [hne']
  · rw [if_neg ha]
    refine Finset.sum_eq_zero ?_
    intro e heS
    have hne : a ≠ e := by
      intro hae
      exact ha (hae ▸ heS)
    simp [hne]

/-- Helper for Theorem 4.16: a single residual-step augmentation changes the outgoing flow at a
vertex only when that vertex is the tail of the underlying original arc. -/
private lemma outgoing_flow_augment_residual_arc_flow
    (tail : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    outgoing_flow tail (augment_residual_arc_flow x ε a) v =
      outgoing_flow tail x v +
        if tail a.edge = v then
          match a.orientation with
          | .forward => ε
          | .backward => -ε
        else 0 := by
  -- Rewrite as a finite sum over outgoing arcs and isolate the single changed original arc.
  rw [outgoing_flow_eq_sum_outgoing_arcs, outgoing_flow_eq_sum_outgoing_arcs]
  unfold augment_residual_arc_flow
  rw [Finset.sum_add_distrib]
  congr 1
  simpa [mem_outgoing_arcs_iff] using
    (sum_single_edge_delta (S := outgoing_arcs tail v) (a := a.edge)
      (δ := match a.orientation with
        | .forward => ε
        | .backward => -ε))

/-- Helper for Theorem 4.16: a single residual-step augmentation changes the incoming flow at a
vertex only when that vertex is the head of the underlying original arc. -/
private lemma incoming_flow_augment_residual_arc_flow
    (head : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    incoming_flow head (augment_residual_arc_flow x ε a) v =
      incoming_flow head x v +
        if head a.edge = v then
          match a.orientation with
          | .forward => ε
          | .backward => -ε
        else 0 := by
  -- Rewrite as a finite sum over incoming arcs and isolate the single changed original arc.
  rw [incoming_flow_eq_sum_incoming_arcs, incoming_flow_eq_sum_incoming_arcs]
  unfold augment_residual_arc_flow
  rw [Finset.sum_add_distrib]
  congr 1
  simpa [mem_incoming_arcs_iff] using
    (sum_single_edge_delta (S := incoming_arcs head v) (a := a.edge)
      (δ := match a.orientation with
        | .forward => ε
        | .backward => -ε))

/-- Helper for Theorem 4.16: augmenting along one realized residual step changes the net outflow
at a vertex by `+ε` at the residual tail, `-ε` at the residual head, and `0` elsewhere. -/
private lemma net_outflow_augment_residual_arc_flow
    (tail head : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    outgoing_flow tail (augment_residual_arc_flow x ε a) v -
        incoming_flow head (augment_residual_arc_flow x ε a) v =
      (outgoing_flow tail x v - incoming_flow head x v) +
        ε * (((if ResidualArc.tail tail head a = v then (1 : ℝ) else 0) -
          (if ResidualArc.head tail head a = v then (1 : ℝ) else 0))) := by
  -- Split into the forward and backward orientation cases and simplify the endpoint bookkeeping.
  cases a with
  | mk edge orientation =>
      cases orientation
      · rw [outgoing_flow_augment_residual_arc_flow, incoming_flow_augment_residual_arc_flow]
        by_cases htail : tail edge = v
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
      · rw [outgoing_flow_augment_residual_arc_flow, incoming_flow_augment_residual_arc_flow]
        by_cases htail : tail edge = v
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]

/-- Helper for Theorem 4.16: a scaled bottleneck keeps every augmented arc value between `0` and
its capacity. -/
private lemma augment_flow_bounds_of_scaled_bottleneck
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    (hx : IsFeasibleSTFlow tail head s t c x)
    {P : List (ResidualArc A)} {ε : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hε : ∀ a ∈ P, (P.length : ℝ) * ε ≤ residual_arc_capacity c x a) :
    ∀ e, 0 ≤ augment_flow x ε P e ∧ augment_flow x ε P e ≤ c e := by
  intro e
  have hf_le_len : ((residual_forward_use_count P e : ℕ) : ℝ) ≤ P.length := by
    exact_mod_cast residual_forward_use_count_le_length P e
  have hb_le_len : ((residual_backward_use_count P e : ℕ) : ℝ) ≤ P.length := by
    exact_mod_cast residual_backward_use_count_le_length P e
  have hf_nonneg : 0 ≤ ((residual_forward_use_count P e : ℕ) : ℝ) := by positivity
  have hb_nonneg : 0 ≤ ((residual_backward_use_count P e : ℕ) : ℝ) := by positivity
  have hforward_bound :
      ((residual_forward_use_count P e : ℕ) : ℝ) * ε ≤ c e - x e := by
    by_cases hf_zero : residual_forward_use_count P e = 0
    · rw [hf_zero]
      simpa using hx.le_capacity e
    · have hf_pos : 0 < residual_forward_use_count P e := Nat.pos_of_ne_zero hf_zero
      rcases exists_forward_residual_use_of_count_pos hf_pos with ⟨a, haP, hae, haori⟩
      have hscaled : (P.length : ℝ) * ε ≤ residual_arc_capacity c x a := hε a haP
      have hcount_scaled :
          ((residual_forward_use_count P e : ℕ) : ℝ) * ε ≤ (P.length : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_right hf_le_len hε_nonneg
      have hslack : (P.length : ℝ) * ε ≤ c e - x e := by
        simpa [residual_arc_capacity, hae, haori] using hscaled
      exact le_trans hcount_scaled hslack
  have hbackward_bound :
      ((residual_backward_use_count P e : ℕ) : ℝ) * ε ≤ x e := by
    by_cases hb_zero : residual_backward_use_count P e = 0
    · rw [hb_zero]
      simpa using hx.nonneg e
    · have hb_pos : 0 < residual_backward_use_count P e := Nat.pos_of_ne_zero hb_zero
      rcases exists_backward_residual_use_of_count_pos hb_pos with ⟨a, haP, hae, haori⟩
      have hscaled : (P.length : ℝ) * ε ≤ residual_arc_capacity c x a := hε a haP
      have hcount_scaled :
          ((residual_backward_use_count P e : ℕ) : ℝ) * ε ≤ (P.length : ℝ) * ε := by
        exact mul_le_mul_of_nonneg_right hb_le_len hε_nonneg
      have hflow : (P.length : ℝ) * ε ≤ x e := by
        simpa [residual_arc_capacity, hae, haori] using hscaled
      exact le_trans hcount_scaled hflow
  constructor
  · -- The backward subtraction is absorbed by the original flow, and the forward addition is
    -- nonnegative.
    have hbase_nonneg :
        0 ≤ x e - ((residual_backward_use_count P e : ℕ) : ℝ) * ε := by
      linarith
    calc
      0 ≤ x e - ((residual_backward_use_count P e : ℕ) : ℝ) * ε := hbase_nonneg
      _ ≤ augment_flow x ε P e := by
        unfold augment_flow
        nlinarith
  · -- The forward addition is absorbed by the original slack, and the backward subtraction only
    -- decreases the value.
    have hbase_le_capacity :
        x e + ((residual_forward_use_count P e : ℕ) : ℝ) * ε ≤ c e := by
      linarith
    calc
      augment_flow x ε P e ≤ x e + ((residual_forward_use_count P e : ℕ) : ℝ) * ε := by
        unfold augment_flow
        nlinarith
      _ ≤ c e := hbase_le_capacity

/-- Helper for Theorem 4.16: the net outflow after augmentation equals the old net outflow plus
`ε` times the signed path incidence at the chosen vertex. -/
private lemma augment_flow_net_outflow_eq_add_path_incidence
    (tail head : A → V) (x : A → ℝ) (ε : ℝ) (P : List (ResidualArc A)) (v : V) :
    outgoing_flow tail (augment_flow x ε P) v - incoming_flow head (augment_flow x ε P) v =
      (outgoing_flow tail x v - incoming_flow head x v) + ε * path_incidence tail head P v := by
  -- Induct on the realized residual path, peeling off one residual step at a time.
  revert x
  induction P with
  | nil =>
      intro x
      simp [augment_flow, residual_forward_use_count, residual_backward_use_count, path_incidence]
  | cons a P ih =>
      intro x
      rw [augment_flow_cons, ih (augment_residual_arc_flow x ε a),
        net_outflow_augment_residual_arc_flow, path_incidence_cons]
      ring_nf

/-- Helper for Theorem 4.16: the signed incidence of a realized residual `u,v`-path is `+1` at
its initial vertex, `-1` at its terminal vertex, and `0` elsewhere. -/
private lemma residual_path_incidence_eq_endpoints
    (tail head : A → V) (c x : A → ℝ) (w : V)
    {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    path_incidence tail head P w =
      (if u = w then (1 : ℝ) else 0) - (if v = w then (1 : ℝ) else 0) := by
  -- Induct on the path and telescope the incidence contributions along the chain.
  revert u v
  induction P with
  | nil =>
      intro u v hP
      exact False.elim (hP.1 rfl)
  | cons a P ih =>
      intro u v hP
      rcases hP with ⟨_, hP_active, hP_head, hP_last, hP_chain⟩
      cases P with
      | nil =>
          have hu : ResidualArc.tail tail head a = u := by
            simpa using hP_head
          have hv : ResidualArc.head tail head a = v := by
            simpa using hP_last
          simp [path_incidence, hu, hv]
      | cons b Q =>
          have hlink :
              ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            simpa using (List.isChain_cons_cons.mp hP_chain).1
          have htail_path :
              IsResidualSTPath tail head c x (ResidualArc.tail tail head b) v (b :: Q) := by
            refine ⟨by simp, ?_, ?_, ?_, ?_⟩
            · intro z hz
              exact hP_active z (by simp [hz])
            · simpa [hlink] using hP_head
            · simpa using hP_last
            · simpa using (List.isChain_cons_cons.mp hP_chain).2
          have hu : ResidualArc.tail tail head a = u := by
            simpa using hP_head
          calc
            path_incidence tail head (a :: b :: Q) w =
                (((if u = w then (1 : ℝ) else 0) -
                    (if ResidualArc.tail tail head b = w then (1 : ℝ) else 0))) +
                  path_incidence tail head (b :: Q) w := by
                    rw [path_incidence_cons]
                    simp [hu, hlink]
            _ = (if u = w then (1 : ℝ) else 0) - (if v = w then (1 : ℝ) else 0) := by
              rw [ih htail_path]
              ring

/-- Helper for Theorem 4.16: an active realized residual path should support the bottleneck
augmentation that increases the flow value while preserving feasibility. -/
private lemma exists_strictly_larger_feasible_flow_of_residual_path
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    (hx : IsFeasibleSTFlow tail head s t c x)
    (hst : s ≠ t)
    {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x s t P) :
    ∃ y : A → ℝ, IsFeasibleSTFlow tail head s t c y ∧
      st_flow_value tail head s x < st_flow_value tail head s y := by
  -- Route correction: the old helper statement omitted `s ≠ t`, but the source-value increase is
  -- only true for genuine source/sink pairs, so we augment under that necessary hypothesis.
  rcases scaled_bottleneck_exists_of_residual_path tail head c x s t hP with ⟨ε, hε_pos, hε⟩
  let y : A → ℝ := augment_flow x ε P
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hbounds :
      ∀ e, 0 ≤ y e ∧ y e ≤ c e := by
    intro e
    simpa [y] using
      augment_flow_bounds_of_scaled_bottleneck tail head c x s t hx hε_nonneg hε e
  have hy_conservation :
      ∀ v, v ≠ s → v ≠ t → incoming_flow head y v = outgoing_flow tail y v := by
    intro v hs ht
    -- Away from the endpoints, the path incidence is zero, so conservation is preserved.
    have hs' : s ≠ v := by
      intro hsv
      exact hs hsv.symm
    have ht' : t ≠ v := by
      intro htv
      exact ht htv.symm
    have hinc_v : path_incidence tail head P v = 0 := by
      simpa [hs', ht'] using
        residual_path_incidence_eq_endpoints tail head c x v hP
    have hx_net_zero : outgoing_flow tail x v - incoming_flow head x v = 0 := by
      linarith [hx.conservation v hs ht]
    have hnet_y := augment_flow_net_outflow_eq_add_path_incidence tail head x ε P v
    have hy_net_zero : outgoing_flow tail y v - incoming_flow head y v = 0 := by
      rw [hinc_v] at hnet_y
      have : outgoing_flow tail y v - incoming_flow head y v =
          outgoing_flow tail x v - incoming_flow head x v := by
        simpa [y] using hnet_y
      linarith
    linarith
  have hy_feasible : IsFeasibleSTFlow tail head s t c y := by
    -- Assemble feasibility from the edge bounds and the preserved conservation equations.
    refine
      { nonneg := fun e ↦ (hbounds e).1
        conservation := hy_conservation
        le_capacity := fun e ↦ (hbounds e).2 }
  have hinc_s : path_incidence tail head P s = 1 := by
    have hts : t ≠ s := by
      intro hts
      exact hst hts.symm
    simpa [hts] using residual_path_incidence_eq_endpoints tail head c x s hP
  have hvalue :
      st_flow_value tail head s y = st_flow_value tail head s x + ε := by
    -- At the source, the path contributes one extra unit of signed incidence.
    have hnet_s := augment_flow_net_outflow_eq_add_path_incidence tail head x ε P s
    rw [hinc_s] at hnet_s
    simpa [st_flow_value, y] using hnet_s
  have hlt : st_flow_value tail head s x < st_flow_value tail head s y := by
    linarith [hε_pos, hvalue]
  exact ⟨y, hy_feasible, hlt⟩

end Augmentation

/-- Theorem 4.16. Given a finite digraph with endpoint maps `tail`, `head`, two distinct nodes
`s,t`, and a feasible `s,t`-flow `x`, the flow is maximum if and only if the residual digraph
contains no directed `s,t`-path. -/
theorem isMaximumSTFlow_iff_noResidualSTPath
    (tail head : A → V) (c x : A → ℝ) (s t : V)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x) :
    IsMaximumSTFlow tail head s t c x ↔ NoResidualSTPath tail head c x s t := by
  classical
  constructor
  · intro hmax
    intro hpath
    -- Route correction: the forward direction stays source-faithful by extracting a realized
    -- residual path and then augmenting along it to contradict maximality.
    rcases realized_residual_path_of_transgen tail head c x hpath with ⟨P, hP⟩
    rcases exists_strictly_larger_feasible_flow_of_residual_path tail head c x s t hx hst hP with
      ⟨y, hy, hlt⟩
    exact not_lt_of_ge (hmax.le_st_flow_value y hy) hlt
  · intro hno
    -- The converse follows the source proof: use the residual-reachable set as a tight cut.
    let S : Set V := residualReachableSet tail head c x s
    have hS : IsSTCutSide s t S := reachable_residual_cut_isSTCutSide tail head c x s t hst hno
    have heq : st_flow_value tail head s x = cut_capacity tail head c S :=
      reachable_residual_cut_value_eq_capacity tail head c x s t hx hst hno
    exact flow_cut_eq_implies_isMaximumSTFlow tail head c x s t S hx hS heq

end MaxFlowResidualPaths

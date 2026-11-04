/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_theorem_4_17
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_lemma_4_14

open scoped BigOperators

section AugmentingPaths

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- A residual path carries the bottleneck augmentation amount when the amount is bounded above by
every residual capacity on the path and is attained on one of them. Positivity is then automatic,
because a residual path only uses arcs of positive residual capacity. -/
def IsBottleneckAugmentation
    (tail head : A → V) (s t : V) (c x : A → ℝ)
    (P : List (ResidualArc A)) (ε : ℝ) : Prop :=
  IsResidualSTPath tail head c x s t P ∧
    (∀ a ∈ P, ε ≤ residual_arc_capacity c x a) ∧
      ∃ a ∈ P, residual_arc_capacity c x a = ε

omit [Fintype V] [Fintype A] [DecidableEq A] in
theorem IsBottleneckAugmentation.pos
    {tail head : A → V} {s t : V} {c x : A → ℝ}
    {P : List (ResidualArc A)} {ε : ℝ}
    (hε : IsBottleneckAugmentation tail head s t c x P ε) :
    0 < ε := by
  rcases hε with ⟨hP, _, a, haP, h_eq⟩
  have h_active : IsActiveResidualArc c x a := hP.2.1 a haP
  simpa [IsActiveResidualArc, h_eq] using h_active

namespace AugmentingPathsAlgorithm

/-- An augmenting-paths run stops at stage `k` when the current feasible flow has no residual
`s,t`-path in the chapter's canonical residual digraph. -/
abbrev StopsAt
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (k : ℕ) : Prop :=
  NoResidualSTPath tail head c (flows k) s t

end AugmentingPathsAlgorithm

/-- A stage-indexed family of feasible `s,t`-flows follows the augmenting-paths algorithm when it
starts at the zero flow and each nonterminal stage augments the current flow along a residual
`s,t`-path by a bottleneck amount. -/
@[mk_iff isAugmentingPathsAlgorithm_iff]
class IsAugmentingPathsAlgorithm
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A)) : Prop where
  start_eq_zero : flows 0 = 0
  feasible (n : ℕ) : IsFeasibleSTFlow tail head s t c (flows n)
  step (n : ℕ)
      (hn : ¬ AugmentingPathsAlgorithm.StopsAt tail head s t c flows n) :
      ∃ ε, IsBottleneckAugmentation tail head s t c (flows n) (paths n) ε ∧
        flows (n + 1) = augment_flow (flows n) ε (paths n)

instance
    {tail head : A → V} {s t : V} {c : A → ℝ}
    {flows : ℕ → A → ℝ} {paths : ℕ → List (ResidualArc A)} :
    CoeFun (IsAugmentingPathsAlgorithm tail head s t c flows paths)
      (fun _ ↦ (n : ℕ) → IsFeasibleSTFlow tail head s t c (flows n)) where
  coe hAlg := hAlg.feasible

namespace AugmentingPathsAlgorithm

/-- A shortest augmenting-path run is an augmenting-paths run in which every chosen nonterminal
residual path has minimum length. -/
class IsShortest
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A)) : Prop
    extends IsAugmentingPathsAlgorithm tail head s t c flows paths where
  shortest (n : ℕ) (hn : ¬ StopsAt tail head s t c flows n) :
    IsShortestResidualSTPath tail head c (flows n) s t (paths n)

instance
    {tail head : A → V} {s t : V} {c : A → ℝ}
    {flows : ℕ → A → ℝ} {paths : ℕ → List (ResidualArc A)}
    [hshort : IsShortest tail head s t c flows paths] :
    IsAugmentingPathsAlgorithm tail head s t c flows paths :=
  hshort.toIsAugmentingPathsAlgorithm

theorem IsShortest.isShortestAugmentingPathStep
    {tail head : A → V} {s t : V} {c : A → ℝ}
    {flows : ℕ → A → ℝ} {paths : ℕ → List (ResidualArc A)}
    (hshort : IsShortest tail head s t c flows paths) (n : ℕ)
    (hn : ¬ StopsAt tail head s t c flows n) :
    IsShortestAugmentingPathStep tail head s t c (flows n) (flows (n + 1)) := by
  rcases hshort.step n hn with ⟨ε, hε, hnext⟩
  refine
    ⟨hshort.feasible n, hshort.feasible (n + 1), ε, paths n,
      hshort.shortest n hn, hε.2.1, hε.2.2, hnext⟩

end AugmentingPathsAlgorithm

/-- A positive integer `D` is a common denominator for the positive capacities when every positive
capacity can be written with denominator `D`. -/
def IsCommonPositiveCapacityDenominator (c : A → ℝ) (D : ℕ) : Prop :=
  0 < D ∧
    ∀ e, 0 < c e → ∃ m : ℤ, c e = (m : ℝ) / D

/-- A least common denominator for the positive capacities is a common denominator with minimal
positive value. -/
def IsLeastCommonPositiveCapacityDenominator (c : A → ℝ) (D : ℕ) : Prop :=
  IsCommonPositiveCapacityDenominator c D ∧
    ∀ D', IsCommonPositiveCapacityDenominator c D' → D ≤ D'

/-- A feasible `s,t`-flow is an integral maximum flow when it is both maximum and integral. -/
class IsIntegralMaximumSTFlow
    (tail head : A → V) (s t : V) (c x : A → ℝ) : Prop where
  isMaximumSTFlow : IsMaximumSTFlow tail head s t c x
  isIntegralSTFlow : IsIntegralSTFlow x

instance
    {tail head : A → V} {s t : V} {c x : A → ℝ}
    [hx : IsIntegralMaximumSTFlow tail head s t c x] :
    IsMaximumSTFlow tail head s t c x :=
  hx.isMaximumSTFlow

theorem IsIntegralMaximumSTFlow.isIntegral
    {tail head : A → V} {s t : V} {c x : A → ℝ}
    (hx : IsIntegralMaximumSTFlow tail head s t c x) :
    IsIntegralSTFlow x :=
  hx.isIntegralSTFlow

end AugmentingPaths

section AlgorithmProofHelpers

variable {V A : Type}
variable [Fintype V] [Fintype A] [DecidableEq A]

/-- Helper for Algorithm 4.3.3-extra-3: prepending one active residual arc to a generalized
residual path extends the reachable-source witness by one residual step. -/
private lemma residualPathBetweenCons
    (tail head : A → V) (c x : A → ℝ) {u v w : V} {a : ResidualArc A}
    (ha_tail : ResidualArc.tail tail head a = u)
    (ha_head : ResidualArc.head tail head a = v)
    (ha_active : IsActiveResidualArc c x a)
    {P : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x v w P) :
    IsResidualPathBetween tail head c x u w (a :: P) := by
  -- Split on whether the suffix path is empty or already a nonempty realized residual path.
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨hP_nil, hvw⟩
    subst hP_nil
    subst hvw
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
    · intro b hb
      rcases List.mem_singleton.mp hb with rfl
      exact ha_active
    · simpa [ha_tail]
    · simpa [ha_head]
  · rcases hP_path with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
    cases P with
    | nil =>
        exact False.elim (hP_ne rfl)
    | cons b Q =>
        refine Or.inr ?_
        have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
          have hb_tail : some (ResidualArc.tail tail head b) = some v := by
            simpa using hP_head
          injection hb_tail with hb_tail_eq
          simpa [ha_head] using hb_tail_eq.symm
        refine ⟨by simp, ?_, ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact ha_active
          · exact hP_active z hz'
        · simpa [ha_tail]
        · simpa using hP_last
        · exact hP_chain.cons_cons hlink

/-- Helper for Algorithm 4.3.3-extra-3: appending one active residual arc to a generalized
residual path extends the witness by one residual step at the end. -/
private lemma residualPathBetweenSnoc
    (tail head : A → V) (c x : A → ℝ) {u v w : V} {a : ResidualArc A}
    (ha_tail : ResidualArc.tail tail head a = v)
    (ha_head : ResidualArc.head tail head a = w)
    (ha_active : IsActiveResidualArc c x a)
    {P : List (ResidualArc A)}
    (hP : IsResidualPathBetween tail head c x u v P) :
    IsResidualPathBetween tail head c x u w (P ++ [a]) := by
  -- Split on the empty-prefix case, then append the final active arc to the realized suffix.
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨hP_nil, huv⟩
    subst hP_nil
    subst huv
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, List.isChain_singleton _⟩
    · intro b hb
      rcases List.mem_singleton.mp hb with rfl
      exact ha_active
    · simpa [ha_tail]
    · simpa [ha_head]
  · rcases hP_path with ⟨hP_ne, hP_active, hP_head, hP_last, hP_chain⟩
    refine Or.inr ?_
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hP_active b hb
      · rcases List.mem_singleton.mp hb with rfl
        exact ha_active
    · simpa [List.head?_append_of_ne_nil P hP_ne] using hP_head
    · have hlast : (P ++ [a]).getLast? = some a := by
        simpa using List.getLast?_append_cons P a ([] : List (ResidualArc A))
      simpa [hlast, ha_head]
    · refine hP_chain.append (List.isChain_singleton _) ?_
      intro b hb_last z hz_head
      have hz_eq : z = a := by
        simpa using hz_head.symm
      subst hz_eq
      rcases List.mem_getLast?_eq_getLast hb_last with ⟨hP_ne', rfl⟩
      have hlast_head :
          ResidualArc.head tail head (P.getLast hP_ne') = v := by
        have :
            some (ResidualArc.head tail head (P.getLast hP_ne')) = some v := by
          simpa [List.getLast?_eq_getLast_of_ne_nil hP_ne'] using hP_last
        exact Option.some.inj this
      simpa [ha_tail] using hlast_head

/-- Helper for Algorithm 4.3.3-extra-3: every realized residual path yields a residual
`TransGen` witness between the same endpoints. -/
private lemma residualTransGenOfResidualPath
    (tail head : A → V) (c x : A → ℝ) {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    Relation.TransGen (ResidualStep tail head c x) u v := by
  -- Follow the realized residual path one arc at a time and turn each active arc into a step.
  induction P generalizing u with
  | nil =>
      exact False.elim (hP.1 rfl)
  | cons a P ih =>
      rcases hP with ⟨_, hP_active, hP_head, hP_last, hP_chain⟩
      have ha_step :
          ResidualStep tail head c x
            (ResidualArc.tail tail head a) (ResidualArc.head tail head a) := by
        exact ⟨a, hP_active a (by simp), rfl, rfl⟩
      cases P with
      | nil =>
          have hu : ResidualArc.tail tail head a = u := by
            simpa using hP_head
          have hv : ResidualArc.head tail head a = v := by
            simpa using hP_last
          exact Relation.TransGen.single (by simpa [hu, hv] using ha_step)
      | cons b Q =>
          have hlink : ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            exact hP_chain.rel_head
          have htail_active :
              ∀ z ∈ b :: Q, IsActiveResidualArc c x z := by
            intro z hz
            exact hP_active z (by simp [hz])
          have htail_path :
              IsResidualSTPath tail head c x (ResidualArc.tail tail head b) v (b :: Q) := by
            refine ⟨by simp, htail_active, by simp, hP_last, hP_chain.tail⟩
          have hu : ResidualArc.tail tail head a = u := by
            simpa using hP_head
          have htail_trans :
              Relation.TransGen (ResidualStep tail head c x)
                (ResidualArc.tail tail head b) v := ih htail_path
          have hhead_trans :
              Relation.TransGen (ResidualStep tail head c x)
                (ResidualArc.head tail head a) v := by
            simpa [hlink] using htail_trans
          exact Relation.TransGen.head (by simpa [hu] using ha_step) hhead_trans

end AlgorithmProofHelpers

section AugmentationValueHelpers

variable {V A : Type}
variable [Fintype A] [DecidableEq A] [DecidableEq V]

/-- Helper for Algorithm 4.3.3-extra-3: augmenting a flow along one residual arc changes only the
underlying original arc, with the sign dictated by the residual orientation. -/
private def augmentResidualArcFlow
    (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) : A → ℝ :=
  fun e ↦ x e + if a.edge = e then
    match a.orientation with
    | .forward => ε
    | .backward => -ε
  else 0

/-- Helper for Algorithm 4.3.3-extra-3: the signed path incidence at a vertex is the number of
departures minus the number of arrivals along the realized residual path. -/
private def pathIncidence
    (tail head : A → V) (P : List (ResidualArc A)) (v : V) : ℝ :=
  ((P.countP fun a ↦ ResidualArc.tail tail head a = v : ℕ) : ℝ) -
    (((P.countP fun a ↦ ResidualArc.head tail head a = v : ℕ) : ℝ))

/-- Helper for Algorithm 4.3.3-extra-3: a singleton delta sum over a finite arc set isolates the
changed original arc and vanishes away from it. -/
private lemma sumSingleEdgeDelta
    (S : Finset A) (a : A) (δ : ℝ) :
    Finset.sum S (fun e ↦ if a = e then δ else (0 : ℝ)) = if a ∈ S then δ else 0 := by
  -- Only the summand indexed by `a` can contribute to the finite sum.
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

/-- Helper for Algorithm 4.3.3-extra-3: the whole-path augmentation can be peeled into the first
residual step followed by augmentation along the remaining suffix. -/
private lemma augmentFlowCons
    (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (P : List (ResidualArc A)) :
    augment_flow x ε (a :: P) = augment_flow (augmentResidualArcFlow x ε a) ε P := by
  -- Expand both sides on each edge and compare the resulting count formulas.
  cases a with
  | mk edge orientation =>
      ext e
      by_cases he : edge = e
      · subst he
        cases orientation <;>
          simp [augment_flow, augmentResidualArcFlow, residual_forward_use_count,
            residual_backward_use_count, List.countP_cons]
          <;> ring_nf
      · cases orientation <;>
          simp [augment_flow, augmentResidualArcFlow, residual_forward_use_count,
            residual_backward_use_count, he]

/-- Helper for Algorithm 4.3.3-extra-3: the signed path incidence splits into the first residual
step contribution plus the incidence of the remaining suffix. -/
private lemma pathIncidenceCons
    (tail head : A → V) (a : ResidualArc A) (P : List (ResidualArc A)) (v : V) :
    pathIncidence tail head (a :: P) v =
      (((if ResidualArc.tail tail head a = v then (1 : ℝ) else 0) -
          (if ResidualArc.head tail head a = v then (1 : ℝ) else 0))) +
        pathIncidence tail head P v := by
  -- Expanding the two count terms at the head of the list exposes the endpoint delta.
  by_cases htail : ResidualArc.tail tail head a = v
  · by_cases hhead : ResidualArc.head tail head a = v
    · simp [pathIncidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
      ring_nf
    · simp [pathIncidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
      ring_nf
  · by_cases hhead : ResidualArc.head tail head a = v
    · simp [pathIncidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]
    · simp [pathIncidence, htail, hhead, sub_eq_add_neg, add_comm, add_assoc]

/-- Helper for Algorithm 4.3.3-extra-3: a one-step residual augmentation changes the outgoing
flow at a vertex only when that vertex is the original tail of the changed arc. -/
private lemma outgoingFlow_augmentResidualArcFlow
    (tail : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    outgoing_flow tail (augmentResidualArcFlow x ε a) v =
      outgoing_flow tail x v +
        if tail a.edge = v then
          match a.orientation with
          | .forward => ε
          | .backward => -ε
        else 0 := by
  -- Rewrite outgoing flow as a finite sum over the outgoing fiber and isolate the changed arc.
  rw [outgoing_flow_eq_sum_outgoing_arcs, outgoing_flow_eq_sum_outgoing_arcs]
  unfold augmentResidualArcFlow
  rw [Finset.sum_add_distrib]
  congr 1
  simpa [mem_outgoing_arcs_iff] using
    (sumSingleEdgeDelta (S := outgoing_arcs tail v) (a := a.edge)
      (δ := match a.orientation with
        | .forward => ε
        | .backward => -ε))

/-- Helper for Algorithm 4.3.3-extra-3: a one-step residual augmentation changes the incoming
flow at a vertex only when that vertex is the original head of the changed arc. -/
private lemma incomingFlow_augmentResidualArcFlow
    (head : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    incoming_flow head (augmentResidualArcFlow x ε a) v =
      incoming_flow head x v +
        if head a.edge = v then
          match a.orientation with
          | .forward => ε
          | .backward => -ε
        else 0 := by
  -- Rewrite incoming flow as a finite sum over the incoming fiber and isolate the changed arc.
  rw [incoming_flow_eq_sum_incoming_arcs, incoming_flow_eq_sum_incoming_arcs]
  unfold augmentResidualArcFlow
  rw [Finset.sum_add_distrib]
  congr 1
  simpa [mem_incoming_arcs_iff] using
    (sumSingleEdgeDelta (S := incoming_arcs head v) (a := a.edge)
      (δ := match a.orientation with
        | .forward => ε
        | .backward => -ε))

/-- Helper for Algorithm 4.3.3-extra-3: a one-step residual augmentation changes the net outflow
by `+ε` at the residual tail, `-ε` at the residual head, and `0` elsewhere. -/
private lemma netOutflow_augmentResidualArcFlow
    (tail head : A → V) (x : A → ℝ) (ε : ℝ) (a : ResidualArc A) (v : V) :
    outgoing_flow tail (augmentResidualArcFlow x ε a) v -
        incoming_flow head (augmentResidualArcFlow x ε a) v =
      (outgoing_flow tail x v - incoming_flow head x v) +
        ε * (((if ResidualArc.tail tail head a = v then (1 : ℝ) else 0) -
          (if ResidualArc.head tail head a = v then (1 : ℝ) else 0))) := by
  -- Split by residual orientation and simplify the endpoint bookkeeping explicitly.
  cases a with
  | mk edge orientation =>
      cases orientation
      · rw [outgoingFlow_augmentResidualArcFlow, incomingFlow_augmentResidualArcFlow]
        by_cases htail : tail edge = v
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
      · rw [outgoingFlow_augmentResidualArcFlow, incomingFlow_augmentResidualArcFlow]
        by_cases htail : tail edge = v
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
        · by_cases hhead : head edge = v
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]
            ring_nf
          · simp [ResidualArc.tail, ResidualArc.head, sub_eq_add_neg, htail, hhead]

/-- Helper for Algorithm 4.3.3-extra-3: augmenting along a realized residual path changes the
net outflow by `ε` times the signed path incidence. -/
private lemma augmentFlowNetOutflowEqAddPathIncidence
    (tail head : A → V) (x : A → ℝ) (ε : ℝ) (P : List (ResidualArc A)) (v : V) :
    outgoing_flow tail (augment_flow x ε P) v - incoming_flow head (augment_flow x ε P) v =
      (outgoing_flow tail x v - incoming_flow head x v) + ε * pathIncidence tail head P v := by
  -- Induct on the realized path and peel off one residual step at a time.
  revert x
  induction P with
  | nil =>
      intro x
      simp [augment_flow, residual_forward_use_count, residual_backward_use_count, pathIncidence]
  | cons a P ih =>
      intro x
      rw [augmentFlowCons, ih (augmentResidualArcFlow x ε a),
        netOutflow_augmentResidualArcFlow, pathIncidenceCons]
      ring_nf

/-- Helper for Algorithm 4.3.3-extra-3: the signed incidence of a realized residual path is `+1`
at the source, `-1` at the sink, and `0` elsewhere. -/
private lemma residualPathIncidenceEqEndpoints
    (tail head : A → V) (c x : A → ℝ) (w : V)
    {u v : V} {P : List (ResidualArc A)}
    (hP : IsResidualSTPath tail head c x u v P) :
    pathIncidence tail head P w =
      (if u = w then (1 : ℝ) else 0) - (if v = w then (1 : ℝ) else 0) := by
  -- Induct on the residual path and telescope the local endpoint contributions.
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
          simp [pathIncidence, hu, hv]
      | cons b Q =>
          have hlink :
              ResidualArc.head tail head a = ResidualArc.tail tail head b := by
            simpa using (List.isChain_cons_cons.mp hP_chain).1
          have htailPath :
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
            pathIncidence tail head (a :: b :: Q) w =
                (((if u = w then (1 : ℝ) else 0) -
                    (if ResidualArc.tail tail head b = w then (1 : ℝ) else 0))) +
                  pathIncidence tail head (b :: Q) w := by
                    rw [pathIncidenceCons]
                    simp [hu, hlink]
            _ = (if u = w then (1 : ℝ) else 0) - (if v = w then (1 : ℝ) else 0) := by
              rw [ih htailPath]
              ring

/-- Helper for Algorithm 4.3.3-extra-3: augmenting a feasible flow along a residual `s,t`-path by
its bottleneck value increases the flow value by exactly that augmentation amount. -/
private lemma stFlowValue_augmentFlow_eq_add_ofBottleneck
    (tail head : A → V) (s t : V) (c x : A → ℝ)
    (hst : s ≠ t) (hx : IsFeasibleSTFlow tail head s t c x)
    {P : List (ResidualArc A)} {ε : ℝ}
    (hε : IsBottleneckAugmentation tail head s t c x P ε) :
    st_flow_value tail head s (augment_flow x ε P) =
      st_flow_value tail head s x + ε := by
  -- The residual path contributes signed incidence `1` at the source, so the source value rises by `ε`.
  have hincS : pathIncidence tail head P s = 1 := by
    have hts : t ≠ s := by
      intro hts
      exact hst hts.symm
    simpa [hts] using residualPathIncidenceEqEndpoints tail head c x s hε.1
  have hnetS :=
    augmentFlowNetOutflowEqAddPathIncidence tail head x ε P s
  rw [hincS] at hnetS
  simpa [st_flow_value] using hnetS

end AugmentationValueHelpers

section Termination

variable {V A : Type}
variable [Fintype V] [Fintype A] [DecidableEq A]

/-- If an augmenting-paths algorithm terminates, then the terminal flow is a maximum feasible
`s,t`-flow. -/
theorem augmenting_paths_algorithm_maximum_flow_at_termination
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths)
    {k : ℕ} (hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k) (hst : s ≠ t) :
    IsMaximumSTFlow tail head s t c (flows k) := by
  exact
    (isMaximumSTFlow_iff_noResidualSTPath tail head c (flows k) s t hst
      (halg.feasible k)).2 hk

/-- Helper for Algorithm 4.3.3-extra-3: an active residual arc has scaled integral residual
capacity whenever the current flow and capacities share the common denominator `D`. -/
private lemma activeResidualArc_scaledCapacity
    (tail head : A → V) (s t : V) (c x : A → ℝ) (D : ℕ)
    (hx : IsFeasibleSTFlow tail head s t c x)
    (hD : IsCommonPositiveCapacityDenominator c D)
    (hxScaled : ∀ e, ∃ z : ℤ, ((D : ℝ) * x e) = z)
    {a : ResidualArc A} (ha : IsActiveResidualArc c x a) :
    ∃ z : ℤ, 0 < z ∧ ((D : ℝ) * residual_arc_capacity c x a) = z := by
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hD.1
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
  rcases a with ⟨e, orientation⟩
  cases orientation with
  | forward =>
      have hx_nonneg : 0 ≤ x e := hx.nonneg e
      have hslack_pos : 0 < c e - x e := by
        simpa [IsActiveResidualArc, residual_arc_capacity] using ha
      have hc_pos : 0 < c e := by
        linarith
      rcases hD.2 e hc_pos with ⟨m, hm⟩
      rcases hxScaled e with ⟨zx, hzx⟩
      have hDc : (D : ℝ) * c e = m := by
        rw [hm]
        field_simp [hDne]
      refine ⟨m - zx, ?_, ?_⟩
      · have hscaled_pos : 0 < (D : ℝ) * residual_arc_capacity c x ⟨e, .forward⟩ := by
          simpa [residual_arc_capacity] using mul_pos hDpos hslack_pos
        have hscaled_eq :
            ((m - zx : ℤ) : ℝ) = (D : ℝ) * residual_arc_capacity c x ⟨e, .forward⟩ := by
          calc
            ((m - zx : ℤ) : ℝ) = (m : ℝ) - (zx : ℝ) := by norm_num
            _ = (D : ℝ) * c e - (D : ℝ) * x e := by rw [hDc, hzx]
            _ = (D : ℝ) * residual_arc_capacity c x ⟨e, .forward⟩ := by
                  simp [residual_arc_capacity]
                  ring
        have : 0 < ((m - zx : ℤ) : ℝ) := by
          rwa [hscaled_eq]
        exact_mod_cast this
      · have hscaled_eq :
            ((m - zx : ℤ) : ℝ) = (D : ℝ) * residual_arc_capacity c x ⟨e, .forward⟩ := by
          calc
            ((m - zx : ℤ) : ℝ) = (m : ℝ) - (zx : ℝ) := by norm_num
            _ = (D : ℝ) * c e - (D : ℝ) * x e := by rw [hDc, hzx]
            _ = (D : ℝ) * residual_arc_capacity c x ⟨e, .forward⟩ := by
                  simp [residual_arc_capacity]
                  ring
        simpa [hscaled_eq]
  | backward =>
      rcases hxScaled e with ⟨zx, hzx⟩
      refine ⟨zx, ?_, ?_⟩
      · have hscaled_pos : 0 < (D : ℝ) * residual_arc_capacity c x ⟨e, .backward⟩ := by
          simpa [IsActiveResidualArc, residual_arc_capacity] using mul_pos hDpos ha
        have : 0 < (zx : ℝ) := by
          simpa [residual_arc_capacity, hzx] using hscaled_pos
        exact_mod_cast this
      · simpa [residual_arc_capacity] using hzx

/-- Helper for Algorithm 4.3.3-extra-3: the bottleneck augmentation is at least `1 / D`, and
augmenting preserves the scaled-integrality invariant with denominator `D`. -/
private lemma bottleneckLowerBoundAndScaledIntegrality_next
    (tail head : A → V) (s t : V) (c x : A → ℝ) (D : ℕ)
    (hx : IsFeasibleSTFlow tail head s t c x)
    (hD : IsCommonPositiveCapacityDenominator c D)
    (hxScaled : ∀ e, ∃ z : ℤ, ((D : ℝ) * x e) = z)
    {P : List (ResidualArc A)} {ε : ℝ}
    (hε : IsBottleneckAugmentation tail head s t c x P ε) :
    (1 / (D : ℝ)) ≤ ε ∧
      ∀ e, ∃ z : ℤ, ((D : ℝ) * augment_flow x ε P e) = z := by
  rcases hε with ⟨hP, _, a, haP, hEq⟩
  have ha_active : IsActiveResidualArc c x a := hP.2.1 a haP
  rcases activeResidualArc_scaledCapacity tail head s t c x D hx hD hxScaled ha_active with
    ⟨zε, hzε_pos, hzε_cap⟩
  have hzε : ((D : ℝ) * ε) = zε := by
    simpa [hEq] using hzε_cap
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hD.1
  constructor
  · have hone_le : (1 : ℝ) ≤ (D : ℝ) * ε := by
      have hone_le_int : (1 : ℤ) ≤ zε := by
        omega
      have hone_le_real : (1 : ℝ) ≤ (zε : ℝ) := by
        exact_mod_cast hone_le_int
      simpa [hzε] using hone_le_real
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
    field_simp [hDne] at hone_le ⊢
    simpa [mul_comm] using hone_le
  · intro e
    rcases hxScaled e with ⟨zx, hzx⟩
    refine
      ⟨zx + zε * (residual_forward_use_count P e : ℤ) -
          zε * (residual_backward_use_count P e : ℤ), ?_⟩
    calc
      (D : ℝ) * augment_flow x ε P e =
          (D : ℝ) * x e + ((D : ℝ) * ε) * (residual_forward_use_count P e : ℝ) -
            ((D : ℝ) * ε) * (residual_backward_use_count P e : ℝ) := by
              simp [augment_flow]
              ring
      _ = (zx : ℝ) + (zε : ℝ) * (residual_forward_use_count P e : ℝ) -
            (zε : ℝ) * (residual_backward_use_count P e : ℝ) := by
              rw [hzx, hzε]
      _ =
          ((zx + zε * (residual_forward_use_count P e : ℤ) -
              zε * (residual_backward_use_count P e : ℤ) : ℤ) : ℝ) := by
              push_cast
              ring

/-- Helper for Algorithm 4.3.3-extra-3: the source value of a feasible flow is bounded by the
total capacity of the original arcs leaving the source. -/
private lemma stFlowValue_le_totalOutgoingCapacity
    (tail head : A → V) (s t : V) (c x : A → ℝ)
    (hx : IsFeasibleSTFlow tail head s t c x) :
    st_flow_value tail head s x ≤
      Finset.sum (outgoing_arcs tail s) c := by
  classical
  -- Bound each outgoing source arc by its capacity and discard the nonnegative incoming term.
  rw [st_flow_value, outgoing_flow_eq_sum_outgoing_arcs, incoming_flow_eq_sum_incoming_arcs]
  let Out : Finset A := outgoing_arcs tail s
  let In : Finset A := incoming_arcs head s
  have hout_le :
      Finset.sum Out x ≤ Finset.sum Out c := by
    refine Finset.sum_le_sum fun e he ↦ hx.le_capacity e
  have hin_nonneg :
      0 ≤ Finset.sum In x := by
    exact Finset.sum_nonneg fun e he ↦ hx.nonneg e
  calc
    Finset.sum Out x - Finset.sum In x ≤ Finset.sum Out x := by
          exact sub_le_self _ hin_nonneg
    _ ≤ Finset.sum Out c := hout_le

/-- Helper for Algorithm 4.3.3-extra-3: integral capacities admit `D = 1` as a least common
positive denominator. -/
private lemma integralCapacitiesHaveUnitDenominator
    (c : A → ℝ) (hC : IsIntegralSTFlow c) :
    IsLeastCommonPositiveCapacityDenominator c 1 := by
  constructor
  · constructor
    · norm_num
    · intro e he
      rcases hC e with ⟨z, hz⟩
      exact ⟨z, by simpa using hz⟩
  · intro D hD
    exact Nat.succ_le_of_lt hD.1

/-- Helper for Algorithm 4.3.3-extra-3: one bottleneck augmentation of an integral feasible flow
along integral capacities remains integral. -/
private lemma integralAugmentFlow_of_bottleneck
    (tail head : A → V) (s t : V) (c x : A → ℝ)
    (hx : IsFeasibleSTFlow tail head s t c x)
    (hxInt : IsIntegralSTFlow x) (hC : IsIntegralSTFlow c)
    {P : List (ResidualArc A)} {ε : ℝ}
    (hε : IsBottleneckAugmentation tail head s t c x P ε) :
    IsIntegralSTFlow (augment_flow x ε P) := by
  have hUnitCommon : IsCommonPositiveCapacityDenominator c 1 :=
    (integralCapacitiesHaveUnitDenominator c hC).1
  have hxScaled : ∀ e, ∃ z : ℤ, (((1 : ℕ) : ℝ) * x e) = z := by
    intro e
    rcases hxInt e with ⟨z, hz⟩
    exact ⟨z, by simpa using hz⟩
  have hnext :=
    (bottleneckLowerBoundAndScaledIntegrality_next tail head s t c x 1 hx hUnitCommon hxScaled
      hε).2
  intro e
  rcases hnext e with ⟨z, hz⟩
  exact ⟨z, by simpa using hz⟩

/-- If `D` is the least common denominator of the positive capacities, then every
augmenting-paths algorithm terminates. -/
theorem augmenting_paths_algorithm_terminates_of_rational_capacities
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths) (D : ℕ)
    (hD : IsLeastCommonPositiveCapacityDenominator c D) (hst : s ≠ t) :
    ∃ k, AugmentingPathsAlgorithm.StopsAt tail head s t c flows k := by
  classical
  by_contra hstop
  let B : ℝ := Finset.sum (outgoing_arcs tail s) c
  let N : ℕ := ⌊(D : ℝ) * B⌋₊ + 1
  have hDcommon : IsCommonPositiveCapacityDenominator c D := hD.1
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast hDcommon.1
  have hnever : ∀ n, ¬ AugmentingPathsAlgorithm.StopsAt tail head s t c flows n := by
    intro n hn
    exact hstop ⟨n, hn⟩
  have hscaled :
      ∀ n e, ∃ z : ℤ, ((D : ℝ) * flows n e) = z := by
    intro n
    induction n with
    | zero =>
        intro e
        refine ⟨0, ?_⟩
        simp [halg.start_eq_zero]
    | succ n ih =>
        intro e
        rcases halg.step n (hnever n) with ⟨ε, hε, hnext⟩
        have hnextScaled :=
          (bottleneckLowerBoundAndScaledIntegrality_next tail head s t c (flows n) D
            (halg.feasible n) hDcommon (fun a ↦ ih a) hε).2 e
        simpa [hnext] using hnextScaled
  have hvalueLower :
      ∀ n : ℕ, ((n : ℝ) / D) ≤ st_flow_value tail head s (flows n) := by
    intro n
    induction n with
    | zero =>
        simp [halg.start_eq_zero, st_flow_value]
    | succ n ih =>
        rcases halg.step n (hnever n) with ⟨ε, hε, hnext⟩
        have hεlb :
            (1 / (D : ℝ)) ≤ ε :=
          (bottleneckLowerBoundAndScaledIntegrality_next tail head s t c (flows n) D
            (halg.feasible n) hDcommon (fun a ↦ hscaled n a) hε).1
        have hvalue :
            st_flow_value tail head s (flows (n + 1)) =
              st_flow_value tail head s (flows n) + ε := by
          rw [hnext]
          exact stFlowValue_augmentFlow_eq_add_ofBottleneck tail head s t c (flows n) hst
            (halg.feasible n) hε
        have hsum :
            (n : ℝ) / D + 1 / (D : ℝ) ≤ st_flow_value tail head s (flows n) + ε := by
          exact add_le_add ih hεlb
        have hsucc :
            (((n + 1 : ℕ) : ℝ) / D) = (n : ℝ) / D + 1 / (D : ℝ) := by
          calc
            (((n + 1 : ℕ) : ℝ) / D) = ((n : ℝ) + 1) / D := by
              norm_num [Nat.cast_add]
            _ = (n : ℝ) / D + 1 / (D : ℝ) := by
              field_simp [hDpos.ne']
        rw [hvalue, hsucc]
        exact hsum
  have hupper : st_flow_value tail head s (flows N) ≤ B := by
    exact stFlowValue_le_totalOutgoingCapacity tail head s t c (flows N) (halg.feasible N)
  have hB_lt : B < (N : ℝ) / D := by
    have hlt : (D : ℝ) * B < (N : ℝ) := by
      simpa [N] using (Nat.lt_succ_floor ((D : ℝ) * B))
    exact (lt_div_iff₀ hDpos).2 (by simpa [mul_comm] using hlt)
  have hlow_upper : (N : ℝ) / D ≤ B := le_trans (hvalueLower N) hupper
  exact (not_lt_of_ge hlow_upper hB_lt).elim

/-- Algorithm 4.3.3-extra-3. With integral capacities, the augmenting-paths algorithm terminates at
an integral maximum `s,t`-flow. -/
theorem augmenting_paths_algorithm_terminates_with_integral_maximum_flow
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths)
    (hC : IsIntegralSTFlow c) (hst : s ≠ t) :
    ∃ k,
      AugmentingPathsAlgorithm.StopsAt tail head s t c flows k ∧
        IsIntegralMaximumSTFlow tail head s t c (flows k) := by
  classical
  have hUnit : IsLeastCommonPositiveCapacityDenominator c 1 :=
    integralCapacitiesHaveUnitDenominator c hC
  rcases augmenting_paths_algorithm_terminates_of_rational_capacities
      tail head s t c flows paths halg 1 hUnit hst with ⟨k₀, hk₀⟩
  let k : ℕ := Nat.find ⟨k₀, hk₀⟩
  have hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k := Nat.find_spec ⟨k₀, hk₀⟩
  have hkmin :
      ∀ n, n < k → ¬ AugmentingPathsAlgorithm.StopsAt tail head s t c flows n := by
    intro n hn hstop
    exact Nat.find_min (H := ⟨k₀, hk₀⟩) hn hstop
  have hIntegralUpTo :
      ∀ n, n ≤ k → IsIntegralSTFlow (flows n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        intro e
        refine ⟨0, ?_⟩
        simp [halg.start_eq_zero]
    | succ n ih =>
        intro hnk
        have hlt : n < k := Nat.lt_of_succ_le hnk
        have hInt : IsIntegralSTFlow (flows n) := ih (Nat.le_of_lt hlt)
        rcases halg.step n (hkmin n hlt) with ⟨ε, hε, hnext⟩
        have hnextInt :
            IsIntegralSTFlow (augment_flow (flows n) ε (paths n)) :=
          integralAugmentFlow_of_bottleneck tail head s t c (flows n)
            (halg.feasible n) hInt hC hε
        simpa [hnext] using hnextInt
  refine ⟨k, hk, ?_⟩
  refine
    { isMaximumSTFlow :=
        augmenting_paths_algorithm_maximum_flow_at_termination
          tail head s t c flows paths halg hk hst
      isIntegralSTFlow := hIntegralUpTo k le_rfl }

end Termination

section ReachableCut

variable {V A : Type}
variable [Fintype V] [Fintype A] [DecidableEq A]

/-- The vertices reachable from `s` in the residual digraph of the current flow. This uses the
chapter's generalized residual-path predicate, so the zero-length path keeps `s` on the reachable
side. -/
def reachableFromSource
    (tail head : A → V) (c x : A → ℝ) (s : V) : Set V :=
  {v | ∃ P : List (ResidualArc A), IsResidualPathBetween tail head c x s v P}

omit [Fintype V] [Fintype A] [DecidableEq A] in
@[simp] theorem source_mem_reachableFromSource
    (tail head : A → V) (c x : A → ℝ) (s : V) :
    s ∈ reachableFromSource tail head c x s := by
  exact ⟨[], is_residual_path_between_nil tail head c x s⟩

/-- Helper for Algorithm 4.3.3-extra-3: reachability from `s` is closed under one residual step
when reachability is expressed by generalized residual paths. -/
private lemma reachableFromSource_mem_of_step
    (tail head : A → V) (c x : A → ℝ) (s u v : V)
    (hu : u ∈ reachableFromSource tail head c x s)
    (hstep : ResidualStep tail head c x u v) :
    v ∈ reachableFromSource tail head c x s := by
  -- Extend any realized generalized path to `u` by the concrete residual step from `u` to `v`.
  rcases hu with ⟨P, hP⟩
  rcases hstep with ⟨a, ha_active, ha_tail, ha_head⟩
  exact ⟨P ++ [a], residualPathBetweenSnoc tail head c x ha_tail ha_head ha_active hP⟩

/-- Helper for Algorithm 4.3.3-extra-3: a terminal stage excludes the sink from the reachable
source side, because any generalized residual path to `t` would contradict `StopsAt`. -/
private lemma target_not_mem_reachableFromSource_at_termination
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) {k : ℕ}
    (hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k) (hst : s ≠ t) :
    t ∉ reachableFromSource tail head c (flows k) s := by
  -- The generalized predicate only adds the empty path when the endpoints coincide.
  intro ht
  rcases ht with ⟨P, hP⟩
  rcases hP with hP_nil | hP_path
  · rcases hP_nil with ⟨hP_nil, hst_eq⟩
    subst hP_nil
    exact hst hst_eq
  · exact hk (residualTransGenOfResidualPath tail head c (flows k) hP_path)

/-- At a terminal stage, the residual-reachable vertices form an `s,t`-cut side. -/
theorem reachableFromSource_isSTCut_at_termination
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths)
    {k : ℕ} (hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k) (hst : s ≠ t) :
    IsSTCutSide s t (reachableFromSource tail head c (flows k) s) := by
  constructor
  · -- The empty generalized path keeps the source on the reachable side.
    exact source_mem_reachableFromSource tail head c (flows k) s
  · -- Termination excludes any realized residual path from `s` to `t`.
    exact target_not_mem_reachableFromSource_at_termination tail head s t c flows hk hst

/-- At termination, the reachable-source cut attains the value of the terminal flow. -/
theorem cutCapacity_reachableFromSource_eq_flowValue_at_termination
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths)
    {k : ℕ} (hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k) (hst : s ≠ t) :
    cut_capacity tail head c (reachableFromSource tail head c (flows k) s) =
      st_flow_value tail head s (flows k) := by
  let S := reachableFromSource tail head c (flows k) s
  have hcut : IsSTCutSide s t S := by
    simpa [S] using
      reachableFromSource_isSTCut_at_termination tail head s t c flows paths halg hk hst
  have htight :
      (∀ e ∈ δ⁺[tail, head] S, flows k e = c e) ∧
        ∀ e ∈ δ⁻[tail, head] S, flows k e = 0 := by
    constructor
    · intro e he
      rcases mem_outgoing_cut_arcs_iff.mp he with ⟨htailS, hheadS⟩
      have hnot_forward : ¬ flows k e < c e := by
        intro hlt
        have hstep : ResidualStep tail head c (flows k) (tail e) (head e) := by
          exact (residualStep_iff tail head c (flows k) (tail e) (head e)).2
            (Or.inl ⟨e, rfl, rfl, hlt⟩)
        have hreach : head e ∈ S :=
          reachableFromSource_mem_of_step tail head c (flows k) s (tail e) (head e) htailS hstep
        exact hheadS hreach
      linarith [halg.feasible k |>.le_capacity e]
    · intro e he
      rcases mem_incoming_cut_arcs_iff.mp he with ⟨htailS, hheadS⟩
      have hnot_backward : ¬ 0 < flows k e := by
        intro hpos
        have hstep : ResidualStep tail head c (flows k) (head e) (tail e) := by
          exact (residualStep_iff tail head c (flows k) (head e) (tail e)).2
            (Or.inr ⟨e, rfl, rfl, hpos⟩)
        have hreach : tail e ∈ S :=
          reachableFromSource_mem_of_step tail head c (flows k) s (head e) (tail e) hheadS hstep
        exact htailS hreach
      linarith [halg.feasible k |>.nonneg e]
  -- Lemma 4.14 converts the tight cut conditions into equality of value and cut capacity.
  have heq :
      st_flow_value tail head s (flows k) = cut_capacity tail head c S := by
    exact (flow_value_eq_cut_capacity_iff tail head c (flows k) s t S (halg.feasible k) hcut).2
      htight
  simpa [S] using heq.symm

/-- At termination, the residual-reachable vertices form a minimum `s,t`-cut side. -/
theorem reachableFromSource_isMinimumSTCut_at_termination
    (tail head : A → V) (s t : V) (c : A → ℝ)
    (flows : ℕ → A → ℝ) (paths : ℕ → List (ResidualArc A))
    (halg : IsAugmentingPathsAlgorithm tail head s t c flows paths)
    {k : ℕ} (hk : AugmentingPathsAlgorithm.StopsAt tail head s t c flows k) (hst : s ≠ t) :
    IsMinimumSTCut tail head c s t (reachableFromSource tail head c (flows k) s) := by
  let S := reachableFromSource tail head c (flows k) s
  have hcut :
      IsSTCutSide s t S := by
    simpa [S] using
      reachableFromSource_isSTCut_at_termination
        tail head s t c flows paths halg hk hst
  have heq :
      st_flow_value tail head s (flows k) = cut_capacity tail head c S := by
    symm
    simpa [S] using
      cutCapacity_reachableFromSource_eq_flowValue_at_termination
        tail head s t c flows paths halg hk hst
  exact flow_cut_eq_implies_isMinimumSTCut
    tail head c (flows k) s t S (halg.feasible k) hcut heq

end ReachableCut

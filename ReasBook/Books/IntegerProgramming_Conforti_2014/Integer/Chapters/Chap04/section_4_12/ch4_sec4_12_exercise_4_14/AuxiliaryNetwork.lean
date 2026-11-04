/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_3.ch4_sec4_3_3_definition_4_3_3_extra_1
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators

namespace Exercise_4_14_Scratch

variable {V A : Type} [Fintype A]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: a subtype-indexed sum
selected by equality with a known member reduces to that member's value. -/
private lemma sumIteSubtypeValue {α M : Type} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (a : α) (ha : a ∈ s) (g : {x // x ∈ s} → M) :
    (∑ x, if a = x.1 then g x else 0) = g ⟨a, ha⟩ := by
  -- Isolate the known subtype element and show every distinct index has a different value.
  rw [Fintype.sum_eq_single ⟨a, ha⟩]
  · simp
  · intro x hxa
    have hne : a ≠ x.1 := by
      intro hax
      apply hxa
      exact Subtype.ext hax.symm
    simp [hne]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: the finite set of
vertices incident to an arc. -/
private abbrev endpointSupport (tail head : A → V) : Finset V :=
  circuit_vertices tail head Finset.univ

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: an incident vertex bundled
with its support proof. -/
private abbrev SupportVertex (tail head : A → V) := {v : V // v ∈ endpointSupport tail head}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: the imbalance of the lower
arc bounds at a vertex. -/
private def lowerBoundImbalance (tail head : A → V) (lower : A → ℝ) (v : V) : ℝ :=
  incoming_flow head lower v - outgoing_flow tail lower v

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: every arc tail belongs to
the endpoint support. -/
private lemma tailMemEndpointSupport (tail head : A → V) (a : A) :
    tail a ∈ endpointSupport tail head := by
  classical
  change tail a ∈ circuit_vertices tail head Finset.univ
  rw [mem_circuit_vertices_iff]
  exact ⟨a, Finset.mem_univ a, Or.inl rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: every arc head belongs to
the endpoint support. -/
private lemma headMemEndpointSupport (tail head : A → V) (a : A) :
    head a ∈ endpointSupport tail head := by
  classical
  change head a ∈ circuit_vertices tail head Finset.univ
  rw [mem_circuit_vertices_iff]
  exact ⟨a, Finset.mem_univ a, Or.inr rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: vertices of the auxiliary
source-sink network. -/
private inductive AuxiliaryVertex (V : Type)
  | source
  | sink
  | node (v : V)
deriving DecidableEq

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: arcs of the auxiliary
source-sink network. -/
private abbrev AuxiliaryArc (tail head : A → V) :=
  A ⊕ (SupportVertex tail head ⊕ SupportVertex tail head)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: the auxiliary arc from the
new source to a supported vertex. -/
private def sourceArc {tail head : A → V} (v : SupportVertex tail head) :
    AuxiliaryArc tail head :=
  Sum.inr <| Sum.inl v

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: the auxiliary arc from a
supported vertex to the new sink. -/
private def sinkArc {tail head : A → V} (v : SupportVertex tail head) :
    AuxiliaryArc tail head :=
  Sum.inr <| Sum.inr v

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: an original arc viewed in
the auxiliary network. -/
private def originalArc {tail head : A → V} (a : A) : AuxiliaryArc tail head :=
  Sum.inl a

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: tail map of the auxiliary
network. -/
private def auxiliaryTail (tail head : A → V) : AuxiliaryArc tail head → AuxiliaryVertex V
  | Sum.inl a => .node (tail a)
  | Sum.inr (Sum.inl _) => .source
  | Sum.inr (Sum.inr v) => .node v.1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: head map of the auxiliary
network. -/
private def auxiliaryHead (tail head : A → V) : AuxiliaryArc tail head → AuxiliaryVertex V
  | Sum.inl a => .node (head a)
  | Sum.inr (Sum.inl v) => .node v.1
  | Sum.inr (Sum.inr _) => .sink

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: capacity on an auxiliary
arc from the source. -/
private def sourceCapacity (tail head : A → V) (lower : A → ℝ)
    (v : SupportVertex tail head) : ℝ :=
  max (lowerBoundImbalance tail head lower v.1) 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: capacity on an auxiliary
arc to the sink. -/
private def sinkCapacity (tail head : A → V) (lower : A → ℝ)
    (v : SupportVertex tail head) : ℝ :=
  max (-lowerBoundImbalance tail head lower v.1) 0

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: capacity function of the
auxiliary network. -/
private def auxiliaryCapacity (tail head : A → V) (lower upper : A → ℝ) :
    AuxiliaryArc tail head → ℝ
  | Sum.inl a => upper a - lower a
  | Sum.inr (Sum.inl v) => sourceCapacity tail head lower v
  | Sum.inr (Sum.inr v) => sinkCapacity tail head lower v

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: total capacity leaving the
new source. -/
private def totalSourceCapacity (tail head : A → V) (lower : A → ℝ) : ℝ :=
  Finset.sum (endpointSupport tail head).attach (sourceCapacity tail head lower)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: supported original vertices
on an auxiliary cut side. -/
private def auxiliaryCutVertices
    (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset V :=
  let _ : DecidablePred fun v : V ↦ AuxiliaryVertex.node v ∈ S := Classical.decPred _
  (endpointSupport tail head).filter fun v ↦ AuxiliaryVertex.node v ∈ S

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: supported vertices outside
an auxiliary cut side. -/
private def sourceSideVertices
    (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset (SupportVertex tail head) :=
  let _ : DecidablePred fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1 ∉ S :=
    Classical.decPred _
  (endpointSupport tail head).attach.filter fun v ↦ AuxiliaryVertex.node v.1 ∉ S

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: supported vertices inside
an auxiliary cut side. -/
private def sinkSideVertices
    (tail head : A → V) (S : Set (AuxiliaryVertex V)) : Finset (SupportVertex tail head) :=
  let _ : DecidablePred fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1 ∈ S :=
    Classical.decPred _
  (endpointSupport tail head).attach.filter fun v ↦ AuxiliaryVertex.node v.1 ∈ S

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: source capacity minus sink
capacity equals the lower-bound imbalance. -/
private lemma sourceCapacitySubSinkCapacity
    (tail head : A → V) (lower : A → ℝ) (v : SupportVertex tail head) :
    sourceCapacity tail head lower v - sinkCapacity tail head lower v =
      lowerBoundImbalance tail head lower v.1 := by
  by_cases h : 0 ≤ lowerBoundImbalance tail head lower v.1
  · have hneg : -lowerBoundImbalance tail head lower v.1 ≤ 0 := by
      linarith
    simp [sourceCapacity, sinkCapacity, h, hneg]
  · have hlt : lowerBoundImbalance tail head lower v.1 < 0 := lt_of_not_ge h
    have hle : lowerBoundImbalance tail head lower v.1 ≤ 0 := le_of_lt hlt
    have hpos : 0 ≤ -lowerBoundImbalance tail head lower v.1 := by
      linarith
    simp [sourceCapacity, sinkCapacity, hle, hpos]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: total lower-bound imbalance
on a finite vertex side is incoming lower flow minus outgoing lower flow. -/
private lemma sumLowerBoundImbalanceEqCutDifference
    (tail head : A → V) (lower : A → ℝ) (X : Finset V) :
    Finset.sum X (lowerBoundImbalance tail head lower) =
      Finset.sum (δ⁻[tail, head] X) lower - Finset.sum (δ⁺[tail, head] X) lower := by
  classical
  let internal : Finset A := Finset.univ.filter fun a ↦ tail a ∈ X ∧ head a ∈ X
  have hIncoming :
      Finset.sum X (incoming_flow head lower) =
        Finset.sum (Finset.univ.filter fun a ↦ head a ∈ X) lower := by
    -- Reindex incoming flow by the head fibers over `X`.
    calc
      Finset.sum X (incoming_flow head lower) =
          Finset.sum X
            (fun v ↦ Finset.sum (Finset.univ.filter fun a ↦ head a = v) lower) := by
            simp [incoming_flow]
      _ = Finset.sum (Finset.univ.filter fun a ↦ head a ∈ X) lower := by
            simpa using Finset.sum_fiberwise_eq_sum_filter
              (Finset.univ : Finset A) X head lower
  have hOutgoing :
      Finset.sum X (outgoing_flow tail lower) =
        Finset.sum (Finset.univ.filter fun a ↦ tail a ∈ X) lower := by
    -- Reindex outgoing flow by the tail fibers over `X`.
    calc
      Finset.sum X (outgoing_flow tail lower) =
          Finset.sum X
            (fun v ↦ Finset.sum (Finset.univ.filter fun a ↦ tail a = v) lower) := by
            simp [outgoing_flow]
      _ = Finset.sum (Finset.univ.filter fun a ↦ tail a ∈ X) lower := by
            simpa using Finset.sum_fiberwise_eq_sum_filter
              (Finset.univ : Finset A) X tail lower
  have hIncomingSplit :
      Finset.sum (Finset.univ.filter fun a ↦ head a ∈ X) lower =
        Finset.sum internal lower + Finset.sum (δ⁻[tail, head] X) lower := by
    -- Separate internal arcs from arcs entering `X`.
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun a ↦ head a ∈ X)
      (p := fun a ↦ tail a ∈ X) (f := lower)]
    simp [internal, incoming_cut_arcs, Finset.filter_filter, and_comm]
  have hOutgoingSplit :
      Finset.sum (Finset.univ.filter fun a ↦ tail a ∈ X) lower =
        Finset.sum internal lower + Finset.sum (δ⁺[tail, head] X) lower := by
    -- Separate internal arcs from arcs leaving `X`.
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter fun a ↦ tail a ∈ X)
      (p := fun a ↦ head a ∈ X) (f := lower)]
    simp [internal, outgoing_cut_arcs, Finset.filter_filter]
  -- Cancel the internal-arc contribution after rewriting both vertex sums.
  simp only [lowerBoundImbalance, Finset.sum_sub_distrib]
  rw [hIncoming, hOutgoing, hIncomingSplit, hOutgoingSplit]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: auxiliary inflow at an
original node is original inflow plus its source-arc flow. -/
private lemma auxiliaryNodeIncomingFlowEq
    (tail head : A → V) (f : AuxiliaryArc tail head → ℝ) (v : V)
    (hv : v ∈ endpointSupport tail head) :
    incoming_flow (auxiliaryHead tail head) f (AuxiliaryVertex.node v) =
      incoming_flow head (fun a ↦ f (originalArc a)) v + f (sourceArc ⟨v, hv⟩) := by
  classical
  -- Split the auxiliary arc type; only original arcs and the unique source arc enter `node v`.
  simpa [incoming_flow, Finset.sum_filter, Fintype.sum_sum_type, auxiliaryHead,
    originalArc, sourceArc, eq_comm] using
    (sumIteSubtypeValue (endpointSupport tail head) v hv
      (fun w ↦ f (sourceArc w))).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: auxiliary outflow at an
original node is original outflow plus its sink-arc flow. -/
private lemma auxiliaryNodeOutgoingFlowEq
    (tail head : A → V) (f : AuxiliaryArc tail head → ℝ) (v : V)
    (hv : v ∈ endpointSupport tail head) :
    outgoing_flow (auxiliaryTail tail head) f (AuxiliaryVertex.node v) =
      outgoing_flow tail (fun a ↦ f (originalArc a)) v + f (sinkArc ⟨v, hv⟩) := by
  classical
  -- Split the auxiliary arc type; only original arcs and the unique sink arc leave `node v`.
  simpa [outgoing_flow, Finset.sum_filter, Fintype.sum_sum_type, auxiliaryTail,
    originalArc, sinkArc, eq_comm] using
    (sumIteSubtypeValue (endpointSupport tail head) v hv
      (fun w ↦ f (sinkArc w))).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: an auxiliary cut capacity
splits into its original, source-arc, and sink-arc contributions. -/
private lemma auxiliaryCutCapacityEq
    (tail head : A → V) (lower upper : A → ℝ) (S : Set (AuxiliaryVertex V))
    (hS : IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink) S) :
    cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head lower upper) S =
      Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S))
          (fun a ↦ upper a - lower a) +
        Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) +
        Finset.sum (sinkSideVertices tail head S) (sinkCapacity tail head lower) := by
  classical
  rcases hS with ⟨hsource, hsink⟩
  have hOriginalSplit :
      (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
          if AuxiliaryVertex.node (head a) ∈ S then 0 else upper a - lower a else 0) =
        (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
            if AuxiliaryVertex.node (head a) ∈ S then 0 else upper a else 0) -
          ∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
            if AuxiliaryVertex.node (head a) ∈ S then 0 else lower a else 0 := by
    -- Distribute subtraction only within the original-arc branch.
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a ha
    by_cases htail : AuxiliaryVertex.node (tail a) ∈ S
    · by_cases hhead : AuxiliaryVertex.node (head a) ∈ S
      · simp [htail, hhead]
      · simp [htail, hhead]
    · simp [htail]
  have hCutSum (weight : A → ℝ) :
      (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
          if AuxiliaryVertex.node (head a) ∈ S then 0 else weight a else 0) =
        Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S)) weight := by
    -- Membership in the induced cut is equivalent to membership of each supported endpoint.
    rw [outgoing_cut_arcs, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a ha
    simp [auxiliaryCutVertices, tailMemEndpointSupport tail head,
      headMemEndpointSupport tail head]
  have hOriginalContribution :
      (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
          if AuxiliaryVertex.node (head a) ∈ S then 0 else upper a - lower a else 0) =
        Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S))
          (fun a ↦ upper a - lower a) := by
    -- Original auxiliary arcs cross precisely when their endpoints cross the induced vertex cut.
    calc
      _ = (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
            if AuxiliaryVertex.node (head a) ∈ S then 0 else upper a else 0) -
          ∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
            if AuxiliaryVertex.node (head a) ∈ S then 0 else lower a else 0 := hOriginalSplit
      _ = Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S)) upper -
          Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S)) lower := by
        exact congrArg₂ (fun x y : ℝ ↦ x - y) (hCutSum upper) (hCutSum lower)
      _ = _ := (Finset.sum_sub_distrib upper lower).symm
  have hSourceContribution :
      (∑ v ∈ (endpointSupport tail head).attach,
          if AuxiliaryVertex.node v.1 ∈ S then 0 else sourceCapacity tail head lower v) =
        Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) := by
    -- The source arcs crossing the cut are exactly those whose supported vertex lies outside it.
    rw [sourceSideVertices, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro v hv
    by_cases hnode : AuxiliaryVertex.node v.1 ∈ S
    · simp [hnode]
    · simp [hnode]
  have hSinkContribution :
      (∑ v ∈ (endpointSupport tail head).attach,
          if AuxiliaryVertex.node v.1 ∈ S then sinkCapacity tail head lower v else 0) =
        Finset.sum (sinkSideVertices tail head S) (sinkCapacity tail head lower) := by
    -- The sink arcs crossing the cut are exactly those whose supported vertex lies inside it.
    rw [sinkSideVertices, Finset.sum_filter]
  -- Split the auxiliary arc type and rewrite the three resulting contributions separately.
  calc
    cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head lower upper) S =
        (∑ a, if AuxiliaryVertex.node (tail a) ∈ S then
            if AuxiliaryVertex.node (head a) ∈ S then 0 else upper a - lower a else 0) +
          ((∑ v ∈ (endpointSupport tail head).attach,
              if AuxiliaryVertex.node v.1 ∈ S then 0 else sourceCapacity tail head lower v) +
            ∑ v ∈ (endpointSupport tail head).attach,
              if AuxiliaryVertex.node v.1 ∈ S then sinkCapacity tail head lower v else 0) := by
      simp [cut_capacity, outgoing_cut_arcs, Finset.sum_filter, Fintype.sum_sum_type,
        auxiliaryTail, auxiliaryHead, auxiliaryCapacity, hsource, hsink]
    _ = Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S))
          (fun a ↦ upper a - lower a) +
        Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) +
        Finset.sum (sinkSideVertices tail head S) (sinkCapacity tail head lower) := by
      rw [hOriginalContribution, hSourceContribution, hSinkContribution]
      exact (add_assoc _ _ _).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14.lean`: the source-minus-sink
capacity on supported vertices inside a cut equals their lower-bound imbalance. -/
private lemma sinkSideCapacityDifferenceEqCutImbalance
    (tail head : A → V) (lower : A → ℝ) (S : Set (AuxiliaryVertex V)) :
    Finset.sum (sinkSideVertices tail head S)
        (fun v ↦ sourceCapacity tail head lower v - sinkCapacity tail head lower v) =
      Finset.sum (auxiliaryCutVertices tail head S)
        (lowerBoundImbalance tail head lower) := by
  classical
  calc
    Finset.sum (sinkSideVertices tail head S)
        (fun v ↦ sourceCapacity tail head lower v - sinkCapacity tail head lower v) =
        Finset.sum (sinkSideVertices tail head S)
          (fun v ↦ lowerBoundImbalance tail head lower v.1) := by
            -- Replace each capacity difference by its vertex imbalance.
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact sourceCapacitySubSinkCapacity tail head lower v
    _ = Finset.sum (endpointSupport tail head).attach
          (fun v ↦ if AuxiliaryVertex.node v.1 ∈ S then
            lowerBoundImbalance tail head lower v.1 else 0) := by
            rw [sinkSideVertices, Finset.sum_filter]
    _ = Finset.sum (endpointSupport tail head)
          (fun v ↦ if AuxiliaryVertex.node v ∈ S then
            lowerBoundImbalance tail head lower v else 0) := by
            exact Finset.sum_attach (endpointSupport tail head)
              (fun v ↦ if AuxiliaryVertex.node v ∈ S then
                lowerBoundImbalance tail head lower v else 0)
    _ = Finset.sum (auxiliaryCutVertices tail head S)
          (lowerBoundImbalance tail head lower) := by
            rw [auxiliaryCutVertices, Finset.sum_filter]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14/AuxiliaryNetwork.lean`:
total source capacity is the sum of its contributions outside and inside an auxiliary cut. -/
private lemma totalSourceCapacityEqCutPartition
    (tail head : A → V) (lower : A → ℝ) (S : Set (AuxiliaryVertex V)) :
    totalSourceCapacity tail head lower =
      Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) +
        Finset.sum (sinkSideVertices tail head S) (sourceCapacity tail head lower) := by
  classical
  have hSourceFinset :
      (endpointSupport tail head).attach.filter
          (fun v ↦ AuxiliaryVertex.node v.1 ∉ S) = sourceSideVertices tail head S := by
    -- Identify the outside filter independently of its generated decidability proof.
    ext v
    simp [sourceSideVertices]
  have hSinkFinset :
      (endpointSupport tail head).attach.filter
          (fun v ↦ AuxiliaryVertex.node v.1 ∈ S) = sinkSideVertices tail head S := by
    -- Identify the inside filter independently of its generated decidability proof.
    ext v
    simp [sinkSideVertices]
  -- Partition supported vertices by cut membership, then put the outside contribution first.
  calc
    totalSourceCapacity tail head lower =
        Finset.sum ((endpointSupport tail head).attach.filter
            (fun v ↦ AuxiliaryVertex.node v.1 ∈ S)) (sourceCapacity tail head lower) +
          Finset.sum ((endpointSupport tail head).attach.filter
            (fun v ↦ AuxiliaryVertex.node v.1 ∉ S)) (sourceCapacity tail head lower) := by
              exact (Finset.sum_filter_add_sum_filter_not
                (s := (endpointSupport tail head).attach)
                (p := fun v : SupportVertex tail head ↦ AuxiliaryVertex.node v.1 ∈ S)
                (f := sourceCapacity tail head lower)).symm
    _ = Finset.sum (sinkSideVertices tail head S) (sourceCapacity tail head lower) +
          Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) := by
            rw [hSinkFinset, hSourceFinset]
    _ = Finset.sum (sourceSideVertices tail head S) (sourceCapacity tail head lower) +
          Finset.sum (sinkSideVertices tail head S) (sourceCapacity tail head lower) := by
            exact add_comm _ _

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap04/section_4_12/ch4_sec4_12_exercise_4_14/AuxiliaryNetwork.lean

Every auxiliary source-sink cut has capacity at least the total source capacity under the
original cut inequalities. -/
lemma totalSourceCapacityLeAuxiliaryCutCapacity
    (tail head : A → V) (lower upper : A → ℝ)
    (hcut :
      ∀ X : Set V, Finset.sum (δ⁻[tail, head] X) lower ≤
        Finset.sum (δ⁺[tail, head] X) upper)
    (S : Set (AuxiliaryVertex V))
    (hS : IsSTCutSide (AuxiliaryVertex.source) (AuxiliaryVertex.sink) S) :
    totalSourceCapacity tail head lower ≤
      cut_capacity (auxiliaryTail tail head) (auxiliaryHead tail head)
        (auxiliaryCapacity tail head lower upper) S := by
  classical
  have hImbalance :
      Finset.sum (auxiliaryCutVertices tail head S)
          (lowerBoundImbalance tail head lower) ≤
        Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S))
          (fun a ↦ upper a - lower a) := by
    -- The original cut hypothesis bounds imbalance by outgoing residual capacity.
    rw [sumLowerBoundImbalanceEqCutDifference, Finset.sum_sub_distrib]
    exact sub_le_sub_right
      (hcut (auxiliaryCutVertices tail head S : Set V))
      (Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S)) lower)
  have hInside :
      Finset.sum (sinkSideVertices tail head S) (sourceCapacity tail head lower) -
          Finset.sum (sinkSideVertices tail head S) (sinkCapacity tail head lower) ≤
        Finset.sum (δ⁺[tail, head] (auxiliaryCutVertices tail head S))
          (fun a ↦ upper a - lower a) := by
    -- Normalize the inside source-minus-sink sum to the preceding imbalance bound.
    rw [← Finset.sum_sub_distrib, sinkSideCapacityDifferenceEqCutImbalance]
    exact hImbalance
  -- Substitute the cut decomposition and finish the scalar inequality.
  rw [auxiliaryCutCapacityEq tail head lower upper S hS,
    totalSourceCapacityEqCutPartition]
  linarith

end Exercise_4_14_Scratch

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_23

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter

private structure NhdsPoint (X : Type u) [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint X x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint X x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint X x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint X x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{w} (NhdsPoint X x)) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
    inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
  refine ⟨ULift.up ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩,
    ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private theorem tendsto_ulift_nhdsPoint {X : Type u} [TopologicalSpace X] {x : X} :
    Tendsto (fun p : ULift.{w} (NhdsPoint X x) ↦ p.down.value) atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨x, U, mem_of_mem_nhds hU, hU⟩, ?_⟩
  intro p hp
  exact hp p.down.value_mem

private lemma continuousAt_of_tendsto_liftedNhdsPoint {X : Type u} {Y : Type v}
    [TopologicalSpace X]
    [TopologicalSpace Y] {T : X → Y} {x : X}
    (h : Tendsto (fun p : ULift.{w} (NhdsPoint X x) ↦ T p.down.value) atTop
      (nhds (T x))) :
    ContinuousAt T x := by
  rw [Filter.tendsto_def] at h
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rcases Filter.mem_atTop_sets.mp (h V hV) with ⟨p, hp⟩
  refine Filter.mem_of_superset p.down.carrier_mem_nhds ?_
  intro y hy
  have hyV := hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
    intro z hz
    exact hz)
  simpa using hyV

/-- Fact 1.19: a map `T : X → Y` is continuous at `x` exactly when it sends every net
converging to `x` to a net converging to `T x`. -/
-- Proof sketch: the forward implication is the canonical filter-composition law for
-- `ContinuousAt`. For the reverse implication, apply the assumed net-preservation property to the
-- neighborhood-point net at `x`, whose convergence is canonical and whose image convergence
-- recovers the neighborhood definition of `ContinuousAt`.
theorem continuousAt_iff_tendsto_nets {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {T : X → Y} {x : X} :
    ContinuousAt T x ↔
      ∀ {A : Type (max u w)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → Tendsto (T ∘ ξ) atTop (nhds (T x)) := by
  constructor
  · intro hCont A _ _ ξ hξ
    simpa [Function.comp] using hCont.tendsto.comp hξ
  · intro hNets
    exact continuousAt_of_tendsto_liftedNhdsPoint <|
      hNets (fun p : ULift.{w} (NhdsPoint X x) ↦ p.down.value) tendsto_ulift_nhdsPoint

/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Topology

/-- Text 1.0.54 (1): an extended-real-valued function is lower semicontinuous on the whole space
exactly when it is lower semicontinuous at every point. -/
-- Proof sketch: this is the direct pointwise expansion of the canonical predicate
-- `LowerSemicontinuous`.
theorem lowerSemicontinuous_iff_forall_lowerSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} :
    LowerSemicontinuous f ↔ ∀ x, LowerSemicontinuousAt f x :=
  lowerSemicontinuous_iff

/-- Text 1.0.54 (2): an extended-real-valued function is upper semicontinuous at `x` exactly when
its negation is lower semicontinuous at `x`. -/
-- Proof sketch: use that negation on `EReal` reverses the order and transports the defining
-- neighborhoods for lower semicontinuity to those for upper semicontinuity.
theorem upperSemicontinuousAt_iff_lowerSemicontinuousAt_neg
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔ LowerSemicontinuousAt (fun y ↦ -f y) x := by
  rw [upperSemicontinuousAt_iff, lowerSemicontinuousAt_iff]
  constructor
  · intro h y hy
    have hxy : f x < -y := EReal.lt_neg_comm.mp hy
    simpa [EReal.lt_neg_comm] using h (-y) hxy
  · intro h y hy
    have hxy : -y < -f x := EReal.neg_lt_neg_iff.2 hy
    simpa [EReal.neg_lt_neg_iff] using h (-y) hxy

private lemma point_mem_of_frequently {X : Type u} [TopologicalSpace X] {x : X}
    {P : X → Prop} (hP : ∃ᶠ z in nhds x, P z) {U : Set X} (hU : U ∈ nhds x) :
    ∃ z, z ∈ U ∧ P z := by
  have hBoth : ∃ᶠ z in nhds x, P z ∧ z ∈ U := by
    simpa [and_left_comm, and_assoc] using hP.and_eventually hU
  rcases hBoth.exists with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private structure NeighborhoodIndex {X : Type u} [TopologicalSpace X] (x : X) where
  carrier : Set X
  mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NeighborhoodIndex x) :=
  ⟨⟨Set.univ, Filter.univ_mem⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NeighborhoodIndex x) :=
  ⟨fun U W ↦ W.carrier ⊆ U.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NeighborhoodIndex x) where
  le := (· ≤ ·)
  le_refl U := by
    intro y hy
    exact hy
  le_trans U V W hUV hVW := by
    intro y hy
    exact hUV (hVW hy)

private def infNeighborhoodIndex {X : Type u} [TopologicalSpace X] {x : X}
    (U W : NeighborhoodIndex x) : NeighborhoodIndex x :=
  ⟨U.carrier ∩ W.carrier, Filter.inter_mem U.mem_nhds W.mem_nhds⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (NeighborhoodIndex x) :=
  ⟨fun U W ↦
    ⟨infNeighborhoodIndex U W,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NeighborhoodIndex x)) :=
  ⟨fun U W ↦
    ⟨ULift.up (infNeighborhoodIndex U.down W.down),
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private noncomputable def badUpperNet {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    NeighborhoodIndex x → X :=
  fun U ↦ Classical.choose (point_mem_of_frequently hfreq U.mem_nhds)

private lemma badUpperNet_mem {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    badUpperNet hfreq U ∈ U.carrier := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).1

private lemma le_badUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    y ≤ f (badUpperNet hfreq U) := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).2

private lemma tendsto_liftedBadUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal}
    {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    Tendsto (fun U : ULift.{v} (NeighborhoodIndex x) ↦ badUpperNet hfreq U.down) atTop
      (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨U, hU⟩, ?_⟩
  intro W hW
  exact hW (badUpperNet_mem hfreq W.down)

private structure NhdsPoint {X : Type u} [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    Filter.inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NhdsPoint x)) :=
  ⟨fun p q ↦
    let r : NhdsPoint x := by
      have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
        Filter.inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
      exact ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩
    ⟨ULift.up r,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private lemma tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X] {x : X} :
    Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ p.down.value) atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨x, U, mem_of_mem_nhds hU, hU⟩, ?_⟩
  intro p hp
  exact hp p.down.value_mem

private lemma continuousAt_of_tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X}
    (h : Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ f p.down.value) atTop (nhds (f x))) :
    ContinuousAt f x := by
  rw [Filter.tendsto_def] at h
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rcases (Filter.mem_atTop_sets.mp (h V hV)) with ⟨p, hp⟩
  refine Filter.mem_of_superset p.down.carrier_mem_nhds ?_
  intro y hy
  have hyV := hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
    intro z hz
    exact hz)
  simpa using hyV

/-- Text 1.0.54 (2), net form: upper semicontinuity at `x` is equivalent to the limsup bound
along every convergent net `ξ`. -/
-- Proof sketch: the forward implication composes the convergent net with the canonical limsup
-- characterization `upperSemicontinuousAt_iff_limsup_le`. For the reverse implication, if some
-- threshold `y > f x` is not eventually avoided near `x`, choose from each neighborhood a point
-- where `f` stays at least `y`; the resulting neighborhood-indexed net converges to `x` and has
-- limsup at least `y`, contradicting the assumed net inequality.
theorem upperSemicontinuousAt_iff_net_limsup_le
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → limsup (f ∘ ξ) atTop ≤ f x := by
  constructor
  · intro h A _ _ ξ hξ
    calc
      limsup (f ∘ ξ) atTop = limsup f (map ξ atTop) := rfl
      _ ≤ limsup f (nhds x) := limsup_le_limsup_of_le hξ
      _ ≤ f x := h.limsup_le
  · intro h
    rw [upperSemicontinuousAt_iff]
    intro y hy
    by_contra hyEvent
    have hyFreq : ∃ᶠ z in nhds x, y ≤ f z := by
      simpa [not_lt] using Filter.not_eventually.mp hyEvent
    let ξ : ULift.{v} (NeighborhoodIndex x) → X := fun U ↦ badUpperNet hyFreq U.down
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedBadUpperNet hyFreq
    have hLimsup : limsup (f ∘ ξ) atTop ≤ f x := h ξ hξ
    have hyLe : y ≤ limsup (f ∘ ξ) atTop := by
      refine le_limsup_of_frequently_le ?_
      exact Filter.Frequently.of_forall fun U ↦ le_badUpperNet hyFreq U.down
    exact (not_le_of_gt hy) (hyLe.trans hLimsup)

/-- Text 1.0.54 (3): an extended-real-valued function is continuous at `x` exactly when it is both
lower semicontinuous and upper semicontinuous at `x`. -/
-- Proof sketch: apply the standard equivalence between continuity at a point and simultaneous
-- lower and upper semicontinuity.
theorem continuousAt_iff_lower_and_upperSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x :=
  continuousAt_iff_lower_upperSemicontinuousAt

/-- Text 1.0.54 (3), net form: continuity at `x` is equivalent to preservation of convergence
along every net converging to `x`. -/
-- Proof sketch: the forward implication composes a convergent net with `ContinuousAt.tendsto`.
-- For the reverse implication, use the universal neighborhood-point net, whose indices are pairs
-- `(y, U)` with `U ∈ 𝓝 x` and `y ∈ U`; convergence of its image shows that some neighborhood of
-- `x` is mapped into each neighborhood of `f x`.
theorem continuousAt_iff_net_tendsto
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → Tendsto (f ∘ ξ) atTop (nhds (f x)) := by
  constructor
  · intro h A _ _ ξ hξ
    simpa [Function.comp] using h.tendsto.comp hξ
  · intro h
    let ξ : ULift.{v} (NhdsPoint x) → X := fun p ↦ p.down.value
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedNhdsPoint
    have hImage : Tendsto (f ∘ ξ) atTop (nhds (f x)) := h ξ hξ
    exact continuousAt_of_tendsto_liftedNhdsPoint <| by
      simpa [ξ, Function.comp] using hImage

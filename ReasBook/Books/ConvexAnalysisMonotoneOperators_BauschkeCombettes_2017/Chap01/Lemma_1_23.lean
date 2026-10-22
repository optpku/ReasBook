/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_56_1_36

-- Declarations for this item will be appended below by the statement pipeline.

open Filter ERealFunction

universe u v

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
    IsDirectedOrder (ULift.{v} (NhdsPoint X x)) := by
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

private theorem map_nhdsPoint_eq_nhds {X : Type u} [TopologicalSpace X] {x : X} :
    map (fun p : ULift.{v} (NhdsPoint X x) ↦ p.down.value) atTop = nhds x := by
  refine Filter.ext fun s ↦ ?_
  rw [mem_map]
  constructor
  · intro hs
    rcases mem_atTop_sets.mp hs with ⟨p, hp⟩
    refine mem_of_superset p.down.carrier_mem_nhds ?_
    intro y hy
    exact hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
      intro z hz
      exact hz)
  · intro hs
    rw [mem_atTop_sets]
    refine ⟨ULift.up ⟨x, s, mem_of_mem_nhds hs, hs⟩, ?_⟩
    intro p hp
    exact hp p.down.value_mem

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The set of limit inferior values of `f` along nets converging to `x`. -/
def netLiminfValuesAt (f : X → EReal) (x : X) : Set EReal :=
  {r | ∃ (A : Type (max u v)) (_ : Preorder A) (_ : IsDirectedOrder A) (_ : Nonempty A)
      (ξ : A → X), Tendsto ξ atTop (nhds x) ∧ liminf (f ∘ ξ) atTop = r}

/-- Any net converging to `x` has limit inferior at least the pointwise limit inferior of `f`
at `x`. -/
private theorem liminfAt_le_liminf_net_of_tendsto (f : X → EReal) {A : Type v} [Preorder A]
    [IsDirectedOrder A] [Nonempty A] (ξ : A → X) (hξ : Tendsto ξ atTop (nhds x)) :
    liminfAt f x ≤ liminf (f ∘ ξ) atTop := by
  simpa [liminfAt, Filter.liminf_comp] using
    (liminf_le_liminf_of_le hξ : liminf f (nhds x) ≤ liminf f (map ξ atTop))

/-- Lemma 1.23: the limit inferior of `f` at `x` is the minimum of the limit inferiors of `f`
along all nets converging to `x`. -/
-- Proof sketch: every convergent net `ξ` satisfies `map ξ atTop ≤ nhds x`, so monotonicity of
-- `Filter.liminf` gives `liminfAt f x ≤ liminf (f ∘ ξ) atTop`. Equality is attained by the
-- canonical neighborhood-point net at `x`, whose pushed-forward filter is exactly `nhds x`.
theorem liminfAt_isLeast_netLiminfValues {X : Type u} [TopologicalSpace X]
    (f : X → EReal) (x : X) :
    IsLeast (netLiminfValuesAt.{u, v} f x) (liminfAt f x) := by
  refine ⟨?_, ?_⟩
  · let ξ : ULift.{v} (NhdsPoint X x) → X := fun p ↦ p.down.value
    have hMap : map ξ atTop = nhds x := map_nhdsPoint_eq_nhds
    have hξ : Tendsto ξ atTop (nhds x) := hMap.le
    have hLiminf : liminf (f ∘ ξ) atTop = liminfAt f x := by
      simpa [liminfAt, Filter.liminf_comp] using congrArg (liminf f) hMap
    exact ⟨ULift.{v} (NhdsPoint X x), inferInstance, inferInstance, inferInstance, ξ, hξ,
      hLiminf⟩
  · intro r hr
    rcases hr with ⟨A, _, _, _, ξ, hξ, rfl⟩
    exact liminfAt_le_liminf_net_of_tendsto f ξ hξ

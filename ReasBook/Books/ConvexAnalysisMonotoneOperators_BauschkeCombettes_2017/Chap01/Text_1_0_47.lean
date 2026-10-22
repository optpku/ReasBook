/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter

private structure ClusterHitPair {X : Type u} [TopologicalSpace X] {A : Type v}
    (u : A → X) (x : X) where
  index : A
  neighborhood : Set X
  neighborhood_mem : neighborhood ∈ nhds x
  hit_mem : u index ∈ neighborhood

private instance clusterHitPairPreorder {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} : Preorder (ClusterHitPair u x) where
  le p q := p.index ≤ q.index ∧ q.neighborhood ⊆ p.neighborhood
  le_refl p := ⟨le_rfl, Set.Subset.rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, Set.Subset.trans hqr.2 hpq.2⟩

private lemma clusterHitPair_nonempty {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Nonempty (ClusterHitPair u x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  obtain ⟨a, _, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩⟩

private lemma clusterHitPair_directed {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    IsDirectedOrder (ClusterHitPair u x) := by
  refine ⟨?_⟩
  intro p q
  obtain ⟨a₀, hpa₀, hqa₀⟩ := exists_ge_ge p.index q.index
  have hpq_mem : p.neighborhood ∩ q.neighborhood ∈ nhds x :=
    Filter.inter_mem p.neighborhood_mem q.neighborhood_mem
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster (p.neighborhood ∩ q.neighborhood) hpq_mem a₀
  refine ⟨⟨a, p.neighborhood ∩ q.neighborhood, hpq_mem, ha_mem⟩, ?_, ?_⟩
  · exact ⟨hpa₀.trans ha₀a, Set.inter_subset_left⟩
  · exact ⟨hqa₀.trans ha₀a, Set.inter_subset_right⟩

private lemma clusterHitPair_index_monotone {X : Type u} [TopologicalSpace X] {A : Type v}
    [Preorder A] {u : A → X} {x : X} :
    Monotone (ClusterHitPair.index : ClusterHitPair u x → A) := by
  intro p q hpq
  exact hpq.1

private lemma clusterHitPair_index_tendsto_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (ClusterHitPair.index : ClusterHitPair u x → A) atTop atTop := by
  refine Monotone.tendsto_atTop_atTop clusterHitPair_index_monotone ?_
  intro a₀
  obtain ⟨a, ha₀a, ha_mem⟩ := hcluster Set.univ Filter.univ_mem a₀
  exact ⟨⟨a, Set.univ, Filter.univ_mem, ha_mem⟩, ha₀a⟩

private lemma clusterHitPair_tendsto_nhds {X : Type u} [TopologicalSpace X] {A : Type v}
    [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    (hcluster : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V) :
    Tendsto (u ∘ (ClusterHitPair.index : ClusterHitPair u x → A)) atTop (nhds x) := by
  classical
  let a₀ : A := Classical.choice ‹Nonempty A›
  let _ : Nonempty (ClusterHitPair u x) := clusterHitPair_nonempty hcluster
  let _ : IsDirectedOrder (ClusterHitPair u x) := clusterHitPair_directed hcluster
  rw [tendsto_atTop']
  intro V hV
  obtain ⟨a, _, ha_mem⟩ := hcluster V hV a₀
  refine ⟨⟨a, V, hV, ha_mem⟩, ?_⟩
  intro b hb
  exact hb.2 b.hit_mem

private lemma subnet_tendsto_implies_mapClusterPt_atTop {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X}
    {B : Type w} [Nonempty B] [Preorder B] [IsDirectedOrder B] {φ : B → A}
    (hφ : Tendsto φ atTop atTop) (hconv : Tendsto (u ∘ φ) atTop (nhds x)) :
    MapClusterPt x atTop u := by
  exact MapClusterPt.of_comp hφ (Filter.Tendsto.mapClusterPt hconv)

/-- Text 1.0.47: a point `x` is a cluster point of a net `u` iff there is a subnet, given by a
monotone cofinal reindexing map, whose reindexed net converges to `x`. -/
-- Proof sketch: for the forward implication, take the directed set of pairs `(a, U)` consisting
-- of an index and a neighborhood of `x` hit by the net, ordered by tail refinement and reverse
-- inclusion of neighborhoods; the projection to `A` is monotone and cofinal, and the reindexed
-- net converges to `x`. For the reverse implication, combine convergence of the subnet with
-- cofinality of the reindexing map to show every neighborhood of `x` is met on every tail of the
-- original net.
theorem mapClusterPt_atTop_iff_exists_subnet_tendsto {X : Type u} [TopologicalSpace X]
    {A : Type v} [Nonempty A] [Preorder A] [IsDirectedOrder A] {u : A → X} {x : X} :
    MapClusterPt x atTop u ↔
      ∃ (B : Type (max u v)) (_ : Nonempty B) (_ : Preorder B) (_ : IsDirectedOrder B)
        (φ : B → A),
        Monotone φ ∧ Tendsto φ atTop atTop ∧ Tendsto (u ∘ φ) atTop (nhds x) := by
  constructor
  · intro hx
    have hx' : ∀ V : Set X, V ∈ nhds x → ∀ a₀ : A, ∃ a : A, a₀ ≤ a ∧ u a ∈ V := by
      rw [mapClusterPt_iff_frequently] at hx
      intro V hV a₀
      have hfreq : ∃ᶠ a in atTop, u a ∈ V := hx V hV
      rw [frequently_atTop] at hfreq
      exact hfreq a₀
    let B : Type (max u v) := ClusterHitPair u x
    let _ : Nonempty B := clusterHitPair_nonempty hx'
    let _ : IsDirectedOrder B := clusterHitPair_directed hx'
    refine ⟨B, inferInstance, inferInstance, inferInstance, ClusterHitPair.index, ?_⟩
    exact ⟨clusterHitPair_index_monotone, clusterHitPair_index_tendsto_atTop hx',
      clusterHitPair_tendsto_nhds hx'⟩
  · rintro ⟨B, _, _, _, φ, _, hφ, hconv⟩
    exact subnet_tendsto_implies_mapClusterPt_atTop hφ hconv

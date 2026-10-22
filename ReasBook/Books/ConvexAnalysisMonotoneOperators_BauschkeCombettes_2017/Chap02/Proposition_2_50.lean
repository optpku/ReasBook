/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology

universe u v

/-- Helper for Proposition 2.50: a weak sequential cluster point supplies a subsequence whose
inner-product coordinates converge against every fixed vector. -/
private lemma subsequence_inner_tendsto_of_weak_cluster_point
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    {xₙ : ℕ → 𝓗} {y : 𝓗}
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : 𝓗, Tendsto (fun n ↦ inner ℝ (xₙ (φ n)) v) atTop (𝓝 (inner ℝ y v)) := by
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  refine ⟨φ, hφ, ?_⟩
  intro v
  -- Compose the weakly convergent subsequence with the continuous coordinate functional.
  simpa using
    (weakSpace_continuous_inner_right v).tendsto (toWeakSpace ℝ 𝓗 y) |>.comp hφ_tendsto

/-- Helper for Proposition 2.50: if `y - x` has zero inner product against every generator of a
dense family, then `y - x` lies in the orthogonal complement of the generated span. -/
private lemma sub_mem_orthogonal_span_of_inner_eq_zero
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (e : I → 𝓗) {x y : 𝓗}
    (hinner : ∀ i : I, inner ℝ (y - x) (e i) = 0) :
    y - x ∈ (Submodule.span ℝ (Set.range e))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  -- Extend the vanishing from the generators to the whole span by linearity in the second slot.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · intro u hu
    rcases hu with ⟨i, rfl⟩
    exact hinner i
  · simp
  · intro u v _ _ hu hv
    simp [inner_add_right, hu, hv]
  · intro a u _ hu
    simp [inner_smul_right, hu]

/-- Helper for Proposition 2.50: dense-span coordinate agreement forces a weak sequential cluster
point to equal the target vector. -/
private lemma weak_cluster_point_eq_target_of_dense_span
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : I → 𝓗)
    (h_dense : Dense ((Submodule.span ℝ (Set.range e) : Set 𝓗)))
    {xₙ : ℕ → 𝓗} {x y : 𝓗}
    (hcoord : ∀ i : I,
      Tendsto (fun n ↦ inner ℝ (xₙ n) (e i)) atTop (𝓝 (inner ℝ x (e i))))
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y)) :
    y = x := by
  rcases subsequence_inner_tendsto_of_weak_cluster_point hy with ⟨φ, hφ, hφ_inner⟩
  have h_eq_coords : ∀ i : I, inner ℝ y (e i) = inner ℝ x (e i) := by
    intro i
    -- The same subsequence converges to both coordinate values, so the limits agree.
    have hsubseq_x :
        Tendsto (fun n ↦ inner ℝ (xₙ (φ n)) (e i)) atTop (𝓝 (inner ℝ x (e i))) :=
      (hcoord i).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique (hφ_inner (e i)) hsubseq_x
  have hsub_mem : y - x ∈ (Submodule.span ℝ (Set.range e))ᗮ := by
    -- Route correction: move from coordinate equalities to orthogonality of `y - x`.
    apply sub_mem_orthogonal_span_of_inner_eq_zero e
    intro i
    rw [inner_sub_left, h_eq_coords i, sub_self]
  exact h_dense.eq_of_sub_mem_orthogonal hsub_mem

/-- Proposition 2.50: for a sequence in a real Hilbert space, weak convergence to `x` is
equivalent to norm-boundedness together with convergence of the inner-product coordinates against
every vector in a family whose linear span is dense. -/
-- Proof sketch: the forward implication follows because weak convergence gives convergence of every
-- continuous coordinate functional, and boundedness follows from the standard boundedness criterion
-- for weakly convergent sequences. For the converse, apply the weak compactness subsequence
-- criterion to the bounded sequence `xₙ - x`; every weak sequential cluster point is orthogonal to
-- the dense spanning family, hence zero, so the sequence has a unique weak cluster point and
-- therefore converges weakly to `x`.
theorem tendsto_weakly_iff_bounded_and_inner_tendsto_of_dense_span
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : I → 𝓗)
    (h_dense : Dense ((Submodule.span ℝ (Set.range e) : Set 𝓗)))
    (xₙ : ℕ → 𝓗) (x : 𝓗) :
    Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      Bornology.IsBounded (Set.range xₙ) ∧
        ∀ i : I,
          Tendsto (fun n ↦ inner ℝ (xₙ n) (e i)) atTop (𝓝 (inner ℝ x (e i))) := by
  constructor
  · intro hx
    refine ⟨bounded_range_of_tendsto_weakly hx, ?_⟩
    intro i
    -- Weak convergence transports through each continuous coordinate functional.
    simpa using
      (weakSpace_continuous_inner_right (e i)).tendsto (toWeakSpace ℝ 𝓗 x) |>.comp hx
  · rintro ⟨hx_bounded, hcoord⟩
    -- Apply the weak compactness criterion once dense-span uniqueness of cluster points is proved.
    have huniq :
        ∀ y z : 𝓗,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 z) →
          y = z := by
      intro y z hy hz
      calc
        y = x := weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hy
        _ = z := (weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hz).symm
    rcases
        (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
          ⟨hx_bounded, huniq⟩ with
      ⟨y, hy⟩
    have hy_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y) := by
      exact ⟨id, strictMono_id, by simpa using hy⟩
    have hy_eq : y = x := weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hy_cluster
    simpa [hy_eq] using hy

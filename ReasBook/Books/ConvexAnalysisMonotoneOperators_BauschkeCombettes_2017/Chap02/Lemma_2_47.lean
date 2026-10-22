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

universe u

variable {H : Type u}

/-- Helper for Lemma 2.47: convergence of the distances to one reference point forces the whole
sequence to be norm-bounded. -/
lemma bounded_range_of_convergent_distance_to_point [NormedAddCommGroup H] {x : ℕ → H} {z : H}
    (hz : ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l)) :
    Bornology.IsBounded (Set.range x) := by
  rcases hz with ⟨l, hl⟩
  have hdist_bounded :
      Bornology.IsBounded (Set.range fun n ↦ ‖x n - z‖) :=
    Metric.isBounded_range_of_tendsto _ hl
  rcases isBounded_iff_forall_norm_le.mp hdist_bounded with ⟨R, hR⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R + ‖z‖, ?_⟩
  rintro y ⟨n, rfl⟩
  have hRn : ‖x n - z‖ ≤ R := by
    simpa using hR _ (Set.mem_range_self n)
  -- Compare `x n` with the translated point `(x n - z) + z`.
  calc
    ‖x n‖ = ‖(x n - z) + z‖ := by abel_nf
    _ ≤ ‖x n - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ R + ‖z‖ := by simpa [add_comm] using add_le_add_right hRn ‖z‖

/-- Helper for Lemma 2.47: convergence of the distance sequences to two points of `C` forces
convergence of the corresponding inner-product coordinate sequence. -/
lemma inner_tendsto_of_tendsto_dist_to_two_points [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} {x : ℕ → H}
    (hdist : ∀ w ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - w‖) atTop (𝓝 l))
    {y z : H} (hy : y ∈ C) (hz : z ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ inner ℝ (x n) (y - z)) atTop (𝓝 l) := by
  rcases hdist y hy with ⟨ly, hly⟩
  rcases hdist z hz with ⟨lz, hlz⟩
  refine ⟨(lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2) / 2, ?_⟩
  have hTwoInnerEq :
      (fun n ↦ 2 * inner ℝ (x n) (y - z)) =
        (fun n ↦ ‖x n - z‖ ^ 2 - ‖x n - y‖ ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2) := by
    funext n
    -- Expand both squared distances and collect the inner-product terms.
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring_nf
  have hTwoInner :
      Tendsto (fun n ↦ 2 * inner ℝ (x n) (y - z)) atTop
        (𝓝 (lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2)) := by
    rw [hTwoInnerEq]
    have hConst :
        Tendsto (fun _ : ℕ ↦ ‖y‖ ^ 2 - ‖z‖ ^ 2) atTop (𝓝 (‖y‖ ^ 2 - ‖z‖ ^ 2)) :=
      tendsto_const_nhds
    -- The polarization identity writes the coordinate as a linear combination of convergent
    -- squared-distance sequences.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((hlz.pow 2).sub (hly.pow 2)).add hConst
  have hHalf :
      Tendsto (fun n ↦ (1 / 2 : ℝ) * (2 * inner ℝ (x n) (y - z))) atTop
        (𝓝 ((1 / 2 : ℝ) * (lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2))) :=
    hTwoInner.const_mul (1 / 2 : ℝ)
  -- Dividing the convergent double-inner-product sequence by `2` gives the desired limit.
  convert hHalf using 1 <;> ring_nf

/-- Helper for Lemma 2.47: two weak sequential cluster points must coincide once all distance
sequences on `C` converge. -/
lemma weak_cluster_point_eq_of_convergent_distances [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {C : Set H} {x : ℕ → H}
    (hdist : ∀ w ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - w‖) atTop (𝓝 l))
    (hcluster :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H w) → w ∈ C)
    {y z : H}
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H y))
    (hz : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z)) :
    y = z := by
  have hyC : y ∈ C := hcluster y hy
  have hzC : z ∈ C := hcluster z hz
  rcases inner_tendsto_of_tendsto_dist_to_two_points hdist hyC hzC with ⟨l, hl⟩
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  rcases hz with ⟨ψ, hψ, hψ_tendsto⟩
  have hφ_limit :
      Tendsto (fun n ↦ inner ℝ (x (φ n)) (y - z)) atTop (𝓝 (inner ℝ y (y - z))) := by
    -- Weak convergence of the `φ`-subsequence controls the coordinate against `y - z`.
    simpa using
      (weakSpace_continuous_inner_right (y - z)).tendsto (toWeakSpace ℝ H y) |>.comp
        hφ_tendsto
  have hψ_limit :
      Tendsto (fun n ↦ inner ℝ (x (ψ n)) (y - z)) atTop (𝓝 (inner ℝ z (y - z))) := by
    -- The same coordinate along the `ψ`-subsequence converges to the corresponding `z`-value.
    simpa using
      (weakSpace_continuous_inner_right (y - z)).tendsto (toWeakSpace ℝ H z) |>.comp
        hψ_tendsto
  have hy_limit_eq : inner ℝ y (y - z) = l := by
    exact tendsto_nhds_unique hφ_limit (hl.comp hφ.tendsto_atTop)
  have hz_limit_eq : inner ℝ z (y - z) = l := by
    exact tendsto_nhds_unique hψ_limit (hl.comp hψ.tendsto_atTop)
  have hzero_sq : ‖y - z‖ ^ 2 = 0 := by
    -- The two subsequential limits agree, so the self-inner-product of `y - z` vanishes.
    calc
      ‖y - z‖ ^ 2 = inner ℝ (y - z) (y - z) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ y (y - z) - inner ℝ z (y - z) := by rw [inner_sub_left]
      _ = 0 := by rw [hy_limit_eq, hz_limit_eq, sub_self]
  have hzero : ‖y - z‖ = 0 := sq_eq_zero_iff.mp hzero_sq
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Lemma 2.47: if `C` is a nonempty subset of a real Hilbert space, the distance sequence
`n ↦ ‖x n - z‖` converges for every `z ∈ C`, and every weak sequential cluster point of `x`
belongs to `C`, then `x` converges weakly in `WeakSpace ℝ H` to some point of `C`. The
cluster-point hypothesis is expressed by `IsSequentialClusterPt` in the canonical weak topology
`WeakSpace ℝ H`. -/
-- Proof sketch: first use nonemptiness of `C` and convergence of one distance sequence to deduce
-- that `x` is bounded. Then apply weak sequential compactness to obtain a weakly convergent
-- subsequence. The cluster-point hypothesis puts every weak sequential cluster point in `C`, and
-- the convergence of all distance sequences on `C` gives uniqueness of such cluster points by the
-- standard polarization identity. Finally conclude that the whole sequence converges weakly to that
-- unique cluster point.
theorem opial_lemma [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : C.Nonempty) (x : ℕ → H)
    (hdist : ∀ z ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l))
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ C) :
    ∃ z ∈ C, Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  rcases hC with ⟨z₀, hz₀⟩
  have hx_bounded : Bornology.IsBounded (Set.range x) := by
    exact bounded_range_of_convergent_distance_to_point (hdist z₀ hz₀)
  have hx_unique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) →
        y = z := by
    intro y z hy hz
    exact weak_cluster_point_eq_of_convergent_distances hdist hcluster hy hz
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x).2
        ⟨hx_bounded, hx_unique⟩ with
    ⟨z, hz⟩
  have hz_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) := by
    exact ⟨id, strictMono_id, by simpa using hz⟩
  exact ⟨z, hcluster z hz_cluster, hz⟩

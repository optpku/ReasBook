/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Remark_3_11_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter Bornology
open scoped InnerProductSpace

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

/-- Helper for Proposition 3.12: the norm of the projection is controlled by the distance to the
set and the norm of the original point. -/
private lemma norm_projectionPoint_le_infDist_add_norm {X : Type u} [NormedAddCommGroup X]
    {C : Set X} (hC : IsChebyshev C) (x : X) :
    ‖projectionPoint C hC x‖ ≤ Metric.infDist x C + ‖x‖ := by
  -- Rewrite the projector as `(P_C x - x) + x` and apply the triangle inequality.
  calc
    ‖projectionPoint C hC x‖ = ‖(projectionPoint C hC x - x) + x‖ := by
      simp [sub_eq_add_neg, add_assoc]
    _ ≤ ‖projectionPoint C hC x - x‖ + ‖x‖ := norm_add_le _ _
    _ = dist x (projectionPoint C hC x) + ‖x‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    _ = Metric.infDist x C + ‖x‖ := by
      rw [(projectionPoint_isBestApproximation C hC x).2]

/-- Helper for Proposition 3.12: any subsequential limit of projection points is a best
approximation to the ambient limit point. -/
  private lemma isBestApproximation_of_tendsto_projection_subsequence {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {C : Set H} (hC : IsChebyshev C)
    {u : ℕ → H} {x y : H} (hu : Tendsto u atTop (nhds x))
    (hy : Tendsto (fun n ↦ projectionPoint C hC (u n)) atTop (nhds y)) :
    y ∈ C ∧ dist x y = Metric.infDist x C := by
  have hclosed : IsClosed C := by
    exact isClosed_of_isChebyshev hC
  have hy_mem : y ∈ C := by
    -- Every term of the projection sequence lies in `C`, and `C` is closed.
    exact hclosed.mem_of_tendsto hy (Filter.Eventually.of_forall fun n =>
      projectionPoint_mem C hC (u n))
  have hdist_proj :
      Tendsto (fun n ↦ dist (u n) (projectionPoint C hC (u n))) atTop (nhds (dist x y)) := by
    -- Distance is continuous in both variables, so it passes to the joint limit.
    exact (continuous_fst.dist continuous_snd).tendsto (x, y) |>.comp (hu.prodMk_nhds hy)
  have hinfDist :
      Tendsto (fun n ↦ Metric.infDist (u n) C) atTop (nhds (Metric.infDist x C)) := by
    -- The distance-to-set function is continuous.
    exact (Metric.continuous_infDist_pt C).tendsto x |>.comp hu
  have hdist_inf :
      Tendsto (fun n ↦ dist (u n) (projectionPoint C hC (u n))) atTop
        (nhds (Metric.infDist x C)) := by
    -- Each term realizes the distance to `C`.
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n =>
      ((projectionPoint_isBestApproximation C hC (u n)).2).symm) hinfDist
  exact ⟨hy_mem, tendsto_nhds_unique hdist_proj hdist_inf⟩

/-- Proposition 3.12: in a finite-dimensional real Hilbert space, the metric projection point map
onto a Chebyshev set is continuous. -/
theorem continuous_projectionPoint_of_isChebyshev {C : Set 𝓗} (hC : IsChebyshev C) :
    Continuous (projectionPoint C hC) := by
  -- Route correction: the proof works by sequential compactness of bounded projection subsequences,
  -- not by trying to prove a direct Lipschitz estimate for an arbitrary Chebyshev set.
  refine (continuous_iff_seqContinuous).2 ?_
  intro u x hu
  -- It suffices to show that every subsequence of the projection sequence has a further
  -- subsubsequence converging to the desired limit.
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  have hu_sub : Tendsto (fun n ↦ u (ns n)) atTop (nhds x) := hu.comp hns
  have hu_bdd : IsBounded (Set.range fun n ↦ u (ns n)) :=
    Metric.isBounded_range_of_tendsto _ hu_sub
  have hd_bdd : IsBounded (Set.range fun n ↦ Metric.infDist (u (ns n)) C) :=
    Metric.isBounded_range_of_tendsto _ <|
      ((Metric.continuous_infDist_pt C).tendsto x).comp hu_sub
  obtain ⟨Ru, hRu_pos, hRu⟩ := hu_bdd.subset_closedBall_lt 0 (0 : 𝓗)
  obtain ⟨Rd, hRd_pos, hRd⟩ := hd_bdd.subset_closedBall_lt 0 (0 : ℝ)
  let R : ℝ := Rd + Ru
  have hproj_mem :
      ∀ n, projectionPoint C hC (u (ns n)) ∈ Metric.closedBall (0 : 𝓗) R := by
    intro n
    have hu_norm : ‖u (ns n)‖ ≤ Ru := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hRu (by exact ⟨n, rfl⟩)
    have hd_le : Metric.infDist (u (ns n)) C ≤ Rd := by
      have hd_abs : |Metric.infDist (u (ns n)) C| ≤ Rd := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hRd (by exact ⟨n, rfl⟩)
      simpa [abs_of_nonneg (Metric.infDist_nonneg)] using hd_abs
    have hproj_norm :
        ‖projectionPoint C hC (u (ns n))‖ ≤ R := by
      calc
        ‖projectionPoint C hC (u (ns n))‖
            ≤ Metric.infDist (u (ns n)) C + ‖u (ns n)‖ :=
          norm_projectionPoint_le_infDist_add_norm hC (u (ns n))
        _ ≤ Rd + Ru := add_le_add hd_le hu_norm
        _ = R := rfl
    simpa [R, Metric.mem_closedBall, dist_eq_norm] using hproj_norm
  obtain ⟨y, _hy_closure, φ, hφmono, hφtendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hproj_mem
  have hu_subsub : Tendsto (fun n ↦ u (ns (φ n))) atTop (nhds x) :=
    hu_sub.comp hφmono.tendsto_atTop
  have hy_best :
      y ∈ C ∧ dist x y = Metric.infDist x C := by
    -- The subsubsequence limit remains a best approximation of `x`.
    simpa [Function.comp_def] using
      isBestApproximation_of_tendsto_projection_subsequence hC hu_subsub hφtendsto
  have hy_eq : y = projectionPoint C hC x :=
    eq_projectionPoint_of_isBestApproximation C hC hy_best
  refine ⟨φ, ?_⟩
  -- Uniqueness of the best approximation identifies every cluster point with `P_C x`.
  simpa [Function.comp_def, hy_eq] using hφtendsto

/-- Compatibility reformulation of Proposition 3.12 for the subtype-valued projector. -/
theorem continuous_projector_of_isChebyshev {C : Set 𝓗} (hC : IsChebyshev C) :
    Continuous (projector C hC) := by
  -- First prove continuity of the ambient projection point map.
  have hcont : Continuous (projectionPoint C hC) :=
    continuous_projectionPoint_of_isChebyshev hC
  -- Then package the continuous ambient map into the subtype-valued projector.
  simpa [projector] using hcont.subtype_mk (projectionPoint_mem C hC)

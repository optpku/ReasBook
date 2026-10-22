/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.TrajectoryWeights
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.InteriorWeightedSum
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_19.ClusterConvergence

-- Theorem-local partial-sum divergence helpers for Lemma 13.19.

noncomputable section

open Filter Matrix
open scoped BigOperators Topology

section

variable {n l : ℕ}

variable {Q : positiveDefiniteMatrices n} {b : Fin n → ℝ} {a : Fin l → Fin n → ℝ}
variable {x : ℕ → polytope_quadratic_feasible_set a} {i : ℕ → Fin l}

local notation "λ[" k "]" =>
  polytope_quadratic_exact_line_search_ratios Q b a x i k

section

variable
  {v0 : stdSimplex ℝ (Fin l)} {xStar : Fin n → ℝ}

local notation "Ω" => convexHull ℝ (Set.range a)

local notation "v[" k "]" =>
  polytope_quadratic_exact_line_search_weights
    (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 : Fin l → ℝ) k

namespace Lemma_13_19_PartialSumsDivergence

/-- Helper for Lemma 13.19: summable exact-line-search ratios yield a convergent simplex-weight
subsequence whose limit has strictly positive coordinates. -/
theorem exists_strictly_positive_limit_weights_of_summable_ratio
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : Fin n → ℝ) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    (hs : Summable (polytope_quadratic_exact_line_search_ratios Q b a x i)) :
    ∃ wBar : stdSimplex ℝ (Fin l), ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧
      Filter.Tendsto (fun m ↦ v[ψ m]) Filter.atTop (nhds (wBar : Fin l → ℝ)) ∧
      (∀ j, 0 < wBar j) := by
  let u : ℕ → stdSimplex ℝ (Fin l) := fun k ↦
    ⟨v[k],
      Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_weights_mem_stdSimplex
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj k⟩
  obtain ⟨wBar, ψ, hψmono, hψtendsto⟩ := CompactSpace.tendsto_subseq u
  obtain ⟨δ, hδ_pos, hδbound⟩ :=
    Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_weights_lower_bound_of_summable
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj hs
  have hval_tendsto :
      Filter.Tendsto (fun m ↦ v[ψ m]) Filter.atTop (nhds (wBar : Fin l → ℝ)) := by
    -- Passing from the simplex subtype to its ambient coordinate space preserves convergence.
    simpa [u, Function.comp] using
      (continuous_subtype_val.tendsto (wBar : stdSimplex ℝ (Fin l))).comp hψtendsto
  have hwBar_pos : ∀ j, 0 < wBar j := by
    intro j
    have hcoord_tendsto :
        Filter.Tendsto (fun m ↦ v[ψ m] j) Filter.atTop (nhds (wBar j)) := by
      -- Coordinatewise convergence follows by composing with the continuous evaluation map.
      simpa [Function.comp] using
        ((continuous_apply j).tendsto (wBar : Fin l → ℝ)).comp hval_tendsto
    have hwBar_ge : δ * v0 j ≤ wBar j := by
      -- The uniform lower bound survives in the limit because closed rays are closed.
      refine isClosed_Ici.mem_of_tendsto hcoord_tendsto ?_
      exact Filter.Eventually.of_forall fun m ↦ hδbound (ψ m) j
    have hbase_pos : 0 < δ * v0 j := by
      -- Assumption 13.18 gives strictly positive initial barycentric coordinates.
      exact mul_pos hδ_pos (hinit.weight_pos j)
    exact lt_of_lt_of_le hbase_pos hwBar_ge
  exact ⟨wBar, ψ, hψmono, hval_tendsto, hwBar_pos⟩

/-- Helper for Lemma 13.19: the limit simplex weights from the summable case still represent the
boundary optimizer `xStar` as a barycentric combination of the vertices. -/
theorem boundary_optimizer_eq_weighted_sum_of_limit_weights
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : Fin n → ℝ) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i)
    {wBar : stdSimplex ℝ (Fin l)} {ψ : ℕ → ℕ}
    (hψmono : StrictMono ψ)
    (hψtendsto :
      Filter.Tendsto (fun m ↦ v[ψ m]) Filter.atTop (nhds (wBar : Fin l → ℝ))) :
    xStar = ∑ j, wBar j • a j := by
  let bary : (Fin l → ℝ) → (Fin n → ℝ) := fun w' ↦ ∑ j, w' j • a j
  have hbary_cont : Continuous bary := by
    -- The barycentric synthesis map is continuous because it is a finite sum of coordinates.
    refine continuous_finset_sum _ fun j _ ↦ ?_
    exact (continuous_apply j).smul continuous_const
  have hbary_tendsto :
      Filter.Tendsto (fun m ↦ ∑ j, v[ψ m] j • a j) Filter.atTop
        (nhds (∑ j, wBar j • a j)) := by
    -- Applying the barycentric map transports the weight convergence to vertex combinations.
    simpa [bary, Function.comp] using (hbary_cont.tendsto (wBar : Fin l → ℝ)).comp hψtendsto
  have hxSub_tendsto :
      Filter.Tendsto (fun m ↦ (x (ψ m) : Fin n → ℝ)) Filter.atTop (nhds xStar) := by
    -- Every subsequence inherits the convergence of the full iterate sequence to `xStar`.
    exact
      (Lemma_13_19_ClusterConvergence.polytope_quadratic_iterates_tendsto_boundary_optimizer
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
        hboundary hinit htraj).comp hψmono.tendsto_atTop
  have hweightedSub_tendsto :
      Filter.Tendsto (fun m ↦ ∑ j, v[ψ m] j • a j) Filter.atTop (nhds xStar) := by
    -- The source recursion identifies each iterate with its barycentric vertex combination.
    refine Tendsto.congr' ?_ hxSub_tendsto
    exact Filter.Eventually.of_forall fun m ↦
      Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_iterate_eq_weighted_sum
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj (ψ m)
  -- The same subsequence has both limits, so the limit point is unique.
  exact tendsto_nhds_unique hweightedSub_tendsto hbary_tendsto

/-- Helper for Lemma 13.19: the exact-line-search ratios are not summable, because summability
would force the boundary optimizer into the interior of the polytope. -/
theorem polytope_quadratic_exact_line_search_ratio_not_summable
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : Fin n → ℝ) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    ¬ Summable (polytope_quadratic_exact_line_search_ratios Q b a x i) := by
  intro hs
  obtain ⟨wBar, ψ, hψmono, hψtendsto, hwBar_pos⟩ :=
    exists_strictly_positive_limit_weights_of_summable_ratio
      (Q := Q) (b := b) (a := a) (x := x) (i := i) (v0 := v0) hinit htraj hs
  have hxStar_eq :
      xStar = ∑ j, wBar j • a j := by
    -- The positive limit weights still encode the optimizer by continuity of the barycentric map.
    exact
      boundary_optimizer_eq_weighted_sum_of_limit_weights
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
        hboundary hinit htraj hψmono hψtendsto
  have hxStar_mem_interior : xStar ∈ interior Ω := by
    -- Strictly positive simplex coordinates place the weighted sum in the interior of `Ω`.
    rw [hxStar_eq]
    exact
      Lemma_13_19_InteriorWeights.strictly_positive_stdSimplex_weighted_sum_mem_interior_convexHull
        (a := a) hboundary.interior_nonempty wBar.property hwBar_pos
  have hxStar_not_mem_interior : xStar ∉ interior Ω := by
    -- Boundary membership excludes interior membership.
    simpa [frontier] using hboundary.mem_frontier.2
  exact hxStar_not_mem_interior hxStar_mem_interior

-- Proof sketch: combine the source contradiction `¬ Summable (∑ λ_k)` with the standard
-- nonnegative-series divergence theorem, then shift the canonical `range m` partial sums to the
-- textbook `range (m + 1)` indexing.
/-- Lemma 13.19 (5): the partial sums of the exact-line-search ratios `λ_k` diverge to `+∞`. -/
theorem polytope_quadratic_exact_line_search_ratio_partialSums_tendsto_atTop
    (hboundary :
      IsBoundaryNonExtremeOptimalSolution
        (polytope_quadratic_problem Q b a)
        Ω xStar)
    (hinit :
      IsStrictVertexSublevelInitialPoint
        (polytope_quadratic_objective Q b) a (x 0 : Fin n → ℝ) v0)
    (htraj :
      is_polytope_quadratic_conditional_gradient_exact_line_search_trajectory Q b a x i) :
    Filter.Tendsto
      (fun m : ℕ ↦
        Finset.sum (Finset.range (m + 1)) fun k ↦ λ[k])
      Filter.atTop Filter.atTop := by
  have h_not_summable :
      ¬ Summable (polytope_quadratic_exact_line_search_ratios Q b a x i) := by
    -- The source contradiction is now isolated in its own helper theorem.
    exact
      polytope_quadratic_exact_line_search_ratio_not_summable
        (Q := Q) (b := b) (a := a) (x := x) (i := i) (xStar := xStar) (v0 := v0)
        hboundary hinit htraj
  let p : ℕ → ℝ := fun m ↦ ∑ k ∈ Finset.range m, λ[k]
  have hp_tendsto : Filter.Tendsto p Filter.atTop Filter.atTop := by
    -- A nonnegative non-summable series has partial sums diverging to `+∞`.
    exact
      (not_summable_iff_tendsto_nat_atTop_of_nonneg
        (fun k ↦
          Lemma_13_19_TrajectoryWeights.polytope_quadratic_exact_line_search_ratio_nonneg
            (Q := Q) (b := b) (a := a) (x := x) (i := i) htraj k)).mp h_not_summable
  change Filter.Tendsto (fun m ↦ p (m + 1)) Filter.atTop Filter.atTop
  -- The textbook uses the one-step-shifted partial sums `range (m + 1)`.
  simpa [p] using (tendsto_add_atTop_iff_nat (f := p) 1).2 hp_tendsto

end Lemma_13_19_PartialSumsDivergence

end

end

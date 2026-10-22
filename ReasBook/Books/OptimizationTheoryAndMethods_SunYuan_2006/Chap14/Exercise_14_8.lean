/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Mathlib.Topology.Compactness.Compact
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_5_4

noncomputable section

open Filter

section

variable {n : ℕ}

open Chapter14

/-- A uniformly convex objective on `Set.univ` has at most one global minimizer once its modulus
`φ` is strictly positive away from `0`. -/
theorem eq_of_isMinOn_of_uniformConvexOn
    (f : Point n → ℝ) (φ : ℝ → ℝ)
    (h_uniformConvex : UniformConvexOn Set.univ φ f)
    (h_phi_pos : ∀ r : ℝ, r ≠ 0 → 0 < φ r)
    {x y : Point n}
    (hx : IsMinOn f Set.univ x)
    (hy : IsMinOn f Set.univ y) :
    x = y := by
  exact
    (h_uniformConvex.strictConvexOn h_phi_pos).eq_of_isMinOn
      hx
      hy
      (by simp)
      (by simp)

/-- Any two accumulation points of the bundle-method iterate sequence coincide when every
accumulation point is a global minimizer and the objective is uniformly convex with modulus `φ`
strictly positive away from `0`. -/
theorem bundleMethod_accumulationPoint_eq_of_uniformConvexOn
    (method : BundleMethod n) (φ : ℝ → ℝ)
    (h_uniformConvex : UniformConvexOn Set.univ φ method.objective)
    (h_phi_pos : ∀ r : ℝ, r ≠ 0 → 0 < φ r)
    (h_accumulation_isMinOn :
      ∀ {xStar : Point n} {σ : ℕ → ℕ},
        StrictMono σ →
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar) →
            IsMinOn method.objective Set.univ xStar)
    {xStar yStar : Point n} {σ τ : ℕ → ℕ}
    (hσ : StrictMono σ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar))
    (hτ : StrictMono τ)
    (hyStar : Tendsto (fun k : ℕ ↦ method.shiftedIterate (τ k)) atTop (nhds yStar)) :
    xStar = yStar := by
  exact
    eq_of_isMinOn_of_uniformConvexOn
      method.objective
      φ
      h_uniformConvex
      h_phi_pos
      (h_accumulation_isMinOn hσ hxStar)
      (h_accumulation_isMinOn hτ hyStar)

/-- If a subsequence of the bundle-method iterates converges to `xStar` and every accumulation
point of the iterate sequence is a global minimizer of `method.objective`, then `xStar` is a
global minimizer of `method.objective`. -/
theorem bundleMethod_isMinOn_of_subseqTendsto
    (method : BundleMethod n) {xStar : Point n}
    (h_accumulation_isMinOn :
      ∀ {y : Point n} {σ : ℕ → ℕ},
        StrictMono σ →
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds y) →
            IsMinOn method.objective Set.univ y)
    (h_subseq :
      ∃ σ : ℕ → ℕ,
        StrictMono σ ∧
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar)) :
    IsMinOn method.objective Set.univ xStar := by
  rcases h_subseq with ⟨σ, hσ, hxStar⟩
  exact h_accumulation_isMinOn hσ hxStar

/-- Helper for Chapter14 Exercise 14.8: eventual membership in `s` together with frequent escape
from `U` yields frequent membership in the compact difference `s \ U`. -/
lemma shiftedIterate_frequently_mem_diff
    (method : BundleMethod n) {s U : Set (Point n)}
    (h_iterate_eventually_mem :
      ∀ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s)
    (h_iterate_frequently_notMem :
      ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∉ U) :
    ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s \ U := by
  -- Intersect the frequent escape from `U` with the eventual tail inside `s`.
  refine (h_iterate_frequently_notMem.and_eventually h_iterate_eventually_mem).mono ?_
  intro k hk
  exact ⟨hk.2, hk.1⟩

/-- Helper for Chapter14 Exercise 14.8: once the shifted iterates are eventually trapped in a
compact set, some subsequence converges to a point of that set. -/
lemma bundleMethod_hasCompactSubsequence
    (method : BundleMethod n) {s : Set (Point n)}
    (hs_compact : IsCompact s)
    (h_iterate_eventually_mem :
      ∀ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s) :
    ∃ xStar ∈ s, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar) := by
  -- Eventual membership in `s` is enough to invoke compact subsequence extraction.
  have h_iterate_frequently_mem : ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s :=
    h_iterate_eventually_mem.frequently
  -- Compactness returns a convergent subsequence with limit still in `s`.
  simpa [Function.comp_def] using hs_compact.tendsto_subseq' h_iterate_frequently_mem

/-- Helper for Chapter14 Exercise 14.8: if the shifted iterates remain eventually in the compact
set `s` but frequently avoid the open neighborhood `U`, then a subsequence converges to a point of
`s \ U`. -/
lemma bundleMethod_hasSubsequenceOutsideNeighborhood
    (method : BundleMethod n) {s U : Set (Point n)}
    (hs_compact : IsCompact s)
    (h_iterate_eventually_mem :
      ∀ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s)
    (hU_open : IsOpen U)
    (h_iterate_frequently_notMem :
      ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∉ U) :
    ∃ yStar ∈ s \ U, ∃ τ : ℕ → ℕ, StrictMono τ ∧
      Tendsto (fun k : ℕ ↦ method.shiftedIterate (τ k)) atTop (nhds yStar) := by
  -- First normalize the filter information to frequent membership in the compact difference.
  have h_iterate_frequently_mem_diff :
      ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s \ U :=
    shiftedIterate_frequently_mem_diff
      method
      h_iterate_eventually_mem
      h_iterate_frequently_notMem
  have hs_diff_compact : IsCompact (s \ U) :=
    hs_compact.diff hU_open
  -- Compactness of `s \ U` then gives the required escaping subsequence.
  simpa [Function.comp_def] using hs_diff_compact.tendsto_subseq' h_iterate_frequently_mem_diff

/-- If some subsequence of the bundle-method iterates converges to `xStar`, and every
accumulation point is a global minimizer of `method.objective`, then the full iterate sequence
`method.shiftedIterate` converges to `xStar` under the compactness and uniform-convexity
assumptions. -/
theorem bundleMethod_tendsto_of_uniformConvexOn_of_subseqTendsto
    (method : BundleMethod n) (φ : ℝ → ℝ) {s : Set (Point n)} {xStar : Point n}
    (h_uniformConvex : UniformConvexOn Set.univ φ method.objective)
    (h_phi_pos : ∀ r : ℝ, r ≠ 0 → 0 < φ r)
    (h_accumulation_isMinOn :
      ∀ {y : Point n} {σ : ℕ → ℕ},
        StrictMono σ →
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds y) →
            IsMinOn method.objective Set.univ y)
    (hs_compact : IsCompact s)
    (h_iterate_eventually_mem :
      ∀ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s)
    (h_subseq :
      ∃ σ : ℕ → ℕ,
        StrictMono σ ∧
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar)) :
    Tendsto method.shiftedIterate atTop (nhds xStar) := by
  classical
  -- Every subsequential limit is a minimizer, so the given subsequence already identifies
  -- `xStar` as the unique global minimizer allowed by uniform convexity.
  have hxStar_isMinOn : IsMinOn method.objective Set.univ xStar :=
    bundleMethod_isMinOn_of_subseqTendsto method h_accumulation_isMinOn h_subseq
  by_contra h_not_tendsto
  -- Failure of convergence yields a neighborhood of `xStar` missed infinitely often.
  obtain ⟨W, hW_nhds, h_iterate_frequently_notMem_W⟩ :=
    Filter.not_tendsto_iff_exists_frequently_notMem.mp h_not_tendsto
  obtain ⟨U, hU_subset_W, hU_open, hxStar_mem_U⟩ := mem_nhds_iff.mp hW_nhds
  have h_iterate_frequently_notMem_U :
      ∃ᶠ k : ℕ in atTop, method.shiftedIterate k ∉ U := by
    -- Shrinking the neighborhood preserves frequent escape.
    refine h_iterate_frequently_notMem_W.mono ?_
    intro k hk h_mem_U
    exact hk (hU_subset_W h_mem_U)
  -- Extract a compact escaping subsequence whose limit stays outside the neighborhood.
  obtain ⟨yStar, hyStar_mem_diff, τ, hτ, hyStar_tendsto⟩ :=
    bundleMethod_hasSubsequenceOutsideNeighborhood
      method
      hs_compact
      h_iterate_eventually_mem
      hU_open
      h_iterate_frequently_notMem_U
  have hyStar_isMinOn : IsMinOn method.objective Set.univ yStar :=
    h_accumulation_isMinOn hτ hyStar_tendsto
  have hx_eq_hy : xStar = yStar :=
    eq_of_isMinOn_of_uniformConvexOn
      method.objective
      φ
      h_uniformConvex
      h_phi_pos
      hxStar_isMinOn
      hyStar_isMinOn
  have hyStar_mem_U : yStar ∈ U := by
    simpa [hx_eq_hy] using hxStar_mem_U
  exact hyStar_mem_diff.2 hyStar_mem_U

/-- Chapter14 Exercise 14.8: let `method` be a bundle-method run for a uniformly convex
objective `method.objective` on `Set.univ`, with modulus `φ` strictly positive away from `0`.
Assume prior bundle-method theory shows that every accumulation point of the iterate sequence
`method.shiftedIterate` is a global minimizer of `method.objective`, and that the iterate
sequence is eventually contained in a compact set `s`. Then the bundle-method iterates converge
globally to a global minimizer of `method.objective`. -/
theorem bundleMethod_globalConvergence_of_uniformConvexOn
    (method : BundleMethod n) (φ : ℝ → ℝ) {s : Set (Point n)}
    (h_uniformConvex : UniformConvexOn Set.univ φ method.objective)
    (h_phi_pos : ∀ r : ℝ, r ≠ 0 → 0 < φ r)
    (h_accumulation_isMinOn :
      ∀ {y : Point n} {σ : ℕ → ℕ},
        StrictMono σ →
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds y) →
            IsMinOn method.objective Set.univ y)
    (hs_compact : IsCompact s)
    (h_iterate_eventually_mem :
      ∀ᶠ k : ℕ in atTop, method.shiftedIterate k ∈ s) :
    ∃ xStar : Point n,
      IsMinOn method.objective Set.univ xStar ∧
        Tendsto method.shiftedIterate atTop (nhds xStar) := by
  -- Compactness of the iterate tail gives one convergent subsequence to start the argument.
  obtain ⟨xStar, -, σ, hσ, hxStar_tendsto⟩ :=
    bundleMethod_hasCompactSubsequence
      method
      hs_compact
      h_iterate_eventually_mem
  have h_subseq :
      ∃ σ : ℕ → ℕ,
        StrictMono σ ∧
          Tendsto (fun k : ℕ ↦ method.shiftedIterate (σ k)) atTop (nhds xStar) :=
    ⟨σ, hσ, hxStar_tendsto⟩
  -- The subsequential limit is a global minimizer by the assumed accumulation-point theorem.
  have hxStar_isMinOn : IsMinOn method.objective Set.univ xStar :=
    bundleMethod_isMinOn_of_subseqTendsto method h_accumulation_isMinOn h_subseq
  -- Uniform convexity upgrades that one convergent subsequence to convergence of the full tail.
  have h_shiftedIterate_tendsto : Tendsto method.shiftedIterate atTop (nhds xStar) :=
    bundleMethod_tendsto_of_uniformConvexOn_of_subseqTendsto
      method
      φ
      h_uniformConvex
      h_phi_pos
      h_accumulation_isMinOn
      hs_compact
      h_iterate_eventually_mem
      h_subseq
  exact ⟨xStar, hxStar_isMinOn, h_shiftedIterate_tendsto⟩

end

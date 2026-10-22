/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_34

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-! The source-facing process API used by Theorem 24.35 and Exercise 24.3.3.

The generated development previously supplied these declarations through a cached module under
the legacy `Chap24` namespace. Keeping them here makes the dependency graph explicit and lets the
remaining statements be checked from `Items` alone.
-/

/-- The one-step table-size mass used by the Chinese-restaurant process API. -/
def chineseRestaurantTableSizeMass (α θ : ℝ) (l n k : ℕ) : ℝ :=
  (((n - 1).choose (k - 1) : ℝ) *
      ProbabilityTheory.beta k (((n - k : ℕ) : ℝ) + θ)) /
    ProbabilityTheory.beta 1 θ

/-- The conditional-law package for a Chinese-restaurant process. -/
structure IsChineseRestaurantProcessLaw (α θ : ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (law : @ProbabilityMeasure Ω mΩ)
    (tableSize : ℕ → Ω → ℕ → ℕ) : Prop where
  measurable_tableSize : ∀ n l, Measurable (fun ω ↦ tableSize n ω l)
  total_customers : ∀ n ω, (Finset.range (n + 1)).sum (fun l ↦ tableSize n ω l) = n
  tail_zero : ∀ n ω l, n < l → tableSize n ω l = 0
  next_table_conditional_law :
    ∀ {n l k : ℕ} (ks : Fin l → ℕ), 0 < k → (∀ i, 0 < ks i) →
      Finset.univ.sum ks + k ≤ n →
      (law : Measure Ω)[({ω | tableSize n ω l = k} : Set Ω) |
        ({ω | ∀ i : Fin l, tableSize n ω i = ks i} : Set Ω)] =
          ENNReal.ofReal (chineseRestaurantTableSizeMass α θ l (n - Finset.univ.sum ks) k)

/-- A Chinese-restaurant process together with its probability space and transition law. -/
structure ChineseRestaurantProcess (α θ : ℝ)
    (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ) where
  Ω : Type u
  mΩ : MeasurableSpace Ω
  law : @ProbabilityMeasure Ω mΩ
  tableSize : ℕ → Ω → ℕ → ℕ
  isChineseRestaurantProcess : IsChineseRestaurantProcessLaw α θ law tableSize

instance {α θ : ℝ} {hα_nonneg : 0 ≤ α} {hα_lt_one : α < 1} {hθα : -α < θ}
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) :
    MeasurableSpace process.Ω := process.mΩ

/-- The normalized appearance-order block-size sequence at time `n`. -/
def blockProportions
    {α θ : ℝ} {hα_nonneg : 0 ≤ α} {hα_lt_one : α < 1} {hθα : -α < θ}
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) (n : ℕ) :
    process.Ω → ℕ → ℝ :=
  fun ω l ↦ (process.tableSize (n + 1) ω l : ℝ) / (n + 1)

theorem measurable_blockProportions
    {α θ : ℝ} {hα_nonneg : 0 ≤ α} {hα_lt_one : α < 1} {hθα : -α < θ}
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) (n : ℕ) :
    Measurable (blockProportions process n) := by
  sorry

/-- The ranked normalized block-size law of a Chinese-restaurant process. -/
noncomputable def normalizedChineseRestaurantProcessLaw
    {α θ : ℝ} {hα_nonneg : 0 ≤ α} {hα_lt_one : α < 1} {hθα : -α < θ}
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) (n : ℕ) :
    ProbabilityMeasure MassPartition :=
  process.law.map
    ((measurable_rankedRearrangement.comp
      (measurable_blockProportions process n)).aemeasurable)

/-- The normalized Chinese-restaurant laws converge to the Poisson--Dirichlet law.

This analytic frontier is kept as an explicit `sorry` in the source-facing module rather than
being imported from an unavailable legacy cache.
-/
theorem normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) :
    Tendsto (normalizedChineseRestaurantProcessLaw process) atTop
      (𝓝 (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα)) := by
  sorry

/-- Theorem 24.35, exposed under its item-level owner name. -/
theorem chineseRestaurantProcess_tendsto_poissonDirichlet
    (α θ : ℝ) (hα_nonneg : 0 ≤ α) (hα_lt_one : α < 1) (hθα : -α < θ)
    (process : ChineseRestaurantProcess α θ hα_nonneg hα_lt_one hθα) :
    Tendsto (normalizedChineseRestaurantProcessLaw process) atTop
      (𝓝 (poissonDirichletDistribution α θ hα_nonneg hα_lt_one hθα)) := by
  exact normalizedChineseRestaurantPartitionLaw_tendsto_poissonDirichlet
    α θ hα_nonneg hα_lt_one hθα process

end ProbabilityTheory

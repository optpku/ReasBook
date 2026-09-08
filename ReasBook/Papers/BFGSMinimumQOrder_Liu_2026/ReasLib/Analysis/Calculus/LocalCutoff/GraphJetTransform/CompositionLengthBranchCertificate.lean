module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.UniformRemainderCertificate
public import Mathlib.Combinatorics.Enumerative.Composition

public section

open scoped BigOperators
open scoped Topology
open Filter

universe u v

namespace LocalCutoff.GraphTransform

/-!
This module keeps the composition-index bookkeeping separate from the
source-specific finite-jet estimates.  A non-all-ones composition has either
strictly fewer than `r - 1` blocks or exactly `r - 1` blocks; the adapter below
uses that dichotomy to consume two independently supplied branch bounds.
-/

/-- Helper for Infrastructure I.16a: a non-all-ones composition has either
fewer than `r - 1` blocks or exactly `r - 1` blocks. -/
theorem composition_nonOnes_length_lt_or_eq_pred
    {r : ℕ} {c : Composition r}
    (hc : c ≠ Composition.ones r) :
    c.length < r - 1 ∨ c.length = r - 1 := by
  have hlength_le : c.length ≤ r := c.length_le
  have hlength_ne : c.length ≠ r := by
    intro hlength
    apply hc
    exact Composition.eq_ones_iff_length.mpr hlength
  have hlength_lt : c.length < r := lt_of_le_of_ne hlength_le hlength_ne
  have hpred : c.length ≤ r - 1 := Nat.le_pred_of_lt hlength_lt
  exact lt_or_eq_of_le hpred

/-- Infrastructure I.16a: separate lower-order and critical-order branch
bounds give one compact-uniform estimate for the non-all-ones composition sum. -/
theorem composition_nonOnes_uniformBoundOn_of_length_split
    {r : ℕ} {Θ : Type u} {E : Type v}
    [NormedAddCommGroup E] (K : Set Θ)
    (b : Composition r → Θ → ℝ → E)
    (lowerBound criticalBound : Composition r → Θ → ℝ → ℝ)
    (h_lower : ∀ c, c ≠ Composition.ones r → c.length < r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ lowerBound c u t)
    (h_critical : ∀ c, c ≠ Composition.ones r → c.length = r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ criticalBound c u t) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : Composition r,
          if c = Composition.ones r then 0 else b c u t‖ ≤
        (∑ c : Composition r,
          if c = Composition.ones r then 0
          else if c.length < r - 1 then lowerBound c u t else criticalBound c u t) := by
  let branchBound : Composition r → Θ → ℝ → ℝ := fun c u t ↦
    if c.length < r - 1 then lowerBound c u t else criticalBound c u t
  have hbranch : ∀ c, c ≠ Composition.ones r →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ branchBound c u t := by
    intro c hc
    rcases composition_nonOnes_length_lt_or_eq_pred hc with hlow | hcritical
    · simpa only [branchBound, if_pos hlow] using h_lower c hc hlow
    · have hnotlow : ¬ c.length < r - 1 := Nat.not_lt_of_ge hcritical.ge
      simpa only [branchBound, if_neg hnotlow] using
        h_critical c hc hcritical
  have hbranch_eventually (c : Composition r) (hc : c ≠ Composition.ones r) :
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ u ∈ K, ‖b c u t‖ ≤ branchBound c u t := by
    obtain ⟨δ, hδ, hδ_spec⟩ := hbranch c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, ?_⟩
    intro t ht u hu
    have hnorm : ‖t‖ < δ := by
      simpa only [dist_zero_right] using ht
    exact hδ_spec u hu t hnorm
  have hbranch_eventually' (c : Composition r) :
      ∀ᶠ t in 𝓝 (0 : ℝ), c ≠ Composition.ones r →
        ∀ u ∈ K, ‖b c u t‖ ≤ branchBound c u t := by
    by_cases hc : c = Composition.ones r
    · filter_upwards [] with t hct
      exact (hct hc).elim
    · simpa [hc] using hbranch_eventually c hc
  have hAll : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ c : Composition r,
      c ≠ Composition.ones r → ∀ u ∈ K,
        ‖b c u t‖ ≤ branchBound c u t :=
    (Filter.eventually_all).mpr hbranch_eventually'
  obtain ⟨δ, hδ, hδ_spec⟩ := Metric.eventually_nhds_iff.mp hAll
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hbranches : ∀ c : Composition r, c ≠ Composition.ones r →
      ‖b c u t‖ ≤ branchBound c u t := by
    intro c hc
    have hdist : dist t 0 < δ := by
      simpa only [dist_zero_right] using ht
    exact hδ_spec hdist c hc u hu
  have hsum := UniformRemainder.finiteNonDistinguishedSum_norm_le
    (Composition.ones r) (fun c : Composition r ↦ b c u t)
      (fun c : Composition r ↦ branchBound c u t) hbranches
  simpa only [branchBound] using hsum

/-- Helper for Infrastructure I.16a: a source-side budget for the length-split branch bounds
    turns the finite non-all-ones sum directly into its forcing estimate. -/
theorem composition_nonOnes_norm_le_of_length_split_budget
    {r : ℕ} {Θ : Type u} {E : Type v}
    [NormedAddCommGroup E] (K : Set Θ)
    (b : Composition r → Θ → ℝ → E)
    (lowerBound criticalBound : Composition r → Θ → ℝ → ℝ)
    (η : ℝ)
    (h_lower : ∀ c, c ≠ Composition.ones r → c.length < r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ lowerBound c u t)
    (h_critical : ∀ c, c ≠ Composition.ones r → c.length = r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ criticalBound c u t)
    (hbudget : ∀ u ∈ K, ∀ t : ℝ,
      (∑ c : Composition r,
        if c = Composition.ones r then 0
        else if c.length < r - 1 then lowerBound c u t else criticalBound c u t) ≤
        η * ‖t‖) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : Composition r,
          if c = Composition.ones r then 0 else b c u t‖ ≤ η * ‖t‖ := by
  obtain ⟨δ, hδ, hsum⟩ := composition_nonOnes_uniformBoundOn_of_length_split
    K b lowerBound criticalBound h_lower h_critical
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  exact (hsum u hu t ht).trans (hbudget u hu t)

/-- Helper for Infrastructure I.16a: linear lower-order and critical-order
    branch bounds specialize the length-split estimate to a common increment scale. -/
theorem composition_nonOnes_linearUniformBoundOn_of_length_split
    {r : ℕ} {Θ : Type u} {E : Type v}
    [NormedAddCommGroup E] (K : Set Θ)
    (b : Composition r → Θ → ℝ → E)
    (lowerBound criticalBound : Composition r → ℝ)
    (h_lower : ∀ c, c ≠ Composition.ones r → c.length < r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ lowerBound c * ‖t‖)
    (h_critical : ∀ c, c ≠ Composition.ones r → c.length = r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ criticalBound c * ‖t‖) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : Composition r,
          if c = Composition.ones r then 0 else b c u t‖ ≤
        (∑ c : Composition r,
          if c = Composition.ones r then 0
          else if c.length < r - 1 then lowerBound c else criticalBound c) *
          ‖t‖ := by
  let lower : Composition r → Θ → ℝ → ℝ := fun c _ t ↦ lowerBound c * ‖t‖
  let critical : Composition r → Θ → ℝ → ℝ := fun c _ t ↦ criticalBound c * ‖t‖
  have h_lower' : ∀ c, c ≠ Composition.ones r → c.length < r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ lower c u t := by
    intro c hc hlength
    obtain ⟨δ, hδ, hδ_spec⟩ := h_lower c hc hlength
    refine ⟨δ, hδ, ?_⟩
    intro u hu t ht
    simpa only [lower] using hδ_spec u hu t ht
  have h_critical' : ∀ c, c ≠ Composition.ones r → c.length = r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ critical c u t := by
    intro c hc hlength
    obtain ⟨δ, hδ, hδ_spec⟩ := h_critical c hc hlength
    refine ⟨δ, hδ, ?_⟩
    intro u hu t ht
    simpa only [critical] using hδ_spec u hu t ht
  obtain ⟨δ, hδ, hsum⟩ :=
    composition_nonOnes_uniformBoundOn_of_length_split K b lower critical
      h_lower' h_critical'
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hsum' := hsum u hu t ht
  dsimp only [lower, critical] at hsum'
  calc
    ‖∑ c : Composition r,
        if c = Composition.ones r then 0 else b c u t‖ ≤
        ∑ c : Composition r,
          if c = Composition.ones r then 0
          else if c.length < r - 1 then lowerBound c * ‖t‖
          else criticalBound c * ‖t‖ := hsum'
    _ = (∑ c : Composition r,
          if c = Composition.ones r then 0
          else if c.length < r - 1 then lowerBound c else criticalBound c) *
          ‖t‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hones : c = Composition.ones r
      · simp [hones]
      · by_cases hlow : c.length < r - 1
        · simp [hones, hlow]
        · simp [hones, hlow]

/-
  The constant-coefficient form is the source-facing specialization used when
  all lower and critical branches have already been assigned one scalar budget.
-/

/-- Helper for Infrastructure I.16a: a scalar budget for the lower and critical
    branch constants turns the linear length-split estimate into a forcing bound. -/
theorem composition_nonOnes_norm_le_of_length_split_linear_budget
    {r : ℕ} {Θ : Type u} {E : Type v}
    [NormedAddCommGroup E] (K : Set Θ)
    (b : Composition r → Θ → ℝ → E)
    (lowerBound criticalBound : Composition r → ℝ)
    (η : ℝ)
    (h_lower : ∀ c, c ≠ Composition.ones r → c.length < r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ lowerBound c * ‖t‖)
    (h_critical : ∀ c, c ≠ Composition.ones r → c.length = r - 1 →
      ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
        ‖t‖ < δ → ‖b c u t‖ ≤ criticalBound c * ‖t‖)
    (hbudget :
      (∑ c : Composition r,
        if c = Composition.ones r then 0
        else if c.length < r - 1 then lowerBound c else criticalBound c) ≤ η) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : Composition r,
          if c = Composition.ones r then 0 else b c u t‖ ≤ η * ‖t‖ := by
  obtain ⟨δ, hδ, hsum⟩ :=
    composition_nonOnes_linearUniformBoundOn_of_length_split
      K b lowerBound criticalBound h_lower h_critical
  refine ⟨δ, hδ, ?_⟩
  intro u hu t ht
  have hcoeff := mul_le_mul_of_nonneg_right hbudget (norm_nonneg t)
  calc
    ‖∑ c : Composition r,
        if c = Composition.ones r then 0 else b c u t‖ ≤
        (∑ c : Composition r,
          if c = Composition.ones r then 0
          else if c.length < r - 1 then lowerBound c else criticalBound c) *
          ‖t‖ := hsum u hu t ht
    _ ≤ η * ‖t‖ := hcoeff

end LocalCutoff.GraphTransform

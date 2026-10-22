/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators
open scoped ENNReal
open scoped Function

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Helper for Theorem 4.26: decompose the tail integral on `(0, ∞)` into the sum of the
integrals over the unit intervals `(n, n + 1]`. -/
lemma lintegral_Ioi_eq_tsum_lintegral_Ioc_nat (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0 : ℝ), g t ∂volume =
      ∑' n : ℕ, ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), g t ∂volume := by
  have h_union : (⋃ n : ℕ, Set.Ioc (n : ℝ) (n + 1)) = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      exact lt_of_le_of_lt (by exact_mod_cast Nat.zero_le n) hn.1
    · intro hx
      let N : ℕ := Nat.ceil x
      have hN : 1 ≤ N := by
        simpa [N] using (Nat.one_le_ceil_iff.mpr hx)
      refine Set.mem_iUnion.mpr ⟨N - 1, ?_⟩
      constructor
      · -- The left endpoint is strictly smaller because `N = ⌈x⌉`.
        have hceil : (N - 1 : ℕ) + 1 ≤ Nat.ceil x := by
          simp [N, Nat.sub_add_cancel hN]
        exact (Nat.add_one_le_ceil_iff.mp hceil)
      · -- The right endpoint bounds `x` from above by the defining property of the ceiling.
        have hcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
          exact_mod_cast (Nat.sub_add_cancel hN)
        calc
          x ≤ Nat.ceil x := by exact Nat.le_ceil x
          _ = (((N - 1 : ℕ) : ℝ) + 1) := by
                simpa [N] using hcast.symm
  have h_disjoint : Pairwise (Disjoint on fun n : ℕ => Set.Ioc (n : ℝ) (n + 1)) := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact Set.Ioc_disjoint_Ioc_of_le (by exact_mod_cast hlt)
    · exact (Set.Ioc_disjoint_Ioc_of_le (by exact_mod_cast hgt)).symm
  -- Rewrite the integral over `(0, ∞)` as the sum over the disjoint unit intervals.
  rw [← h_union]
  simpa using (MeasureTheory.lintegral_iUnion (fun n : ℕ => measurableSet_Ioc) h_disjoint g)

/-- Helper for Theorem 4.26: on each unit interval `(n, n + 1]`, the tail function
`t ↦ μ {ω | t ≤ f ω}` is bounded below by the constant value `μ {ω | n + 1 ≤ f ω}`. -/
lemma measure_superlevel_le_lintegral_tail_on_unit_interval {f : Ω → ℝ} (n : ℕ) :
    μ {ω | (n + 1 : ℝ) ≤ f ω} ≤
      ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | t ≤ f ω} ∂volume := by
  have hpoint :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (n : ℝ) (n + 1)),
        μ {ω | (n + 1 : ℝ) ≤ f ω} ≤ μ {ω | t ≤ f ω} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hsubset : {ω | (n + 1 : ℝ) ≤ f ω} ⊆ {ω | t ≤ f ω} := by
      intro ω hω
      exact le_trans ht.2 hω
    exact measure_mono hsubset
  -- Compare the interval integral with the constant lower bound coming from the right endpoint.
  calc
    μ {ω | (n + 1 : ℝ) ≤ f ω}
        = ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | (n + 1 : ℝ) ≤ f ω} ∂volume := by
            rw [MeasureTheory.setLIntegral_const]
            simp [Real.volume_Ioc]
    _ ≤ ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | t ≤ f ω} ∂volume := by
          exact MeasureTheory.lintegral_mono_ae hpoint

/-- Helper for Theorem 4.26: on each unit interval `(n, n + 1]`, the tail function
`t ↦ μ {ω | t < f ω}` is bounded above by the constant value `μ {ω | n < f ω}`. -/
lemma lintegral_tail_on_unit_interval_le_measure_strict_superlevel {f : Ω → ℝ} (n : ℕ) :
    ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | t < f ω} ∂volume ≤
      μ {ω | (n : ℝ) < f ω} := by
  have hpoint :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (n : ℝ) (n + 1)),
        μ {ω | t < f ω} ≤ μ {ω | (n : ℝ) < f ω} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hsubset : {ω | t < f ω} ⊆ {ω | (n : ℝ) < f ω} := by
      intro ω hω
      exact lt_trans ht.1 hω
    exact measure_mono hsubset
  -- Compare pointwise on the interval and then evaluate the constant interval integral.
  calc
    ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | t < f ω} ∂volume
        ≤ ∫⁻ t in Set.Ioc (n : ℝ) (n + 1), μ {ω | (n : ℝ) < f ω} ∂volume := by
            exact MeasureTheory.lintegral_mono_ae hpoint
    _ = μ {ω | (n : ℝ) < f ω} := by
          rw [MeasureTheory.setLIntegral_const]
          simp [Real.volume_Ioc]

-- Proof sketch: compare `f` from below with `⌊f⌋`, write the integral of the integer-valued
-- approximation as a countable sum over its level sets, and then identify those level sets with
-- `{ω | n ≤ f ω}` for integers `n ≥ 1`.
/-- Theorem 4.26 (1): Equation `(4.7)`, lower bound. For a measurable real-valued function that is
nonnegative almost everywhere, the sum of the measures of the superlevel sets `{f ≥ n}` over
positive integers is bounded above by the nonnegative integral of `f`. -/
theorem tsum_measure_superlevel_nat_le_lintegral {f : Ω → ℝ} (hf : Measurable f)
    (h_nonneg : 0 ≤ᵐ[μ] f) :
    (∑' n : ℕ, μ {ω | (n + 1 : ℝ) ≤ f ω}) ≤ ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ := by
  -- Rewrite the integral as the tail integral over `(0, ∞)` and decompose into unit intervals.
  rw [MeasureTheory.lintegral_eq_lintegral_meas_le μ h_nonneg hf.aemeasurable,
    lintegral_Ioi_eq_tsum_lintegral_Ioc_nat]
  -- Each summand is controlled by the tail measure at the right endpoint of the interval.
  exact ENNReal.tsum_le_tsum fun n =>
    measure_superlevel_le_lintegral_tail_on_unit_interval (μ := μ) (f := f) n

-- Proof sketch: compare `f` from above with `⌈f⌉`, express the integral of this integer-valued
-- majorant as a countable sum over its level sets, and rewrite these level sets as `{ω | f ω > n}`
-- for natural numbers `n`.
/-- Theorem 4.26 (2): Equation `(4.7)`, upper bound. For a measurable real-valued function that is
nonnegative almost everywhere, the nonnegative integral of `f` is bounded above by the sum of the
measures of the strict superlevel sets `{f > n}` over natural numbers. -/
theorem lintegral_le_tsum_measure_strict_superlevel_nat {f : Ω → ℝ} (hf : Measurable f)
    (h_nonneg : 0 ≤ᵐ[μ] f) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ∑' n : ℕ, μ {ω | ((n : ℝ) < f ω)} := by
  -- Rewrite the integral using the strict tail version of layer cake and split into unit intervals.
  rw [MeasureTheory.lintegral_eq_lintegral_meas_lt μ h_nonneg hf.aemeasurable,
    lintegral_Ioi_eq_tsum_lintegral_Ioc_nat]
  -- Each unit-interval contribution is bounded by the strict superlevel set at the left endpoint.
  exact ENNReal.tsum_le_tsum fun n =>
    lintegral_tail_on_unit_interval_le_measure_strict_superlevel (μ := μ) (f := f) n

/- Theorem 4.26 (3): Equation `(4.8)`. The canonical mathlib form of the layer-cake formula is
`MeasureTheory.lintegral_eq_lintegral_meas_le`, which assumes only `AEMeasurable` together with
almost-everywhere nonnegativity. -/
recall MeasureTheory.lintegral_eq_lintegral_meas_le

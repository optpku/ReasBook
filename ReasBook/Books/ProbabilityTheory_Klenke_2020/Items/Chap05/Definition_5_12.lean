/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The centered partial sum attached to the first `n` terms of a `0`-based real-valued sequence.
-/
def centered_partial_sum (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, (X i ω - μ[X i])

/-- The normalized centered average `\widetilde S_n / n`. -/
def centered_average (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ centered_partial_sum μ X n ω / n

/-- For the textbook sequence `X₁, X₂, …`, represented by `fun n ↦ X (n + 1)`, the centered
partial sum is `∑_{i=1}^n (Xᵢ - 𝔼[Xᵢ])`. -/
private theorem centered_partial_sum_def (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    centered_partial_sum μ (fun k ↦ X (k + 1)) n =
      fun ω ↦ ∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i]) := by
  -- Proof comment: rewrite the shifted `range n` sum as the textbook interval `Icc 1 n`.
  ext ω
  rw [centered_partial_sum]
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- For the textbook sequence `X₁, X₂, …`, represented by `fun n ↦ X (n + 1)`, the normalized
centered average is `(1 / n) * ∑_{i=1}^n (Xᵢ - 𝔼[Xᵢ])`. -/
private theorem centered_average_def (μ : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    centered_average μ (fun k ↦ X (k + 1)) n =
      fun ω ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n := by
  -- Proof comment: unfold the normalization and reuse the centered-sum bridge.
  ext ω
  rw [centered_average, centered_partial_sum_def]

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Definition 5.12 (1): Item (i). A `0`-based Lean sequence `X 0, X 1, …` satisfies the weak law
of large numbers if its terms are integrable and the normalized centered averages converge to `0`
in probability. For the textbook sequence `X₁, X₂, …`, apply this definition to
`fun n ↦ X (n + 1)`. -/
def satisfies_weak_law_of_large_numbers (X : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Integrable (X n) μ) ∧
    TendstoInMeasure μ (centered_average μ X) atTop 0

/-- Definition 5.12 (2): Item (ii). A `0`-based Lean sequence `X 0, X 1, …` satisfies the strong
law of large numbers if its terms are integrable and the normalized centered averages converge
almost surely to `0`. For the textbook sequence `X₁, X₂, …`, apply this definition to
`fun n ↦ X (n + 1)`. -/
def satisfies_strong_law_of_large_numbers (X : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Integrable (X n) μ) ∧
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ centered_average μ X n ω) atTop (𝓝 0)

omit [IsProbabilityMeasure μ] in
/-- For an identically distributed textbook sequence `X₁, X₂, …`, each shifted variable
`X (n + 1)` has the same expectation as `X 1`. -/
theorem expectation_eq_of_shifted_identDistrib
    (X : ℕ → Ω → ℝ) (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) μ μ) (n : ℕ) :
    μ[X (n + 1)] = μ[X 1] := by
  simpa using (hX_ident n).integral_eq

omit [IsProbabilityMeasure μ] in
/-- For positive indices, the centered empirical average of the shifted sequence is the raw
empirical average minus the common mean. -/
theorem centered_average_eq_raw_average_sub_mean
    (X : ℕ → Ω → ℝ) (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) μ μ)
    (ω : Ω) {n : ℕ} (hn : 0 < n) :
    centered_average μ (fun k ↦ X (k + 1)) n ω =
      (∑ i ∈ Finset.range n, X (i + 1) ω) / n - μ[X 1] := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  rw [centered_average, centered_partial_sum, Finset.sum_sub_distrib]
  simp_rw [expectation_eq_of_shifted_identDistrib μ X hX_ident]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_div, mul_div_cancel_left₀ _ hnR]

omit [IsProbabilityMeasure μ] in
/-- An almost sure limit statement for the raw empirical averages of the textbook sequence
translates to the centered-average limit in Definition 5.12. -/
theorem ae_tendsto_centered_average_of_ae_tendsto_raw_average
    (X : ℕ → Ω → ℝ) (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) μ μ)
    (hraw :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n) atTop (𝓝 μ[X 1])) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ centered_average μ (fun k ↦ X (k + 1)) n ω) atTop (𝓝 0) := by
  filter_upwards [hraw] with ω hω
  have heq :
      (fun n ↦ centered_average μ (fun k ↦ X (k + 1)) n ω) =ᶠ[atTop]
        (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X (i + 1) ω) / n - μ[X 1]) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact centered_average_eq_raw_average_sub_mean μ X hX_ident ω (Nat.succ_le_iff.mp hn)
  have hcentered :
      Tendsto (fun n ↦ centered_average μ (fun k ↦ X (k + 1)) n ω) atTop
        (𝓝 (μ[X 1] - μ[X 1])) := by
    refine Tendsto.congr' heq.symm ?_
    exact hω.sub tendsto_const_nhds
  simpa using hcentered

section

omit [IsProbabilityMeasure μ]

/-- For the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, the weak law amounts to
integrability of all terms together with convergence in probability of the centered empirical
averages to `0`. -/
private theorem satisfies_weak_law_of_large_numbers_iff (X : ℕ → Ω → ℝ) :
    satisfies_weak_law_of_large_numbers μ (fun n ↦ X (n + 1)) ↔
      (∀ n, Integrable (X (n + 1)) μ) ∧
        TendstoInMeasure μ
          (fun n ω ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n)
          atTop 0 := by
  -- Proof comment: the only nontrivial step is transporting convergence in measure
  -- across the pointwise equality from `centered_average_def`.
  have havg :
      centered_average μ (fun n ↦ X (n + 1)) =
        fun n ω ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n := by
    funext n
    exact centered_average_def μ X n
  constructor
  · rintro ⟨hInt, hT⟩
    refine ⟨?_, ?_⟩
    · simpa using hInt
    · simpa [havg] using hT
  · rintro ⟨hInt, hT⟩
    refine ⟨?_, ?_⟩
    · simpa using hInt
    · simpa [havg] using hT

/-- For the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, the weak law is
equivalently expressed by the vanishing of the deviation probabilities of the centered empirical
averages. This is the textbook expansion of
`satisfies_weak_law_of_large_numbers_iff` via `tendstoInMeasure_iff_norm`. -/
private theorem satisfies_weak_law_of_large_numbers_iff_probability (X : ℕ → Ω → ℝ) :
    satisfies_weak_law_of_large_numbers μ (fun n ↦ X (n + 1)) ↔
      (∀ n, Integrable (X (n + 1)) μ) ∧
        ∀ ⦃ε : ℝ⦄, 0 < ε →
          Tendsto
            (fun n ↦ μ {ω | ε ≤ |(∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n|})
            atTop (𝓝 0) := by
  rw [satisfies_weak_law_of_large_numbers_iff]
  constructor
  · rintro ⟨hInt, hT⟩
    refine ⟨hInt, ?_⟩
    -- Proof comment: rewrite convergence in measure with the norm criterion and
    -- simplify `‖x - 0‖` to `|x|` on `ℝ`.
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] using
      (MeasureTheory.tendstoInMeasure_iff_norm
        (μ := μ)
        (l := atTop)
        (f := fun n ω ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n)
        (g := 0)).mp hT
  · rintro ⟨hInt, hT⟩
    refine ⟨hInt, ?_⟩
    rw [MeasureTheory.tendstoInMeasure_iff_norm]
    intro ε hε
    simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hT (ε := ε) hε

/-- For the textbook sequence `X₁, X₂, …`, represented by `X 1, X 2, …`, the strong law amounts to
integrability of all terms together with almost sure convergence of the centered empirical
averages to `0`. -/
private theorem satisfies_strong_law_of_large_numbers_iff (X : ℕ → Ω → ℝ) :
    satisfies_strong_law_of_large_numbers μ (fun n ↦ X (n + 1)) ↔
      (∀ n, Integrable (X (n + 1)) μ) ∧
        ∀ᵐ ω ∂μ, Tendsto
          (fun n ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n) atTop (𝓝 0) := by
  -- Proof comment: rewrite the almost-sure convergence statement pointwise using
  -- the same average identity as in the weak-law formulation.
  have havg :
      ∀ ω,
        (fun n ↦ centered_average μ (fun k ↦ X (k + 1)) n ω) =
          fun n ↦ (∑ i ∈ Finset.Icc 1 n, (X i ω - μ[X i])) / n := by
    intro ω
    funext n
    simpa using congrFun (centered_average_def μ X n) ω
  constructor
  · rintro ⟨hInt, hT⟩
    refine ⟨?_, ?_⟩
    · simpa using hInt
    · filter_upwards [hT] with ω hω
      simpa [havg ω] using hω
  · rintro ⟨hInt, hT⟩
    refine ⟨?_, ?_⟩
    · simpa using hInt
    · filter_upwards [hT] with ω hω
      simpa [havg ω] using hω

end

end

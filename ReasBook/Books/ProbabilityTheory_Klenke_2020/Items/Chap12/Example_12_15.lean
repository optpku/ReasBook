/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Exercise_12_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

omit [MeasurableSpace Ω] in
private theorem exchangeableAverage_apply_zero_comp_swap_eq_exchangeableCesaroAverage
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    exchangeableAverage (n + 1) (fun x ↦ x 0) ∘ Function.swap X =
      exchangeableCesaroAverage X n := by
  funext ω
  have h_average :=
    congrArg (fun f ↦ f (Function.swap X ω))
      (exchangeableAverage_apply_zero ⟨n + 1, Nat.succ_pos n⟩)
  have h_sum :
      (∑ i : Fin (n + 1), X i ω) = ∑ i ∈ Finset.range (n + 1), X i ω := by
    simpa using (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ X i ω) (n + 1))
  have h_cesaro := congrArg (fun f ↦ f ω) (exchangeableCesaroAverage_def X n)
  calc
    exchangeableAverage (n + 1) (fun x ↦ x 0) (Function.swap X ω) =
        (∑ i : Fin (n + 1), X i ω) / ((n + 1 : ℕ) : ℝ) := by
          simpa [Function.swap] using h_average
    _ = (∑ i ∈ Finset.range (n + 1), X i ω) / ((n + 1 : ℕ) : ℝ) := by rw [h_sum]
    _ = (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1), X i ω) := by
          rw [div_eq_mul_inv, mul_comm]
    _ = exchangeableCesaroAverage X n ω := by
          simpa using h_cesaro.symm

-- Proof sketch: Example 12.13 identifies the Cesàro averages as a backwards martingale for the
-- exchangeable filtration, so the backwards martingale limit is
-- `μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)]`. Example 2.36 makes this limit
-- tail-measurable, and then the tower
-- property upgrades tail measurability to the claimed almost-everywhere equality.
/-- Example 12.15 (1): for an exchangeable real sequence with integrable first coordinate,
conditioning the first variable on the tail `σ`-algebra agrees almost surely with conditioning on
the exchangeable `σ`-algebra. -/
theorem condExp_first_tail_ae_eq_condExp_first_exchangeableSigmaAlgebra
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hX_exchangeable : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n))
    (hX0_integrable : Integrable (X 0) μ) :
    μ[X 0 | tailRandomVariableMeasurableSpace X] =ᵐ[μ]
      μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)] := by
  let φ : (Fin 1 → ℝ) → ℝ := fun y ↦ y 0
  have hφ_meas : Measurable φ := by
    simpa [φ] using measurable_pi_apply 0
  have hφ_int : Integrable (fun ω ↦ φ (fun i ↦ X i ω)) μ := by
    simpa [φ] using hX0_integrable
  simpa using
    (exchangeableAverage_limit_of_isExchangeable hX_exchangeable hX_meas hφ_meas hφ_int).1.symm

-- Proof sketch: combine the permutation-average identity from Theorem 12.10 with the backwards
-- martingale convergence theorem applied to the exchangeable filtration; the resulting limit is
-- the conditional expectation of `X 0` with respect to the exchangeable `σ`-algebra.
/-- Example 12.15 (2): the Cesàro averages of an exchangeable real sequence with integrable first
coordinate converge almost surely to the conditional expectation of the first variable given the
exchangeable `σ`-algebra. -/
theorem exchangeableCesaroAverage_tendsto_ae_condExp_first_exchangeableSigmaAlgebra
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hX_exchangeable : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n))
    (hX0_integrable : Integrable (X 0) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ exchangeableCesaroAverage X n ω) atTop
      (nhds (μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)] ω)) := by
  let φ : (Fin 1 → ℝ) → ℝ := fun y ↦ y 0
  have hφ_meas : Measurable φ := by
    simpa [φ] using measurable_pi_apply 0
  have hφ_int : Integrable (fun ω ↦ φ (fun i ↦ X i ω)) μ := by
    simpa [φ] using hX0_integrable
  have h_owner :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ exchangeableAverage n (fun y ↦ y 0) (Function.swap X ω))
          atTop (nhds (μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)] ω)) := by
    simpa using
      (exchangeableAverage_limit_of_isExchangeable hX_exchangeable hX_meas hφ_meas hφ_int).2.1
  have h_owner_shift :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ exchangeableAverage (n + 1) (fun y ↦ y 0) (Function.swap X ω))
          atTop
          (nhds (μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)] ω)) := by
    filter_upwards [h_owner] with ω hω
    exact hω.comp (tendsto_add_atTop_nat 1)
  have h_bridge :
      ∀ᵐ ω ∂μ, ∀ n,
        exchangeableAverage (n + 1) (fun y ↦ y 0) (Function.swap X ω) =
          exchangeableCesaroAverage X n ω := by
    rw [ae_all_iff]
    intro n
    exact Filter.EventuallyEq.of_eq
      (exchangeableAverage_apply_zero_comp_swap_eq_exchangeableCesaroAverage X n)
  filter_upwards [h_owner_shift, h_bridge] with ω hω hω_bridge
  convert hω using 1
  funext n
  exact (hω_bridge n).symm

-- Proof sketch: apply the `L¹` martingale convergence theorem to the backwards martingale of
-- exchangeable averages, identifying its limit with `μ[X 0 | exchangeableSigmaAlgebra X]`.
/-- Example 12.15 (3): the Cesàro averages of an exchangeable real sequence with integrable first
coordinate converge in `L¹` to the conditional expectation of the first variable given the
exchangeable `σ`-algebra. -/
theorem exchangeableCesaroAverage_tendsto_eLpNorm_condExp_first_exchangeableSigmaAlgebra
    {X : ℕ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hX_exchangeable : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n))
    (hX0_integrable : Integrable (X 0) μ) :
    Tendsto
      (fun n ↦
        eLpNorm
          (exchangeableCesaroAverage X n -
            μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)])
          1 μ)
      atTop (nhds 0) := by
  let φ : (Fin 1 → ℝ) → ℝ := fun y ↦ y 0
  have hφ_meas : Measurable φ := by
    simpa [φ] using measurable_pi_apply 0
  have hφ_int : Integrable (fun ω ↦ φ (fun i ↦ X i ω)) μ := by
    simpa [φ] using hX0_integrable
  let G : Ω → ℝ := μ[X 0 | exchangeableSigmaAlgebra (Function.swap X)]
  change Tendsto (fun n ↦ eLpNorm (exchangeableCesaroAverage X n - G) 1 μ) atTop (nhds 0)
  have h_owner :
      Tendsto
        (fun n ↦
          eLpNorm (exchangeableAverage n (fun y ↦ y 0) ∘ Function.swap X - G) 1 μ)
        atTop (nhds 0) := by
    simpa [G] using
      (exchangeableAverage_limit_of_isExchangeable
        hX_exchangeable hX_meas hφ_meas hφ_int).2.2.tendsto_eLpNorm
  have h_owner_shift :
      Tendsto
        (fun n ↦
          eLpNorm (exchangeableAverage (n + 1) (fun y ↦ y 0) ∘ Function.swap X - G) 1 μ)
        atTop (nhds 0) := h_owner.comp (tendsto_add_atTop_nat 1)
  have h_eq :
      (fun n ↦ eLpNorm (exchangeableCesaroAverage X n - G) 1 μ) =
        fun n ↦
          eLpNorm (exchangeableAverage (n + 1) (fun y ↦ y 0) ∘ Function.swap X - G) 1 μ := by
    funext n
    rw [← exchangeableAverage_apply_zero_comp_swap_eq_exchangeableCesaroAverage X n]
  rw [h_eq]
  exact h_owner_shift

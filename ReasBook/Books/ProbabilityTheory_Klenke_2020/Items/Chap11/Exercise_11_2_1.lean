/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Exercise_10_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

namespace MeasureTheory

/- Exercise 11.2.1 is `source-facing`: it asserts the existence of a filtered probability space
supporting a martingale with four standard properties. The `core/canonical` owner layer is the
existing martingale API (`Martingale`, pointwise nonnegativity, expectation identities, and
almost-sure convergence), so no extra witness structure is kept here. -/

section Counterexample

/-- Helper for Exercise 11.2.1: the desired nonnegative martingale is the complement `1 - Xₙ` of
the geometric counterexample martingale from Exercise 10.2.1. -/
def counterexampleComplement : ℕ → ℕ → ℝ :=
  fun n ω ↦ 1 - counterexampleProcess n ω

/-- Helper for Exercise 11.2.1: the complemented geometric process is again a martingale. -/
private theorem counterexampleComplement_martingale :
    Martingale counterexampleComplement counterexampleFiltration counterexampleMeasure := by
  -- Subtract the imported martingale from the constant-one martingale.
  simpa [counterexampleComplement] using
    (martingale_const counterexampleFiltration counterexampleMeasure (1 : ℝ)).sub
      counterexampleProcess_martingale

/-- Helper for Exercise 11.2.1: the complemented geometric process is pointwise nonnegative. -/
private theorem counterexampleComplement_nonneg :
    0 ≤ counterexampleComplement := by
  intro n ω
  by_cases hω : ω < n
  · simp [counterexampleComplement, counterexampleProcess, hω]
  · simp [counterexampleComplement, counterexampleProcess, hω]

/-- Helper for Exercise 11.2.1: the complemented geometric process has expectation `1` at every
deterministic time. -/
private theorem counterexampleComplement_expectation_one (n : ℕ) :
    counterexampleMeasure[counterexampleComplement n] = 1 := by
  have hExpZero : counterexampleMeasure[counterexampleProcess n] = 0 := by
    rw [← martingale_expectation_eq counterexampleProcess_martingale (Nat.zero_le n)]
    simp [counterexampleProcess]
  have hIntegral :
      counterexampleMeasure[counterexampleComplement n] =
        counterexampleMeasure[(fun _ : ℕ ↦ (1 : ℝ))] -
          counterexampleMeasure[counterexampleProcess n] := by
    -- Rewrite the complement as a difference and apply linearity of expectation.
    simpa [counterexampleComplement] using
      (integral_sub' (integrable_const (1 : ℝ))
        (counterexampleProcess_martingale.integrable n))
  rw [hIntegral, hExpZero]
  simp

/-- Helper for Exercise 11.2.1: along every sample path the complemented process is eventually
equal to `0`. -/
private theorem counterexampleComplement_tendsto_zero (ω : ℕ) :
    Tendsto (fun n ↦ counterexampleComplement n ω) atTop (𝓝 (0 : ℝ)) := by
  -- For fixed `ω`, the process is exactly `0` once `n > ω`.
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop ω] with n hn
  simp [counterexampleComplement, counterexampleProcess, hn]

/-- Helper for Exercise 11.2.1: the complemented geometric process converges almost surely to `0`.
-/
private theorem counterexampleComplement_ae_tendsto_zero :
    ∀ᵐ ω ∂counterexampleMeasure,
      Tendsto (fun n ↦ counterexampleComplement n ω) atTop (𝓝 (0 : ℝ)) := by
  exact Filter.Eventually.of_forall counterexampleComplement_tendsto_zero

/-- Helper for Exercise 11.2.1: the witness sample space is `ULift ℕ`, viewed in universe `u`. -/
private abbrev Omega0 : Type u := ULift ℕ

/-- Helper for Exercise 11.2.1: the canonical measurable equivalence `ℕ ≃ᵐ ULift ℕ`. -/
private abbrev omega0Equiv : ℕ ≃ᵐ Omega0 :=
  show ℕ ≃ᵐ Omega0 from MeasurableEquiv.ulift.symm

/-- Helper for Exercise 11.2.1: the counterexample measure transported to `ULift ℕ`. -/
noncomputable def liftedCounterexampleMeasure : Measure Omega0 :=
  counterexampleMeasure.map ULift.up

/-- Helper for Exercise 11.2.1: the lifted counterexample measure is a probability measure. -/
instance liftedCounterexampleMeasure_isProbabilityMeasure :
    IsProbabilityMeasure liftedCounterexampleMeasure := by
  change IsProbabilityMeasure (counterexampleMeasure.map ULift.up)
  infer_instance

/-- Helper for Exercise 11.2.1: the lifted filtration reveals the truncated waiting time
`ω ↦ min (ULift.down ω) n`. -/
noncomputable def liftedCounterexampleFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace Omega0) :=
  { seq := fun n ↦ MeasurableSpace.comap ULift.down (counterexampleFiltration n)
    mono' := by
      intro n m hnm s hs
      rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
      exact MeasurableSpace.measurableSet_comap.2 ⟨t, counterexampleFiltration.mono hnm t ht, rfl⟩
    le' := by
      intro n s hs
      rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
      exact measurable_down (counterexampleFiltration.le n t ht) }

/-- Helper for Exercise 11.2.1: the complemented counterexample process on `ULift ℕ`. -/
def liftedCounterexampleComplement : ℕ → Omega0 → ℝ :=
  fun n ω ↦ counterexampleComplement n (ULift.down ω)

/-- Helper for Exercise 11.2.1: each lifted time slice is strongly measurable with respect to the
lifted filtration. -/
private theorem liftedCounterexampleComplement_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable[liftedCounterexampleFiltration n] (liftedCounterexampleComplement n) := by
  have hdown :
      @Measurable Omega0 ℕ (liftedCounterexampleFiltration n) (counterexampleFiltration n)
        ULift.down := by
    change @Measurable Omega0 ℕ
      (MeasurableSpace.comap ULift.down (counterexampleFiltration n))
      (counterexampleFiltration n) ULift.down
    exact comap_measurable ULift.down
  simpa [liftedCounterexampleComplement] using
    (counterexampleComplement_martingale.stronglyMeasurable n).comp_measurable hdown

/-- Helper for Exercise 11.2.1: the lifted complemented process is strongly adapted. -/
private theorem liftedCounterexampleComplement_stronglyAdapted :
    StronglyAdapted liftedCounterexampleFiltration liftedCounterexampleComplement := by
  intro n
  exact liftedCounterexampleComplement_stronglyMeasurable n

/-- Helper for Exercise 11.2.1: each lifted time slice is integrable. -/
private theorem liftedCounterexampleComplement_integrable (n : ℕ) :
    Integrable (liftedCounterexampleComplement n) liftedCounterexampleMeasure := by
  let A : Set Omega0 := {ω | ULift.down ω < n}
  have hEq :
      liftedCounterexampleComplement n =
        A.piecewise (fun _ : Omega0 ↦ (0 : ℝ)) (fun _ ↦ (2 : ℝ) ^ n) := by
    funext ω
    by_cases hω : ULift.down ω < n
    · simp [liftedCounterexampleComplement, counterexampleComplement, counterexampleProcess, A,
        Set.piecewise, hω]
    · simp [liftedCounterexampleComplement, counterexampleComplement, counterexampleProcess, A,
        Set.piecewise, hω]
  have hleft :
      IntegrableOn (fun _ : Omega0 ↦ (0 : ℝ)) A liftedCounterexampleMeasure :=
    integrableOn_const (measure_ne_top liftedCounterexampleMeasure A) (by simp)
  have hright :
      IntegrableOn (fun _ : Omega0 ↦ (2 : ℝ) ^ n) Aᶜ liftedCounterexampleMeasure :=
    integrableOn_const (measure_ne_top liftedCounterexampleMeasure Aᶜ) (by simp)
  rw [hEq]
  exact Integrable.piecewise (measurable_down measurableSet_Iio) hleft hright

/-- Helper for Exercise 11.2.1: transporting the complemented process along `ULift` preserves the
martingale property. -/
private theorem liftedCounterexampleComplement_martingale :
    Martingale liftedCounterexampleComplement liftedCounterexampleFiltration
      liftedCounterexampleMeasure := by
  -- Transport the deterministic-time set-integral martingale identity along `ULift`.
  refine martingale_of_setIntegral_eq_succ liftedCounterexampleComplement_stronglyAdapted
    liftedCounterexampleComplement_integrable ?_
  intro n s hs
  rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨t, ht, rfl⟩
  calc
    ∫ ω in ULift.down ⁻¹' t, liftedCounterexampleComplement n ω ∂liftedCounterexampleMeasure =
        ∫ x in t, counterexampleComplement n x ∂counterexampleMeasure := by
          simpa [liftedCounterexampleMeasure, liftedCounterexampleComplement] using
            (setIntegral_map_equiv (μ := counterexampleMeasure) omega0Equiv
              (liftedCounterexampleComplement n) (ULift.down ⁻¹' t))
    _ = ∫ x in t, counterexampleComplement (n + 1) x ∂counterexampleMeasure := by
          simpa using
            (counterexampleComplement_martingale.setIntegral_eq (Nat.le_succ n) ht)
    _ = ∫ ω in ULift.down ⁻¹' t, liftedCounterexampleComplement (n + 1) ω
          ∂liftedCounterexampleMeasure := by
          simpa [liftedCounterexampleMeasure, liftedCounterexampleComplement] using
            (setIntegral_map_equiv (μ := counterexampleMeasure) omega0Equiv
              (liftedCounterexampleComplement (n + 1)) (ULift.down ⁻¹' t)).symm

/-- Helper for Exercise 11.2.1: the lifted complemented process is pointwise nonnegative. -/
private theorem liftedCounterexampleComplement_nonneg :
    0 ≤ liftedCounterexampleComplement := by
  intro n ω
  simpa [liftedCounterexampleComplement] using
    counterexampleComplement_nonneg n (ULift.down ω)

/-- Helper for Exercise 11.2.1: the lifted complemented process has expectation `1` at every
deterministic time. -/
private theorem liftedCounterexampleComplement_expectation_one (n : ℕ) :
    liftedCounterexampleMeasure[liftedCounterexampleComplement n] = 1 := by
  have hIntegral :
      ∫ ω, liftedCounterexampleComplement n ω ∂liftedCounterexampleMeasure =
        ∫ x, counterexampleComplement n x ∂counterexampleMeasure := by
    simpa [liftedCounterexampleMeasure, liftedCounterexampleComplement, omega0Equiv] using
      (integral_map_equiv (μ := counterexampleMeasure) omega0Equiv
        (fun ω : Omega0 ↦ liftedCounterexampleComplement n ω))
  have hExpectation :
      ∫ ω, liftedCounterexampleComplement n ω ∂liftedCounterexampleMeasure = 1 :=
    hIntegral.trans (counterexampleComplement_expectation_one n)
  simpa using hExpectation

/-- Helper for Exercise 11.2.1: every lifted sample path converges to `0`. -/
private theorem liftedCounterexampleComplement_tendsto_zero (ω : Omega0) :
    Tendsto (fun n ↦ liftedCounterexampleComplement n ω) atTop (𝓝 (0 : ℝ)) := by
  simpa [liftedCounterexampleComplement] using
    counterexampleComplement_tendsto_zero (ULift.down ω)

/-- Helper for Exercise 11.2.1: the lifted complemented process converges almost surely to `0`.
-/
private theorem liftedCounterexampleComplement_ae_tendsto_zero :
    ∀ᵐ ω ∂liftedCounterexampleMeasure,
      Tendsto (fun n ↦ liftedCounterexampleComplement n ω) atTop (𝓝 (0 : ℝ)) := by
  exact Filter.Eventually.of_forall liftedCounterexampleComplement_tendsto_zero

/-- Exercise 11.2.1: there exists a filtered probability space carrying a nonnegative martingale
with expectation `1` at every time and which converges almost surely to `0`, so the `p = 1`
analogue of Theorem 11.10 can fail. -/
theorem exists_nonnegative_martingale_with_expectation_one_ae_tendsto_zero :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          0 ≤ X ∧
          (∀ n, μ[X n] = 1) ∧
          ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (0 : ℝ)) := by
  refine ⟨Omega0, inferInstance, liftedCounterexampleMeasure, inferInstance,
    liftedCounterexampleFiltration, liftedCounterexampleComplement, ?_⟩
  refine ⟨liftedCounterexampleComplement_martingale, liftedCounterexampleComplement_nonneg, ?_⟩
  exact ⟨liftedCounterexampleComplement_expectation_one,
    liftedCounterexampleComplement_ae_tendsto_zero⟩

end Counterexample

end MeasureTheory

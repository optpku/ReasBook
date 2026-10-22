/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
public import TR_LALM_theory.Corollary_4_2.StoppedRestartResidual
public import TR_LALM_theory.Corollary_4_2

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

namespace StoppedUniformResidualBridge

open StoppedAttemptAnalysis
open StochasticRun.Localization

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

/-- Helper for Corollary 4.2: mapping the right coordinate of a product
measure commutes with a measurable nonnegative integral. -/
theorem lintegral_prod_map_right
    {E : Type*} [MeasurableSpace E]
    (mu : Measure ℕ) (g : Ω → E) (hg : Measurable g)
    (F : ℕ × E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂mu.prod (P.map g)) =
      ∫⁻ z, F (z.1, g z.2) ∂mu.prod P := by
  have hsection (k : ℕ) :
      AEMeasurable (fun y : E ↦ F (k, y)) (P.map g) :=
    (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hcomposedSection (k : ℕ) :
      Measurable (fun omega ↦ F (k, g omega)) :=
    hF.comp (measurable_const.prodMk hg)
  have hcomposed : Measurable
      (fun z : ℕ × Ω ↦ F (z.1, g z.2)) :=
    measurable_from_prod_countable_right hcomposedSection
  calc
    (∫⁻ z, F z ∂mu.prod (P.map g)) =
        ∫⁻ k, ∫⁻ y, F (k, y) ∂P.map g ∂mu :=
      lintegral_prod F hF.aemeasurable
    _ = ∫⁻ k, ∫⁻ omega, F (k, g omega) ∂P ∂mu := by
      apply lintegral_congr
      intro k
      exact lintegral_map' (hsection k) hg.aemeasurable
    _ = ∫⁻ z, F (z.1, g z.2) ∂mu.prod P :=
      (lintegral_prod _ hcomposed.aemeasurable).symm

/-- Helper for Corollary 4.2: the finite observable success record is exactly
the analysis success event of the underlying stopped attempt. -/
theorem finiteObservable_mem_successRecord_iff_attempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) (omega : Ω) :
    stoppedAttemptFiniteObservable attempt omega ∈
        successRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      omega ∈ StoppedAttemptAnalysis.successEvent attempt := by
  rw [stoppedAttemptFiniteObservable_mem_successRecord_iff,
    successEvent_eq_stoppedAttempt]

/-- Helper for Corollary 4.2: finite stopped coordinates and a corrected
scheduled run have the same successful uniform-output residual integrand. -/
theorem finiteOutputResidualIntegrand_eq
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hsuccess : StoppedAttemptAnalysis.successEvent attempt =
      survivalEvent run X K)
    (hpoint : ∀ k ≤ K, ∀ omega,
      omega ∈ survivalEvent run X K →
        StoppedAttempt.point attempt k omega = run.point k omega)
    (hmultiplier : ∀ k ≤ K, ∀ omega,
      omega ∈ survivalEvent run X K →
        StoppedAttempt.multiplier attempt k omega = run.multiplier k omega)
    (hXregion : X ⊆ h.region) :
    (fun output : ℕ × Ω ↦ outputResidualIntegrand (h := h) K X
      (output.1, stoppedAttemptFiniteObservable attempt output.2)) =ᵐ[
        (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod P]
      fun output ↦
        (Set.univ ×ˢ survivalEvent run X K).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (LALM.Correction.StochasticRun.UniformOutput.point run output)
              (LALM.Correction.StochasticRun.UniformOutput.multiplier run output) ^ 2))
          output := by
  let p := LALM.StochasticRun.UniformOutput.indexLaw K hK
  have hpSupport : ∀ᵐ k ∂p.toMeasure, k ∈ Finset.Icc 1 (K - 1) := by
    rw [ae_iff_of_countable]
    intro k hkMeasure
    by_contra hk
    have hpZero : p k = 0 := by
      simp only [p, LALM.StochasticRun.UniformOutput.indexLaw,
        PMF.uniformOfFinset_apply, if_neg hk]
    have hsingleton : p.toMeasure {k} = p k :=
      PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)
    exact hkMeasure (hsingleton.trans hpZero)
  have hpSupportLifted :
      ∀ᵐ output ∂p.toMeasure.prod P,
        output.1 ∈ Finset.Icc 1 (K - 1) :=
    (Measure.quasiMeasurePreserving_fst (μ := p.toMeasure) (ν := P)).ae
      hpSupport
  change _ =ᵐ[p.toMeasure.prod P] _
  filter_upwards [hpSupportLifted] with output hindex
  let i := output.1
  let omega := output.2
  let record : stoppedAttemptOutputRecordType Ξ n m K :=
    (i, stoppedAttemptFiniteObservable attempt omega)
  change outputResidualIntegrand (h := h) K X record = _
  have hiBounds : i ∈ Finset.Icc 1 (K - 1) := by
    exact hindex
  have hi := Finset.mem_Icc.mp hiBounds
  have hiSuccLe : i + 1 ≤ K := by omega
  have hiSuccLt : i + 1 < K + 1 := by omega
  have hsuccessRecord :
      record ∈ successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
        omega ∈ survivalEvent run X K := by
    rw [mem_successfulOutputRecord_iff]
    rw [finiteObservable_mem_successRecord_iff_attempt, hsuccess]
    exact and_iff_right hiBounds
  by_cases hsurvival : omega ∈ survivalEvent run X K
  · have hrecord : record ∈
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X :=
      hsuccessRecord.mpr hsurvival
    have hselectedX : run.point (i + 1) omega ∈ X := by
      have hsurvivalPoints := hsurvival
      rw [mem_survivalEvent] at hsurvivalPoints
      exact hsurvivalPoints (i + 1) ⟨by omega, by omega⟩
    have hselectedRegion : run.point (i + 1) omega ∈ h.region :=
      hXregion hselectedX
    have hextension :
        KKT.residualExtension h
            (run.point (i + 1) omega, run.multiplier (i + 1) omega) =
          KKT.residual f c (run.point (i + 1) omega)
            (run.multiplier (i + 1) omega) :=
      KKT.residualExtension_eq h hselectedRegion
    have hpointSelected :
        record.2.2.1 (Fin.ofNat (K + 1) (i + 1)) =
          run.point (i + 1) omega := by
      rw [stoppedAttemptFiniteObservable_point attempt (i + 1) hiSuccLt omega,
        hpoint (i + 1) hiSuccLe omega hsurvival]
    have hmultiplierSelected :
        record.2.2.2.1 (Fin.ofNat (K + 1) (i + 1)) =
          run.multiplier (i + 1) omega := by
      rw [stoppedAttemptFiniteObservable_multiplier attempt (i + 1) hiSuccLt omega,
        hmultiplier (i + 1) hiSuccLe omega hsurvival]
    have hproduct : output ∈ Set.univ ×ˢ survivalEvent run X K :=
      ⟨Set.mem_univ _, hsurvival⟩
    rw [outputResidualIntegrand_def, Set.indicator_of_mem hrecord,
      Set.indicator_of_mem hproduct,
      hpointSelected, hmultiplierSelected,
      LALM.Correction.StochasticRun.UniformOutput.point_apply,
      LALM.Correction.StochasticRun.UniformOutput.multiplier_apply,
      hextension]
  · have hrecord : record ∉
        successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X := by
      intro hrecord
      exact hsurvival (hsuccessRecord.mp hrecord)
    have hproduct : output ∉ Set.univ ×ˢ survivalEvent run X K := by
      intro houtput
      exact hsurvival houtput.2
    rw [outputResidualIntegrand_def, Set.indicator_of_notMem hrecord,
      Set.indicator_of_notMem hproduct]

/-- Corollary 4.2: under the coordinate bridge, the finite stopped residual
numerator is exactly the terminal-survival uniform-output integral. -/
theorem successRestrictedResidualNumerator_eq_uniformSurvivalIntegral
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hsuccess : StoppedAttemptAnalysis.successEvent attempt =
      survivalEvent run X K)
    (hpoint : ∀ k ≤ K, ∀ omega,
      omega ∈ survivalEvent run X K →
        StoppedAttempt.point attempt k omega = run.point k omega)
    (hmultiplier : ∀ k ≤ K, ∀ omega,
      omega ∈ survivalEvent run X K →
        StoppedAttempt.multiplier attempt k omega = run.multiplier k omega)
    (hX : MeasurableSet X) (hXregion : X ⊆ h.region) :
    successRestrictedResidualNumerator attempt hK =
      ∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c
            (LALM.Correction.StochasticRun.UniformOutput.point run output)
            (LALM.Correction.StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂LALM.StochasticRun.UniformOutput.measure K hK P := by
  let observable := stoppedAttemptFiniteObservable attempt
  let muIndex := (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure
  have hobservable : Measurable observable :=
    measurable_stoppedAttemptFiniteObservable attempt
  have hintegrand : Measurable
      (outputResidualIntegrand (h := h) K X) :=
    measurable_outputResidualIntegrand (Ξ := Ξ) (m := m) (h := h) K X hX
  have hreference : NullMeasurableSet
      (Set.univ ×ˢ survivalEvent run X K) (muIndex.prod P) :=
    MeasurableSet.univ.nullMeasurableSet.prod
      (nullMeasurableSet_survivalEvent run X hX K)
  calc
    successRestrictedResidualNumerator attempt hK =
        ∫⁻ output, outputResidualIntegrand (h := h) K X output
          ∂muIndex.prod (P.map observable) := by
      rw [successRestrictedResidualNumerator_def,
        stoppedAttemptOutputMeasure_def]
    _ = ∫⁻ output,
        outputResidualIntegrand (h := h) K X
          (output.1, observable output.2) ∂muIndex.prod P := by
      exact lintegral_prod_map_right (P := P) muIndex observable hobservable
        (outputResidualIntegrand (h := h) K X) hintegrand
    _ = ∫⁻ output,
        (Set.univ ×ˢ survivalEvent run X K).indicator
          (fun output ↦ ENNReal.ofReal
            (KKT.residual f c
              (LALM.Correction.StochasticRun.UniformOutput.point run output)
              (LALM.Correction.StochasticRun.UniformOutput.multiplier run output) ^ 2))
          output ∂muIndex.prod P := by
      exact lintegral_congr_ae
        (finiteOutputResidualIntegrand_eq attempt run hsuccess hpoint hmultiplier
          hXregion)
    _ = ∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c
            (LALM.Correction.StochasticRun.UniformOutput.point run output)
            (LALM.Correction.StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂muIndex.prod P := by
      exact lintegral_indicator₀ hreference _
    _ = ∫⁻ output in Set.univ ×ˢ survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c
            (LALM.Correction.StochasticRun.UniformOutput.point run output)
            (LALM.Correction.StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂LALM.StochasticRun.UniformOutput.measure K hK P := by
      rfl

end StoppedUniformResidualBridge

end LALM.Correction

end

open LALM.Correction.StoppedUniformResidualBridge

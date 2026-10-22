/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedCertificate
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedCertificate

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.FiniteStopped.StoppedAttemptAnalysis

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
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

open LALM.FiniteStopped
open LALM.StochasticRun.UniformOutput

/-- Helper for Theorem 3.7: restricting a product integral with a finite
uniform first coordinate is bounded by the uniform average of its sections. -/
theorem setLIntegral_uniform_le_sum
    (K : ℕ) (hK : 2 ≤ K) (S : Set Ω) (g : ℕ × Ω → ℝ≥0∞) :
    (∫⁻ output in Set.univ ×ˢ S, g output ∂measure K hK P) ≤
      (∑ k ∈ Finset.Icc 1 (K - 1), ∫⁻ omega in S, g (k, omega) ∂P) /
        (Finset.Icc 1 (K - 1)).card := by
  let s := Finset.Icc 1 (K - 1)
  let p := indexLaw K hK
  change (∫⁻ output in Set.univ ×ˢ S, g output ∂p.toMeasure.prod P) ≤ _
  rw [← Measure.prod_restrict]
  calc
    (∫⁻ output, g output ∂
        (p.toMeasure.restrict Set.univ).prod (P.restrict S)) ≤
        ∫⁻ k in Set.univ, ∫⁻ omega in S, g (k, omega) ∂P ∂p.toMeasure :=
      lintegral_prod_le g
    _ = ∑' k, (∫⁻ omega in S, g (k, omega) ∂P) * p.toMeasure {k} := by
      rw [Measure.restrict_univ, lintegral_countable']
    _ = ∑ k ∈ s,
        (∫⁻ omega in S, g (k, omega) ∂P) * (s.card : ℝ≥0∞)⁻¹ := by
      have hp (k : ℕ) :
          p.toMeasure {k} =
            if k ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 := by
        rw [PMF.toMeasure_apply_singleton p k (MeasurableSet.singleton k)]
        change (PMF.uniformOfFinset s _) k = _
        by_cases hk : k ∈ s
        · simp only [PMF.uniformOfFinset_apply, if_pos hk]
        · simp only [PMF.uniformOfFinset_apply, if_neg hk]
      simp_rw [hp]
      rw [tsum_eq_sum (s := s)]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [if_pos hk]
      · intro k hk
        rw [if_neg hk, mul_zero]
    _ = (∑ k ∈ Finset.Icc 1 (K - 1),
        ∫⁻ omega in S, g (k, omega) ∂P) /
          (Finset.Icc 1 (K - 1)).card := by
      rw [ENNReal.div_eq_inv_mul, mul_comm, Finset.sum_mul]

/-- Theorem 3.7: the actual KKT residual numerator obtained from an independent
uniform selector, restricted to successful finite stopped attempts. -/
noncomputable def canonicalUniformSuccessResidualNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) : ℝ≥0∞ :=
  ∫⁻ output in Set.univ ×ˢ attempt.successEvent,
    ENNReal.ofReal
      (KKT.residual f c
        (canonicalPointNat attempt (output.1 + 1) output.2)
        (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2)
      ∂measure K hK P

/-- Helper for Theorem 3.7: on a successful attempt, the canonical pathwise
residual energy is exactly the sum over the uniform output support. -/
theorem canonicalPathwiseResidualEnergy_eq_sum_of_success
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (omega : Ω) (hsuccess : omega ∈ attempt.successEvent) :
    canonicalPathwiseResidualEnergy attempt omega =
      ∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.residualExtension h
          (canonicalPointNat attempt (k + 1) omega,
            canonicalMultiplierNat attempt (k + 1) omega) ^ 2 := by
  have hprefix : canonicalPrefixLength attempt omega = K := by
    unfold canonicalPrefixLength
    rw [(LALM.FiniteStopped.StoppedAttempt.mem_successEvent_iff_firstExitEndpoint_eq_succ
      attempt omega).mp hsuccess]
    omega
  have hinterval : Finset.Ico 1 K = Finset.Icc 1 (K - 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  unfold canonicalPathwiseResidualEnergy
  rw [hinterval]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < K := by
    have hbounds := Finset.mem_Icc.mp hk
    omega
  rw [dif_pos]
  rwa [hprefix]

/-- Helper for Theorem 3.7: the success-restricted real numerator is the
corresponding set integral divided by the uniform support cardinality. -/
theorem canonicalSuccessRestrictedResidualNumerator_eq_setAverage
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) :
    canonicalSuccessRestrictedResidualNumerator attempt =
      ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) /
        (Finset.Icc 1 (K - 1)).card := by
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKreal : 0 < (K : ℝ) - 1 := by
    have hKnat : 1 < K := by omega
    exact sub_pos.mpr (by exact_mod_cast hKnat)
  unfold canonicalSuccessRestrictedResidualNumerator
  rw [integral_indicator
    (LALM.FiniteStopped.StoppedAttempt.measurableSet_successEvent attempt),
    ENNReal.ofReal_div_of_pos hKreal, hcard, ENNReal.natCast_sub,
    Nat.cast_one, ENNReal.ofReal_sub (K : ℝ) (by norm_num),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- Theorem 3.7: integrating the genuine uniformly selected KKT residual on
successful attempts is controlled by the success-restricted canonical path
numerator. -/
theorem canonicalUniformSuccessResidualNumerator_le
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    canonicalUniformSuccessResidualNumerator attempt hK ≤
      canonicalSuccessRestrictedResidualNumerator attempt := by
  let s := Finset.Icc 1 (K - 1)
  let residualExtensionSquare : ℕ → Ω → ℝ := fun k omega ↦
    KKT.residualExtension h
      (canonicalPointNat attempt (k + 1) omega,
        canonicalMultiplierNat attempt (k + 1) omega) ^ 2
  have hsuccessMeasurable : MeasurableSet attempt.successEvent :=
    LALM.FiniteStopped.StoppedAttempt.measurableSet_successEvent attempt
  have hsection (k : ℕ) (hk : k ∈ s) :
      (∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) ^ 2) ∂P) =
        ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal (residualExtensionSquare k omega) ∂P := by
    have hk' : k ∈ Finset.Icc 1 (K - 1) := by
      simpa only [s] using hk
    have hbounds := Finset.mem_Icc.mp hk'
    have hkEndpoint : k + 1 ≤ K := by
      omega
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem₀ hsuccessMeasurable.nullMeasurableSet] with
      omega hsuccess
    have hpointX : canonicalPointNat attempt (k + 1) omega ∈ X := by
      rw [canonicalPointNat_eq_point attempt (k + 1) hkEndpoint omega]
      let kFin : Fin K := ⟨k, by omega⟩
      have hmembership :=
        (LALM.FiniteStopped.StoppedAttempt.mem_successEvent_iff_points_mem
          attempt omega).mp hsuccess kFin
      have hindex :
          (⟨k + 1, Nat.lt_succ_iff.mpr hkEndpoint⟩ : Fin (K + 1)) =
            kFin.succ := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hmembership
    have hpointRegion : canonicalPointNat attempt (k + 1) omega ∈ h.region :=
      attempt.region_condition.thickening_subset
        (Metric.self_subset_cthickening X hpointX)
    have hextension := KKT.residualExtension_eq h
      (z := (canonicalPointNat attempt (k + 1) omega,
        canonicalMultiplierNat attempt (k + 1) omega)) hpointRegion
    dsimp only [residualExtensionSquare]
    rw [hextension]
  have hextensionMeasurable (k : ℕ) :
      Measurable (fun omega ↦
        ENNReal.ofReal (residualExtensionSquare k omega)) := by
    exact (measurable_canonicalResidualSquare attempt (k + 1)).ennreal_ofReal
  have hsumExtension :
      (∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal (residualExtensionSquare k omega) ∂P) =
        ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) := by
    have hintegrable :=
      integrable_canonicalPathwiseResidualEnergy_of_prefixInvariant
        (f' := f) (c' := c) attempt invariant hK
    calc
      (∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal (residualExtensionSquare k omega) ∂P) =
          ∫⁻ omega in attempt.successEvent,
            ∑ k ∈ s, ENNReal.ofReal (residualExtensionSquare k omega) ∂P := by
        exact (lintegral_finsetSum s fun k _hk ↦
          hextensionMeasurable k).symm
      _ = ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal (canonicalPathwiseResidualEnergy attempt omega) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem₀ hsuccessMeasurable.nullMeasurableSet] with
          omega hsuccess
        rw [canonicalPathwiseResidualEnergy_eq_sum_of_success attempt omega hsuccess]
        exact (ENNReal.ofReal_sum_of_nonneg
          (fun k _hk ↦ sq_nonneg
            (KKT.residualExtension h
              (canonicalPointNat attempt (k + 1) omega,
                canonicalMultiplierNat attempt (k + 1) omega)))).symm
      _ = ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hintegrable.integrableOn
          (ae_of_all _ fun omega ↦
            canonicalPathwiseResidualEnergy_nonneg attempt omega)).symm
  have hsumRaw :
      (∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) ^ 2) ∂P) =
        ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) := by
    calc
      (∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) ^ 2) ∂P) =
          ∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
            ENNReal.ofReal (residualExtensionSquare k omega) ∂P := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hsection k hk
      _ = ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) := hsumExtension
  have huniform := setLIntegral_uniform_le_sum (P := P) K hK
    attempt.successEvent
    (fun output ↦ ENNReal.ofReal
      (KKT.residual f c
        (canonicalPointNat attempt (output.1 + 1) output.2)
        (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2))
  unfold canonicalUniformSuccessResidualNumerator
  calc
    (∫⁻ output in Set.univ ×ˢ attempt.successEvent,
        ENNReal.ofReal
          (KKT.residual f c
            (canonicalPointNat attempt (output.1 + 1) output.2)
            (canonicalMultiplierNat attempt (output.1 + 1) output.2) ^ 2)
          ∂measure K hK P) ≤
        (∑ k ∈ s, ∫⁻ omega in attempt.successEvent,
          ENNReal.ofReal
            (KKT.residual f c
              (canonicalPointNat attempt (k + 1) omega)
              (canonicalMultiplierNat attempt (k + 1) omega) ^ 2) ∂P) /
          s.card := by
      simpa only [s] using huniform
    _ = ENNReal.ofReal
          (∫ omega in attempt.successEvent,
            canonicalPathwiseResidualEnergy attempt omega ∂P) /
        (Finset.Icc 1 (K - 1)).card := by
      rw [hsumRaw]
    _ = canonicalSuccessRestrictedResidualNumerator attempt :=
      (canonicalSuccessRestrictedResidualNumerator_eq_setAverage attempt hK).symm

/-- Theorem 3.7: a finite canonical certificate controls the genuine
success-restricted residual under the independent uniform output law. -/
theorem FiniteStoppedCanonicalCertificate.uniformSuccessResidualNumerator_le
    {attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X}
    {hK : 2 ≤ K}
    (certificate : FiniteStoppedCanonicalCertificate attempt hK)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    canonicalUniformSuccessResidualNumerator attempt hK ≤
      P attempt.successEvent *
        (certificate.residualPerSuccessBound : ℝ≥0∞) := by
  exact (canonicalUniformSuccessResidualNumerator_le attempt hK invariant).trans
    certificate.canonicalSuccessRestrictedResidualNumerator_le

end LALM.FiniteStopped.StoppedAttemptAnalysis

end

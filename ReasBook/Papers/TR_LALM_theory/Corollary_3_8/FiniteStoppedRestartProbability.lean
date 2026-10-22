/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestart

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.FiniteStopped.StoppedSafeguardedRestart

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
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

/-- Helper for Corollary 3.8: exceeding `t` attempts is exactly failure of
each of the first `t` finite attempts. -/
theorem attemptCount_tail_eq_failureInter
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (t : ℕ) :
    {omega | (t : ℕ∞) < attemptCount restart omega} =
      ⋂ i ∈ Finset.range t, (successEvent restart i)ᶜ := by
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range,
    Set.mem_compl_iff]
  cases hfirst : firstAccepted restart omega using ENat.recTopCoe with
  | top =>
      have hall := (firstAccepted_eq_top_iff restart omega).mp hfirst
      simp only [attemptCount, hfirst, top_add, ENat.coe_lt_top, true_iff]
      intro i _hi hsuccess
      exact hall i ((completionIndicator_eq_true restart i omega).mpr hsuccess)
  | coe accepted =>
      have hcharacterization :=
        (firstAccepted_eq_coe_iff restart accepted omega).mp hfirst
      simp only [attemptCount, hfirst, ← ENat.coe_one, ← ENat.coe_add,
        ENat.coe_lt_coe]
      constructor
      · intro ht i hit hsuccess
        apply hcharacterization.2 i
        · omega
        · exact (completionIndicator_eq_true restart i omega).mpr hsuccess
      · intro hall
        have hta : t ≤ accepted := by
          by_contra hnot
          have hat : accepted < t := Nat.lt_of_not_ge hnot
          exact hall accepted hat
            ((completionIndicator_eq_true restart accepted omega).mp
              hcharacterization.1)
        omega

/-- Helper for Corollary 3.8: a success lower bound of `1 - confidence`
implies a failure upper bound of `confidence`. -/
lemma failureProbability_le_confidence
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i))
    (i : ℕ) :
    P (successEvent restart i)ᶜ ≤ ENNReal.ofReal confidence := by
  have hsuccessNull : NullMeasurableSet (successEvent restart i) P :=
    (measurableSet_successEvent restart i).nullMeasurableSet
  have hsuccessLower := successProbability_lower i
  have hconfidence : ENNReal.ofReal confidence ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal confidence_lt_one.le
  calc
    P (successEvent restart i)ᶜ = 1 - P (successEvent restart i) :=
      prob_compl_eq_one_sub₀ hsuccessNull
    _ ≤ 1 - ENNReal.ofReal (1 - confidence) :=
      tsub_le_tsub_left hsuccessLower 1
    _ = ENNReal.ofReal confidence := by
      rw [ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one,
        ENNReal.sub_sub_cancel ENNReal.one_ne_top hconfidence]

/-- Corollary 3.8: mutually independent finite attempts give the geometric
tail bound for the one-based attempt count. -/
theorem attemptCount_tail_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i))
    (t : ℕ) :
    P {omega | (t : ℕ∞) < attemptCount restart omega} ≤
      ENNReal.ofReal confidence ^ t := by
  have hfailure (i : ℕ) :
      P (successEvent restart i)ᶜ ≤ ENNReal.ofReal confidence :=
    failureProbability_le_confidence restart confidence_pos confidence_lt_one
      successProbability_lower i
  have hX : MeasurableSet X :=
    (restart.attempt 0).measurableSet_localization
  have hfactor := restart.independent_attempt.measure_inter_preimage_eq_mul
    (Finset.range t)
    (sets := fun _ ↦
      failureRecordWithSelector (Ξ := Ξ) (n := n) (m := m) K X)
    (fun _ _ ↦ measurableSet_failureRecordWithSelector K X hX)
  rw [attemptCount_tail_eq_failureInter restart t]
  calc
    P (⋂ i ∈ Finset.range t, (successEvent restart i)ᶜ) =
        ∏ i ∈ Finset.range t, P (successEvent restart i)ᶜ := by
      simpa only [failureRecordWithSelector_preimage] using hfactor
    _ ≤ ∏ _i ∈ Finset.range t, ENNReal.ofReal confidence :=
      Finset.prod_le_prod' fun i _hi ↦ hfailure i
    _ = ENNReal.ofReal confidence ^ t := by simp

/-- Helper for Corollary 3.8: an extended natural is the sum of indicators of
its strict natural lower bounds. -/
private lemma enatToENNReal_eq_tsum_lt (count : ℕ∞) :
    (count : ℝ≥0∞) =
      ∑' t : ℕ, if (t : ℕ∞) < count then 1 else 0 := by
  cases count using ENat.recTopCoe with
  | top =>
      simp only [ENat.toENNReal_top, lt_top_iff_ne_top]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe count =>
      simp only [ENat.toENNReal_coe, ENat.coe_lt_coe]
      calc
        (count : ℝ≥0∞) = ∑ t ∈ Finset.range count, (1 : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_one, Finset.card_range]
        _ = ∑' t : ℕ, if t < count then 1 else 0 := by
          rw [tsum_eq_sum (s := Finset.range count)]
          · apply Finset.sum_congr rfl
            intro t ht
            rw [if_pos (Finset.mem_range.mp ht)]
          · intro t ht
            rw [if_neg]
            simpa only [Finset.mem_range] using ht

omit [IsProbabilityMeasure P] in
/-- Helper for Corollary 3.8: the lower integral of an extended-natural
random variable is bounded by the sum of its outer tail probabilities. -/
private lemma lintegralENat_le_tsum_tail (count : Ω → ℕ∞) :
    ∫⁻ omega, (count omega : ℝ≥0∞) ∂P ≤
      ∑' t : ℕ, P {omega | (t : ℕ∞) < count omega} := by
  have hpoint (omega : Ω) : (count omega : ℝ≥0∞) ≤
      ∑' t : ℕ,
        (toMeasurable P {omega | (t : ℕ∞) < count omega}).indicator
          (fun _ ↦ 1) omega := by
    rw [enatToENNReal_eq_tsum_lt]
    apply ENNReal.tsum_le_tsum
    intro t
    by_cases ht : (t : ℕ∞) < count omega
    · have hmem : omega ∈
          toMeasurable P {omega | (t : ℕ∞) < count omega} :=
        subset_toMeasurable P _ ht
      simp only [ht, if_true, Set.indicator_of_mem hmem]
      exact le_rfl
    · simp only [ht, if_false, zero_le]
  calc
    (∫⁻ omega, (count omega : ℝ≥0∞) ∂P) ≤
        ∫⁻ omega, ∑' t : ℕ,
          (toMeasurable P {omega | (t : ℕ∞) < count omega}).indicator
            (fun _ ↦ 1) omega ∂P := lintegral_mono hpoint
    _ = ∑' t : ℕ, ∫⁻ omega,
        (toMeasurable P {omega | (t : ℕ∞) < count omega}).indicator
          (fun _ ↦ 1) omega ∂P := by
      rw [lintegral_tsum]
      intro t
      exact (measurable_const.indicator
        (measurableSet_toMeasurable P _)).aemeasurable
    _ = ∑' t : ℕ, P {omega | (t : ℕ∞) < count omega} := by
      apply tsum_congr
      intro t
      calc
        (∫⁻ omega,
            (toMeasurable P {omega | (t : ℕ∞) < count omega}).indicator
              (fun _ ↦ 1) omega ∂P) =
            P (toMeasurable P {omega | (t : ℕ∞) < count omega}) :=
          lintegral_indicator_one (measurableSet_toMeasurable P _)
        _ = P {omega | (t : ℕ∞) < count omega} := measure_toMeasurable _

/-- Corollary 3.8: the finite stopped restart terminates almost surely under
the uniform positive success bound. -/
theorem terminatesAE
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∀ᵐ omega ∂P, firstAccepted restart omega ≠ ⊤ := by
  rw [ae_iff]
  simp only [not_ne_iff]
  refine ENNReal.eq_zero_of_le_mul_pow (ε := 1)
    (ENNReal.ofReal_lt_one.mpr confidence_lt_one) ?_
  intro t
  calc
    P {omega | firstAccepted restart omega = ⊤} ≤
        P {omega | (t : ℕ∞) < attemptCount restart omega} := by
      apply measure_mono
      intro omega homega
      have hcount : attemptCount restart omega = ⊤ :=
        (attemptCount_eq_top_iff restart omega).2 homega
      simp only [Set.mem_setOf_eq, hcount, ENat.coe_lt_top]
    _ ≤ ENNReal.ofReal confidence ^ t :=
      attemptCount_tail_le restart confidence_pos confidence_lt_one
        successProbability_lower t
    _ = (1 : ℝ≥0) * ENNReal.ofReal confidence ^ t := by simp

/-- Corollary 3.8: the expected number of finite stopped attempts is at most
the reciprocal success probability. -/
theorem expectedAttemptCount_le
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (successProbability_lower : ∀ i,
      ENNReal.ofReal (1 - confidence) ≤ P (successEvent restart i)) :
    ∫⁻ omega, (attemptCount restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (1 / (1 - confidence)) := by
  calc
    (∫⁻ omega, (attemptCount restart omega : ℝ≥0∞) ∂P) ≤
        ∑' t : ℕ, P {omega | (t : ℕ∞) < attemptCount restart omega} :=
      lintegralENat_le_tsum_tail restart.attemptCount
    _ ≤ ∑' t : ℕ, ENNReal.ofReal confidence ^ t :=
      ENNReal.tsum_le_tsum fun t ↦
        attemptCount_tail_le restart confidence_pos confidence_lt_one
          successProbability_lower t
    _ = (1 - ENNReal.ofReal confidence)⁻¹ := ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (1 / (1 - confidence)) := by
      rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr confidence_lt_one),
        ENNReal.ofReal_one, ENNReal.ofReal_sub 1 confidence_pos.le,
        ENNReal.ofReal_one, one_div]

end LALM.FiniteStopped.StoppedSafeguardedRestart

end

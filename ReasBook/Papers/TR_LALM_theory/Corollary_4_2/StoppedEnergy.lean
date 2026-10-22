/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.FixedPathEnergy
public import TR_LALM_theory.Corollary_4_2.StoppedProcess

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction.StochasticRun.Localization

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
variable {params : Parameters h x₀ multiplier₀} {Q B b : ℕ+}
variable {confidence : ℝ}

/-- Helper for Corollary 4.2: each sample path's survival-weighted corrected
base-step energy is controlled by its survival-weighted estimator-error energy. -/
private lemma activeBaseStepEnergy_le
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) (omega : Ω) :
    (∑ k ∈ Finset.range K,
        (survivalEvent run X k).indicator
          (fun omega' ↦ ‖run.baseStep k omega'‖ ^ 2) omega) ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega := by
  let activePrefixLength : Ω → ℕ := fun omega' ↦
    min K ((exitTime run X omega').untopD K)
  have hKOne : 1 ≤ K := by omega
  -- Hitting-time minimality characterizes exactly the indices in the active prefix.
  have hprefixSpec (omega' : Ω) :
      1 ≤ activePrefixLength omega' ∧
        activePrefixLength omega' ≤ K ∧
        ∀ k < K,
          (k < activePrefixLength omega' ↔
            omega' ∈ survivalEvent run X k) := by
    have hexitLower : (1 : ℕ∞) ≤ exitTime run X omega' := by
      rw [exitTime_def]
      exact MeasureTheory.le_hittingAfter
        (u := run.point) (s := Xᶜ) (n := 1) omega'
    have hdefaultLower : 1 ≤ (exitTime run X omega').untopD K := by
      rw [WithTop.le_untopD_iff (fun _ ↦ hKOne)]
      exact hexitLower
    refine ⟨(Nat.le_min).2 ⟨hKOne, hdefaultLower⟩, min_le_left _ _, ?_⟩
    intro k hk
    have hdefault :
        k < (exitTime run X omega').untopD K ↔
          (k : ℕ∞) < exitTime run X omega' := by
      apply WithTop.lt_untopD_iff
      intro hexitTop
      simpa only [hexitTop, WithTop.untopD_top] using hk
    have hsurvival :
        omega' ∈ survivalEvent run X k ↔
          (k : ℕ∞) < exitTime run X omega' :=
      mem_survivalEvent_iff_lt_exitTime run X k omega'
    dsimp only [activePrefixLength]
    rw [lt_min_iff, hdefault, hsurvival]
    simp only [hk, true_and]
  -- One parameterized normalizer handles both survival-indicator sums.
  have hprefixSum (omega' : Ω) (g : ℕ → Ω → ℝ) :
      (∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator (g k) omega') =
        ∑ k ∈ Finset.range (activePrefixLength omega'), g k omega' := by
    have hindicator :
        (∑ k ∈ Finset.range K,
            (survivalEvent run X k).indicator (g k) omega') =
          ∑ k ∈ Finset.range K,
            if k < activePrefixLength omega' then g k omega' else 0 := by
      apply Finset.sum_congr rfl
      intro k hkRange
      have hk : k < K := Finset.mem_range.mp hkRange
      have hactive := (hprefixSpec omega').2.2 k hk
      by_cases hkPrefix : k < activePrefixLength omega'
      · rw [Set.indicator_of_mem (hactive.mp hkPrefix), if_pos hkPrefix]
      · rw [Set.indicator_of_notMem
          (fun hmem ↦ hkPrefix (hactive.mpr hmem)), if_neg hkPrefix]
    rw [hindicator]
    have hsubset :
        Finset.range (activePrefixLength omega') ⊆ Finset.range K :=
      Finset.range_mono (hprefixSpec omega').2.1
    have htrimmed :
        (∑ k ∈ Finset.range (activePrefixLength omega'),
            if k < activePrefixLength omega' then g k omega' else 0) =
          ∑ k ∈ Finset.range K,
            if k < activePrefixLength omega' then g k omega' else 0 :=
      Finset.sum_subset hsubset
        (fun k _hkRange hkPrefix ↦ by
          have hkNotLt : ¬k < activePrefixLength omega' := by
            simpa only [Finset.mem_range] using hkPrefix
          simp only [if_neg hkNotLt])
    calc
      (∑ k ∈ Finset.range K,
          if k < activePrefixLength omega' then g k omega' else 0) =
          ∑ k ∈ Finset.range (activePrefixLength omega'),
            if k < activePrefixLength omega' then g k omega' else 0 :=
        htrimmed.symm
      _ = ∑ k ∈ Finset.range (activePrefixLength omega'), g k omega' := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [if_pos (Finset.mem_range.mp hk)]
  rw [hprefixSum omega (fun k omega' ↦ ‖run.baseStep k omega'‖ ^ 2),
    hprefixSum omega (fun k omega' ↦ ‖run.gradientError k omega'‖ ^ 2)]
  -- Survival through the last active index supplies the fixed-path invariant.
  have hprefix := hprefixSpec omega
  have hlastLt : activePrefixLength omega - 1 < activePrefixLength omega := by
    omega
  have hlastLtK : activePrefixLength omega - 1 < K := by omega
  have hsurvival :
      omega ∈ survivalEvent run X (activePrefixLength omega - 1) :=
    (hprefix.2.2 _ hlastLtK).mp hlastLt
  have hrawBounds := preExitPrefixBounds run X initial_mem h_region omega
    (activePrefixLength omega - 1) hsurvival
  have hendpoint : activePrefixLength omega - 1 + 1 = activePrefixLength omega :=
    Nat.sub_add_cancel hprefix.1
  have hbounds :
      run.BoundedAdmissiblePath (activePrefixLength omega) omega := by
    constructor
    · intro j hj
      have hjRaw : j < activePrefixLength omega - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hrawBounds.1 j hjRaw
    · intro j hj
      have hjRaw : j < activePrefixLength omega - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hrawBounds.2.1 j hjRaw
    · intro j hj
      have hjRaw : j ≤ activePrefixLength omega - 1 + 1 := by
        simpa only [hendpoint] using hj
      exact hrawBounds.2.2 j hjRaw
  exact hbounds.sumBaseStepSq_le hprefix.1

/-- Helper for Corollary 4.2: stopped corrected base-step energy is bounded by
the initial allowance plus the stopped corrected estimator-error energy. -/
theorem stoppedBaseStepEnergy_le
    (K : ℕ) (hK : 2 ≤ K)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (h_region : RegionCondition h oracle params confidence X) :
    stoppedBaseStepEnergy run X K ≤
      initialStepBound h params +
        errorStepConstant h params * stoppedGradientErrorEnergy run X K := by
  -- Each survival indicator is integrable by the stopped-process owner API.
  have hstepTerm (k : ℕ) : Integrable
      ((survivalEvent run X k).indicator
        (fun omega ↦ ‖run.baseStep k omega‖ ^ 2)) P := by
    have hrestricted :=
      integrableOn_baseStepSquare_preExit run X hX initial_mem h_region k
    exact hrestricted.integrable_indicator₀
      (nullMeasurableSet_survivalEvent run X hX k)
  have herrorTerm (k : ℕ) : Integrable
      ((survivalEvent run X k).indicator
        (fun omega ↦ ‖run.gradientError k omega‖ ^ 2)) P := by
    have hrestricted :=
      integrableOn_gradientErrorSquare_preExit run X hX initial_mem h_region k
    exact hrestricted.integrable_indicator₀
      (nullMeasurableSet_survivalEvent run X hX k)
  have hstepIntegrable : Integrable
      (fun omega ↦ ∑ k ∈ Finset.range K,
        (survivalEvent run X k).indicator
          (fun omega' ↦ ‖run.baseStep k omega'‖ ^ 2) omega) P :=
    integrable_finsetSum (Finset.range K) fun k _hk ↦ hstepTerm k
  have herrorIntegrable : Integrable
      (fun omega ↦ ∑ k ∈ Finset.range K,
        (survivalEvent run X k).indicator
          (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega) P :=
    integrable_finsetSum (Finset.range K) fun k _hk ↦ herrorTerm k
  -- Exchange each finite sum with its integral and recover the stopped energies.
  have hstepIntegral :
      (∫ omega, ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.baseStep k omega'‖ ^ 2) omega ∂P) =
        stoppedBaseStepEnergy run X K := by
    rw [stoppedBaseStepEnergy_def,
      integral_finsetSum (Finset.range K) (fun k _hk ↦ hstepTerm k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_indicator₀ (nullMeasurableSet_survivalEvent run X hX k)]
  have herrorIntegral :
      (∫ omega, ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega ∂P) =
        stoppedGradientErrorEnergy run X K := by
    rw [stoppedGradientErrorEnergy_def,
      integral_finsetSum (Finset.range K) (fun k _hk ↦ herrorTerm k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_indicator₀ (nullMeasurableSet_survivalEvent run X hX k)]
  have hrhsIntegrable : Integrable
      (fun omega ↦ initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega) P :=
    (integrable_const _).add
      (herrorIntegrable.const_mul (errorStepConstant h params))
  -- Integrate the pathwise telescope and identify both stopped finite sums.
  calc
    stoppedBaseStepEnergy run X K =
        ∫ omega, ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.baseStep k omega'‖ ^ 2) omega ∂P :=
      hstepIntegral.symm
    _ ≤ ∫ omega, (initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range K,
          (survivalEvent run X k).indicator
            (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega) ∂P :=
      integral_mono hstepIntegrable hrhsIntegrable
        (activeBaseStepEnergy_le K hK X initial_mem run h_region)
    _ = initialStepBound h params +
        errorStepConstant h params * stoppedGradientErrorEnergy run X K := by
      rw [integral_add (integrable_const _)
          (herrorIntegrable.const_mul (errorStepConstant h params)),
        integral_const_mul, integral_const, Measure.real, measure_univ,
        ENNReal.toReal_one, one_smul, herrorIntegral]

end LALM.Correction.StochasticRun.Localization

end

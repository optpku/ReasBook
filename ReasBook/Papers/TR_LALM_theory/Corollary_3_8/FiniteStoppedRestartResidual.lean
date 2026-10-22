/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidualLaw
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartResidualLaw

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.FiniteStopped

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

open StoppedAttemptAnalysis
open StoppedSafeguardedRestart

/-- Corollary 3.8: the event that every finite stopped attempt before `i`
fails. -/
def priorFiniteStoppedFailureEvent
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range i, (successEvent restart j)ᶜ

/-- Corollary 3.8: the indicator of prior finite-attempt failure. -/
noncomputable def priorFiniteStoppedFailureWeight
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) : ℝ≥0∞ :=
  (priorFiniteStoppedFailureEvent restart i).indicator (fun _ ↦ 1) omega

/-- Corollary 3.8: the expected squared residual of the pair returned by a
finite stopped restart. -/
noncomputable def finiteStoppedResidualMeanSquare
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) : ℝ≥0∞ :=
  KKT.Stochastic.residualMeanSquare P f c
    (StoppedSafeguardedRestart.returnedPoint restart)
    (StoppedSafeguardedRestart.returnedMultiplier restart)

/-- Helper for Corollary 3.8: the returned residual is the selected residual
at the defaulted first-accepted attempt. -/
theorem finiteStoppedReturnedResidual_eq_selected
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) :
    ENNReal.ofReal
        (KKT.residual f c (StoppedSafeguardedRestart.returnedPoint restart omega)
          (StoppedSafeguardedRestart.returnedMultiplier restart omega) ^ 2) =
      selectedFiniteStoppedResidual restart
        ((StoppedSafeguardedRestart.firstAccepted restart omega).untopD 0) omega := by
  rw [StoppedSafeguardedRestart.returnedPoint_apply,
    StoppedSafeguardedRestart.returnedMultiplier_apply]
  rfl

/-- Helper for Corollary 3.8: default unwrapping agrees with ordinary unwrapping
on a finite extended natural. -/
lemma finiteStoppedUntopD_eq_untop (a : ℕ∞) (d : ℕ) (ha : a ≠ ⊤) :
    a.untopD d = a.untop ha := by
  cases a using ENat.recTopCoe with
  | top => exact False.elim (ha rfl)
  | coe k => rfl

/-- Helper for Corollary 3.8: a finite first-accepted index lies in its success
event. -/
theorem finiteStoppedSelected_mem_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (omega : Ω) (htermination : firstAccepted restart omega ≠ ⊤) :
    omega ∈ successEvent restart ((firstAccepted restart omega).untopD 0) := by
  have hindex : (firstAccepted restart omega).untopD 0 =
      (firstAccepted restart omega).untop htermination :=
    finiteStoppedUntopD_eq_untop _ 0 htermination
  rw [hindex]
  have hcompletion := firstAccepted_completion restart omega htermination
  rw [completionIndicator_eq_true] at hcompletion
  exact hcompletion

/-- Corollary 3.8: the first-accepted fiber is prior failure intersected with
the current finite success event. -/
theorem finiteStoppedFirstAcceptedFiber_eq
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) :
    {omega | firstAccepted restart omega = (i : ℕ∞)} =
      priorFiniteStoppedFailureEvent restart i ∩ successEvent restart i := by
  ext omega
  rw [Set.mem_setOf_eq, firstAccepted_eq_coe_iff]
  simp only [priorFiniteStoppedFailureEvent, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff, Finset.mem_range]
  constructor
  · rintro ⟨hsuccess, hprior⟩
    constructor
    · intro j hj hmem
      apply hprior j hj
      exact (completionIndicator_eq_true restart j omega).mpr hmem
    · exact (completionIndicator_eq_true restart i omega).mp hsuccess
  · rintro ⟨hprior, hsuccess⟩
    constructor
    · exact (completionIndicator_eq_true restart i omega).mpr hsuccess
    · intro j hj hcompletion
      exact hprior j hj ((completionIndicator_eq_true restart j omega).mp hcompletion)

/-- Corollary 3.8: prior finite-attempt failures are measurable. -/
theorem measurableSet_priorFiniteStoppedFailureEvent
    (_hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet (priorFiniteStoppedFailureEvent restart i) := by
  unfold priorFiniteStoppedFailureEvent
  apply (Finset.range i).measurableSet_biInter
  intro j hj
  exact (measurableSet_successEvent restart j).compl

/-- Corollary 3.8: every finite first-accepted fiber is measurable. -/
theorem measurableSet_finiteStoppedFirstAcceptedFiber
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) : MeasurableSet {omega | firstAccepted restart omega = (i : ℕ∞)} := by
  rw [finiteStoppedFirstAcceptedFiber_eq restart i]
  exact (measurableSet_priorFiniteStoppedFailureEvent hX restart i).inter
    (measurableSet_successEvent restart i)

/-- Helper for Corollary 3.8: multiplying prior failure by current success
gives the indicator of the corresponding first-accepted fiber. -/
theorem priorFiniteStoppedFailureWeight_mul_success
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    priorFiniteStoppedFailureWeight restart i omega *
        (finiteStoppedSuccessResidualObservable restart i omega).1 =
      {omega | firstAccepted restart omega = (i : ℕ∞)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) omega := by
  change priorFiniteStoppedFailureWeight restart i omega *
      (successEvent restart i).indicator (fun _ ↦ (1 : ℝ≥0∞)) omega = _
  by_cases hprior : omega ∈ priorFiniteStoppedFailureEvent restart i
  · by_cases hsuccess : omega ∈ successEvent restart i
    · have hfiber : omega ∈ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
        rw [finiteStoppedFirstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFiniteStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
    · have hnotFiber : omega ∉ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
        rw [finiteStoppedFirstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFiniteStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : omega ∉ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
      rw [finiteStoppedFirstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFiniteStoppedFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 3.8: on a first-accepted fiber, the returned residual
is the selected residual of that fixed finite attempt. -/
theorem finiteStoppedReturnedResidual_eq_selected_on_fiber
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω)
    (hfirst : firstAccepted restart omega = (i : ℕ∞)) :
    ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart omega)
          (returnedMultiplier restart omega) ^ 2) =
      selectedFiniteStoppedResidual restart i omega := by
  have hindex : (firstAccepted restart omega).untopD 0 = i := by
    rw [hfirst]
    rfl
  calc
    ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart omega)
          (returnedMultiplier restart omega) ^ 2) =
        selectedFiniteStoppedResidual restart
          ((firstAccepted restart omega).untopD 0) omega :=
      finiteStoppedReturnedResidual_eq_selected restart omega
    _ = selectedFiniteStoppedResidual restart i omega := by rw [hindex]

/-- Helper for Corollary 3.8: multiplying prior failure by the current
restricted residual gives the returned residual restricted to that fiber. -/
theorem priorFiniteStoppedFailureWeight_mul_residual
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    priorFiniteStoppedFailureWeight restart i omega *
        (finiteStoppedSuccessResidualObservable restart i omega).2 =
      {omega | firstAccepted restart omega = (i : ℕ∞)}.indicator
        (fun omega ↦ ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart omega)
            (returnedMultiplier restart omega) ^ 2)) omega := by
  change priorFiniteStoppedFailureWeight restart i omega *
      (successEvent restart i).indicator
        (selectedFiniteStoppedResidual restart i) omega = _
  by_cases hprior : omega ∈ priorFiniteStoppedFailureEvent restart i
  · by_cases hsuccess : omega ∈ successEvent restart i
    · have hfiber : omega ∈ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
        rw [finiteStoppedFirstAcceptedFiber_eq restart i]
        exact ⟨hprior, hsuccess⟩
      unfold priorFiniteStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_mem hsuccess,
        Set.indicator_of_mem hfiber, one_mul]
      exact (finiteStoppedReturnedResidual_eq_selected_on_fiber
        restart i omega hfiber).symm
    · have hnotFiber : omega ∉ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
        rw [finiteStoppedFirstAcceptedFiber_eq restart i]
        exact fun hfiber ↦ hsuccess hfiber.2
      unfold priorFiniteStoppedFailureWeight
      rw [Set.indicator_of_mem hprior, Set.indicator_of_notMem hsuccess,
        Set.indicator_of_notMem hnotFiber, mul_zero]
  · have hnotFiber : omega ∉ {omega | firstAccepted restart omega = (i : ℕ∞)} := by
      rw [finiteStoppedFirstAcceptedFiber_eq restart i]
      exact fun hfiber ↦ hprior hfiber.1
    unfold priorFiniteStoppedFailureWeight
    rw [Set.indicator_of_notMem hprior, Set.indicator_of_notMem hnotFiber,
      zero_mul]

/-- Helper for Corollary 3.8: the finite tuple all-zero weight summarizes the
strict prefix of independent success/residual observables. -/
noncomputable def finiteAllFirstCoordinatesZeroWeight
    {ι : Type*} (z : ι → ℝ≥0∞ × ℝ≥0∞) : ℝ≥0∞ :=
  {z | ∀ j, (z j).1 = 0}.indicator (fun _ ↦ 1) z

/-- Helper for Corollary 3.8: the finite all-zero summary is measurable. -/
theorem measurable_finiteAllFirstCoordinatesZeroWeight
    {ι : Type*} [Finite ι] :
    Measurable (finiteAllFirstCoordinatesZeroWeight (ι := ι)) := by
  have hcoordinate (j : ι) : Measurable
      (fun z : ι → ℝ≥0∞ × ℝ≥0∞ ↦ (z j).1) :=
    measurable_fst.comp (measurable_pi_apply j)
  unfold finiteAllFirstCoordinatesZeroWeight
  apply measurable_const.indicator
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun j ↦
    (measurableSet_singleton (0 : ℝ≥0∞)).preimage (hcoordinate j)

/-- Helper for Corollary 3.8: the finite all-zero summary agrees pointwise with
the prior-failure indicator. -/
theorem finiteAllFirstCoordinatesZeroWeight_eq_prior
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (i : ℕ) (omega : Ω) :
    finiteAllFirstCoordinatesZeroWeight
        (fun j : Finset.range i ↦
          finiteStoppedSuccessResidualObservable restart j omega) =
      priorFiniteStoppedFailureWeight restart i omega := by
  classical
  by_cases hprior : omega ∈ priorFiniteStoppedFailureEvent restart i
  · have hfail : ∀ j ∈ Finset.range i, omega ∉ successEvent restart j := by
      simpa only [priorFiniteStoppedFailureEvent, Set.mem_iInter,
        Set.mem_compl_iff] using hprior
    have hsummary :
        (fun j : Finset.range i ↦
          finiteStoppedSuccessResidualObservable restart j omega) ∈
          {z | ∀ j, (z j).1 = 0} := by
      intro j
      unfold finiteStoppedSuccessResidualObservable
      change (successEvent restart j).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) omega = 0
      rw [Set.indicator_of_notMem (hfail j j.property)]
    unfold finiteAllFirstCoordinatesZeroWeight priorFiniteStoppedFailureWeight
    rw [Set.indicator_of_mem hsummary, Set.indicator_of_mem hprior]
  · have hsummary :
        (fun j : Finset.range i ↦
          finiteStoppedSuccessResidualObservable restart j omega) ∉
          {z | ∀ j, (z j).1 = 0} := by
      intro hall
      apply hprior
      simp only [priorFiniteStoppedFailureEvent, Set.mem_iInter,
        Set.mem_compl_iff]
      intro j hj hsuccess
      have hzero := hall ⟨j, hj⟩
      unfold finiteStoppedSuccessResidualObservable at hzero
      change (successEvent restart j).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) omega = 0 at hzero
      rw [Set.indicator_of_mem hsuccess] at hzero
      exact one_ne_zero hzero
    unfold finiteAllFirstCoordinatesZeroWeight priorFiniteStoppedFailureWeight
    rw [Set.indicator_of_notMem hsummary, Set.indicator_of_notMem hprior]

/-- Helper for Corollary 3.8: prior failures are independent of the current
success/residual observable. -/
theorem priorFiniteStoppedFailureWeight_indep
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (hsummaryMeas : ∀ i,
      AEMeasurable (finiteStoppedSuccessResidualObservable restart i) P)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ finiteStoppedSuccessResidualObservable restart i) P)
    (i : ℕ) : ProbabilityTheory.IndepFun
      (priorFiniteStoppedFailureWeight restart i)
      (finiteStoppedSuccessResidualObservable restart i) P := by
  classical
  have hdisjoint : Disjoint (Finset.range i) {i} := by simp
  have htuple := hsummaryIndep.indepFun_finset₀
    (Finset.range i) {i} hdisjoint hsummaryMeas
  have hprojected := htuple.comp
    measurable_finiteAllFirstCoordinatesZeroWeight
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩)
  refine hprojected.congr ?_ ?_
  · exact Filter.Eventually.of_forall fun omega ↦
      finiteAllFirstCoordinatesZeroWeight_eq_prior restart i omega
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Corollary 3.8: a fixed finite-attempt success-restricted integral bound
transfers to its first-accepted fiber. -/
theorem finiteStoppedFirstAcceptedFiberResidual_le
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (bound : ℝ≥0∞)
    (hsummaryMeas : ∀ i,
      AEMeasurable (finiteStoppedSuccessResidualObservable restart i) P)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ finiteStoppedSuccessResidualObservable restart i) P)
    (hfixed : ∀ i,
      (∫⁻ omega in successEvent restart i,
        selectedFiniteStoppedResidual restart i omega ∂P) ≤
        P (successEvent restart i) * bound)
    (i : ℕ) :
    (∫⁻ omega in {omega | firstAccepted restart omega = (i : ℕ∞)},
      ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart omega)
          (returnedMultiplier restart omega) ^ 2) ∂P) ≤
      P {omega | firstAccepted restart omega = (i : ℕ∞)} * bound := by
  have hpriorNull : MeasurableSet (priorFiniteStoppedFailureEvent restart i) :=
    measurableSet_priorFiniteStoppedFailureEvent hX restart i
  have hfiberNull : MeasurableSet
      {omega | firstAccepted restart omega = (i : ℕ∞)} :=
    measurableSet_finiteStoppedFirstAcceptedFiber hX restart i
  have hsuccessNull : MeasurableSet (successEvent restart i) :=
    measurableSet_successEvent restart i
  have hpriorMeas : AEMeasurable
      (priorFiniteStoppedFailureWeight restart i) P := by
    unfold priorFiniteStoppedFailureWeight
    exact aemeasurable_const.indicator₀ hpriorNull.nullMeasurableSet
  have hcurrentMeas := hsummaryMeas i
  have hindependent := priorFiniteStoppedFailureWeight_indep restart
    hsummaryMeas hsummaryIndep i
  have hfactorResidual :
      (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega *
          (finiteStoppedSuccessResidualObservable restart i omega).2 ∂P) =
        (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
          ∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).2 ∂P :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.snd
        (hindependent.comp measurable_id measurable_snd)
  have hfactorSuccess :
      (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega *
          (finiteStoppedSuccessResidualObservable restart i omega).1 ∂P) =
        (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
          ∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).1 ∂P :=
    ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
      hpriorMeas hcurrentMeas.fst
        (hindependent.comp measurable_id measurable_fst)
  have hcurrentResidualIntegral :
      (∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).2 ∂P) =
        ∫⁻ omega in successEvent restart i,
          selectedFiniteStoppedResidual restart i omega ∂P := by
    unfold finiteStoppedSuccessResidualObservable
    exact lintegral_indicator₀ hsuccessNull.nullMeasurableSet _
  have hcurrentSuccessIntegral :
      (∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).1 ∂P) =
        P (successEvent restart i) := by
    unfold finiteStoppedSuccessResidualObservable
    exact lintegral_indicator_one₀ hsuccessNull.nullMeasurableSet
  have hmeasureFiber :
      P {omega | firstAccepted restart omega = (i : ℕ∞)} =
        (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
          P (successEvent restart i) := by
    calc
      P {omega | firstAccepted restart omega = (i : ℕ∞)} =
          ∫⁻ omega, {omega | firstAccepted restart omega = (i : ℕ∞)}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) omega ∂P :=
        (lintegral_indicator_one₀ hfiberNull.nullMeasurableSet).symm
      _ = ∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega *
          (finiteStoppedSuccessResidualObservable restart i omega).1 ∂P := by
        apply lintegral_congr
        intro omega
        exact (priorFiniteStoppedFailureWeight_mul_success restart i omega).symm
      _ = (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
          ∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).1 ∂P :=
        hfactorSuccess
      _ = (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
          P (successEvent restart i) := by rw [hcurrentSuccessIntegral]
  calc
    (∫⁻ omega in {omega | firstAccepted restart omega = (i : ℕ∞)},
      ENNReal.ofReal
        (KKT.residual f c (returnedPoint restart omega)
          (returnedMultiplier restart omega) ^ 2) ∂P) =
        ∫⁻ omega, {omega | firstAccepted restart omega = (i : ℕ∞)}.indicator
          (fun omega ↦ ENNReal.ofReal
            (KKT.residual f c (returnedPoint restart omega)
              (returnedMultiplier restart omega) ^ 2)) omega ∂P :=
      (lintegral_indicator₀ hfiberNull.nullMeasurableSet _).symm
    _ = ∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega *
        (finiteStoppedSuccessResidualObservable restart i omega).2 ∂P := by
      apply lintegral_congr
      intro omega
      exact (priorFiniteStoppedFailureWeight_mul_residual restart i omega).symm
    _ = (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
        ∫⁻ omega, (finiteStoppedSuccessResidualObservable restart i omega).2 ∂P :=
      hfactorResidual
    _ = (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
        (∫⁻ omega in successEvent restart i,
          selectedFiniteStoppedResidual restart i omega ∂P) := by
      rw [hcurrentResidualIntegral]
    _ ≤ (∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
        (P (successEvent restart i) * bound) :=
      mul_le_mul_right (hfixed i) _
    _ = ((∫⁻ omega, priorFiniteStoppedFailureWeight restart i omega ∂P) *
        P (successEvent restart i)) * bound := (mul_assoc _ _ _).symm
    _ = P {omega | firstAccepted restart omega = (i : ℕ∞)} * bound := by
      rw [← hmeasureFiber]

/-- Helper for Corollary 3.8: almost-sure termination makes the union of all
finite first-accepted fibers conull. -/
theorem finiteStoppedFirstAcceptedFiberUnion_ae
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂P, firstAccepted restart omega ≠ ⊤) :
    ∀ᵐ omega ∂P,
      omega ∈ ⋃ i : ℕ, {omega | firstAccepted restart omega = (i : ℕ∞)} := by
  filter_upwards [htermination] with omega hfinite
  cases hvalue : firstAccepted restart omega using ENat.recTopCoe with
  | top => exact False.elim (hfinite hvalue)
  | coe i => exact Set.mem_iUnion.mpr ⟨i, hvalue⟩

omit [IsProbabilityMeasure P] in
/-- Helper for Corollary 3.8: almost-everywhere measurable functions glue
along a countable null-measurable conull partition. -/
theorem finiteStoppedAEMeasurable_of_eq_on_countable_partition
    {E : Type*} [MeasurableSpace E]
    (sets : ℕ → Set Ω) (hsets : ∀ i, NullMeasurableSet (sets i) P)
    (hcover : ∀ᵐ omega ∂P, omega ∈ ⋃ i, sets i)
    (selected : ℕ → Ω → E) (returned : Ω → E)
    (hselected : ∀ i, AEMeasurable (selected i) P)
    (heq : ∀ i omega, omega ∈ sets i → returned omega = selected i omega) :
    AEMeasurable returned P := by
  have hrestricted : AEMeasurable returned (P.restrict (⋃ i, sets i)) := by
    rw [aemeasurable_iUnion_iff]
    intro i
    have hselectedRestricted :
        AEMeasurable (selected i) (P.restrict (sets i)) :=
      (hselected i).mono_measure Measure.restrict_le_self
    have heqAE : selected i =ᵐ[P.restrict (sets i)] returned :=
      (ae_restrict_mem₀ (hsets i)).mono fun omega homega ↦
        (heq i omega homega).symm
    exact hselectedRestricted.congr heqAE
  have hmeasure : P.restrict (⋃ i, sets i) = P :=
    Measure.restrict_eq_self_of_ae_mem hcover
  rwa [hmeasure] at hrestricted

/-- Corollary 3.8: the primal point returned by a finite stopped restart is
almost everywhere measurable under almost-sure termination. -/
theorem finiteStoppedReturnedPoint_aemeasurable
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂P,
      firstAccepted restart omega ≠ ⊤) :
    AEMeasurable (returnedPoint restart) P := by
  let sets : ℕ → Set Ω := fun i ↦
    {omega | firstAccepted restart omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) P :=
    by
      simpa only [sets] using
        (measurableSet_finiteStoppedFirstAcceptedFiber hX restart i).nullMeasurableSet
  have hcover : ∀ᵐ omega ∂P, omega ∈ ⋃ i, sets i :=
    finiteStoppedFirstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      returnedPoint restart omega = selectedFiniteStoppedPoint restart i omega := by
    have hindex : (firstAccepted restart omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [returnedPoint_apply]
    unfold selectedFiniteStoppedPoint
    rw [hindex]
  exact finiteStoppedAEMeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedFiniteStoppedPoint restart) (returnedPoint restart)
    (selectedFiniteStoppedPoint_aemeasurable restart) heq

/-- Corollary 3.8: the multiplier returned by a finite stopped restart is
almost everywhere measurable under almost-sure termination. -/
theorem finiteStoppedReturnedMultiplier_aemeasurable
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (htermination : ∀ᵐ omega ∂P,
      firstAccepted restart omega ≠ ⊤) :
    AEMeasurable (returnedMultiplier restart) P := by
  let sets : ℕ → Set Ω := fun i ↦
    {omega | firstAccepted restart omega = (i : ℕ∞)}
  have hsets (i : ℕ) : NullMeasurableSet (sets i) P :=
    by
      simpa only [sets] using
        (measurableSet_finiteStoppedFirstAcceptedFiber hX restart i).nullMeasurableSet
  have hcover : ∀ᵐ omega ∂P, omega ∈ ⋃ i, sets i :=
    finiteStoppedFirstAcceptedFiberUnion_ae restart htermination
  have heq (i : ℕ) (omega : Ω) (homega : omega ∈ sets i) :
      returnedMultiplier restart omega = selectedFiniteStoppedMultiplier restart i omega := by
    have hindex : (firstAccepted restart omega).untopD 0 = i := by
      rw [homega]
      rfl
    rw [returnedMultiplier_apply]
    unfold selectedFiniteStoppedMultiplier
    rw [hindex]
  exact finiteStoppedAEMeasurable_of_eq_on_countable_partition sets hsets hcover
    (selectedFiniteStoppedMultiplier restart) (returnedMultiplier restart)
    (selectedFiniteStoppedMultiplier_aemeasurable restart) heq

/-- Corollary 3.8: a uniform success-restricted selected-residual bound passes
through the almost-surely terminating first-success mixture. -/
theorem finiteStoppedResidualMeanSquare_le_of_successRestricted
    (hX : MeasurableSet X)
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (bound : ℝ≥0∞)
    (htermination : ∀ᵐ omega ∂P, firstAccepted restart omega ≠ ⊤)
    (hsummaryMeas : ∀ i,
      AEMeasurable (finiteStoppedSuccessResidualObservable restart i) P)
    (hsummaryIndep : ProbabilityTheory.iIndepFun
      (fun i ↦ finiteStoppedSuccessResidualObservable restart i) P)
    (hfixed : ∀ i,
      (∫⁻ omega in successEvent restart i,
        selectedFiniteStoppedResidual restart i omega ∂P) ≤
        P (successEvent restart i) * bound) :
    finiteStoppedResidualMeanSquare restart ≤ bound := by
  have hdisjoint : Pairwise fun i j : ℕ ↦
      Disjoint {omega | firstAccepted restart omega = (i : ℕ∞)}
        {omega | firstAccepted restart omega = (j : ℕ∞)} := by
    intro i j hij
    rw [Set.disjoint_left]
    intro omega hi hj
    apply hij
    apply ENat.coe_inj.mp
    exact hi.symm.trans hj
  have haedisjoint : Pairwise fun i j : ℕ ↦
      AEDisjoint P {omega | firstAccepted restart omega = (i : ℕ∞)}
        {omega | firstAccepted restart omega = (j : ℕ∞)} :=
    hdisjoint.aedisjoint
  have hfiberMeas (i : ℕ) : MeasurableSet
      {omega | firstAccepted restart omega = (i : ℕ∞)} :=
    measurableSet_finiteStoppedFirstAcceptedFiber hX restart i
  have hunionAE : ∀ᵐ omega ∂P,
      omega ∈ ⋃ i : ℕ, {omega | firstAccepted restart omega = (i : ℕ∞)} :=
    finiteStoppedFirstAcceptedFiberUnion_ae restart htermination
  have hunionMeasure :
      P (⋃ i : ℕ, {omega | firstAccepted restart omega = (i : ℕ∞)}) = 1 := by
    calc
      P (⋃ i : ℕ, {omega | firstAccepted restart omega = (i : ℕ∞)}) =
          P Set.univ := measure_congr (Filter.eventuallyEq_univ.mpr hunionAE)
      _ = 1 := measure_univ
  calc
    finiteStoppedResidualMeanSquare restart =
        ∫⁻ omega, ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart omega)
            (returnedMultiplier restart omega) ^ 2) ∂P := by
      rw [finiteStoppedResidualMeanSquare, KKT.Stochastic.residualMeanSquare_def]
    _ = ∫⁻ omega in ⋃ i : ℕ,
        {omega | firstAccepted restart omega = (i : ℕ∞)},
        ENNReal.ofReal
          (KKT.residual f c (returnedPoint restart omega)
            (returnedMultiplier restart omega) ^ 2) ∂P := by
      rw [Measure.restrict_eq_self_of_ae_mem hunionAE]
    _ = ∑' i : ℕ,
        ∫⁻ omega in {omega | firstAccepted restart omega = (i : ℕ∞)},
          ENNReal.ofReal
            (KKT.residual f c (returnedPoint restart omega)
              (returnedMultiplier restart omega) ^ 2) ∂P :=
      lintegral_iUnion₀ (fun i ↦ (hfiberMeas i).nullMeasurableSet)
        haedisjoint _
    _ ≤ ∑' i : ℕ,
        P {omega | firstAccepted restart omega = (i : ℕ∞)} * bound :=
      ENNReal.tsum_le_tsum fun i ↦
        finiteStoppedFirstAcceptedFiberResidual_le hX restart bound
          hsummaryMeas hsummaryIndep hfixed i
    _ = (∑' i : ℕ,
        P {omega | firstAccepted restart omega = (i : ℕ∞)}) * bound :=
      ENNReal.tsum_mul_right
    _ = P (⋃ i : ℕ,
        {omega | firstAccepted restart omega = (i : ℕ∞)}) * bound := by
      rw [measure_iUnion₀ haedisjoint
        (fun i ↦ (hfiberMeas i).nullMeasurableSet)]
    _ = 1 * bound := by rw [hunionMeasure]
    _ = bound := one_mul bound

namespace CertifiedStoppedSafeguardedRestart

/-- Corollary 3.8: a certified stopped restart transfers a uniform finite
success-restricted bound to the residual of its first accepted pair. -/
theorem finiteStoppedResidualMeanSquare_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (bound : ℝ≥0∞)
    (hbound : ∀ i,
      (canonicalUniformSuccessResidualNumerator
        (certified.restart.attempt i) hK) ≤
        P (successEvent certified.restart i) * bound) :
    finiteStoppedResidualMeanSquare certified.restart ≤ bound := by
  have htermination := certified.terminatesAE confidence_pos confidence_lt_one
  have hsummaryMeas : ∀ i,
      AEMeasurable (finiteStoppedSuccessResidualObservable certified.restart i) P :=
    fun i ↦ finiteStoppedSuccessResidualObservable_aemeasurable
      certified.restart i
  have hsummaryIndep :=
    finiteStoppedSuccessResidualObservable_iIndep certified.restart
  have hfixed : ∀ i,
      (∫⁻ omega in successEvent certified.restart i,
        selectedFiniteStoppedResidual certified.restart i omega ∂P) ≤
      P (successEvent certified.restart i) * bound := by
    intro i
    rw [successRestrictedSelectedFiniteStoppedResidual_eq_canonicalNumerator
      certified.restart i]
    exact hbound i
  have hX : MeasurableSet X :=
    (certified.restart.attempt 0).measurableSet_localization
  exact finiteStoppedResidualMeanSquare_le_of_successRestricted
    hX certified.restart bound
    htermination hsummaryMeas hsummaryIndep hfixed

/-- Corollary 3.8: the canonical source certificate yields the advertised
`C_st / ((1 - confidence) * (K - 1))` residual target. -/
theorem finiteStoppedResidualMeanSquare_le_tex
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    finiteStoppedResidualMeanSquare
        (CertifiedStoppedSafeguardedRestart.canonical restart
          confidence_pos confidence_lt_one).restart ≤
      ENNReal.ofReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) := by
  let certified := CertifiedStoppedSafeguardedRestart.canonical restart
    confidence_pos confidence_lt_one
  change finiteStoppedResidualMeanSquare certified.restart ≤
    ENNReal.ofReal
      (LALM.StochasticRun.complexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1)))
  refine finiteStoppedResidualMeanSquare_le certified confidence_pos
    confidence_lt_one
    (ENNReal.ofReal
      (LALM.StochasticRun.complexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1)))) ?_
  intro i
  let hcert := certified.certificate i
  dsimp [certified, CertifiedStoppedSafeguardedRestart.canonical] at hcert
  have hnum := hcert.uniformSuccessResidualNumerator_le
    (finiteStoppedPrefixInvariant (certified.restart.attempt i))
  calc
    canonicalUniformSuccessResidualNumerator
        (certified.restart.attempt i) hK ≤
        P (successEvent certified.restart i) *
          (hcert.residualPerSuccessBound : ℝ≥0∞) := by
      exact hnum
    _ ≤ P (successEvent certified.restart i) *
        ENNReal.ofReal
          (LALM.StochasticRun.complexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := by
      apply mul_le_mul_right
      have hres : hcert.residualPerSuccessBound =
          Real.toNNReal
            (LALM.StochasticRun.complexityConstant h oracle params /
              ((1 - confidence) * ((K : ℝ) - 1))) := by
        simpa [hcert, certified, CertifiedStoppedSafeguardedRestart.canonical] using
          (canonical_certificate_residualPerSuccessBound restart
            confidence_pos confidence_lt_one i)
      rw [hres]
      rw [← ENNReal.ofReal_coe_nnreal]
      rw [ENNReal.ofReal_le_ofReal_iff']
      by_cases hnonneg : 0 ≤
          LALM.StochasticRun.complexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))
      · left
        rw [Real.coe_toNNReal _ hnonneg]
      · right
        simp [Real.toNNReal_of_nonpos (le_of_not_ge hnonneg)]

/-- Corollary 3.8: a certified stopped restart has measurable returned
coordinates and inherits a uniform residual bound. -/
theorem returnedPairResidualBounds
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (bound : ℝ≥0∞)
    (hbound : ∀ i,
      canonicalUniformSuccessResidualNumerator
          (certified.restart.attempt i) hK ≤
        P (successEvent certified.restart i) * bound) :
    AEMeasurable (returnedPoint certified.restart) P ∧
      AEMeasurable (returnedMultiplier certified.restart) P ∧
      finiteStoppedResidualMeanSquare certified.restart ≤ bound := by
  have htermination := certified.terminatesAE confidence_pos confidence_lt_one
  have hX : MeasurableSet X :=
    (certified.restart.attempt 0).measurableSet_localization
  have hpoint := finiteStoppedReturnedPoint_aemeasurable hX
    certified.restart htermination
  have hmultiplier := finiteStoppedReturnedMultiplier_aemeasurable hX
    certified.restart htermination
  have hresidual := finiteStoppedResidualMeanSquare_le certified
    confidence_pos confidence_lt_one bound hbound
  exact ⟨hpoint, hmultiplier, hresidual⟩

/-- Corollary 3.8: a residual mean-square bound gives the stochastic
approximate-KKT pair property for the first accepted finite attempt. -/
theorem isApproximatePair_of_residualMeanSquare_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (ε : ℝ≥0)
    (hresidual : finiteStoppedResidualMeanSquare certified.restart ≤ ε ^ 2) :
    KKT.Stochastic.IsApproximatePair P f c ε
      (returnedPoint certified.restart) (returnedMultiplier certified.restart) := by
  have htermination := certified.terminatesAE confidence_pos confidence_lt_one
  have hX : MeasurableSet X :=
    (certified.restart.attempt 0).measurableSet_localization
  have hpoint := finiteStoppedReturnedPoint_aemeasurable hX
    certified.restart htermination
  have hmultiplier := finiteStoppedReturnedMultiplier_aemeasurable hX
    certified.restart htermination
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hpoint hmultiplier hresidual

/-- Corollary 3.8: at the article iteration threshold, the first accepted
finite stopped output is a stochastic `ε`-KKT pair. -/
theorem isApproximatePair_of_iterationBound
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      LALM.StochasticRun.complexityConstant h oracle params *
          (ε : ℝ)⁻¹ ^ 2 ≤
        (1 - confidence) * ((K : ℝ) - 1)) :
    KKT.Stochastic.IsApproximatePair P f c ε
      (returnedPoint
        (CertifiedStoppedSafeguardedRestart.canonical restart
          confidence_pos confidence_lt_one).restart)
      (returnedMultiplier
        (CertifiedStoppedSafeguardedRestart.canonical restart
          confidence_pos confidence_lt_one).restart) := by
  let certified := CertifiedStoppedSafeguardedRestart.canonical restart
    confidence_pos confidence_lt_one
  change KKT.Stochastic.IsApproximatePair P f c ε
    (returnedPoint certified.restart) (returnedMultiplier certified.restart)
  have hε : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hεne : (ε : ℝ) ≠ 0 := hε.ne'
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator : 0 < (1 - confidence) * ((K : ℝ) - 1) :=
    mul_pos (sub_pos.mpr confidence_lt_one) (sub_pos.mpr hKreal)
  have hrealRate :
      LALM.StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1)) ≤
        (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      LALM.StochasticRun.complexityConstant h oracle params =
          (LALM.StochasticRun.complexityConstant h oracle params *
              (ε : ℝ)⁻¹ ^ 2) * (ε : ℝ) ^ 2 := by
        field_simp [hεne]
      _ ≤ ((1 - confidence) * ((K : ℝ) - 1)) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 * ((1 - confidence) * ((K : ℝ) - 1)) := by
        ring
  have htex := finiteStoppedResidualMeanSquare_le_tex restart
    confidence_pos confidence_lt_one
  change finiteStoppedResidualMeanSquare certified.restart ≤
    ENNReal.ofReal
      (LALM.StochasticRun.complexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1))) at htex
  have hresidual : finiteStoppedResidualMeanSquare certified.restart ≤ ε ^ 2 := by
    calc
      finiteStoppedResidualMeanSquare certified.restart ≤
          ENNReal.ofReal
            (LALM.StochasticRun.complexityConstant h oracle params /
              ((1 - confidence) * ((K : ℝ) - 1))) := htex
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  exact isApproximatePair_of_residualMeanSquare_le certified
    confidence_pos confidence_lt_one ε hresidual

end CertifiedStoppedSafeguardedRestart

end LALM.FiniteStopped

end

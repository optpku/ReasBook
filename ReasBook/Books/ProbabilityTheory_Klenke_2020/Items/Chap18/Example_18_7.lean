/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_3
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

/-- The one-step increment law of the lazy nearest-neighbor walk on `ℤ`: jump by `-1`, `0`, or
`1` with probability `1 / 3` each. -/
def lazyNearestNeighborStepPMF : PMF ℤ :=
  (PMF.uniformOfFintype (Fin 3)).bind fun i ↦ PMF.pure (((i : ℕ) : ℤ) - 1)

/-- The transition matrix of the lazy nearest-neighbor walk on `ℤ`, viewed as the singleton-mass
presentation of the translation kernel driven by `lazyNearestNeighborStepPMF`. -/
abbrev lazyNearestNeighborTransitionMatrix : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure x {y}

/-- Helper for Example 18.7: the lazy nearest-neighbor step law assigns mass `1 / 3` exactly to
the increments `-1`, `0`, and `1`. -/
theorem lazyNearestNeighborStepPMF_apply (z : ℤ) :
    lazyNearestNeighborStepPMF z =
      if |z| ≤ 1 then
        1 / 3
      else
        0 := by
  by_cases hz : |z| ≤ 1
  · -- Proof comment: inside the support, `z` can only be `-1`, `0`, or `1`, so the finite
    -- enumeration of the uniform law closes the calculation.
    have hzcases : z = -1 ∨ z = 0 ∨ z = 1 := by
      have hz' : -1 ≤ z ∧ z ≤ 1 := abs_le.mp hz
      omega
    rcases hzcases with rfl | rfl | rfl
    · simp [lazyNearestNeighborStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
        Fin.sum_univ_three]
    · simp [lazyNearestNeighborStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
        Fin.sum_univ_three]
    · simp [lazyNearestNeighborStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply,
        Fin.sum_univ_three]
  · -- Proof comment: outside `{-1, 0, 1}`, every Dirac summand in the finite support misses `z`.
    have hzoff : ∀ i : Fin 3, z ≠ (((i : ℕ) : ℤ) - 1) := by
      intro i
      fin_cases i
      · intro h
        subst h
        exact hz (by norm_num)
      · intro h
        subst h
        exact hz (by norm_num)
      · intro h
        subst h
        exact hz (by norm_num)
    simp [lazyNearestNeighborStepPMF, PMF.bind_apply, PMF.uniformOfFintype_apply, hz, hzoff]

/-- Helper for Example 18.7: the lazy nearest-neighbor step law has finite first moment and zero
drift. -/
theorem lazyNearestNeighborStepPMF_integrable_mean_zero :
    Integrable (fun z : ℤ ↦ (z : ℝ)) lazyNearestNeighborStepPMF.toMeasure ∧
      ∫ z, (z : ℝ) ∂lazyNearestNeighborStepPMF.toMeasure = 0 := by
  let μ : Measure ℤ := lazyNearestNeighborStepPMF.toMeasure
  let A : Set ℤ := {z | |z| ≤ 1}
  have hAcompl_zero : μ Aᶜ = 0 := by
    -- Proof comment: outside `{-1, 0, 1}` the explicit PMF formula already vanishes.
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF)
      (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)]
    refine ENNReal.tsum_eq_zero.2 ?_
    intro z
    by_cases hz : |z| ≤ 1
    · simp [A, hz]
    · simp [A, hz, lazyNearestNeighborStepPMF_apply]
  have hA_ae : ∀ᵐ z ∂μ, z ∈ A := by
    filter_upwards [compl_mem_ae_iff.2 hAcompl_zero] with z hz
    simpa using hz
  let g : ℤ → ℝ := fun z ↦ if z ∈ A then (z : ℝ) else 0
  have hg_integrable : Integrable g μ := by
    -- Proof comment: truncating to the three-point support bounds the observable by `1`.
    refine (integrable_const (1 : ℝ)).mono'
      (Measurable.of_discrete.aestronglyMeasurable) <|
      Filter.Eventually.of_forall fun z => by
        by_cases hz : z ∈ A
        · have hz' : |z| ≤ 1 := hz
          have hzreal : |(z : ℝ)| ≤ 1 := by
            exact_mod_cast hz'
          simpa [g, hz, Real.norm_eq_abs] using hzreal
        · simp [g, hz]
  have hfg_ae : (fun z : ℤ ↦ (z : ℝ)) =ᵐ[μ] g := by
    filter_upwards [hA_ae] with z hz
    simp [g, hz]
  have h_integrable : Integrable (fun z : ℤ ↦ (z : ℝ)) μ :=
    hg_integrable.congr hfg_ae.symm
  refine ⟨h_integrable, ?_⟩
  -- Proof comment: the expectation is the three-point sum of the explicit masses, and the
  -- symmetric `±1` contributions cancel.
  rw [show ∫ z, (z : ℝ) ∂μ =
      ∑' z : ℤ, (lazyNearestNeighborStepPMF z).toReal * (z : ℝ) by
        simpa [μ, smul_eq_mul] using
          (PMF.integral_eq_tsum lazyNearestNeighborStepPMF
            (fun z : ℤ ↦ (z : ℝ)) h_integrable)]
  rw [tsum_eq_sum (s := ({(-1 : ℤ), 0, 1} : Finset ℤ))]
  · norm_num [lazyNearestNeighborStepPMF_apply]
  · intro z hz
    have hz' : ¬ |z| ≤ 1 := by
      intro habs
      have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by
        have hzabs : -1 ≤ z ∧ z ≤ 1 := abs_le.mp habs
        omega
      rcases hcases with rfl | rfl | rfl <;> exact hz (by simp)
    simp [lazyNearestNeighborStepPMF_apply, hz']

/-- Helper for Example 18.7: evaluating `lazyNearestNeighborTransitionMatrix` on a singleton
target recovers the usual lazy nearest-neighbor transition probabilities. -/
theorem lazyNearestNeighborTransitionMatrix_apply (x y : ℤ) :
    lazyNearestNeighborTransitionMatrix x y =
      if |x - y| ≤ 1 then
        1 / 3
      else
        0 := by
  -- Proof comment: rewrite the translated singleton back to the increment `y - x` and then use
  -- the explicit step-law formula.
  rw [lazyNearestNeighborTransitionMatrix, dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage : (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp
    omega
  rw [hpreimage, PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF)
    (measurableSet_singleton (y - x))]
  simpa [abs_sub_comm] using lazyNearestNeighborStepPMF_apply (y - x)

/-- Helper for Example 18.7: the lazy nearest-neighbor transition matrix is stochastic. -/
theorem lazyNearestNeighborTransitionMatrix_kernel_eq_diracConvolutionKernel :
    discreteMatrixKernel lazyNearestNeighborTransitionMatrix =
      dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure := by
  -- Proof comment: on the discrete state space `ℤ`, equality of kernels is determined by their
  -- singleton masses, and `lazyNearestNeighborTransitionMatrix` was defined from exactly those.
  ext x s hs
  exact congrArg (fun μ : Measure ℤ ↦ μ s) <|
    Measure.ext_of_singleton
      (μ := discreteMatrixKernel lazyNearestNeighborTransitionMatrix x)
      (ν := dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure x) fun y ↦ by
        rw [discreteMatrixKernel_apply_singleton]

/-- Helper for Example 18.7: the lazy nearest-neighbor transition matrix is stochastic. -/
theorem lazyNearestNeighborTransitionMatrix_isStochastic :
    IsStochasticMatrix lazyNearestNeighborTransitionMatrix := by
  intro x
  -- Proof comment: each row sum is the total mass of the corresponding convolution-kernel row.
  calc
    ∑' y : ℤ, lazyNearestNeighborTransitionMatrix x y =
        discreteMatrixKernel lazyNearestNeighborTransitionMatrix x Set.univ := by
          rw [← discreteMatrixKernel_univ lazyNearestNeighborTransitionMatrix x]
    _ = dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure x Set.univ := by
      rw [lazyNearestNeighborTransitionMatrix_kernel_eq_diracConvolutionKernel]
    _ = 1 := by
      simp

/-- Helper for Example 18.7: the lazy nearest-neighbor walk on `ℤ` is translation invariant. -/
theorem lazyNearestNeighborTransitionMatrix_isTranslationInvariant :
    IsTranslationInvariantStepMatrix lazyNearestNeighborTransitionMatrix := by
  intro x y
  -- Proof comment: the explicit singleton formula depends only on the increment `y - x`.
  have hsub : 0 - (y - x) = x - y := by
    omega
  simp [lazyNearestNeighborTransitionMatrix_apply, hsub]

/-- Helper for Example 18.7: the lazy nearest-neighbor walk has strictly positive one-step
holding probability at every state. -/
theorem lazyNearestNeighborTransitionMatrix_selfLoop_pos (x : ℤ) :
    0 < (discreteMatrixKernel lazyNearestNeighborTransitionMatrix) x ({x} : Set ℤ) := by
  -- Proof comment: the singleton mass at the current state is the step mass of increment `0`.
  rw [discreteMatrixKernel_apply_singleton, lazyNearestNeighborTransitionMatrix_apply]
  norm_num

/-- Helper for Example 18.7: the lazy nearest-neighbor walk on `ℤ` is aperiodic because every
state has a positive one-step return probability. -/
theorem lazyNearestNeighborTransitionMatrix_isAperiodic :
    IsAperiodic (discreteMatrixKernel lazyNearestNeighborTransitionMatrix) := by
  intro x
  have hmem :
      1 ∈
        positiveTransitionStepSet
          (discreteMatrixKernel lazyNearestNeighborTransitionMatrix) x x := by
      rw [mem_positiveTransitionStepSet_iff]
      simpa [pow_one] using lazyNearestNeighborTransitionMatrix_selfLoop_pos x
  exact Nat.dvd_one.mp
    (statePeriod_dvd_of_mem_positiveTransitionStepSet
      (discreteMatrixKernel lazyNearestNeighborTransitionMatrix) x hmem)

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [DiscreteMeasurableSpace (E × E)]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞}
variable {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}

/-- Helper for Example 18.7: the one-step kernel attached to the independent coalescent matrix. -/
abbrev coalescentKernel (p : E → E → ℝ≥0∞) : Kernel (E × E) (E × E) :=
  discreteMatrixKernel (independentCoalescentMatrix p)

/-- Helper for Example 18.7: the one-step kernel attached to the base matrix `p`. -/
abbrev baseKernel (p : E → E → ℝ≥0∞) : Kernel E E :=
  discreteMatrixKernel p

/-- Helper for Example 18.7: the semigroup generated by the independent coalescent one-step
kernel. -/
abbrev coalescentSemigroup (p : E → E → ℝ≥0∞) : ℕ → Kernel (E × E) (E × E) :=
  fun n ↦ coalescentKernel p ^ n

omit [MeasurableSpace Ω] in
/-- Helper for Example 18.7: applying a measurable state map pointwise can only shrink the
generated history filtration. -/
lemma generatedFiltrationSpace_comp_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (X : ℕ → Ω → α) (f : α → β) (hf : Measurable f) (s : ℕ) :
    generatedFiltrationSpace (fun n ω ↦ f (X n ω)) s ≤ generatedFiltrationSpace X s := by
  -- Proof comment: every transformed coordinate is measurable with respect to the original
  -- history because it is just the old coordinate followed by `f`.
  rw [generatedFiltrationSpace]
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  have hXn :
      Measurable[generatedFiltrationSpace X s] (X n) := by
    exact Measurable.of_comap_le <| le_iSup_of_le n <| le_iSup_of_le hn le_rfl
  exact (hf.comp hXn).comap_le

omit [MeasurableSpace Ω] in
/-- Helper for Example 18.7: the present-coordinate sigma-algebra sits inside the generated
history filtration. -/
lemma present_le_generatedHistory {α : Type*} [MeasurableSpace α]
    (X : ℕ → Ω → α) (s : ℕ) :
    MeasurableSpace.comap (X s) ‹MeasurableSpace α› ≤ generatedFiltrationSpace X s := by
  -- Proof comment: the defining supremum for the history filtration already contains the time-`s`
  -- coordinate sigma-algebra.
  exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl

/-- Helper for Example 18.7: if all coordinates are ambient-measurable, then the generated
history filtration is also ambient-measurable. -/
lemma generatedHistory_le_ambient {α : Type*} [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n : ℕ, Measurable (X n)) (s : ℕ) :
    generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
  -- Proof comment: each coordinate sigma-algebra in the supremum already lies in the ambient
  -- measurable structure.
  refine iSup_le fun n ↦ ?_
  refine iSup_le fun hn ↦ ?_
  exact (hX n).comap_le

/-- Helper for Example 18.7: on a history event fixing `X n = y`, the next-step singleton mass is
the one-step mass from `y` times the probability of that history event. -/
lemma measureInter_eq_mul_stepMass_of_stateEvent
    {q : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : E) (n : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + 1) ω = w}) =
      (discreteMatrixKernel q y ({w} : Set E)) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃B : Set E⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the Markov-property owner theorem to one step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hnext_meas : MeasurableSet (X (n + 1) ⁻¹' ({w} : Set E)) := by
    exact (hReal.measurable_process (n + 1)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + 1) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + 1) ⁻¹' ({w} : Set E)) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced intersection as the indicator of the next-step
              -- singleton event restricted to the history event.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hnext_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ 1) (X n ω)).real ({w} : Set E) ∂μ := by
            symm
            -- Proof comment: the history bridge reduces the sliced event to the one-step kernel
            -- mass seen from the time-`n` state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set E))
                (measurableSet_singleton w) n 1 (B := A) hA_measFiltration
      _ = ∫ ω in A, (discreteMatrixKernel q y).real ({w} : Set E) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is frozen at `y`, so the integrand is
            -- constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
            simp [pow_one]
      _ = (discreteMatrixKernel q y ({w} : Set E)).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q) y).real ({w} : Set E) =
                (((discreteMatrixKernel q) y) ({w} : Set E)).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + 1) ω = w}) =
        (discreteMatrixKernel q y ({w} : Set E)) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top (discreteMatrixKernel q y) ({w} : Set E)).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

/-- Helper for Example 18.7: on a history event fixing `X n = y`, the future singleton mass
after `t` additional steps factors through the `t`-step kernel row from `y`. -/
lemma measureInter_eq_mul_kernelPowMass_of_stateEvent
    {q : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω}
    {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X]
    (x y w : E) (n t : ℕ) (A : Set Ω)
    (hA_meas : MeasurableSet A)
    (hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_state : ∀ ⦃ω : Ω⦄, ω ∈ A → X n ω = y) :
    (P x : Measure Ω) (A ∩ {ω | X (n + t) ω = w}) =
      ((discreteMatrixKernel q ^ t) y ({w} : Set E)) * (P x : Measure Ω) A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal : IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) P X := inferInstance
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hstep :
      ∀ x' : E, ∀ ⦃B : Set E⦄, MeasurableSet B → ∀ s : ℕ,
        (P x')⟦X (s + 1) ⁻¹' B | generatedFiltrationSpace X s⟧ =ᵐ[(P x' : Measure Ω)]
          fun ω ↦ ((discreteMatrixKernel q) (X s ω)).real B := by
    intro x' B hB s
    -- Proof comment: specialize the owner Markov property to one step and simplify `^ 1`.
    simpa [Nat.add_comm] using hReal.markov_property x' (A := B) hB s 1
  have hfuture_meas : MeasurableSet (X (n + t) ⁻¹' ({w} : Set E)) := by
    exact (hReal.measurable_process (n + t)) (measurableSet_singleton w)
  have hslice_real :
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
        (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal * μ.real A := by
    calc
      μ.real (A ∩ {ω | X (n + t) ω = w}) =
          ∫ ω in A,
            Set.indicator (X (n + t) ⁻¹' ({w} : Set E)) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
              rw [← MeasureTheory.integral_indicator hA_meas]
              -- Proof comment: rewrite the sliced future event as the restricted indicator on the
              -- history event `A`.
              simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                Set.inter_comm, smul_eq_mul] using
                (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                  (hA_meas.inter hfuture_meas)).symm
      _ =
          ∫ ω in A, ((discreteMatrixKernel q ^ t) (X n ω)).real ({w} : Set E) ∂μ := by
            symm
            -- Proof comment: the arbitrary-gap history bridge identifies the restricted future
            -- singleton event with the `t`-step kernel mass from the present state.
            simpa [Nat.add_comm] using
              kernelPow_setIntegral_eq_on_history
                (κ₁ := discreteMatrixKernel q) (P := P) (X := X)
                hReal.measurable_process hstep x (A := ({w} : Set E))
                (measurableSet_singleton w) n t (B := A) hA_measFiltration
      _ = ∫ ω in A, ((discreteMatrixKernel q ^ t) y).real ({w} : Set E) ∂μ := by
            -- Proof comment: on `A`, the time-`n` state is fixed, so the `t`-step row is constant.
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem hA_meas] with ω hω
            rw [hA_state hω]
      _ = (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal * μ.real A := by
            rw [show ((discreteMatrixKernel q ^ t) y).real ({w} : Set E) =
                (((discreteMatrixKernel q ^ t) y) ({w} : Set E)).toReal by rfl]
            rw [MeasureTheory.setIntegral_const, Measure.real_def, smul_eq_mul, mul_comm]
  have hslice_enn :
      μ (A ∩ {ω | X (n + t) ω = w}) =
        ((discreteMatrixKernel q ^ t) y ({w} : Set E)) * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff'
        (measure_lt_top μ _).ne
        (ENNReal.mul_ne_top
          (by exact (measure_lt_top ((discreteMatrixKernel q ^ t) y) ({w} : Set E)).ne)
          (by exact (measure_lt_top μ A).ne))).mp ?_
    simpa [μ, Measure.real_def, ENNReal.toReal_mul, mul_comm] using hslice_real
  simpa [μ] using hslice_enn

omit [DiscreteMeasurableSpace (E × E)] in
/-- Helper for Example 18.7: summing an independent-coalescent row over the second coordinate
recovers the first-coordinate transition probability. -/
lemma tsum_independentCoalescentMatrix_fst
    (hp : IsStochasticMatrix p) (x y z : E) :
    ∑' w : E, independentCoalescentMatrix p (x, y) (z, w) = p x z := by
  -- Proof comment: on the diagonal only the term `w = z` survives; off the diagonal the row
  -- factorizes and the second-coordinate sum is `1`.
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single z]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro w hw
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hw hzw.symm
  · calc
      ∑' w : E, independentCoalescentMatrix p (x, y) (z, w)
          = ∑' w : E, p x z * p y w := by
              refine tsum_congr fun w ↦ ?_
              rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]
      _ = p x z * ∑' w : E, p y w := by
            rw [ENNReal.tsum_mul_left]
      _ = p x z := by
            simp [hp y]

omit [DiscreteMeasurableSpace (E × E)] in
/-- Helper for Example 18.7: summing an independent-coalescent row over the first coordinate
recovers the second-coordinate transition probability. -/
lemma tsum_independentCoalescentMatrix_snd
    (hp : IsStochasticMatrix p) (x y w : E) :
    ∑' z : E, independentCoalescentMatrix p (x, y) (z, w) = p y w := by
  -- Proof comment: this is the symmetric companion of the first row-sum identity.
  classical
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single w]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro z hz
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hz hzw
  · calc
      ∑' z : E, independentCoalescentMatrix p (x, y) (z, w)
          = ∑' z : E, p x z * p y w := by
              refine tsum_congr fun z ↦ ?_
              rw [independentCoalescentMatrix_apply_of_ne (p := p) hxy]
      _ = (∑' z : E, p x z) * p y w := by
            rw [ENNReal.tsum_mul_right]
      _ = p y w := by
            simp [hp x]

/-- Helper for Example 18.7: any realization of the coalescent semigroup forces the base matrix
to be stochastic. -/
lemma baseMatrix_isStochastic_of_coalescentRealization
    (P : E × E → ProbabilityMeasure Ω) (Z : ℕ → Ω → E × E)
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z] :
    IsStochasticMatrix p := by
  classical
  let hreal : IsMarkovProcessRealization (coalescentSemigroup p) P Z := inferInstance
  let _ : IsMarkovKernel (coalescentKernel p) := by
    simpa [coalescentSemigroup, coalescentKernel] using hreal.semigroup.isMarkovKernel 1
  intro x
  have hslice : ∀ z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) = p x z := by
    intro z
    rw [tsum_eq_single z]
    · rw [independentCoalescentMatrix_apply_diag]
    · intro w hw
      rw [independentCoalescentMatrix_apply_diag_of_ne (p := p)]
      exact fun hzw ↦ hw hzw.symm
  have huniv : coalescentKernel p (x, x) Set.univ = 1 := by
    let hprob : IsProbabilityMeasure ((coalescentKernel p) (x, x)) :=
      (inferInstance : IsMarkovKernel (coalescentKernel p)).isProbabilityMeasure (x, x)
    exact hprob.measure_univ
  -- Proof comment: the diagonal coalescent row has total mass `1`, and Example 18.6 collapses
  -- that row sum to the single row sum of `p`.
  calc
    ∑' z : E, p x z
        = ∑' z : E, ∑' w : E, independentCoalescentMatrix p (x, x) (z, w) := by
            refine tsum_congr fun z ↦ ?_
            exact (hslice z).symm
    _ = ∑' s : E × E, independentCoalescentMatrix p (x, x) s := by
          simpa using
            (ENNReal.tsum_prod'
              (f := fun s : E × E ↦ independentCoalescentMatrix p (x, x) s)).symm
    _ = 1 := by
          simpa [coalescentKernel, discreteMatrixKernel_univ] using huniv

/-- Helper for Example 18.7: the first marginal of the coalescent one-step kernel is the base
kernel. -/
lemma independentCoalescentKernel_fst (hp : IsStochasticMatrix p) :
    Kernel.fst (coalescentKernel p) =
      Kernel.comap (baseKernel p) Prod.fst measurable_fst := by
  classical
  refine Kernel.ext fun a ↦ ?_
  rcases a with ⟨x, y⟩
  refine Measure.ext fun (s : Set E) hs ↦ ?_
  -- Proof comment: rewrite the marginal as an iterated sum and collapse the second-coordinate
  -- slice with the previous row-sum lemma.
  rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply', coalescentKernel, baseKernel,
    discreteMatrixKernel_apply, discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  calc
    (Measure.sum fun j ↦ independentCoalescentMatrix p (x, y) j • Measure.dirac j) (Prod.fst ⁻¹' s)
        = ∑' b : E × E,
            (independentCoalescentMatrix p (x, y) b • Measure.dirac b) (Prod.fst ⁻¹' s) := by
              rw [Measure.sum_apply _ (measurable_fst hs)]
    _ = ∑' b : E × E, independentCoalescentMatrix p (x, y) b * s.indicator 1 b.1 := by
          refine tsum_congr fun b ↦ ?_
          simp [Set.indicator, Measure.smul_apply, mul_comm]
    _ = ∑' z : E, ∑' w : E,
          independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 z := by
            simpa using
              (ENNReal.tsum_prod'
                (f := fun b : E × E ↦
                  independentCoalescentMatrix p (x, y) b * s.indicator 1 b.1))
    _ = ∑' z : E,
          (∑' w : E, independentCoalescentMatrix p (x, y) (z, w)) * s.indicator 1 z := by
          refine tsum_congr fun z ↦ ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' z : E, p x z * s.indicator 1 z := by
          refine tsum_congr fun z ↦ ?_
          rw [tsum_independentCoalescentMatrix_fst hp x y z]
    _ = ∑' z : E, (p x z • Measure.dirac z) s := by
          refine tsum_congr fun z ↦ ?_
          simp [Measure.smul_apply]

/-- Helper for Example 18.7: the second marginal of the coalescent one-step kernel is the base
kernel. -/
lemma independentCoalescentKernel_snd (hp : IsStochasticMatrix p) :
    Kernel.snd (coalescentKernel p) =
      Kernel.comap (baseKernel p) Prod.snd measurable_snd := by
  classical
  refine Kernel.ext fun a ↦ ?_
  rcases a with ⟨x, y⟩
  refine Measure.ext fun (s : Set E) hs ↦ ?_
  -- Proof comment: the second marginal is the symmetric iterated-sum collapse.
  rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply', coalescentKernel, baseKernel,
    discreteMatrixKernel_apply, discreteMatrixKernel_apply, Measure.sum_apply _ hs]
  calc
    (Measure.sum fun j ↦ independentCoalescentMatrix p (x, y) j • Measure.dirac j) (Prod.snd ⁻¹' s)
        = ∑' b : E × E,
            (independentCoalescentMatrix p (x, y) b • Measure.dirac b) (Prod.snd ⁻¹' s) := by
              rw [Measure.sum_apply _ (measurable_snd hs)]
    _ = ∑' b : E × E, independentCoalescentMatrix p (x, y) b * s.indicator 1 b.2 := by
          refine tsum_congr fun b ↦ ?_
          simp [Set.indicator, Measure.smul_apply, mul_comm]
    _ = ∑' z : E, ∑' w : E,
          independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 w := by
            simpa using
              (ENNReal.tsum_prod'
                (f := fun b : E × E ↦
                  independentCoalescentMatrix p (x, y) b * s.indicator 1 b.2))
    _ = ∑' w : E, ∑' z : E,
            independentCoalescentMatrix p (x, y) (z, w) * s.indicator 1 w := by
          rw [ENNReal.tsum_comm]
    _ = ∑' w : E,
          (∑' z : E, independentCoalescentMatrix p (x, y) (z, w)) * s.indicator 1 w := by
          refine tsum_congr fun w ↦ ?_
          rw [ENNReal.tsum_mul_right]
    _ = ∑' w : E, p y w * s.indicator 1 w := by
          refine tsum_congr fun w ↦ ?_
          rw [tsum_independentCoalescentMatrix_snd hp x y w]
    _ = ∑' w : E, (p y w • Measure.dirac w) s := by
          refine tsum_congr fun w ↦ ?_
          simp [Measure.smul_apply]

/-- Helper for Example 18.7: the first coordinate inherits the one-step conditional law of the
base chain after descending from pair history to coordinate history. -/
lemma fst_oneStep_conditional
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z]
    (hp : IsStochasticMatrix p) (y x : E) (s : ℕ) {A : Set E} (hA : MeasurableSet A) :
    (P (x, y))⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A |
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s⟧ =ᵐ[(P (x, y) : Measure Ω)]
        fun ω ↦ (baseKernel p ((Z s ω).1)).real A := by
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let hpair :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z := by
    simpa [coalescentSemigroup, coalescentKernel] using
      (inferInstance : IsMarkovProcessRealization (coalescentSemigroup p) P Z)
  let g : Ω → ℝ := fun ω ↦ (baseKernel p ((Z s ω).1)).real A
  have hsmall_le :
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s ≤ generatedFiltrationSpace Z s := by
    exact generatedFiltrationSpace_comp_le Z Prod.fst measurable_fst s
  have hlarge_le : generatedFiltrationSpace Z s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient Z hpair.measurable_process s
  have hstate :
      Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] fun ω ↦ (Z s ω).1 := by
    exact Measurable.of_comap_le <|
      present_le_generatedHistory (fun n ω ↦ (Z n ω).1) s
  have hg :
      AEStronglyMeasurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] g μ := by
    have hg_measurable :
        Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s] g := by
      exact ((Kernel.measurable_coe (baseKernel p) hA).ennreal_toReal).comp hstate
    exact Measurable.aestronglyMeasurable hg_measurable
  have hpair :
      μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ] g := by
    have hpairRaw :
        μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real
            (Prod.fst ⁻¹' A) := by
      simpa [Function.comp, pow_one, coalescentSemigroup, coalescentKernel, add_comm] using
        hpair.markov_property (x, y) (A := Prod.fst ⁻¹' A) (measurable_fst hA) s 1
    have hkernel :
        ∀ ω : Ω,
          ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.fst ⁻¹' A) =
            (baseKernel p ((Z s ω).1)).real A := by
      intro ω
      calc
        ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.fst ⁻¹' A)
            = ((Kernel.fst (coalescentKernel p)) (Z s ω)).real A := by
                simpa [coalescentKernel] using
                  (Kernel.fst_real_apply (coalescentKernel p) (Z s ω) (s := A) hA).symm
        _ = (baseKernel p ((Z s ω).1)).real A := by
              simpa [baseKernel, Kernel.comap_apply] using
                congrArg (fun κ : Kernel (E × E) E => (κ (Z s ω)).real A)
                  (independentCoalescentKernel_fst (p := p) hp)
    exact hpairRaw.trans <| Filter.Eventually.of_forall hkernel
  have hg_int : Integrable g μ := by
    exact (integrable_congr hpair).1 integrable_condExp
  -- Proof comment: descend the pair-filtration conditional law to the smaller first-coordinate
  -- filtration by the tower property.
  calc
    μ⟦(fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A | generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s⟧
        =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s)
            (MeasureTheory.condExp μ
              (m := generatedFiltrationSpace Z s)
              (((fun ω ↦ (Z (s + 1) ω).1) ⁻¹' A).indicator fun _ ↦ (1 : ℝ))) := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
    _ =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).1) s) g := by
          exact condExp_congr_ae hpair
    _ =ᵐ[μ] g := by
          exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int

/-- Helper for Example 18.7: the second coordinate inherits the one-step conditional law of the
base chain after descending from pair history to coordinate history. -/
lemma snd_oneStep_conditional
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z]
    (hp : IsStochasticMatrix p) (x y : E) (s : ℕ) {A : Set E} (hA : MeasurableSet A) :
    (P (x, y))⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A |
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s⟧ =ᵐ[(P (x, y) : Measure Ω)]
        fun ω ↦ (baseKernel p ((Z s ω).2)).real A := by
  let μ : Measure Ω := (P (x, y) : Measure Ω)
  let hpair :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z := by
    simpa [coalescentSemigroup, coalescentKernel] using
      (inferInstance : IsMarkovProcessRealization (coalescentSemigroup p) P Z)
  let g : Ω → ℝ := fun ω ↦ (baseKernel p ((Z s ω).2)).real A
  have hsmall_le :
      generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s ≤ generatedFiltrationSpace Z s := by
    exact generatedFiltrationSpace_comp_le Z Prod.snd measurable_snd s
  have hlarge_le : generatedFiltrationSpace Z s ≤ ‹MeasurableSpace Ω› := by
    exact generatedHistory_le_ambient Z hpair.measurable_process s
  have hstate :
      Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] fun ω ↦ (Z s ω).2 := by
    exact Measurable.of_comap_le <|
      present_le_generatedHistory (fun n ω ↦ (Z n ω).2) s
  have hg :
      AEStronglyMeasurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] g μ := by
    have hg_measurable :
        Measurable[generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s] g := by
      exact ((Kernel.measurable_coe (baseKernel p) hA).ennreal_toReal).comp hstate
    exact Measurable.aestronglyMeasurable hg_measurable
  have hpair :
      μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ] g := by
    have hpairRaw :
        μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace Z s⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real
            (Prod.snd ⁻¹' A) := by
      simpa [Function.comp, pow_one, coalescentSemigroup, coalescentKernel, add_comm] using
        hpair.markov_property (x, y) (A := Prod.snd ⁻¹' A) (measurable_snd hA) s 1
    have hkernel :
        ∀ ω : Ω,
          ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.snd ⁻¹' A) =
            (baseKernel p ((Z s ω).2)).real A := by
      intro ω
      calc
        ((discreteMatrixKernel (independentCoalescentMatrix p)) (Z s ω)).real (Prod.snd ⁻¹' A)
            = ((Kernel.snd (coalescentKernel p)) (Z s ω)).real A := by
                simpa [coalescentKernel, measureReal_def] using
                  congrArg ENNReal.toReal
                    (Kernel.snd_apply' (coalescentKernel p) (Z s ω) hA).symm
        _ = (baseKernel p ((Z s ω).2)).real A := by
              simpa [baseKernel, Kernel.comap_apply'] using
                congrArg (fun κ : Kernel (E × E) E => (κ (Z s ω)).real A)
                  (independentCoalescentKernel_snd (p := p) hp)
    exact hpairRaw.trans <| Filter.Eventually.of_forall hkernel
  have hg_int : Integrable g μ := by
    exact (integrable_congr hpair).1 integrable_condExp
  -- Proof comment: descend from the pair filtration exactly as in the first-coordinate proof.
  calc
    μ⟦(fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A | generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s⟧
        =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s)
            (MeasureTheory.condExp μ
              (m := generatedFiltrationSpace Z s)
              (((fun ω ↦ (Z (s + 1) ω).2) ⁻¹' A).indicator fun _ ↦ (1 : ℝ))) := by
              symm
              exact condExp_condExp_of_le hsmall_le hlarge_le
    _ =ᵐ[μ]
          MeasureTheory.condExp μ
            (m := generatedFiltrationSpace (fun n ω ↦ (Z n ω).2) s) g := by
          exact condExp_congr_ae hpair
    _ =ᵐ[μ] g := by
          exact condExp_of_aestronglyMeasurable' (hsmall_le.trans hlarge_le) hg hg_int

/-- Helper for Example 18.7: every realization of the coalescent semigroup is a Markov coupling
for its base matrix. -/
theorem independentCoalescentChain_isMarkovCoupling
    [IsMarkovProcessRealization (coalescentSemigroup p) P Z] :
    IsMarkovCoupling p P Z := by
  let hpair : IsMarkovProcessRealization (coalescentSemigroup p) P Z := inferInstance
  let hp : IsStochasticMatrix p :=
    baseMatrix_isStochastic_of_coalescentRealization (p := p) P Z
  letI : IsMarkovKernel (baseKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp
  refine
    { fst_realization := ?_
      snd_realization := ?_ }
  · intro y
    -- Proof comment: package the first-coordinate one-step conditional law with Theorem 17.11.
    refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
      (κ₁ := baseKernel p)
      (P := fun x ↦ P (x, y))
      (X := fun n ω ↦ (Z n ω).1)
      (hmeas := fun n ↦ measurable_fst.comp (hpair.measurable_process n))
      (hstart := ?_)
      (hstep := ?_)
    · intro x
      let μ : Measure Ω := (P (x, y) : Measure Ω)
      have hmap :
          (μ.map (Z 0)).map Prod.fst = μ.map (fun ω ↦ (Z 0 ω).1) := by
        simpa [Function.comp] using
          (Measure.map_map (μ := μ) (f := Z 0) (g := Prod.fst)
            (hf := hpair.measurable_process 0) (hg := measurable_fst))
      calc
        μ.map (fun ω ↦ (Z 0 ω).1) = (μ.map (Z 0)).map Prod.fst := hmap.symm
        _ = (Measure.dirac (x, y)).map Prod.fst := by
          rw [hpair.initial_eq (x, y)]
        _ = Measure.dirac x := by
          simp
    · intro x A hA s
      simpa using fst_oneStep_conditional (p := p) (P := P) (Z := Z) hp y x s hA
  · intro x
    -- Proof comment: the second coordinate is the symmetric one-step application of the same
    -- owner theorem.
    refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
      (κ₁ := baseKernel p)
      (P := fun y ↦ P (x, y))
      (X := fun n ω ↦ (Z n ω).2)
      (hmeas := fun n ↦ measurable_snd.comp (hpair.measurable_process n))
      (hstart := ?_)
      (hstep := ?_)
    · intro y
      let μ : Measure Ω := (P (x, y) : Measure Ω)
      have hmap :
          (μ.map (Z 0)).map Prod.snd = μ.map (fun ω ↦ (Z 0 ω).2) := by
        simpa [Function.comp] using
          (Measure.map_map (μ := μ) (f := Z 0) (g := Prod.snd)
            (hf := hpair.measurable_process 0) (hg := measurable_snd))
      calc
        μ.map (fun ω ↦ (Z 0 ω).2) = (μ.map (Z 0)).map Prod.snd := hmap.symm
        _ = (Measure.dirac (x, y)).map Prod.snd := by
          rw [hpair.initial_eq (x, y)]
        _ = Measure.dirac y := by
          simp
    · intro y A hA s
      simpa using snd_oneStep_conditional (p := p) (P := P) (Z := Z) hp x y s hA

end

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
variable {p : E → E → ℝ≥0∞}
variable [DiscreteMeasurableSpace (E × E)]
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n)
  P Z]

/-- Helper for Example 18.7: once the coalescent chain starts on the diagonal, the next step has
zero mass on the off-diagonal. -/
private lemma coalescentDiagonal_offDiagonalMass_eq_zero
    [Countable E]
    (hp : IsStochasticMatrix p) (x : E) :
    discreteMatrixKernel (independentCoalescentMatrix p) (x, x)
      {s : E × E | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (E × E) (E × E) := discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (E × E) := {s | s.1 ≠ s.2}
  have hstochastic :
      IsStochasticMatrix (independentCoalescentMatrix p) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := p) hp
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel
    (independentCoalescentMatrix p) hstochastic
  calc
    κ (x, x) offDiag
        = ∑' s : E × E, offDiag.indicator (fun s ↦ κ (x, x) ({s} : Set (E × E))) s := by
            simpa using
              (Measure.tsum_indicator_apply_singleton (κ (x, x)) offDiag
                (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
    _ = 0 := by
          refine ENNReal.tsum_eq_zero.mpr ?_
          intro s
          by_cases hs : s.1 ≠ s.2
          · rcases s with ⟨z, w⟩
            have hsOff : (z, w) ∈ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_mem hsOff]
            rw [discreteMatrixKernel_apply_singleton]
            simpa using independentCoalescentMatrix_apply_diag_of_ne (p := p) (x := x) hs
          · have hsNotOff : s ∉ offDiag := by
              simpa [offDiag] using hs
            rw [Set.indicator_of_notMem hsNotOff]

/-- Helper for Example 18.7: once the coalescent chain reaches the diagonal, every later
off-diagonal mass vanishes. -/
private theorem coalescentDiagonal_offDiagonalMass_pow_eq_zero
    [Countable E]
    (hp : IsStochasticMatrix p) (x : E) :
    ∀ n : ℕ, 0 < n →
      ((discreteMatrixKernel (independentCoalescentMatrix p) ^ n) (x, x))
        {s : E × E | s.1 ≠ s.2} = 0 := by
  let κ : Kernel (E × E) (E × E) := discreteMatrixKernel (independentCoalescentMatrix p)
  let offDiag : Set (E × E) := {s | s.1 ≠ s.2}
  have hstochastic :
      IsStochasticMatrix (independentCoalescentMatrix p) := by
    exact independentCoalescentMatrix_isStochasticMatrix (p := p) hp
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel
    (independentCoalescentMatrix p) hstochastic
  have hoffDiag_meas : MeasurableSet offDiag := MeasurableSet.of_discrete
  have hstep_le :
      ∀ z : E × E,
        κ z offDiag ≤ Set.indicator offDiag (fun _ ↦ (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z.1 ≠ z.2
    · have hzOff : z ∈ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_mem hzOff]
      calc
        κ z offDiag ≤ κ z Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := by
            simpa [κ, discreteMatrixKernel_univ] using hstochastic z
    · have hzNotOff : z ∉ offDiag := by
        simpa [offDiag] using hz
      rw [Set.indicator_of_notMem hzNotOff]
      rcases z with ⟨a, b⟩
      have hab : a = b := by
        simpa using hz
      subst b
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) hp a
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction m with
  | zero =>
      -- Proof comment: at one step, the diagonal row already has zero off-diagonal mass.
      simpa [κ, offDiag] using coalescentDiagonal_offDiagonalMass_eq_zero (p := p) hp x
  | succ m ih =>
      -- Proof comment: the next Chapman-Kolmogorov step integrates the same one-step
      -- off-diagonal bound against a measure already supported on the diagonal.
      rw [Kernel.pow_succ_apply_eq_lintegral κ (m + 1) (x, x) hoffDiag_meas]
      refine le_antisymm ?_ bot_le
      calc
        ∫⁻ z, κ z offDiag ∂((κ ^ (m + 1)) (x, x)) ≤
            ∫⁻ z, Set.indicator offDiag (fun _ ↦ (1 : ℝ≥0∞)) z
              ∂((κ ^ (m + 1)) (x, x)) := by
                refine lintegral_mono ?_
                intro z
                exact hstep_le z
        _ = ((κ ^ (m + 1)) (x, x)) offDiag := by
            simp [offDiag, hoffDiag_meas]
        _ = 0 := ih (Nat.succ_pos _)

/-- Helper for Example 18.7: after time `n`, any later disagreement was already present at time
`n`, because the coalescent cannot leave the diagonal once it has entered it. -/
lemma coalescentTailDisagreement_le_currentDisagreement
    [Countable E]
    (hp : IsStochasticMatrix p)
    (x y : E) :
    ∀ n : ℕ,
      (P (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}) ≤
        (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  let μ : Measure Ω := P (x, y)
  let disagree : ℕ → Set Ω := fun n ↦ {ω | (Z n ω).1 ≠ (Z n ω).2}
  let hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z :=
    inferInstance
  intro n
  have hfuture_null :
      μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) = 0 := by
    have hslice_zero :
        ∀ k : ℕ, μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) = 0 := by
      intro k
      have hcover :
          {ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1)) ⊆
            ⋃ z : E, ⋃ s : {t : E × E // t.1 ≠ t.2},
              ({ω | Z n ω = (z, z)} ∩ {ω | Z (n + (k + 1)) ω = s}) := by
        intro ω hω
        rcases hω with ⟨hdiag, hdis⟩
        refine Set.mem_iUnion.2 ?_
        refine ⟨(Z n ω).1, ?_⟩
        have hpair : Z n ω = ((Z n ω).1, (Z n ω).1) := by
          exact Prod.ext rfl hdiag.symm
        refine Set.mem_iUnion.2 ?_
        refine ⟨⟨Z (n + (k + 1)) ω, hdis⟩, ?_⟩
        constructor
        · exact hpair
        · rfl
      refine measure_mono_null hcover ?_
      refine measure_iUnion_null fun z ↦ ?_
      refine measure_iUnion_null fun s ↦ ?_
      have hslice_zero :
          μ ({ω | Z n ω = (z, z)} ∩ {ω | Z (n + (k + 1)) ω = s}) = 0 := by
        have hState_meas :
            MeasurableSet ({ω | Z n ω = (z, z)} : Set Ω) := by
          rw [show ({ω | Z n ω = (z, z)} : Set Ω) =
              Z n ⁻¹' ({(z, z)} : Set (E × E)) by
            ext ω
            simp]
          exact hrealization.measurable_process n (measurableSet_singleton (z, z))
        have hState_hist :
            MeasurableSet[generatedFiltrationSpace Z n] ({ω | Z n ω = (z, z)} : Set Ω) := by
          have hZn :
              Measurable[generatedFiltrationSpace Z n] (Z n) := by
            exact Measurable.of_comap_le <| present_le_generatedHistory (X := Z) n
          rw [show ({ω | Z n ω = (z, z)} : Set Ω) =
              Z n ⁻¹' ({(z, z)} : Set (E × E)) by
            ext ω
            simp]
          exact hZn (measurableSet_singleton (z, z))
        have hState_eq :
            ∀ ⦃ω : Ω⦄, ω ∈ ({ω | Z n ω = (z, z)} : Set Ω) → Z n ω = (z, z) := by
          intro ω hω
          simpa using hω
        rw [measureInter_eq_mul_kernelPowMass_of_stateEvent
          (q := independentCoalescentMatrix p)
          (P := P) (X := Z) (x := (x, y)) (y := (z, z))
          (w := (s : E × E)) (n := n) (t := k + 1)
          ({ω | Z n ω = (z, z)}) hState_meas hState_hist hState_eq]
        have hmass_zero :
            ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1))
              (z, z)) ({(s : E × E)} : Set (E × E)) = 0 := by
          have hOff :
              ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1))
                (z, z)) {t : E × E | t.1 ≠ t.2} = 0 :=
            coalescentDiagonal_offDiagonalMass_pow_eq_zero
              (p := p) hp z (k + 1) (Nat.succ_pos _)
          refine le_antisymm ?_ bot_le
          calc
            ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1))
              (z, z)) ({(s : E × E)} : Set (E × E))
                ≤
              ((discreteMatrixKernel (independentCoalescentMatrix p) ^ (k + 1))
                (z, z)) {t : E × E | t.1 ≠ t.2} := by
                  exact measure_mono (Set.singleton_subset_iff.mpr s.property)
            _ = 0 := hOff
        rw [hmass_zero]
        simp
      exact hslice_zero
    have hinter :
        {ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1)) =
          ⋃ k : ℕ, ({ω | (Z n ω).1 = (Z n ω).2} ∩ disagree (n + (k + 1))) := by
      ext ω
      simp
    rw [hinter]
    exact measure_iUnion_null hslice_zero
  have hUnion :
      (⋃ m ≥ n, disagree m) = disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1)) := by
    ext ω
    constructor
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨m, hm⟩
      rcases Set.mem_iUnion.1 hm with ⟨hmn, hdis⟩
      rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
      · exact Or.inl hdis
      · have hkExists : ∃ k : ℕ, n + (k + 1) = m := ⟨m - n - 1, by omega⟩
        rcases hkExists with ⟨k, hk⟩
        exact Or.inr <| Set.mem_iUnion.2 ⟨k, hk ▸ hdis⟩
    · intro hω
      rcases hω with hω | hω
      · exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩
      · rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
        exact Set.mem_iUnion.2 ⟨n + (k + 1), Set.mem_iUnion.2 ⟨by omega, hk⟩⟩
  have hsubset :
      ⋃ k : ℕ, disagree (n + (k + 1)) ⊆
        disagree n ∪ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
    intro ω hω
    by_cases hdis : (Z n ω).1 ≠ (Z n ω).2
    · exact Or.inl hdis
    · have hEq : (Z n ω).1 = (Z n ω).2 := by
        by_contra hneq
        exact hdis hneq
      exact Or.inr ⟨hEq, hω⟩
  -- Proof comment: split the tail into the present disagreement slice and the strictly later
  -- disagreements; the latter can only occur on a null event where the chain is already on the
  -- diagonal at time `n` and then leaves it again.
  calc
    μ (⋃ m ≥ n, disagree m)
        = μ (disagree n ∪ ⋃ k : ℕ, disagree (n + (k + 1))) := by
            rw [hUnion]
    _ ≤ μ (disagree n) +
        μ ({ω | (Z n ω).1 = (Z n ω).2} ∩ ⋃ k : ℕ, disagree (n + (k + 1))) := by
          refine le_trans (measure_mono ?_) (measure_union_le _ _)
          intro ω hω
          rcases hω with hω | hω
          · exact Or.inl hω
          · exact hsubset hω
    _ = μ (disagree n) := by
          rw [hfuture_null, add_zero]

end

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable {P : ℤ × ℤ → ProbabilityMeasure Ω} {Z : ℕ → Ω → ℤ × ℤ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦
    discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) ^ n)
  P Z]

/-- Helper for Example 18.7: two integer coordinates disagree exactly when their difference is
nonzero. -/
theorem integerPairDisagreementEvent_eq_differenceEvent
    (Z : ℕ → Ω → ℤ × ℤ) (n : ℕ) :
    {ω | (Z n ω).1 ≠ (Z n ω).2} = {ω | (Z n ω).1 - (Z n ω).2 ≠ 0} := by
  -- Proof comment: on `ℤ`, equality of the two coordinates is equivalent to vanishing of their
  -- difference.
  ext ω
  change (Z n ω).1 ≠ (Z n ω).2 ↔ (Z n ω).1 - (Z n ω).2 ≠ 0
  constructor
  · intro h hsub
    exact h (sub_eq_zero.mp hsub)
  · intro h hxy
    apply h
    exact sub_eq_zero.mpr hxy

/-- Helper for Example 18.7: the free one-step difference law of two independent lazy
nearest-neighbor increments. -/
def lazyDifferenceStepPMF : PMF ℤ :=
  let μ : Measure (ℤ × ℤ) := lazyNearestNeighborStepPMF.toMeasure.prod lazyNearestNeighborStepPMF.toMeasure
  letI : IsProbabilityMeasure μ := by infer_instance
  letI : IsProbabilityMeasure (μ.map (fun s : ℤ × ℤ ↦ s.1 - s.2)) := by
    exact Measure.isProbabilityMeasure_map (μ := μ) (by fun_prop)
  (μ.map (fun s : ℤ × ℤ ↦ s.1 - s.2)).toPMF

/-- Helper for Example 18.7: the product measure of two singleton events is the product of the
two singleton masses. -/
private lemma productMeasure_apply_singleton_pair
    (μ ν : Measure ℤ) (x y : ℤ) :
    (μ.prod ν) ({(x, y)} : Set (ℤ × ℤ)) =
      μ ({x} : Set ℤ) * ν ({y} : Set ℤ) := by
  -- Proof comment: rewrite the singleton pair as a measurable rectangle and apply the product
  -- measure formula once.
  simpa [Set.singleton_prod_singleton] using
    (Measure.prod_prod (μ := μ) (ν := ν) ({x} : Set ℤ) ({y} : Set ℤ))

/-- Helper for Example 18.7: on the countable discrete state space `ℤ`, integrating kernel
singleton masses is the same as summing them against the source singleton masses. -/
private lemma lintegralKernelApplySingleton_eq_tsum
    (κ : Kernel ℤ ℤ) (μ : Measure ℤ) (w : ℤ) :
    ∫⁻ c, κ c ({w} : Set ℤ) ∂μ =
      ∑' c : ℤ, κ c ({w} : Set ℤ) * μ ({c} : Set ℤ) := by
  -- Proof comment: `lintegral_countable'` is the standard discrete-space bridge from the kernel
  -- integral to the singleton-mass series.
  simpa [mul_comm] using
    (MeasureTheory.lintegral_countable' (μ := μ)
      (f := fun c : ℤ ↦ κ c ({w} : Set ℤ)))

/-- Helper for Example 18.7: the free difference walk attached to the lazy nearest-neighbor step
law is the translation kernel driven by `lazyDifferenceStepPMF`. -/
abbrev lazyDifferenceStepMatrix : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure x {y}

/-- Helper for Example 18.7: the discrete kernel built from `lazyDifferenceStepMatrix` is the
owner convolution kernel of `lazyDifferenceStepPMF`. -/
lemma lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel :
    discreteMatrixKernel lazyDifferenceStepMatrix =
      dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure := by
  -- Proof comment: on the discrete state space `ℤ`, equality of kernels is determined by
  -- singleton masses, and `lazyDifferenceStepMatrix` was defined from exactly those masses.
  ext x s hs
  have hrow :
      discreteMatrixKernel lazyDifferenceStepMatrix x =
        dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure x := by
    refine Measure.ext_of_singleton ?_
    intro y
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [lazyDifferenceStepMatrix]
    · intro z hz
      simp [Measure.smul_apply, Measure.dirac_apply', hz]
  exact congrArg (fun μ ↦ μ s) hrow

/-- Helper for Example 18.7: the free lazy difference kernel is stochastic. -/
lemma lazyDifferenceStepMatrix_isStochastic :
    IsStochasticMatrix lazyDifferenceStepMatrix := by
  intro x
  -- Proof comment: each row sum is the total mass of the corresponding convolution-kernel row.
  calc
    ∑' y : ℤ, lazyDifferenceStepMatrix x y =
        discreteMatrixKernel lazyDifferenceStepMatrix x Set.univ := by
          rw [← discreteMatrixKernel_univ lazyDifferenceStepMatrix x]
    _ = dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure x Set.univ := by
      rw [lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel]
    _ = 1 := by
      simp

/-- Helper for Example 18.7: the free lazy difference kernel is translation invariant. -/
lemma lazyDifferenceStepMatrix_isTranslationInvariant :
    IsTranslationInvariantStepMatrix lazyDifferenceStepMatrix := by
  intro x y
  -- Proof comment: the convolution-kernel row depends only on the increment `y - x`.
  change dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure x ({y} : Set ℤ) =
    dirac_convolution_kernel lazyDifferenceStepPMF.toMeasure 0 ({y - x} : Set ℤ)
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton y)]
  have hpreimage : (fun z : ℤ ↦ x + z) ⁻¹' ({y} : Set ℤ) = {y - x} := by
    ext z
    simp
    omega
  rw [hpreimage]
  rw [dirac_convolution_kernel_apply, Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (y - x))]
  simp

/-- Helper for Example 18.7: the free lazy difference step law has finite first moment and zero
drift. -/
lemma lazyDifferenceStepPMF_integrable_mean_zero :
    Integrable (fun z : ℤ ↦ (z : ℝ)) lazyDifferenceStepPMF.toMeasure ∧
      ∫ z, (z : ℝ) ∂lazyDifferenceStepPMF.toMeasure = 0 := by
  let μ : Measure ℤ := lazyNearestNeighborStepPMF.toMeasure
  let ν : Measure (ℤ × ℤ) := μ.prod μ
  let A : Set ℤ := {z | |z| ≤ 1}
  let B : Set (ℤ × ℤ) := {s | |s.1| ≤ 1 ∧ |s.2| ≤ 1}
  let f : ℤ × ℤ → ℝ := fun s ↦ ((s.1 - s.2 : ℤ) : ℝ)
  have hAcompl_zero : μ Aᶜ = 0 := by
    -- Proof comment: each coordinate step law is supported on `{-1, 0, 1}`.
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF)
      (show MeasurableSet Aᶜ from MeasurableSet.of_discrete)]
    refine ENNReal.tsum_eq_zero.2 ?_
    intro z
    by_cases hz : |z| ≤ 1
    · simp [A, hz]
    · simp [A, hz, lazyNearestNeighborStepPMF_apply]
  have hBcompl_subset :
      Bᶜ ⊆ (Aᶜ ×ˢ (Set.univ : Set ℤ)) ∪ ((Set.univ : Set ℤ) ×ˢ Aᶜ) := by
    intro s hs
    by_cases hs₁ : |s.1| ≤ 1
    · right
      simp [A, B, hs₁] at hs ⊢
      exact hs
    · left
      simp [A, B, hs₁]
  have hBcompl_zero : ν Bᶜ = 0 := by
    have hfst_zero : ν (Aᶜ ×ˢ (Set.univ : Set ℤ)) = 0 := by
      rw [Measure.prod_prod, hAcompl_zero]
      simp [μ, ν]
    have hsnd_zero : ν ((Set.univ : Set ℤ) ×ˢ Aᶜ) = 0 := by
      rw [Measure.prod_prod, hAcompl_zero]
      simp [μ, ν]
    refine le_antisymm ?_ bot_le
    calc
      ν Bᶜ ≤ ν ((Aᶜ ×ˢ (Set.univ : Set ℤ)) ∪ ((Set.univ : Set ℤ) ×ˢ Aᶜ)) := by
            exact measure_mono hBcompl_subset
      _ ≤ ν (Aᶜ ×ˢ (Set.univ : Set ℤ)) + ν ((Set.univ : Set ℤ) ×ˢ Aᶜ) := by
            exact measure_union_le _ _
      _ = 0 := by rw [hfst_zero, hsnd_zero, zero_add]
  have hB_ae : ∀ᵐ s ∂ν, s ∈ B := by
    filter_upwards [compl_mem_ae_iff.2 hBcompl_zero] with s hs
    simpa using hs
  let g : ℤ × ℤ → ℝ := fun s ↦ if s ∈ B then f s else 0
  have hg_integrable : Integrable g ν := by
    -- Proof comment: on the nine-point support, the difference observable is bounded by `2`.
    refine (integrable_const (2 : ℝ)).mono'
      (Measurable.of_discrete.aestronglyMeasurable) <|
      Filter.Eventually.of_forall fun s => by
        by_cases hs : s ∈ B
        · have hs₁ : |s.1| ≤ 1 := hs.1
          have hs₂ : |s.2| ≤ 1 := hs.2
          have hs₁' : |(s.1 : ℝ)| ≤ 1 := by
            exact_mod_cast hs₁
          have hs₂' : |(s.2 : ℝ)| ≤ 1 := by
            exact_mod_cast hs₂
          have hbound : |((s.1 : ℝ) - s.2)| ≤ 2 := by
            calc
              |((s.1 : ℝ) - s.2)| = |(s.1 : ℝ) + (-(s.2 : ℝ))| := by ring_nf
              _ ≤ |(s.1 : ℝ)| + |-(s.2 : ℝ)| := abs_add_le _ _
              _ = |(s.1 : ℝ)| + |(s.2 : ℝ)| := by simp
              _ ≤ 2 := by linarith
          simpa [g, f, hs, Real.norm_eq_abs] using hbound
        · simp [g, hs]
  have hfg_ae : f =ᵐ[ν] g := by
    filter_upwards [hB_ae] with s hs
    simp [g, hs]
  have hf_integrable : Integrable f ν :=
    hg_integrable.congr hfg_ae.symm
  have hmap :
      lazyDifferenceStepPMF.toMeasure = Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν := by
    simp [lazyDifferenceStepPMF, μ, ν, Measure.toPMF_toMeasure]
  have h_map_integrable :
      Integrable (fun z : ℤ ↦ (z : ℝ))
        (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν) := by
    have hcomp_eq :
        ((fun z : ℤ ↦ (z : ℝ)) ∘ fun s : ℤ × ℤ ↦ s.1 - s.2) = f := by
      funext s
      simp [f, Function.comp]
    have hcomp_integrable :
        Integrable (((fun z : ℤ ↦ (z : ℝ)) ∘ fun s : ℤ × ℤ ↦ s.1 - s.2)) ν := by
      rw [hcomp_eq]
      exact hf_integrable
    exact
      (integrable_map_measure
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable (fun z : ℤ ↦ (z : ℝ))
            (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν))
        (by fun_prop : AEMeasurable (fun s : ℤ × ℤ ↦ s.1 - s.2) ν)).2 hcomp_integrable
  refine ⟨by simpa [hmap] using h_map_integrable, ?_⟩
  have hswap_map : Measure.map Prod.swap ν = ν := by
    simpa [ν] using (Measure.prod_swap (μ := μ) (ν := μ))
  have hswap_neg : ∀ s : ℤ × ℤ, f s.swap = -f s := by
    intro s
    dsimp [f]
    have h : s.2 - s.1 = -(s.1 - s.2 : ℤ) := by
      omega
    exact_mod_cast h
  have hsymm :
      ∫ s, f s ∂ν = ∫ s, f s.swap ∂ν := by
    calc
      ∫ s, f s ∂ν = ∫ s, f s ∂Measure.map Prod.swap ν := by rw [hswap_map]
      _ = ∫ s, f (Prod.swap s) ∂ν := by
            rw [MeasureTheory.integral_map
              (by fun_prop : AEMeasurable Prod.swap ν)
              (Measurable.of_discrete.aestronglyMeasurable :
                AEStronglyMeasurable f (Measure.map Prod.swap ν))]
  have hzero_pair : ∫ s, f s ∂ν = 0 := by
    have hEq : ∫ s, f s ∂ν = -∫ s, f s ∂ν := by
      calc
        ∫ s, f s ∂ν = ∫ s, f s.swap ∂ν := hsymm
        _ = ∫ s, -f s ∂ν := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun s ↦ hswap_neg s
        _ = -∫ s, f s ∂ν := by rw [integral_neg]
    linarith
  -- Proof comment: the mapped difference law inherits integrability from the bounded product
  -- support, and the mean vanishes because swapping the two coordinates negates the difference
  -- while preserving the symmetric product law.
  rw [hmap]
  calc
    ∫ z, (z : ℝ) ∂Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν =
        ∫ s, ((s.1 - s.2 : ℤ) : ℝ) ∂ν := by
          rw [MeasureTheory.integral_map
            (by fun_prop : AEMeasurable (fun s : ℤ × ℤ ↦ s.1 - s.2) ν)
            (Measurable.of_discrete.aestronglyMeasurable :
              AEStronglyMeasurable (fun z : ℤ ↦ (z : ℝ))
                (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) ν))]
    _ = 0 := by simpa [f] using hzero_pair

/-- Helper for Example 18.7: absorbing a step matrix at `0` freezes the state `0` and leaves all
other rows unchanged. -/
def absorbAtZeroIntegerStepMatrix (q : ℤ → ℤ → ℝ≥0∞) : ℤ → ℤ → ℝ≥0∞ :=
  fun z w ↦ if z = 0 then if w = 0 then 1 else 0 else q z w

/-- Helper for Example 18.7: the absorbed-at-zero integer matrix has the Dirac row at `0`. -/
lemma absorbAtZeroIntegerStepMatrix_apply_zero
    (q : ℤ → ℤ → ℝ≥0∞) (w : ℤ) :
    absorbAtZeroIntegerStepMatrix q 0 w = if w = 0 then 1 else 0 := by
  -- Proof comment: the absorbing row is built into the definition.
  simp [absorbAtZeroIntegerStepMatrix]

/-- Helper for Example 18.7: away from `0`, the absorbed-at-zero integer matrix agrees with the
original step matrix. -/
lemma absorbAtZeroIntegerStepMatrix_apply_of_ne
    (q : ℤ → ℤ → ℝ≥0∞) {z w : ℤ} (hz : z ≠ 0) :
    absorbAtZeroIntegerStepMatrix q z w = q z w := by
  -- Proof comment: every nonzero row is copied verbatim from the original matrix.
  simp [absorbAtZeroIntegerStepMatrix, hz]

/-- Helper for Example 18.7: the absorbed-at-zero integer matrix stays stochastic when the
original step matrix is stochastic. -/
lemma absorbAtZeroIntegerStepMatrix_isStochastic
    (q : ℤ → ℤ → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    IsStochasticMatrix (absorbAtZeroIntegerStepMatrix q) := by
  intro z
  by_cases hz : z = 0
  · subst hz
    -- Proof comment: the absorbing row has exactly one nonzero entry.
    rw [tsum_eq_single (0 : ℤ)]
    · simp [absorbAtZeroIntegerStepMatrix]
    · intro w hw
      simp [absorbAtZeroIntegerStepMatrix, hw]
  · -- Proof comment: every nonzero row is unchanged, so stochasticity transfers directly.
    simp [absorbAtZeroIntegerStepMatrix, hz, hq z]

/-- Helper for Example 18.7: the endpoint-refined bounded zero-avoidance event for a free
integer walk. -/
def avoidZeroUntilWithEndpoint {Ωq : Type*} [MeasurableSpace Ωq]
    (Xq : ℕ → Ωq → ℤ) (n : ℕ) (w : ℤ) : Set Ωq :=
  -- Proof comment: this records both the prescribed endpoint `Xq n = w` and avoidance of `0`
  -- up to time `n`.
  {ω | Xq n ω = w ∧ ∀ m ≤ n, Xq m ω ≠ 0}

/-- Helper for Example 18.7: bounded zero-avoidance with a fixed endpoint is measurable with
respect to the time-`n` history filtration. -/
lemma avoidZeroUntilWithEndpoint_measurableSet
    {Ωq : Type*} [MeasurableSpace Ωq] {Xq : ℕ → Ωq → ℤ}
    (_hXq : ∀ n : ℕ, Measurable (Xq n)) (n : ℕ) (w : ℤ) :
    MeasurableSet[generatedFiltrationSpace Xq n] (avoidZeroUntilWithEndpoint Xq n w) := by
  have hState :
      MeasurableSet[generatedFiltrationSpace Xq n] {ω | Xq n ω = w} := by
    have hXqn : Measurable[generatedFiltrationSpace Xq n] (Xq n) := by
      exact Measurable.of_comap_le <| present_le_generatedHistory (X := Xq) n
    rw [show ({ω | Xq n ω = w} : Set Ωq) = Xq n ⁻¹' ({w} : Set ℤ) by
      ext ω
      simp]
    exact hXqn (measurableSet_singleton w)
  have hAvoid :
      MeasurableSet[generatedFiltrationSpace Xq n] {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
    have hrepr :
        {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
          ⋂ m : ℕ, if m ≤ n then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hXqm : Measurable[generatedFiltrationSpace Xq n] (Xq m) := by
        exact Measurable.of_comap_le <|
          le_iSup_of_le m <| le_iSup_of_le hm le_rfl
      have hZero :
          MeasurableSet[generatedFiltrationSpace Xq n] {ω : Ωq | Xq m ω = (0 : ℤ)} := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact hXqm (measurableSet_singleton (0 : ℤ))
      have hNonzero :
          MeasurableSet[generatedFiltrationSpace Xq n] {ω : Ωq | Xq m ω ≠ (0 : ℤ)} := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hrepr :
      avoidZeroUntilWithEndpoint Xq n w =
        {ω | Xq n ω = w} ∩ {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
    ext ω
    simp [avoidZeroUntilWithEndpoint]
  -- Proof comment: both the endpoint condition and the bounded avoidance condition are already
  -- determined by the time-`n` history.
  rw [hrepr]
  exact hState.inter hAvoid

/-- Helper for Example 18.7: bounded zero-avoidance with endpoint `0` is impossible. -/
lemma avoidZeroUntilWithEndpoint_eq_empty_of_zero
    {Ωq : Type*} [MeasurableSpace Ωq] {Xq : ℕ → Ωq → ℤ}
    (n : ℕ) :
    avoidZeroUntilWithEndpoint Xq n 0 = (∅ : Set Ωq) := by
  ext ω
  constructor
  · intro hω
    exact False.elim <| (hω.2 n le_rfl) hω.1
  · simp [avoidZeroUntilWithEndpoint]

/-- Helper for Example 18.7: bounded zero-avoidance with nonzero endpoint equals the
corresponding absorbed singleton mass. -/
theorem freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ℝ≥0∞}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q))] :
    ∀ n : ℕ, ∀ z : ℤ, ∀ {w : ℤ}, w ≠ 0 →
      (Pq z : Measure Ωq) (avoidZeroUntilWithEndpoint Xq n w) =
        ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) ^ n) z)
          ({w} : Set ℤ) := by
  let κAbs : Kernel ℤ ℤ := discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  intro n
  induction n with
  | zero =>
      intro z w hw
      have hset : avoidZeroUntilWithEndpoint Xq 0 w = {ω | Xq 0 ω = w} := by
        -- Proof comment: at time `0`, the endpoint condition already forces zero avoidance.
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro m hm
          have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
          subst hm0
          intro hzero
          exact hw (hω.symm.trans hzero)
      rw [hset]
      rw [show ({ω | Xq 0 ω = w} : Set Ωq) = Xq 0 ⁻¹' ({w} : Set ℤ) by
        ext ω
        simp]
      rw [← Measure.map_apply (hqreal.measurable_process 0) (measurableSet_singleton w)]
      rw [hqreal.transition_eq z 0]
      simp
  | succ n ih =>
      intro z w hw
      let μ : Measure Ωq := (Pq z : Measure Ωq)
      have hUnion :
          avoidZeroUntilWithEndpoint Xq (n + 1) w =
            ⋃ c : ℤ,
              avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w} := by
            ext ω
            constructor
            · intro hω
              refine Set.mem_iUnion.2 ⟨Xq n ω, ?_⟩
              refine ⟨?_, hω.1⟩
              refine ⟨rfl, ?_⟩
              intro m hm
              exact hω.2 m (Nat.le_trans hm (Nat.le_succ _))
            · intro hω
              rcases Set.mem_iUnion.1 hω with ⟨c, hcω⟩
              refine ⟨hcω.2, ?_⟩
              intro m hm
              rcases Nat.eq_or_lt_of_le hm with rfl | hm_lt
              · intro hzero
                exact hw (hcω.2.symm.trans hzero)
              · exact hcω.1.2 m (Nat.le_of_lt_succ hm_lt)
      have hPairwise :
          Pairwise fun c d : ℤ ↦
            Disjoint
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w})
              (avoidZeroUntilWithEndpoint Xq n d ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c d hcd
            refine Set.disjoint_left.2 ?_
            intro ω hc hd
            apply hcd
            exact hc.1.1.symm.trans hd.1.1
      have hMeas :
          ∀ c : ℤ,
            MeasurableSet
              (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
            intro c
            have hAvoid_hist :
                MeasurableSet[generatedFiltrationSpace Xq n]
                  (avoidZeroUntilWithEndpoint Xq n c) :=
              avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
            have hAvoid :
                MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
              exact (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                hAvoid_hist
            have hState :
                MeasurableSet ({ω | Xq (n + 1) ω = w} : Set Ωq) := by
              rw [show ({ω | Xq (n + 1) ω = w} : Set Ωq) =
                  Xq (n + 1) ⁻¹' ({w} : Set ℤ) by
                ext ω
                simp]
              exact (hqreal.measurable_process (n + 1)) (measurableSet_singleton w)
            exact hAvoid.inter hState
      -- Proof comment: decompose by the time-`n` endpoint, factor each history slice through the
      -- free one-step row, and replace that row by the absorbed row away from `0`.
      calc
        μ (avoidZeroUntilWithEndpoint Xq (n + 1) w) =
            ∑' c : ℤ,
              μ (avoidZeroUntilWithEndpoint Xq n c ∩ {ω | Xq (n + 1) ω = w}) := by
                rw [hUnion]
                exact MeasureTheory.measure_iUnion hPairwise hMeas
        _ =
            ∑' c : ℤ,
              (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) c
                  ({w} : Set ℤ)) *
                ((κAbs ^ n) z) ({c} : Set ℤ) := by
                  refine tsum_congr fun c ↦ ?_
                  by_cases hc : c ≠ 0
                  · have hAvoid_meas :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidZeroUntilWithEndpoint Xq n c) :=
                      avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n c
                    have hAvoid_meas_ambient :
                        MeasurableSet (avoidZeroUntilWithEndpoint Xq n c) := by
                      exact
                        (generatedHistory_le_ambient Xq hqreal.measurable_process n) _
                          hAvoid_meas
                    have hAvoid_measFiltration :
                        MeasurableSet[generatedFiltrationSpace Xq n]
                          (avoidZeroUntilWithEndpoint Xq n c) := hAvoid_meas
                    have hAvoid_state :
                        ∀ ⦃ω : Ωq⦄, ω ∈ avoidZeroUntilWithEndpoint Xq n c → Xq n ω = c := by
                      intro ω hω
                      exact hω.1
                    rw [measureInter_eq_mul_stepMass_of_stateEvent
                      (q := q) (P := Pq) (X := Xq) z c w n
                      (avoidZeroUntilWithEndpoint Xq n c)
                      hAvoid_meas_ambient hAvoid_measFiltration hAvoid_state]
                    rw [ih z hc, discreteMatrixKernel_apply_singleton,
                      discreteMatrixKernel_apply_singleton]
                    simpa [κAbs, absorbAtZeroIntegerStepMatrix, hc]
                  · have hczero : c = 0 := by simpa using hc
                    subst c
                    have hrow_zero :
                        discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) 0
                          ({w} : Set ℤ) = 0 := by
                      rw [discreteMatrixKernel_apply_singleton,
                        absorbAtZeroIntegerStepMatrix_apply_zero]
                      simp [hw]
                    rw [avoidZeroUntilWithEndpoint_eq_empty_of_zero (Xq := Xq) n]
                    rw [hrow_zero]
                    simp
        _ = ((κAbs ^ (n + 1)) z) ({w} : Set ℤ) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n z (measurableSet_singleton w)]
              rw [MeasureTheory.lintegral_countable']

/-- Helper for Example 18.7: the nonzero mass of the absorbed difference walk is exactly the
bounded zero-avoidance probability of the free difference walk. -/
theorem absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ℝ≥0∞}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    [IsMarkovKernel (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q))]
    (z : ℤ) (n : ℕ) :
    ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q) ^ n) z)
        {w : ℤ | w ≠ 0} =
      (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0} := by
  let κAbs : Kernel ℤ ℤ := discreteMatrixKernel (absorbAtZeroIntegerStepMatrix q)
  let offDiag : Set ℤ := {w : ℤ | w ≠ 0}
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let hqreal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hMass :
      ((κAbs ^ n) z) offDiag =
        ∑' w : {u : ℤ // u ∈ offDiag},
          ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := by
    calc
      ((κAbs ^ n) z) offDiag =
          ∑' w : ℤ,
            offDiag.indicator
              (fun w ↦ ((κAbs ^ n) z) ({w} : Set ℤ)) w := by
                simpa using
                  (Measure.tsum_indicator_apply_singleton ((κAbs ^ n) z) offDiag
                    (show MeasurableSet offDiag from MeasurableSet.of_discrete)).symm
      _ =
          ∑' w : {u : ℤ // u ∈ offDiag},
            ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := by
              rw [← tsum_subtype offDiag
                (fun w : ℤ ↦ ((κAbs ^ n) z) ({w} : Set ℤ))]
  have hUnion :
      {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ⋃ w : {u : ℤ // u ∈ offDiag}, avoidZeroUntilWithEndpoint Xq n w := by
      ext ω
      constructor
      · intro hω
        refine Set.mem_iUnion.2 ⟨⟨Xq n ω, hω n le_rfl⟩, ?_⟩
        exact ⟨rfl, hω⟩
      · intro hω
        rcases Set.mem_iUnion.1 hω with ⟨w, hw⟩
        exact hw.2
  have hAvoid :
      μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} =
        ∑' w : {u : ℤ // u ∈ offDiag},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
    have hPairwise :
        Pairwise fun w₁ w₂ : {u : ℤ // u ∈ offDiag} ↦
          Disjoint
            (avoidZeroUntilWithEndpoint Xq n (w₁ : ℤ))
            (avoidZeroUntilWithEndpoint Xq n (w₂ : ℤ)) := by
          intro w₁ w₂ hw
          refine Set.disjoint_left.2 ?_
          intro ω h₁ h₂
          apply hw
          exact Subtype.ext <| h₁.1.symm.trans h₂.1
    have hMeas :
        ∀ w : {u : ℤ // u ∈ offDiag},
          MeasurableSet (avoidZeroUntilWithEndpoint Xq n (w : ℤ)) := by
          intro w
          have hAvoid_hist :
              MeasurableSet[generatedFiltrationSpace Xq n]
                (avoidZeroUntilWithEndpoint Xq n (w : ℤ)) :=
            avoidZeroUntilWithEndpoint_measurableSet hqreal.measurable_process n (w : ℤ)
          exact
            (generatedHistory_le_ambient Xq hqreal.measurable_process n) _ hAvoid_hist
    rw [hUnion]
    exact MeasureTheory.measure_iUnion hPairwise hMeas
  -- Proof comment: decompose the absorbed nonzero mass into singleton endpoints and match each
  -- singleton mass with the corresponding bounded free zero-avoidance endpoint event.
  calc
    ((κAbs ^ n) z) offDiag =
        ∑' w : {u : ℤ // u ∈ offDiag},
          ((κAbs ^ n) z) ({(w : ℤ)} : Set ℤ) := hMass
    _ =
        ∑' w : {u : ℤ // u ∈ offDiag},
          μ (avoidZeroUntilWithEndpoint Xq n w) := by
            refine tsum_congr fun w ↦ ?_
            symm
            simpa [μ, offDiag] using
              freeAvoidZeroEndpointProb_eq_absorbedEndpointMass
                (Pq := Pq) (Xq := Xq) n z (w := (w : ℤ)) w.2
    _ = μ {ω | ∀ m ≤ n, Xq m ω ≠ 0} := hAvoid.symm

/-- Helper for Example 18.7: if the free walk hits `0` almost surely from every start, then the
bounded zero-avoidance probabilities converge to `0`. -/
theorem freeAvoidZeroProb_tendsto_zero_of_hitsZero_eq_one
    {Ωq : Type*} [MeasurableSpace Ωq]
    {q : ℤ → ℤ → ℝ≥0∞}
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq]
    (hHit : ∀ z : ℤ, (F[Pq, Xq]) z 0 = 1) (z : ℤ) :
    Tendsto
      (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0})
      atTop (nhds 0) := by
  let μ : Measure Ωq := (Pq z : Measure Ωq)
  let avoidUpTo : ℕ → Set Ωq := fun n ↦ {ω | ∀ m ≤ n, Xq m ω ≠ 0}
  let noHit : Set Ωq := {ω | ∀ m : ℕ, Xq m ω ≠ 0}
  let noPositiveHit : Set Ωq := {ω | ∀ m : ℕ, 0 < m → Xq m ω ≠ 0}
  let hitZero : Set Ωq := {ω | ∃ m : ℕ, 0 < m ∧ Xq m ω = 0}
  let hReal :
      IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel q ^ n) Pq Xq := inferInstance
  have hAvoid_meas : ∀ n : ℕ, MeasurableSet (avoidUpTo n) := by
    intro n
    have hrepr :
        avoidUpTo n = ⋂ m : ℕ, if m ≤ n then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [avoidUpTo]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : m ≤ n
    · have hZero : MeasurableSet ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : ℤ))
      have hNonzero : MeasurableSet ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hNoPositiveHit_meas : MeasurableSet noPositiveHit := by
    have hrepr :
        noPositiveHit = ⋂ m : ℕ, if 0 < m then {ω | Xq m ω ≠ 0} else Set.univ := by
      ext ω
      simp [noPositiveHit]
    rw [hrepr]
    refine MeasurableSet.iInter fun m ↦ ?_
    by_cases hm : 0 < m
    · have hZero : MeasurableSet ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq) =
            Xq m ⁻¹' ({0} : Set ℤ) by
          ext ω
          simp]
        exact (hReal.measurable_process m) (measurableSet_singleton (0 : ℤ))
      have hNonzero : MeasurableSet ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) := by
        rw [show ({ω : Ωq | Xq m ω ≠ (0 : ℤ)} : Set Ωq) =
            ({ω : Ωq | Xq m ω = (0 : ℤ)} : Set Ωq)ᶜ by
          ext ω
          simp]
        exact hZero.compl
      simpa [hm] using hNonzero
    · simp [hm]
  have hAntitone : Antitone avoidUpTo := by
    intro n m hnm ω hω k hk
    exact hω k (le_trans hk hnm)
  have hInter : (⋂ n : ℕ, avoidUpTo n) = noHit := by
    ext ω
    constructor
    · intro hω m
      exact (Set.mem_iInter.1 hω) m m le_rfl
    · intro hω
      refine Set.mem_iInter.2 ?_
      intro n
      exact fun m _ ↦ hω m
  have hHit_compl : hitZero = noPositiveHitᶜ := by
    ext ω
    simp [hitZero, noPositiveHit]
  have hNoHit_subset : noHit ⊆ noPositiveHit := by
    intro ω hω m hm
    exact hω m
  have hAvoid_tendsto :
      Tendsto (fun n ↦ μ (avoidUpTo n)) atTop (nhds (μ (⋂ n : ℕ, avoidUpTo n))) := by
    exact
      tendsto_measure_iInter_atTop
        (μ := μ)
        (s := avoidUpTo)
        (fun n ↦ (hAvoid_meas n).nullMeasurableSet)
        hAntitone
        ⟨0, by finiteness⟩
  have hHit_real : μ.real hitZero = 1 := by
    simpa [μ, hitZero, everHitsProbability_def] using hHit z
  have hNoPositiveHit_real : μ.real noPositiveHit = 0 := by
    have hsum :
        μ.real noPositiveHit + μ.real hitZero = μ.real Set.univ := by
      rw [hHit_compl]
      simpa using measureReal_add_measureReal_compl (μ := μ) hNoPositiveHit_meas
    have huniv : μ.real Set.univ = 1 := by
      simp [μ]
    linarith
  have hNoPositiveHit_zero : μ noPositiveHit = 0 := by
    exact (measureReal_eq_zero_iff (μ := μ) (s := noPositiveHit)).1 hNoPositiveHit_real
  have hInter_zero : μ (⋂ n : ℕ, avoidUpTo n) = 0 := by
    rw [hInter]
    exact le_antisymm
      (le_trans (measure_mono hNoHit_subset) hNoPositiveHit_zero.le)
      bot_le
  -- Proof comment: continuity from above reduces the bounded avoidance events to the infinite
  -- no-hit event, and the almost-sure hit hypothesis makes that limit event null.
  simpa [μ, hInter_zero] using hAvoid_tendsto

/-- Helper for Example 18.7: off the diagonal, an independent-coalescent row is the product of
the two one-step rows. -/
lemma coalescentRow_eq_prod_of_ne
    {x y : ℤ} (hxy : x ≠ y) :
    discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) (x, y) =
      (discreteMatrixKernel lazyNearestNeighborTransitionMatrix x).prod
        (discreteMatrixKernel lazyNearestNeighborTransitionMatrix y) := by
  refine Measure.ext_of_singleton ?_
  intro b
  rcases b with ⟨z, w⟩
  have hsingleton :
      ({((z, w) : ℤ × ℤ)} : Set (ℤ × ℤ)) =
        ({z} : Set ℤ) ×ˢ ({w} : Set ℤ) := by
    ext s
    simp
  -- Proof comment: compare the two rows on singleton rectangles and unfold the off-diagonal
  -- branch of `independentCoalescentMatrix`.
  rw [discreteMatrixKernel_apply_singleton, hsingleton]
  rw [Measure.prod_prod]
  rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
  rw [independentCoalescentMatrix_apply_of_ne (p := lazyNearestNeighborTransitionMatrix) hxy]

/-- Helper for Example 18.7: subtracting the coordinates of the product row yields the free lazy
difference kernel at the current displacement. -/
lemma productPairDifferenceRow_eq_lazyDifferenceKernel
    (x y : ℤ) :
    Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
      ((discreteMatrixKernel lazyNearestNeighborTransitionMatrix x).prod
        (discreteMatrixKernel lazyNearestNeighborTransitionMatrix y)) =
      discreteMatrixKernel lazyDifferenceStepMatrix (x - y) := by
  let μ : Measure ℤ := lazyNearestNeighborStepPMF.toMeasure
  have hx :
      discreteMatrixKernel lazyNearestNeighborTransitionMatrix x =
        Measure.map (fun z : ℤ ↦ x + z) μ := by
    -- Proof comment: the row at `x` is the translation of the common increment law.
    rw [lazyNearestNeighborTransitionMatrix_kernel_eq_diracConvolutionKernel,
      dirac_convolution_kernel_apply, Measure.dirac_conv]
  have hy :
      discreteMatrixKernel lazyNearestNeighborTransitionMatrix y =
        Measure.map (fun z : ℤ ↦ y + z) μ := by
    -- Proof comment: the same translation formula applies to the row at `y`.
    rw [lazyNearestNeighborTransitionMatrix_kernel_eq_diracConvolutionKernel,
      dirac_convolution_kernel_apply, Measure.dirac_conv]
  have hcomp₁ :
      (fun s : ℤ × ℤ ↦ s.1 - s.2) ∘
          Prod.map (fun z : ℤ ↦ x + z) (fun z : ℤ ↦ y + z) =
        fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2) := by
    funext s
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hcomp₂ :
      (fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2)) =
        (fun z : ℤ ↦ (x - y) + z) ∘ (fun s : ℤ × ℤ ↦ s.1 - s.2) := by
    rfl
  rw [hx, hy]
  calc
    Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
        ((Measure.map (fun z : ℤ ↦ x + z) μ).prod
          (Measure.map (fun z : ℤ ↦ y + z) μ)) =
      Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
        ((μ.prod μ).map
          (Prod.map (fun z : ℤ ↦ x + z) (fun z : ℤ ↦ y + z))) := by
            rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    _ =
        Measure.map (fun s : ℤ × ℤ ↦ (x - y) + (s.1 - s.2)) (μ.prod μ) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          simp [hcomp₁]
    _ =
        Measure.map (fun z : ℤ ↦ (x - y) + z)
          (Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2) (μ.prod μ)) := by
            rw [hcomp₂]
            rw [← Measure.map_map (μ := μ.prod μ) (f := fun s : ℤ × ℤ ↦ s.1 - s.2)
              (g := fun z : ℤ ↦ (x - y) + z) (by fun_prop) (by fun_prop)]
    _ =
        Measure.map (fun z : ℤ ↦ (x - y) + z)
          lazyDifferenceStepPMF.toMeasure := by
            simp [lazyDifferenceStepPMF, μ]
    _ = discreteMatrixKernel lazyDifferenceStepMatrix (x - y) := by
          rw [lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel,
            dirac_convolution_kernel_apply, Measure.dirac_conv]

/-- Helper for Example 18.7: subtracting the coordinates of one coalescent step gives the
absorbed lazy difference kernel. -/
lemma lazyNearestNeighborDifferenceRow_eq_absorbedDifferenceKernel
    (x y : ℤ) :
    Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
      (discreteMatrixKernel
        (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) (x, y)) =
      discreteMatrixKernel
        (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) (x - y) := by
  by_cases hxy : x = y
  · subst hxy
    refine Measure.ext_of_singleton ?_
    intro w
    by_cases hw : w = 0
    · subst hw
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
      have hpreimage :
          (fun s : ℤ × ℤ ↦ s.1 - s.2) ⁻¹' ({0} : Set ℤ) =
            {s : ℤ × ℤ | s.1 = s.2} := by
        ext s
        simp [sub_eq_zero]
      rw [hpreimage]
      have hOff :
          discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
            (x, x) {s : ℤ × ℤ | s.1 ≠ s.2} = 0 :=
        coalescentDiagonal_offDiagonalMass_eq_zero
          (p := lazyNearestNeighborTransitionMatrix)
          lazyNearestNeighborTransitionMatrix_isStochastic x
      have hDiag :
          discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
            (x, x) {s : ℤ × ℤ | s.1 = s.2} = 1 := by
        have hstochastic :
            IsStochasticMatrix
              (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) := by
          exact
            independentCoalescentMatrix_isStochasticMatrix
              (p := lazyNearestNeighborTransitionMatrix)
              lazyNearestNeighborTransitionMatrix_isStochastic
        have hcompl_zero :
            discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
              (x, x) ({s : ℤ × ℤ | s.1 = s.2}ᶜ) = 0 := by
          simpa [Set.compl_setOf, not_not] using hOff
        calc
          discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
              (x, x) {s : ℤ × ℤ | s.1 = s.2}
              =
          discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
              (x, x) Set.univ := by
                exact measure_of_measure_compl_eq_zero (μ := discreteMatrixKernel
                  (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) (x, x))
                  hcompl_zero
          _ = 1 := by
                simpa [discreteMatrixKernel_univ] using hstochastic (x, x)
      calc
        discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
            (x, x) {s : ℤ × ℤ | s.1 = s.2}
            = 1 := hDiag
        _ = discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) 0
              ({0} : Set ℤ) := by
                rw [discreteMatrixKernel_apply_singleton, absorbAtZeroIntegerStepMatrix_apply_zero]
                simp
        _ = discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) (x - x)
              ({0} : Set ℤ) := by
                simp
    · have hsubset :
          (fun s : ℤ × ℤ ↦ s.1 - s.2) ⁻¹' ({w} : Set ℤ) ⊆
            {s : ℤ × ℤ | s.1 ≠ s.2} := by
        intro s hs
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hs
        have hne : s.1 - s.2 ≠ 0 := by
          rwa [hs]
        exact fun hEq ↦ hne (sub_eq_zero.mpr hEq)
      have hOff :
          discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
            (x, x) {s : ℤ × ℤ | s.1 ≠ s.2} = 0 :=
        coalescentDiagonal_offDiagonalMass_eq_zero
          (p := lazyNearestNeighborTransitionMatrix)
          lazyNearestNeighborTransitionMatrix_isStochastic x
      have hright :
          discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) (x - x)
            ({w} : Set ℤ) = 0 := by
        simpa [sub_self, hw] using
          (show
            discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) 0
              ({w} : Set ℤ) = 0 by
                rw [discreteMatrixKernel_apply_singleton,
                  absorbAtZeroIntegerStepMatrix_apply_zero]
                simp [hw])
      have hleft :
          Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
              (discreteMatrixKernel
                (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) (x, x))
              ({w} : Set ℤ) = 0 := by
        refine le_antisymm ?_ bot_le
        calc
          Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
              (discreteMatrixKernel
                (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) (x, x))
              ({w} : Set ℤ)
              =
            discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
              (x, x) ((fun s : ℤ × ℤ ↦ s.1 - s.2) ⁻¹' ({w} : Set ℤ)) := by
                rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
          _ ≤ discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
                (x, x) {s : ℤ × ℤ | s.1 ≠ s.2} := by
                  exact measure_mono hsubset
          _ = 0 := hOff
      rw [hleft, hright]
  · -- Proof comment: off the diagonal, the coalescent row factorizes, and subtracting the two
    -- coordinates recovers the free lazy difference kernel, which matches the absorbed kernel
    -- away from zero.
    rw [coalescentRow_eq_prod_of_ne hxy, productPairDifferenceRow_eq_lazyDifferenceKernel]
    have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hrow :
        discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) (x - y) =
          discreteMatrixKernel lazyDifferenceStepMatrix (x - y) := by
      refine Measure.ext_of_singleton ?_
      intro w
      rw [discreteMatrixKernel_apply_singleton, discreteMatrixKernel_apply_singleton]
      rw [absorbAtZeroIntegerStepMatrix_apply_of_ne (q := lazyDifferenceStepMatrix) hdiff]
    exact hrow.symm

/-- Helper for Example 18.7: every realization of the lazy nearest-neighbor coalescent kernel is
already a Markov coupling of the two coordinate chains. -/
theorem lazyNearestNeighborIndependentCoalescent_isMarkovCoupling :
    IsMarkovCoupling lazyNearestNeighborTransitionMatrix P Z := by
  -- Proof comment: Exercise 18.2.2 already packages the coordinate-chain argument for every
  -- independent coalescent realization.
  exact
    independentCoalescentChain_isMarkovCoupling
      (p := lazyNearestNeighborTransitionMatrix) (P := P) (Z := Z)

/-- Helper for Example 18.7: the free lazy difference step law gives positive mass to `-1`. -/
lemma lazyDifferenceStepMass_negOne_pos :
    0 < lazyDifferenceStepPMF.toMeasure ({(-1 : ℤ)} : Set ℤ) := by
  let μ : Measure ℤ := lazyNearestNeighborStepPMF.toMeasure
  let νprod : Measure (ℤ × ℤ) := μ.prod μ
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hpair_pos :
      0 < νprod ({(0, 1)} : Set (ℤ × ℤ)) := by
    rw [productMeasure_apply_singleton_pair]
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF) (measurableSet_singleton 0)]
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF) (measurableSet_singleton 1)]
    norm_num [lazyNearestNeighborStepPMF_apply]
  have hsubset :
      ({(0, 1)} : Set (ℤ × ℤ)) ⊆ diff ⁻¹' ({(-1 : ℤ)} : Set ℤ) := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    simp [diff, hs]
  have hmap_pos :
      0 < Measure.map diff νprod ({(-1 : ℤ)} : Set ℤ) := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (-1 : ℤ))]
    exact lt_of_lt_of_le hpair_pos (measure_mono hsubset)
  simpa [lazyDifferenceStepPMF, μ, νprod, diff, Measure.toPMF_toMeasure] using hmap_pos

/-- Helper for Example 18.7: the free lazy difference step law gives positive mass to `1`. -/
lemma lazyDifferenceStepMass_posOne_pos :
    0 < lazyDifferenceStepPMF.toMeasure ({(1 : ℤ)} : Set ℤ) := by
  let μ : Measure ℤ := lazyNearestNeighborStepPMF.toMeasure
  let νprod : Measure (ℤ × ℤ) := μ.prod μ
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hpair_pos :
      0 < νprod ({(1, 0)} : Set (ℤ × ℤ)) := by
    rw [productMeasure_apply_singleton_pair]
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF) (measurableSet_singleton 1)]
    rw [PMF.toMeasure_apply (p := lazyNearestNeighborStepPMF) (measurableSet_singleton 0)]
    norm_num [lazyNearestNeighborStepPMF_apply]
  have hsubset :
      ({(1, 0)} : Set (ℤ × ℤ)) ⊆ diff ⁻¹' ({(1 : ℤ)} : Set ℤ) := by
    intro s hs
    simp only [Set.mem_singleton_iff] at hs
    simp [diff, hs]
  have hmap_pos :
      0 < Measure.map diff νprod ({(1 : ℤ)} : Set ℤ) := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (1 : ℤ))]
    exact lt_of_lt_of_le hpair_pos (measure_mono hsubset)
  simpa [lazyDifferenceStepPMF, μ, νprod, diff, Measure.toPMF_toMeasure] using hmap_pos

/-- Helper for Example 18.7: every free-difference row has positive mass to move one step left. -/
lemma lazyDifferenceKernel_stepLeft_pos (t : ℤ) :
    0 < discreteMatrixKernel lazyDifferenceStepMatrix t ({t - 1} : Set ℤ) := by
  -- Proof comment: translate the common increment law and use the positive `-1` increment mass.
  rw [lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel, dirac_convolution_kernel_apply,
    Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (t - 1))]
  have hpreimage :
      (fun z : ℤ ↦ t + z) ⁻¹' ({t - 1} : Set ℤ) = {(-1 : ℤ)} := by
    ext z
    simp
    omega
  rw [hpreimage]
  exact lazyDifferenceStepMass_negOne_pos

/-- Helper for Example 18.7: every free-difference row has positive mass to move one step right. -/
lemma lazyDifferenceKernel_stepRight_pos (t : ℤ) :
    0 < discreteMatrixKernel lazyDifferenceStepMatrix t ({t + 1} : Set ℤ) := by
  -- Proof comment: translate the common increment law and use the positive `1` increment mass.
  rw [lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel, dirac_convolution_kernel_apply,
    Measure.dirac_conv]
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (t + 1))]
  have hpreimage :
      (fun z : ℤ ↦ t + z) ⁻¹' ({t + 1} : Set ℤ) = ({(1 : ℤ)} : Set ℤ) := by
    ext z
    simp
  rw [hpreimage]
  exact lazyDifferenceStepMass_posOne_pos

/-- Helper for Example 18.7: every positive displacement reaches `0` by repeated left moves with
positive probability under the free lazy difference kernel. -/
lemma lazyDifferenceKernel_reachesZeroFromNat :
    ∀ n : ℕ, 0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (n + 1)) (n + 1 : ℤ)
      ({0} : Set ℤ) := by
  let κ : Kernel ℤ ℤ := discreteMatrixKernel lazyDifferenceStepMatrix
  intro n
  induction n with
  | zero =>
      simpa [κ, pow_one] using lazyDifferenceKernel_stepLeft_pos 1
  | succ n ih =>
      have hprev : (n + 2 : ℤ) - 1 = (n + 1 : ℤ) := by
        omega
      have hleft_step :
          0 < κ (n + 2 : ℤ) ({((n + 2 : ℤ) - 1)} : Set ℤ) := by
        simpa [κ] using lazyDifferenceKernel_stepLeft_pos (n + 2)
      have hleft :
          0 < κ (n + 2 : ℤ) ({(n + 1 : ℤ)} : Set ℤ) := by
        simpa [hprev] using hleft_step
      have htail :
          0 < (κ ^ (n + 1)) (n + 1 : ℤ) ({0} : Set ℤ) := by
        simpa [κ] using ih
      have hcomp :
          0 < (((κ ^ (n + 1)) ∘ₖ κ) (n + 2 : ℤ)) ({0} : Set ℤ) :=
        compSingletonMass_pos_of_posSingletonMass hleft htail
      have happ :
          (((κ ^ (n + 1)) ∘ₖ κ) (n + 2 : ℤ)) ({0} : Set ℤ) =
            (κ ^ (n + 2)) (n + 2 : ℤ) ({0} : Set ℤ) := by
        change (((κ ^ n * κ) * κ) (n + 2 : ℤ)) ({0} : Set ℤ) =
          (κ ^ (n + 2)) (n + 2 : ℤ) ({0} : Set ℤ)
        simpa [pow_succ] using
          congrArg (fun ξ : Kernel ℤ ℤ ↦ ξ (n + 2 : ℤ) ({0} : Set ℤ))
            (mul_assoc (κ ^ n) κ κ)
      have hgoal : 0 < (κ ^ (n + 2)) (n + 2 : ℤ) ({0} : Set ℤ) := by
        rw [← happ]
        exact hcomp
      have hpow : n + 2 = n + 1 + 1 := by omega
      have hx : (n + 2 : ℤ) = (n + 1 : ℤ) + 1 := by omega
      simpa [κ, hpow, hx] using hgoal

/-- Helper for Example 18.7: every negative displacement reaches `0` by repeated right moves with
positive probability under the free lazy difference kernel. -/
lemma lazyDifferenceKernel_reachesZeroFromNegNat :
    ∀ n : ℕ, 0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (n + 1))
      (-((n + 1 : ℕ) : ℤ)) ({0} : Set ℤ) := by
  let κ : Kernel ℤ ℤ := discreteMatrixKernel lazyDifferenceStepMatrix
  intro n
  induction n with
  | zero =>
      simpa [κ, pow_one] using lazyDifferenceKernel_stepRight_pos (-1)
  | succ n ih =>
      have hnext :
          (-((n + 2 : ℕ) : ℤ)) + 1 = -((n + 1 : ℕ) : ℤ) := by
        omega
      have hright_step :
          0 < κ (-((n + 2 : ℕ) : ℤ)) ({(-((n + 2 : ℕ) : ℤ) + 1)} : Set ℤ) := by
        simpa [κ] using lazyDifferenceKernel_stepRight_pos (-((n + 2 : ℕ) : ℤ))
      have hright :
          0 < κ (-((n + 2 : ℕ) : ℤ)) ({(-((n + 1 : ℕ) : ℤ))} : Set ℤ) := by
        rw [hnext] at hright_step
        simpa using hright_step
      have htail :
          0 < (κ ^ (n + 1)) (-((n + 1 : ℕ) : ℤ)) ({0} : Set ℤ) := by
        simpa [κ] using ih
      have hcomp :
          0 < (((κ ^ (n + 1)) ∘ₖ κ) (-((n + 2 : ℕ) : ℤ))) ({0} : Set ℤ) :=
        compSingletonMass_pos_of_posSingletonMass hright htail
      have happ :
          (((κ ^ (n + 1)) ∘ₖ κ) (-((n + 2 : ℕ) : ℤ))) ({0} : Set ℤ) =
            (κ ^ (n + 2)) (-((n + 2 : ℕ) : ℤ)) ({0} : Set ℤ) := by
        change (((κ ^ n * κ) * κ) (-((n + 2 : ℕ) : ℤ))) ({0} : Set ℤ) =
          (κ ^ (n + 2)) (-((n + 2 : ℕ) : ℤ)) ({0} : Set ℤ)
        simpa [pow_succ] using
          congrArg (fun ξ : Kernel ℤ ℤ ↦ ξ (-((n + 2 : ℕ) : ℤ)) ({0} : Set ℤ))
            (mul_assoc (κ ^ n) κ κ)
      have hgoal :
          0 < (κ ^ (n + 2)) (-((n + 2 : ℕ) : ℤ)) ({0} : Set ℤ) := by
        rw [← happ]
        exact hcomp
      have hpow : n + 2 = n + 1 + 1 := by omega
      have hx : (-((n + 2 : ℕ) : ℤ)) = -1 + (-1 + -↑n) := by
        omega
      simpa [κ, hpow, hx] using hgoal

/-- Helper for Example 18.7: every realization of the free lazy difference walk hits `0` almost
surely from every start. -/
theorem lazyDifferenceHitsZero_eq_one
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n) Pq Xq] :
    ∀ z : ℤ, (F[Pq, Xq]) z 0 = 1 := by
  let ν : ProbabilityMeasure ℤ := ⟨lazyDifferenceStepPMF.toMeasure, inferInstance⟩
  have hconv :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) Pq Xq := by
    simpa [ν, lazyDifferenceStepMatrix_kernel_eq_diracConvolutionKernel] using
      (inferInstance :
        IsMarkovProcessRealization
          (fun n ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n) Pq Xq)
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure ℤ) ^ n) Pq Xq := hconv
  have hν_moment := lazyDifferenceStepPMF_integrable_mean_zero
  have hrec : IsRecurrentMarkovChain Pq Xq := by
    simpa [ν] using
      OneDimensionalWalk.integerRandomWalk_recurrent_of_integrable_mean_zero
        (ν := ν) (P := Pq) (X := Xq) hν_moment.1 hν_moment.2
  intro z
  by_cases hz0 : z = 0
  · subst hz0
    simpa [IsRecurrentState] using hrec 0
  · have hzrec : IsRecurrentState Pq Xq z := hrec z
    let hproc : IsStochasticProcess Xq := fun n ↦ (inferInstance :
      IsMarkovProcessRealization
        (fun n ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n) Pq Xq).measurable_process n
    have hhit_pos : 0 < (F[Pq, Xq]) z 0 := by
      rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
      · have hz_nonneg : 0 ≤ -z := by omega
        let n : ℕ := Int.toNat (-z)
        have hn_eq : (n : ℤ) = -z := by
          simpa [n] using Int.toNat_of_nonneg hz_nonneg
        cases hn : n with
        | zero =>
            exfalso
            have hz_eq : z = 0 := by
              have hnegz : (-z : ℤ) = 0 := by
                simpa [n, hn] using hn_eq
              omega
            exact hz0 hz_eq
        | succ m =>
            have hz_eq : z = -((m + 1 : ℕ) : ℤ) := by
              have hnegz : ((m + 1 : ℕ) : ℤ) = -z := by
                simpa [n, hn] using hn_eq
              omega
            have hstep :
                0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (m + 1)) z
                  ({0} : Set ℤ) := by
              have hbase :
                  0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (m + 1))
                    (-((m + 1 : ℕ) : ℤ)) ({0} : Set ℤ) :=
                lazyDifferenceKernel_reachesZeroFromNegNat m
              simpa [hz_eq] using hbase
            have hgreen : 0 < (G[Pq, Xq; 1]) z 0 :=
              greenFunctionFrom_one_pos_of_posStepMass
                (κ := fun n : ℕ ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n)
                Pq Xq (Nat.succ_pos m) hstep
            exact
              (greenFunctionFrom_one_pos_iff_everHitsProbability_pos Pq Xq hproc z 0).1 hgreen
      · simp at hz0
      · have hz_nonneg : 0 ≤ z := le_of_lt hzpos
        let n : ℕ := Int.toNat z
        have hn_eq : (n : ℤ) = z := by
          simpa [n] using Int.toNat_of_nonneg hz_nonneg
        cases hn : n with
        | zero =>
            exfalso
            have hz_eq : z = 0 := by
              simpa [n, hn] using hn_eq.symm
            exact hz0 hz_eq
        | succ m =>
            have hz_eq : z = (m + 1 : ℤ) := by
              simpa [n, hn] using hn_eq.symm
            have hstep :
                0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (m + 1)) z
                  ({0} : Set ℤ) := by
              have hbase :
                  0 < (discreteMatrixKernel lazyDifferenceStepMatrix ^ (m + 1))
                    (m + 1 : ℤ) ({0} : Set ℤ) :=
                lazyDifferenceKernel_reachesZeroFromNat m
              simpa [hz_eq] using hbase
            have hgreen : 0 < (G[Pq, Xq; 1]) z 0 :=
              greenFunctionFrom_one_pos_of_posStepMass
                (κ := fun n : ℕ ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n)
                Pq Xq (Nat.succ_pos m) hstep
            exact
              (greenFunctionFrom_one_pos_iff_everHitsProbability_pos Pq Xq hproc z 0).1 hgreen
    -- Proof comment: recurrence of the starting state upgrades any positive hit probability to an
    -- almost-sure hit probability.
    exact
      everHitsProbability_eq_one_of_isRecurrentState_of_everHitsProbability_pos
        (P := Pq) (X := Xq)
        (κ := fun n : ℕ ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n)
        hzrec hhit_pos

/-- Helper for Example 18.7: the absorbed lazy difference walk loses all nonzero mass once the
free lazy difference walk hits `0` almost surely. -/
theorem absorbedLazyDifferenceNonzeroMass_tendsto_zero_of_hitsZero_eq_one
    {Ωq : Type*} [MeasurableSpace Ωq]
    {Pq : ℤ → ProbabilityMeasure Ωq}
    {Xq : ℕ → Ωq → ℤ}
    [IsMarkovProcessRealization
      (fun n ↦ discreteMatrixKernel lazyDifferenceStepMatrix ^ n) Pq Xq]
    [IsMarkovKernel
      (discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix))]
    (hHit : ∀ z : ℤ, (F[Pq, Xq]) z 0 = 1) (z : ℤ) :
    Tendsto
      (fun n ↦
        ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) ^ n) z)
          {w : ℤ | w ≠ 0})
      atTop (nhds 0) := by
  have hAvoid :
      Tendsto
        (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0})
        atTop (nhds 0) :=
    freeAvoidZeroProb_tendsto_zero_of_hitsZero_eq_one
      (q := lazyDifferenceStepMatrix) (Pq := Pq) (Xq := Xq) hHit z
  have hfun :
      (fun n ↦
        ((discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) ^ n) z)
          {w : ℤ | w ≠ 0}) =
        (fun n ↦ (Pq z : Measure Ωq) {ω | ∀ m ≤ n, Xq m ω ≠ 0}) := by
    funext n
    exact
      absorbedDifferenceNonzeroMass_eq_freeAvoidZeroProb
        (q := lazyDifferenceStepMatrix) (Pq := Pq) (Xq := Xq) z n
  -- Proof comment: compare the absorbed nonzero mass with the bounded avoid-zero probability.
  simpa [hfun] using hAvoid

/-- Helper for Example 18.7: subtracting the coalescent `n`-step law yields the absorbed lazy
difference `n`-step law at displacement `a - b`. -/
lemma coalescentDifferenceKernelPow_eq_absorbedDifferenceKernelPow
    (n : ℕ) (a b : ℤ) :
    Measure.map (fun s : ℤ × ℤ ↦ s.1 - s.2)
      ((discreteMatrixKernel
        (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) ^ n) (a, b)) =
      (discreteMatrixKernel
        (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) ^ n) (a - b) := by
  let κPair : Kernel (ℤ × ℤ) (ℤ × ℤ) :=
    discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
  let κAbs : Kernel ℤ ℤ :=
    discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix)
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  induction n with
  | zero =>
      refine Measure.ext_of_singleton ?_
      intro w
      rw [Measure.map_apply hdiff_meas (measurableSet_singleton w)]
      simp only [pow_zero]
      change Measure.dirac (a, b) (diff ⁻¹' ({w} : Set ℤ)) =
        Measure.dirac (a - b) ({w} : Set ℤ)
      by_cases h : a - b = w
      · simp [Measure.dirac_apply', diff, h]
      · simp [Measure.dirac_apply', diff, h]
  | succ n ih =>
      refine Measure.ext_of_singleton ?_
      intro w
      have hpreimage_meas :
          MeasurableSet (diff ⁻¹' ({w} : Set ℤ)) :=
        hdiff_meas (measurableSet_singleton w)
      calc
        Measure.map diff ((κPair ^ (n + 1)) (a, b)) ({w} : Set ℤ) =
            ((κPair ^ (n + 1)) (a, b)) (diff ⁻¹' ({w} : Set ℤ)) := by
              rw [Measure.map_apply hdiff_meas (measurableSet_singleton w)]
        _ =
            ∫⁻ s : ℤ × ℤ, (κPair s) (diff ⁻¹' ({w} : Set ℤ)) ∂((κPair ^ n) (a, b)) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κPair n (a, b) hpreimage_meas]
        _ =
            ∫⁻ s : ℤ × ℤ, Measure.map diff (κPair s) ({w} : Set ℤ) ∂((κPair ^ n) (a, b)) := by
              refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
              intro s
              symm
              exact Measure.map_apply hdiff_meas (measurableSet_singleton w)
        _ =
            ∫⁻ s : ℤ × ℤ, κAbs (diff s) ({w} : Set ℤ) ∂((κPair ^ n) (a, b)) := by
              refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
              intro s
              rcases s with ⟨c, d⟩
              have hrow : Measure.map diff (κPair (c, d)) = κAbs (c - d) := by
                simpa [κPair, κAbs, diff] using
                  lazyNearestNeighborDifferenceRow_eq_absorbedDifferenceKernel c d
              exact congrArg (fun μ : Measure ℤ ↦ μ ({w} : Set ℤ)) hrow
        _ =
            ∫⁻ z : ℤ, κAbs z ({w} : Set ℤ) ∂Measure.map diff ((κPair ^ n) (a, b)) := by
              symm
              exact
                MeasureTheory.lintegral_map'
                  (μ := ((κPair ^ n) (a, b)))
                  (f := fun z : ℤ ↦ κAbs z ({w} : Set ℤ))
                  (g := diff)
                  (Kernel.measurable_coe κAbs (measurableSet_singleton w)).aemeasurable
                  hdiff_meas.aemeasurable
        _ =
            ∫⁻ z : ℤ, κAbs z ({w} : Set ℤ) ∂((κAbs ^ n) (a - b)) := by
              rw [ih]
        _ = (κAbs ^ (n + 1)) (a - b) ({w} : Set ℤ) := by
              rw [Kernel.pow_succ_apply_eq_lintegral κAbs n (a - b) (measurableSet_singleton w)]

/-- Helper for Example 18.7: the only remaining probabilistic input is that the lazy difference
walk is recurrent and forces the coalescent disagreement tail to vanish. -/
lemma lazyNearestNeighborIndependentCoalescent_tailDisagreement_tendsto_zero :
    ∀ x y : ℤ,
      Tendsto
        (fun n ↦
          (P (x, y) : Measure Ω) (⋃ m ≥ n, {ω | (Z m ω).1 ≠ (Z m ω).2}))
        atTop (nhds 0) := by
  -- Route correction: the earlier file tried to realize the absorbed difference process locally
  -- and broke across several owner APIs. This proof keeps the pair transport at the semigroup
  -- level: realize the free lazy difference walk once, show it hits `0` almost surely by
  -- recurrence plus explicit positive paths, then push the coalescent `n`-step law through
  -- subtraction and squeeze the tail disagreement by the current nonzero difference mass.
  let hrealization :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel
            (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) ^ n)
        P Z := inferInstance
  let κPair : Kernel (ℤ × ℤ) (ℤ × ℤ) :=
    discreteMatrixKernel (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix)
  let κq : Kernel ℤ ℤ := discreteMatrixKernel lazyDifferenceStepMatrix
  let κAbs : Kernel ℤ ℤ :=
    discreteMatrixKernel (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix)
  have hκq_stochastic : IsStochasticMatrix lazyDifferenceStepMatrix :=
    lazyDifferenceStepMatrix_isStochastic
  letI : IsMarkovKernel κq :=
    discreteMatrixKernel_isMarkovKernel lazyDifferenceStepMatrix hκq_stochastic
  have hκAbs_stochastic :
      IsStochasticMatrix (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) := by
    exact
      absorbAtZeroIntegerStepMatrix_isStochastic
        lazyDifferenceStepMatrix lazyDifferenceStepMatrix_isStochastic
  letI : IsMarkovKernel κAbs :=
    discreteMatrixKernel_isMarkovKernel
      (absorbAtZeroIntegerStepMatrix lazyDifferenceStepMatrix) hκAbs_stochastic
  let _ : IsProbabilityMeasure (κq 0) := inferInstance
  obtain ⟨Ωi, hΩi, Qq, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :=
    ProbabilityTheory.exists_iid (ULift.{0} ℕ) (κq 0)
  let Qprob : ProbabilityMeasure Ωi := ⟨Qq, hQ_prob⟩
  let Zq : ℕ → Ωi → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZq_meas : ∀ n : ℕ, Measurable (Zq n) := by
    intro n
    simpa [Zq] using hZ_meas ⟨n⟩
  have hZq_law : ∀ n : ℕ, HasLaw (Zq n) (κq 0) (Qprob : Measure Ωi) := by
    intro n
    simpa [Zq, Qprob] using hZ_law ⟨n⟩
  have hZq_indep : iIndepFun Zq (Qprob : Measure Ωi) := by
    simpa [Zq, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift.{0} ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  have hqreal :
      IsMarkovProcessRealization (fun n : ℕ ↦ κq ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Zq) := by
    exact
      productStartRandomWalk_isMarkovProcessRealization
        lazyDifferenceStepMatrix hκq_stochastic
        lazyDifferenceStepMatrix_isTranslationInvariant
        Qprob Zq hZq_meas hZq_indep <| by
          intro n
          simpa [κq] using hZq_law n
  letI :
      IsMarkovProcessRealization (fun n : ℕ ↦ κq ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Zq) := hqreal
  intro x y
  let offZero : Set ℤ := {w : ℤ | w ≠ 0}
  let diff : ℤ × ℤ → ℤ := fun s ↦ s.1 - s.2
  have hdiff_meas : Measurable diff := Measurable.of_discrete
  have hHit :
      ∀ z : ℤ,
        (F[productStartRandomWalkMeasure Qprob, productStartRandomWalk Zq]) z 0 = 1 :=
    lazyDifferenceHitsZero_eq_one
      (Pq := productStartRandomWalkMeasure Qprob)
      (Xq := productStartRandomWalk Zq)
  have hcurrent_tendsto :
      Tendsto
        (fun n ↦ (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2})
        atTop (nhds 0) := by
    have habsorbed_tendsto :
        Tendsto
          (fun n ↦ (κAbs ^ n) (x - y) offZero)
          atTop (nhds 0) := by
      simpa [κAbs, offZero] using
        absorbedLazyDifferenceNonzeroMass_tendsto_zero_of_hitsZero_eq_one
          (Pq := productStartRandomWalkMeasure Qprob)
          (Xq := productStartRandomWalk Zq) hHit (x - y)
    have hcurrent_fun :
        (fun n ↦ (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2}) =
          (fun n ↦ (κAbs ^ n) (x - y) offZero) := by
      funext n
      have hdiff_process_meas : Measurable (fun ω ↦ (Z n ω).1 - (Z n ω).2) :=
        hdiff_meas.comp (hrealization.measurable_process n)
      rw [integerPairDisagreementEvent_eq_differenceEvent (Z := Z) n]
      have hpreimage :
          {ω | (Z n ω).1 - (Z n ω).2 ≠ 0} =
            (fun ω ↦ (Z n ω).1 - (Z n ω).2) ⁻¹' offZero := by
        ext ω
        simp [offZero]
      rw [hpreimage, ← Measure.map_apply hdiff_process_meas
        (show MeasurableSet offZero from MeasurableSet.of_discrete)]
      have hmap :
          Measure.map (fun ω ↦ (Z n ω).1 - (Z n ω).2) (P (x, y) : Measure Ω) =
            Measure.map diff ((κPair ^ n) (x, y)) := by
        calc
          Measure.map (fun ω ↦ (Z n ω).1 - (Z n ω).2) (P (x, y) : Measure Ω) =
              Measure.map diff (Measure.map (Z n) (P (x, y) : Measure Ω)) := by
                symm
                simpa [diff, Function.comp] using
                  (Measure.map_map (μ := (P (x, y) : Measure Ω))
                    (f := Z n) (g := diff)
                    (hf := hrealization.measurable_process n) (hg := hdiff_meas))
          _ = Measure.map diff ((κPair ^ n) (x, y)) := by
                rw [hrealization.transition_eq (x, y) n]
      rw [hmap]
      simpa [κAbs, offZero] using
        congrArg (fun μ : Measure ℤ ↦ μ offZero)
          (coalescentDifferenceKernelPow_eq_absorbedDifferenceKernelPow n x y)
    -- Proof comment: current disagreement is exactly the absorbed difference nonzero mass,
    -- which equals bounded zero-avoidance for the free recurrent difference walk.
    simpa [hcurrent_fun] using habsorbed_tendsto
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hcurrent_tendsto (fun n ↦ zero_le _)
      (coalescentTailDisagreement_le_currentDisagreement
        (p := lazyNearestNeighborTransitionMatrix)
        lazyNearestNeighborTransitionMatrix_isStochastic x y)

/-- Example 18.7: every realization of the independent coalescent chain associated with the lazy
nearest-neighbor walk on `ℤ` is a successful Markov coupling for that walk. -/
theorem lazyNearestNeighborIndependentCoalescent_isSuccessfulMarkovCoupling :
    IsSuccessfulMarkovCoupling lazyNearestNeighborTransitionMatrix P Z := by
  refine
    { toIsMarkovCoupling :=
        lazyNearestNeighborIndependentCoalescent_isMarkovCoupling (P := P) (Z := Z)
      tail_disagreement_tendsto_zero := ?_ }
  -- Proof comment: once the tail-disagreement estimate is isolated, the final structure is just
  -- the Definition 18.5 packaging.
  exact lazyNearestNeighborIndependentCoalescent_tailDisagreement_tendsto_zero
    (P := P) (Z := Z)

end

end ProbabilityTheory

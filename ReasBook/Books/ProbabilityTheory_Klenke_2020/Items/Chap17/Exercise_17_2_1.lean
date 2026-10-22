/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Example_17_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v}

/-- The source-facing rowwise support data `Aₓ` contains every possible next state from `x` for
the transition matrix `p`. -/
def HasStepSupportWithin (p : E → E → ℝ≥0∞) (A : E → Set E) : Prop :=
  ∀ ⦃x y : E⦄, p x y ≠ 0 → y ∈ A x

/-- The source-facing rowwise support data `Aₓ` has size at most three. -/
def HasAtMostThreePointSet (A : E → Set E) : Prop :=
  ∀ x : E, ∃ a b c : E, ∀ ⦃y : E⦄, y ∈ A x → y = a ∨ y = b ∨ y = c

/-- Each row of the transition matrix has support of size at most three. This is the rowwise
source-facing finite-support hypothesis from the exercise. -/
def HasAtMostThreePointStepSupportAt (p : E → E → ℝ≥0∞) (x : E) : Prop :=
  ∃ a b c : E, ∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c

/-- Each row of the transition matrix has support of size at most three. -/
def HasAtMostThreePointStepSupport (p : E → E → ℝ≥0∞) : Prop :=
  ∀ x : E, HasAtMostThreePointStepSupportAt p x

/-- A fixed rowwise support container of size at most three yields the exercise's rowwise
three-point support hypothesis for the transition matrix `p`. -/
theorem HasAtMostThreePointSet.hasAtMostThreePointStepSupport
    {p : E → E → ℝ≥0∞} {A : E → Set E} (hA : HasAtMostThreePointSet A)
    (hpA : HasStepSupportWithin p A) :
    HasAtMostThreePointStepSupport p := by
  intro x
  rcases hA x with ⟨a, b, c, hAxc⟩
  refine ⟨a, b, c, ?_⟩
  intro y hy
  exact hAxc (hpA hy)

section ThreePointSupport

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
  {p : E → E → ℝ≥0∞}

private def transitionNextStateMean (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦ ∫ y, (y : ℝ) ∂ discreteMatrixKernel p x

private def transitionNextStateSecondMoment (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦ ∫ y, (y : ℝ) ^ (2 : ℕ) ∂ discreteMatrixKernel p x

/-- The one-step drift of the transition matrix `p`, expressed as the conditional mean of the
increment `X₁ - X₀` via the owner kernel `discreteMatrixKernel p`. -/
def transitionDrift (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦ transitionNextStateMean p x - (x : ℝ)

/-- The predictable square-variation increment of the transition matrix `p`, i.e. the conditional
variance of the next state, equivalently the centered conditional second moment of the increment
`X₁ - X₀`. -/
def transitionSquareVariationIncrement (p : E → E → ℝ≥0∞) : E → ℝ :=
  fun x ↦
    transitionNextStateSecondMoment p x - transitionNextStateMean p x ^ (2 : ℕ)

/-- The compensated process obtained by subtracting the accumulated drift from the real-valued
chain `X`, written using the owner partial-sum process on the drift observable `transitionDrift p`.
-/
def compensatedTransitionProcess (p : E → E → ℝ≥0∞) (X : ℕ → Ω → E) : ℕ → Ω → ℝ :=
  fun n ω ↦
    (X n ω : ℝ) - partialSum (fun n ↦ transitionDrift p ∘ X n) n ω

end ThreePointSupport

/-- The square-variation density from the Moran model in Example 17.22 and formula `(17.12)`,
written on the owner state space `Fin (N + 1)` via `moranFrequency`. -/
def moranSquareVariationDensity (N : ℕ+) : Fin (N + 1) → ℝ :=
  fun i ↦ ((2 : ℝ) / (N : ℝ) ^ (2 : ℕ)) * moranFrequency N i * (1 - moranFrequency N i)

section ProcessPastFiltration

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable {p : E → E → ℝ≥0∞}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

local notation "ℱ" => processFiltration X

/-- Helper for Exercise 17.2.1: a realized chain is adapted to its own process filtration. -/
private theorem adapted_processFiltration_of_realization
    (hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance) :
    Adapted (processFiltration X) X := by
  intro n
  -- Proof comment: the time-`n` coordinate belongs both to the ambient sigma-algebra and to the
  -- `n`th generator in the process filtration definition.
  refine measurable_iff_comap_le.2 ?_
  exact le_inf
    ((hReal.measurable_process n).comap_le)
    (le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl)

/-- Helper for Exercise 17.2.1: if every nonzero row entry of `p x` lies in a finite set `s`,
then the one-step row measure is almost surely supported on `s`. -/
private lemma ae_mem_of_rowSupportInFinset
    (x : E) (s : Finset E)
    (hrow : ∀ y : E, p x y ≠ 0 → y ∈ s) :
    ∀ᵐ y ∂ (discreteMatrixKernel p x), y ∈ s := by
  rw [ae_iff]
  change discreteMatrixKernel p x {y | y ∉ s} = 0
  -- Proof comment: every point outside `s` has zero matrix weight, so the bad set has zero row
  -- mass under the discrete kernel.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ <|
    show MeasurableSet {y : E | y ∉ s} from MeasurableSet.of_discrete]
  refine ENNReal.tsum_eq_zero.2 ?_
  intro y
  rw [Measure.smul_apply]
  by_cases hy : y ∈ s
  · have hy_not_mem : y ∉ {z : E | z ∉ s} := by
      simpa using hy
    rw [Measure.dirac_apply, Set.indicator_of_notMem hy_not_mem]
    simp
  · have hpxy : p x y = 0 := by
      by_contra hpxy
      exact hy (hrow y hpxy)
    rw [Measure.dirac_apply, Set.indicator_of_mem hy, Pi.one_apply]
    simp [hpxy]

/-- Helper for Exercise 17.2.1: on a time-`n` history event, the restricted law of `X (n + 1)`
is the discrete-kernel average of the restricted law of `X n`. -/
private lemma restrictMap_next_eq_discreteKernelComp_of_history
    (hp : IsStochasticMatrix p) (x : E) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[processFiltration X n] s) :
    ((P x : Measure Ω).restrict s).map (X (n + 1)) =
      (discreteMatrixKernel p) ∘ₘ (((P x : Measure Ω).restrict s).map (X n)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  have hX_meas : ∀ k : ℕ, Measurable (X k) := hReal.measurable_process
  have hs_meas : MeasurableSet s := hs.1
  have hs_generated : MeasurableSet[generatedFiltrationSpace X n] s := hs.2
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hX_meas k).comap_le
  refine Measure.ext fun A hA ↦ ?_
  have hleft_real :
      (((μ.restrict s).map (X (n + 1))).real A) =
        ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
    let B : Set Ω := X (n + 1) ⁻¹' A
    have hB_meas : MeasurableSet B := by
      simpa [B] using (hX_meas (n + 1)) hA
    have hIndicatorInt : Integrable (Set.indicator B (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hB_meas
    have hmarkov :
        μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
          fun ω ↦ ((discreteMatrixKernel p) (X n ω)).real A := by
      -- Proof comment: specialize the one-step Markov property to the event `A`.
      simpa [B, add_comm] using hReal.markov_property x (A := A) hA n 1
    have hmass :
        μ.real (s ∩ B) =
          ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
      calc
        μ.real (s ∩ B)
            = ∫ ω in s, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hs_generated,
                  ← MeasureTheory.integral_indicator hs_meas]
                simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
                  Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hs_meas.inter hB_meas)).symm
        _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    calc
      (((μ.restrict s).map (X (n + 1))).real A)
          = (μ.restrict s).real ((X (n + 1)) ⁻¹' A) := by
              simpa using MeasureTheory.map_measureReal_apply
                (μ := μ.restrict s) (f := X (n + 1)) (hX_meas (n + 1)) hA
      _ = μ.real (((X (n + 1)) ⁻¹' A) ∩ s) := by
            simpa [B] using
              (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := s) (t := B) hB_meas)
      _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
            simpa [B, Set.inter_comm] using hmass
  have hright_real :
      (((discreteMatrixKernel p) ∘ₘ ((μ.restrict s).map (X n))).real A) =
        ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
    let ν : Measure E := ((μ.restrict s).map (X n))
    have hkernel_int :
        Integrable (fun y : E ↦ ((discreteMatrixKernel p) y).real A) ν := by
      simpa [ν] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := ν) (κ := discreteMatrixKernel p) hA)
    have hkernel_nonneg :
        0 ≤ᵐ[ν] fun y : E ↦ ((discreteMatrixKernel p) y).real A :=
      Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
    have hcomp_real :
        (((discreteMatrixKernel p) ∘ₘ ν).real A) =
          ∫ y, ((discreteMatrixKernel p) y).real A ∂ν := by
      rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
        (ProbabilityTheory.Kernel.aemeasurable _)]
      have hlintegral :
          ∫⁻ y, ((discreteMatrixKernel p) y) A ∂ν =
            ENNReal.ofReal (∫ y, ((discreteMatrixKernel p) y).real A ∂ν) := by
        calc
          ∫⁻ y, ((discreteMatrixKernel p) y) A ∂ν
              = ∫⁻ y, ENNReal.ofReal (((discreteMatrixKernel p) y).real A) ∂ν := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with y
                  rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                  exact measure_ne_top _ _
          _ = ENNReal.ofReal (∫ y, ((discreteMatrixKernel p) y).real A ∂ν) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  hkernel_int hkernel_nonneg
      rw [hlintegral, ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae hkernel_nonneg
    have hmap_real :
        ∫ y, ((discreteMatrixKernel p) y).real A ∂ν =
          ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
      -- Proof comment: push the kernel mass function back through the restricted present-state
      -- law.
      change ∫ y, ((discreteMatrixKernel p) y).real A ∂((μ.restrict s).map (X n)) =
        ∫ ω, ((discreteMatrixKernel p) (X n ω)).real A ∂(μ.restrict s)
      rw [MeasureTheory.integral_map (hX_meas n).aemeasurable hkernel_int.aestronglyMeasurable]
    calc
      (((discreteMatrixKernel p) ∘ₘ ((μ.restrict s).map (X n))).real A)
          = ∫ y, ((discreteMatrixKernel p) y).real A ∂ν := by
              simpa [ν] using hcomp_real
      _ = ∫ ω in s, ((discreteMatrixKernel p) (X n ω)).real A ∂μ := by
            simpa [ν] using hmap_real
  have hleft_ne_top : (((μ.restrict s).map (X (n + 1))) A) ≠ ∞ := by
    finiteness
  have hright_ne_top :
      (((discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n)))) A) ≠ ∞ := by
    finiteness
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict s).map (X (n + 1))))
      (ν := (discreteMatrixKernel p) ∘ₘ (((μ.restrict s).map (X n))))
      (s := A) (t := A)).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Exercise 17.2.1: for every fixed start state `x`, the time-`n` state `X n` is
almost surely contained in a finite reachable set built from the three-point support hypothesis. -/
private theorem reachableStates_finite_ae
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p) (x : E)
    (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) :
    ∀ n : ℕ, ∃ s : Finset E, ∀ᵐ ω ∂ (P x : Measure Ω), X n ω ∈ s := by
  classical
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  intro n
  induction n with
  | zero =>
      refine ⟨{x}, ?_⟩
      have hSingleton :
          ∀ᵐ y ∂ Measure.dirac x, y ∈ ({x} : Finset E) := by
        simp
      have hSetMeas : MeasurableSet {y : E | y ∈ ({x} : Finset E)} := MeasurableSet.of_discrete
      -- Proof comment: the deterministic start law pushes the singleton support back to the
      -- underlying realization.
      have hMap :
          ∀ᵐ y ∂ (P x : Measure Ω).map (X 0), y ∈ ({x} : Finset E) := by
        rw [h_start]
        simpa using hSingleton
      exact (MeasureTheory.ae_map_iff (hReal.measurable_process 0).aemeasurable hSetMeas).1 hMap
  | succ n ih =>
      rcases ih with ⟨s, hsAE⟩
      let stepSupport : E → Finset E := fun y ↦
        let a := Classical.choose (h_support y)
        let hbc := Classical.choose_spec (h_support y)
        let b := Classical.choose hbc
        let hc := Classical.choose_spec hbc
        let c := Classical.choose hc
        {a, b, c}
      let t : Finset E :=
        s.biUnion stepSupport
      have hX_adapted : Adapted (processFiltration X) X :=
        adapted_processFiltration_of_realization (P := P) (X := X) (p := p)
      let B : Set Ω := {ω | X n ω ∈ s}
      have hB_meas : MeasurableSet[processFiltration X n] B := by
        -- Proof comment: the reachable-set event only depends on the present state `X n`.
        change MeasurableSet[processFiltration X n] ((X n) ⁻¹' {y : E | y ∈ s})
        simpa [B] using
          (hX_adapted n) (MeasurableSet.of_discrete : MeasurableSet {y : E | y ∈ s})
      have hμ_restrict : μ.restrict B = μ := Measure.restrict_eq_self_of_ae_mem hsAE
      have hXn_restrict :
          ∀ᵐ ω ∂ μ.restrict B, X n ω ∈ s := by
        refine (ae_restrict_iff' hB_meas.1).2 ?_
        exact Filter.Eventually.of_forall fun ω hω ↦ hω
      let ν : Measure E := ((μ.restrict B).map (X n))
      have hSetMeas : MeasurableSet {y : E | y ∈ s} := MeasurableSet.of_discrete
      have hν_support : ∀ᵐ y ∂ ν, y ∈ s := by
        exact (MeasureTheory.ae_map_iff (hReal.measurable_process n).aemeasurable hSetMeas).2
          hXn_restrict
      have hBad_zero :
          ((discreteMatrixKernel p) ∘ₘ ν) {y : E | y ∉ t} = 0 := by
        have hBad_meas : MeasurableSet {y : E | y ∉ t} := MeasurableSet.of_discrete
        rw [Measure.bind_apply hBad_meas (ProbabilityTheory.Kernel.aemeasurable _)]
        calc
          ∫⁻ y, discreteMatrixKernel p y {z : E | z ∉ t} ∂ν = ∫⁻ y, 0 ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards [hν_support] with y hy
            have hrow :
                ∀ z : E, p y z ≠ 0 → z ∈ t := by
              intro z hpz
              let a := Classical.choose (h_support y)
              let hbc := Classical.choose_spec (h_support y)
              let b := Classical.choose hbc
              let hc := Classical.choose_spec hbc
              let c := Classical.choose hc
              have hz : z = a ∨ z = b ∨ z = c := by
                exact (Classical.choose_spec hc) z hpz
              refine Finset.mem_biUnion.2 ?_
              refine ⟨y, hy, ?_⟩
              simp [stepSupport, a, hbc, b, hc, c, hz]
            have hrowAE : ∀ᵐ z ∂ discreteMatrixKernel p y, z ∈ t :=
              ae_mem_of_rowSupportInFinset (p := p) y t hrow
            have hrowZero : discreteMatrixKernel p y {z : E | z ∉ t} = 0 := by
              simpa using (ae_iff.1 hrowAE)
            exact hrowZero
          _ = 0 := by simp
      have hNext_map :
          ((μ.restrict B).map (X (n + 1))) = (discreteMatrixKernel p) ∘ₘ ν := by
        simpa [ν] using
          restrictMap_next_eq_discreteKernelComp_of_history
            (P := P) (X := X) (p := p) hp x n hB_meas
      have hNext_support_map :
          ∀ᵐ y ∂ ((μ.restrict B).map (X (n + 1))), y ∈ t := by
        rw [hNext_map, ae_iff]
        simpa using hBad_zero
      have hTMeas : MeasurableSet {y : E | y ∈ t} := MeasurableSet.of_discrete
      have hNext_support :
          ∀ᵐ ω ∂ μ.restrict B, X (n + 1) ω ∈ t := by
        exact
          (MeasureTheory.ae_map_iff (hReal.measurable_process (n + 1)).aemeasurable hTMeas).1
            hNext_support_map
      refine ⟨t, ?_⟩
      -- Proof comment: the previous reachable event has full mass, so the restricted next-step
      -- support statement upgrades back to the original start law.
      simpa [μ, B, hμ_restrict] using hNext_support

/-- Helper for Exercise 17.2.1: fixed-time sampled observables `g (X n)` are integrable because
the reachable state set at time `n` is finite under the deterministic start law. -/
private theorem integrable_comp_process_of_reachableStates
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (x : E) (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) (n : ℕ) (g : E → ℝ) :
    Integrable (fun ω ↦ g (X n ω)) (P x : Measure Ω) := by
  classical
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  rcases reachableStates_finite_ae (P := P) (X := X) (p := p) hp h_support x h_start n with
    ⟨s, hsAE⟩
  let valueRange : Set ℝ := Set.range fun y : {z // z ∈ s} ↦ g y.1
  have hValueRangeBounded : Bornology.IsBounded valueRange := by
    simpa [valueRange] using (Set.toFinite valueRange).isBounded
  obtain ⟨C, hC⟩ := hValueRangeBounded.exists_norm_le
  refine Integrable.mono' (integrable_const C)
    ((Measurable.of_discrete.comp (hReal.measurable_process n)).aestronglyMeasurable) ?_
  -- Proof comment: on the almost-surely finite reachable set, the sampled observable takes only
  -- finitely many values, hence is uniformly bounded.
  filter_upwards [hsAE] with ω hω
  exact hC (g (X n ω)) ⟨⟨X n ω, hω⟩, rfl⟩

/-- Helper for Exercise 17.2.1: fixed-time sampled observables are almost surely bounded by a
deterministic constant because the reachable state set is finite. -/
private theorem ae_norm_comp_process_le_of_reachableStates
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (x : E) (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) (n : ℕ) (g : E → ℝ) :
    ∃ C : ℝ, ∀ᵐ ω ∂ (P x : Measure Ω), ‖g (X n ω)‖ ≤ C := by
  classical
  rcases reachableStates_finite_ae (P := P) (X := X) (p := p) hp h_support x h_start n with
    ⟨s, hsAE⟩
  let valueRange : Set ℝ := Set.range fun y : {z // z ∈ s} ↦ g y.1
  have hValueRangeBounded : Bornology.IsBounded valueRange := by
    simpa [valueRange] using (Set.toFinite valueRange).isBounded
  obtain ⟨C, hC⟩ := hValueRangeBounded.exists_norm_le
  refine ⟨C, ?_⟩
  -- Proof comment: the sampled values stay inside the finite image of the reachable-state set.
  filter_upwards [hsAE] with ω hω
  exact hC (g (X n ω)) ⟨⟨X n ω, hω⟩, rfl⟩

/-- Helper for Exercise 17.2.1: conditioning the next state on the process history returns the
rowwise first moment of the transition matrix. -/
private theorem condExp_nextState_eq_transitionNextStateMean
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (x : E) (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) (n : ℕ) :
    (P x : Measure Ω)[fun ω ↦ (X (n + 1) ω : ℝ) | ℱ n] =ᵐ[(P x : Measure Ω)]
      fun ω ↦ transitionNextStateMean p (X n ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hX_adapted : Adapted ℱ X :=
    adapted_processFiltration_of_realization (P := P) (X := X) (p := p)
  have hNextInt :
      Integrable (fun ω ↦ (X (n + 1) ω : ℝ)) μ :=
    integrable_comp_process_of_reachableStates
      (P := P) (X := X) (p := p) hp h_support x h_start (n + 1) fun y ↦ (y : ℝ)
  have hMeanInt :
      Integrable (fun ω ↦ transitionNextStateMean p (X n ω)) μ :=
    integrable_comp_process_of_reachableStates
      (P := P) (X := X) (p := p) hp h_support x h_start n (transitionNextStateMean p)
  have hMeanMeas :
      AEStronglyMeasurable[ℱ n] (fun ω ↦ transitionNextStateMean p (X n ω)) μ := by
    exact
      (((Measurable.of_discrete : Measurable (transitionNextStateMean p)).comp
        (hX_adapted n)).aestronglyMeasurable)
  -- Proof comment: identify the conditional expectation by matching its set integrals on every
  -- history event and transporting the restricted next-step law through the discrete kernel.
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq ((processFiltration X).le n) hNextInt
      (fun (B : Set Ω) _ _ ↦ hMeanInt.integrableOn) (fun (B : Set Ω) hB _ ↦ ?_) hMeanMeas).symm
  let ν : Measure E := ((μ.restrict B).map (X n))
  have hNextMap :
      ((μ.restrict B).map (X (n + 1))) = (discreteMatrixKernel p) ∘ₘ ν := by
    simpa [ν] using
      restrictMap_next_eq_discreteKernelComp_of_history
        (P := P) (X := X) (p := p) hp x n hB
  have hNextRestrictInt :
      Integrable (fun y : E ↦ (y : ℝ)) (((μ.restrict B).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict B) (f := X (n + 1)) (g := fun y : E ↦ (y : ℝ))
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (hNextInt.restrict)
  have hCurrentMeanInt :
      Integrable (transitionNextStateMean p) ν := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict B) (f := X n) (g := transitionNextStateMean p)
        (Measurable.of_discrete.aestronglyMeasurable) (hReal.measurable_process n).aemeasurable).2 <|
        (hMeanInt.restrict)
  have hCurrentMeanMap :
      ∫ y, transitionNextStateMean p y ∂ν =
        ∫ ω in B, transitionNextStateMean p (X n ω) ∂μ := by
    change ∫ y, transitionNextStateMean p y ∂((μ.restrict B).map (X n)) =
      ∫ ω, transitionNextStateMean p (X n ω) ∂(μ.restrict B)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hCurrentMeanInt.aestronglyMeasurable]
  have hNextMapIntegral :
      ∫ y, (y : ℝ) ∂((μ.restrict B).map (X (n + 1))) =
        ∫ ω in B, (X (n + 1) ω : ℝ) ∂μ := by
    change ∫ y, (y : ℝ) ∂((μ.restrict B).map (X (n + 1))) =
      ∫ ω, (X (n + 1) ω : ℝ) ∂(μ.restrict B)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hNextRestrictInt.aestronglyMeasurable]
  have hCompInt :
      Integrable (fun y : E ↦ (y : ℝ)) ((discreteMatrixKernel p) ∘ₘ ν) := by
    simpa [ν] using (hNextMap ▸ hNextRestrictInt)
  calc
    ∫ ω in B, transitionNextStateMean p (X n ω) ∂μ
        = ∫ y, transitionNextStateMean p y ∂ν := hCurrentMeanMap.symm
    _ = ∫ y, ∫ z, (z : ℝ) ∂ discreteMatrixKernel p y ∂ν := by
          simp [transitionNextStateMean]
    _ = ∫ y, (y : ℝ) ∂((discreteMatrixKernel p) ∘ₘ ν) := by
          symm
          calc
            ∫ y, (y : ℝ) ∂((discreteMatrixKernel p) ∘ₘ ν)
                =
                  ∫ y, (y : ℝ) ∂(
                    (discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
                      rw [ProbabilityTheory.Kernel.comp_const,
                        ProbabilityTheory.Kernel.const_apply]
            _ = ∫ y, ∫ z, (z : ℝ) ∂ discreteMatrixKernel p y ∂ν := by
                  exact
                    ProbabilityTheory.Kernel.integral_comp
                      (η := discreteMatrixKernel p)
                      (κ := ProbabilityTheory.Kernel.const Unit ν) (a := ()) hCompInt
    _ = ∫ y, (y : ℝ) ∂((μ.restrict B).map (X (n + 1))) := by
          rw [hNextMap]
    _ = ∫ ω in B, (X (n + 1) ω : ℝ) ∂μ := hNextMapIntegral

/-- Helper for Exercise 17.2.1: conditioning the squared next state on the process history returns
the rowwise second moment of the transition matrix. -/
private theorem condExp_nextStateSq_eq_transitionNextStateSecondMoment
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (x : E) (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) (n : ℕ) :
    (P x : Measure Ω)[fun ω ↦ (X (n + 1) ω : ℝ) ^ (2 : ℕ) | ℱ n] =ᵐ[(P x : Measure Ω)]
      fun ω ↦ transitionNextStateSecondMoment p (X n ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let g : E → ℝ := fun y ↦ (y : ℝ) ^ (2 : ℕ)
  have hX_adapted : Adapted ℱ X :=
    adapted_processFiltration_of_realization (P := P) (X := X) (p := p)
  have hNextInt :
      Integrable (fun ω ↦ (X (n + 1) ω : ℝ) ^ (2 : ℕ)) μ :=
    integrable_comp_process_of_reachableStates
      (P := P) (X := X) (p := p) hp h_support x h_start (n + 1) g
  have hSecondInt :
      Integrable (fun ω ↦ transitionNextStateSecondMoment p (X n ω)) μ :=
    integrable_comp_process_of_reachableStates
      (P := P) (X := X) (p := p) hp h_support x h_start n
        (transitionNextStateSecondMoment p)
  have hSecondMeas :
      AEStronglyMeasurable[ℱ n] (fun ω ↦ transitionNextStateSecondMoment p (X n ω)) μ := by
    exact
      (((Measurable.of_discrete : Measurable (transitionNextStateSecondMoment p)).comp
        (hX_adapted n)).aestronglyMeasurable)
  -- Proof comment: the same restricted-law transport works for the squared identity observable.
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq ((processFiltration X).le n) hNextInt
      (fun (B : Set Ω) _ _ ↦ hSecondInt.integrableOn)
      (fun (B : Set Ω) hB _ ↦ ?_) hSecondMeas).symm
  let ν : Measure E := ((μ.restrict B).map (X n))
  have hNextMap :
      ((μ.restrict B).map (X (n + 1))) = (discreteMatrixKernel p) ∘ₘ ν := by
    simpa [ν] using
      restrictMap_next_eq_discreteKernelComp_of_history
        (P := P) (X := X) (p := p) hp x n hB
  have hNextRestrictInt : Integrable g (((μ.restrict B).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict B) (f := X (n + 1)) (g := g)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (hNextInt.restrict)
  have hCurrentSecondInt :
      Integrable (transitionNextStateSecondMoment p) ν := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict B) (f := X n) (g := transitionNextStateSecondMoment p)
        (Measurable.of_discrete.aestronglyMeasurable) (hReal.measurable_process n).aemeasurable).2 <|
        (hSecondInt.restrict)
  have hCurrentSecondMap :
      ∫ y, transitionNextStateSecondMoment p y ∂ν =
        ∫ ω in B, transitionNextStateSecondMoment p (X n ω) ∂μ := by
    change ∫ y, transitionNextStateSecondMoment p y ∂((μ.restrict B).map (X n)) =
      ∫ ω, transitionNextStateSecondMoment p (X n ω) ∂(μ.restrict B)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hCurrentSecondInt.aestronglyMeasurable]
  have hNextMapIntegral :
      ∫ y, g y ∂((μ.restrict B).map (X (n + 1))) =
        ∫ ω in B, (X (n + 1) ω : ℝ) ^ (2 : ℕ) ∂μ := by
    change ∫ y, g y ∂((μ.restrict B).map (X (n + 1))) =
      ∫ ω, (X (n + 1) ω : ℝ) ^ (2 : ℕ) ∂(μ.restrict B)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hNextRestrictInt.aestronglyMeasurable]
  have hCompInt : Integrable g ((discreteMatrixKernel p) ∘ₘ ν) := by
    simpa [ν] using (hNextMap ▸ hNextRestrictInt)
  calc
    ∫ ω in B, transitionNextStateSecondMoment p (X n ω) ∂μ
        = ∫ y, transitionNextStateSecondMoment p y ∂ν := hCurrentSecondMap.symm
    _ = ∫ y, ∫ z, (z : ℝ) ^ (2 : ℕ) ∂ discreteMatrixKernel p y ∂ν := by
          simp [transitionNextStateSecondMoment, g]
    _ = ∫ y, g y ∂((discreteMatrixKernel p) ∘ₘ ν) := by
          symm
          calc
            ∫ y, g y ∂((discreteMatrixKernel p) ∘ₘ ν)
                =
                  ∫ y, g y ∂(
                    (discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
                      rw [ProbabilityTheory.Kernel.comp_const,
                        ProbabilityTheory.Kernel.const_apply]
            _ = ∫ y, ∫ z, g z ∂ discreteMatrixKernel p y ∂ν := by
                  exact
                    ProbabilityTheory.Kernel.integral_comp
                      (η := discreteMatrixKernel p)
                      (κ := ProbabilityTheory.Kernel.const Unit ν) (a := ()) hCompInt
    _ = ∫ y, g y ∂((μ.restrict B).map (X (n + 1))) := by
          rw [hNextMap]
    _ = ∫ ω in B, (X (n + 1) ω : ℝ) ^ (2 : ℕ) ∂μ := hNextMapIntegral

/-- Helper for Exercise 17.2.1: finite partial sums belong to `L²` once each summand has an
integrable square. -/
private lemma partialSumMemLpTwoOfSquareIntegrableTerms
    {μ : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_sq_int : ∀ n, Integrable (fun ω ↦ (Y n ω) ^ (2 : ℕ)) μ) :
    ∀ n, MemLp (partialSum Y n) 2 μ := by
  intro n
  -- Proof comment: expand the partial sum over `Finset.range n` and sum the `L²` bounds for the
  -- individual terms.
  simpa [partialSum] using
    (MeasureTheory.memLp_finset_sum (Finset.range n) fun i _ ↦
      (MeasureTheory.memLp_two_iff_integrable_sq
        ((hY_meas i).stronglyMeasurable.aestronglyMeasurable)).2
        (hY_sq_int i))

/-- Helper for Exercise 17.2.1: the compensated increment is the next state minus the conditional
row mean. -/
private lemma compensatedTransitionProcess_increment_eq
    (p : E → E → ℝ≥0∞) (X : ℕ → Ω → E) (n : ℕ) :
    (fun ω ↦ compensatedTransitionProcess p X (n + 1) ω -
        compensatedTransitionProcess p X n ω) =
      fun ω ↦ (X (n + 1) ω : ℝ) - transitionNextStateMean p (X n ω) := by
  funext ω
  -- Proof comment: expanding the partial sums at times `n + 1` and `n` leaves exactly the new
  -- drift term, which is `transitionNextStateMean p (X n ω) - X n ω`.
  simp [compensatedTransitionProcess, transitionDrift, partialSum, Finset.sum_range_succ]
  ring

/-- Helper for Exercise 17.2.1: the compensated chain is square integrable at each fixed time
under the deterministic start law. -/
private lemma compensatedTransitionProcess_memLpTwo
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (x : E) (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) :
    ∀ n, MemLp (compensatedTransitionProcess p X n) 2 (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let driftTerms : ℕ → Ω → ℝ := fun n ↦ transitionDrift p ∘ X n
  have hXMemLp : ∀ n, MemLp (fun ω ↦ (X n ω : ℝ)) 2 μ := by
    intro n
    have hXsqInt :
        Integrable (fun ω ↦ (X n ω : ℝ) ^ (2 : ℕ)) μ :=
      integrable_comp_process_of_reachableStates
        (P := P) (X := X) (p := p) hp h_support x h_start n
        (fun y ↦ (y : ℝ) ^ (2 : ℕ))
    exact
      (MeasureTheory.memLp_two_iff_integrable_sq
        (((Measurable.of_discrete : Measurable (fun y : E ↦ (y : ℝ))).comp
          (hReal.measurable_process n)).stronglyMeasurable.aestronglyMeasurable)).2
        hXsqInt
  have hDriftTermsMeas : ∀ n, Measurable (driftTerms n) := by
    intro n
    simpa [driftTerms] using
      ((Measurable.of_discrete : Measurable (transitionDrift p)).comp
        (hReal.measurable_process n))
  have hDriftSqInt :
      ∀ n, Integrable (fun ω ↦ (driftTerms n ω) ^ (2 : ℕ)) μ := by
    intro n
    simpa [driftTerms] using
      integrable_comp_process_of_reachableStates
        (P := P) (X := X) (p := p) hp h_support x h_start n
        (fun y ↦ (transitionDrift p y) ^ (2 : ℕ))
  have hDriftPartialMemLp :
      ∀ n, MemLp (partialSum driftTerms n) 2 μ :=
    partialSumMemLpTwoOfSquareIntegrableTerms hDriftTermsMeas hDriftSqInt
  intro n
  -- Proof comment: subtract the `L²` drift partial sum from the `L²` state observable.
  simpa [μ, driftTerms, compensatedTransitionProcess] using
    (hXMemLp n).sub (hDriftPartialMemLp n)

/-
Proof sketch: apply the one-step Markov property with the drift function coming from the
three-point-support hypothesis, identify the conditional expectation of the next increment with the
rowwise first moment of `p`, and then use the centered second-moment formula to identify the
square variation density.
-/
/-- Exercise 17.2.1 (1): for a countable real-valued state space with at most three possible next
states from each point, subtracting the accumulated drift `d(X_k)` from the Markov chain produces
a martingale under the start law `P x` concentrated at `x`, and the square variation process of
that compensated chain is the accumulated canonical density coming from the three-point-support
hypothesis. -/
theorem compensatedTransitionProcess_martingale_and_squareVariation
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p) (x : E)
    (h_start : (P x : Measure Ω).map (X 0) = Measure.dirac x) :
    Martingale (compensatedTransitionProcess p X) ℱ (P x : Measure Ω) ∧
      IsSquareVariationProcess ℱ (P x : Measure Ω)
        (compensatedTransitionProcess p X)
        (partialSum (fun n ↦ transitionSquareVariationIncrement p ∘ X n)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let driftTerms : ℕ → Ω → ℝ := fun n ↦ transitionDrift p ∘ X n
  let density : ℕ → Ω → ℝ := fun n ↦ transitionSquareVariationIncrement p ∘ X n
  let driftPartial : ℕ → Ω → ℝ := partialSum driftTerms
  let A : ℕ → Ω → ℝ := partialSum density
  let M : ℕ → Ω → ℝ := compensatedTransitionProcess p X
  have hX_adapted : Adapted ℱ X :=
    adapted_processFiltration_of_realization (P := P) (X := X) (p := p)
  have hXStrong : ∀ n, StronglyMeasurable[ℱ n] (fun ω ↦ (X n ω : ℝ)) := by
    intro n
    exact
      (((Measurable.of_discrete : Measurable (fun y : E ↦ (y : ℝ))).comp
        (hX_adapted n)).stronglyMeasurable)
  have hDriftStrong : ∀ n, StronglyMeasurable[ℱ n] (driftTerms n) := by
    intro n
    exact
      (((Measurable.of_discrete : Measurable (transitionDrift p)).comp
        (hX_adapted n)).stronglyMeasurable)
  have hDensityStrong : ∀ n, StronglyMeasurable[ℱ n] (density n) := by
    intro n
    exact
      (((Measurable.of_discrete : Measurable (transitionSquareVariationIncrement p)).comp
        (hX_adapted n)).stronglyMeasurable)
  have hDriftTermsMeas : ∀ n, Measurable (driftTerms n) := by
    intro n
    simpa [driftTerms] using
      ((Measurable.of_discrete : Measurable (transitionDrift p)).comp
        (hReal.measurable_process n))
  have hDriftPartialStrong : ∀ n, StronglyMeasurable[ℱ n] (driftPartial n) := by
    intro n
    induction n with
    | zero =>
        simpa [driftPartial, partialSum] using
          (stronglyMeasurable_zero : StronglyMeasurable[ℱ 0] (0 : Ω → ℝ))
    | succ n ih =>
        have hStep : driftPartial (n + 1) = driftPartial n + driftTerms n := by
          funext ω
          simp [driftPartial, driftTerms, partialSum, Finset.sum_range_succ]
        rw [hStep]
        exact
          (ih.mono (Filtration.mono ℱ (Nat.le_succ n))).add
            ((hDriftStrong n).mono (Filtration.mono ℱ (Nat.le_succ n)))
  have hAStrong : ∀ n, StronglyMeasurable[ℱ n] (A n) := by
    intro n
    induction n with
    | zero =>
        simpa [A, partialSum] using
          (stronglyMeasurable_zero : StronglyMeasurable[ℱ 0] (0 : Ω → ℝ))
    | succ n ih =>
        have hStep : A (n + 1) = A n + density n := by
          funext ω
          simp [A, density, partialSum, Finset.sum_range_succ]
        rw [hStep]
        exact
          (ih.mono (Filtration.mono ℱ (Nat.le_succ n))).add
            ((hDensityStrong n).mono (Filtration.mono ℱ (Nat.le_succ n)))
  have hAAddOneStrong : ∀ n, StronglyMeasurable[ℱ n] (A (n + 1)) := by
    intro n
    have hStep : A (n + 1) = A n + density n := by
      funext ω
      simp [A, density, partialSum, Finset.sum_range_succ]
    rw [hStep]
    exact (hAStrong n).add (hDensityStrong n)
  have hA0Meas : Measurable[ℱ 0] (A 0) := by
    have hA0 : A 0 = fun _ : Ω ↦ (0 : ℝ) := by
      funext ω
      simp [A, partialSum]
    rw [hA0]
    exact measurable_const
  have hAPredictable : IsPredictable ℱ A := by
    refine MeasureTheory.isPredictable_of_measurable_add_one hA0Meas ?_
    · intro n
      exact (hAAddOneStrong n).measurable
  have hMad : StronglyAdapted ℱ M := by
    intro n
    -- Proof comment: the compensated chain is the present state minus the predictable drift sum,
    -- and both terms are measurable with respect to the current history.
    simpa [M, driftPartial, driftTerms, compensatedTransitionProcess] using
      (hXStrong n).sub (hDriftPartialStrong n)
  have hMint : ∀ n, Integrable (M n) μ := by
    intro n
    exact
      (compensatedTransitionProcess_memLpTwo
        (P := P) (X := X) (p := p) hp h_support x h_start n).integrable (by norm_num)
  have hCondZero :
      ∀ n, μ[fun ω ↦ M (n + 1) ω - M n ω | ℱ n] =ᵐ[μ] 0 := by
    intro n
    have hNextInt :
        Integrable (fun ω ↦ (X (n + 1) ω : ℝ)) μ :=
      integrable_comp_process_of_reachableStates
        (P := P) (X := X) (p := p) hp h_support x h_start (n + 1) fun y ↦ (y : ℝ)
    have hMeanInt :
        Integrable (fun ω ↦ transitionNextStateMean p (X n ω)) μ :=
      integrable_comp_process_of_reachableStates
        (P := P) (X := X) (p := p) hp h_support x h_start n
          (transitionNextStateMean p)
    have hMeanStrong :
        StronglyMeasurable[ℱ n] (fun ω ↦ transitionNextStateMean p (X n ω)) := by
      exact
        (((Measurable.of_discrete : Measurable (transitionNextStateMean p)).comp
          (hX_adapted n)).stronglyMeasurable)
    -- Proof comment: rewrite the compensated increment into the row-mean normal form, then use
    -- the one-step conditional expectation formula and measurability of the row mean.
    calc
      μ[fun ω ↦ M (n + 1) ω - M n ω | ℱ n] =ᵐ[μ]
          μ[fun ω ↦ (X (n + 1) ω : ℝ) - transitionNextStateMean p (X n ω) | ℱ n] := by
            exact
              condExp_congr_ae <|
                Filter.EventuallyEq.of_eq
                  (compensatedTransitionProcess_increment_eq (p := p) (X := X) n)
      _ =ᵐ[μ]
          μ[fun ω ↦ (X (n + 1) ω : ℝ) | ℱ n] -
            μ[fun ω ↦ transitionNextStateMean p (X n ω) | ℱ n] := by
              exact condExp_sub hNextInt hMeanInt (ℱ n)
      _ =ᵐ[μ]
          (fun ω ↦ transitionNextStateMean p (X n ω)) -
            μ[fun ω ↦ transitionNextStateMean p (X n ω) | ℱ n] := by
              exact
                (condExp_nextState_eq_transitionNextStateMean
                  (P := P) (X := X) (p := p) hp h_support x h_start n).sub
                  Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          (fun ω ↦ transitionNextStateMean p (X n ω)) -
            (fun ω ↦ transitionNextStateMean p (X n ω)) := by
              refine Filter.EventuallyEq.rfl.sub ?_
              exact Filter.EventuallyEq.of_eq
                (MeasureTheory.condExp_of_stronglyMeasurable
                  ((processFiltration X).le n) hMeanStrong hMeanInt)
      _ =ᵐ[μ] 0 := by
            simp
  have hMmart : Martingale M ℱ μ :=
    MeasureTheory.martingale_of_condExp_sub_eq_zero_nat hMad hMint hCondZero
  have hMsq : ∀ n, Integrable (fun ω ↦ M n ω ^ (2 : ℕ)) μ := by
    intro n
    exact
      (compensatedTransitionProcess_memLpTwo
        (P := P) (X := X) (p := p) hp h_support x h_start n).integrable_sq
  have hDensityInt : ∀ n, Integrable (density n) μ := by
    intro n
    simpa [density] using
      integrable_comp_process_of_reachableStates
        (P := P) (X := X) (p := p) hp h_support x h_start n
          (transitionSquareVariationIncrement p)
  have hAint : ∀ n, Integrable (A n) μ := by
    intro n
    -- Proof comment: the predictable quadratic-variation candidate is a finite sum of integrable
    -- one-step density terms.
    simpa [A, density, partialSum] using
      integrable_finset_sum (Finset.range n) fun i _ ↦ hDensityInt i
  have hMSquareStrong :
      ∀ n, StronglyMeasurable[ℱ n] (fun ω ↦ M n ω ^ (2 : ℕ)) := by
    intro n
    simpa [pow_two] using (hMad n).mul (hMad n)
  have hMadiff :
      StronglyAdapted ℱ (fun n ω ↦ M n ω ^ (2 : ℕ) - A n ω) := by
    intro n
    exact (hMSquareStrong n).sub (hAStrong n)
  have hSqIncrementCond :
      ∀ n, μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] =ᵐ[μ] density n := by
    intro n
    let Y : Ω → ℝ := fun ω ↦ (X (n + 1) ω : ℝ)
    let mean : Ω → ℝ := fun ω ↦ transitionNextStateMean p (X n ω)
    let cross : Ω → ℝ := fun ω ↦ Y ω * mean ω
    have hYInt : Integrable Y μ := by
      simpa [Y] using
        integrable_comp_process_of_reachableStates
          (P := P) (X := X) (p := p) hp h_support x h_start (n + 1) fun y ↦ (y : ℝ)
    have hYSqInt : Integrable (fun ω ↦ Y ω ^ (2 : ℕ)) μ := by
      simpa [Y] using
        integrable_comp_process_of_reachableStates
          (P := P) (X := X) (p := p) hp h_support x h_start (n + 1)
            (fun y ↦ (y : ℝ) ^ (2 : ℕ))
    have hMeanInt : Integrable mean μ := by
      simpa [mean] using
        integrable_comp_process_of_reachableStates
          (P := P) (X := X) (p := p) hp h_support x h_start n
            (transitionNextStateMean p)
    have hMeanSqInt : Integrable (fun ω ↦ mean ω ^ (2 : ℕ)) μ := by
      simpa [mean] using
        integrable_comp_process_of_reachableStates
          (P := P) (X := X) (p := p) hp h_support x h_start n
            (fun y ↦ transitionNextStateMean p y ^ (2 : ℕ))
    have hYLp : MemLp Y 2 μ := by
      exact
        (MeasureTheory.memLp_two_iff_integrable_sq
          (((Measurable.of_discrete : Measurable (fun y : E ↦ (y : ℝ))).comp
            (hReal.measurable_process (n + 1))).stronglyMeasurable.aestronglyMeasurable)).2
          hYSqInt
    have hMeanStrong : StronglyMeasurable[ℱ n] mean := by
      exact
        (((Measurable.of_discrete : Measurable (transitionNextStateMean p)).comp
          (hX_adapted n)).stronglyMeasurable)
    have hMeanLp : MemLp mean 2 μ := by
      exact
        (MeasureTheory.memLp_two_iff_integrable_sq
          ((hMeanStrong.mono ((processFiltration X).le n)).aestronglyMeasurable)).2
          hMeanSqInt
    have hCrossInt : Integrable cross μ := by
      simpa [cross] using MeasureTheory.MemLp.integrable_mul hYLp hMeanLp
    have hMeanSqStrong : StronglyMeasurable[ℱ n] (fun ω ↦ mean ω ^ (2 : ℕ)) := by
      simpa [pow_two] using hMeanStrong.mul hMeanStrong
    have hYSqMinusCrossInt :
        Integrable (fun ω ↦ Y ω ^ (2 : ℕ) - ((2 : ℝ) • cross) ω) μ := by
      exact hYSqInt.sub (hCrossInt.const_mul 2)
    -- Proof comment: expand the centered square, evaluate the three conditional expectations
    -- separately, and then collapse them to the raw second moment minus the squared conditional
    -- mean.
    calc
      μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] =ᵐ[μ]
          μ[fun ω ↦ (Y ω - mean ω) ^ (2 : ℕ) | ℱ n] := by
            refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            have hω := congrFun (compensatedTransitionProcess_increment_eq (p := p) (X := X) n) ω
            simpa [Y, mean] using congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) hω
      _ =ᵐ[μ]
          μ[fun ω ↦ Y ω ^ (2 : ℕ) - ((2 : ℝ) • cross) ω + mean ω ^ (2 : ℕ) | ℱ n] := by
            refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            simp [cross]
            ring
      _ =ᵐ[μ]
          μ[fun ω ↦ Y ω ^ (2 : ℕ) - ((2 : ℝ) • cross) ω | ℱ n] +
            μ[fun ω ↦ mean ω ^ (2 : ℕ) | ℱ n] := by
              exact condExp_add hYSqMinusCrossInt hMeanSqInt (ℱ n)
      _ =ᵐ[μ]
          (μ[fun ω ↦ Y ω ^ (2 : ℕ) | ℱ n] - μ[(2 : ℝ) • cross | ℱ n]) +
            μ[fun ω ↦ mean ω ^ (2 : ℕ) | ℱ n] := by
              exact (condExp_sub hYSqInt (hCrossInt.const_mul 2) (ℱ n)).add
                Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          (μ[fun ω ↦ Y ω ^ (2 : ℕ) | ℱ n] - (2 : ℝ) • μ[cross | ℱ n]) +
            μ[fun ω ↦ mean ω ^ (2 : ℕ) | ℱ n] := by
              exact
                (Filter.EventuallyEq.rfl.sub
                  (MeasureTheory.condExp_smul (μ := μ) (m := ℱ n) (c := (2 : ℝ))
                    (f := cross))).add
                    Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          (μ[fun ω ↦ Y ω ^ (2 : ℕ) | ℱ n] -
              (2 : ℝ) • (μ[Y | ℱ n] * mean)) +
            μ[fun ω ↦ mean ω ^ (2 : ℕ) | ℱ n] := by
              exact
                (Filter.EventuallyEq.rfl.sub
                  ((MeasureTheory.condExp_mul_of_stronglyMeasurable_right
                    hMeanStrong hCrossInt hYInt).const_smul (2 : ℝ))).add
                    Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          (fun ω ↦ transitionNextStateSecondMoment p (X n ω)) -
              (2 : ℝ) •
                ((fun ω ↦ transitionNextStateMean p (X n ω)) * mean) +
            μ[fun ω ↦ mean ω ^ (2 : ℕ) | ℱ n] := by
              have hMeanCond :
                  (2 : ℝ) • (μ[Y | ℱ n] * mean) =ᵐ[μ]
                    (2 : ℝ) • ((fun ω ↦ transitionNextStateMean p (X n ω)) * mean) :=
                ((condExp_nextState_eq_transitionNextStateMean
                  (P := P) (X := X) (p := p) hp h_support x h_start n).mul
                  Filter.EventuallyEq.rfl).const_smul (2 : ℝ)
              exact
                ((condExp_nextStateSq_eq_transitionNextStateSecondMoment
                  (P := P) (X := X) (p := p) hp h_support x h_start n).sub hMeanCond).add
                  Filter.EventuallyEq.rfl
      _ =ᵐ[μ]
          (fun ω ↦ transitionNextStateSecondMoment p (X n ω)) -
              (2 : ℝ) •
                ((fun ω ↦ transitionNextStateMean p (X n ω)) * mean) +
            (fun ω ↦ mean ω ^ (2 : ℕ)) := by
              refine Filter.EventuallyEq.rfl.add ?_
              exact Filter.EventuallyEq.of_eq
                (MeasureTheory.condExp_of_stronglyMeasurable
                  ((processFiltration X).le n) hMeanSqStrong hMeanSqInt)
      _ =ᵐ[μ]
          fun ω ↦ transitionNextStateSecondMoment p (X n ω) -
            transitionNextStateMean p (X n ω) ^ (2 : ℕ) := by
              exact Filter.EventuallyEq.of_eq <| by
                funext ω
                simp [mean]
                ring
      _ =ᵐ[μ] density n := by
            exact Filter.EventuallyEq.of_eq <| by
              funext ω
              simp [density, transitionSquareVariationIncrement]
  have hCondZeroSq :
      ∀ n, μ[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - A (n + 1) ω -
          (M n ω ^ (2 : ℕ) - A n ω) | ℱ n] =ᵐ[μ] 0 := by
    intro n
    have hAdiff : A (n + 1) - A n = density n := by
      funext ω
      simp [A, density, partialSum, Finset.sum_range_succ]
    have hSqDiffInt :
        Integrable (fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ)) μ :=
      (hMsq (n + 1)).sub (hMsq n)
    have hAdiffInt : Integrable (A (n + 1) - A n) μ := by
      rw [hAdiff]
      exact hDensityInt n
    -- Route correction: compare the compensated square increment with the martingale square
    -- increment and then cancel the predictable density term.
    calc
      μ[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - A (n + 1) ω -
          (M n ω ^ (2 : ℕ) - A n ω) | ℱ n] =ᵐ[μ]
          μ[fun ω ↦
              (M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ)) -
                (A (n + 1) ω - A n ω) | ℱ n] := by
                refine condExp_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
                ring
      _ =ᵐ[μ]
          μ[fun ω ↦ M (n + 1) ω ^ (2 : ℕ) - M n ω ^ (2 : ℕ) | ℱ n] -
            μ[A (n + 1) - A n | ℱ n] := by
              exact condExp_sub hSqDiffInt hAdiffInt (ℱ n)
      _ =ᵐ[μ]
          μ[fun ω ↦ (M (n + 1) ω - M n ω) ^ (2 : ℕ) | ℱ n] -
            μ[A (n + 1) - A n | ℱ n] := by
              exact (condExp_sqMomentDiff_eq_condExp_sqIncrement hMmart hMsq n).sub
                Filter.EventuallyEq.rfl
      _ =ᵐ[μ] density n - μ[A (n + 1) - A n | ℱ n] := by
            exact (hSqIncrementCond n).sub Filter.EventuallyEq.rfl
      _ =ᵐ[μ] density n - density n := by
            rw [hAdiff]
            refine Filter.EventuallyEq.rfl.sub ?_
            exact Filter.EventuallyEq.of_eq
              (MeasureTheory.condExp_of_stronglyMeasurable
                ((processFiltration X).le n) (hDensityStrong n) (hDensityInt n))
      _ =ᵐ[μ] 0 := by
            simp
  refine ⟨?_, ?_⟩
  · simpa [M, μ] using hMmart
  · refine ⟨?_, hAPredictable, ?_⟩
    · ext ω
      simp [A, partialSum]
    · simpa [M, A, μ] using
        MeasureTheory.martingale_of_condExp_sub_eq_zero_nat hMadiff
          (fun n ↦ (hMsq n).sub (hAint n)) hCondZeroSq

end ProcessPastFiltration

/-- Helper for Exercise 17.2.1: if the row `p x` only charges the three states `a`, `b`, and `c`,
then the next state sampled from `discreteMatrixKernel p x` lies in that triple almost surely. -/
private lemma ae_eq_or_eq_or_eq_of_rowSupport [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {x a b c : E}
    (hrow : ∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c) :
    ∀ᵐ y ∂ (discreteMatrixKernel p x), y = a ∨ y = b ∨ y = c := by
  rw [ae_iff]
  change discreteMatrixKernel p x {y | ¬ (y = a ∨ y = b ∨ y = c)} = 0
  -- Proof comment: the bad set carries no row mass because every singleton outside `{a, b, c}`
  -- has zero matrix entry.
  rw [discreteMatrixKernel_apply, Measure.sum_apply _ <|
    show MeasurableSet {y : E | ¬ (y = a ∨ y = b ∨ y = c)} from MeasurableSet.of_discrete]
  refine ENNReal.tsum_eq_zero.2 ?_
  intro y
  rw [Measure.smul_apply]
  by_cases hy : y = a ∨ y = b ∨ y = c
  · have hy_not_mem : y ∉ {z : E | ¬ (z = a ∨ z = b ∨ z = c)} := by
      intro hbad
      exact hbad hy
    rw [Measure.dirac_apply, Set.indicator_of_notMem hy_not_mem]
    simp
  · have hpxy : p x y = 0 := by
      by_contra hpxy
      exact hy (hrow y hpxy)
    have hy_mem : y ∈ {z : E | ¬ (z = a ∨ z = b ∨ z = c)} := by
      exact hy
    rw [Measure.dirac_apply, Set.indicator_of_mem hy_mem, Pi.one_apply]
    simp [hpxy]

/-- Helper for Exercise 17.2.1: the identity observable on a three-point row support is square
integrable under the corresponding row measure. -/
private lemma rowState_memLp_two [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support : HasAtMostThreePointStepSupport p) (x : E) :
    MeasureTheory.MemLp (fun y : E ↦ (y : ℝ)) 2 (discreteMatrixKernel p x) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  rcases h_support x with ⟨a, b, c, hrow⟩
  let lo : ℝ := min (min (a : ℝ) (b : ℝ)) (c : ℝ)
  let hi : ℝ := max (max (a : ℝ) (b : ℝ)) (c : ℝ)
  have hAE_support :
      ∀ᵐ y ∂ (discreteMatrixKernel p x), y = a ∨ y = b ∨ y = c :=
    ae_eq_or_eq_or_eq_of_rowSupport hrow
  have hAE_bounded :
      {y : E | (y : ℝ) ∈ Set.Icc lo hi} ∈ ae (discreteMatrixKernel p x) := by
    -- Proof comment: on the almost-sure support `{a, b, c}`, the identity observable is trapped
    -- between the minimum and maximum of those three real values.
    filter_upwards [hAE_support] with y hy
    rcases hy with rfl | rfl | rfl <;> simp [lo, hi]
  have hAEMeas :
      AEStronglyMeasurable (fun y : E ↦ (y : ℝ)) (discreteMatrixKernel p x) := by
    exact (Measurable.of_discrete : Measurable (fun y : E ↦ (y : ℝ))).aestronglyMeasurable
  exact MeasureTheory.memLp_of_bounded hAE_bounded hAEMeas 2

/-- Helper for Exercise 17.2.1: under the stochastic-row hypothesis, the canonical square-variation
increment is exactly the variance of the next-state identity observable under the row measure. -/
private lemma transitionSquareVariationIncrement_eq_variance [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support : HasAtMostThreePointStepSupport p) (x : E) :
    transitionSquareVariationIncrement p x =
      ProbabilityTheory.variance (fun y : E ↦ (y : ℝ)) (discreteMatrixKernel p x) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  have hmemLp :
      MeasureTheory.MemLp (fun y : E ↦ (y : ℝ)) 2 (discreteMatrixKernel p x) :=
    rowState_memLp_two hp h_support x
  -- Proof comment: `transitionSquareVariationIncrement` is the textbook second moment minus the
  -- square of the first moment, which matches the standard probability-space variance formula.
  rw [ProbabilityTheory.variance_eq_sub hmemLp]
  simp [transitionSquareVariationIncrement, transitionNextStateMean, transitionNextStateSecondMoment]

/-
Proof sketch: each summand in the square-variation increment is a square multiplied by a
nonnegative transition weight, so the whole series is nonnegative.
-/
-- Route correction: the displayed quantity is a variance only when the row measure
-- `discreteMatrixKernel p x` is a probability measure, so the stochastic
-- hypothesis `IsStochasticMatrix p` is essential.
-- Counterexample: take `E := Unit` with coercion `(⋆ : Unit) ↦ (1 : ℝ)` and `p ⋆ ⋆ = 2`.
-- Then the three-point support hypothesis holds, but
-- `transitionSquareVariationIncrement p ⋆ = 2 - 2^2 = -2`.
/-- Auxiliary nonnegativity fact: the canonical square-variation density from part (i) takes
values in `[0, ∞)`. Equivalently, the canonical square-variation increment is nonnegative for
every state `x`. -/
theorem transitionSquareVariationIncrement_nonneg [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support : HasAtMostThreePointStepSupport p) (x : E) :
    0 ≤ transitionSquareVariationIncrement p x := by
  -- Proof comment: identify the increment with a variance under the row measure and then invoke
  -- the general nonnegativity of variance.
  rw [transitionSquareVariationIncrement_eq_variance hp h_support x]
  exact ProbabilityTheory.variance_nonneg _ _

section ProcessPastFiltration

variable [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E] [Coe E ℝ]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable {p : E → E → ℝ≥0∞}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

local notation "ℱ" => processFiltration X

/-
Proof sketch: compare the given square-variation process with the canonical one from
`compensatedTransitionProcess_martingale_and_squareVariation`; equality of predictable quadratic
variation increments forces the rowwise density to agree with the canonical square-variation
increment.
-/
-- Route correction: a square-variation witness under a single start law `(P x : Measure Ω)`
-- only determines the density along states visited from `x`, so global uniqueness must be stated
-- using witnesses for every starting state.
-- Counterexample: for the deterministic identity chain started from `x`, the sampled path stays at
-- `x` almost surely, so any `f : E → NNReal` with `f x = transitionSquareVariationIncrement p x`
-- gives the same partial-sum witness under `(P x : Measure Ω)` even if `f` differs elsewhere.
/-- Continuation of Exercise 17.2.1 (1): the function `f : E → [0, ∞)` from part (i) is unique.
Any nonnegative square-variation density that realizes the compensated chain's square variation for
every starting state, with the time-`0` law under `P x` concentrated at `x`, agrees with the
canonical function coming from the three-point-support hypothesis. -/
theorem squareVariationDensity_unique
    (hp : IsStochasticMatrix p) (h_support : HasAtMostThreePointStepSupport p)
    (h_start : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x)
    {f : E → NNReal}
    (h_squareVariation :
      ∀ x : E,
        IsSquareVariationProcess ℱ (P x : Measure Ω)
          (compensatedTransitionProcess p X)
          (partialSum (fun n ↦ (fun x ↦ (f x : ℝ)) ∘ X n))) :
    (fun x ↦ (f x : ℝ)) = transitionSquareVariationIncrement p := by
  funext x
  let μ : Measure Ω := (P x : Measure Ω)
  let canonicalSquareVariation : ℕ → Ω → ℝ :=
    partialSum (fun n ↦ transitionSquareVariationIncrement p ∘ X n)
  let candidateSquareVariation : ℕ → Ω → ℝ :=
    partialSum (fun n ↦ (fun y ↦ (f y : ℝ)) ∘ X n)
  let difference : ℕ → Ω → ℝ :=
    fun n ω ↦ candidateSquareVariation n ω - canonicalSquareVariation n ω
  have hCanonical :
      IsSquareVariationProcess ℱ μ (compensatedTransitionProcess p X) canonicalSquareVariation :=
    (compensatedTransitionProcess_martingale_and_squareVariation
      hp h_support x (h_start x)).2
  have hCandidate :
      IsSquareVariationProcess ℱ μ (compensatedTransitionProcess p X) candidateSquareVariation :=
    h_squareVariation x
  have hDifferenceMartingale : Martingale difference ℱ μ := by
    -- Proof comment: subtract the two compensated-square martingales; the square terms cancel,
    -- leaving the difference of the two predictable quadratic-variation candidates.
    convert hCanonical.martingale_sq_sub.sub hCandidate.martingale_sq_sub using 1
    funext n ω
    dsimp [difference]
    ring
  have hDifferencePredictable : IsPredictable ℱ difference := by
    -- Proof comment: both square-variation witnesses are predictable, so their difference is
    -- predictable as well.
    simpa [difference] using hCandidate.predictable.sub hCanonical.predictable
  have hDifferenceTimeOne :
      difference 1 =ᵐ[μ] 0 := by
    -- Proof comment: a predictable martingale is almost surely constant, and here the initial
    -- value is `0` because both partial sums start at `0`.
    calc
      difference 1 =ᵐ[μ] difference 0 :=
        Martingale.eq_zero_of_predictable' hDifferenceMartingale hDifferencePredictable 1
      _ =ᵐ[μ] 0 := by
        filter_upwards [] with ω
        simp [difference, candidateSquareVariation, canonicalSquareVariation, partialSum]
  have hStateTimeOne :
      ∀ᵐ ω ∂ μ,
        (f (X 0 ω) : ℝ) - transitionSquareVariationIncrement p (X 0 ω) = 0 := by
    -- Proof comment: evaluate the partial sums at time `1`; only the time-`0` density remains.
    simpa [difference, candidateSquareVariation, canonicalSquareVariation, partialSum] using
      hDifferenceTimeOne
  have hEqSet :
      MeasurableSet {y : E | (f y : ℝ) - transitionSquareVariationIncrement p y = 0} := by
    have hMeas :
        Measurable (fun y : E ↦ (f y : ℝ) - transitionSquareVariationIncrement p y) :=
      Measurable.of_discrete
    show MeasurableSet ((fun y : E ↦ (f y : ℝ) - transitionSquareVariationIncrement p y) ⁻¹'
      ({0} : Set ℝ))
    simpa using hMeas (measurableSet_singleton (0 : ℝ))
  have hRealization :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hDiracTimeOne :
      ∀ᵐ y ∂ Measure.dirac x,
        (f y : ℝ) - transitionSquareVariationIncrement p y = 0 := by
    -- Proof comment: push the almost-sure time-`1` identity through the deterministic start law
    -- `X 0 ∼ δ_x`.
    rw [← h_start x]
    exact
      (MeasureTheory.ae_map_iff
        (hRealization.measurable_process 0).aemeasurable
        hEqSet).2 hStateTimeOne
  have hx :
      (f x : ℝ) - transitionSquareVariationIncrement p x = 0 := by
    simpa using hDiracTimeOne
  exact sub_eq_zero.mp hx

end ProcessPastFiltration

/-- Helper for Exercise 17.2.1: equal drifts at a fixed state force equality of the corresponding
next-state means. -/
private lemma transitionNextStateMean_eq_of_drift_eq [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p q : E → E → ℝ≥0∞} {x : E}
    (hd : transitionDrift p x = transitionDrift q x) :
    transitionNextStateMean p x = transitionNextStateMean q x := by
  -- Proof comment: both drifts subtract the same present-state term `(x : ℝ)`, so their equality
  -- is exactly equality of the two next-state means.
  dsimp [transitionDrift] at hd
  linarith

/-- Helper for Exercise 17.2.1: once the drifts agree at a state, equality of the square-variation
increments is equivalent to equality of the corresponding next-state second moments. -/
private lemma transitionNextStateSecondMoment_eq_of_drift_eq_and_squareVariationIncrement_eq
    [Countable E] [Coe E ℝ] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p q : E → E → ℝ≥0∞} {x : E}
    (hd : transitionDrift p x = transitionDrift q x)
    (hf : transitionSquareVariationIncrement p x = transitionSquareVariationIncrement q x) :
    transitionNextStateSecondMoment p x = transitionNextStateSecondMoment q x := by
  have hMean : transitionNextStateMean p x = transitionNextStateMean q x :=
    transitionNextStateMean_eq_of_drift_eq hd
  -- Proof comment: after rewriting the equal means, the two centered second moments differ only
  -- by their uncentered second moments.
  dsimp [transitionSquareVariationIncrement] at hf ⊢
  rw [hMean] at hf
  linarith

/-- Helper for Exercise 17.2.1: the real mass of a singleton under a discrete matrix-kernel row is
the corresponding matrix entry written in `ℝ`. -/
private lemma discreteMatrixKernel_real_singleton [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (x y : E) :
    ((discreteMatrixKernel p x).real ({y} : Set E)) = (p x y).toReal := by
  -- Proof comment: evaluate the defining countable sum of weighted Dirac masses on the singleton
  -- `{y}` and only the `y`-term survives.
  classical
  have happly : discreteMatrixKernel p x ({y} : Set E) = p x y := by
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    rw [tsum_eq_single y]
    · simp [Measure.dirac_apply]
    · intro i hi
      simp [Measure.dirac_apply, hi]
  simpa [Measure.real_def] using congrArg ENNReal.toReal happly

/-- Helper for Exercise 17.2.1: an integrable observable on a discrete row measure integrates to
the corresponding weighted row series. -/
private lemma transitionRowIntegral_eq_tsum [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} {x : E} {f : E → ℝ}
    (hf : Integrable f (discreteMatrixKernel p x)) :
    ∫ y, f y ∂ discreteMatrixKernel p x = ∑' y : E, (p x y).toReal * f y := by
  -- Proof comment: on a countable discrete state space, the Bochner integral is the countable
  -- sum of singleton masses times function values.
  calc
    ∫ y, f y ∂ discreteMatrixKernel p x
        = ∑' y : E, ((discreteMatrixKernel p x).real ({y} : Set E)) • f y := by
            simpa using
              (MeasureTheory.integral_countable (μ := discreteMatrixKernel p x) (f := f) hf)
    _ = ∑' y : E, (p x y).toReal * f y := by
          refine tsum_congr ?_
          intro y
          rw [discreteMatrixKernel_real_singleton]
          simp [smul_eq_mul]

/-- Helper for Exercise 17.2.1: under a three-point row-support hypothesis, every real-valued
observable is integrable against the corresponding row measure. -/
private lemma rowObservable_integrable_of_threePointSupport [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {p : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support : HasAtMostThreePointStepSupport p) (x : E) (f : E → ℝ) :
    Integrable f (discreteMatrixKernel p x) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  rcases h_support x with ⟨a, b, c, hrow⟩
  let C : ℝ := max (max ‖f a‖ ‖f b‖) ‖f c‖
  have hAE_support :
      ∀ᵐ y ∂ (discreteMatrixKernel p x), y = a ∨ y = b ∨ y = c :=
    ae_eq_or_eq_or_eq_of_rowSupport hrow
  have hAE_bound : ∀ᵐ y ∂ (discreteMatrixKernel p x), ‖f y‖ ≤ C := by
    -- Proof comment: once the row is supported on `{a, b, c}`, the observable can only take
    -- three values, so its norm is uniformly bounded there.
    filter_upwards [hAE_support] with y hy
    rcases hy with rfl | rfl | rfl <;> simp [C]
  refine Integrable.mono' (integrable_const C)
    ((Measurable.of_discrete : Measurable f).aestronglyMeasurable) ?_
  filter_upwards [hAE_bound] with y hy
  simpa using hy

/-- Helper for Exercise 17.2.1: every entry of a stochastic matrix row is finite because it is
bounded above by the total row mass `1`. -/
private lemma stochasticMatrixEntry_ne_top
    {α : Type*} {p : α → α → ℝ≥0∞} (hp : IsStochasticMatrix p) (i j : α) :
    p i j ≠ ∞ := by
  -- Proof comment: a single row entry is dominated by the full row sum, which is `1`.
  have hle : p i j ≤ ∑' y : α, p i y := ENNReal.le_tsum j
  rw [hp i] at hle
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

/-- Helper for Exercise 17.2.1: taking `toReal` commutes with the row sum of a stochastic matrix,
so the real row masses also sum to `1`. -/
private lemma stochasticRow_tsum_toReal
    {α : Type*} {p : α → α → ℝ≥0∞} (hp : IsStochasticMatrix p) (i : α) :
    ∑' j : α, (p i j).toReal = 1 := by
  -- Proof comment: every row entry is finite, so `ENNReal.tsum_toReal_eq` rewrites the row sum
  -- directly into the real-valued series.
  calc
    ∑' j : α, (p i j).toReal = (∑' j : α, p i j).toReal := by
      symm
      exact ENNReal.tsum_toReal_eq (fun j ↦ stochasticMatrixEntry_ne_top hp i j)
    _ = 1 := by simpa [hp i]

/-- Helper for Exercise 17.2.1: once a finite support container `s` is fixed, every weighted row
series collapses to the corresponding finite sum over `s`. -/
private lemma rowWeightedTsum_eq_of_support_in_finset [Countable E]
    {p : E → E → ℝ≥0∞} {x : E} (s : Finset E)
    (hrow : ∀ y : E, p x y ≠ 0 → y ∈ s) (g : E → ℝ) :
    ∑' y : E, g y * (p x y).toReal = s.sum (fun y ↦ g y * (p x y).toReal) := by
  have hsupport :
      ∀ y ∉ s, g y * (p x y).toReal = 0 := by
    intro y hy
    by_cases hpy : p x y = 0
    · simp [hpy]
    · exact False.elim (hy (hrow y hpy))
  simpa using (tsum_eq_sum hsupport)

/-- Helper for Exercise 17.2.1: two masses on distinct support points are determined by their
total mass and first moment. -/
private lemma twoMasses_eq_of_sum_mean_eq
    {u v pu pv qu qv : ℝ} (huv : u ≠ v)
    (hsum : pu + pv = qu + qv)
    (hmean : u * pu + v * pv = u * qu + v * qv) :
    pu = qu ∧ pv = qv := by
  have hsumDiff : (pu - qu) + (pv - qv) = 0 := by
    nlinarith [hsum]
  have hmeanDiff : u * (pu - qu) + v * (pv - qv) = 0 := by
    nlinarith [hmean]
  have hpu_zero : (u - v) * (pu - qu) = 0 := by
    -- Proof comment: subtracting the total-mass equation from the first-moment equation isolates
    -- the mass difference at `u`.
    calc
      (u - v) * (pu - qu)
          = (u * (pu - qu) + v * (pv - qv)) - v * ((pu - qu) + (pv - qv)) := by
              ring
      _ = 0 := by rw [hmeanDiff, hsumDiff]; ring
  have huvm : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hpu : pu = qu := by
    rcases mul_eq_zero.mp hpu_zero with hcoeff | hsub
    · exact False.elim (huvm hcoeff)
    · exact sub_eq_zero.mp hsub
  have hpv : pv = qv := by
    -- Proof comment: once one mass matches, the total-mass identity forces the other to match.
    nlinarith [hsum, hpu]
  exact ⟨hpu, hpv⟩

/-- Helper for Exercise 17.2.1: three masses on pairwise distinct support points are determined by
their total mass, first moment, and second moment. -/
private lemma threeMasses_eq_of_sum_mean_secondMoment_eq
    {u v w pu pv pw qu qv qw : ℝ}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hsum : pu + pv + pw = qu + qv + qw)
    (hmean : u * pu + v * pv + w * pw = u * qu + v * qv + w * qw)
    (hsq :
      u ^ (2 : ℕ) * pu + v ^ (2 : ℕ) * pv + w ^ (2 : ℕ) * pw =
        u ^ (2 : ℕ) * qu + v ^ (2 : ℕ) * qv + w ^ (2 : ℕ) * qw) :
    pu = qu ∧ pv = qv ∧ pw = qw := by
  have hsumDiff : (pu - qu) + (pv - qv) + (pw - qw) = 0 := by
    nlinarith [hsum]
  have hmeanDiff :
      u * (pu - qu) + v * (pv - qv) + w * (pw - qw) = 0 := by
    nlinarith [hmean]
  have hsqDiff :
      u ^ (2 : ℕ) * (pu - qu) + v ^ (2 : ℕ) * (pv - qv) + w ^ (2 : ℕ) * (pw - qw) = 0 := by
    nlinarith [hsq]
  have hpu_zero : ((u - v) * (u - w)) * (pu - qu) = 0 := by
    -- Proof comment: the quadratic isolator `(t - v) (t - w)` kills the `v` and `w` masses.
    calc
      ((u - v) * (u - w)) * (pu - qu)
          =
            (u ^ (2 : ℕ) * (pu - qu) + v ^ (2 : ℕ) * (pv - qv) + w ^ (2 : ℕ) * (pw - qw)) -
              (v + w) * (u * (pu - qu) + v * (pv - qv) + w * (pw - qw)) +
              (v * w) * ((pu - qu) + (pv - qv) + (pw - qw)) := by
                ring
      _ = 0 := by rw [hsqDiff, hmeanDiff, hsumDiff]; ring
  have hpu_coeff : ((u - v) * (u - w)) ≠ 0 := by
    exact mul_ne_zero (sub_ne_zero.mpr huv) (sub_ne_zero.mpr huw)
  have hpu : pu = qu := by
    rcases mul_eq_zero.mp hpu_zero with hcoeff | hsub
    · exact False.elim (hpu_coeff hcoeff)
    · exact sub_eq_zero.mp hsub
  have hpv_zero : ((v - u) * (v - w)) * (pv - qv) = 0 := by
    -- Proof comment: the same quadratic-isolator argument now isolates the `v` mass.
    calc
      ((v - u) * (v - w)) * (pv - qv)
          =
            (u ^ (2 : ℕ) * (pu - qu) + v ^ (2 : ℕ) * (pv - qv) + w ^ (2 : ℕ) * (pw - qw)) -
              (u + w) * (u * (pu - qu) + v * (pv - qv) + w * (pw - qw)) +
              (u * w) * ((pu - qu) + (pv - qv) + (pw - qw)) := by
                ring
      _ = 0 := by rw [hsqDiff, hmeanDiff, hsumDiff]; ring
  have hpv_coeff : ((v - u) * (v - w)) ≠ 0 := by
    exact mul_ne_zero (sub_ne_zero.mpr huv.symm) (sub_ne_zero.mpr hvw)
  have hpv : pv = qv := by
    rcases mul_eq_zero.mp hpv_zero with hcoeff | hsub
    · exact False.elim (hpv_coeff hcoeff)
    · exact sub_eq_zero.mp hsub
  have hpw : pw = qw := by
    -- Proof comment: after matching the first two masses, the total mass identifies the last one.
    nlinarith [hsum, hpu, hpv]
  exact ⟨hpu, hpv, hpw⟩

/-- Helper for Exercise 17.2.1: if both stochastic rows are supported on the singleton `{u}`,
then the two rows agree. -/
private lemma rowEq_ofSingletonSupport [Countable E]
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p) (hq : IsStochasticMatrix q)
    {x u : E}
    (hpU : ∀ y : E, p x y ≠ 0 → y = u)
    (hqU : ∀ y : E, q x y ≠ 0 → y = u) :
    p x = q x := by
  classical
  have hpSupport : ∀ y : E, p x y ≠ 0 → y ∈ ({u} : Finset E) := by
    intro y hy
    simp [hpU y hy]
  have hqSupport : ∀ y : E, q x y ≠ 0 → y ∈ ({u} : Finset E) := by
    intro y hy
    simp [hqU y hy]
  have hpCollapse : ∑' y : E, (p x y).toReal = (p x u).toReal := by
    -- Proof comment: once the singleton support is fixed, the real row mass collapses to the
    -- lone surviving matrix entry.
    simpa using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u} : Finset E) hpSupport
        fun _ ↦ (1 : ℝ))
  have hqCollapse : ∑' y : E, (q x y).toReal = (q x u).toReal := by
    -- Proof comment: the same singleton collapse applies to the comparison row.
    simpa using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u} : Finset E) hqSupport
        fun _ ↦ (1 : ℝ))
  have hpu : (p x u).toReal = 1 := by
    calc
      (p x u).toReal = ∑' y : E, (p x y).toReal := hpCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hp x
  have hqu : (q x u).toReal = 1 := by
    calc
      (q x u).toReal = ∑' y : E, (q x y).toReal := hqCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hq x
  funext y
  by_cases hy : y = u
  · cases hy
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x u)
        (stochasticMatrixEntry_ne_top hq x u)).mp (hpu.trans hqu.symm)
  · have hpy : p x y = 0 := by
      by_contra hpy
      exact hy (hpU y hpy)
    have hqy : q x y = 0 := by
      by_contra hqy
      exact hy (hqU y hqy)
    simp [hpy, hqy]

/-- Helper for Exercise 17.2.1: on two distinct support points, equality of total mass and first
moment determines the row uniquely. -/
private lemma rowEq_ofPairSupport_of_mean_eq [Countable E]
    {φ : E → ℝ} {p q : E → E → ℝ≥0∞} {x u v : E}
    (huv : u ≠ v) (hφuv : φ u ≠ φ v)
    (hp : IsStochasticMatrix p) (hq : IsStochasticMatrix q)
    (hpUv : ∀ y : E, p x y ≠ 0 → y = u ∨ y = v)
    (hqUv : ∀ y : E, q x y ≠ 0 → y = u ∨ y = v)
    (hmean : ∑' y : E, φ y * (p x y).toReal = ∑' y : E, φ y * (q x y).toReal) :
    p x = q x := by
  classical
  let pu : ℝ := (p x u).toReal
  let pv : ℝ := (p x v).toReal
  let qu : ℝ := (q x u).toReal
  let qv : ℝ := (q x v).toReal
  have hpSupport : ∀ y : E, p x y ≠ 0 → y ∈ ({u, v} : Finset E) := by
    intro y hy
    rcases hpUv y hy with rfl | rfl <;> simp [huv]
  have hqSupport : ∀ y : E, q x y ≠ 0 → y ∈ ({u, v} : Finset E) := by
    intro y hy
    rcases hqUv y hy with rfl | rfl <;> simp [huv]
  have hpCollapse : ∑' y : E, (p x y).toReal = pu + pv := by
    -- Proof comment: after fixing the pair support, the total real row mass is the sum of the
    -- two surviving entries.
    simpa [pu, pv, huv, add_comm, add_left_comm, add_assoc] using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u, v} : Finset E) hpSupport
        fun _ ↦ (1 : ℝ))
  have hqCollapse : ∑' y : E, (q x y).toReal = qu + qv := by
    -- Proof comment: the comparison row collapses to the same two support coordinates.
    simpa [qu, qv, huv, add_comm, add_left_comm, add_assoc] using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u, v} : Finset E) hqSupport
        fun _ ↦ (1 : ℝ))
  have hpSum : pu + pv = 1 := by
    calc
      pu + pv = ∑' y : E, (p x y).toReal := hpCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hp x
  have hqSum : qu + qv = 1 := by
    calc
      qu + qv = ∑' y : E, (q x y).toReal := hqCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hq x
  have hpMeanCollapse : ∑' y : E, φ y * (p x y).toReal = φ u * pu + φ v * pv := by
    -- Proof comment: the first moment also collapses to the two surviving support points.
    simpa [pu, pv, huv, add_comm, add_left_comm, add_assoc] using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u, v} : Finset E) hpSupport φ)
  have hqMeanCollapse : ∑' y : E, φ y * (q x y).toReal = φ u * qu + φ v * qv := by
    -- Proof comment: the same finite-support collapse gives the comparison first moment.
    simpa [qu, qv, huv, add_comm, add_left_comm, add_assoc] using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u, v} : Finset E) hqSupport φ)
  have hsum : pu + pv = qu + qv := by
    nlinarith [hpSum, hqSum]
  have hmean' : φ u * pu + φ v * pv = φ u * qu + φ v * qv := by
    calc
      φ u * pu + φ v * pv = ∑' y : E, φ y * (p x y).toReal := hpMeanCollapse.symm
      _ = ∑' y : E, φ y * (q x y).toReal := hmean
      _ = φ u * qu + φ v * qv := hqMeanCollapse
  rcases twoMasses_eq_of_sum_mean_eq hφuv hsum hmean' with ⟨hpu, hpv⟩
  funext y
  by_cases hyu : y = u
  · cases hyu
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x u)
        (stochasticMatrixEntry_ne_top hq x u)).mp hpu
  by_cases hyv : y = v
  · cases hyv
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x v)
        (stochasticMatrixEntry_ne_top hq x v)).mp hpv
  · have hpy : p x y = 0 := by
      by_contra hpy
      rcases hpUv y hpy with hy | hy
      · exact hyu hy
      · exact hyv hy
    have hqy : q x y = 0 := by
      by_contra hqy
      rcases hqUv y hqy with hy | hy
      · exact hyu hy
      · exact hyv hy
    simp [hpy, hqy]

/-- Helper for Exercise 17.2.1: on three pairwise distinct support points, equality of total mass,
first moment, and second moment determines the row uniquely. -/
private lemma rowEq_ofTripleSupport_of_mean_sq_eq [Countable E]
    {φ : E → ℝ} {p q : E → E → ℝ≥0∞} {x u v w : E}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hφuv : φ u ≠ φ v) (hφuw : φ u ≠ φ w) (hφvw : φ v ≠ φ w)
    (hp : IsStochasticMatrix p) (hq : IsStochasticMatrix q)
    (hpUvw : ∀ y : E, p x y ≠ 0 → y = u ∨ y = v ∨ y = w)
    (hqUvw : ∀ y : E, q x y ≠ 0 → y = u ∨ y = v ∨ y = w)
    (hmean : ∑' y : E, φ y * (p x y).toReal = ∑' y : E, φ y * (q x y).toReal)
    (hsq : ∑' y : E, (φ y) ^ (2 : ℕ) * (p x y).toReal =
      ∑' y : E, (φ y) ^ (2 : ℕ) * (q x y).toReal) :
    p x = q x := by
  classical
  let pu : ℝ := (p x u).toReal
  let pv : ℝ := (p x v).toReal
  let pw : ℝ := (p x w).toReal
  let qu : ℝ := (q x u).toReal
  let qv : ℝ := (q x v).toReal
  let qw : ℝ := (q x w).toReal
  have hpSupport : ∀ y : E, p x y ≠ 0 → y ∈ ({u, v, w} : Finset E) := by
    intro y hy
    rcases hpUvw y hy with rfl | rfl | rfl <;> simp [huv, huw, hvw]
  have hqSupport : ∀ y : E, q x y ≠ 0 → y ∈ ({u, v, w} : Finset E) := by
    intro y hy
    rcases hqUvw y hy with rfl | rfl | rfl <;> simp [huv, huw, hvw]
  have hpCollapse : ∑' y : E, (p x y).toReal = pu + pv + pw := by
    -- Proof comment: with a duplicate-free triple support, the row sum collapses to three masses.
    simpa [pu, pv, pw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u, v, w} : Finset E)
        hpSupport fun _ ↦ (1 : ℝ))
  have hqCollapse : ∑' y : E, (q x y).toReal = qu + qv + qw := by
    -- Proof comment: the comparison row collapses to the same triple of coordinates.
    simpa [qu, qv, qw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u, v, w} : Finset E)
        hqSupport fun _ ↦ (1 : ℝ))
  have hpSum : pu + pv + pw = 1 := by
    calc
      pu + pv + pw = ∑' y : E, (p x y).toReal := hpCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hp x
  have hqSum : qu + qv + qw = 1 := by
    calc
      qu + qv + qw = ∑' y : E, (q x y).toReal := hqCollapse.symm
      _ = 1 := stochasticRow_tsum_toReal hq x
  have hpMeanCollapse : ∑' y : E, φ y * (p x y).toReal = φ u * pu + φ v * pv + φ w * pw := by
    -- Proof comment: the first moment collapses to the same three explicit masses.
    simpa [pu, pv, pw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u, v, w} : Finset E)
        hpSupport φ)
  have hqMeanCollapse : ∑' y : E, φ y * (q x y).toReal = φ u * qu + φ v * qv + φ w * qw := by
    -- Proof comment: the comparison first moment uses the same finite support normal form.
    simpa [qu, qv, qw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u, v, w} : Finset E)
        hqSupport φ)
  have hpSqCollapse :
      ∑' y : E, (φ y) ^ (2 : ℕ) * (p x y).toReal =
        (φ u) ^ (2 : ℕ) * pu + (φ v) ^ (2 : ℕ) * pv + (φ w) ^ (2 : ℕ) * pw := by
    -- Proof comment: the second moment collapses to the three squared support values.
    simpa [pu, pv, pw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := p) (x := x) ({u, v, w} : Finset E)
        hpSupport fun y ↦ (φ y) ^ (2 : ℕ))
  have hqSqCollapse :
      ∑' y : E, (φ y) ^ (2 : ℕ) * (q x y).toReal =
        (φ u) ^ (2 : ℕ) * qu + (φ v) ^ (2 : ℕ) * qv + (φ w) ^ (2 : ℕ) * qw := by
    -- Proof comment: the comparison second moment uses the same explicit three-mass form.
    simpa [qu, qv, qw, huv, huw, hvw, add_assoc, add_comm, add_left_comm] using
      (rowWeightedTsum_eq_of_support_in_finset (p := q) (x := x) ({u, v, w} : Finset E)
        hqSupport fun y ↦ (φ y) ^ (2 : ℕ))
  have hsum : pu + pv + pw = qu + qv + qw := by
    nlinarith [hpSum, hqSum]
  have hmean' : φ u * pu + φ v * pv + φ w * pw = φ u * qu + φ v * qv + φ w * qw := by
    calc
      φ u * pu + φ v * pv + φ w * pw = ∑' y : E, φ y * (p x y).toReal := hpMeanCollapse.symm
      _ = ∑' y : E, φ y * (q x y).toReal := hmean
      _ = φ u * qu + φ v * qv + φ w * qw := hqMeanCollapse
  have hsq' :
      (φ u) ^ (2 : ℕ) * pu + (φ v) ^ (2 : ℕ) * pv + (φ w) ^ (2 : ℕ) * pw =
        (φ u) ^ (2 : ℕ) * qu + (φ v) ^ (2 : ℕ) * qv + (φ w) ^ (2 : ℕ) * qw := by
    calc
      (φ u) ^ (2 : ℕ) * pu + (φ v) ^ (2 : ℕ) * pv + (φ w) ^ (2 : ℕ) * pw =
          ∑' y : E, (φ y) ^ (2 : ℕ) * (p x y).toReal := hpSqCollapse.symm
      _ = ∑' y : E, (φ y) ^ (2 : ℕ) * (q x y).toReal := hsq
      _ =
          (φ u) ^ (2 : ℕ) * qu + (φ v) ^ (2 : ℕ) * qv + (φ w) ^ (2 : ℕ) * qw := hqSqCollapse
  rcases threeMasses_eq_of_sum_mean_secondMoment_eq hφuv hφuw hφvw hsum hmean' hsq' with
    ⟨hpu, hpv, hpw⟩
  funext y
  by_cases hyu : y = u
  · cases hyu
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x u)
        (stochasticMatrixEntry_ne_top hq x u)).mp hpu
  by_cases hyv : y = v
  · cases hyv
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x v)
        (stochasticMatrixEntry_ne_top hq x v)).mp hpv
  by_cases hyw : y = w
  · cases hyw
    exact
      (ENNReal.toReal_eq_toReal (stochasticMatrixEntry_ne_top hp x w)
        (stochasticMatrixEntry_ne_top hq x w)).mp hpw
  · have hpy : p x y = 0 := by
      by_contra hpy
      rcases hpUvw y hpy with hy | hy | hy
      · exact hyu hy
      · exact hyv hy
      · exact hyw hy
    have hqy : q x y = 0 := by
      by_contra hqy
      rcases hqUvw y hqy with hy | hy | hy
      · exact hyu hy
      · exact hyv hy
      · exact hyw hy
    simp [hpy, hqy]

/-- Helper for Exercise 17.2.1: on a common support of size at most three, equality of total mass,
first moment, and second moment for an injective observable determines the whole row. -/
private theorem threePointSupport_row_eq_of_moments_eq [Countable E]
    {φ : E → ℝ} (hφ : Function.Injective φ)
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p) (hq : IsStochasticMatrix q)
    {x a b c : E}
    (hpAx : ∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c)
    (hqAx : ∀ y : E, q x y ≠ 0 → y = a ∨ y = b ∨ y = c)
    (hmean : ∑' y : E, φ y * (p x y).toReal = ∑' y : E, φ y * (q x y).toReal)
    (hsq : ∑' y : E, (φ y) ^ (2 : ℕ) * (p x y).toReal =
      ∑' y : E, (φ y) ^ (2 : ℕ) * (q x y).toReal) :
    p x = q x := by
  -- Route correction: split the duplicate-labelled support triple before any finite-support
  -- collapse, then call the fixed singleton/pair/triple reconstruction lemmas.
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      have hpSingleton : ∀ y : E, p x y ≠ 0 → y = a := by
        intro y hy
        rcases hpAx y hy with hy | hy | hy <;> simpa using hy
      have hqSingleton : ∀ y : E, q x y ≠ 0 → y = a := by
        intro y hy
        rcases hqAx y hy with hy | hy | hy <;> simpa using hy
      -- Proof comment: when all three labels coincide, both rows are forced onto the same
      -- singleton support.
      exact rowEq_ofSingletonSupport hp hq hpSingleton hqSingleton
    · have hφac : φ a ≠ φ c := by
        intro hEq
        exact hac (hφ hEq)
      have hpPair : ∀ y : E, p x y ≠ 0 → y = a ∨ y = c := by
        intro y hy
        rcases hpAx y hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inl hy
        · exact Or.inr hy
      have hqPair : ∀ y : E, q x y ≠ 0 → y = a ∨ y = c := by
        intro y hy
        rcases hqAx y hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inl hy
        · exact Or.inr hy
      -- Proof comment: once `a = b` but `c` stays distinct, only the pair `{a, c}` remains.
      exact rowEq_ofPairSupport_of_mean_eq hac hφac hp hq hpPair hqPair hmean
  · by_cases hac : a = c
    · subst c
      have hφab : φ a ≠ φ b := by
        intro hEq
        exact hab (hφ hEq)
      have hpPair : ∀ y : E, p x y ≠ 0 → y = a ∨ y = b := by
        intro y hy
        rcases hpAx y hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr hy
        · exact Or.inl hy
      have hqPair : ∀ y : E, q x y ≠ 0 → y = a ∨ y = b := by
        intro y hy
        rcases hqAx y hy with hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr hy
        · exact Or.inl hy
      -- Proof comment: when `a = c` and `a ≠ b`, the common support reduces to `{a, b}`.
      exact rowEq_ofPairSupport_of_mean_eq hab hφab hp hq hpPair hqPair hmean
    · by_cases hbc : b = c
      · have hφab : φ a ≠ φ b := by
          intro hEq
          exact hab (hφ hEq)
        have hpPair : ∀ y : E, p x y ≠ 0 → y = a ∨ y = b := by
          intro y hy
          rcases hpAx y hy with hy | hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
          · exact Or.inr (hy.trans hbc.symm)
        have hqPair : ∀ y : E, q x y ≠ 0 → y = a ∨ y = b := by
          intro y hy
          rcases hqAx y hy with hy | hy | hy
          · exact Or.inl hy
          · exact Or.inr hy
          · exact Or.inr (hy.trans hbc.symm)
        -- Proof comment: when `b = c` and `a` stays distinct, the support is again a pair.
        exact rowEq_ofPairSupport_of_mean_eq hab hφab hp hq hpPair hqPair hmean
      · have hφab : φ a ≠ φ b := by
          intro hEq
          exact hab (hφ hEq)
        have hφac : φ a ≠ φ c := by
          intro hEq
          exact hac (hφ hEq)
        have hφbc : φ b ≠ φ c := by
          intro hEq
          exact hbc (hφ hEq)
        -- Proof comment: in the genuine three-point case, the fixed triple-support lemma
        -- reconstructs all three masses from total mass, mean, and second moment.
        exact
          rowEq_ofTripleSupport_of_mean_sq_eq hab hac hbc hφab hφac hφbc hp hq hpAx hqAx
            hmean hsq
-- Proof sketch: once the source-facing rowwise support container `Aₓ` is fixed and has
-- cardinality at most three, the rows `p x` and `q x` have at most three unknown masses inside
-- `Aₓ`. Stochasticity, the drift identity, and the square-variation identity give three linear
-- relations, which determine those masses uniquely; injectivity of `E → ℝ` prevents distinct
-- states from collapsing to the same real location.
/-- Auxiliary rowwise uniqueness statement: on a genuine real state space `E ⊂ ℝ`, once the
source-facing support container `Aₓ` is fixed, the row `p x` is uniquely determined by its drift
and square-variation increment at `x`. -/
theorem transitionRow_eq_of_drift_eq_and_squareVariationIncrement_eq [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (h_real : Function.Injective (fun x : E ↦ (x : ℝ)))
    {A : E → Set E} (hA : HasAtMostThreePointSet A)
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (hq : IsStochasticMatrix q)
    (h_support_p : HasAtMostThreePointStepSupport p)
    (h_support_q : HasAtMostThreePointStepSupport q)
    (hpA : HasStepSupportWithin p A)
    (hqA : HasStepSupportWithin q A)
    {x : E}
    (hd : transitionDrift p x = transitionDrift q x)
    (hf :
      transitionSquareVariationIncrement p x = transitionSquareVariationIncrement q x) :
    p x = q x := by
  have hMean : transitionNextStateMean p x = transitionNextStateMean q x :=
    transitionNextStateMean_eq_of_drift_eq hd
  have hSecond : transitionNextStateSecondMoment p x = transitionNextStateSecondMoment q x :=
    transitionNextStateSecondMoment_eq_of_drift_eq_and_squareVariationIncrement_eq
      hd hf
  rcases hA x with ⟨a, b, c, hAx⟩
  have hpAx : ∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c := by
    intro y hy
    exact hAx (hpA hy)
  have hqAx : ∀ y : E, q x y ≠ 0 → y = a ∨ y = b ∨ y = c := by
    intro y hy
    exact hAx (hqA hy)
  have _hSkeleton :
      transitionNextStateMean p x = transitionNextStateMean q x ∧
        transitionNextStateSecondMoment p x = transitionNextStateSecondMoment q x := by
    exact ⟨hMean, hSecond⟩
  have _hSupport :
      (∀ y : E, p x y ≠ 0 → y = a ∨ y = b ∨ y = c) ∧
        (∀ y : E, q x y ≠ 0 → y = a ∨ y = b ∨ y = c) := by
    exact ⟨hpAx, hqAx⟩
  have hpMeanIntegrable :
      Integrable (fun y : E ↦ (y : ℝ)) (discreteMatrixKernel p x) :=
    rowObservable_integrable_of_threePointSupport hp h_support_p x fun y : E ↦ (y : ℝ)
  have hqMeanIntegrable :
      Integrable (fun y : E ↦ (y : ℝ)) (discreteMatrixKernel q x) :=
    rowObservable_integrable_of_threePointSupport hq h_support_q x fun y : E ↦ (y : ℝ)
  have hpSecondIntegrable :
      Integrable (fun y : E ↦ (y : ℝ) ^ (2 : ℕ)) (discreteMatrixKernel p x) :=
    rowObservable_integrable_of_threePointSupport hp h_support_p x
      fun y : E ↦ (y : ℝ) ^ (2 : ℕ)
  have hqSecondIntegrable :
      Integrable (fun y : E ↦ (y : ℝ) ^ (2 : ℕ)) (discreteMatrixKernel q x) :=
    rowObservable_integrable_of_threePointSupport hq h_support_q x
      fun y : E ↦ (y : ℝ) ^ (2 : ℕ)
  have hMeanSeries :
      ∑' y : E, (y : ℝ) * (p x y).toReal = ∑' y : E, (y : ℝ) * (q x y).toReal := by
    have hpMeanTsum :
        transitionNextStateMean p x = ∑' y : E, (y : ℝ) * (p x y).toReal := by
      rw [transitionNextStateMean, transitionRowIntegral_eq_tsum hpMeanIntegrable]
      refine tsum_congr ?_
      intro y
      ring
    have hqMeanTsum :
        transitionNextStateMean q x = ∑' y : E, (y : ℝ) * (q x y).toReal := by
      rw [transitionNextStateMean, transitionRowIntegral_eq_tsum hqMeanIntegrable]
      refine tsum_congr ?_
      intro y
      ring
    simpa [hpMeanTsum, hqMeanTsum] using hMean
  have hSecondSeries :
      ∑' y : E, ((y : ℝ) ^ (2 : ℕ)) * (p x y).toReal =
        ∑' y : E, ((y : ℝ) ^ (2 : ℕ)) * (q x y).toReal := by
    have hpSecondTsum :
        transitionNextStateSecondMoment p x =
          ∑' y : E, ((y : ℝ) ^ (2 : ℕ)) * (p x y).toReal := by
      rw [transitionNextStateSecondMoment, transitionRowIntegral_eq_tsum hpSecondIntegrable]
      refine tsum_congr ?_
      intro y
      ring
    have hqSecondTsum :
        transitionNextStateSecondMoment q x =
          ∑' y : E, ((y : ℝ) ^ (2 : ℕ)) * (q x y).toReal := by
      rw [transitionNextStateSecondMoment, transitionRowIntegral_eq_tsum hqSecondIntegrable]
      refine tsum_congr ?_
      intro y
      ring
    simpa [hpSecondTsum, hqSecondTsum] using hSecond
  -- Proof comment: the reusable three-point moment-reconstruction lemma absorbs the one-point,
  -- two-point, and genuine three-point support degeneracies in one place.
  exact
    threePointSupport_row_eq_of_moments_eq
      (φ := fun y : E ↦ (y : ℝ)) h_real hp hq hpAx hqAx hMeanSeries hSecondSeries

/-- Exercise 17.2.1 (2): on a countable real state space `E ⊂ ℝ`, once a rowwise support
container `Aₓ` with at most three points is fixed, the transition matrix is uniquely determined by
its drift function and by the square-variation density from part (i). -/
theorem transitionMatrix_eq_of_drift_eq_and_squareVariationIncrement_eq [Countable E] [Coe E ℝ]
    [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (h_real : Function.Injective (fun x : E ↦ (x : ℝ)))
    {A : E → Set E} (hA : HasAtMostThreePointSet A)
    {p q : E → E → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (hq : IsStochasticMatrix q)
    (hpA : HasStepSupportWithin p A)
    (hqA : HasStepSupportWithin q A)
    (hd : transitionDrift p = transitionDrift q)
    (hf :
      transitionSquareVariationIncrement p = transitionSquareVariationIncrement q) :
    p = q := by
  have h_support_p : HasAtMostThreePointStepSupport p := hA.hasAtMostThreePointStepSupport hpA
  have h_support_q : HasAtMostThreePointStepSupport q := hA.hasAtMostThreePointStepSupport hqA
  funext x
  exact
    transitionRow_eq_of_drift_eq_and_squareVariationIncrement_eq
      h_real hA hp hq h_support_p h_support_q hpA hqA (congrFun hd x) (congrFun hf x)

/-- Helper for Exercise 17.2.1: the Moran frequency at state `0` is `0`. -/
private lemma moranFrequency_zero_local (N : ℕ+) :
    moranFrequency N 0 = 0 := by
  -- Proof comment: the zero count state has zero frequency by definition.
  simp [moranFrequency]

/-- Helper for Exercise 17.2.1: the Moran frequency at the maximal state is `1`. -/
private lemma moranFrequency_last_local (N : ℕ+) :
    moranFrequency N (Fin.last N) = 1 := by
  -- Proof comment: the maximal count state equals `N`, so dividing by `N` gives `1`.
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast N.ne_zero
  simp [moranFrequency, hN]

/-- Helper for Exercise 17.2.1: moving to the successor raises the Moran frequency by `1 / N`. -/
private lemma moranFrequency_succ_local (N : ℕ+) (i : Fin (N + 1))
    (h : (i : ℕ) + 1 < N + 1) :
    moranFrequency N ⟨(i : ℕ) + 1, h⟩ = moranFrequency N i + 1 / N := by
  -- Proof comment: both sides are the same linear expression in the count coordinate.
  calc
    moranFrequency N ⟨(i : ℕ) + 1, h⟩ = ((((i : ℕ) + 1 : ℕ) : ℝ) / N) := by
      rw [moranFrequency]
    _ = (((i : ℝ) + 1) / N) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ = moranFrequency N i + 1 / N := by
      rw [moranFrequency]
      ring

/-- Helper for Exercise 17.2.1: moving to the predecessor lowers the Moran frequency by `1 / N`.
-/
private lemma moranFrequency_pred_local (N : ℕ+) (i : Fin (N + 1))
    (h : (i : ℕ) ≠ 0) :
    moranFrequency N ⟨(i : ℕ) - 1, by omega⟩ = moranFrequency N i - 1 / N := by
  have hi : 1 ≤ (i : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
  -- Proof comment: both sides are the same linear expression in the count coordinate.
  calc
    moranFrequency N ⟨(i : ℕ) - 1, by omega⟩ = ((((i : ℕ) - 1 : ℕ) : ℝ) / N) := by
      rw [moranFrequency]
    _ = (((i : ℝ) - 1) / N) := by
      rw [Nat.cast_sub hi, Nat.cast_one]
    _ = moranFrequency N i - 1 / N := by
      rw [moranFrequency]
      ring

/-- Helper for Exercise 17.2.1: removing `ENNReal.ofReal` from the Moran move mass gives the
textbook polynomial `x (1 - x)`. -/
private lemma moranMoveProb_toReal_local (N : ℕ+) (i : Fin (N + 1)) :
    (moranMoveProb N i).toReal = moranFrequency N i * (1 - moranFrequency N i) := by
  have hnonneg : 0 ≤ moranFrequency N i * (1 - moranFrequency N i) := by
    have hN : (0 : ℝ) < N := by
      exact_mod_cast N.pos
    have hfreq_nonneg : 0 ≤ moranFrequency N i := by
      exact div_nonneg (by positivity) hN.le
    have hfreq_le_one : moranFrequency N i ≤ 1 := by
      have hi : (i : ℝ) ≤ N := by
        exact_mod_cast (Nat.lt_succ_iff.mp i.2)
      have hdiv : (i : ℝ) / N ≤ N / N := by
        exact div_le_div_of_nonneg_right hi hN.le
      simpa [moranFrequency, hN.ne'] using hdiv
    exact mul_nonneg hfreq_nonneg (sub_nonneg.mpr hfreq_le_one)
  -- Proof comment: `moranMoveProb` is defined as `ENNReal.ofReal` of the move polynomial.
  simp [moranMoveProb, ENNReal.toReal_ofReal, hnonneg]

/-- Helper for Exercise 17.2.1: removing `ENNReal.ofReal` from the Moran stay mass gives the
textbook polynomial `x^2 + (1 - x)^2`. -/
private lemma moranStayProb_toReal_local (N : ℕ+) (i : Fin (N + 1)) :
    (moranStayProb N i).toReal =
      moranFrequency N i ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ) := by
  have hnonneg :
      0 ≤ moranFrequency N i ^ (2 : ℕ) + (1 - moranFrequency N i) ^ (2 : ℕ) := by
    positivity
  -- Proof comment: `moranStayProb` is defined as `ENNReal.ofReal` of the stay polynomial.
  simp [moranStayProb, ENNReal.toReal_ofReal, hnonneg]

/-- Helper for Exercise 17.2.1: the Moran frequency map is injective because all states are scaled
by the same positive population size `N`. -/
private lemma moranFrequency_injective_local (N : ℕ+) :
    Function.Injective (moranFrequency N) := by
  intro i j hij
  apply Fin.ext
  have hmul := congrArg (fun t : ℝ ↦ t * (N : ℝ)) hij
  have hcast : (i : ℝ) = (j : ℝ) := by
    -- Proof comment: multiplying by the common nonzero denominator `N` recovers the underlying
    -- count coordinates.
    simpa [moranFrequency, N.ne_zero] using hmul
  exact_mod_cast hcast

/-- Helper for Exercise 17.2.1: every nonzero Moran row entry lies at the successor, the current
state, or the predecessor. -/
private lemma moranTransitionMatrix_support_local (N : ℕ+) {i j : Fin (N + 1)}
    (hij : moranTransitionMatrix N i j ≠ 0) :
    (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1 := by
  by_cases hsucc : (j : ℕ) = (i : ℕ) + 1
  · exact Or.inl hsucc
  by_cases hstay : j = i
  · exact Or.inr (Or.inl hstay)
  by_cases hpred : (i : ℕ) = (j : ℕ) + 1
  · exact Or.inr (Or.inr hpred)
  -- Proof comment: once the successor, stay, and predecessor branches are all ruled out, the
  -- defining `if`-chain for `moranTransitionMatrix` forces the row entry to vanish.
  · simp [moranTransitionMatrix, hsucc, hstay, hpred] at hij

/-- Helper for Exercise 17.2.1: on a finite stochastic row, centered first and second moments
around `c` determine the corresponding raw first and second moments. -/
private lemma centeredRowMoments_to_rawMoments
    {α : Type*} [Fintype α] {r : α → ℝ≥0∞} {φ : α → ℝ} {c v : ℝ}
    (hr : ∑' y : α, (r y).toReal = 1)
    (hcentered : ∑' y : α, (φ y - c) * (r y).toReal = 0)
    (hsq : ∑' y : α, ((φ y - c) ^ (2 : ℕ)) * (r y).toReal = v) :
    (∑' y : α, φ y * (r y).toReal = c) ∧
      (∑' y : α, (φ y) ^ (2 : ℕ) * (r y).toReal = c ^ (2 : ℕ) + v) := by
  rw [tsum_fintype] at hr hcentered hsq ⊢
  have hcentered' :
      (∑ y : α, φ y * (r y).toReal) - c * ∑ y : α, (r y).toReal = 0 := by
    -- Proof comment: expand the centered first moment and factor out the constant center `c`.
    calc
      (∑ y : α, φ y * (r y).toReal) - c * ∑ y : α, (r y).toReal
          = (∑ y : α, φ y * (r y).toReal) - ∑ y : α, c * (r y).toReal := by
              rw [← Finset.mul_sum]
      _ = ∑ y : α, (φ y * (r y).toReal - c * (r y).toReal) := by
            rw [← Finset.sum_sub_distrib]
      _ = ∑ y : α, (φ y - c) * (r y).toReal := by
            refine Finset.sum_congr rfl ?_
            intro y _
            ring
      _ = 0 := hcentered
  have hrawMean : ∑ y : α, φ y * (r y).toReal = c := by
    -- Proof comment: the centered first moment vanishes, so the raw mean equals the center `c`.
    calc
      ∑ y : α, φ y * (r y).toReal = c * ∑ y : α, (r y).toReal := by
        linarith [hcentered']
      _ = c := by
            rw [hr]
            ring
  have hsq' :
      (∑ y : α, (φ y) ^ (2 : ℕ) * (r y).toReal) -
          (2 * c) * ∑ y : α, φ y * (r y).toReal +
          c ^ (2 : ℕ) * ∑ y : α, (r y).toReal = v := by
    -- Proof comment: expand the centered square and separate the quadratic, linear, and constant
    -- contributions.
    calc
      (∑ y : α, (φ y) ^ (2 : ℕ) * (r y).toReal) -
          (2 * c) * ∑ y : α, φ y * (r y).toReal +
          c ^ (2 : ℕ) * ∑ y : α, (r y).toReal
          = (∑ y : α, (φ y) ^ (2 : ℕ) * (r y).toReal) -
              ∑ y : α, (2 * c) * (φ y * (r y).toReal) +
              ∑ y : α, c ^ (2 : ℕ) * (r y).toReal := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = ∑ y : α,
            ((φ y) ^ (2 : ℕ) * (r y).toReal - (2 * c) * (φ y * (r y).toReal)) +
              ∑ y : α, c ^ (2 : ℕ) * (r y).toReal := by
              rw [← Finset.sum_sub_distrib]
      _ = ∑ y : α,
            (((φ y) ^ (2 : ℕ) * (r y).toReal - (2 * c) * (φ y * (r y).toReal)) +
              c ^ (2 : ℕ) * (r y).toReal) := by
              rw [← Finset.sum_add_distrib]
      _ = ∑ y : α, ((φ y - c) ^ (2 : ℕ)) * (r y).toReal := by
            refine Finset.sum_congr rfl ?_
            intro y _
            ring
      _ = v := hsq
  constructor
  · simpa [tsum_fintype] using hrawMean
  · -- Proof comment: substituting the recovered raw mean and row mass into the expanded centered
    -- square identity yields the raw second moment.
    have hsqRaw :
        ∑ y : α, (φ y) ^ (2 : ℕ) * (r y).toReal =
          v + (2 * c) * ∑ y : α, φ y * (r y).toReal - c ^ (2 : ℕ) * ∑ y : α, (r y).toReal := by
      linarith [hsq']
    calc
      ∑' y : α, (φ y) ^ (2 : ℕ) * (r y).toReal
          = ∑ y : α, (φ y) ^ (2 : ℕ) * (r y).toReal := by rw [tsum_fintype]
      _ = v + (2 * c) * ∑ y : α, φ y * (r y).toReal - c ^ (2 : ℕ) * ∑ y : α, (r y).toReal :=
            hsqRaw
      _ = c ^ (2 : ℕ) + v := by
            rw [hrawMean, hr]
            ring

/-- Helper for Exercise 17.2.1: the real-valued Moran row entry splits into the three
successor/self/predecessor branches. -/
private lemma moranTransitionMatrix_apply_nat_toReal_local
    (N : ℕ+) (i : Fin (N + 1)) {k : ℕ} (hk : k < N + 1) :
    (moranTransitionMatrix N i ⟨k, hk⟩).toReal =
      (if k = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0) +
        (if k = (i : ℕ) then (moranStayProb N i).toReal else 0) +
          (if (i : ℕ) = k + 1 then (moranMoveProb N i).toReal else 0) := by
  -- Proof comment: the `toReal` row formula has the same three cases as the original
  -- `ENNReal`-valued transition matrix.
  by_cases hsucc : k = (i : ℕ) + 1
  · have himpossible : (i : ℕ) ≠ (i : ℕ) + 1 + 1 := by omega
    simp [moranTransitionMatrix, hsucc, himpossible]
  · by_cases hstay : k = (i : ℕ)
    · simp [moranTransitionMatrix, hstay]
    · by_cases hpred : (i : ℕ) = k + 1
      · have himpossible : k ≠ k + 1 + 1 := by omega
        have hne : (⟨k, hk⟩ : Fin (N + 1)) ≠ i := by
          intro hki
          exact hstay (Fin.ext_iff.mp hki)
        simp [moranTransitionMatrix, hpred, himpossible, hne]
      · have hne : (⟨k, hk⟩ : Fin (N + 1)) ≠ i := by
          intro hki
          exact hstay (Fin.ext_iff.mp hki)
        simp [moranTransitionMatrix, hsucc, hstay, hpred, hne]

/-- Helper for Exercise 17.2.1: summing a successor-indicator weighted term over the Moran state
space collapses to the unique successor index when it exists. -/
private lemma moranSuccessorWeightedSum_local
    (N : ℕ+) (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦
          g j * (if (j : ℕ) = (i : ℕ) + 1 then c else 0)) =
      (if h : (i : ℕ) + 1 < N + 1 then g ⟨(i : ℕ) + 1, h⟩ * c else 0) := by
  by_cases h : (i : ℕ) + 1 < N + 1
  · let jsucc : Fin (N + 1) := ⟨(i : ℕ) + 1, h⟩
    -- Proof comment: in the interior there is exactly one successor index contributing.
    rw [Finset.sum_eq_single_of_mem jsucc (by simp)]
    · simp [jsucc, h]
    · intro j _ hj
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact hj (Fin.ext hji)
      simp [hneq]
  · -- Proof comment: at the upper boundary no successor index exists, so every summand vanishes.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro hji
        exact h (by simpa [hji] using j.2)
      simp [hneq]

/-- Helper for Exercise 17.2.1: summing a stay-indicator weighted term over the Moran state space
collapses to the current state. -/
private lemma moranStayWeightedSum_local
    (N : ℕ+) (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ g j * (if (j : ℕ) = (i : ℕ) then c else 0)) =
      g i * c := by
  -- Proof comment: the stay indicator singles out the present index `i`.
  rw [Finset.sum_eq_single_of_mem i (by simp)]
  · simp
  · intro j _ hj
    have hneq : (j : ℕ) ≠ (i : ℕ) := by
      intro hji
      exact hj (Fin.ext hji)
    simp [hneq]

/-- Helper for Exercise 17.2.1: summing a predecessor-indicator weighted term over the Moran
state space collapses to the unique predecessor index when it exists. -/
private lemma moranPredecessorWeightedSum_local
    (N : ℕ+) (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) (c : ℝ) :
    Finset.sum Finset.univ
        (fun j : Fin (N + 1) ↦ g j * (if (i : ℕ) = (j : ℕ) + 1 then c else 0)) =
      (if h : (i : ℕ) = 0 then 0 else g ⟨(i : ℕ) - 1, by omega⟩ * c) := by
  by_cases h : (i : ℕ) = 0
  · -- Proof comment: at the lower boundary there is no predecessor state.
    rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
      simp [hneq]
  · let jpred : Fin (N + 1) := ⟨(i : ℕ) - 1, by omega⟩
    have hjpred : (i : ℕ) = (jpred : ℕ) + 1 := by
      dsimp [jpred]
      omega
    -- Proof comment: away from `0`, exactly the predecessor index survives.
    rw [Finset.sum_eq_single_of_mem jpred (by simp [jpred])]
    · rw [if_pos hjpred]
      simp [h, jpred]
    · intro j _ hj
      have hneq : (i : ℕ) ≠ (j : ℕ) + 1 := by
        intro hij
        apply hj
        exact Fin.ext (by omega)
      simp [hneq]

/-- Helper for Exercise 17.2.1: collapsing a weighted Moran row once gives a stable three-point
real-valued normal form for later moment calculations. -/
private lemma moranWeightedRowToReal_local
    (N : ℕ+) (i : Fin (N + 1)) (g : Fin (N + 1) → ℝ) :
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      g j * (moranTransitionMatrix N i j).toReal) =
      (if h : (i : ℕ) + 1 < N + 1 then
        g ⟨(i : ℕ) + 1, h⟩ * (moranMoveProb N i).toReal
      else 0) +
        (g i * (moranStayProb N i).toReal +
          (if _h : (i : ℕ) = 0 then
            0
          else
            g ⟨(i : ℕ) - 1, by omega⟩ * (moranMoveProb N i).toReal)) := by
  -- Route correction: normalize the entire Moran row to the successor/self/predecessor interface
  -- once, then collapse the three weighted supports separately.
  calc
    Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
      g j * (moranTransitionMatrix N i j).toReal)
      = Finset.sum Finset.univ (fun j : Fin (N + 1) ↦
          g j *
            ((if (j : ℕ) = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0) +
              ((if (j : ℕ) = (i : ℕ) then (moranStayProb N i).toReal else 0) +
                (if (i : ℕ) = (j : ℕ) + 1 then (moranMoveProb N i).toReal else 0)))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          simpa [add_assoc] using congrArg (fun t : ℝ ↦ g j * t)
            (moranTransitionMatrix_apply_nat_toReal_local N i (k := (j : ℕ)) j.2)
    _ = Finset.sum Finset.univ
          (fun j : Fin (N + 1) ↦
            g j * (if (j : ℕ) = (i : ℕ) + 1 then (moranMoveProb N i).toReal else 0)) +
        (Finset.sum Finset.univ
          (fun j : Fin (N + 1) ↦
            g j * (if (j : ℕ) = (i : ℕ) then (moranStayProb N i).toReal else 0)) +
          Finset.sum Finset.univ
            (fun j : Fin (N + 1) ↦
              g j * (if (i : ℕ) = (j : ℕ) + 1 then (moranMoveProb N i).toReal else 0))) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (if h : (i : ℕ) + 1 < N + 1 then
          g ⟨(i : ℕ) + 1, h⟩ * (moranMoveProb N i).toReal
        else 0) +
        (g i * (moranStayProb N i).toReal +
          (if _h : (i : ℕ) = 0 then
            0
          else
            g ⟨(i : ℕ) - 1, by omega⟩ * (moranMoveProb N i).toReal)) := by
          rw [moranSuccessorWeightedSum_local, moranStayWeightedSum_local,
            moranPredecessorWeightedSum_local]

/-- Helper for Exercise 17.2.1: the real-valued Moran local masses also sum to `1`. -/
private lemma moranLocalMass_sum_one_toReal_local
    (N : ℕ+) (i : Fin (N + 1)) :
    (moranMoveProb N i).toReal + (moranStayProb N i).toReal + (moranMoveProb N i).toReal = 1 := by
  -- Proof comment: removing `ENNReal.ofReal` reduces the mass identity to the textbook
  -- polynomial relation.
  rw [moranMoveProb_toReal_local, moranStayProb_toReal_local]
  ring

/-- Helper for Exercise 17.2.1: averaging the Moran frequency over one canonical row returns the
current frequency. -/
private lemma moranFrequencyMeanStep_local
    (N : ℕ+) (i : Fin (N + 1)) :
    ∑' j : Fin (N + 1), moranFrequency N j * (moranTransitionMatrix N i j).toReal =
      moranFrequency N i := by
  rw [tsum_fintype]
  by_cases hzero : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext hzero
    have hsucc : (i : ℕ) + 1 < N + 1 := by simp [hzero]
    -- Proof comment: at the lower boundary the move mass vanishes, so only the stay term
    -- contributes.
    simp [moranWeightedRowToReal_local, hi, moranFrequency_zero_local, moranMoveProb_toReal_local,
      moranStayProb_toReal_local, hsucc]
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · -- Proof comment: in the interior the successor and predecessor shifts cancel, leaving the
      -- current frequency times the total row mass.
      calc
        ∑ j : Fin (N + 1), moranFrequency N j * (moranTransitionMatrix N i j).toReal
            = (moranFrequency N i + 1 / N) * (moranMoveProb N i).toReal +
                (moranFrequency N i * (moranStayProb N i).toReal +
                  (moranFrequency N i - 1 / N) * (moranMoveProb N i).toReal) := by
                  simp [moranWeightedRowToReal_local, hzero, hsucc, moranFrequency_succ_local,
                    moranFrequency_pred_local]
        _ = moranFrequency N i *
              ((moranMoveProb N i).toReal + (moranStayProb N i).toReal +
                (moranMoveProb N i).toReal) := by
              ring
        _ = moranFrequency N i * 1 := by
              rw [moranLocalMass_sum_one_toReal_local]
        _ = moranFrequency N i := by
              ring
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      -- Proof comment: at the upper boundary the move mass again vanishes and the row stays put.
      simp [moranWeightedRowToReal_local, hi, moranFrequency_last_local, moranMoveProb_toReal_local,
        moranStayProb_toReal_local, hsucc]

/-- Helper for Exercise 17.2.1: the canonical Moran row has centered squared increment equal to
the explicit density from formula `(17.12)`. -/
private lemma moranSquaredIncrementMeanStep_local
    (N : ℕ+) (i : Fin (N + 1)) :
    ∑' j : Fin (N + 1),
      (moranFrequency N j - moranFrequency N i) ^ (2 : ℕ) *
        (moranTransitionMatrix N i j).toReal =
      moranSquareVariationDensity N i := by
  rw [tsum_fintype]
  by_cases hzero : (i : ℕ) = 0
  · have hi : i = 0 := Fin.ext hzero
    have hsucc : (i : ℕ) + 1 < N + 1 := by simp [hzero]
    -- Proof comment: at the lower boundary the chain does not move, so the centered square is
    -- identically zero.
    simp [moranWeightedRowToReal_local, hi, moranFrequency_zero_local, moranMoveProb_toReal_local,
      moranStayProb_toReal_local, moranSquareVariationDensity, hsucc]
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · -- Proof comment: in the interior only the two neighbors contribute, each with squared
      -- increment `(1 / N)^2`.
      calc
        ∑ j : Fin (N + 1),
            (moranFrequency N j - moranFrequency N i) ^ (2 : ℕ) *
              (moranTransitionMatrix N i j).toReal
            = ((1 / N : ℝ) ^ (2 : ℕ)) * (moranMoveProb N i).toReal +
                (0 * (moranStayProb N i).toReal +
                  ((1 / N : ℝ) ^ (2 : ℕ)) * (moranMoveProb N i).toReal) := by
                    simp [moranWeightedRowToReal_local, hzero, hsucc, moranFrequency_succ_local,
                      moranFrequency_pred_local]
        _ = moranSquareVariationDensity N i := by
              rw [moranMoveProb_toReal_local, moranSquareVariationDensity]
              ring
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      -- Proof comment: the upper boundary is also absorbing, so the centered square is zero.
      simp [moranWeightedRowToReal_local, hi, moranFrequency_last_local, moranMoveProb_toReal_local,
        moranStayProb_toReal_local, moranSquareVariationDensity, hsucc]

-- Proof sketch: at a fixed Moran count state `i`, the row support lies in the three neighboring
-- count states. The stochastic-row equation together with the zero drift and the explicit
-- square-variation density from `(17.12)`, written via `moranFrequency`, determines the three row
-- entries uniquely, so the row must equal the corresponding row of `moranTransitionMatrix N`.
/-- Auxiliary Moran rowwise uniqueness statement: at a fixed Moran count state `i`, the zero
drift and the explicit square-variation formula `(17.12)` determine the transition row to be the
corresponding row of `moranTransitionMatrix N`. -/
theorem moranTransitionMatrix_row_of_squareVariationFormula
    {N : ℕ+} {p : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞} (hp : IsStochasticMatrix p)
    {i : Fin (N + 1)}
    (h_support : ∀ j : Fin (N + 1), p i j ≠ 0 →
      (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1)
    (hd :
      ∑' j : Fin (N + 1), ((moranFrequency N j - moranFrequency N i) * (p i j).toReal) = 0)
    (hf :
      ∑' j : Fin (N + 1),
        (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) * (p i j).toReal) =
          moranSquareVariationDensity N i) :
    p i = moranTransitionMatrix N i := by
  let q : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞ := moranTransitionMatrix N
  have hq : IsStochasticMatrix q := by
    simpa [q] using moranTransitionMatrix_isStochasticMatrix (N := N)
  have hpRaw :
      (∑' j : Fin (N + 1), moranFrequency N j * (p i j).toReal = moranFrequency N i) ∧
        (∑' j : Fin (N + 1), (moranFrequency N j) ^ (2 : ℕ) * (p i j).toReal =
          moranFrequency N i ^ (2 : ℕ) + moranSquareVariationDensity N i) := by
    -- Proof comment: the hypotheses `hd` and `hf` are centered moments, so first recover the
    -- corresponding raw first and second moments of the unknown row.
    exact
      centeredRowMoments_to_rawMoments
        (hr := stochasticRow_tsum_toReal hp i)
        (φ := moranFrequency N) (c := moranFrequency N i) (v := moranSquareVariationDensity N i)
        hd hf
  have hqCenteredMean :
      ∑' j : Fin (N + 1), (moranFrequency N j - moranFrequency N i) * (q i j).toReal = 0 := by
    -- Proof comment: the canonical Moran row has raw mean `moranFrequency N i`, hence centered
    -- mean zero.
    have hMean : ∑ j : Fin (N + 1), moranFrequency N j * (q i j).toReal = moranFrequency N i := by
      simpa [q, tsum_fintype] using moranFrequencyMeanStep_local N i
    have hRow : ∑ j : Fin (N + 1), (q i j).toReal = 1 := by
      simpa [tsum_fintype] using (stochasticRow_tsum_toReal hq i)
    have hCenteredFin :
        ∑ j : Fin (N + 1), (moranFrequency N j - moranFrequency N i) * (q i j).toReal = 0 := by
      calc
        ∑ j : Fin (N + 1), (moranFrequency N j - moranFrequency N i) * (q i j).toReal
            = ∑ j : Fin (N + 1), moranFrequency N j * (q i j).toReal -
                moranFrequency N i * ∑ j : Fin (N + 1), (q i j).toReal := by
                  calc
                    ∑ j : Fin (N + 1), (moranFrequency N j - moranFrequency N i) * (q i j).toReal
                        = ∑ j : Fin (N + 1),
                            (moranFrequency N j * (q i j).toReal -
                              moranFrequency N i * (q i j).toReal) := by
                                refine Finset.sum_congr rfl ?_
                                intro j _
                                ring
                    _ = ∑ j : Fin (N + 1), moranFrequency N j * (q i j).toReal -
                          ∑ j : Fin (N + 1), moranFrequency N i * (q i j).toReal := by
                            rw [Finset.sum_sub_distrib]
                    _ = ∑ j : Fin (N + 1), moranFrequency N j * (q i j).toReal -
                          moranFrequency N i * ∑ j : Fin (N + 1), (q i j).toReal := by
                            rw [← Finset.mul_sum]
        _ = moranFrequency N i - moranFrequency N i * 1 := by
              rw [hMean, hRow]
        _ = 0 := by
              ring
    simpa [tsum_fintype] using hCenteredFin
  have hqRaw :
      (∑' j : Fin (N + 1), moranFrequency N j * (q i j).toReal = moranFrequency N i) ∧
        (∑' j : Fin (N + 1), (moranFrequency N j) ^ (2 : ℕ) * (q i j).toReal =
          moranFrequency N i ^ (2 : ℕ) + moranSquareVariationDensity N i) := by
    -- Proof comment: apply the same centered-to-raw conversion to the canonical Moran row.
    exact
      centeredRowMoments_to_rawMoments
        (hr := stochasticRow_tsum_toReal hq i)
        (φ := moranFrequency N) (c := moranFrequency N i) (v := moranSquareVariationDensity N i)
        hqCenteredMean (by simpa [q] using moranSquaredIncrementMeanStep_local N i)
  rcases hpRaw with ⟨hpMean, hpSq⟩
  rcases hqRaw with ⟨hqMean, hqSq⟩
  have hMeanEq :
      ∑' j : Fin (N + 1), moranFrequency N j * (p i j).toReal =
        ∑' j : Fin (N + 1), moranFrequency N j * (q i j).toReal := by
    exact hpMean.trans hqMean.symm
  have hSqEq :
      ∑' j : Fin (N + 1), (moranFrequency N j) ^ (2 : ℕ) * (p i j).toReal =
        ∑' j : Fin (N + 1), (moranFrequency N j) ^ (2 : ℕ) * (q i j).toReal := by
    exact hpSq.trans hqSq.symm
  by_cases hzero : (i : ℕ) = 0
  · let jsucc : Fin (N + 1) := ⟨(i : ℕ) + 1, by simp [hzero]⟩
    have hpAx : ∀ j : Fin (N + 1), p i j ≠ 0 → j = jsucc ∨ j = i ∨ j = i := by
      intro j hj
      rcases h_support j hj with hsucc | hstay | hpred
      · exact Or.inl (Fin.ext hsucc)
      · exact Or.inr (Or.inl hstay)
      · omega
    have hqAx : ∀ j : Fin (N + 1), q i j ≠ 0 → j = jsucc ∨ j = i ∨ j = i := by
      intro j hj
      rcases moranTransitionMatrix_support_local N hj with hsucc | hstay | hpred
      · exact Or.inl (Fin.ext hsucc)
      · exact Or.inr (Or.inl hstay)
      · omega
    -- Proof comment: at the lower boundary the common three-point support degenerates to the pair
    -- `{i, i+1}`, and the finished reconstruction lemma handles that duplicate automatically.
    simpa [q] using
      (threePointSupport_row_eq_of_moments_eq
        (φ := moranFrequency N) (moranFrequency_injective_local N) hp hq hpAx hqAx hMeanEq hSqEq)
  · by_cases hsucc : (i : ℕ) + 1 < N + 1
    · let jsucc : Fin (N + 1) := ⟨(i : ℕ) + 1, hsucc⟩
      let jpred : Fin (N + 1) := ⟨(i : ℕ) - 1, by omega⟩
      have hpAx : ∀ j : Fin (N + 1), p i j ≠ 0 → j = jsucc ∨ j = i ∨ j = jpred := by
        intro j hj
        rcases h_support j hj with hnext | hstay | hprev
        · exact Or.inl (Fin.ext hnext)
        · exact Or.inr (Or.inl hstay)
        · have hjpred : (j : ℕ) = (i : ℕ) - 1 := by omega
          exact Or.inr (Or.inr (Fin.ext hjpred))
      have hqAx : ∀ j : Fin (N + 1), q i j ≠ 0 → j = jsucc ∨ j = i ∨ j = jpred := by
        intro j hj
        rcases moranTransitionMatrix_support_local N hj with hnext | hstay | hprev
        · exact Or.inl (Fin.ext hnext)
        · exact Or.inr (Or.inl hstay)
        · have hjpred : (j : ℕ) = (i : ℕ) - 1 := by omega
          exact Or.inr (Or.inr (Fin.ext hjpred))
      -- Proof comment: in the genuine interior case the common support is the predecessor/self/
      -- successor triple, so the three-moment reconstruction lemma applies directly.
      simpa [q] using
        (threePointSupport_row_eq_of_moments_eq
          (φ := moranFrequency N) (moranFrequency_injective_local N) hp hq hpAx hqAx hMeanEq
          hSqEq)
    · have hiVal : (i : ℕ) = N := by omega
      have hi : i = Fin.last N := Fin.ext hiVal
      let jpred : Fin (N + 1) := ⟨(i : ℕ) - 1, by omega⟩
      have hpAx : ∀ j : Fin (N + 1), p i j ≠ 0 → j = i ∨ j = i ∨ j = jpred := by
        intro j hj
        rcases h_support j hj with hnext | hstay | hprev
        · omega
        · exact Or.inl hstay
        · have hjpred : (j : ℕ) = (i : ℕ) - 1 := by omega
          exact Or.inr (Or.inr (Fin.ext hjpred))
      have hqAx : ∀ j : Fin (N + 1), q i j ≠ 0 → j = i ∨ j = i ∨ j = jpred := by
        intro j hj
        rcases moranTransitionMatrix_support_local N hj with hnext | hstay | hprev
        · omega
        · exact Or.inl hstay
        · have hjpred : (j : ℕ) = (i : ℕ) - 1 := by omega
          exact Or.inr (Or.inr (Fin.ext hjpred))
      -- Proof comment: at the upper boundary the support degenerates to `{i-1, i}`, which the
      -- duplicate-aware reconstruction lemma again handles automatically.
      simpa [q, hi] using
        (threePointSupport_row_eq_of_moments_eq
          (φ := moranFrequency N) (moranFrequency_injective_local N) hp hq hpAx hqAx hMeanEq
          hSqEq)

-- Proof sketch: apply the rowwise Moran uniqueness statement at each state `i`.
/-- Exercise 17.2.1 (3): for the discrete Moran model of Example 17.22, the zero drift and the
explicit square-variation formula `(17.12)` determine the transition matrix itself to be the
canonical Moran matrix `moranTransitionMatrix N`. -/
theorem moranTransitionMatrix_eq_of_squareVariationFormula
    {N : ℕ+} {p : Fin (N + 1) → Fin (N + 1) → ℝ≥0∞} (hp : IsStochasticMatrix p)
    (h_support :
      ∀ i : Fin (N + 1), ∀ j : Fin (N + 1), p i j ≠ 0 →
        (j : ℕ) = (i : ℕ) + 1 ∨ j = i ∨ (i : ℕ) = (j : ℕ) + 1)
    (hd :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1), ((moranFrequency N j - moranFrequency N i) * (p i j).toReal) = 0)
    (hf :
      ∀ i : Fin (N + 1),
        ∑' j : Fin (N + 1),
          (((moranFrequency N j - moranFrequency N i) ^ (2 : ℕ)) * (p i j).toReal) =
            moranSquareVariationDensity N i) :
    p = moranTransitionMatrix N := by
  -- Proof comment: the rowwise Moran characterization already identifies each row `p i`.
  funext i
  exact moranTransitionMatrix_row_of_squareVariationFormula hp (h_support i) (hd i) (hf i)

end ProbabilityTheory

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [mE : MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Lemma 17.45: bounded range makes every sampled value `f (X n)` integrable under
the realization measure `(P x : Measure Ω)`. -/
lemma integrable_comp_process_of_boundedRange
    {f : E → ℝ} (hX_meas : ∀ n : ℕ, Measurable (X n))
    (hf_bdd : Bornology.IsBounded (Set.range f)) (x : E) :
    ∀ n, Integrable (fun ω ↦ f (X n ω)) (P x : Measure Ω) := by
  intro n
  obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
  let μ : Measure Ω := (P x : Measure Ω)
  -- Proof comment: bounded range gives a uniform deterministic `L¹` bound on the sampled process.
  refine Integrable.mono' (integrable_const R)
    ((Measurable.of_discrete.comp (hX_meas n)).aestronglyMeasurable)
    ?_
  filter_upwards with ω
  simpa using hR (f (X n ω)) ⟨X n ω, rfl⟩

/-- Helper for Lemma 17.45: on an event from the time-`n` history, the restricted law of
`X (n + 1)` is obtained by composing the restricted law of `X n` with the one-step discrete
kernel. -/
lemma restrictMap_succ_eq_discreteKernelComp
    (x : E) (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ((P x : Measure Ω).restrict s).map (X (n + 1)) =
      (discreteMatrixKernel p) ∘ₘ (((P x : Measure Ω).restrict s).map (X n)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hX_meas : ∀ k : ℕ, Measurable (X k) := hReal.measurable_process
  have hs_meas : MeasurableSet s := hs.1
  have hs_generated : MeasurableSet[generatedFiltrationSpace X n] s := hs.2
  have hgenerated_le : generatedFiltrationSpace X n ≤ mΩ := by
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
      -- Proof comment: the realization Markov property turns a future state event into the
      -- one-step transition probability from the present state.
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
      -- Proof comment: push the kernel mass function back through the restricted current-state law.
      change ∫ y, ((discreteMatrixKernel p) y).real A ∂((μ.restrict s).map (X n)) =
        ∫ ω, ((discreteMatrixKernel p) (X n ω)).real A ∂(μ.restrict s)
      rw [MeasureTheory.integral_map
        (IsMarkovProcessRealization.measurable_process
          (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X) n).aemeasurable
        hkernel_int.aestronglyMeasurable]
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
      (s := A) (t := A) hleft_ne_top hright_ne_top).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Lemma 17.45: harmonicity turns the one-step restricted kernel average of `f`
along the chain into equality of the time-`n` and time-`n+1` set integrals. -/
lemma harmonicSetIntegralSuccEq
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (x : E)
    (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ∫ ω in s, f (X n ω) ∂(P x : Measure Ω) =
      ∫ ω in s, f (X (n + 1) ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure E := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  rcases (isHarmonic_iff (p := discreteMatrixKernel p) (f := f)).mp hf_harmonic with
    ⟨_, hharmonic⟩
  have hcurrent_int : Integrable f ν := by
    -- Proof comment: integrability transfers from the bounded sampled process to its restricted
    -- pushed-forward law.
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X n) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process n).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x n).restrict
  have hnext_int : Integrable f (((μ.restrict s).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X (n + 1)) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x (n + 1)).restrict
  have hcomp_int : Integrable f ((discreteMatrixKernel p) ∘ₘ ν) := by
    -- Proof comment: the restricted next-step law already equals the kernel composition law.
    simpa [ν] using
      (restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs ▸ hnext_int)
  have hcurrent_map :
      ∫ y, f y ∂ν = ∫ ω in s, f (X n ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X n)) = ∫ ω, f (X n ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hcurrent_int.aestronglyMeasurable]
  have hnext_map :
      ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ ω in s, f (X (n + 1) ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
      ∫ ω, f (X (n + 1) ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hnext_int.aestronglyMeasurable]
  have hcomp_integral :
      ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
        ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
    rw [restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs]
    calc
      ∫ y, f y ∂((discreteMatrixKernel p) ∘ₘ ν)
          = ∫ y, f y ∂((discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
              rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
      _ = ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
            exact
              ProbabilityTheory.Kernel.integral_comp
                (η := discreteMatrixKernel p) (κ := ProbabilityTheory.Kernel.const Unit ν)
                (a := ()) <| by
                  rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
                  exact hcomp_int
  have hharmonic_integral :
      ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν = ∫ y, f y ∂ν := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun y ↦ (hharmonic y).symm
  -- Proof comment: the one-step law becomes a kernel average, and harmonicity collapses that
  -- average back to the present sampled value.
  calc
    ∫ ω in s, f (X n ω) ∂μ = ∫ y, f y ∂ν := hcurrent_map.symm
    _ = ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := hharmonic_integral.symm
    _ = ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) := hcomp_integral.symm
    _ = ∫ ω in s, f (X (n + 1) ω) ∂μ := hnext_map

/-- Helper for Lemma 17.45: subharmonicity makes the one-step kernel average dominate the present
sampled value on every history event. -/
lemma subharmonicSetIntegralLeSucc
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_subharmonic : IsSubharmonic (discreteMatrixKernel p) f) (x : E)
    (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ∫ ω in s, f (X n ω) ∂(P x : Measure Ω) ≤
      ∫ ω in s, f (X (n + 1) ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure E := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  rcases (isSubharmonic_iff (p := discreteMatrixKernel p) (f := f)).mp hf_subharmonic with
    ⟨hrow_int, hsubharmonic⟩
  have hcurrent_int : Integrable f ν := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X n) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process n).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x n).restrict
  have hnext_int : Integrable f (((μ.restrict s).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X (n + 1)) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x (n + 1)).restrict
  have hcomp_int : Integrable f ((discreteMatrixKernel p) ∘ₘ ν) := by
    simpa [ν] using
      (restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs ▸ hnext_int)
  have haverage_sm : StronglyMeasurable (fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y) :=
    (Measurable.of_discrete :
      Measurable fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y).stronglyMeasurable
  have haverage_int : Integrable (fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y) ν := by
    refine Integrable.mono
      (MeasureTheory.Measure.integrable_integral_norm_of_integrable_comp
        (μ := ν) (κ := discreteMatrixKernel p) (f := f) hcomp_int)
      haverage_sm.aestronglyMeasurable ?_
    filter_upwards with y
    calc
      ‖∫ z, f z ∂discreteMatrixKernel p y‖ ≤ ∫ z, ‖f z‖ ∂discreteMatrixKernel p y := by
        exact norm_integral_le_integral_norm (f := f)
      _ = ‖∫ z, ‖f z‖ ∂discreteMatrixKernel p y‖ := by
        rw [Real.norm_of_nonneg]
        exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  have hcurrent_map :
      ∫ y, f y ∂ν = ∫ ω in s, f (X n ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X n)) = ∫ ω, f (X n ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hcurrent_int.aestronglyMeasurable]
  have hnext_map :
      ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ ω in s, f (X (n + 1) ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
      ∫ ω, f (X (n + 1) ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hnext_int.aestronglyMeasurable]
  have hcomp_integral :
      ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
        ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
    rw [restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs]
    calc
      ∫ y, f y ∂((discreteMatrixKernel p) ∘ₘ ν)
          = ∫ y, f y ∂((discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
              rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
      _ = ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
            exact
              ProbabilityTheory.Kernel.integral_comp
                (η := discreteMatrixKernel p) (κ := ProbabilityTheory.Kernel.const Unit ν)
                (a := ()) <| by
                  rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
                  exact hcomp_int
  -- Proof comment: the restricted next-step integral is the integral of the one-step averages,
  -- and subharmonicity compares those averages pointwise to `f`.
  calc
    ∫ ω in s, f (X n ω) ∂μ = ∫ y, f y ∂ν := hcurrent_map.symm
    _ ≤ ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
          refine MeasureTheory.integral_mono_ae hcurrent_int haverage_int ?_
          exact Filter.Eventually.of_forall hsubharmonic
    _ = ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) := hcomp_integral.symm
    _ = ∫ ω in s, f (X (n + 1) ω) ∂μ := hnext_map

/-- Helper for Lemma 17.45: superharmonicity makes the one-step kernel average stay below the
present sampled value on every history event. -/
lemma superharmonicSetIntegralSuccLe
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_superharmonic : IsSuperharmonic (discreteMatrixKernel p) f) (x : E)
    (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ∫ ω in s, f (X (n + 1) ω) ∂(P x : Measure Ω) ≤
      ∫ ω in s, f (X n ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure E := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  rcases (isSuperharmonic_iff (p := discreteMatrixKernel p) (f := f)).mp hf_superharmonic with
    ⟨hrow_int, hsuperharmonic⟩
  have hcurrent_int : Integrable f ν := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X n) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process n).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x n).restrict
  have hnext_int : Integrable f (((μ.restrict s).map (X (n + 1)))) := by
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X (n + 1)) (g := f)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hf_bdd x (n + 1)).restrict
  have hcomp_int : Integrable f ((discreteMatrixKernel p) ∘ₘ ν) := by
    simpa [ν] using
      (restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs ▸ hnext_int)
  have haverage_sm : StronglyMeasurable (fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y) :=
    (Measurable.of_discrete :
      Measurable fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y).stronglyMeasurable
  have haverage_int : Integrable (fun y : E ↦ ∫ z, f z ∂discreteMatrixKernel p y) ν := by
    refine Integrable.mono
      (MeasureTheory.Measure.integrable_integral_norm_of_integrable_comp
        (μ := ν) (κ := discreteMatrixKernel p) (f := f) hcomp_int)
      haverage_sm.aestronglyMeasurable ?_
    filter_upwards with y
    calc
      ‖∫ z, f z ∂discreteMatrixKernel p y‖ ≤ ∫ z, ‖f z‖ ∂discreteMatrixKernel p y := by
        exact norm_integral_le_integral_norm (f := f)
      _ = ‖∫ z, ‖f z‖ ∂discreteMatrixKernel p y‖ := by
        rw [Real.norm_of_nonneg]
        exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  have hcurrent_map :
      ∫ y, f y ∂ν = ∫ ω in s, f (X n ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X n)) = ∫ ω, f (X n ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hcurrent_int.aestronglyMeasurable]
  have hnext_map :
      ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ ω in s, f (X (n + 1) ω) ∂μ := by
    change ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
      ∫ ω, f (X (n + 1) ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hnext_int.aestronglyMeasurable]
  have hcomp_integral :
      ∫ y, f y ∂((μ.restrict s).map (X (n + 1))) =
        ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
    rw [restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs]
    calc
      ∫ y, f y ∂((discreteMatrixKernel p) ∘ₘ ν)
          = ∫ y, f y ∂((discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
              rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
      _ = ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := by
            exact
              ProbabilityTheory.Kernel.integral_comp
                (η := discreteMatrixKernel p) (κ := ProbabilityTheory.Kernel.const Unit ν)
                (a := ()) <| by
                  rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
                  exact hcomp_int
  -- Proof comment: the same transport as in the harmonic case now uses the superharmonic
  -- inequality in the opposite direction.
  calc
    ∫ ω in s, f (X (n + 1) ω) ∂μ = ∫ y, f y ∂(((μ.restrict s).map (X (n + 1)))) := hnext_map.symm
    _ = ∫ y, ∫ z, f z ∂discreteMatrixKernel p y ∂ν := hcomp_integral
    _ ≤ ∫ y, f y ∂ν := by
          refine MeasureTheory.integral_mono_ae haverage_int hcurrent_int ?_
          exact Filter.Eventually.of_forall hsuperharmonic
    _ = ∫ ω in s, f (X n ω) ∂μ := hcurrent_map

-- Proof sketch: use the one-step Markov property for the realization of `p` to identify the
-- conditional expectation of `f (X (n + 1))` given the past with the one-step averaging operator
-- `y ↦ ∫ z, f z ∂ discreteMatrixKernel p y`, evaluated at `X n`; the harmonicity hypothesis turns
-- this conditional expectation into `f (X n)`, and boundedness supplies the required
-- integrability.
/-- Lemma 17.45 (1): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is harmonic for the owner kernel `discreteMatrixKernel p`, then the process
`(f (X_n))_n` is a martingale with respect to the natural filtration of `X`. -/
theorem harmonicFunction_comp_martingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (x : E) :
    Martingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hX_meas : ∀ n : ℕ, Measurable (X n) :=
    IsMarkovProcessRealization.measurable_process
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X)
  have hX_adapted : Adapted (processFiltration X) X := by
    intro n
    -- Proof comment: the time-`n` state is one of the defining generators of its natural
    -- filtration.
    refine measurable_iff_comap_le.2 ?_
    exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
      refine le_iSup_of_le n ?_
      refine le_iSup_of_le le_rfl ?_
      exact le_rfl
  have hF_stronglyAdapted : StronglyAdapted (processFiltration X) (fun n ω ↦ f (X n ω)) := by
    intro n
    -- Proof comment: composing the adapted state variable with the discrete measurable `f`
    -- preserves strong measurability at time `n`.
    exact (Measurable.of_discrete.comp (hX_adapted n)).stronglyMeasurable
  have hF_integrable : ∀ n, Integrable (fun ω ↦ f (X n ω)) μ :=
    integrable_comp_process_of_boundedRange
      (P := P) (X := X)
      (IsMarkovProcessRealization.measurable_process (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (P := P) (X := X))
      hf_bdd x
  -- Proof comment: the set-integral equality from harmonicity is exactly the hypothesis required
  -- by the martingale constructor.
  exact MeasureTheory.martingale_of_setIntegral_eq_succ hF_stronglyAdapted hF_integrable
    (harmonicSetIntegralSuccEq (P := P) (X := X) (p := p) hf_bdd hf_harmonic x)

-- Proof sketch: the same one-step conditional-expectation computation gives
-- `f (X n) ≤ E[f (X (n + 1)) | 𝓕_n]` almost surely, because subharmonicity says the one-step
-- averaged value dominates `f`; boundedness gives integrability of every `f (X n)`.
/-- Lemma 17.45 (2): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is subharmonic for the owner kernel `discreteMatrixKernel p`, then the
process
`(f (X_n))_n` is a submartingale with respect to the natural filtration of `X`. -/
theorem subharmonicFunction_comp_submartingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_subharmonic : IsSubharmonic (discreteMatrixKernel p) f) (x : E) :
    Submartingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hX_meas : ∀ n : ℕ, Measurable (X n) :=
    IsMarkovProcessRealization.measurable_process
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X)
  have hX_adapted : Adapted (processFiltration X) X := by
    intro n
    -- Proof comment: the current state is measurable with respect to its own history sigma
    -- algebra.
    refine measurable_iff_comap_le.2 ?_
    exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
      refine le_iSup_of_le n ?_
      refine le_iSup_of_le le_rfl ?_
      exact le_rfl
  have hF_stronglyAdapted : StronglyAdapted (processFiltration X) (fun n ω ↦ f (X n ω)) := by
    intro n
    -- Proof comment: measurable composition with `f` preserves strong adaptedness.
    exact (Measurable.of_discrete.comp (hX_adapted n)).stronglyMeasurable
  have hF_integrable : ∀ n, Integrable (fun ω ↦ f (X n ω)) μ :=
    integrable_comp_process_of_boundedRange
      (P := P) (X := X)
      (IsMarkovProcessRealization.measurable_process (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (P := P) (X := X))
      hf_bdd x
  -- Proof comment: the subharmonic set-integral inequality is the one-step submartingale
  -- criterion.
  exact MeasureTheory.submartingale_of_setIntegral_le_succ hF_stronglyAdapted hF_integrable
    (subharmonicSetIntegralLeSucc (P := P) (X := X) (p := p) hf_bdd hf_subharmonic x)

-- Proof sketch: identify the conditional expectation of `f (X (n + 1))` given the past with the
-- one-step averaging operator applied at `X n`; the superharmonicity inequality shows this
-- conditional expectation is almost surely bounded above by `f (X n)`, and boundedness yields the
-- needed integrability.
/-- Lemma 17.45 (3): for a realization of the discrete chain with transition matrix `p`, if `f`
has bounded range and is superharmonic for the owner kernel `discreteMatrixKernel p`, then the
process
`(f (X_n))_n` is a supermartingale with respect to the natural filtration of `X`. -/
theorem superharmonicFunction_comp_supermartingale
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_superharmonic : IsSuperharmonic (discreteMatrixKernel p) f) (x : E) :
    Supermartingale (fun n ω ↦ f (X n ω)) (processFiltration X) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hX_meas : ∀ n : ℕ, Measurable (X n) :=
    IsMarkovProcessRealization.measurable_process
      (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) (P := P) (X := X)
  have hX_adapted : Adapted (processFiltration X) X := by
    intro n
    -- Proof comment: the present coordinate is measurable with respect to the natural history.
    refine measurable_iff_comap_le.2 ?_
    exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
      refine le_iSup_of_le n ?_
      refine le_iSup_of_le le_rfl ?_
      exact le_rfl
  have hF_stronglyAdapted : StronglyAdapted (processFiltration X) (fun n ω ↦ f (X n ω)) := by
    intro n
    -- Proof comment: strong measurability again comes from composing the adapted state with
    -- the discrete measurable function `f`.
    exact (Measurable.of_discrete.comp (hX_adapted n)).stronglyMeasurable
  have hF_integrable : ∀ n, Integrable (fun ω ↦ f (X n ω)) μ :=
    integrable_comp_process_of_boundedRange
      (P := P) (X := X)
      (IsMarkovProcessRealization.measurable_process (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (P := P) (X := X))
      hf_bdd x
  -- Proof comment: the superharmonic inequality gives the one-step supermartingale criterion on
  -- every history event.
  exact MeasureTheory.supermartingale_of_setIntegral_succ_le hF_stronglyAdapted hF_integrable
    (superharmonicSetIntegralSuccLe (P := P) (X := X) (p := p) hf_bdd hf_superharmonic x)

end

end ProbabilityTheory

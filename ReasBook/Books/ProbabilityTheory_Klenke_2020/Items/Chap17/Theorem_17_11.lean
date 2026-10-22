/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Corollary_14_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: the kernels `κ₁ ^ n` are stochastic by induction from `IsMarkovKernel κ₁`, the
-- zero-time kernel is `Kernel.id`, and the Chapman--Kolmogorov law is `Kernel.pow_add`.
/-- The powers of a one-step stochastic kernel form the discrete-time Markov semigroup of its
`n`-step transition kernels. -/
instance isMarkovSemigroup_kernelPowers (κ₁ : Kernel E E) [IsMarkovKernel κ₁] :
    IsMarkovSemigroup (fun n : ℕ ↦ κ₁ ^ n) := by
  refine
    { isMarkovKernel := fun n ↦ ?_
      zero_eq := by rfl
      comp_eq := ?_ }
  · -- Proof comment: powers of a Markov kernel stay Markov by the standard kernel composition
    -- induction.
    induction n with
    | zero =>
        simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
    | succ n ih =>
        simpa [pow_succ] using (inferInstance : IsMarkovKernel ((κ₁ ^ n) ∘ₖ κ₁))
  · intro s t
    -- Proof comment: the Chapman--Kolmogorov identity for kernel powers is `Kernel.pow_add`,
    -- followed by the commutativity of addition on `ℕ`.
    calc
      (κ₁ ^ t) ∘ₖ (κ₁ ^ s) = κ₁ ^ (t + s) := by
        simpa using (Kernel.pow_add κ₁ t s).symm
      _ = κ₁ ^ (s + t) := by simp [Nat.add_comm]

/-- Every power of a Markov kernel is again a Markov kernel. -/
instance isMarkovKernel_kernelPow (κ₁ : Kernel E E) [IsMarkovKernel κ₁] (n : ℕ) :
    IsMarkovKernel (κ₁ ^ n) := by
  induction n with
  | zero =>
      simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
  | succ n ih =>
      simpa [pow_succ] using (inferInstance : IsMarkovKernel ((κ₁ ^ n) ∘ₖ κ₁))

section

variable {Ω : Type v} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 17.11: the present-state sigma-algebra is contained in the generated
history sigma-algebra at the same time. -/
lemma present_le_generatedFiltrationSpace
    (X : ℕ → Ω → E) (s : ℕ) :
    MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ generatedFiltrationSpace X s := by
  -- Proof comment: the defining supremum already contains the generator coming from time `s`
  -- itself.
  exact le_iSup₂_of_le s le_rfl le_rfl

/-- Helper for Theorem 17.11: the generated history filtration of a measurable process lives
inside the ambient measurable space. -/
lemma generatedFiltrationSpace_le_ambient
    {Ω' : Type*} [MeasurableSpace Ω'] {F : Type*} [MeasurableSpace F]
    (X : ℕ → Ω' → F) (hX : ∀ n : ℕ, Measurable (X n)) (s : ℕ) :
    generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω'› := by
  -- Proof comment: every coordinate sigma-algebra in the defining supremum is ambient because
  -- the corresponding coordinate map is measurable.
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  exact (hX r).comap_le

/-- Helper for Theorem 17.11: a finite history tuple is measurable once each sampled coordinate is
measurable. -/
lemma measurable_historyTuple {n : ℕ}
    (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ)
    (hX : ∀ t : ℕ, Measurable (X t)) :
    Measurable (fun ω k ↦ X (times k) ω) := by
  -- Proof comment: measurability on a finite product space is coordinatewise.
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact hX (times k)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 17.11: a strictly increasing finite history tuple is measurable with
respect to the generated filtration at its terminal time. -/
lemma historyTuple_comap_le_generatedFiltrationSpace {n : ℕ}
    (X : ℕ → Ω → E) (times : Fin (n + 1) → ℕ)
    (htimes : StrictMono times) :
    MeasurableSpace.comap (fun ω k ↦ X (times k) ω) inferInstance ≤
      generatedFiltrationSpace X (times (Fin.last n)) := by
  -- Proof comment: a map into a finite product is measurable once each coordinate is measurable
  -- for the terminal generated filtration.
  refine Measurable.comap_le ?_
  letI : MeasurableSpace Ω := generatedFiltrationSpace X (times (Fin.last n))
  rw [measurable_pi_iff]
  intro k
  exact Measurable.of_comap_le <|
    le_iSup_of_le (times k) <| le_iSup_of_le
      (htimes.monotone (Fin.le_last k)) le_rfl

/-- Helper for Theorem 17.11: the generated history filtration of a discrete-time process is
monotone in the terminal time. -/
lemma generatedFiltrationSpace_monoNat
    {Ω' : Type*} [MeasurableSpace Ω'] {F : Type*} [MeasurableSpace F]
    (X : ℕ → Ω' → F) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace X m ≤ generatedFiltrationSpace X n := by
  -- Proof comment: enlarging the terminal time only enlarges the supremum of admissible past
  -- coordinate sigma-algebras.
  refine iSup_le fun r ↦ ?_
  refine iSup_le fun hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

/-- Helper for Theorem 17.11: evaluating a kernel composition against a restricted pushforward is
the same as integrating the kernel row over the restricted source event. -/
lemma kernelComp_restrictMap_real_eq_setIntegral
    (κ : Kernel E E) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set E} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := ((μ.restrict B).map Y)
  have hkernel_int :
      Integrable (fun y : E ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : E ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change ∫ y, (κ y).real A ∂((μ.restrict B).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
        simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
        simpa [ν] using hmap_real

/-- Helper for Theorem 17.11: on a history event from time `s`, the restricted law of the next
state is obtained by composing the restricted current-state law with `κ₁`. -/
lemma restrictMap_succ_eq_kernelComp_of_oneStep
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A)
    (x : E) (s : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    (((P x : Measure Ω).restrict B).map (X (s + 1))) =
      κ₁ ∘ₘ (((P x : Measure Ω).restrict B).map (X s)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
    exact generatedFiltrationSpace_le_ambient (X := X) hmeas s
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  refine Measure.ext fun A hA ↦ ?_
  let futureEvent : Set Ω := X (s + 1) ⁻¹' A
  have hfuture_meas : MeasurableSet futureEvent := by
    simpa [futureEvent] using (hmeas (s + 1)) hA
  have hleft_real :
      ((((μ.restrict B).map (X (s + 1))).real A)) =
        ∫ ω in B, (κ₁ (X s ω)).real A ∂μ := by
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X s⟧ =ᵐ[μ]
          fun ω ↦ (κ₁ (X s ω)).real A := by
      simpa [futureEvent] using hstep x hA s
    have hmass :
        μ.real (B ∩ futureEvent) =
          ∫ ω in B, (κ₁ (X s ω)).real A ∂μ := by
      calc
        μ.real (B ∩ futureEvent)
            = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace X s⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                  ← MeasureTheory.integral_indicator hB_ambient]
                simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                  Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hB_ambient.inter hfuture_meas)).symm
        _ = ∫ ω in B, (κ₁ (X s ω)).real A ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    calc
      (((μ.restrict B).map (X (s + 1))).real A)
          = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                MeasureTheory.map_measureReal_apply
                  (μ := μ.restrict B) (f := X (s + 1)) (hmeas (s + 1)) hA
      _ = μ.real (futureEvent ∩ B) := by
            simpa [futureEvent] using
              (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B)
                (t := futureEvent) hfuture_meas)
      _ = ∫ ω in B, (κ₁ (X s ω)).real A ∂μ := by
            simpa [futureEvent, Set.inter_comm] using hmass
  have hright_real :
      ((κ₁ ∘ₘ (((μ.restrict B).map (X s)))).real A) =
        ∫ ω in B, (κ₁ (X s ω)).real A ∂μ := by
    exact kernelComp_restrictMap_real_eq_setIntegral
      (κ := κ₁) (μ := μ) (hY := hmeas s) hB_ambient hA
  -- Proof comment: compare the two restricted next-step laws on every measurable state set.
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict B).map (X (s + 1))))
      (ν := κ₁ ∘ₘ (((μ.restrict B).map (X s))))
      (s := A) (t := A)).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Theorem 17.11: every restricted future marginal at time `s + t` is obtained by
applying the `t`-step kernel power to the restricted law at time `s`. -/
lemma restrictMap_add_eq_kernelPowComp
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A)
    (x : E) (s t : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    (((P x : Measure Ω).restrict B).map (X (s + t))) =
      (κ₁ ^ t) ∘ₘ (((P x : Measure Ω).restrict B).map (X s)) := by
  induction t with
  | zero =>
      -- Proof comment: the zero-step future law is the restricted present law.
      rw [Nat.add_zero, pow_zero]
      exact (Measure.id_comp (μ := (((P x : Measure Ω).restrict B).map (X s)))).symm
  | succ t ih =>
      have hB_big : MeasurableSet[generatedFiltrationSpace X (s + t)] B := by
        exact
          (generatedFiltrationSpace_monoNat (X := X) (m := s) (n := s + t)
            (Nat.le_add_right s t)) B hB
      -- Proof comment: first advance one step from time `s + t`, then substitute the induction
      -- hypothesis and fold the two kernel compositions into the next power.
      calc
        (((P x : Measure Ω).restrict B).map (X (s + t.succ)))
            = (((P x : Measure Ω).restrict B).map (X ((s + t) + 1))) := by
                simp [Nat.add_assoc]
        _ = κ₁ ∘ₘ (((P x : Measure Ω).restrict B).map (X (s + t))) := by
              exact
                restrictMap_succ_eq_kernelComp_of_oneStep
                  (κ₁ := κ₁) (P := P) (X := X) hmeas hstep x (s + t) hB_big
        _ = κ₁ ∘ₘ ((κ₁ ^ t) ∘ₘ (((P x : Measure Ω).restrict B).map (X s))) := by
              rw [ih]
        _ = (κ₁ ∘ₖ (κ₁ ^ t)) ∘ₘ (((P x : Measure Ω).restrict B).map (X s)) := by
              rw [Measure.comp_assoc]
        _ = (κ₁ ^ t.succ) ∘ₘ (((P x : Measure Ω).restrict B).map (X s)) := by
              have hpow : κ₁ ∘ₖ (κ₁ ^ t) = κ₁ ^ t.succ := by
                simpa [pow_one, Nat.add_comm] using (Kernel.pow_add κ₁ 1 t).symm
              rw [hpow]

/-- Helper for Theorem 17.11: the one-step conditional law upgrades to the full arbitrary-gap
Markov property with transition kernel `κ₁ ^ t`. -/
lemma kernelPow_setIntegral_eq_on_history
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A)
    (x : E) {A : Set E} (hA : MeasurableSet A) (s t : ℕ)
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    ∫ ω in B, ((κ₁ ^ t) (X s ω)).real A ∂(P x : Measure Ω) =
      ∫ ω in B, Set.indicator (X (t + s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hB_ambient : MeasurableSet B := (generatedFiltrationSpace_le_ambient (X := X) hmeas s) B hB
  have hfuture_meas : MeasurableSet (X (t + s) ⁻¹' A) := by
    simpa using (hmeas (t + s)) hA
  have hrestrict_real :
      (((μ.restrict B).map (X (t + s))).real A) =
        ∫ ω in B, Set.indicator (X (t + s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
    -- Proof comment: rewrite the restricted pushforward mass as the mass of the restricted future
    -- event, then identify that mass with the corresponding set integral.
    calc
      (((μ.restrict B).map (X (t + s))).real A)
          = (μ.restrict B).real (X (t + s) ⁻¹' A) := by
              simpa using
                MeasureTheory.map_measureReal_apply
                  (μ := μ.restrict B) (f := X (t + s)) (hmeas (t + s)) hA
      _ = μ.real ((X (t + s) ⁻¹' A) ∩ B) := by
            simpa using
              (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B)
                (t := X (t + s) ⁻¹' A) hfuture_meas)
      _ = ∫ ω in B, Set.indicator (X (t + s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            rw [← MeasureTheory.integral_indicator hB_ambient]
            simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm,
              Set.inter_comm, smul_eq_mul] using
              (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                (hB_ambient.inter hfuture_meas)).symm
  have hkernel_real :
      (((κ₁ ^ t) ∘ₘ ((μ.restrict B).map (X s))).real A) =
        ∫ ω in B, ((κ₁ ^ t) (X s ω)).real A ∂μ := by
    -- Proof comment: evaluate the kernel composition on `A` by integrating the `t`-step row over
    -- the restricted present-state law.
    exact
      kernelComp_restrictMap_real_eq_setIntegral
        (κ := κ₁ ^ t) (μ := μ) (hY := hmeas s) hB_ambient hA
  have hrestrict_eq :
      (((μ.restrict B).map (X (t + s))).real A) =
        (((κ₁ ^ t) ∘ₘ ((μ.restrict B).map (X s))).real A) := by
    -- Proof comment: this is the already-proved restricted-law recursion specialized to the set
    -- `A` by taking real masses on both sides.
    simpa [μ, Nat.add_comm] using
      congrArg (fun ν : Measure E => ν.real A)
        (restrictMap_add_eq_kernelPowComp
          (κ₁ := κ₁) (P := P) (X := X) hmeas hstep x s t hB)
  -- Proof comment: combine the restricted-law identity with the two normal forms needed by the
  -- conditional-expectation uniqueness theorem.
  calc
    ∫ ω in B, ((κ₁ ^ t) (X s ω)).real A ∂μ
        = (((κ₁ ^ t) ∘ₘ ((μ.restrict B).map (X s))).real A) := hkernel_real.symm
    _ = (((μ.restrict B).map (X (t + s))).real A) := hrestrict_eq.symm
    _ = ∫ ω in B, Set.indicator (X (t + s) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := hrestrict_real

/-- Helper for Theorem 17.11: the one-step conditional law upgrades to the full arbitrary-gap
Markov property with transition kernel `κ₁ ^ t`. -/
lemma markovProperty_eq_kernelPow_of_oneStep
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A)
    (x : E) {A : Set E} (hA : MeasurableSet A) (s t : ℕ) :
    (P x)⟦X (t + s) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
      fun ω ↦ ((κ₁ ^ t) (X s ω)).real A := by
  let μ : Measure Ω := (P x : Measure Ω)
  let futureEvent : Set Ω := X (t + s) ⁻¹' A
  let g : Ω → ℝ := fun ω ↦ ((κ₁ ^ t) (X s ω)).real A
  have hgenerated_le : generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
    exact generatedFiltrationSpace_le_ambient (X := X) hmeas s
  have hfuture_meas : MeasurableSet futureEvent := by
    simpa [futureEvent] using (hmeas (t + s)) hA
  have hIndicatorInt : Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hfuture_meas
  have hstate :
      Measurable[generatedFiltrationSpace X s] (fun ω ↦ X s ω) := by
    exact Measurable.of_comap_le (present_le_generatedFiltrationSpace (X := X) s)
  have hg_meas :
      AEStronglyMeasurable[generatedFiltrationSpace X s] g μ := by
    -- Proof comment: the candidate depends only on the present state `X s`, so it is measurable
    -- with respect to the history sigma-algebra at time `s`.
    exact (((Kernel.measurable_coe (κ₁ ^ t) hA).ennreal_toReal).comp hstate).aestronglyMeasurable
  have hg_int_row : Integrable (fun y : E ↦ ((κ₁ ^ t) y).real A) (μ.map (X s)) := by
    simpa using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := μ.map (X s)) (κ := κ₁ ^ t) hA)
  have hg_int : Integrable g μ := by
    -- Proof comment: pull the integrability of the kernel row back along the measurable present
    -- state map.
    simpa [g] using hg_int_row.comp_measurable (hmeas s)
  -- Route correction: the earlier stalled inline proof is replaced by the dedicated
  -- `kernelPow_setIntegral_eq_on_history` bridge, which matches the normal form required by
  -- `ae_eq_condExp_of_forall_setIntegral_eq`.
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hIndicatorInt
      (fun B _ _ ↦ hg_int.integrableOn)
      (fun B hB _ ↦ ?_) hg_meas).symm
  -- Proof comment: the restricted-law recursion already proves equality of the two test-set
  -- integrals on every history event.
  simpa [futureEvent, g] using
    (kernelPow_setIntegral_eq_on_history
      (κ₁ := κ₁) (P := P) (X := X) hmeas hstep x hA s t hB)

/-- Helper for Theorem 17.11: the one-step conditional law determines every time-`n` marginal as
the `n`-fold kernel power applied to the starting state. -/
lemma map_eq_kernelPow_of_oneStep
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstart : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A) :
    ∀ x : E, ∀ n : ℕ, (P x : Measure Ω).map (X n) = (κ₁ ^ n) x := by
  intro x
  refine Nat.rec (hstart x) ?_
  intro n ih
  let μ : Measure Ω := (P x : Measure Ω)
  refine Measure.ext fun A hA ↦ ?_
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    exact generatedFiltrationSpace_le_ambient (X := X) hmeas n
  have hcomp_real :
      ((κ₁ ∘ₖ (κ₁ ^ n)) x).real A = ∫ y, (κ₁ y).real A ∂((κ₁ ^ n) x) := by
    -- Proof comment: the successor kernel row integrates the one-step mass against the time-`n`
    -- marginal.
    rw [Measure.real_def, Kernel.comp_apply' _ _ _ hA]
    simpa [Measure.real_def] using
      (integral_toReal (μ := (κ₁ ^ n) x)
        ((Kernel.measurable_coe κ₁ hA).aemeasurable)
        (Filter.Eventually.of_forall fun y ↦
          lt_of_le_of_lt (prob_le_one : (κ₁ y) A ≤ 1) ENNReal.one_lt_top)).symm
  have hmap_real :
      ∫ y, (κ₁ y).real A ∂((κ₁ ^ n) x) = ∫ ω, (κ₁ (X n ω)).real A ∂μ := by
    -- Proof comment: replace the time-`n` kernel row by the time-`n` pushforward law from the
    -- induction hypothesis.
    rw [← ih]
    exact
      integral_map (hmeas n).aemeasurable
        ((Kernel.measurable_coe κ₁ hA).ennreal_toReal.aestronglyMeasurable)
  have hfuture_real :
      ∫ ω, (κ₁ (X n ω)).real A ∂μ = (μ.map (X (n + 1))).real A := by
    -- Proof comment: integrate the one-step conditional-law identity over the whole space and
    -- rewrite the resulting event integral as the time-`n + 1` pushforward mass.
    calc
      ∫ ω, (κ₁ (X n ω)).real A ∂μ
          = ∫ ω, (μ⟦X (n + 1) ⁻¹' A | generatedFiltrationSpace X n⟧) ω ∂μ := by
              exact integral_congr_ae (hstep x hA n).symm
      _ = ∫ ω, Set.indicator (X (n + 1) ⁻¹' A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            exact
              integral_condExp
                (μ := μ)
                (m := generatedFiltrationSpace X n)
                (f := Set.indicator (X (n + 1) ⁻¹' A) fun _ ↦ (1 : ℝ))
                hgenerated_le
      _ = μ.real (X (n + 1) ⁻¹' A) := by
            rw [integral_indicator ((hmeas (n + 1)) hA)]
            rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real_def]
      _ = (μ.map (X (n + 1))).real A := by
            symm
            exact
              MeasureTheory.map_measureReal_apply
                (μ := μ) (f := X (n + 1)) (hmeas (n + 1)) hA
  have hpow : κ₁ ∘ₖ (κ₁ ^ n) = κ₁ ^ n.succ := by
    simpa [pow_one, Nat.one_add] using (Kernel.pow_add κ₁ 1 n).symm
  -- Proof comment: compare the two probability measures on measurable sets via their real masses.
  simpa [μ, hpow] using
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := μ.map (X (n + 1)))
      (ν := (κ₁ ∘ₖ (κ₁ ^ n)) x)
      (s := A) (t := A)).mp <|
        hfuture_real.symm.trans <| hmap_real.symm.trans hcomp_real.symm

-- Proof sketch: the hypothesis `hstart` supplies the primitive initial-state law required by
-- `IsMarkovProcessRealization`. Iterating the one-step conditional-probability identity through
-- the natural filtration then gives the full Markov property and identifies the time-`n`
-- marginals with the kernel powers `κ₁ ^ n`, so the result lands directly in the owner
-- abstraction `IsMarkovProcessRealization`.
/-- Realization form of Theorem 17.11: if a discrete-time process started from `x` has one-step
conditional law given by the stochastic kernel `κ₁`, then the Markov property from Definition
17.3(iii) follows, and the `n`-step transition kernels are the powers `κ₁ ^ n`. -/
theorem isMarkovProcessRealization_of_oneStepKernel
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    (hmeas : ∀ n : ℕ, Measurable (X n))
    (hstart : ∀ x : E, (P x : Measure Ω).map (X 0) = Measure.dirac x)
    (hstep :
      ∀ x : E, ∀ ⦃A : Set E⦄, MeasurableSet A → ∀ s : ℕ,
        (P x)⟦X (s + 1) ⁻¹' A | generatedFiltrationSpace X s⟧ =ᵐ[(P x : Measure Ω)]
          fun ω ↦ (κ₁ (X s ω)).real A) :
    IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X := by
  -- Proof comment: the one-step law already determines the entire discrete-time owner package:
  -- kernel powers give the semigroup, `hstart` gives the initial law, the iterated one-step law
  -- gives the time marginals, and the arbitrary-gap conditional law gives the Markov field.
  refine
    { semigroup := isMarkovSemigroup_kernelPowers κ₁
      measurable_process := hmeas
      initial_eq := hstart
      transition_eq := ?_
      markov_property := ?_ }
  · -- Proof comment: the time-`n` marginal is the `n`-step kernel power by the earlier
    -- induction on `n`.
    exact map_eq_kernelPow_of_oneStep (κ₁ := κ₁) (P := P) (X := X) hmeas hstart hstep
  · -- Proof comment: the arbitrary-gap Markov property is exactly the upgraded conditional-law
    -- lemma proved above.
    intro x A hA s t
    exact
      markovProperty_eq_kernelPow_of_oneStep
        (κ₁ := κ₁) (P := P) (X := X) hmeas hstep x hA s t

end

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

/-- Helper for Theorem 17.11: splitting a successor tuple at its last coordinate is a measurable
equivalence with the prefix tuple and the terminal state. -/
noncomputable def succTupleEquiv (m : ℕ) :
    (Fin (m + 2) → E) ≃ᵐ (Fin (m + 1) → E) × E :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) ↦ E) (Fin.last (m + 1))).trans
    MeasurableEquiv.prodComm

/-- Helper for Theorem 17.11: `succTupleEquiv` records a successor tuple by its prefix and last
coordinate. -/
@[simp] lemma succTupleEquiv_apply
    (m : ℕ) (z : Fin (m + 2) → E) :
    succTupleEquiv (E := E) m z =
      ((fun i ↦ z i.castSucc), z (Fin.last (m + 1))) := by
  refine Prod.ext ?_ ?_
  · funext i
    change
      (MeasurableEquiv.prodComm
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) ↦ E) (Fin.last (m + 1))) z)).1 i =
        z i.castSucc
    rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_last]
    rfl
  · change
      (MeasurableEquiv.prodComm
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 2) ↦ E) (Fin.last (m + 1))) z)).2 =
        z (Fin.last (m + 1))
    rw [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_last]
    rfl

/-- Helper for Theorem 17.11: the inverse of `succTupleEquiv` glues a prefix tuple and a last
state into the full successor tuple. -/
@[simp] lemma succTupleEquiv_symm_apply
    (m : ℕ) (z : (Fin (m + 1) → E) × E) :
    (succTupleEquiv (E := E) m).symm z = Fin.snoc z.1 z.2 := by
  have hsplit :
      z =
        ((fun i ↦ (succTupleEquiv (E := E) m).symm z i.castSucc),
          (succTupleEquiv (E := E) m).symm z (Fin.last (m + 1))) := by
    simpa using
      (succTupleEquiv_apply (E := E) m ((succTupleEquiv (E := E) m).symm z))
  have hcastSucc :
      ∀ j : Fin (m + 1), (succTupleEquiv (E := E) m).symm z j.castSucc = z.1 j := by
    intro j
    exact congrFun (congrArg Prod.fst hsplit.symm) j
  have hlast :
      (succTupleEquiv (E := E) m).symm z (Fin.last (m + 1)) = z.2 := by
    exact congrArg Prod.snd hsplit.symm
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa using hcastSucc j
  · simpa using hlast

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 17.11: a measurable event in the prefix tuple is measurable with respect
to the generated filtration at the predecessor time. -/
lemma prefixTuple_preimage_measurable_generatedFiltration
    {X : ℕ → Ω → E} {m : ℕ} (times : Fin (m + 2) → ℕ) (htimes : StrictMono times)
    {B : Set (Fin (m + 1) → E)} (hB : MeasurableSet B) :
    let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
    let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
    let sPrev : ℕ := prefixTimes (Fin.last m)
    MeasurableSet[generatedFiltrationSpace X sPrev] (prefixTuple ⁻¹' B) := by
  let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
  let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
  let sPrev : ℕ := prefixTimes (Fin.last m)
  have hprefixTimes : StrictMono prefixTimes := by
    intro i j hij
    exact htimes (by simpa using hij)
  have hprefixMeas :
      Measurable[generatedFiltrationSpace X sPrev] prefixTuple := by
    -- Proof comment: the prefix tuple is a finite history tuple, so the earlier
    -- `historyTuple_comap_le_generatedFiltrationSpace` bridge makes it measurable for the
    -- generated filtration at the predecessor time.
    refine Measurable.of_comap_le ?_
    simpa [prefixTimes, prefixTuple, sPrev] using
      (historyTuple_comap_le_generatedFiltrationSpace (X := X) (times := prefixTimes)
        hprefixTimes)
  -- Proof comment: measurability of the tuple map transfers measurable events on the tuple
  -- space back to measurable history events.
  simpa [prefixTuple] using hprefixMeas hB

/-- Helper for Theorem 17.11: after splitting a successor tuple into its prefix tuple and final
state, the resulting law is the product of the prefix law with the appropriate kernel power. -/
lemma orderedTupleLawSucc_eq_compProd_kernelPow
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X]
    (x : E) {m : ℕ} (times : Fin (m + 2) → ℕ) (htimes : StrictMono times) :
    let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
    let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
    let sPrev : ℕ := prefixTimes (Fin.last m)
    let sLast : ℕ := times (Fin.last (m + 1))
    let gap : ℕ := sLast - sPrev
    let stepKernel : Kernel (Fin (m + 1) → E) E :=
      Kernel.comap (κ₁ ^ gap) (fun z ↦ z (Fin.last m)) (by fun_prop)
    ((P x : Measure Ω).map (fun ω ↦ (prefixTuple ω, X sLast ω))) =
      ((P x : Measure Ω).map prefixTuple) ⊗ₘ stepKernel := by
  let hX : IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X := inferInstance
  let μ : Measure Ω := (P x : Measure Ω)
  let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
  let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
  let sPrev : ℕ := prefixTimes (Fin.last m)
  let sLast : ℕ := times (Fin.last (m + 1))
  let gap : ℕ := sLast - sPrev
  let prefixMeasure : Measure (Fin (m + 1) → E) := μ.map prefixTuple
  let stepKernel : Kernel (Fin (m + 1) → E) E :=
    Kernel.comap (κ₁ ^ gap) (fun z ↦ z (Fin.last m)) (by fun_prop)
  let realizedSplitMeasure : Measure ((Fin (m + 1) → E) × E) :=
    μ.map (fun ω ↦ (prefixTuple ω, X sLast ω))
  let productSplitMeasure : Measure ((Fin (m + 1) → E) × E) :=
    prefixMeasure ⊗ₘ stepKernel
  have hprefixTupleMeas : Measurable prefixTuple := by
    -- Proof comment: each prefix coordinate is one of the measurable process coordinates.
    exact measurable_historyTuple (X := X) (times := prefixTimes) hX.measurable_process
  have hlast :
      sPrev < sLast := by
    -- Proof comment: strict monotonicity of the tuple times forces the predecessor time to be
    -- strictly smaller than the last time.
    simpa [prefixTimes, sPrev, sLast] using htimes (Fin.castSucc_lt_last (Fin.last m))
  have hgap :
      gap + sPrev = sLast := by
    -- Proof comment: `gap` was defined as the difference between the last time and the
    -- predecessor time.
    simpa [gap] using Nat.sub_add_cancel hlast.le
  have hprefixLast :
      (fun z : Fin (m + 1) → E ↦ z (Fin.last m)) ∘ prefixTuple = X sPrev := by
    -- Proof comment: evaluating the prefix tuple at its terminal coordinate recovers the
    -- predecessor state itself.
    funext ω
    simp [Function.comp, prefixTuple, sPrev, prefixTimes]
  have hgenerated_le : generatedFiltrationSpace X sPrev ≤ ‹MeasurableSpace Ω› := by
    exact generatedFiltrationSpace_le_ambient (X := X) hX.measurable_process sPrev
  have hrealizedRect :
      ∀ (B : Set (Fin (m + 1) → E)) (hB : MeasurableSet B)
        (A : Set E) (hA : MeasurableSet A),
        realizedSplitMeasure (B ×ˢ A) =
          ∫⁻ z in B, stepKernel z A ∂prefixMeasure := by
    intro B hB A hA
    let prefixEvent : Set Ω := prefixTuple ⁻¹' B
    let lastEvent : Set Ω := X sLast ⁻¹' A
    have hprefixGenerated :
        MeasurableSet[generatedFiltrationSpace X sPrev] prefixEvent := by
      -- Proof comment: the prefix event is a measurable history event at time `sPrev`.
      simpa [prefixEvent, prefixTuple, prefixTimes, sPrev] using
        (prefixTuple_preimage_measurable_generatedFiltration
          (X := X) (times := times) htimes hB)
    have hprefixEventMeas : MeasurableSet prefixEvent := hgenerated_le prefixEvent hprefixGenerated
    have hlastEventMeas : MeasurableSet lastEvent := by
      simpa [lastEvent] using (hX.measurable_process sLast) hA
    have hmarkov :
        μ⟦lastEvent | generatedFiltrationSpace X sPrev⟧ =ᵐ[μ]
          fun ω ↦ ((κ₁ ^ gap) (X sPrev ω)).real A := by
      -- Proof comment: rewrite the last time as `gap + sPrev` and apply the realization-side
      -- Markov property at the predecessor time.
      simpa [μ, lastEvent, sPrev, sLast, hgap] using
        hX.markov_property x hA sPrev gap
    have hIndicatorInt :
        Integrable (Set.indicator lastEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hlastEventMeas
    have hrect :
        μ.real (prefixEvent ∩ lastEvent) =
          ∫ ω in prefixEvent, ((κ₁ ^ gap) (X sPrev ω)).real A ∂μ := by
      -- Proof comment: integrate the conditional expectation over the measurable prefix event.
      calc
        μ.real (prefixEvent ∩ lastEvent)
            = ∫ ω in prefixEvent, (μ⟦lastEvent | generatedFiltrationSpace X sPrev⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hprefixGenerated,
                  ← MeasureTheory.integral_indicator hprefixEventMeas]
                simpa [lastEvent, Set.indicator_indicator, Set.inter_assoc,
                  Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hprefixEventMeas.inter hlastEventMeas)).symm
        _ = ∫ ω in prefixEvent, ((κ₁ ^ gap) (X sPrev ω)).real A ∂μ := by
              refine MeasureTheory.setIntegral_congr_ae hprefixEventMeas ?_
              filter_upwards [hmarkov] with ω hω _
              exact hω
    have hstepInt :
        Integrable (fun z : Fin (m + 1) → E ↦ (stepKernel z).real A) prefixMeasure := by
      -- Proof comment: a Markov-kernel row mass is integrable against the finite prefix law.
      simpa [stepKernel] using
        (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
          (μ := prefixMeasure) (κ := stepKernel) hA)
    have hstepNonneg :
        0 ≤ᵐ[prefixMeasure] fun z : Fin (m + 1) → E ↦ (stepKernel z).real A := by
      exact Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
    have hpush :
        ∫ z in B, (stepKernel z).real A ∂prefixMeasure =
          ∫ ω in prefixEvent, ((κ₁ ^ gap) (X sPrev ω)).real A ∂μ := by
      -- Proof comment: push the prefix-state integral back along the measurable prefix tuple.
      rw [← MeasureTheory.integral_indicator hB]
      change
        ∫ z, Set.indicator B (fun z : Fin (m + 1) → E ↦ (stepKernel z).real A) z
          ∂prefixMeasure =
            ∫ ω in prefixEvent, ((κ₁ ^ gap) (X sPrev ω)).real A ∂μ
      rw [MeasureTheory.integral_map hprefixTupleMeas.aemeasurable
        ((hstepInt.indicator hB).aestronglyMeasurable)]
      have hindicator :
          (fun ω ↦
            Set.indicator B (fun z : Fin (m + 1) → E ↦ (stepKernel z).real A) (prefixTuple ω)) =
            Set.indicator prefixEvent (fun ω ↦ ((κ₁ ^ gap) (X sPrev ω)).real A) := by
        funext ω
        by_cases hω : prefixTuple ω ∈ B
        · have hlastValue : prefixTuple ω (Fin.last m) = X sPrev ω := by
            simpa [Function.comp] using congrFun hprefixLast ω
          simp [prefixEvent, hω, stepKernel, hlastValue]
        · simp [prefixEvent, hω, stepKernel]
      rw [hindicator, MeasureTheory.integral_indicator hprefixEventMeas]
    have hproductRect :
        productSplitMeasure.real (B ×ˢ A) =
          ∫ z in B, (stepKernel z).real A ∂prefixMeasure := by
      have hlintegral :
          ∫⁻ z in B, stepKernel z A ∂prefixMeasure =
            ENNReal.ofReal (∫ z in B, ((stepKernel z).real A) ∂prefixMeasure) := by
        calc
          ∫⁻ z in B, stepKernel z A ∂prefixMeasure
              = ∫⁻ z in B, ENNReal.ofReal ((stepKernel z).real A) ∂prefixMeasure := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with z
                  rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                  exact measure_ne_top _ _
          _ = ENNReal.ofReal (∫ z in B, ((stepKernel z).real A) ∂prefixMeasure) := by
                symm
                exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  hstepInt.restrict
                  (ae_restrict_of_ae hstepNonneg)
      have hprodRect :
          productSplitMeasure (B ×ˢ A) =
            ∫⁻ z in B, stepKernel z A ∂prefixMeasure := by
        simpa [productSplitMeasure] using
          (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hA)
      calc
        productSplitMeasure.real (B ×ˢ A)
            = (∫⁻ z in B, stepKernel z A ∂prefixMeasure).toReal := by
                simpa [MeasureTheory.measureReal_def] using congrArg ENNReal.toReal hprodRect
        _ = ∫ z in B, ((stepKernel z).real A) ∂prefixMeasure := by
              rw [hlintegral, ENNReal.toReal_ofReal]
              exact integral_nonneg_of_ae (ae_restrict_of_ae hstepNonneg)
    have hrealizedRectReal :
        realizedSplitMeasure.real (B ×ˢ A) =
          ∫ z in B, (stepKernel z).real A ∂prefixMeasure := by
      -- Proof comment: identify the realized split rectangle with the corresponding history
      -- event intersection, then push the kernel integral through the prefix tuple.
      have hsplitMeas : Measurable (fun ω ↦ (prefixTuple ω, X sLast ω)) := by
        exact hprefixTupleMeas.prodMk (hX.measurable_process sLast)
      calc
        realizedSplitMeasure.real (B ×ˢ A)
            = μ.real (prefixEvent ∩ lastEvent) := by
                rw [MeasureTheory.map_measureReal_apply hsplitMeas (hB.prod hA)]
                congr
        _ = ∫ ω in prefixEvent, ((κ₁ ^ gap) (X sPrev ω)).real A ∂μ := hrect
        _ = ∫ z in B, (stepKernel z).real A ∂prefixMeasure := hpush.symm
    have hrectMeas :
        realizedSplitMeasure (B ×ˢ A) = productSplitMeasure (B ×ˢ A) := by
      exact
        (MeasureTheory.measureReal_eq_measureReal_iff
          (μ := realizedSplitMeasure) (ν := productSplitMeasure)).mp
          (hrealizedRectReal.trans hproductRect.symm)
    exact hrectMeas.trans <| by
      simpa [productSplitMeasure] using
        (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hA)
  have hrealizedProd :
      realizedSplitMeasure = productSplitMeasure := by
    have hstepFiniteTransition : IsFiniteTransitionKernel stepKernel := by
      exact isFiniteTransitionKernel_of_isFiniteKernel stepKernel
    rcases existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel
        prefixMeasure stepKernel hstepFiniteTransition with
      ⟨ν, hν, huniq⟩
    have hrealizedChar :
        SigmaFinite realizedSplitMeasure ∧
          ∀ B : Set (Fin (m + 1) → E), ∀ A : Set E,
            MeasurableSet B → MeasurableSet A →
              realizedSplitMeasure (B ×ˢ A) =
                ∫⁻ z in B, stepKernel z A ∂prefixMeasure := by
      exact ⟨inferInstance, fun B A hB hA ↦ hrealizedRect B hB A hA⟩
    have hproductChar :
        SigmaFinite productSplitMeasure ∧
          ∀ B : Set (Fin (m + 1) → E), ∀ A : Set E,
            MeasurableSet B → MeasurableSet A →
              productSplitMeasure (B ×ˢ A) =
                ∫⁻ z in B, stepKernel z A ∂prefixMeasure := by
      refine ⟨inferInstance, ?_⟩
      intro B A hB hA
      simpa [productSplitMeasure] using
        (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hA)
    exact (huniq realizedSplitMeasure hrealizedChar).trans
      (huniq productSplitMeasure hproductChar).symm
  -- Proof comment: the split tuple law is characterized uniquely by the product-measure rectangle
  -- formula, so the realized split law equals the explicit `compProd`.
  simpa [μ, prefixTimes, prefixTuple, sPrev, sLast, gap, prefixMeasure, stepKernel,
    realizedSplitMeasure, productSplitMeasure] using hrealizedProd

/-- Helper for Theorem 17.11: after splitting a positive-length history into its prefix tuple and
terminal state, the rectangle mass is computed by the gap kernel applied to the prefix's last
state. -/
lemma orderedTupleLawSuccRect_eq_kernelPowIntegral
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X]
    (x : E) {m : ℕ} (times : Fin (m + 2) → ℕ) (htimes : StrictMono times)
    {B : Set (Fin (m + 1) → E)} (hB : MeasurableSet B)
    {A : Set E} (hA : MeasurableSet A) :
    let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
    let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
    let sPrev : ℕ := prefixTimes (Fin.last m)
    let sLast : ℕ := times (Fin.last (m + 1))
    let gap : ℕ := sLast - sPrev
    (((P x : Measure Ω).map (fun ω ↦ (prefixTuple ω, X sLast ω))).real (B ×ˢ A)) =
      ∫ z in B, ((κ₁ ^ gap) (z (Fin.last m))).real A ∂((P x : Measure Ω).map prefixTuple) := by
  let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
  let prefixTuple : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
  let sPrev : ℕ := prefixTimes (Fin.last m)
  let sLast : ℕ := times (Fin.last (m + 1))
  let gap : ℕ := sLast - sPrev
  let prefixMeasure : Measure (Fin (m + 1) → E) := (P x : Measure Ω).map prefixTuple
  let stepKernel : Kernel (Fin (m + 1) → E) E :=
    Kernel.comap (κ₁ ^ gap) (fun z ↦ z (Fin.last m)) (by fun_prop)
  have hsplit :
      ((P x : Measure Ω).map (fun ω ↦ (prefixTuple ω, X sLast ω))) =
        prefixMeasure ⊗ₘ stepKernel := by
    -- Proof comment: first identify the full split law with the explicit product measure.
    simpa [prefixTimes, prefixTuple, sPrev, sLast, gap, prefixMeasure, stepKernel] using
      (orderedTupleLawSucc_eq_compProd_kernelPow
        (κ₁ := κ₁) (P := P) (X := X) x times htimes)
  have hstepInt :
      Integrable (fun z : Fin (m + 1) → E ↦ (stepKernel z).real A) prefixMeasure := by
    -- Proof comment: the gap kernel remains Markov after the `Kernel.comap`, so its row masses
    -- are integrable against the prefix law.
    simpa [stepKernel] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := prefixMeasure) (κ := stepKernel) hA)
  have hstepNonneg :
      0 ≤ᵐ[prefixMeasure] fun z : Fin (m + 1) → E ↦ (stepKernel z).real A := by
    exact Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hlintegral :
      ∫⁻ z in B, stepKernel z A ∂prefixMeasure =
        ENNReal.ofReal (∫ z in B, ((stepKernel z).real A) ∂prefixMeasure) := by
    calc
      ∫⁻ z in B, stepKernel z A ∂prefixMeasure
          = ∫⁻ z in B, ENNReal.ofReal ((stepKernel z).real A) ∂prefixMeasure := by
              refine lintegral_congr_ae ?_
              filter_upwards with z
              rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
              exact measure_ne_top _ _
      _ = ENNReal.ofReal (∫ z in B, ((stepKernel z).real A) ∂prefixMeasure) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
              hstepInt.restrict
              (ae_restrict_of_ae hstepNonneg)
  have hproductRect :
      (prefixMeasure ⊗ₘ stepKernel).real (B ×ˢ A) =
        ∫ z in B, ((stepKernel z).real A) ∂prefixMeasure := by
    have hprodRect :
        (prefixMeasure ⊗ₘ stepKernel) (B ×ˢ A) =
          ∫⁻ z in B, stepKernel z A ∂prefixMeasure := by
      simpa using (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hB hA)
    calc
      (prefixMeasure ⊗ₘ stepKernel).real (B ×ˢ A)
          = (∫⁻ z in B, stepKernel z A ∂prefixMeasure).toReal := by
              simpa [MeasureTheory.measureReal_def] using congrArg ENNReal.toReal hprodRect
      _ = ∫ z in B, ((stepKernel z).real A) ∂prefixMeasure := by
            rw [hlintegral, ENNReal.toReal_ofReal]
            exact integral_nonneg_of_ae (ae_restrict_of_ae hstepNonneg)
  -- Proof comment: evaluate the split law on a measurable rectangle and unfold the comapped gap
  -- kernel on the last prefix coordinate.
  calc
    (((P x : Measure Ω).map (fun ω ↦ (prefixTuple ω, X sLast ω))).real (B ×ˢ A))
        = (prefixMeasure ⊗ₘ stepKernel).real (B ×ˢ A) := by rw [hsplit]
    _ = ∫ z in B, ((stepKernel z).real A) ∂prefixMeasure := hproductRect
    _ = ∫ z in B, ((κ₁ ^ gap) (z (Fin.last m))).real A ∂((P x : Measure Ω).map prefixTuple) := by
          simp [prefixMeasure, stepKernel]

-- Proof sketch: this is the owner-level uniqueness statement from Theorem 17.8, specialized to
-- the canonical semigroup `n ↦ κ₁ ^ n` attached to the one-step kernel `κ₁`.
/-- Theorem 17.11: in particular, the one-step kernel `κ₁` determines the finite-dimensional
distributions of any discrete-time Markov-process realization uniquely. Equivalently, two
realizations with the same one-step kernel have the same ordered finite-dimensional distributions.
-/
theorem finiteDimensionalDistribution_eq_of_same_oneStepKernel
    (κ₁ : Kernel E E) [IsMarkovKernel κ₁]
    {P : E → ProbabilityMeasure Ω} {Q : E → ProbabilityMeasure Ω'}
    {X : ℕ → Ω → E} {Y : ℕ → Ω' → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) Q Y]
    (x : E) {n : ℕ} (times : Fin (n + 1) → ℕ)
    (h_zero : times 0 = 0) (htimes : StrictMono times) :
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
      (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := by
  let hX : IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) P X := inferInstance
  let hY : IsMarkovProcessRealization (fun n : ℕ ↦ κ₁ ^ n) Q Y := inferInstance
  induction n with
  | zero =>
      let e : E → Fin 1 → E := (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ E)).symm
      have heMeas : Measurable e := by
        fun_prop
      have htupleX : (fun ω i ↦ X (times i) ω) = e ∘ X 0 := by
        funext ω i
        fin_cases i
        simp [e, h_zero]
      have htupleY : (fun ω i ↦ Y (times i) ω) = e ∘ Y 0 := by
        funext ω i
        fin_cases i
        simp [e, h_zero]
      -- Proof comment: the one-coordinate tuple law is just the time-zero marginal, and both
      -- realizations start from the same deterministic initial state.
      calc
        (P x : Measure Ω).map (fun ω i ↦ X (times i) ω)
            = ((P x : Measure Ω).map (X 0)).map e := by
                simpa [htupleX, Function.comp] using
                  (Measure.map_map heMeas (hX.measurable_process 0)
                    (μ := (P x : Measure Ω))).symm
        _ = (Measure.dirac x).map e := by
              rw [hX.initial_eq x]
        _ = ((Q x : Measure Ω').map (Y 0)).map e := by
              rw [hY.initial_eq x]
        _ = (Q x : Measure Ω').map (fun ω i ↦ Y (times i) ω) := by
              simpa [htupleY, Function.comp] using
                (Measure.map_map heMeas (hY.measurable_process 0)
                  (μ := (Q x : Measure Ω')))
  | succ m ih =>
      let prefixTimes : Fin (m + 1) → ℕ := fun i ↦ times i.castSucc
      let tupleX : Ω → Fin (m + 2) → E := fun ω i ↦ X (times i) ω
      let tupleY : Ω' → Fin (m + 2) → E := fun ω i ↦ Y (times i) ω
      let prefixTupleX : Ω → Fin (m + 1) → E := fun ω i ↦ X (prefixTimes i) ω
      let prefixTupleY : Ω' → Fin (m + 1) → E := fun ω i ↦ Y (prefixTimes i) ω
      let sPrev : ℕ := prefixTimes (Fin.last m)
      let sLast : ℕ := times (Fin.last (m + 1))
      let gap : ℕ := sLast - sPrev
      let stepKernel : Kernel (Fin (m + 1) → E) E :=
        Kernel.comap (κ₁ ^ gap) (fun z ↦ z (Fin.last m)) (by fun_prop)
      let splitTupleX : Ω → (Fin (m + 1) → E) × E := fun ω ↦ (prefixTupleX ω, X sLast ω)
      let splitTupleY : Ω' → (Fin (m + 1) → E) × E := fun ω ↦ (prefixTupleY ω, Y sLast ω)
      have hprefixZero : prefixTimes 0 = 0 := by
        simpa [prefixTimes] using h_zero
      have hprefixTimes : StrictMono prefixTimes := by
        intro i j hij
        exact htimes (by simpa using hij)
      have hprefixLaw :
          (P x : Measure Ω).map prefixTupleX =
            (Q x : Measure Ω').map prefixTupleY := by
        -- Proof comment: apply the induction hypothesis to the predecessor tuple.
        simpa [prefixTimes, prefixTupleX, prefixTupleY] using
          (ih (times := prefixTimes) hprefixZero hprefixTimes)
      have htupleXMeas : Measurable tupleX := by
        exact measurable_historyTuple (X := X) (times := times) hX.measurable_process
      have htupleYMeas : Measurable tupleY := by
        exact measurable_historyTuple (X := Y) (times := times) hY.measurable_process
      have hsplitTupleX :
          (succTupleEquiv (E := E) m) ∘ tupleX = splitTupleX := by
        funext ω
        calc
          ((succTupleEquiv (E := E) m) ∘ tupleX) ω
              = ((fun i ↦ tupleX ω i.castSucc), tupleX ω (Fin.last (m + 1))) := by
                  change (succTupleEquiv (E := E) m (tupleX ω)) =
                    ((fun i ↦ tupleX ω i.castSucc), tupleX ω (Fin.last (m + 1)))
                  exact succTupleEquiv_apply (E := E) m (tupleX ω)
          _ = splitTupleX ω := by
                simp [tupleX, splitTupleX, prefixTupleX, prefixTimes, sLast]
      have hsplitTupleY :
          (succTupleEquiv (E := E) m) ∘ tupleY = splitTupleY := by
        funext ω
        calc
          ((succTupleEquiv (E := E) m) ∘ tupleY) ω
              = ((fun i ↦ tupleY ω i.castSucc), tupleY ω (Fin.last (m + 1))) := by
                  change (succTupleEquiv (E := E) m (tupleY ω)) =
                    ((fun i ↦ tupleY ω i.castSucc), tupleY ω (Fin.last (m + 1)))
                  exact succTupleEquiv_apply (E := E) m (tupleY ω)
          _ = splitTupleY ω := by
                simp [tupleY, splitTupleY, prefixTupleY, prefixTimes, sLast]
      have hmapX :
          ((P x : Measure Ω).map tupleX).map (succTupleEquiv (E := E) m) =
            (P x : Measure Ω).map splitTupleX := by
        -- Proof comment: `succTupleEquiv` exactly splits the full successor tuple into its
        -- predecessor tuple and terminal coordinate.
        simpa [hsplitTupleX] using
          (Measure.map_map (succTupleEquiv (E := E) m).measurable htupleXMeas
            (μ := (P x : Measure Ω)))
      have hmapY :
          ((Q x : Measure Ω').map tupleY).map (succTupleEquiv (E := E) m) =
            (Q x : Measure Ω').map splitTupleY := by
        -- Proof comment: the same tuple splitting applies to the second realization.
        simpa [hsplitTupleY] using
          (Measure.map_map (succTupleEquiv (E := E) m).measurable htupleYMeas
            (μ := (Q x : Measure Ω')))
      have hsplitX :
          (P x : Measure Ω).map splitTupleX =
            ((P x : Measure Ω).map prefixTupleX) ⊗ₘ stepKernel := by
        -- Proof comment: the realization-side split law is the canonical `compProd` with the
        -- gap kernel row evaluated at the predecessor state.
        simpa [prefixTimes, prefixTupleX, sPrev, sLast, gap, stepKernel, splitTupleX] using
          (orderedTupleLawSucc_eq_compProd_kernelPow
            (κ₁ := κ₁) (P := P) (X := X) x times htimes)
      have hsplitY :
          (Q x : Measure Ω').map splitTupleY =
            ((Q x : Measure Ω').map prefixTupleY) ⊗ₘ stepKernel := by
        -- Proof comment: the same split law holds for the second realization because the gap
        -- kernel depends only on `κ₁` and the time tuple.
        simpa [prefixTimes, prefixTupleY, sPrev, sLast, gap, stepKernel, splitTupleY] using
          (orderedTupleLawSucc_eq_compProd_kernelPow
            (κ₁ := κ₁) (P := Q) (X := Y) x times htimes)
      have hsplitEq :
          ((P x : Measure Ω).map tupleX).map (succTupleEquiv (E := E) m) =
            ((Q x : Measure Ω').map tupleY).map (succTupleEquiv (E := E) m) := by
        -- Route correction: compare both laws only after transporting them to the split
        -- product side, where the induction hypothesis rewrites the prefix measure directly.
        calc
          ((P x : Measure Ω).map tupleX).map (succTupleEquiv (E := E) m)
              = (P x : Measure Ω).map splitTupleX := hmapX
          _ = ((P x : Measure Ω).map prefixTupleX) ⊗ₘ stepKernel := hsplitX
          _ = ((Q x : Measure Ω').map prefixTupleY) ⊗ₘ stepKernel := by
                rw [hprefixLaw]
          _ = (Q x : Measure Ω').map splitTupleY := hsplitY.symm
          _ = ((Q x : Measure Ω').map tupleY).map (succTupleEquiv (E := E) m) := hmapY.symm
      -- Proof comment: transport the common split law back through the inverse equivalence to
      -- recover equality of the original successor tuple laws.
      calc
        (P x : Measure Ω).map tupleX
            = (((P x : Measure Ω).map tupleX).map (succTupleEquiv (E := E) m)).map
                (succTupleEquiv (E := E) m).symm := by
                  symm
                  calc
                    (((P x : Measure Ω).map tupleX).map (succTupleEquiv (E := E) m)).map
                        (succTupleEquiv (E := E) m).symm
                        = ((P x : Measure Ω).map tupleX).map
                            ((succTupleEquiv (E := E) m).symm ∘ succTupleEquiv (E := E) m) := by
                              exact
                                (Measure.map_map
                                  (MeasurableEquiv.symm (succTupleEquiv (E := E) m)).measurable
                                  (succTupleEquiv (E := E) m).measurable
                                  (μ := (P x : Measure Ω).map tupleX))
                    _ = (P x : Measure Ω).map tupleX := by
                          simp
        _ = (((Q x : Measure Ω').map tupleY).map (succTupleEquiv (E := E) m)).map
              (succTupleEquiv (E := E) m).symm := by
                rw [hsplitEq]
        _ = (Q x : Measure Ω').map tupleY := by
              calc
                (((Q x : Measure Ω').map tupleY).map (succTupleEquiv (E := E) m)).map
                    (succTupleEquiv (E := E) m).symm
                    = ((Q x : Measure Ω').map tupleY).map
                        ((succTupleEquiv (E := E) m).symm ∘ succTupleEquiv (E := E) m) := by
                          exact
                            (Measure.map_map
                              (MeasurableEquiv.symm (succTupleEquiv (E := E) m)).measurable
                              (succTupleEquiv (E := E) m).measurable
                              (μ := (Q x : Measure Ω').map tupleY))
                _ = (Q x : Measure Ω').map tupleY := by
                      simp

end

end ProbabilityTheory

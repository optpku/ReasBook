/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_15
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_11

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

variable {p C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsRandomWalkWithWeights p C]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Corollary 19.16: under `P x`, the realized chain starts at the deterministic state
`x` almost surely. -/
private lemma initialState_ae_eq_start
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X) (x : E) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  -- Proof comment: rewrite the time-`0` event through the pushed-forward law and use the
  -- realization axiom `(P x).map (X 0) = dirac x`.
  have hprob : (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1 := by
    have hInit := congrArg (fun ν : Measure E ↦ ν ({x} : Set E)) (hReal.initial_eq x)
    simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit
  have hmeas : MeasurableSet (X 0 ⁻¹' {x}) := by
    simpa using (hReal.measurable_process 0) (measurableSet_singleton x)
  exact (mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Corollary 19.16: the realized chain is adapted to its own natural filtration. -/
private lemma adapted_processFiltration
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X) :
    Adapted (processFiltration X) X := by
  intro n
  -- Proof comment: the time-`n` coordinate is one of the generators of `processFiltration X n`.
  have hX_meas : ∀ k : ℕ, Measurable (X k) := by
    intro k
    simpa using hReal.measurable_process k
  refine measurable_iff_comap_le.2 ?_
  exact le_inf (measurable_iff_comap_le.1 (hX_meas n)) <| by
    refine le_iSup_of_le n ?_
    refine le_iSup_of_le le_rfl ?_
    exact le_rfl

/-- Helper for Corollary 19.16: bounded range makes every sampled value `f (X n)` integrable
under the realization measure `(P x : Measure Ω)`. -/
private lemma integrable_comp_process_of_boundedRange
    {f : E → ℝ} (hX_meas : ∀ n : ℕ, Measurable (X n))
    (hf_bdd : Bornology.IsBounded (Set.range f)) (x : E) :
    ∀ n, Integrable (fun ω ↦ f (X n ω)) (P x : Measure Ω) := by
  intro n
  obtain ⟨R, hR⟩ := hf_bdd.exists_norm_le
  let μ : Measure Ω := (P x : Measure Ω)
  -- Proof comment: bounded range gives a uniform deterministic `L¹` bound on the sampled
  -- process.
  refine Integrable.mono' (integrable_const R)
    ((Measurable.of_discrete.comp (hX_meas n)).aestronglyMeasurable) ?_
  filter_upwards with ω
  simpa using hR (f (X n ω)) ⟨X n ω, rfl⟩

/-- Helper for Corollary 19.16: on an event from the time-`n` history, the restricted law of
`X (n + 1)` is obtained by composing the restricted law of `X n` with the one-step discrete
kernel. -/
private lemma restrictMap_succ_eq_discreteKernelComp
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
      -- Proof comment: push the kernel mass function back through the restricted current-state
      -- law.
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

/-- Helper for Corollary 19.16: the first entrance time `hittingAfter X A 0` is a stopping time
for the natural filtration of the realized chain. -/
private lemma hittingAfter_zero_isStoppingTime
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (A : Set E) :
    IsStoppingTime (processFiltration X) (hittingAfter X A 0) := by
  -- Proof comment: hitting times of measurable sets are stopping times for adapted processes.
  simpa using
    Adapted.isStoppingTime_hittingAfter
      (u := X) (s := A) (n := 0) (adapted_processFiltration (P := P) (X := X) hReal)
      MeasurableSet.of_discrete

/-- Helper for Corollary 19.16: if the realized trajectory starts outside `A`, then the first
entrance time searched from `0` agrees with the first entrance time searched from `1`. -/
private lemma hittingAfter_zero_eq_one_of_not_mem_initial
    {A : Set E} {ω : Ω} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  -- Proof comment: monotonicity in the search start gives one inequality, and `h0` excludes a
  -- hit at time `0`, so the first hit from time `0` must in fact occur at some time `≥ 1`.
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle : hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
        hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simp [htop]
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Corollary 19.16: before the first entrance time `τ`, truncating at the deterministic
time `n` leaves the stopped value equal to the raw time-`n` slice. -/
private lemma stoppedValue_min_const_eq_time_on_preHit
    {Y : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} (n : ℕ) :
    Set.EqOn
      (stoppedValue Y (fun ω ↦ min (τ ω) (n : ℕ∞)))
      (Y n)
      {ω | (n : ℕ∞) < τ ω} := by
  intro ω hω
  -- Proof comment: on `{n < τ}`, the minimum picks the deterministic time `n`.
  have hmin : min (τ ω) (n : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hω)
  have hidx : (min (τ ω) (n : ℕ∞)).untopA = n := by
    rw [hmin]
    simp
  change Y (min (τ ω) (n : ℕ∞)).untopA ω = Y n ω
  simpa using congrArg (fun k ↦ Y k ω) hidx

/-- Helper for Corollary 19.16: if the entrance time `τ` is still strictly after `n`, then the
`n + 1` truncation has not stopped yet either, so the stopped value is the raw time-`n + 1`
slice. -/
private lemma stoppedValue_min_const_succ_eq_time_on_preHit
    {Y : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} (n : ℕ) :
    Set.EqOn
      (stoppedValue Y (fun ω ↦ min (τ ω) (((n + 1 : ℕ) : ℕ∞))))
      (Y (n + 1))
      {ω | (n : ℕ∞) < τ ω} := by
  intro ω hω
  -- Proof comment: `n < τ` means either `τ = ⊤` or `τ = m` with `n < m`, so the
  -- next truncation still reads time `n + 1`.
  have hmin : min (τ ω) (((n + 1 : ℕ) : ℕ∞)) = (((n + 1 : ℕ) : ℕ∞)) := by
    refine min_eq_right ?_
    by_cases htop : τ ω = ⊤
    · simp [htop]
    · lift τ ω to ℕ using htop with m hm
      have hmgt_top : (n : ℕ∞) < m := by
        simpa [hm] using hω
      have hmgt : n < m := by
        exact_mod_cast hmgt_top
      exact_mod_cast Nat.succ_le_of_lt hmgt
  have hidx : (min (τ ω) (((n + 1 : ℕ) : ℕ∞))).untopA = n + 1 := by
    have hcast : (((n + 1 : ℕ) : ℕ∞)) = (n : ℕ∞) + 1 := by
      simp
    have hne : ¬ ((n : ℕ∞) + 1 = ⊤) := by
      exact (show ((n : ℕ∞) + 1) < ⊤ by simp).ne
    rw [hmin]
    rw [hcast]
    rw [WithTop.untopA_eq_untop hne]
    exact (WithTop.untop_eq_iff hne).2 rfl
  change Y (min (τ ω) (((n + 1 : ℕ) : ℕ∞))).untopA ω = Y (n + 1) ω
  simpa using congrArg (fun k ↦ Y k ω) hidx

/-- Helper for Corollary 19.16: once the entrance time `τ` has occurred by time `n`, the `n` and
`n + 1` truncations of the stopped process agree. -/
private lemma stoppedValue_min_const_succ_eq_on_postHit
    {Y : ℕ → Ω → ℝ} {τ : Ω → ℕ∞} (n : ℕ) :
    Set.EqOn
      (stoppedValue Y (fun ω ↦ min (τ ω) (((n + 1 : ℕ) : ℕ∞))))
      (stoppedValue Y (fun ω ↦ min (τ ω) (n : ℕ∞)))
      {ω | τ ω ≤ n} := by
  intro ω hω
  -- Proof comment: on `{τ ≤ n}`, both bounded stopping times reduce to the same value `τ`.
  have hmin_n : min (τ ω) (n : ℕ∞) = τ ω := min_eq_left hω
  have hmin_succ :
      min (τ ω) (((n + 1 : ℕ) : ℕ∞)) = τ ω := min_eq_left (hω.trans (by simp))
  have hidx :
      (min (τ ω) (((n + 1 : ℕ) : ℕ∞))).untopA = (min (τ ω) (n : ℕ∞)).untopA := by
    rw [hmin_succ, hmin_n]
  change Y (min (τ ω) (((n + 1 : ℕ) : ℕ∞))).untopA ω =
    Y (min (τ ω) (n : ℕ∞)).untopA ω
  simpa using congrArg (fun k ↦ Y k ω) hidx

/-- Helper for Corollary 19.16: restricting to an event `s` and pushing forward by `X n`
preserves the outside-`A` support assumption. -/
private lemma restrictedCurrentLaw_ae_notMem
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    {A : Set E} {μ : Measure Ω} (n : ℕ) {s : Set Ω} (hs : MeasurableSet s)
    (hs_out : ∀ ⦃ω : Ω⦄, ω ∈ s → X n ω ∉ A) :
    ∀ᵐ y ∂((μ.restrict s).map (X n)), y ∉ A := by
  have hX_meas : Measurable (X n) := by
    simpa using hReal.measurable_process n
  have hsupport : ∀ᵐ ω ∂(μ.restrict s), X n ω ∉ A := by
    -- Proof comment: after restricting to `s`, almost every sample path still lies in `s`.
    filter_upwards [ae_restrict_mem hs] with ω hω
    exact hs_out hω
  -- Proof comment: push the restricted a.e. support statement forward through the time-`n`
  -- coordinate map.
  rw [MeasureTheory.ae_map_iff hX_meas.aemeasurable
    (MeasurableSet.of_discrete : MeasurableSet {y : E | y ∉ A})]
  exact hsupport

/-- Helper for Corollary 19.16: the restricted one-step future law is the kernel average of the
restricted current law. -/
private lemma discreteKernelCompIntegral_eq_restrictedSuccIntegral
    {u : E → ℝ} (hu_bdd : Bornology.IsBounded (Set.range u))
    (x : E) (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂((((P x : Measure Ω).restrict s).map (X n))) =
      ∫ ω in s, u (X (n + 1) ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure E := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  have hnext_int : Integrable u (((μ.restrict s).map (X (n + 1)))) := by
    -- Proof comment: boundedness of `u` keeps the restricted next-step slice integrable.
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X (n + 1)) (g := u)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process (n + 1)).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hu_bdd x (n + 1)).restrict
  have hnext_map :
      ∫ y, u y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ ω in s, u (X (n + 1) ω) ∂μ := by
    change ∫ y, u y ∂((μ.restrict s).map (X (n + 1))) =
      ∫ ω, u (X (n + 1) ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process (n + 1)).aemeasurable
      hnext_int.aestronglyMeasurable]
  have hcomp_int : Integrable u ((discreteMatrixKernel p) ∘ₘ ν) := by
    -- Proof comment: rewrite the restricted next-step law through the Markov kernel.
    simpa [ν] using
      (restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs ▸ hnext_int)
  have hcomp_integral :
      ∫ y, u y ∂(((μ.restrict s).map (X (n + 1)))) =
        ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂ν := by
    rw [restrictMap_succ_eq_discreteKernelComp (P := P) (X := X) (p := p) x n hs]
    calc
      ∫ y, u y ∂((discreteMatrixKernel p) ∘ₘ ν)
          =
            ∫ y, u y ∂(
              (discreteMatrixKernel p ∘ₖ ProbabilityTheory.Kernel.const Unit ν) ()) := by
              rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
      _ = ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂ν := by
            exact
              ProbabilityTheory.Kernel.integral_comp
                (η := discreteMatrixKernel p) (κ := ProbabilityTheory.Kernel.const Unit ν)
                (a := ()) <| by
                  rw [ProbabilityTheory.Kernel.comp_const, ProbabilityTheory.Kernel.const_apply]
                  exact hcomp_int
  -- Proof comment: first transport to the one-step kernel average, then read the restricted
  -- next-step slice as an integral against the pushed-forward law.
  calc
    ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂ν
        = ∫ y, u y ∂(((μ.restrict s).map (X (n + 1)))) := hcomp_integral.symm
    _ = ∫ ω in s, u (X (n + 1) ω) ∂μ := hnext_map

/-- Helper for Corollary 19.16: if a measure is supported outside `A`, then harmonicity outside
`A` collapses the one-step kernel average back to the current integral. -/
private lemma harmonicOutsideKernelAverage_eq_currentIntegral
    {A : Set E} {u : E → ℝ}
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u) {ν : Measure E}
    (hν_out : ∀ᵐ y ∂ν, y ∉ A) :
    ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂ν = ∫ y, u y ∂ν := by
  -- Proof comment: harmonicity gives the pointwise identity `Ku = u` on the support of `ν`.
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hν_out] with y hy
  exact (hu_harmonic hy).2.symm

/-- Helper for Corollary 19.16: on a time-`n` history event where the current state stays outside
`A`, harmonicity outside `A` identifies the time-`n` and time-`n + 1` set integrals. -/
private lemma harmonicOutsideSetIntegralSuccEqOnEvent
    {A : Set E} {u : E → ℝ} (hu_bdd : Bornology.IsBounded (Set.range u))
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u) (x : E)
    (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s)
    (hs_out : ∀ ⦃ω : Ω⦄, ω ∈ s → X n ω ∉ A) :
    ∫ ω in s, u (X n ω) ∂(P x : Measure Ω) =
      ∫ ω in s, u (X (n + 1) ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let ν : Measure E := ((μ.restrict s).map (X n))
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hcurrent_int : Integrable u ν := by
    -- Proof comment: boundedness of `u` makes the restricted current-state law integrable.
    exact
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict s) (f := X n) (g := u)
        (Measurable.of_discrete.aestronglyMeasurable)
        (hReal.measurable_process n).aemeasurable).2 <|
        (integrable_comp_process_of_boundedRange
          (P := P) (X := X) hReal.measurable_process hu_bdd x n).restrict
  have hcurrent_map :
      ∫ y, u y ∂ν = ∫ ω in s, u (X n ω) ∂μ := by
    change ∫ y, u y ∂((μ.restrict s).map (X n)) = ∫ ω, u (X n ω) ∂(μ.restrict s)
    rw [MeasureTheory.integral_map (hReal.measurable_process n).aemeasurable
      hcurrent_int.aestronglyMeasurable]
  have hν_out : ∀ᵐ y ∂ν, y ∉ A := by
    simpa [ν] using
      restrictedCurrentLaw_ae_notMem
        (P := P) (X := X) (p := p) (hReal := hReal) (A := A)
        (μ := μ) n hs.1 hs_out
  -- Route correction: keep event bookkeeping at the current-time integral and move all
  -- transport/harmonic collapse onto the pushed-forward law `ν`.
  calc
    ∫ ω in s, u (X n ω) ∂μ = ∫ y, u y ∂ν := hcurrent_map.symm
    _ = ∫ y, ∫ z, u z ∂discreteMatrixKernel p y ∂ν := by
          exact
            (harmonicOutsideKernelAverage_eq_currentIntegral
              (A := A) (u := u) hu_harmonic hν_out).symm
    _ = ∫ ω in s, u (X (n + 1) ω) ∂μ := by
          simpa [ν, μ] using
            discreteKernelCompIntegral_eq_restrictedSuccIntegral
              (P := P) (X := X) (p := p) (u := u) hu_bdd x n hs

/-- Helper for Corollary 19.16: `hittingAfter X A 0` is the entrance time used in the stopped
potential formulas. -/
private abbrev firstEntranceTimeFromZero (A : Set E) : Ω → ℕ∞ :=
  hittingAfter X A 0

/-- Helper for Corollary 19.16: `potentialAlongTrajectory u n ω = u (X n ω)` records the
electrical potential along the realized chain. -/
private abbrev potentialAlongTrajectory (u : E → ℝ) : ℕ → Ω → ℝ :=
  fun n ω ↦ u (X n ω)

/-- Helper for Corollary 19.16: the deterministic truncation of the stopped potential at time
`n` is `u (X_{τ₀ ∧ n})`. -/
private abbrev truncatedStoppedPotential (A : Set E) (u : E → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    stoppedValue (potentialAlongTrajectory (X := X) u)
      (fun ω' ↦ min (firstEntranceTimeFromZero (X := X) A ω') (n : ℕ∞)) ω

/-- Helper for Corollary 19.16: the fully stopped potential is `u (X_{τ₀})`. -/
private abbrev stoppedPotentialAtFirstEntrance (A : Set E) (u : E → ℝ) : Ω → ℝ :=
  fun ω ↦
    stoppedValue (potentialAlongTrajectory (X := X) u)
      (firstEntranceTimeFromZero (X := X) A) ω

/-- Helper for Corollary 19.16: the deterministic truncation `u (X_{τ₀ ∧ n})` is exactly the
stopped process associated with `u ∘ X` and the entrance time `τ₀`. -/
private lemma truncatedStoppedPotential_eq_stoppedProcess
    {A : Set E} {u : E → ℝ} :
    truncatedStoppedPotential (X := X) A u =
      MeasureTheory.stoppedProcess
        (potentialAlongTrajectory (X := X) u)
        (firstEntranceTimeFromZero (X := X) A) := by
  -- Proof comment: both sides evaluate `u` at the same truncated index; only the spelling of
  -- the minimum differs.
  ext n ω
  change
    stoppedValue (potentialAlongTrajectory (X := X) u)
      (fun ω' ↦ min (firstEntranceTimeFromZero (X := X) A ω') (n : ℕ∞)) ω
      =
    u (X (min (n : ℕ∞) (firstEntranceTimeFromZero (X := X) A ω)).untopA ω)
  rw [min_comm]
  rfl

/-- Helper for Corollary 19.16: on any time-`n` history event, one deterministic truncation step
of the stopped potential keeps the same restricted expectation. -/
private lemma truncatedStoppedPotential_setIntegral_succEqOnHistory
    {A : Set E} {u : E → ℝ} {x : E}
    (hu_bdd : Bornology.IsBounded (Set.range u))
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u)
    (n : ℕ) {s : Set Ω} (hs : MeasurableSet[processFiltration X n] s) :
    ∫ ω in s, truncatedStoppedPotential (X := X) A u (n + 1) ω ∂(P x : Measure Ω)
      =
      ∫ ω in s, truncatedStoppedPotential (X := X) A u n ω ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let τ₀ : Ω → ℕ∞ := firstEntranceTimeFromZero (X := X) A
  let Y : ℕ → Ω → ℝ := potentialAlongTrajectory (X := X) u
  let F : ℕ → Ω → ℝ := truncatedStoppedPotential (X := X) A u
  let post : Set Ω := {ω | τ₀ ω ≤ n}
  let pre : Set Ω := {ω | (n : ℕ∞) < τ₀ ω}
  let postS : Set Ω := s ∩ post
  let preS : Set Ω := s ∩ pre
  have hτ0_stop : IsStoppingTime (processFiltration X) τ₀ := by
    -- Proof comment: `τ₀` is exactly the first entrance time searched from `0`.
    simpa [τ₀, firstEntranceTimeFromZero] using hittingAfter_zero_isStoppingTime
      (P := P) (X := X) (p := p) (hReal := inferInstance) A
  have hpost_meas : MeasurableSet post := by
    -- Proof comment: the post-hit slice is measurable because `τ₀` is a stopping time.
    simpa [post] using hτ0_stop.measurableSpace_le _ (hτ0_stop.measurableSet_le' n)
  have hpre_fil : MeasurableSet[processFiltration X n] pre := by
    -- Proof comment: the pre-hit slice is the standard `{n < τ₀}` stopping-time event.
    simpa [pre] using hτ0_stop.measurableSet_gt n
  have hpostS_meas : MeasurableSet postS := hs.1.inter hpost_meas
  have hpreS_fil : MeasurableSet[processFiltration X n] preS := hs.inter hpre_fil
  have hpreS_meas : MeasurableSet preS := hpreS_fil.1
  have hpartition : postS ∪ preS = s := by
    ext ω
    by_cases hω : τ₀ ω ≤ n
    · simp [postS, preS, post, pre, hω]
    · have hlt : (n : ℕ∞) < τ₀ ω := lt_of_not_ge hω
      simp [postS, preS, post, pre, hω, hlt]
  have hdisj : Disjoint postS preS := by
    refine Set.disjoint_left.2 ?_
    intro ω hωpost hωpre
    have hpostω : τ₀ ω ≤ n := by
      simpa [postS, post] using hωpost.2
    have hpreω : (n : ℕ∞) < τ₀ ω := by
      simpa [preS, pre] using hωpre.2
    exact (not_lt_of_ge hpostω) hpreω
  have hY_int : ∀ k, Integrable (Y k) μ := by
    intro k
    simpa [Y, μ] using
      integrable_comp_process_of_boundedRange
        (P := P) (X := X)
        ((inferInstance : IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process)
        hu_bdd x k
  have hF_int : ∀ k, Integrable (F k) μ := by
    intro k
    -- Proof comment: each truncation samples the bounded potential process at the bounded
    -- stopping time `τ₀ ∧ k`.
    simpa [F] using
      integrable_stoppedValue ℕ (hτ0_stop.min_const k) hY_int (fun ω ↦ min_le_right _ _)
  have hpost_eq_succ :
      Set.EqOn (F (n + 1)) (stoppedValue Y τ₀) postS := by
    intro ω hω
    have hpostω : τ₀ ω ≤ n := by
      simpa [postS, post] using hω.2
    -- Proof comment: once `τ₀` has occurred by time `n`, enlarging the deterministic cutoff
    -- still leaves the stopped value frozen at `τ₀`.
    simpa [F] using
      (stoppedValue_min_const_eqOn_le_const (X := Y) (σ := τ₀) (n := n + 1))
        (show τ₀ ω ≤ n + 1 from le_trans hpostω (by simp))
  have hpost_eq_curr :
      Set.EqOn (F n) (stoppedValue Y τ₀) postS := by
    intro ω hω
    -- Proof comment: on the same post-hit slice, the time-`n` truncation has already stopped.
    simpa [F] using
      (stoppedValue_min_const_eqOn_le_const (X := Y) (σ := τ₀) (n := n))
        (by simpa [postS, post] using hω.2)
  have hpost_eq :
      ∫ ω in postS, F (n + 1) ω ∂μ = ∫ ω in postS, F n ω ∂μ := by
    calc
      ∫ ω in postS, F (n + 1) ω ∂μ = ∫ ω in postS, stoppedValue Y τ₀ ω ∂μ := by
        exact MeasureTheory.setIntegral_congr_fun hpostS_meas hpost_eq_succ
      _ = ∫ ω in postS, F n ω ∂μ := by
        exact MeasureTheory.setIntegral_congr_fun hpostS_meas hpost_eq_curr.symm
  have hpre_eq_succ :
      Set.EqOn (F (n + 1)) (Y (n + 1)) preS := by
    intro ω hω
    -- Proof comment: before the hit time, the `n + 1` truncation has not yet stopped.
    simpa [F] using
      (stoppedValue_min_const_succ_eq_time_on_preHit (Y := Y) (τ := τ₀) n)
        (by simpa [preS, pre] using hω.2)
  have hpre_eq_curr :
      Set.EqOn (F n) (Y n) preS := by
    intro ω hω
    -- Proof comment: the time-`n` truncation likewise reads the raw time-`n` slice on `preS`.
    simpa [F] using
      (stoppedValue_min_const_eq_time_on_preHit (Y := Y) (τ := τ₀) n)
        (by simpa [preS, pre] using hω.2)
  have hs_out : ∀ ⦃ω : Ω⦄, ω ∈ preS → X n ω ∉ A := by
    intro ω hω
    -- Proof comment: if `X n ω` were already in `A`, then the first entrance time could not
    -- lie strictly after `n`.
    exact
      notMem_of_lt_hittingAfter
        (u := X) (s := A) (n := 0) (ω := ω) (k := n)
        (by simpa [preS, pre, τ₀] using hω.2) (by simp)
  have hharmonic :
      ∫ ω in preS, Y n ω ∂μ = ∫ ω in preS, Y (n + 1) ω ∂μ := by
    -- Route correction: replace the bespoke full-space induction step by the owner
    -- history-event criterion needed for the martingale constructor.
    simpa [Y] using
      harmonicOutsideSetIntegralSuccEqOnEvent
        (P := P) (X := X) (p := p) (A := A) (u := u)
        hu_bdd hu_harmonic x n hpreS_fil hs_out
  have hpre_eq :
      ∫ ω in preS, F (n + 1) ω ∂μ = ∫ ω in preS, F n ω ∂μ := by
    calc
      ∫ ω in preS, F (n + 1) ω ∂μ = ∫ ω in preS, Y (n + 1) ω ∂μ := by
        exact MeasureTheory.setIntegral_congr_fun hpreS_meas hpre_eq_succ
      _ = ∫ ω in preS, Y n ω ∂μ := hharmonic.symm
      _ = ∫ ω in preS, F n ω ∂μ := by
        exact MeasureTheory.setIntegral_congr_fun hpreS_meas hpre_eq_curr.symm
  have hsplit_succ :
      ∫ ω in s, F (n + 1) ω ∂μ =
        ∫ ω in postS, F (n + 1) ω ∂μ + ∫ ω in preS, F (n + 1) ω ∂μ := by
    simpa [hpartition] using
      (MeasureTheory.setIntegral_union
        hdisj hpreS_meas (hF_int (n + 1)).restrict (hF_int (n + 1)).restrict)
  have hsplit_curr :
      ∫ ω in s, F n ω ∂μ = ∫ ω in postS, F n ω ∂μ + ∫ ω in preS, F n ω ∂μ := by
    simpa [hpartition] using
      (MeasureTheory.setIntegral_union
        hdisj hpreS_meas (hF_int n).restrict (hF_int n).restrict)
  -- Proof comment: split the history event into the post-hit and pre-hit pieces, then use the
  -- frozen-value identity on the former and harmonicity on the latter.
  calc
    ∫ ω in s, F (n + 1) ω ∂μ
        = ∫ ω in postS, F (n + 1) ω ∂μ + ∫ ω in preS, F (n + 1) ω ∂μ := hsplit_succ
    _ = ∫ ω in postS, F n ω ∂μ + ∫ ω in preS, F (n + 1) ω ∂μ := by rw [hpost_eq]
    _ = ∫ ω in postS, F n ω ∂μ + ∫ ω in preS, F n ω ∂μ := by rw [hpre_eq]
    _ = ∫ ω in s, F n ω ∂μ := hsplit_curr.symm

/-- Helper for Corollary 19.16: the truncated stopped-potential process is strongly adapted to
the natural filtration of the realized chain. -/
private lemma truncatedStoppedPotential_stronglyAdapted
    {A : Set E} {u : E → ℝ}
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X) :
    StronglyAdapted (processFiltration X) (truncatedStoppedPotential (X := X) A u) := by
  let Y : ℕ → Ω → ℝ := potentialAlongTrajectory (X := X) u
  let τ₀ : Ω → ℕ∞ := firstEntranceTimeFromZero (X := X) A
  have hX_adapted : Adapted (processFiltration X) X :=
    adapted_processFiltration (P := P) (X := X) hReal
  have hY_strong : StronglyAdapted (processFiltration X) Y := by
    intro n
    -- Proof comment: the time-`n` state is measurable with respect to its own history, and the
    -- discrete target makes `u ∘ X_n` strongly measurable.
    exact (Measurable.of_discrete.comp (hX_adapted n)).stronglyMeasurable
  have hτ0_stop : IsStoppingTime (processFiltration X) τ₀ := by
    -- Proof comment: the entrance time used in the truncation is a stopping time.
    simpa [τ₀, firstEntranceTimeFromZero] using hittingAfter_zero_isStoppingTime
      (P := P) (X := X) hReal A
  -- Proof comment: after identifying the truncations with the stopped process, the owner
  -- stopped-process adaptedness theorem applies directly.
  rw [truncatedStoppedPotential_eq_stoppedProcess (X := X) (A := A) (u := u)]
  exact StronglyAdapted.stoppedProcess_of_discrete hY_strong hτ0_stop

/-- Helper for Corollary 19.16: the bounded stopped potential process
`F n ω = u (X_{τ₀ ∧ n}(ω))` is a martingale. -/
private lemma truncatedStoppedPotential_martingale
    {A : Set E} {u : E → ℝ} {x : E}
    (hu_bdd : Bornology.IsBounded (Set.range u))
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u) :
    Martingale (truncatedStoppedPotential (X := X) A u) (processFiltration X)
      (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let τ₀ : Ω → ℕ∞ := firstEntranceTimeFromZero (X := X) A
  let Y : ℕ → Ω → ℝ := potentialAlongTrajectory (X := X) u
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hτ0_stop : IsStoppingTime (processFiltration X) τ₀ := by
    -- Proof comment: this is the same first-entrance stopping time used in the truncation.
    simpa [τ₀, firstEntranceTimeFromZero] using hittingAfter_zero_isStoppingTime
      (P := P) (X := X) hReal A
  have hY_int : ∀ n, Integrable (Y n) μ := by
    intro n
    simpa [Y, μ] using
      integrable_comp_process_of_boundedRange
        (P := P) (X := X) hReal.measurable_process
        hu_bdd x n
  have hF_int :
      ∀ n, Integrable (truncatedStoppedPotential (X := X) A u n) μ := by
    intro n
    -- Proof comment: identify the truncation with the stopped process and use the owner
    -- integrability theorem for stopped processes.
    rw [truncatedStoppedPotential_eq_stoppedProcess (X := X) (A := A) (u := u)]
    simpa [Y, τ₀] using
      integrable_stoppedProcess (μ := μ) (ℱ := processFiltration X) (u := Y) (τ := τ₀)
        hτ0_stop hY_int n
  -- Proof comment: the history-event equality proved above is exactly the set-integral
  -- criterion used by the martingale constructor.
  exact
    MeasureTheory.martingale_of_setIntegral_eq_succ
      (truncatedStoppedPotential_stronglyAdapted
        (P := P) (X := X) (A := A) (u := u) hReal)
      hF_int
      (fun n s hs ↦
        (truncatedStoppedPotential_setIntegral_succEqOnHistory
          (P := P) (X := X) (p := p) (A := A) (u := u) (x := x)
          hu_bdd hu_harmonic n hs).symm)

/-- Helper for Corollary 19.16: the martingale optional-sampling theorem at deterministic times
shows that every truncation still has expectation `u x`. -/
private lemma truncatedStoppedPotential_expectation_eq_start
    {A : Set E} {u : E → ℝ} {x : E}
    (hu_bdd : Bornology.IsBounded (Set.range u))
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u)
    (hstart : ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x) :
    ∀ n,
      ∫ ω, truncatedStoppedPotential (X := X) A u n ω ∂(P x : Measure Ω) = u x := by
  let μ : Measure Ω := (P x : Measure Ω)
  let F : ℕ → Ω → ℝ := truncatedStoppedPotential (X := X) A u
  have hF0_ae : (fun ω ↦ F 0 ω) =ᵐ[μ] fun _ ↦ u x := by
    -- Proof comment: the time-`0` truncation reads the initial state, which is almost surely
    -- equal to `x`.
    filter_upwards [hstart] with ω hω
    calc
      F 0 ω
          = u (X ((min (firstEntranceTimeFromZero (X := X) A ω) (0 : ℕ∞)).untopA) ω) := by
              rfl
      _ = u (X 0 ω) := by
        have hzero :
            (min (firstEntranceTimeFromZero (X := X) A ω) (0 : ℕ∞)).untopA = 0 := by
          rw [min_eq_right (by simp)]
          rw [WithTop.untopA_eq_untop (show ((0 : ℕ∞) ≠ ⊤) by simp)]
          exact (WithTop.untop_eq_iff (show ((0 : ℕ∞) ≠ ⊤) by simp)).2 rfl
        rw [hzero]
      _ = u x := by simp [hω]
  have hF0_eq : ∫ ω, F 0 ω ∂μ = u x := by
    calc
      ∫ ω, F 0 ω ∂μ = ∫ ω, u x ∂μ := by exact integral_congr_ae hF0_ae
      _ = u x := by simp [μ]
  have hFmgle : Martingale F (processFiltration X) μ := by
    simpa [F, μ] using
      truncatedStoppedPotential_martingale
        (P := P) (X := X) (p := p) (A := A) (u := u) (x := x)
        hu_bdd hu_harmonic
  intro n
  have hconst :
      ∫ ω, F n ω ∂μ = ∫ ω, F 0 ω ∂μ := by
    -- Proof comment: apply bounded optional stopping to the martingale `F` between the constant
    -- times `0` and `n`.
    simpa [F, stoppedValue] using
      (martingale_expected_stoppedValue_eq_of_le_of_bounded
        (X := F) (μ := μ) (ℱ := processFiltration X) hFmgle
        (isStoppingTime_const (processFiltration X) 0)
        (isStoppingTime_const (processFiltration X) n)
        (fun _ ↦ show (0 : ℕ∞) ≤ (n : ℕ∞) by simp)
        (N := n) (fun _ ↦ le_rfl))
  calc
    ∫ ω, F n ω ∂μ = ∫ ω, F 0 ω ∂μ := hconst
    _ = u x := hF0_eq

/-- Helper for Corollary 19.16: if `τ₀` is almost surely finite, then the bounded truncations of
`u (X_{τ₀ ∧ n})` converge almost surely to the full stopped value `u (X_{τ₀})`. -/
private lemma truncatedStoppedPotential_ae_tendsto
    {A : Set E} {u : E → ℝ} {x : E}
    (hτ0_ae_ne_top : ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 0 ω ≠ ⊤) :
    ∀ᵐ ω ∂(P x : Measure Ω),
      Filter.Tendsto
        (fun n ↦ truncatedStoppedPotential (X := X) A u n ω)
        Filter.atTop
        (nhds (stoppedPotentialAtFirstEntrance (X := X) A u ω)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hτ0_ae_ne_top' :
      ∀ᵐ ω ∂μ, firstEntranceTimeFromZero (X := X) A ω ≠ ⊤ := by
    simpa [μ, firstEntranceTimeFromZero] using hτ0_ae_ne_top
  -- Proof comment: on almost every path, once `n` passes the finite entrance time, every
  -- truncation has already stabilized at the terminal stopped value.
  filter_upwards
    [stoppedValue_truncation_ae_eventuallyEq
      (X := potentialAlongTrajectory (X := X) u) (μ := μ)
      (τ := firstEntranceTimeFromZero (X := X) A) hτ0_ae_ne_top'] with
    ω hω
  have hEq :
      (fun n ↦ truncatedStoppedPotential (X := X) A u n ω) =ᶠ[Filter.atTop]
        fun _ ↦ stoppedPotentialAtFirstEntrance (X := X) A u ω := by
    filter_upwards [hω] with n hn
    simpa [truncatedStoppedPotential, stoppedPotentialAtFirstEntrance] using hn
  exact Filter.Tendsto.congr' hEq.symm tendsto_const_nhds

/-- Helper for Corollary 19.16: boundedness of `u` supplies a uniform deterministic norm bound
for all truncated stopped values `u (X_{τ₀ ∧ n})`. -/
private lemma truncatedStoppedPotential_norm_bound
    {A : Set E} {u : E → ℝ} {x : E}
    (hu_bdd : Bornology.IsBounded (Set.range u)) :
    ∃ R, ∀ n, ∀ᵐ ω ∂(P x : Measure Ω), ‖truncatedStoppedPotential (X := X) A u n ω‖ ≤ R := by
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range u) hu_bdd
  refine ⟨R, ?_⟩
  intro n
  -- Proof comment: every truncation still evaluates `u` at some realized state of the chain.
  filter_upwards with ω
  change ‖u (X (min (firstEntranceTimeFromZero (X := X) A ω) (n : ℕ∞)).untopA ω)‖ ≤ R
  exact hR _ ⟨X (min (firstEntranceTimeFromZero (X := X) A ω) (n : ℕ∞)).untopA ω, rfl⟩

/-- Helper for Corollary 19.16: dominated convergence upgrades the truncated stopped-value
expectations to the full stopped value at `τ₀`. -/
private lemma truncatedStoppedPotentialIntegral_eq_stoppedValue
    {A : Set E} {u : E → ℝ} {x : E}
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (hu_bdd : Bornology.IsBounded (Set.range u))
    (hτ0_ae_ne_top : ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 0 ω ≠ ⊤)
    (htrunc :
      ∀ n,
        ∫ ω, truncatedStoppedPotential (X := X) A u n ω ∂(P x : Measure Ω) = u x) :
    ∫ ω, stoppedPotentialAtFirstEntrance (X := X) A u ω ∂(P x : Measure Ω) = u x := by
  let μ : Measure Ω := (P x : Measure Ω)
  let τ₀ : Ω → ℕ∞ := firstEntranceTimeFromZero (X := X) A
  let Y : ℕ → Ω → ℝ := potentialAlongTrajectory (X := X) u
  let F : ℕ → Ω → ℝ := truncatedStoppedPotential (X := X) A u
  have hτ0_stop : IsStoppingTime (processFiltration X) τ₀ := by
    -- Proof comment: the truncated stopped values use the same entrance time `τ₀`.
    simpa [τ₀, firstEntranceTimeFromZero] using hittingAfter_zero_isStoppingTime
      (P := P) (X := X) hReal A
  have hY_int : ∀ n, Integrable (Y n) μ := by
    intro n
    simpa [Y, μ, potentialAlongTrajectory] using
      integrable_comp_process_of_boundedRange
        (P := P) (X := X) hReal.measurable_process
        hu_bdd x n
  have hF_int : ∀ n, Integrable (F n) μ := by
    intro n
    simpa [F] using
      integrable_stoppedValue ℕ (hτ0_stop.min_const n) hY_int (fun ω ↦ min_le_right _ _)
  have hF_integral_eq : ∀ n, ∫ ω, F n ω ∂μ = u x := by
    simpa [F] using htrunc
  have hF_tendsto :
      ∀ᵐ ω ∂μ,
        Filter.Tendsto (fun n ↦ F n ω) Filter.atTop (nhds (stoppedValue Y τ₀ ω)) := by
    simpa [F, Y, τ₀, truncatedStoppedPotential, stoppedPotentialAtFirstEntrance,
      potentialAlongTrajectory, firstEntranceTimeFromZero] using
      truncatedStoppedPotential_ae_tendsto
        (P := P) (X := X) (A := A) (u := u) (x := x) hτ0_ae_ne_top
  obtain ⟨R, hF_norm_bound⟩ :=
    truncatedStoppedPotential_norm_bound
      (P := P) (X := X) (A := A) (u := u) (x := x) hu_bdd
  have hF_integral_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) Filter.atTop
        (nhds (∫ ω, stoppedValue Y τ₀ ω ∂μ)) := by
    -- Proof comment: after separating almost-sure convergence from uniform domination, the
    -- limit of the expectations is a direct dominated-convergence consequence.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ ↦ R)
      (fun n ↦ (hF_int n).aestronglyMeasurable)
      (integrable_const R)
      hF_norm_bound hF_tendsto
  have hconst_tendsto :
      Filter.Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) Filter.atTop (nhds (u x)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun n ↦ (hF_integral_eq n).symm
  exact tendsto_nhds_unique hF_integral_tendsto hconst_tendsto

/-- Helper for Corollary 19.16: the event that the first entrance time searched from `1` is
finite is measurable. -/
private lemma measurableSet_hittingAfter_one_lt_top
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (A : Set E) :
    MeasurableSet {ω | hittingAfter X A 1 ω < ⊤} := by
  have hEq : {ω | hittingAfter X A 1 ω < ⊤} = ⋃ n : ℕ, X n.succ ⁻¹' A := by
    ext ω
    constructor
    · intro hω
      have hne_top : hittingAfter X A 1 ω ≠ ⊤ := lt_top_iff_ne_top.mp hω
      lift hittingAfter X A 1 ω to ℕ using hne_top with m hm
      have hm_ne_top : hittingAfter X A 1 ω ≠ ⊤ := by
        rw [← hm]
        simp
      have hm_idx : (hittingAfter X A 1 ω).untopA = m := by
        rw [← hm, WithTop.untopA_eq_untop (by simp)]
        exact (WithTop.untop_eq_iff (by simp)).2 rfl
      have hm_mem : X m ω ∈ A := by
        -- Proof comment: a finite first entrance time always lands inside the target set.
        simpa [hm_idx] using
          hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 1) (ω := ω) hm_ne_top
      have hm_ne_zero : m ≠ 0 := by
        intro hm_zero
        have hm_pos_top : (1 : ℕ∞) ≤ hittingAfter X A 1 ω :=
          le_hittingAfter (u := X) (s := A) (n := 1) ω
        have hm_zero_top : hittingAfter X A 1 ω = 0 := by
          symm
          simpa [hm_zero] using hm
        have hm_absurd : (1 : ℕ∞) ≤ (0 : ℕ∞) := by
          exact hm_zero_top ▸ hm_pos_top
        have hnot : ¬ ((1 : ℕ∞) ≤ (0 : ℕ∞)) := by simp
        exact hnot hm_absurd
      rcases Nat.exists_eq_succ_of_ne_zero hm_ne_zero with ⟨n, rfl⟩
      exact Set.mem_iUnion.2 ⟨n, by simpa [Set.mem_preimage] using hm_mem⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨n, hn⟩
      have hn_mem : X n.succ ω ∈ A := by
        simpa [Set.mem_preimage] using hn
      have hle :
          hittingAfter X A 1 ω ≤ n.succ := by
        exact
          hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω)
            (Nat.succ_le_succ (Nat.zero_le n)) hn_mem
      exact lt_of_le_of_lt hle (by simp)
  rw [hEq]
  refine MeasurableSet.iUnion ?_
  intro n
  exact (hReal.measurable_process n.succ) MeasurableSet.of_discrete

/-- Helper for Corollary 19.16: the probability-one finiteness assumption on `hittingAfter X A 1`
upgrades to an almost-sure statement. -/
private lemma hittingAfter_one_ae_ne_top_of_prob_eq_one
    {A : Set E} {x : E}
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (hτ : (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1) :
    ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤ := by
  have hτ_ae : ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω < ⊤ :=
    (mem_ae_iff_prob_eq_one
      (measurableSet_hittingAfter_one_lt_top (P := P) (X := X) (p := p) hReal A)).2 hτ
  simpa [lt_top_iff_ne_top] using hτ_ae

/-- Helper for Corollary 19.16: if the chain starts outside `A` almost surely, then the
first-entrance times searched from `0` and from `1` agree almost surely. -/
private lemma firstEntranceTimeFromZero_ae_eq_hittingAfter_one
    {A : Set E} {x : E}
    (hx : x ∉ A)
    (hstart : ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x) :
    ∀ᵐ ω ∂(P x : Measure Ω),
      firstEntranceTimeFromZero (X := X) A ω = hittingAfter X A 1 ω := by
  -- Proof comment: once `X 0 = x ∉ A`, the search from `0` cannot stop at time `0`.
  filter_upwards [hstart] with ω hω
  have hx0 : X 0 ω ∉ A := by
    simpa [hω] using hx
  simpa [firstEntranceTimeFromZero] using
    hittingAfter_zero_eq_one_of_not_mem_initial (X := X) (A := A) hx0

/-- Helper for Corollary 19.16: almost-sure finiteness of `hittingAfter X A 1` transfers to the
proof-local stopping time `hittingAfter X A 0`. -/
private lemma firstEntranceTimeFromZero_ae_ne_top
    {A : Set E} {x : E}
    (hτ01_ae :
      ∀ᵐ ω ∂(P x : Measure Ω),
        firstEntranceTimeFromZero (X := X) A ω = hittingAfter X A 1 ω)
    (hτ1_ae_ne_top :
      ∀ᵐ ω ∂(P x : Measure Ω), hittingAfter X A 1 ω ≠ ⊤) :
    ∀ᵐ ω ∂(P x : Measure Ω), firstEntranceTimeFromZero (X := X) A ω ≠ ⊤ := by
  -- Proof comment: rewrite the local stopping time through the almost-sure equality with the
  -- textbook entrance time.
  filter_upwards [hτ01_ae, hτ1_ae_ne_top] with ω hω hfin
  simpa [hω] using hfin

/-- Helper for Corollary 19.16: stopping the potential process `u ∘ X` is pointwise the same as
applying `u` to the stopped chain. -/
private lemma stoppedPotentialAtFirstEntrance_ae_eq_u_stoppedValue
    {A : Set E} {u : E → ℝ} {x : E} :
    (fun ω ↦ stoppedPotentialAtFirstEntrance (X := X) A u ω) =ᵐ[(P x : Measure Ω)]
      fun ω ↦ u (stoppedValue X (firstEntranceTimeFromZero (X := X) A) ω) := by
  -- Proof comment: this is a direct normalization of the two spellings of the stopped value.
  filter_upwards with ω
  simp [stoppedPotentialAtFirstEntrance, potentialAlongTrajectory, firstEntranceTimeFromZero,
    stoppedValue]

/-- Helper for Corollary 19.16: after transporting the stopping time from `0` to `1`, applying
`u` to the stopped chain is unchanged almost surely. -/
private lemma u_stoppedValue_firstEntrance_transport_ae
    {A : Set E} {u : E → ℝ} {x : E}
    (hτ01_ae :
      ∀ᵐ ω ∂(P x : Measure Ω),
        firstEntranceTimeFromZero (X := X) A ω = hittingAfter X A 1 ω) :
    (fun ω ↦ u (stoppedValue X (firstEntranceTimeFromZero (X := X) A) ω)) =ᵐ[(P x : Measure Ω)]
      fun ω ↦ u (stoppedValue X (hittingAfter X A 1) ω) := by
  -- Proof comment: replace the proof-local stopping time by the textbook one on the almost-sure
  -- set where they coincide.
  filter_upwards [hτ01_ae] with ω hω
  simp [stoppedValue, hω]

/- Layering for Corollary 19.16:
- `source-facing`: the first-entrance representation formula for an electrical potential on a
  finite conductance network.
- `core/canonical`: `IsElectricalPotential` as the owner abstraction, together with
  `IsRandomWalkWithWeights`, `hittingAfter X A 1`, and
  `stoppedValue X (hittingAfter X A 1)`.
- `bridge/view`: the realization hypothesis identifies the textbook random walk with the kernel
  owner `discreteMatrixKernel p`, while the stopping-time hypothesis keeps the source's
  probability-one finiteness event. -/

-- Proof sketch: `hu` gives harmonicity on `E \ A` by
-- `electricalPotential_isHarmonicOn_compl`. Since `E` is finite, the electrical potential is
-- bounded, so optional stopping applies to `u (X_n)` stopped at the first entrance time
-- `hittingAfter X A 1`. The assumption `hτ` then identifies the stopped value with the boundary
-- value `u (X_{τ_A})`.
/-- Helper for Corollary 19.16: once harmonicity outside `A` is available for the discrete
random-walk kernel, optional stopping yields the first-entrance expectation formula. -/
private theorem electricalPotential_eq_expectation_at_firstEntrance_aux
    {A : Set E} {u : E → ℝ} {x : E}
    (hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u)
    (hx : x ∉ A)
    (hτ : (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1) :
    u x = ∫ ω, u (stoppedValue X (hittingAfter X A 1) ω) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let τ₀ : Ω → ℕ∞ := hittingAfter X A 0
  let Y : ℕ → Ω → ℝ := fun n ω ↦ u (X n ω)
  let hReal : IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
    initialState_ae_eq_start (P := P) (X := X) (p := p) hReal x
  have hτ1_ae_ne_top : ∀ᵐ ω ∂μ, hittingAfter X A 1 ω ≠ ⊤ :=
    hittingAfter_one_ae_ne_top_of_prob_eq_one
      (P := P) (X := X) (p := p) (A := A) (x := x) hReal hτ
  have hτ01_ae : ∀ᵐ ω ∂μ, τ₀ ω = hittingAfter X A 1 ω := by
    simpa [τ₀] using
      firstEntranceTimeFromZero_ae_eq_hittingAfter_one
        (P := P) (X := X) (A := A) (x := x) hx hstart
  have hτ0_ae_ne_top : ∀ᵐ ω ∂μ, τ₀ ω ≠ ⊤ := by
    simpa [τ₀] using
      firstEntranceTimeFromZero_ae_ne_top
        (P := P) (X := X) (A := A) (x := x) hτ01_ae hτ1_ae_ne_top
  have hu_bdd : Bornology.IsBounded (Set.range u) := by
    -- Proof comment: the state space is finite, so every real-valued function on it has bounded
    -- range.
    simpa using (Set.toFinite (Set.range u)).isBounded
  have htrunc :
      ∀ n,
        ∫ ω, truncatedStoppedPotential (X := X) A u n ω ∂μ = u x :=
    truncatedStoppedPotential_expectation_eq_start
      (P := P) (X := X) (p := p) (A := A) (u := u) (x := x)
      hu_bdd hu_harmonic hstart
  have hlimit_eq :
      ∫ ω, stoppedPotentialAtFirstEntrance (X := X) A u ω ∂μ = u x := by
    simpa [μ] using
      truncatedStoppedPotentialIntegral_eq_stoppedValue
        (P := P) (X := X) (A := A) (u := u) (x := x) hReal
        hu_bdd hτ0_ae_ne_top htrunc
  have hvalue_ae :
      (fun ω ↦ stoppedPotentialAtFirstEntrance (X := X) A u ω) =ᵐ[μ]
        fun ω ↦ u (stoppedValue X τ₀ ω) := by
    simpa [τ₀] using
      stoppedPotentialAtFirstEntrance_ae_eq_u_stoppedValue
        (P := P) (X := X) (A := A) (u := u) (x := x)
  have htransport_ae :
      (fun ω ↦ u (stoppedValue X τ₀ ω)) =ᵐ[μ]
        fun ω ↦ u (stoppedValue X (hittingAfter X A 1) ω) := by
    simpa [τ₀] using
      u_stoppedValue_firstEntrance_transport_ae
        (P := P) (X := X) (A := A) (u := u) (x := x) hτ01_ae
  calc
    u x = ∫ ω, stoppedPotentialAtFirstEntrance (X := X) A u ω ∂μ := hlimit_eq.symm
    _ = ∫ ω, u (stoppedValue X τ₀ ω) ∂μ := integral_congr_ae hvalue_ae
    _ = ∫ ω, u (stoppedValue X (hittingAfter X A 1) ω) ∂μ := integral_congr_ae htransport_ae

include p P X
/-- Corollary 19.16: on a finite conductance network, the value of an electrical potential at a
starting point `x ∉ A` equals the expected value at the first entrance point into `A`, provided
that this first entrance time is almost surely finite. In Lean, `X_{τ_A}` is represented by
`stoppedValue X (hittingAfter X A 1)`. -/
theorem electricalPotential_eq_expectation_at_firstEntrance
    {A : Set E} {u : E → ℝ} {x : E}
    (hu : IsElectricalPotential C A u) (hx : x ∉ A)
    (hτ : (P x : Measure Ω) {ω | hittingAfter X A 1 ω < ⊤} = 1) :
    u x = ∫ ω, u (stoppedValue X (hittingAfter X A 1) ω) ∂(P x : Measure Ω) := by
  -- Route correction: the martingale proof is already closed in the private auxiliary theorem,
  -- so the public wrapper should only bridge `hu` to harmonicity and then specialize that result.
  have hu_harmonic : IsHarmonicOutside (discreteMatrixKernel p) A u :=
    electricalPotential_isHarmonicOn_compl (p := p) (C := C) hu
  -- Proof comment: fixing `p`, `P`, and `X` at the call site prevents instance search from
  -- creating a fresh kernel metavariable in the final wrapper application.
  simpa using
    electricalPotential_eq_expectation_at_firstEntrance_aux
      (P := P) (X := X) (p := p) (A := A) (u := u) (x := x) hu_harmonic hx hτ

end ProbabilityTheory

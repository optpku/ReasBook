/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.TotalVariation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Lemma_18_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_12
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

section

variable (κ : Kernel E E) [IsMarkovKernel κ]
variable [Kernel.IsIrreducible (Measure.count : Measure E) κ]
variable (π : ProbabilityMeasure E)

/-- Helper for Theorem 18.13: `tendsToInvariantFromState κ π x` packages convergence in total
variation of the `n`-step law started from the Dirac state `x`. -/
private abbrev tendsToInvariantFromState (x : E) : Prop :=
  Tendsto
    (fun n : ℕ ↦
      totalVariationDistance
        (⟨(κ ^ n) ∘ₘ diracProba x, inferInstance⟩ : ProbabilityMeasure E)
        π)
    atTop (𝓝 0)

/-- Helper for Theorem 18.13: `tendsToInvariantFromMeasure κ π μ` packages convergence in total
variation of the `n`-step law started from the initial law `μ`. -/
private abbrev tendsToInvariantFromMeasure (μ : ProbabilityMeasure E) : Prop :=
  Tendsto
    (fun n : ℕ ↦
      totalVariationDistance
        (⟨(κ ^ n) ∘ₘ μ, inferInstance⟩ : ProbabilityMeasure E)
        π)
    atTop (𝓝 0)

/-- Helper for Theorem 18.13: on a countable discrete state space, a Markov kernel is recovered
from its singleton transition masses via `discreteMatrixKernel`. -/
private theorem discreteKernel_eq_discreteMatrixKernel [Countable E] :
    discreteMatrixKernel (fun x y : E ↦ κ x ({y} : Set E)) = κ := by
  -- Proof comment: equality of kernels is equality of row measures, and on a countable discrete
  -- space a measure is determined by its singleton masses.
  apply Kernel.ext
  intro x
  refine Measure.ext_of_singleton
    (μ := discreteMatrixKernel (fun x y : E ↦ κ x ({y} : Set E)) x)
    (ν := κ x) fun y ↦ ?_
  rw [discreteMatrixKernel_apply]
  exact Measure.sum_smul_dirac_singleton
    (f := fun z : E ↦ κ x ({z} : Set E)) (a := y)

/-- Helper for Theorem 18.13: starting from `diracProba x`, the singleton mass of the composed
`n`-step law is the corresponding singleton mass of `(κ ^ n) x`. -/
private theorem kernelPowCompDirac_apply_singleton (x y : E) (n : ℕ) :
    ((κ ^ n) ∘ₘ diracProba x) ({y} : Set E) = (κ ^ n) x ({y} : Set E) := by
  -- Proof comment: rewrite measure-kernel composition as kernel composition with a constant
  -- kernel and then evaluate the resulting Dirac integral.
  rw [MeasureTheory.Measure.comp_eq_comp_const_apply]
  rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton y)]
  rw [Kernel.const_apply]
  change ∫⁻ b, ((κ ^ n) b) ({y} : Set E) ∂(Measure.dirac x) = ((κ ^ n) x) ({y} : Set E)
  rw [lintegral_dirac' x ((κ ^ n).measurable_coe (MeasurableSet.singleton y))]

/-- Helper for Theorem 18.13: the signed gap on any measurable event is controlled by the total
variation distance. -/
private theorem eventMassSub_le_totalVariationDistance
    (μ ν : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A) :
    (ν : Measure E).real A - (μ : Measure E).real A ≤ totalVariationDistance μ ν := by
  let S : Set ℝ := {r : ℝ | ∃ f : E → ℝ,
    Measurable f ∧
      (∀ x, ‖f x‖ ≤ 1) ∧
      r = ∫ x, f x ∂(μ : Measure E) - ∫ x, f x ∂(ν : Measure E)}
  have hS_bddAbove : BddAbove S := by
    refine ⟨2, ?_⟩
    intro r hr
    rcases hr with ⟨f, hf_meas, hf_bound, rfl⟩
    have hμ_norm :
        ‖∫ x, f x ∂(μ : Measure E)‖ ≤ 1 := by
      simpa using
        (norm_integral_le_of_norm_le_const (μ := (μ : Measure E)) (C := 1)
          (ae_of_all _ hf_bound))
    have hν_norm :
        ‖∫ x, f x ∂(ν : Measure E)‖ ≤ 1 := by
      simpa using
        (norm_integral_le_of_norm_le_const (μ := (ν : Measure E)) (C := 1)
          (ae_of_all _ hf_bound))
    have hμ_bounds :
        -1 ≤ ∫ x, f x ∂(μ : Measure E) ∧ ∫ x, f x ∂(μ : Measure E) ≤ 1 := by
      exact abs_le.mp (by simpa using hμ_norm)
    have hν_bounds :
        -1 ≤ ∫ x, f x ∂(ν : Measure E) ∧ ∫ x, f x ∂(ν : Measure E) ≤ 1 := by
      exact abs_le.mp (by simpa using hν_norm)
    linarith
  let g : E → ℝ := fun x ↦
    Aᶜ.indicator (fun _ : E ↦ (1 : ℝ)) x - A.indicator (fun _ : E ↦ (1 : ℝ)) x
  have hg_meas : Measurable g := by
    -- Proof comment: the sign test is a difference of measurable indicator functions.
    exact (Measurable.indicator measurable_const hA.compl).sub
      (Measurable.indicator measurable_const hA)
  have hg_bound : ∀ x, ‖g x‖ ≤ 1 := by
    -- Proof comment: the sign test only takes the values `1` and `-1`.
    intro x
    by_cases hx : x ∈ A <;> simp [g, hx]
  have hμAc :
      Integrable (Aᶜ.indicator (fun _ : E ↦ (1 : ℝ))) (μ : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  have hμA :
      Integrable (A.indicator (fun _ : E ↦ (1 : ℝ))) (μ : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hνAc :
      Integrable (Aᶜ.indicator (fun _ : E ↦ (1 : ℝ))) (ν : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  have hνA :
      Integrable (A.indicator (fun _ : E ↦ (1 : ℝ))) (ν : Measure E) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hg_value :
      ∫ x, g x ∂(μ : Measure E) - ∫ x, g x ∂(ν : Measure E) =
        2 * ((ν : Measure E).real A - (μ : Measure E).real A) := by
    -- Proof comment: the sign test converts the integral difference into twice the event-mass
    -- gap by splitting over `A` and `Aᶜ`.
    rw [integral_sub hμAc hμA, integral_sub hνAc hνA]
    simp [measureReal_compl, hA]
    ring
  have hg_mem :
      2 * ((ν : Measure E).real A - (μ : Measure E).real A) ∈ S := by
    exact ⟨g, hg_meas, hg_bound, hg_value.symm⟩
  have hsSup_ge :
      2 * ((ν : Measure E).real A - (μ : Measure E).real A) ≤ sSup S :=
    le_csSup hS_bddAbove hg_mem
  -- Proof comment: the sign test is one admissible bounded measurable witness in the dual
  -- characterization of total variation.
  rw [totalVariationDistance_eq_sSup_bounded_measurable]
  linarith

/-- Helper for Theorem 18.13: the gap on the singleton event `{x}` is bounded by total variation.
-/
private theorem singletonMass_gap_le_totalVariationDistance
    (μ ν : ProbabilityMeasure E) (x : E) :
    (ν : Measure E).real ({x} : Set E) - (μ : Measure E).real ({x} : Set E) ≤
      totalVariationDistance μ ν := by
  -- Proof comment: specialize the general measurable-event estimate to the singleton event.
  exact eventMassSub_le_totalVariationDistance (μ := μ) (ν := ν)
    (A := ({x} : Set E)) (MeasurableSet.singleton x)

/-- Helper for Theorem 18.13: an invariant distribution of an irreducible discrete kernel gives
strictly positive mass to every singleton state. -/
private theorem invariant_apply_singleton_pos_of_irreducible [Countable E]
    (hπ : Kernel.Invariant κ (π : Measure E)) (x : E) :
    0 < (π : Measure E) ({x} : Set E) := by
  classical
  have hsource :
      ∃ y : E, 0 < (π : Measure E) ({y} : Set E) := by
    by_contra hnone
    push Not at hnone
    have hzero : (π : Measure E) = 0 := by
      refine Measure.ext_of_singleton fun y ↦ ?_
      show (π : Measure E) ({y} : Set E) = 0
      exact le_antisymm (hnone y) bot_le
    have hone_univ : ((π : Measure E) Set.univ) = 1 := by
      simpa using (measure_univ : ((π : Measure E)) Set.univ = 1)
    have hcontr : (0 : ℝ≥0∞) = 1 := by simpa [hzero] using hone_univ
    exact zero_ne_one hcontr
  rcases hsource with ⟨y, hy_pos⟩
  have hx_pos : (Measure.count : Measure E) ({x} : Set E) > 0 := by
    simp
  rcases (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ).irreducible
      (A := ({x} : Set E)) (MeasurableSet.singleton x) hx_pos y with ⟨n, hn⟩
  have hpowπ : ((κ ^ n) ∘ₘ (π : Measure E)) ({x} : Set E) = (π : Measure E) ({x} : Set E) := by
    simpa using congrArg (fun μ : Measure E ↦ μ ({x} : Set E))
      (kernelInvariant_pow_comp_eq_self (κ := κ) hπ n)
  have hcomp_pos : 0 < ((κ ^ n) ∘ₘ (π : Measure E)) ({x} : Set E) := by
    rw [MeasureTheory.Measure.comp_eq_comp_const_apply]
    rw [Kernel.comp_apply' _ _ _ (MeasurableSet.singleton x)]
    rw [Kernel.const_apply]
    have hsingleton_pos :
        0 < ∫⁻ z in ({y} : Set E), (κ ^ n) z ({x} : Set E) ∂(π : Measure E) := by
      rw [MeasureTheory.lintegral_singleton]
      exact ENNReal.mul_pos hn.ne' hy_pos.ne'
    have hmono :
        ∫⁻ z in ({y} : Set E), (κ ^ n) z ({x} : Set E) ∂(π : Measure E) ≤
          ∫⁻ z in Set.univ, (κ ^ n) z ({x} : Set E) ∂(π : Measure E) :=
      MeasureTheory.lintegral_mono_set (show ({y} : Set E) ⊆ Set.univ from Set.subset_univ _)
    exact lt_of_lt_of_le hsingleton_pos (by simpa [Measure.restrict_univ] using hmono)
  simpa [hpowπ] using hcomp_pos

-- Proof sketch: irreducibility together with the invariant-distribution hypothesis implies
-- positive recurrence by Theorem 17.51, so Theorem 18.12 yields `(i) → (ii)`. The implications
-- `(ii) → (iii)` and `(iv) → (ii)` are immediate. For `(iii) → (i)`, argue by contraposition and
-- use the cyclic decomposition from Theorem 18.4 to show that a non-aperiodic chain stays a
-- positive total variation distance away from `π` along infinitely many times.
/-- Theorem 18.13: for an irreducible discrete-time Markov kernel with invariant distribution `π`
(equivalently, for an irreducible positive recurrent chain with invariant distribution `π`), the
following are equivalent: (i) the chain is aperiodic; (ii) for every
starting state `x`, equivalently for the evolved Dirac initial law `(κ ^ n) ∘ₘ δ_x`, the law at
time `n` converges to `π` in total variation; (iii) this total-variation convergence holds for
some starting state `x`; (iv) for every initial distribution `μ ∈ M_1(E)`, the evolved law
`(κ ^ n) ∘ₘ μ` converges to `π` in total variation. -/
theorem aperiodic_tfae_tendsto_totalVariation_invariantDistribution
    (hπ : Kernel.Invariant κ (π : Measure E)) :
    List.TFAE
      [ IsAperiodic κ,
        ∀ x : E, tendsToInvariantFromState (κ := κ) (π := π) x,
        ∃ x : E, tendsToInvariantFromState (κ := κ) (π := π) x,
        ∀ μ : ProbabilityMeasure E, tendsToInvariantFromMeasure (κ := κ) (π := π) μ ] := by
  classical
  let _ : Countable E := countableOfIrreducibleCountKernel (κ := κ)
  let q : E → E → ℝ≥0∞ := fun x y ↦ κ x ({y} : Set E)
  have hκeq : discreteMatrixKernel q = κ := by
    -- Proof comment: the normalized matrix `q` encodes the same kernel row-by-row.
    simpa [q] using discreteKernel_eq_discreteMatrixKernel (κ := κ)
  letI : IsMarkovKernel (discreteMatrixKernel q) := by
    simpa [q, hκeq] using (inferInstance : IsMarkovKernel κ)
  letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q) := by
    simpa [q, hκeq] using
      (inferInstance : Kernel.IsIrreducible (Measure.count : Measure E) κ)
  have hπq : Kernel.Invariant (discreteMatrixKernel q) (π : Measure E) := by
    -- Proof comment: stationarity transports directly across the kernel normalization.
    simpa [q, hκeq] using hπ
  obtain ⟨Ω, mΩ, P, X, hreal⟩ :
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : E → ProbabilityMeasure Ω)
        (X : ℕ → Ω → E),
        IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P X := by
    simpa using
      (existsMarkovProcessRealization_of_markovKernelPowers.{u, u}
        (κ₁ := discreteMatrixKernel q))
  tfae_have 1 → 4 := by
    intro haperiodic
    have haperiodicq : IsAperiodic (discreteMatrixKernel q) := by
      -- Proof comment: aperiodicity is another owner-side property that survives the same
      -- normalization.
      simpa [q, hκeq] using haperiodic
    have htend :
        ∀ μ : ProbabilityMeasure E,
          Tendsto (fun n : ℕ ↦ totalVariationDistance (nStepLaw q μ n) π) atTop (𝓝 0) := by
      intro μ
      exact
        @nStepTotalVariationDistance_tendsto_zero_to_invariantDistribution_of_irreducible_aperiodic_positiveRecurrent
          E _ _ Ω mΩ q P X hreal inferInstance haperiodicq π hπq μ
    intro μ
    -- Proof comment: rewrite the owner `nStepLaw` back into the original kernel-power notation.
    simpa [q, tendsToInvariantFromMeasure, nStepLaw, hκeq] using htend μ
  tfae_have 4 → 2 := by
    intro hμ x
    -- Proof comment: Dirac initial laws are special cases of arbitrary initial distributions.
    simpa using hμ (diracProba x)
  tfae_have 2 → 3 := by
    intro hx
    have hnonempty : Nonempty E := by
      by_contra hE
      letI : IsEmpty E := not_nonempty_iff.mp hE
      have huniv : (Set.univ : Set E) = ∅ := by
        ext e
        exact False.elim (isEmptyElim e)
      have hzero : (π : Measure E) Set.univ = 0 := by
        simpa [huniv] using (Measure.empty (μ := (π : Measure E)))
      have hone : (π : Measure E) Set.univ = 1 := by
        simpa using (measure_univ : (π : Measure E) Set.univ = 1)
      exact zero_ne_one (hzero.symm.trans hone)
    let x : E := Classical.choice hnonempty
    exact ⟨x, hx x⟩
  tfae_have 3 → 1 := by
    intro hx
    by_contra hnotAperiodic
    rcases hx with ⟨x, hxTendsto⟩
    have hxPeriod_ne_one : statePeriod κ x ≠ 1 := by
      intro hxPeriod
      apply hnotAperiodic
      intro y
      calc
        statePeriod κ y = statePeriod κ x := statePeriod_eq (κ := κ) y x
        _ = 1 := hxPeriod
    have hπx_pos : 0 < (π : Measure E) ({x} : Set E) :=
      invariant_apply_singleton_pos_of_irreducible (κ := κ) (π := π) hπ x
    have hπx_toReal_pos : 0 < ((π : Measure E) ({x} : Set E)).toReal := by
      exact ENNReal.toReal_pos (ne_of_gt hπx_pos) (measure_ne_top _ _)
    rcases Metric.tendsto_atTop.1 hxTendsto
        ((((π : Measure E) ({x} : Set E)).toReal) / 2)
        (by linarith) with ⟨N, hN⟩
    by_cases hperiod_zero : statePeriod κ x = 0
    · let n : ℕ := N + 1
      have hndvd : ¬ statePeriod κ x ∣ n := by
        simp [hperiod_zero, n]
      have hreturn_zero : ((κ ^ n) x) ({x} : Set E) = 0 := by
        by_contra hpos
        have hmem : n ∈ positiveTransitionStepSet κ x x := by
          simpa [mem_positiveTransitionStepSet_iff] using (bot_lt_iff_ne_bot.mpr hpos)
        exact hndvd (statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hmem)
      let μn : ProbabilityMeasure E := ⟨(κ ^ n) ∘ₘ diracProba x, inferInstance⟩
      have hmass_zero : ((μn : Measure E) ({x} : Set E)).toReal = 0 := by
        -- Proof comment: when the self-return mass vanishes, the singleton mass of the evolved
        -- Dirac law vanishes as well.
        rw [show ((μn : Measure E) ({x} : Set E)) = ((κ ^ n) ∘ₘ diracProba x) ({x} : Set E) by rfl]
        rw [kernelPowCompDirac_apply_singleton (κ := κ) x x n, hreturn_zero]
        simp
      have hgap' :
          (π : Measure E).real ({x} : Set E) - (μn : Measure E).real ({x} : Set E) ≤
            totalVariationDistance μn π :=
        singletonMass_gap_le_totalVariationDistance (μ := μn) (ν := π) x
      have hgap :
          ((π : Measure E) ({x} : Set E)).toReal ≤ totalVariationDistance μn π := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, hmass_zero] at hgap'
        linarith
      have hsmall : totalVariationDistance μn π <
          (((π : Measure E) ({x} : Set E)).toReal) / 2 := by
        have hn_ge : N ≤ n := by omega
        have htv_nonneg : 0 ≤ totalVariationDistance μn π := by
          rw [totalVariationDistance_eq_half_totalVariationNorm]
          positivity
        simpa [n, μn, abs_of_nonneg htv_nonneg] using hN n hn_ge
      linarith
    · let n : ℕ := N * statePeriod κ x + 1
      have hndvd : ¬ statePeriod κ x ∣ n := by
        -- Proof comment: any divisor of `N * statePeriod κ x + 1` would also divide `1`, forcing
        -- the common period to be `1`, contrary to the periodic obstruction at `x`.
        intro hdvd
        have hmod_zero : n % statePeriod κ x = 0 := Nat.mod_eq_zero_of_dvd hdvd
        have hlt : 1 < statePeriod κ x := by
          omega
        have hmod_one : n % statePeriod κ x = 1 := by
          simp [n, Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
        omega
      have hreturn_zero : ((κ ^ n) x) ({x} : Set E) = 0 := by
        by_contra hpos
        have hmem : n ∈ positiveTransitionStepSet κ x x := by
          simpa [mem_positiveTransitionStepSet_iff] using (bot_lt_iff_ne_bot.mpr hpos)
        exact hndvd (statePeriod_dvd_of_mem_positiveTransitionStepSet κ x hmem)
      let μn : ProbabilityMeasure E := ⟨(κ ^ n) ∘ₘ diracProba x, inferInstance⟩
      have hmass_zero : ((μn : Measure E) ({x} : Set E)).toReal = 0 := by
        -- Proof comment: at the obstructed times, the evolved Dirac law has zero singleton mass
        -- at the starting state.
        rw [show ((μn : Measure E) ({x} : Set E)) = ((κ ^ n) ∘ₘ diracProba x) ({x} : Set E) by rfl]
        rw [kernelPowCompDirac_apply_singleton (κ := κ) x x n, hreturn_zero]
        simp
      have hgap' :
          (π : Measure E).real ({x} : Set E) - (μn : Measure E).real ({x} : Set E) ≤
            totalVariationDistance μn π :=
        singletonMass_gap_le_totalVariationDistance (μ := μn) (ν := π) x
      have hgap :
          ((π : Measure E) ({x} : Set E)).toReal ≤ totalVariationDistance μn π := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def, hmass_zero] at hgap'
        linarith
      have hsmall : totalVariationDistance μn π <
          (((π : Measure E) ({x} : Set E)).toReal) / 2 := by
        have hn_ge : N ≤ n := by
          have hperiod_pos : 0 < statePeriod κ x := Nat.pos_of_ne_zero hperiod_zero
          calc
            N ≤ N * statePeriod κ x := Nat.le_mul_of_pos_right _ hperiod_pos
            _ ≤ n := by simp [n]
        have htv_nonneg : 0 ≤ totalVariationDistance μn π := by
          rw [totalVariationDistance_eq_half_totalVariationNorm]
          positivity
        simpa [n, μn, abs_of_nonneg htv_nonneg] using hN n hn_ge
      linarith
  tfae_finish

end

end ProbabilityTheory

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u u' v w

namespace ProbabilityTheory

variable {Omega : Type u} [MeasurableSpace Omega]
variable {Omega' : Type u'} [MeasurableSpace Omega']
variable {E : Type v} [MeasurableSpace E]
variable {F : Type w} [MeasurableSpace F]

/-- The intensity measure `μκ` obtained by applying the transition kernel `κ` to the source
measure `μ`. -/
abbrev kernelImageMeasure (mu : Measure E) (kappa : Kernel E F) : Measure F :=
  kappa ∘ₘ mu

-- Proof sketch: unfold `kernelImageMeasure`; this is the standard application formula for
-- composing a kernel with a measure.
/-- Evaluating `kernelImageMeasure μ κ` on a measurable set integrates the kernel rows against the
source measure `μ`. -/
theorem kernelImageMeasure_apply
    (mu : Measure E) (kappa : Kernel E F) {A : Set F} (hA : MeasurableSet A) :
    kernelImageMeasure mu kappa A = ∫⁻ x, kappa x A ∂mu := by
  -- Proof comment: `kernelImageMeasure μ κ` is the measure-kernel composition `κ ∘ₘ μ`,
  -- so evaluating it on a measurable set is exactly the bind formula.
  rw [kernelImageMeasure, Measure.bind_apply hA (Kernel.aemeasurable _)]

/-- The Laplace transform identity that characterizes the kernel-colored random measure `X^κ` in
Theorem 24.24. -/
def HasKernelColoredLaplaceTransform
    [TopologicalSpace F] [OpensMeasurableSpace F] [BorelSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E)
    (kappa : Kernel E F) [IsMarkovKernel kappa] (Xkappa : Omega → Measure F)
    (hXkappa : IsRandomMeasure P Xkappa) : Prop :=
  ∀ f : CompactlySupportedContinuousMap F NNReal,
    (∫ nu, Real.exp (-∫ y, (f y : ℝ) ∂nu)
      ∂(P.map hXkappa.1.aemeasurable : Measure (Measure F))) =
      Real.exp (∫ x, ∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kappa x ∂mu)

-- Proof sketch: unfold `HasKernelColoredLaplaceTransform`; it is exactly the Poisson
-- kernel-coloring Laplace formula displayed in the textbook proof.
/-- Unfolding `HasKernelColoredLaplaceTransform` gives the exponential Laplace formula for the
kernel-colored random measure. -/
theorem hasKernelColoredLaplaceTransform_iff
    [TopologicalSpace F] [OpensMeasurableSpace F] [BorelSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xkappa : Omega → Measure F) (hXkappa : IsRandomMeasure P Xkappa) :
    HasKernelColoredLaplaceTransform P mu kappa Xkappa hXkappa ↔
      ∀ f : CompactlySupportedContinuousMap F NNReal,
        (∫ nu, Real.exp (-∫ y, (f y : ℝ) ∂nu)
          ∂(P.map hXkappa.1.aemeasurable : Measure (Measure F))) =
          Real.exp (∫ x, ∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kappa x ∂mu) := by
  -- Proof comment: this theorem only unfolds the defining predicate.
  rfl

/-- The kernel-colored random measure `X^κ` obtained from a genuine marked point process on
`E × F` by forgetting the source coordinate and retaining only the mark coordinate. This owner
handles multiplicities correctly, since distinct atoms of the marked process remain distinct before
the projection to `F`. -/
noncomputable def kernelColoredRandomMeasure
    (Xi : Omega → Measure (E × F)) : Omega → Measure F :=
  fun ω ↦ (Xi ω).snd

/-- Helper for Theorem 24.24: the kernel-colored random measure `X^κ` is measurable as a
`Measure F`-valued map once the marked process itself is a random measure. -/
theorem measurable_kernelColoredRandomMeasure
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (Xi : Omega → Measure (E × F))
    (hXi : IsRandomMeasure P Xi) :
    Measurable (kernelColoredRandomMeasure Xi) := by
  -- Proof comment: `kernelColoredRandomMeasure Xi` is the composition of `Xi` with the measurable
  -- marginal map `ρ ↦ ρ.snd`.
  simpa [kernelColoredRandomMeasure, Measure.snd] using
    (Measure.measurable_map Prod.snd measurable_snd).comp hXi.1

/-- Helper for Theorem 24.24: evaluating the projected kernel-colored random measure on a
measurable set is a measurable `ℝ≥0∞`-valued random variable. -/
theorem measurable_kernelColoredRandomMeasure_apply
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (Xi : Omega → Measure (E × F))
    (hXi : IsRandomMeasure P Xi) {A : Set F} (hA : MeasurableSet A) :
    Measurable fun ω ↦ kernelColoredRandomMeasure Xi ω A := by
  -- Proof comment: measurable-set evaluation is measurable on the measure-valued target, so
  -- compose it with the measurable projection owner `ω ↦ (Xi ω).snd`.
  exact (Measure.measurable_coe hA).comp (measurable_kernelColoredRandomMeasure P Xi hXi)

/-- Helper for Theorem 24.24: finiteness on one compact exhaustion implies local finiteness of the
underlying measure. -/
theorem compactExhaustionFinite_isLocallyFiniteMeasure
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (nu : Measure F) (K : CompactExhaustion F) (hnu : ∀ n, nu (K n) < ⊤) :
    IsLocallyFiniteMeasure nu := by
  -- Proof comment: an exhaustion piece eventually gives a compact neighborhood of each point, and
  -- the assumed finiteness on every exhaustion piece supplies the needed finite neighborhood mass.
  refine ⟨fun y ↦ ?_⟩
  rcases K.exists_mem_nhds y with ⟨n, hKn⟩
  exact ⟨K n, hKn, hnu n⟩

/-- Helper for Theorem 24.24: almost-sure finiteness on a compact exhaustion upgrades to almost-
sure local finiteness. -/
theorem ae_isLocallyFiniteMeasure_of_compactExhaustionFinite
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    {P : ProbabilityMeasure Omega} {X : Omega → Measure F}
    (K : CompactExhaustion F)
    (hX : ∀ n, ∀ᵐ ω ∂(P : Measure Omega), X ω (K n) < ⊤) :
    ∀ᵐ ω ∂(P : Measure Omega), IsLocallyFiniteMeasure (X ω) := by
  -- Proof comment: `ae_all_iff` places the whole exhaustion on one full-measure event, where the
  -- pointwise compact-exhaustion lemma applies.
  filter_upwards [ae_all_iff.2 hX] with ω hω
  exact compactExhaustionFinite_isLocallyFiniteMeasure (X ω) K hω

/-- Helper for Theorem 24.24: the small Laplace scales are `s_n = (n + 1)⁻¹` on `ℝ`. -/
private def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Theorem 24.24: the extended-real Laplace kernel `ennrealExpNeg` is measurable. -/
private theorem measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) :=
    Real.measurable_exp.comp ENNReal.measurable_toReal.neg
  -- Proof comment: rewrite the `∞` case as a piecewise constant patch over the singleton
  -- `{∞}`.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (⊤ : ℝ≥0∞)) hcore)

/-- Helper for Theorem 24.24: the extended-real Laplace kernel is pointwise nonnegative. -/
private theorem ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ⊤
  · -- Proof comment: at `∞`, the kernel is exactly `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: away from `∞`, the kernel is an ordinary exponential.
    simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Theorem 24.24: the extended-real Laplace kernel is bounded above by `1`. -/
private theorem ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ⊤
  · -- Proof comment: the `∞` value is `0`, so the estimate is immediate.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: on finite inputs the exponent is nonpositive, hence its exponential is at
    -- most `1`.
    have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Theorem 24.24: the scaled Laplace kernel tends to the finiteness indicator. -/
private theorem ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ⊤ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ⊤
  · -- Proof comment: positive scales keep `∞` at `∞`, so the whole sequence is constantly `0`.
    have hconst :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          fun _ ↦ (0 : ℝ) := by
      funext n
      have hn : 0 < (n : ℝ) + 1 := by
        positivity
      have hs_pos : 0 < invSuccScaleReal n := by
        simpa [invSuccScaleReal] using one_div_pos.mpr hn
      have hs_pos' : 0 < ENNReal.ofReal (invSuccScaleReal n) := ENNReal.ofReal_pos.mpr hs_pos
      simp [hy, ennrealExpNeg, ne_of_gt hs_pos']
    rw [hconst]
    simp [hy]
  · -- Proof comment: on finite `y`, rewrite the kernel as an ordinary exponential and use
    -- continuity at `0`.
    have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
      change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * y.toReal) Filter.atTop
          (nhds (0 * y.toReal)) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    have hexp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) Filter.atTop
          (nhds (Real.exp (-(0 * y.toReal)))) := by
      exact hcont.continuousAt.tendsto.comp hmul
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) := by
      funext n
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp [invSuccScaleReal]) hy
      have hs_nonneg : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
      change Real.exp (-((ENNReal.ofReal (invSuccScaleReal n)).toReal * y.toReal)) = _
      rw [ENNReal.toReal_ofReal hs_nonneg]
    rw [hrewrite]
    simpa [hy] using hexp

/-- Helper for Theorem 24.24: small-scale Laplace expectations converge to the probability that an
extended-real random variable is finite. -/
private theorem laplaceInvSuccTendstoMeasureFinite
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {Y : α → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ⊤}).toReal) := by
  let A : Set α := {a | Y a < ⊤}
  let G : α → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    -- Proof comment: measurability comes from the measurable Laplace kernel and the measurable
    -- variable `Y`.
    exact (measurable_ennrealExpNeg.comp (measurable_const.mul hY)).aestronglyMeasurable
  have hBound :
      ∀ n, ∀ᵐ a ∂μ, ‖ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with a
    have hnonneg : 0 ≤ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) :=
      ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ≤ 1 :=
      ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLim :
      ∀ᵐ a ∂μ, Filter.Tendsto
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a))
        Filter.atTop (nhds (G a)) := by
    filter_upwards with a
    by_cases ha : Y a = ⊤
    · -- Proof comment: at `∞` the pointwise limit is `0`, matching the indicator complement.
      simpa [A, G, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · -- Proof comment: on finite points the pointwise limit is `1`, matching the indicator.
      have ha' : Y a < ⊤ := lt_top_iff_ne_top.mpr ha
      simpa [A, G, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : α ↦ (1 : ℝ)) hF_meas (integrable_const 1) hBound hLim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hGIntegral : ∫ a, G a ∂μ = (μ A).toReal := by
    -- Proof comment: integrating the finiteness indicator recovers the measure of the finiteness
    -- event because `μ` is finite.
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hGIntegral] using hDCT

/-- Helper for Theorem 24.24: evaluating the projected marked process on a measurable mark set has
the Poisson Laplace transform with parameter `(μκ)(A)`. -/
theorem kernelColoredRandomMeasure_apply_laplace
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) [SigmaFinite mu]
    (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    {A : Set F} (hA : MeasurableSet A) (t : ENNReal) :
    ∫ ω, ennrealExpNeg (t * kernelColoredRandomMeasure Xi ω A) ∂(P : Measure Omega) =
      ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * kernelImageMeasure mu kappa A) := by
  let f : NonnegativeMeasurableFunction (E × F) :=
    ⟨Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t),
      measurable_const.indicator (measurable_snd hA)⟩
  have hLintegral :
      (fun ω ↦ ∫⁻ z, f z ∂Xi ω) =
        (fun ω ↦ t * kernelColoredRandomMeasure Xi ω A) := by
    funext ω
    -- Proof comment: the test function is the constant `t` on the mark cylinder
    -- `Prod.snd ⁻¹' A`, so its lower integral is `t` times the projected mass of `A`.
    change
      ∫⁻ z, Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t) z ∂Xi ω =
        t * kernelColoredRandomMeasure Xi ω A
    rw [lintegral_indicator_const (measurable_snd hA)]
    rw [kernelColoredRandomMeasure, Measure.snd_apply hA]
  have hExponent :
      ∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z)) ∂(mu ⊗ₘ kappa) =
        (1 - ENNReal.ofReal (ennrealExpNeg t)) * kernelImageMeasure mu kappa A := by
    -- Proof comment: the Laplace exponent vanishes off the mark cylinder and is constant on it,
    -- so only the projected intensity mass `(μκ)(A)` remains.
    change
      ∫⁻ z,
        (1 : ℝ≥0∞) -
          ENNReal.ofReal
            (ennrealExpNeg (Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t) z)) ∂(mu ⊗ₘ kappa) =
        (1 - ENNReal.ofReal (ennrealExpNeg t)) * kernelImageMeasure mu kappa A
    have hIntegrand :
        (fun z : E × F ↦
          (1 : ℝ≥0∞) -
            ENNReal.ofReal
              (ennrealExpNeg (Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ t) z))) =
          Set.indicator (Prod.snd ⁻¹' A) (fun _ ↦ 1 - ENNReal.ofReal (ennrealExpNeg t)) := by
      funext z
      by_cases hz : z ∈ Prod.snd ⁻¹' A
      · simp [Set.indicator, hz]
      · simp [Set.indicator, hz, ennrealExpNeg]
    rw [hIntegrand, lintegral_indicator_const (measurable_snd hA)]
    rw [← Measure.snd_apply hA, Measure.snd_compProd]
  have hRaw :
      ∫ ω, ennrealExpNeg (∫⁻ z, f z ∂Xi ω) ∂(P : Measure Omega) =
        ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z)) ∂(mu ⊗ₘ kappa)) := by
    -- Proof comment: this is exactly Theorem 24.14 specialized to the mark-indicator test
    -- function `f`.
    simpa using poisson_point_process_laplaceTransform P (mu ⊗ₘ kappa) Xi hXi f
  have hLeft :
      (fun ω ↦ ennrealExpNeg (∫⁻ z, f z ∂Xi ω)) =
        (fun ω ↦ ennrealExpNeg (t * kernelColoredRandomMeasure Xi ω A)) := by
    funext ω
    exact congrArg ennrealExpNeg (congrArg (fun g ↦ g ω) hLintegral)
  calc
    ∫ ω, ennrealExpNeg (t * kernelColoredRandomMeasure Xi ω A) ∂(P : Measure Omega)
        = ∫ ω, ennrealExpNeg (∫⁻ z, f z ∂Xi ω) ∂(P : Measure Omega) := by
            rw [hLeft]
    _ = ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (f z)) ∂(mu ⊗ₘ kappa)) := hRaw
    _ = ennrealExpNeg ((1 - ENNReal.ofReal (ennrealExpNeg t)) * kernelImageMeasure mu kappa A) := by
          rw [hExponent]

/-- Helper for Theorem 24.24: bounded measurable mark sets have finite projected mass almost
surely. -/
theorem kernelColoredRandomMeasure_apply_lt_top_ae
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) [SigmaFinite mu]
    (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    {A : Set F} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hMuKappaFinite : kernelImageMeasure mu kappa A ≠ ⊤) :
    ∀ᵐ ω ∂(P : Measure Omega), kernelColoredRandomMeasure Xi ω A < ⊤ := by
  let Y : Omega → ℝ≥0∞ := fun ω ↦ kernelColoredRandomMeasure Xi ω A
  let B : Set Omega := {ω | Y ω < ⊤}
  have hYMeas : Measurable Y :=
    measurable_kernelColoredRandomMeasure_apply P Xi hXi.1 hA
  have hLeft :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
          ∂(P : Measure Omega))
        Filter.atTop (nhds ((P : Measure Omega) B).toReal) := by
    simpa [Y, B] using
      laplaceInvSuccTendstoMeasureFinite (μ := (P : Measure Omega)) hYMeas
  have hsNonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      positivity
    simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
  have hCoeffNonneg : ∀ n, 0 ≤ 1 - Real.exp (-(invSuccScaleReal n)) := by
    intro n
    have hExpLeOne : Real.exp (-(invSuccScaleReal n)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith [hsNonneg n]
    linarith
  have hScaledEq :
      ∀ n,
        ((1 - ENNReal.ofReal
            (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
          kernelImageMeasure mu kappa A) =
          ENNReal.ofReal
            ((1 - Real.exp (-(invSuccScaleReal n))) *
              (kernelImageMeasure mu kappa A).toReal) := by
    intro n
    have hExpNonneg : 0 ≤ Real.exp (-(invSuccScaleReal n)) := Real.exp_nonneg _
    have hCoeffEq :
        1 - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n))) =
          ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n))) := by
      have hExpEval :
          ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)) =
            Real.exp (-(invSuccScaleReal n)) := by
        rw [ennrealExpNeg]
        simp [hsNonneg n]
      calc
        1 - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))
            = ENNReal.ofReal 1 - ENNReal.ofReal (Real.exp (-(invSuccScaleReal n))) := by
                rw [hExpEval]
                simp
        _ = ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n))) := by
              simpa using (ENNReal.ofReal_sub 1 hExpNonneg).symm
    rw [hCoeffEq]
    rw [ENNReal.ofReal_mul (hCoeffNonneg n), ENNReal.ofReal_toReal hMuKappaFinite]
  have hRight :
      Filter.Tendsto
        (fun n : ℕ ↦
          ennrealExpNeg
            (((1 - ENNReal.ofReal
                (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
              kernelImageMeasure mu kappa A)))
        Filter.atTop (nhds 1) := by
    have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
      change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hKernelLimit :
        Filter.Tendsto
          (fun n : ℕ ↦
            (1 - Real.exp (-(invSuccScaleReal n))) *
              (kernelImageMeasure mu kappa A).toReal)
          Filter.atTop (nhds 0) := by
      have hCont :
          Continuous fun r : ℝ ↦
            (1 - Real.exp (-r)) * (kernelImageMeasure mu kappa A).toReal :=
        (continuous_const.sub (Real.continuous_exp.comp continuous_neg)).mul continuous_const
      simpa using hCont.continuousAt.tendsto.comp hs
    have hRewrite :
        (fun n : ℕ ↦
          ennrealExpNeg
            (((1 - ENNReal.ofReal
                (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
              kernelImageMeasure mu kappa A))) =
          (fun n : ℕ ↦
            Real.exp
              (-((1 - Real.exp (-(invSuccScaleReal n))) *
                (kernelImageMeasure mu kappa A).toReal))) := by
      funext n
      rw [hScaledEq n, ennrealExpNeg]
      have hProdNonneg :
          0 ≤
            (1 - Real.exp (-(invSuccScaleReal n))) *
              (kernelImageMeasure mu kappa A).toReal :=
        mul_nonneg (hCoeffNonneg n) ENNReal.toReal_nonneg
      simp [hProdNonneg]
    rw [hRewrite]
    have hContExp : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    simpa using hContExp.continuousAt.tendsto.comp hKernelLimit
  have hLaplaceScaled :
      ∀ n,
        ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
          ∂(P : Measure Omega) =
          ennrealExpNeg
            (((1 - ENNReal.ofReal
                (ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n)))) *
              kernelImageMeasure mu kappa A)) := by
    intro n
    simpa [Y] using
      kernelColoredRandomMeasure_apply_laplace
        P mu kappa Xi hXi hA (ENNReal.ofReal (invSuccScaleReal n))
  have hLeftOne :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)
          ∂(P : Measure Omega))
        Filter.atTop (nhds 1) := by
    simpa [hLaplaceScaled] using hRight
  have hBOne : ((P : Measure Omega) B).toReal = 1 :=
    tendsto_nhds_unique hLeft hLeftOne
  have hBMeas : MeasurableSet B := measurableSet_lt hYMeas measurable_const
  have hBProbOne : (P : Measure Omega) B = 1 :=
    (ENNReal.toReal_eq_one_iff ((P : Measure Omega) B)).mp hBOne
  -- Proof comment: once the finiteness event has probability one, the projected mass is finite
  -- almost surely on the bounded measurable set `A`.
  simpa [B, Y] using
    (MeasureTheory.mem_ae_iff_prob_eq_one (μ := (P : Measure Omega)) hBMeas).2 hBProbOne

/-- Helper for Theorem 24.24: the Poisson counting law on `ℝ≥0∞` is supported on the natural
number range. -/
private theorem ae_mem_natCastRange_of_hasLawPoissonCount
    {P : Measure Omega} {Z : Omega → ENNReal} {lam : NNReal}
    (hZ :
      HasLaw Z
        (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure lam))
        P) :
    ∀ᵐ ω ∂P, Z ω ∈ Set.range (fun n : ℕ ↦ (n : ENNReal)) := by
  let S : Set ENNReal := Set.range (fun n : ℕ ↦ (n : ENNReal))
  have hS_meas : MeasurableSet S := Set.Countable.measurableSet (Set.countable_range _)
  have hS_meas_fun : Measurable fun y : ENNReal ↦ y ∈ S :=
    measurableSet_setOf.mp hS_meas
  refine (hZ.ae_iff hS_meas_fun).2 ?_
  rw [MeasureTheory.ae_iff]
  have hCompl :
      (Measure.map (fun n : ℕ ↦ (n : ENNReal)) (poissonMeasure lam)) Sᶜ = 0 := by
    rw [Measure.map_apply (measurable_of_countable (fun n : ℕ ↦ (n : ENNReal))) hS_meas.compl]
    have hPreimage : (fun n : ℕ ↦ (n : ENNReal)) ⁻¹' Sᶜ = ∅ := by
      ext n
      simp [S]
    simp [hPreimage]
  simpa using hCompl

/-- Helper for Theorem 24.24: every finite-intensity evaluation of a Poisson point process is
count-valued almost surely. -/
private theorem ae_eval_mem_natCastRange_of_isPoissonPointProcess
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    {P : ProbabilityMeasure Omega} {μ : Measure F} {X : Omega → Measure F}
    (hX : IsPoissonPointProcess μ P X)
    {A : Set F} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_finite : μ A ≠ ⊤) :
    ∀ᵐ ω ∂(P : Measure Omega), X ω A ∈ Set.range (fun n : ℕ ↦ (n : ENNReal)) := by
  rcases (ProbabilityTheory.isPoissonPointProcess_iff μ P X).1 hX with
    ⟨_, _, _, hX_poisson⟩
  exact ae_mem_natCastRange_of_hasLawPoissonCount (hX_poisson hA hA_bdd hA_finite)

/-- Helper for Theorem 24.24: if a measure is finite on all integer-radius balls around one
center, then it is boundedly finite. -/
noncomputable def boundedlyFiniteMeasure_of_centerBallFinite
    [PseudoMetricSpace F] [MeasurableSpace F]
    (x0 : F) (ν : Measure F)
    (hν : ∀ n : ℕ, ν (Metric.ball x0 ((n : ℝ) + 1)) < ∞) :
    BoundedlyFiniteMeasure F := by
  refine ⟨ν, ?_⟩
  intro A hA hA_bdd
  -- Proof comment: every bounded set lies in some large ball around the fixed center `x0`.
  obtain ⟨r, hrA⟩ := hA_bdd.subset_ball x0
  obtain ⟨n, hn⟩ := exists_nat_ge r
  have hsubset : A ⊆ Metric.ball x0 ((n : ℝ) + 1) := by
    intro y hy
    have hy_lt : dist y x0 < r := by
      exact hrA hy
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hy_lt (by linarith)
  exact lt_of_le_of_lt (MeasureTheory.measure_mono hsubset) (hν n)

/-- Coercing a subtype-built boundedly finite measure back to `Measure` preserves evaluation. -/
@[simp] theorem BoundedlyFiniteMeasure.coe_mk_apply
    [PseudoMetricSpace F] [MeasurableSpace F]
    (ν : Measure F)
    (hν : ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A → ν A < ∞)
    (A : Set F) :
    (((⟨ν, hν⟩ : BoundedlyFiniteMeasure F) : Measure F) A) = ν A :=
  rfl

/-- Helper for Theorem 24.24: the zero measure defines a boundedly finite measure. -/
theorem zero_measure_isBoundedlyFinite
    [PseudoMetricSpace F] [MeasurableSpace F] :
    ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A → (0 : Measure F) A < ∞ := by
  intro A hA hA_bdd
  simp

/-- Helper for Theorem 24.24: a measure that is finite on every bounded measurable set packages
as a boundedly finite measure. -/
noncomputable def boundedlyFiniteMeasureOfFiniteOnBounded
    [PseudoMetricSpace F] [MeasurableSpace F]
    (ν : Measure F)
    (hν :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A → ν A ≠ ⊤) :
    BoundedlyFiniteMeasure F :=
  ⟨ν, fun {_A} hA hA_bdd ↦ lt_top_iff_ne_top.mpr (hν hA hA_bdd)⟩

/-- Helper for Theorem 24.24: a `BoundedlyFiniteMeasure`-valued map is measurable once every
bounded measurable evaluation coordinate is measurable. -/
theorem measurable_boundedlyFiniteMeasure_of_measurable_apply
    [PseudoMetricSpace F] [MeasurableSpace F]
    {Z : Omega → BoundedlyFiniteMeasure F}
    (hZ :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        Measurable fun ω ↦ ((Z ω : BoundedlyFiniteMeasure F) : Measure F) A) :
    Measurable Z := by
  -- Proof comment: the random-measure sigma-algebra on `BoundedlyFiniteMeasure F` is generated by
  -- bounded measurable evaluations, so measurability follows by checking those generators.
  change @Measurable Omega (BoundedlyFiniteMeasure F) _ (randomMeasureMeasurableSpace F) Z
  refine Measurable.of_comap_le ?_
  rw [randomMeasureMeasurableSpace_def, MeasurableSpace.comap_iSup]
  refine iSup_le fun A ↦ ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hA ↦ ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hA_bdd ↦ ?_
  rw [MeasurableSpace.comap_comp]
  exact (hZ hA hA_bdd).comap_le

/-- Helper for Theorem 24.24: packaging a measure-valued map into boundedly finite representatives
on a measurable good event is measurable for the random-measure sigma-algebra. -/
theorem measurableBoundedlyFiniteRepresentativeOnGood
    [PseudoMetricSpace F] [BorelSpace F]
    {X : Omega → Measure F} (hX : Measurable X) {Good : Set Omega}
    (decGood : DecidablePred Good)
    (hGood : MeasurableSet Good)
    (x0 : F)
    (hfinite :
      ∀ ⦃ω : Omega⦄, ω ∈ Good →
        ∀ n : ℕ, X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞) :
    Measurable fun ω ↦
      @dite (BoundedlyFiniteMeasure F) (ω ∈ Good) (decGood ω)
        (fun hω ↦ boundedlyFiniteMeasure_of_centerBallFinite x0 (X ω) (hfinite hω))
        (fun _ ↦ ⟨0, zero_measure_isBoundedlyFinite (F := F)⟩) := by
  -- Proof comment: use the owner-level generated-sigma bridge, so it is enough to check each
  -- bounded measurable evaluation coordinate separately.
  refine measurable_boundedlyFiniteMeasure_of_measurable_apply ?_
  intro A hA hA_bdd
  have hXA : Measurable fun ω ↦ X ω A :=
    (Measure.measurable_coe hA).comp hX
  have hEval :
      (fun ω ↦
        (((@dite (BoundedlyFiniteMeasure F) (ω ∈ Good) (decGood ω)
            (fun hω ↦ boundedlyFiniteMeasure_of_centerBallFinite x0 (X ω) (hfinite hω))
            (fun _ ↦ ⟨0, zero_measure_isBoundedlyFinite (F := F)⟩) :
              BoundedlyFiniteMeasure F) : Measure F) A)) =
        Set.indicator Good (fun ω ↦ X ω A) := by
    funext ω
    by_cases hω : ω ∈ Good
    · -- Proof comment: on the good event, the packaged representative coerces back to `X ω`.
      rw [dif_pos hω]
      rw [Set.indicator_of_mem hω]
      rfl
    · -- Proof comment: off the good event, the representative is the zero measure.
      rw [dif_neg hω]
      rw [Set.indicator_of_notMem hω]
      rfl
  -- Proof comment: the coordinate is exactly the indicator of the measurable evaluation map.
  rw [hEval]
  exact hXA.indicator hGood

/-- Helper for Theorem 24.24: almost-sure finiteness on all integer-radius balls around one center
produces a measurable `BoundedlyFiniteMeasure`-valued representative. -/
theorem exists_boundedlyFiniteRepresentative_of_centerBallFinite
    [PseudoMetricSpace F] [BorelSpace F]
    {P : ProbabilityMeasure Omega} {X : Omega → Measure F}
    (hX : Measurable X) (x0 : F)
    (hXfinite :
      ∀ n : ℕ, ∀ᵐ ω ∂(P : Measure Omega), X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞) :
    ∃ Xbf : Omega → BoundedlyFiniteMeasure F,
      Measurable Xbf ∧
      (fun ω ↦ ((Xbf ω : BoundedlyFiniteMeasure F) : Measure F)) =ᵐ[(P : Measure Omega)] X := by
  classical
  let Good : Set Omega := ⋂ n : ℕ, {ω | X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞}
  have hGoodMeas : MeasurableSet Good := by
    -- Proof comment: `Good` is the intersection of the measurable centered-ball finiteness
    -- events.
    refine MeasurableSet.iInter fun n ↦ ?_
    exact measurableSet_lt
      (((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp hX)) measurable_const
  have hGoodAE : ∀ᵐ ω ∂(P : Measure Omega), ω ∈ Good := by
    -- Proof comment: `ae_all_iff` packages the almost-sure ball finiteness assumptions into one
    -- full-measure event.
    simpa [Good] using (ae_all_iff.2 hXfinite)
  let Xbf : Omega → BoundedlyFiniteMeasure F := fun ω ↦
    if hω : ω ∈ Good then
      boundedlyFiniteMeasure_of_centerBallFinite x0 (X ω) (by
        have hωfinite : ∀ n : ℕ, X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞ := by
          simpa [Good] using hω
        intro n
        exact hωfinite n)
    else ⟨0, zero_measure_isBoundedlyFinite (F := F)⟩
  refine ⟨Xbf, ?_, ?_⟩
  · -- Proof comment: the previous helper isolates the random-measure sigma-algebra packaging
    -- step on the good event.
    exact measurableBoundedlyFiniteRepresentativeOnGood hX (Classical.decPred Good) hGoodMeas x0
      (fun {ω} hω ↦ by
        have hωfinite : ∀ n : ℕ, X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞ := by
          simpa [Good] using hω
        exact hωfinite)
  · -- Proof comment: on the full-measure event `Good`, coercing the representative back to
    -- `Measure F` gives exactly the original measure.
    filter_upwards [hGoodAE] with ω hω
    have hωfinite : ∀ n : ℕ, X ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞ := by
      simpa [Good] using hω
    ext A hA
    unfold Xbf
    simp [hω, boundedlyFiniteMeasure_of_centerBallFinite]
    rfl

/-- Helper for Theorem 24.24: if a measure is finite on the support of a compactly supported
nonnegative test function, then the `ENNReal` Laplace kernel is the corresponding real
exponential. -/
private theorem ennrealExpNeg_lintegral_eq_exp_integral_of_support_lt_top
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (f : CompactlySupportedContinuousMap F NNReal) {ν : Measure F}
    (hν : ν (tsupport f) < ∞) :
    ennrealExpNeg (∫⁻ y, (f y : ℝ≥0∞) ∂ν) =
      Real.exp (-∫ y, (f y : ℝ) ∂ν) := by
  let K : Set F := tsupport f
  let νK : BoundedlyFiniteMeasure F :=
    ⟨ν.restrict K, fun A hA hA_bdd ↦ by
      rw [Measure.restrict_apply hA]
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hν⟩
  have hsupportENN :
      Function.support (fun y : F ↦ (f y : ℝ≥0∞)) ⊆ K := by
    intro y hy
    exact subset_tsupport f (by simpa using hy)
  have hindicator :
      Set.indicator K (fun y : F ↦ (f y : ℝ)) = fun y ↦ (f y : ℝ) := by
    funext y
    by_cases hy : y ∈ K
    · simp [hy]
    · have hfy : f y = 0 := by
        by_contra hfy
        exact hy (subset_tsupport f hfy)
      simp [Set.indicator, hy, hfy]
  have hlintegral_restrict :
      ∫⁻ y, (f y : ℝ≥0∞) ∂(νK : Measure F) =
        ∫⁻ y, (f y : ℝ≥0∞) ∂ν := by
    -- Proof comment: the `ENNReal` test function vanishes off `tsupport f`, so restriction to the
    -- support does not change its lower integral.
    simpa [K, νK] using
      (setLIntegral_eq_of_support_subset hsupportENN :
        ∫⁻ y in K, (f y : ℝ≥0∞) ∂ν = ∫⁻ y, (f y : ℝ≥0∞) ∂ν)
  have hintegral_restrict :
      ∫ y, (f y : ℝ) ∂(νK : Measure F) = ∫ y, (f y : ℝ) ∂ν := by
    -- Proof comment: the real-valued test function also vanishes off `tsupport f`, so the
    -- restricted and unrestricted integrals coincide.
    calc
      ∫ y, (f y : ℝ) ∂(νK : Measure F) = ∫ y in K, (f y : ℝ) ∂ν := by
          rfl
      _ = ∫ y, Set.indicator K (fun y : F ↦ (f y : ℝ)) y ∂ν := by
            symm
            rw [integral_indicator (isClosed_tsupport f).measurableSet]
      _ = ∫ y, (f y : ℝ) ∂ν := by
            simp [hindicator]
  have hnonneg :
      0 ≤ BoundedlyFiniteMeasure.nonnegativeVagueIntegral f νK := by
    rw [BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply]
    exact integral_nonneg fun y ↦ NNReal.coe_nonneg (f y)
  have hnonneg_ae :
      0 ≤ᵐ[(νK : Measure F)] f.toReal := by
    exact Filter.Eventually.of_forall fun y ↦ by
      simpa using NNReal.coe_nonneg (f y)
  have hofReal :
      ENNReal.ofReal (BoundedlyFiniteMeasure.nonnegativeVagueIntegral f νK) =
        ∫⁻ y, (f y : ℝ≥0∞) ∂(νK : Measure F) := by
    -- Proof comment: on the boundedly finite restriction, the real and `ENNReal` integrals agree
    -- by the Chapter 24 vague-integral API.
    simpa [BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_vagueTest νK f.toReal) hnonneg_ae)
  calc
    ennrealExpNeg (∫⁻ y, (f y : ℝ≥0∞) ∂ν)
        = ennrealExpNeg (∫⁻ y, (f y : ℝ≥0∞) ∂(νK : Measure F)) := by
            rw [hlintegral_restrict]
    _ = ennrealExpNeg (ENNReal.ofReal (BoundedlyFiniteMeasure.nonnegativeVagueIntegral f νK)) := by
          rw [hofReal.symm]
    _ = Real.exp (-BoundedlyFiniteMeasure.nonnegativeVagueIntegral f νK) := by
          rw [ennrealExpNeg, if_neg (by simp), ENNReal.toReal_ofReal hnonneg]
    _ = Real.exp (-∫ y, (f y : ℝ) ∂ν) := by
          rw [BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply, hintegral_restrict]

/-- Helper for Theorem 24.24: pushing the law of a boundedly finite representative forward along
the coercion `BoundedlyFiniteMeasure F → Measure F` recovers the original measure-valued law. -/
theorem boundedlyFiniteLaw_pushforward_coe_eq_measureLaw
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    {P : ProbabilityMeasure Omega} {X : Omega → Measure F}
    (hX : Measurable X) {Xbf : Omega → BoundedlyFiniteMeasure F}
    (hXbf : Measurable Xbf)
    (hcoe :
      (fun ω ↦ ((Xbf ω : BoundedlyFiniteMeasure F) : Measure F)) =ᵐ[(P : Measure Omega)] X) :
    Measure.map (fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F))
        (P.map hXbf.aemeasurable : Measure (BoundedlyFiniteMeasure F)) =
      (P.map hX.aemeasurable : Measure (Measure F)) := by
  have hmeasCoe : Measurable fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F) := by
    refine Measure.measurable_of_measurable_coe _ ?_
    intro A hA
    simpa using measurable_apply_random (E := F) A hA
  -- Proof comment: collapse the two successive pushforwards and then use the almost-sure coercion
  -- equality of the representative.
  rw [ProbabilityMeasure.toMeasure_map]
  rw [AEMeasurable.map_map_of_aemeasurable hmeasCoe.aemeasurable hXbf.aemeasurable]
  exact MeasureTheory.Measure.map_congr hcoe

/-- Helper for Theorem 24.24: the scalar map `r ↦ 1 - exp(-r)` as a continuous self-map of `ℝ`.
-/
private noncomputable def oneSubExpNegContinuousMap : C(ℝ, ℝ) where
  toFun r := 1 - Real.exp (-r)
  continuous_toFun := continuous_const.sub (Real.continuous_exp.comp continuous_neg)

/-- Helper for Theorem 24.24: package the Poisson exponent `1 - exp(-f)` as a compactly
supported nonnegative test function. -/
private noncomputable def oneSubExpNegTestFunction
    [TopologicalSpace F]
    (f : CompactlySupportedContinuousMap F NNReal) :
    CompactlySupportedContinuousMap F NNReal :=
  (f.toReal.compLeft oneSubExpNegContinuousMap).nnrealPart

/-- Helper for Theorem 24.24: the packaged exponent test function evaluates pointwise to
`Real.toNNReal (1 - exp(-f))`. -/
@[simp] private theorem oneSubExpNegTestFunction_apply
    [TopologicalSpace F]
    (f : CompactlySupportedContinuousMap F NNReal) (y : F) :
    oneSubExpNegTestFunction f y = Real.toNNReal (1 - Real.exp (-(f y : ℝ))) := by
  -- Proof comment: `compLeft` applies the continuous scalar map to `f.toReal`, and `nnrealPart`
  -- then keeps the nonnegative value unchanged.
  change Real.toNNReal ((f.toReal.compLeft oneSubExpNegContinuousMap) y) =
    Real.toNNReal (1 - Real.exp (-(f y : ℝ)))
  rw [CompactlySupportedContinuousMap.coe_compLeft
    (g := oneSubExpNegContinuousMap) (by simp [oneSubExpNegContinuousMap]) f.toReal]
  simp [oneSubExpNegContinuousMap]

/-- Helper for Theorem 24.24: coercing the packaged exponent test function to `ℝ` recovers the
real-valued exponent `1 - exp(-f)`. -/
@[simp] private theorem oneSubExpNegTestFunction_coe_apply
    [TopologicalSpace F]
    (f : CompactlySupportedContinuousMap F NNReal) (y : F) :
    ((oneSubExpNegTestFunction f y : NNReal) : ℝ) =
      1 - Real.exp (-(f y : ℝ)) := by
  have hExpLeOne : Real.exp (-(f y : ℝ)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hfy : 0 ≤ (f y : ℝ) := NNReal.coe_nonneg _
    linarith
  have hNonneg : 0 ≤ 1 - Real.exp (-(f y : ℝ)) := by
    linarith
  -- Proof comment: the `Real.toNNReal` introduced by `nnrealPart` is transparent on the
  -- nonnegative exponent value.
  simp [oneSubExpNegTestFunction_apply, Real.coe_toNNReal, hNonneg]

/-- Helper for Theorem 24.24: integrating a mark-only nonnegative measurable test function against
the marked process equals integrating it against the projected random measure. -/
private theorem kernelColoredRandomMeasure_lintegral_snd
    (Xi : Omega → Measure (E × F)) (ω : Omega) (g : NonnegativeMeasurableFunction F) :
    ∫⁻ z, g z.2 ∂Xi ω = ∫⁻ y, g y ∂kernelColoredRandomMeasure Xi ω := by
  -- Proof comment: `kernelColoredRandomMeasure Xi ω` is the `snd` marginal of `Xi ω`, so this is
  -- exactly `lintegral_map` for the projection `Prod.snd`.
  rw [kernelColoredRandomMeasure, Measure.snd, MeasureTheory.lintegral_map g.2 measurable_snd]

/-- Helper for Theorem 24.24: the intensity-side `ENNReal` Laplace exponent for `1 - exp(-f)`
rewrites to the real Laplace exponent against `μκ`. -/
private theorem kernelImageMeasure_oneSubExpNeg_laplace
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤)
    (f : CompactlySupportedContinuousMap F NNReal) :
    ennrealExpNeg
        (∫⁻ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞)
          ∂kernelImageMeasure mu kappa) =
      Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := by
  have hSupportFinite :
      kernelImageMeasure mu kappa (tsupport (oneSubExpNegTestFunction f)) < ∞ := by
    -- Proof comment: the bounded-set finiteness hypothesis applies to the compact support of the
    -- packaged exponent test function.
    refine lt_top_iff_ne_top.mpr ?_
    exact hMuKappaFinite
      (isClosed_tsupport (oneSubExpNegTestFunction f)).measurableSet
      (oneSubExpNegTestFunction f).hasCompactSupport.isCompact.isBounded
  have hIntegralExponent :
      ∫ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ) ∂kernelImageMeasure mu kappa =
        -∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa := by
    -- Proof comment: the packaged exponent is exactly `-(exp(-f)-1)` pointwise.
    calc
      ∫ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ) ∂kernelImageMeasure mu kappa
          = ∫ y, (1 - Real.exp (-(f y : ℝ))) ∂kernelImageMeasure mu kappa := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun y ↦ oneSubExpNegTestFunction_coe_apply f y
      _ = ∫ y, (-(Real.exp (-(f y : ℝ)) - 1)) ∂kernelImageMeasure mu kappa := by
            congr 1
            ext y
            ring
      _ = -∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa := by
            rw [integral_neg]
  -- Proof comment: the `ENNReal` exponent becomes the desired real exponential once the support
  -- finiteness and single-measure normalization are in place.
  calc
    ennrealExpNeg
        (∫⁻ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞)
          ∂kernelImageMeasure mu kappa)
        = Real.exp
            (-∫ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ)
              ∂kernelImageMeasure mu kappa) := by
              exact
                ennrealExpNeg_lintegral_eq_exp_integral_of_support_lt_top
                  (oneSubExpNegTestFunction f) hSupportFinite
    _ = Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := by
          rw [hIntegralExponent]
          ring_nf

-- Semantic recall: LeanSearch surfaced generic kernel-map infrastructure but no existing owner
-- for the kernel-colored PPP statement, so this file keeps `Xkappa` as the source-facing object
-- and isolates the marked-process presentation behind the helper statements below.
-- Proof sketch: apply `random_measure_distribution_ext_iff_laplace_transform_eq` to the law of
-- `X^κ` and to any Poisson point process realization with intensity `μκ`. The hypothesis
-- `HasKernelColoredLaplaceTransform` gives the Laplace transform of `X^κ`, and Theorem 24.14
-- gives the same Laplace transform for the realizing `PPP_{μκ}`.
/-- If a measure-valued map is already known to be a random measure and satisfies the textbook
kernel-coloring Laplace transform, then its law agrees with the Poisson point process law
`PPP_{μκ}`. -/
theorem kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw_of_randomMeasure
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xkappa : Omega → Measure F) (hXkappa : IsRandomMeasure P Xkappa)
    (hXkappaBF : IsBoundedlyFiniteRandomMeasure P Xkappa)
    (hLaplace :
      ∀ f : CompactlySupportedContinuousMap F NNReal,
        ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂Xkappa ω) ∂(P : Measure Omega) =
          Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa))
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤)
    (P' : ProbabilityMeasure Omega') (Y : Omega' → Measure F)
    (hY : IsPoissonPointProcess (kernelImageMeasure mu kappa) P' Y) :
    P.map hXkappa.1.aemeasurable =
      poissonPointProcessLaw (kernelImageMeasure mu kappa) P' Y hY := by
  -- Route correction: the direct `Measure F` law comparison was the wrong surface.
  rcases isEmpty_or_nonempty F with hF | hF
  · letI : IsEmpty F := hF
    have hXzero :
        (fun ω ↦ Xkappa ω) =ᵐ[(P : Measure Omega)] fun _ ↦ (0 : Measure F) :=
      Filter.Eventually.of_forall fun ω ↦ Measure.eq_zero_of_isEmpty (Xkappa ω)
    have hYzero :
        (fun ω ↦ Y ω) =ᵐ[(P' : Measure Omega')] fun _ ↦ (0 : Measure F) :=
      Filter.Eventually.of_forall fun ω ↦ Measure.eq_zero_of_isEmpty (Y ω)
    -- Proof comment: on the empty mark space every sample measure is the zero measure, so both
    -- pushforward laws collapse to the same Dirac mass at `0`.
    rw [poissonPointProcessLaw_def]
    ext A hA
    change (P.map hXkappa.1.aemeasurable : Measure (Measure F)) A =
      (P'.map hY.1.1.aemeasurable : Measure (Measure F)) A
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_congr hXzero, Measure.map_congr hYzero]
    simp [Measure.map_const]
  · letI : Nonempty F := hF
    let x0 : F := Classical.choice hF
    have hXkappaBallFinite :
        ∀ n : ℕ, ∀ᵐ ω ∂(P : Measure Omega),
          Xkappa ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞ := by
      intro n
      -- Proof comment: the boundedly finite hypothesis applies to every centered ball.
      exact hXkappaBF.2 _ Metric.isOpen_ball.measurableSet Metric.isBounded_ball
    rcases
      exists_boundedlyFiniteRepresentative_of_centerBallFinite
        hXkappaBF.1 x0 hXkappaBallFinite with
      ⟨Xbf, hXbfMeas, hXbfCoe⟩
    have hYBallFinite :
        ∀ n : ℕ, ∀ᵐ ω ∂(P' : Measure Omega'),
          Y ω (Metric.ball x0 ((n : ℝ) + 1)) < ∞ := by
      intro n
      have hNatCast :
          ∀ᵐ ω ∂(P' : Measure Omega'),
            Y ω (Metric.ball x0 ((n : ℝ) + 1)) ∈ Set.range (fun m : ℕ ↦ (m : ENNReal)) :=
        ae_eval_mem_natCastRange_of_isPoissonPointProcess
          hY Metric.isOpen_ball.measurableSet Metric.isBounded_ball
          (hMuKappaFinite Metric.isOpen_ball.measurableSet Metric.isBounded_ball)
      -- Proof comment: count-valued evaluations are automatically finite.
      filter_upwards [hNatCast] with ω hω
      rcases hω with ⟨m, hm⟩
      rw [← hm]
      simp
    rcases
      exists_boundedlyFiniteRepresentative_of_centerBallFinite
        hY.1.1 x0 hYBallFinite with
      ⟨Ybf, hYbfMeas, hYbfCoe⟩
    let PXbf : ProbabilityMeasure (BoundedlyFiniteMeasure F) :=
      P.map hXbfMeas.aemeasurable
    let PYbf : ProbabilityMeasure (BoundedlyFiniteMeasure F) :=
      P'.map hYbfMeas.aemeasurable
    have hLaplaceEq :
        ∀ f : CompactlySupportedContinuousMap F NNReal,
          random_measure_laplace_transform PXbf f =
            random_measure_laplace_transform PYbf f := by
      intro f
      have hKernelMeas :
          Measurable fun ν : BoundedlyFiniteMeasure F ↦
            Real.exp (-BoundedlyFiniteMeasure.nonnegativeVagueIntegral f ν) := by
        -- Proof comment: Theorem 24.7 uses the boundedly finite Laplace kernel, whose
        -- measurability comes from the vague-integral measurable coordinate.
        exact Real.measurable_exp.comp (measurable_nonnegativeVagueIntegral f).neg
      have hXbfEval :
          random_measure_laplace_transform PXbf f =
            ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂Xkappa ω) ∂(P : Measure Omega) := by
        -- Proof comment: push the boundedly finite law back to `P` and then use the almost-sure
        -- coercion equality of the representative.
        rw [random_measure_laplace_transform_def, ProbabilityMeasure.toMeasure_map]
        rw [integral_map hXbfMeas.aemeasurable hKernelMeas.aestronglyMeasurable]
        refine integral_congr_ae ?_
        filter_upwards [hXbfCoe] with ω hω
        simp [BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply, hω]
      have hYbfEval :
          random_measure_laplace_transform PYbf f =
            ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂Y ω) ∂(P' : Measure Omega') := by
        -- Proof comment: the same representative pushforward argument identifies the boundedly
        -- finite Poisson law with the original process on the sample side.
        rw [random_measure_laplace_transform_def, ProbabilityMeasure.toMeasure_map]
        rw [integral_map hYbfMeas.aemeasurable hKernelMeas.aestronglyMeasurable]
        refine integral_congr_ae ?_
        filter_upwards [hYbfCoe] with ω hω
        simp [BoundedlyFiniteMeasure.nonnegativeVagueIntegral_apply, hω]
      let g : NonnegativeMeasurableFunction F :=
        ⟨fun y ↦ (f y : ℝ≥0∞),
          measurable_coe_nnreal_ennreal.comp f.continuous.measurable⟩
      have hYSupportFinite :
          ∀ᵐ ω ∂(P' : Measure Omega'), Y ω (tsupport f) < ∞ := by
        filter_upwards [hY.1.2] with ω hω
        exact f.hasCompactSupport.isCompact.measure_lt_top (μ := Y ω)
      have hYLeft :
          (fun ω ↦ ennrealExpNeg (∫⁻ y, g y ∂Y ω)) =ᵐ[(P' : Measure Omega')]
            fun ω ↦ Real.exp (-∫ y, (f y : ℝ) ∂Y ω) := by
        -- Proof comment: local finiteness of the Poisson sample on the compact support of `f`
        -- turns the `ENNReal` Laplace kernel into the desired real exponential.
        filter_upwards [hYSupportFinite] with ω hω
        simpa [g] using
          (ennrealExpNeg_lintegral_eq_exp_integral_of_support_lt_top f hω)
      have hYRaw :
          ∫ ω, ennrealExpNeg (∫⁻ y, g y ∂Y ω) ∂(P' : Measure Omega') =
            ennrealExpNeg
              (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))
                ∂kernelImageMeasure mu kappa) := by
        -- Proof comment: this is Theorem 24.14 for the Poisson point process `Y`.
        simpa [kernelImageMeasure] using
          poisson_point_process_laplaceTransform P' (kernelImageMeasure mu kappa) Y hY g
      have hYRight :
          ennrealExpNeg
              (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))
                ∂kernelImageMeasure mu kappa) =
            Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := by
        -- Proof comment: on the intensity side, `1 - exp(-f)` is the packaged compactly
        -- supported exponent test function on `F`.
        have hIntegrand :
            (fun y : F ↦ (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))) =
              fun y : F ↦ ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞) := by
          funext y
          have hExp :
              ennrealExpNeg (g y) = Real.exp (-(f y : ℝ)) := by
            simp [g, ennrealExpNeg]
          have hExpNonneg : 0 ≤ Real.exp (-(f y : ℝ)) := Real.exp_nonneg _
          have hExpLeOne : Real.exp (-(f y : ℝ)) ≤ 1 := by
            refine Real.exp_le_one_iff.mpr ?_
            have hfy : 0 ≤ (f y : ℝ) := NNReal.coe_nonneg _
            linarith
          have hNonneg : 0 ≤ 1 - Real.exp (-(f y : ℝ)) := by
            linarith
          calc
            (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))
                = ENNReal.ofReal 1 - ENNReal.ofReal (Real.exp (-(f y : ℝ))) := by
                    rw [hExp]
                    simp
            _ = ENNReal.ofReal (1 - Real.exp (-(f y : ℝ))) := by
                  simpa using (ENNReal.ofReal_sub 1 hExpNonneg).symm
            _ = ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞) := by
                  rw [oneSubExpNegTestFunction_apply]
                  simpa [Real.toNNReal_of_nonneg hNonneg] using
                    (ENNReal.ofReal_eq_coe_nnreal hNonneg)
        rw [hIntegrand]
        exact kernelImageMeasure_oneSubExpNeg_laplace mu kappa hMuKappaFinite f
      calc
        random_measure_laplace_transform PXbf f
            = ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂Xkappa ω) ∂(P : Measure Omega) := hXbfEval
        _ = Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := hLaplace f
        _ = ∫ ω, ennrealExpNeg (∫⁻ y, g y ∂Y ω) ∂(P' : Measure Omega') := by
              rw [hYRaw, hYRight]
        _ = ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂Y ω) ∂(P' : Measure Omega') := by
              exact integral_congr_ae hYLeft
        _ = random_measure_laplace_transform PYbf f := hYbfEval.symm
    have hLawBF :
        PXbf = PYbf :=
      (random_measure_distribution_ext_iff_laplace_transform_eq PXbf PYbf).2 hLaplaceEq
    have hXMeasureLaw :
        Measure.map (fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F))
            (PXbf : Measure (BoundedlyFiniteMeasure F)) =
          (P.map hXkappa.1.aemeasurable : Measure (Measure F)) :=
      boundedlyFiniteLaw_pushforward_coe_eq_measureLaw
        hXkappa.1 hXbfMeas hXbfCoe
    have hYMeasureLaw :
        Measure.map (fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F))
            (PYbf : Measure (BoundedlyFiniteMeasure F)) =
          (P'.map hY.1.1.aemeasurable : Measure (Measure F)) :=
      boundedlyFiniteLaw_pushforward_coe_eq_measureLaw
        hY.1.1 hYbfMeas hYbfCoe
    have hMeasureBF :
        (PXbf : Measure (BoundedlyFiniteMeasure F)) =
          (PYbf : Measure (BoundedlyFiniteMeasure F)) := by
      simpa using congrArg
        (fun q : ProbabilityMeasure (BoundedlyFiniteMeasure F) =>
          (q : Measure (BoundedlyFiniteMeasure F)))
        hLawBF
    -- Proof comment: once the boundedly finite representative laws agree, coercing them back to
    -- `Measure F` recovers the original measure-valued laws.
    rw [poissonPointProcessLaw_def]
    ext A hA
    change (P.map hXkappa.1.aemeasurable : Measure (Measure F)) A =
      (P'.map hY.1.1.aemeasurable : Measure (Measure F)) A
    calc
      (P.map hXkappa.1.aemeasurable : Measure (Measure F)) A
          = Measure.map (fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F))
              (PXbf : Measure (BoundedlyFiniteMeasure F)) A := by
                rw [hXMeasureLaw]
      _ = Measure.map (fun ν : BoundedlyFiniteMeasure F ↦ (ν : Measure F))
            (PYbf : Measure (BoundedlyFiniteMeasure F)) A := by
              rw [hMeasureBF]
      _ = (P'.map hY.1.1.aemeasurable : Measure (Measure F)) A := by
            rw [hYMeasureLaw]

/-- Helper for Theorem 24.24: bounded-set finiteness of `μκ` upgrades the mark projection of the
marked Poisson point process to a random measure on `F`. -/
theorem kernelColoredRandomMeasure_isBoundedlyFiniteRandomMeasure
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) [SigmaFinite mu]
    (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤) :
    IsBoundedlyFiniteRandomMeasure P (kernelColoredRandomMeasure Xi) := by
  refine ⟨measurable_kernelColoredRandomMeasure P Xi hXi.1, ?_⟩
  intro A hA hA_bdd
  -- Proof comment: the bounded-set Poisson Laplace identity already proves finiteness of every
  -- bounded measurable evaluation almost surely.
  exact kernelColoredRandomMeasure_apply_lt_top_ae
    P mu kappa Xi hXi hA hA_bdd (hMuKappaFinite hA hA_bdd)

/-- Helper for Theorem 24.24: bounded-set finiteness of `μκ` upgrades the mark projection of the
marked Poisson point process to a random measure on `F`. -/
theorem kernelColoredRandomMeasure_isRandomMeasure
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) [SigmaFinite mu]
    (kappa : Kernel E F) [IsMarkovKernel kappa]
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤) :
    IsRandomMeasure P (kernelColoredRandomMeasure Xi) := by
  let K : CompactExhaustion F := CompactExhaustion.choice F
  refine ⟨measurable_kernelColoredRandomMeasure P Xi hXi.1, ?_⟩
  -- Proof comment: finite mass on every compact exhaustion piece gives almost-sure local
  -- finiteness of the projected measure.
  exact ae_isLocallyFiniteMeasure_of_compactExhaustionFinite K fun n ↦
    kernelColoredRandomMeasure_apply_lt_top_ae P mu kappa Xi hXi
      (K.isCompact n).measurableSet (K.isCompact n).isBounded
      (hMuKappaFinite (K.isCompact n).measurableSet (K.isCompact n).isBounded)

/-- Helper for Theorem 24.24: the kernel-colored random measure `X^κ` satisfies the textbook
Laplace transform identity. -/
theorem kernelColoredRandomMeasure_hasKernelColoredLaplaceTransform
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (X : Omega → Measure E) (hX : IsPoissonPointProcess mu P X)
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    (hXiFst : (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Omega)] X)
    (hXkappa : IsRandomMeasure P (kernelColoredRandomMeasure Xi))
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤) :
    ∀ f : CompactlySupportedContinuousMap F NNReal,
      ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂kernelColoredRandomMeasure Xi ω) ∂(P : Measure Omega) =
        Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := by
  letI : IsLocallyFiniteMeasure mu := hX.2.2.1
  letI : SigmaFinite mu := inferInstance
  intro f
  let gF : NonnegativeMeasurableFunction F :=
    ⟨fun y ↦ (f y : ℝ≥0∞), measurable_coe_nnreal_ennreal.comp f.continuous.measurable⟩
  let g : NonnegativeMeasurableFunction (E × F) :=
    ⟨fun z ↦ gF z.2, gF.2.comp measurable_snd⟩
  have hSupportFinite :
      ∀ᵐ ω ∂(P : Measure Omega),
        kernelColoredRandomMeasure Xi ω (tsupport f) < ∞ := by
    -- Proof comment: local finiteness of the projected random measure gives finite mass on the
    -- compact support of `f` almost surely.
    filter_upwards [hXkappa.2] with ω hω
    exact f.hasCompactSupport.isCompact.measure_lt_top (μ := kernelColoredRandomMeasure Xi ω)
  have hLeft :
      (fun ω ↦ ennrealExpNeg (∫⁻ z, g z ∂Xi ω)) =ᵐ[(P : Measure Omega)]
        fun ω ↦ Real.exp (-∫ y, (f y : ℝ) ∂kernelColoredRandomMeasure Xi ω) := by
    -- Proof comment: first collapse the marked-process integral to the `snd` marginal, then use
    -- support finiteness on the projected measure.
    filter_upwards [hSupportFinite] with ω hω
    have hProj :
        ∫⁻ z, g z ∂Xi ω =
          ∫⁻ y, gF y ∂kernelColoredRandomMeasure Xi ω := by
      simpa [g] using kernelColoredRandomMeasure_lintegral_snd (Xi := Xi) (ω := ω) gF
    calc
      ennrealExpNeg (∫⁻ z, g z ∂Xi ω)
          = ennrealExpNeg (∫⁻ y, gF y ∂kernelColoredRandomMeasure Xi ω) := by
              rw [hProj]
      _ = Real.exp (-∫ y, (f y : ℝ) ∂kernelColoredRandomMeasure Xi ω) := by
            simpa [gF] using
              (ennrealExpNeg_lintegral_eq_exp_integral_of_support_lt_top f hω)
  have hRaw :
      ∫ ω, ennrealExpNeg (∫⁻ z, g z ∂Xi ω) ∂(P : Measure Omega) =
        ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g z)) ∂(mu ⊗ₘ kappa)) := by
    -- Proof comment: this is Theorem 24.14 applied to the marked process with the mark-only test
    -- function `(x, y) ↦ f y`.
    simpa using poisson_point_process_laplaceTransform P (mu ⊗ₘ kappa) Xi hXi g
  have hRight :
      ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g z)) ∂(mu ⊗ₘ kappa)) =
        Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := by
    -- Proof comment: the intensity-side mark-only exponent integrates exactly against the
    -- projected intensity `μκ`.
    have hIntegrand :
        (fun z : E × F ↦ (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g z))) =
          fun z : E × F ↦ ((oneSubExpNegTestFunction f z.2 : NNReal) : ℝ≥0∞) := by
      funext z
      have hExp :
          ennrealExpNeg (g z) = Real.exp (-(f z.2 : ℝ)) := by
        simp [g, gF, ennrealExpNeg]
      have hExpNonneg : 0 ≤ Real.exp (-(f z.2 : ℝ)) := Real.exp_nonneg _
      have hExpLeOne : Real.exp (-(f z.2 : ℝ)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        have hfy : 0 ≤ (f z.2 : ℝ) := NNReal.coe_nonneg _
        linarith
      have hNonneg : 0 ≤ 1 - Real.exp (-(f z.2 : ℝ)) := by
        linarith
      calc
        (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g z))
            = ENNReal.ofReal 1 - ENNReal.ofReal (Real.exp (-(f z.2 : ℝ))) := by
                rw [hExp]
                simp
        _ = ENNReal.ofReal (1 - Real.exp (-(f z.2 : ℝ))) := by
              simpa using (ENNReal.ofReal_sub 1 hExpNonneg).symm
        _ = ((oneSubExpNegTestFunction f z.2 : NNReal) : ℝ≥0∞) := by
              rw [oneSubExpNegTestFunction_apply]
              simpa [Real.toNNReal_of_nonneg hNonneg] using
                (ENNReal.ofReal_eq_coe_nnreal hNonneg)
    rw [hIntegrand]
    have hMap :
        ∫⁻ y, ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞)
          ∂kernelImageMeasure mu kappa =
            ∫⁻ z, ((oneSubExpNegTestFunction f z.2 : NNReal) : ℝ≥0∞) ∂(mu ⊗ₘ kappa) := by
      rw [kernelImageMeasure, ← Measure.snd_compProd (μ := mu) (κ := kappa)]
      rw [Measure.snd]
      simpa using
        (MeasureTheory.lintegral_map
          (μ := mu ⊗ₘ kappa)
          (f := fun y : F ↦ ((oneSubExpNegTestFunction f y : NNReal) : ℝ≥0∞))
          (g := Prod.snd)
          (measurable_coe_nnreal_ennreal.comp (oneSubExpNegTestFunction f).continuous.measurable)
          measurable_snd)
    rw [← hMap]
    exact kernelImageMeasure_oneSubExpNeg_laplace mu kappa hMuKappaFinite f
  calc
    ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂kernelColoredRandomMeasure Xi ω) ∂(P : Measure Omega)
        = ∫ ω, ennrealExpNeg (∫⁻ z, g z ∂Xi ω) ∂(P : Measure Omega) := by
            symm
            exact integral_congr_ae hLeft
    _ = ennrealExpNeg
          (∫⁻ z, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g z)) ∂(mu ⊗ₘ kappa)) := hRaw
    _ = Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) := hRight

/-- Witness predicate for the marked Poisson point process whose mark projection is the
kernel-colored random measure from Theorem 24.24. -/
def IsKernelColoredRandomMeasureWitness
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E)
    (Xi : Omega → Measure (E × F)) (Xkappa : Omega → Measure F) : Prop :=
  IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi ∧
    (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Omega)] X ∧
    Xkappa = kernelColoredRandomMeasure Xi

/-- Unfolding the witness predicate for Theorem 24.24 recovers the marked-process conditions from
the source argument. -/
theorem isKernelColoredRandomMeasureWitness_iff
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E)
    (Xi : Omega → Measure (E × F)) (Xkappa : Omega → Measure F) :
    IsKernelColoredRandomMeasureWitness P mu kappa X Xi Xkappa ↔
      IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi ∧
        (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Omega)] X ∧
        Xkappa = kernelColoredRandomMeasure Xi := by
  rfl

/-- Source-facing predicate expressing that `Xkappa` is the kernel-colored random measure `X^κ`
attached to `X` and `κ`; the auxiliary marked Poisson point process witness is kept internal to
this predicate rather than in the main theorem statement. -/
def IsKernelColoredRandomMeasure
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E)
    (Xkappa : Omega → Measure F) : Prop :=
  ∃ Xi : Omega → Measure (E × F), IsKernelColoredRandomMeasureWitness P mu kappa X Xi Xkappa

/-- Unfolding `IsKernelColoredRandomMeasure` recovers the hidden marked-process witness from the
source construction of `X^κ`. -/
theorem isKernelColoredRandomMeasure_iff
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E)
    (Xkappa : Omega → Measure F) :
    IsKernelColoredRandomMeasure P mu kappa X Xkappa ↔
      ∃ Xi : Omega → Measure (E × F),
        IsKernelColoredRandomMeasureWitness P mu kappa X Xi Xkappa := by
  rfl

/-- Canonical owner for the kernel-colored random measure `X^κ`, chosen from the source-facing
predicate `IsKernelColoredRandomMeasure` when such a realization exists. -/
noncomputable def kernelColoredRandomMeasureOf
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E) :
    Omega → Measure F := by
  classical
  exact
    if hXkappa : ∃ Xkappa : Omega → Measure F, IsKernelColoredRandomMeasure P mu kappa X Xkappa then
      Classical.choose hXkappa
    else
      fun _ ↦ 0

/-- The chosen owner `kernelColoredRandomMeasureOf P mu kappa X` satisfies the source-facing
predicate as soon as some realization of `X^κ` exists. -/
theorem kernelColoredRandomMeasureOf_spec
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) (X : Omega → Measure E)
    (hExists : ∃ Xkappa : Omega → Measure F, IsKernelColoredRandomMeasure P mu kappa X Xkappa) :
    IsKernelColoredRandomMeasure P mu kappa X (kernelColoredRandomMeasureOf P mu kappa X) := by
  classical
  -- Proof comment: once an actual realization exists, the `if` branch in
  -- `kernelColoredRandomMeasureOf` chooses one such realization.
  unfold kernelColoredRandomMeasureOf
  simpa [hExists] using Classical.choose_spec hExists

-- Proof sketch: the source proof uses that `(μκ)(A) < ∞` for every bounded measurable set
-- `A ⊆ F`, so the theorem keeps that bounded-set finiteness as an explicit side condition on the
-- intensity `μκ`. This helper records the older witness-based formulation used internally to
-- obtain the chosen owner `kernelColoredRandomMeasureOf P mu kappa X`.
/-- Existence helper for Theorem 24.24: under the source hypotheses, there is a realization of the
kernel-colored random measure `X^κ` whose law is `PPP_{μκ}`. -/
theorem exists_kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (X : Omega → Measure E) (hX : IsPoissonPointProcess mu P X)
    (Xi : Omega → Measure (E × F))
    (hXi : IsPoissonPointProcess (mu ⊗ₘ kappa) P Xi)
    (hXiFst : (fun ω ↦ (Xi ω).fst) =ᵐ[(P : Measure Omega)] X)
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤) :
    ∃ hXkappaRandom : IsRandomMeasure P (kernelColoredRandomMeasure Xi),
      ∀ (P' : ProbabilityMeasure Omega') (Y : Omega' → Measure F)
        (hY : IsPoissonPointProcess (kernelImageMeasure mu kappa) P' Y),
          P.map hXkappaRandom.1.aemeasurable =
            poissonPointProcessLaw (kernelImageMeasure mu kappa) P' Y hY := by
  -- Route correction: this helper now takes the marked witness `Xi` explicitly, because creating
  -- `Xi` from `hX` alone is the later marking theorem and is not available in the dependency
  -- closure of Theorem 24.24.
  -- Proof comment: choose `Xkappa` to be the mark projection of `Xi`, then combine the
  -- random-measure, Laplace-transform, and law-comparison helper theorems.
  letI : IsLocallyFiniteMeasure mu := hX.2.2.1
  letI : SigmaFinite mu := inferInstance
  let hXkappaRandom : IsRandomMeasure P (kernelColoredRandomMeasure Xi) :=
    kernelColoredRandomMeasure_isRandomMeasure P mu kappa Xi hXi hMuKappaFinite
  refine ⟨hXkappaRandom, ?_⟩
  intro P' Y hY
  have hLaplace :
      ∀ f : CompactlySupportedContinuousMap F NNReal,
        ∫ ω, Real.exp (-∫ y, (f y : ℝ) ∂kernelColoredRandomMeasure Xi ω)
          ∂(P : Measure Omega) =
          Real.exp (∫ y, (Real.exp (-(f y : ℝ)) - 1) ∂kernelImageMeasure mu kappa) :=
    kernelColoredRandomMeasure_hasKernelColoredLaplaceTransform
      P mu kappa X hX Xi hXi hXiFst hXkappaRandom hMuKappaFinite
  let hXkappaBF : IsBoundedlyFiniteRandomMeasure P (kernelColoredRandomMeasure Xi) :=
    kernelColoredRandomMeasure_isBoundedlyFiniteRandomMeasure P mu kappa Xi hXi hMuKappaFinite
  exact
    kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw_of_randomMeasure
      P mu kappa (kernelColoredRandomMeasure Xi) hXkappaRandom hXkappaBF
      hLaplace hMuKappaFinite P' Y hY

-- Proof sketch: the source theorem is stated about the already constructed colored random measure
-- `X^κ`, so the public statement keeps an explicit parameter `Xkappa` together with the
-- source-facing witness predicate `IsKernelColoredRandomMeasure P mu kappa X Xkappa`. The law
-- `PPP_{μκ}` remains expressed by equality with the law of any realizing Poisson point process of
-- intensity `μκ`, as elsewhere in the chapter API.
/-- Theorem 24.24: if `Xkappa` is the source-facing kernel-colored random measure `X^κ`
attached to `X` and `κ`, then `Xkappa` is a random measure with distribution `PPP_{μκ}`.
The source proof uses the additional bounded-set finiteness condition `(μκ)(A) < ∞` for bounded
measurable `A ⊆ F`. -/
theorem kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw
    [PseudoMetricSpace E] [BorelSpace E] [LocallyCompactSpace E] [PolishSpace E]
    [PseudoMetricSpace F] [BorelSpace F] [LocallyCompactSpace F] [PolishSpace F]
    (P : ProbabilityMeasure Omega) (mu : Measure E) (kappa : Kernel E F) [IsMarkovKernel kappa]
    (X : Omega → Measure E) (hX : IsPoissonPointProcess mu P X)
    (Xkappa : Omega → Measure F)
    (hXkappa : IsKernelColoredRandomMeasure P mu kappa X Xkappa)
    (hMuKappaFinite :
      ∀ ⦃A : Set F⦄, MeasurableSet A → Bornology.IsBounded A →
        kernelImageMeasure mu kappa A ≠ ⊤) :
    ∃ hXkappaRandom : IsRandomMeasure P Xkappa,
      ∀ (P' : ProbabilityMeasure Omega') (Y : Omega' → Measure F)
        (hY : IsPoissonPointProcess (kernelImageMeasure mu kappa) P' Y),
          P.map hXkappaRandom.1.aemeasurable =
            poissonPointProcessLaw (kernelImageMeasure mu kappa) P' Y hY := by
  -- Proof comment: unpack the hidden marked witness from `hXkappa`, rewrite the goal along the
  -- defining equality `Xkappa = kernelColoredRandomMeasure Xi`, and invoke the repaired witness
  -- helper.
  rcases hXkappa with ⟨Xi, hXi, hXiFst, hEq⟩
  rw [hEq]
  have hExists :
      ∃ hXkappaRandom : IsRandomMeasure P (kernelColoredRandomMeasure Xi),
        ∀ (P' : ProbabilityMeasure Omega') (Y : Omega' → Measure F)
          (hY : IsPoissonPointProcess (kernelImageMeasure mu kappa) P' Y),
            P.map hXkappaRandom.1.aemeasurable =
              poissonPointProcessLaw (kernelImageMeasure mu kappa) P' Y hY :=
      exists_kernelColoredRandomMeasure_distribution_eq_poissonPointProcessLaw
        P mu kappa X hX Xi hXi hXiFst hMuKappaFinite
  rcases hExists with
    ⟨hXkappaRandom, hLaw⟩
  exact ⟨hXkappaRandom, hLaw⟩

end ProbabilityTheory

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.BrownianStartedAt
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_4_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6.DyadicGeometry

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory NNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

private lemma covariance_congr_ae {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ := integral_congr_ae hX
  have hIntY : ∫ ω, Y ω ∂μ = ∫ ω, Y' ω ∂μ := integral_congr_ae hY
  rw [ProbabilityTheory.covariance, ProbabilityTheory.covariance, hIntX, hIntY]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY]

private def pinValueAtZero (X : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ if t = 0 then 0 else X t ω

private lemma areModifications_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1) :
    AreModifications μ (pinValueAtZero X) X := by
  have hzero :
      ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using
      (mem_ae_iff_prob_eq_one₀
        ((hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton 0))).2
        hstart
  intro t
  filter_upwards [hzero] with ω hω
  by_cases ht : t = 0
  · subst ht
    simp [pinValueAtZero, hω]
  · simp [pinValueAtZero, ht]

private lemma hasAlmostSurelyContinuousPaths_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1)
    (hcont : HasAlmostSurelyContinuousPaths μ X) :
    HasAlmostSurelyContinuousPaths μ (pinValueAtZero X) := by
  have hzero :
      ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using
      (mem_ae_iff_prob_eq_one₀
        ((hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton 0))).2
        hstart
  filter_upwards [hzero, hcont] with ω hω hωcont
  have hpath : processPath (pinValueAtZero X) ω = processPath X ω := by
    funext t
    by_cases ht : t = 0
    · subst ht
      simp [processPath, pinValueAtZero, hω]
    · simp [processPath, pinValueAtZero, ht]
  simpa [HasAlmostSurelyContinuousPaths] using hpath.symm ▸ hωcont

private lemma tendstoUniformlyOn_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xapprox : ℕ → NNReal → Ω → ℝ} {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1)
    (hconv :
      ∀ᵐ ω ∂μ,
        TendstoUniformlyOn
          (fun n t ↦ Xapprox n t ω)
          (fun t ↦ X t ω)
          atTop
          (Set.Icc (0 : NNReal) 1)) :
    ∀ᵐ ω ∂μ,
      TendstoUniformlyOn
        (fun n t ↦ Xapprox n t ω)
        (fun t ↦ pinValueAtZero X t ω)
        atTop
        (Set.Icc (0 : NNReal) 1) := by
  have hzero :
      ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using
      (mem_ae_iff_prob_eq_one₀
        ((hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton 0))).2
        hstart
  filter_upwards [hzero, hconv] with ω hω hωconv
  have hEq :
      Set.EqOn
        (fun t ↦ X t ω)
        (fun t ↦ pinValueAtZero X t ω)
        (Set.Icc (0 : NNReal) 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      simp [pinValueAtZero, hω]
    · simp [pinValueAtZero, ht0]
  exact hωconv.congr_right hEq

section BrownianApproximation

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Xtilde X : NNReal → Ω → ℝ}

local notation "UnitIntervalTime" => Set.Icc (0 : NNReal) 1

/-- Helper for Theorem 21.28: the left endpoint `0` belongs to the unit interval. -/
private lemma zero_mem_unitIntervalTime : (0 : NNReal) ∈ Set.Icc (0 : NNReal) 1 := by
  simp

/-- A real-valued process on `[0,1]` is Brownian motion on the unit interval if it starts from
`0`, is a centered Gaussian process with covariance kernel `s ∧ t`, and has almost surely
continuous paths. This is the finite-horizon source-facing bridge for Theorem 21.28. -/
def IsBrownianMotionOnUnitInterval (μ : Measure Ω) (B : UnitIntervalTime → Ω → ℝ) : Prop :=
  B ⟨0, zero_mem_unitIntervalTime⟩ = 0 ∧
    IsGaussianProcess B μ ∧
      (∀ t : UnitIntervalTime, ∫ ω, B t ω ∂μ = 0) ∧
      (∀ s t : UnitIntervalTime, cov[B s, B t; μ] = ((s.1 ⊓ t.1 : NNReal) : ℝ)) ∧
      HasAlmostSurelyContinuousPaths μ B

theorem isBrownianMotionOnUnitInterval_iff
    (μ : Measure Ω) (B : UnitIntervalTime → Ω → ℝ) :
    IsBrownianMotionOnUnitInterval μ B ↔
      B ⟨0, zero_mem_unitIntervalTime⟩ = 0 ∧
        IsGaussianProcess B μ ∧
          (∀ t : UnitIntervalTime, ∫ ω, B t ω ∂μ = 0) ∧
          (∀ s t : UnitIntervalTime, cov[B s, B t; μ] = ((s.1 ⊓ t.1 : NNReal) : ℝ)) ∧
          HasAlmostSurelyContinuousPaths μ B :=
  Iff.rfl

omit [IsProbabilityMeasure μ] in
/-- Restricting a Brownian motion on `[0,∞)` to `[0,1]` yields the finite-horizon Brownian
notion used in Theorem 21.28. -/
theorem IsBrownianMotion.onUnitInterval
    {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotionOnUnitInterval μ (fun t ω ↦ B t ω) := by
  have hcont :
      HasAlmostSurelyContinuousPaths μ (fun t : UnitIntervalTime ↦ B t) := by
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.comp continuous_subtype_val
  refine ⟨?_, hB.isGaussianProcess.restrict UnitIntervalTime, ?_, ?_, hcont⟩
  · simpa using hB.zero
  · intro t
    simpa using hB.mean_zero t
  · intro s t
    simpa using hB.covariance_eq s t

-- Proof sketch: the almost-sure sup-norm Cauchy condition yields, for almost every `ω`, a
-- uniform limit on `[0,1]`; the continuity of each approximant makes this limit continuous.
-- The deterministic-time `L^2` convergence identifies the limit with `Xtilde` at each time, so
-- the resulting process is a continuous Brownian version of `Xtilde` on `[0,1]`, and the same
-- pathwise limit is the asserted almost-sure uniform convergence on `[0,1]`.
/-- Helper for Theorem 21.28: if one fixed-time approximant family converges almost surely to `X`
and in `L²` to `Xtilde`, then the two limits agree almost surely. -/
private lemma fixedTimeAeEq_of_aeTendsto_and_tendstoL2
    {Xapprox : ℕ → Ω → ℝ} {X Xtilde : Ω → ℝ}
    (hXapprox_meas : ∀ n, AEStronglyMeasurable (Xapprox n) μ)
    (hXtilde_meas : AEStronglyMeasurable Xtilde μ)
    (hAe :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Xapprox n ω) atTop (nhds (X ω)))
    (hL2 :
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ Xapprox n ω - Xtilde ω) (2 : ℝ≥0∞) μ)
        atTop (nhds 0)) :
    X =ᵐ[μ] Xtilde := by
  have hX_measure :
      TendstoInMeasure μ (fun n ω ↦ Xapprox n ω) atTop X := by
    -- Proof comment: almost-sure convergence with measurable slices upgrades directly to
    -- convergence in measure.
    exact tendstoInMeasure_of_tendsto_ae hXapprox_meas hAe
  have hXtilde_measure :
      TendstoInMeasure μ (fun n ω ↦ Xapprox n ω) atTop Xtilde := by
    -- Proof comment: `L²` convergence gives the same convergence in measure to `Xtilde`.
    have htwo_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    simpa [Pi.sub_apply] using
      (tendstoInMeasure_of_tendsto_eLpNorm htwo_ne_zero
        hXapprox_meas hXtilde_meas hL2)
  -- Proof comment: limits in measure are almost-surely unique.
  simpa using tendstoInMeasure_ae_unique hX_measure hXtilde_measure

/-- Helper for the Brownian `L²` approximation theorem: if the Levy approximants `Xapprox n` are
pathwise continuous on `[0,1]`, have measurable deterministic-time slices, converge to `Xtilde`
at each deterministic time in `L^2`, and are almost surely Cauchy in the uniform topology on
`[0,1]`, then `Xtilde` admits a continuous version `X` on `[0,1]` such that `Xapprox n`
converges uniformly to `X` on `[0,1]` almost surely. -/
private theorem exists_continuous_version_on_unitInterval_with_uniform_limit_of_l2_approximants
    {Xapprox : ℕ → UnitIntervalTime → Ω → ℝ}
    {Xtilde : UnitIntervalTime → Ω → ℝ}
    (hXapprox_cont :
      ∀ n : ℕ, ∀ ω : Ω,
        Continuous (fun t : UnitIntervalTime ↦ Xapprox n t ω))
    (hXapprox_meas :
      ∀ t : UnitIntervalTime, ∀ n : ℕ,
        AEStronglyMeasurable (fun ω ↦ Xapprox n t ω) μ)
    (hXtilde_meas :
      ∀ t : UnitIntervalTime, AEStronglyMeasurable (fun ω ↦ Xtilde t ω) μ)
    (hL2 :
      ∀ t : UnitIntervalTime,
        Tendsto
          (fun n ↦ eLpNorm (fun ω ↦ Xapprox n t ω - Xtilde t ω) (2 : ℝ≥0∞) μ)
          atTop (nhds 0))
    (hCauchy :
      ∀ᵐ ω ∂μ,
        UniformCauchySeqOn
          (fun n (t : UnitIntervalTime) ↦ Xapprox n t ω)
          atTop
          Set.univ) :
    ∃ X : UnitIntervalTime → Ω → ℝ,
      AreModifications μ X (fun t : UnitIntervalTime ↦ Xtilde t) ∧
        HasAlmostSurelyContinuousPaths μ X ∧
        ∀ᵐ ω ∂μ,
          TendstoUniformlyOn
            (fun n (t : UnitIntervalTime) ↦ Xapprox n t ω)
            (fun t ↦ X t ω)
            atTop
            Set.univ := by
  classical
  let X : UnitIntervalTime → Ω → ℝ := fun t ω ↦ Filter.limUnder atTop (fun n ↦ Xapprox n t ω)
  have hXtendsto :
      ∀ t : UnitIntervalTime,
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ Xapprox n t ω) atTop (nhds (X t ω)) := by
    intro t
    -- Proof comment: the pathwise uniform Cauchy event gives a pointwise Cauchy sequence at each
    -- fixed time, and `limUnder` realizes its limit in the complete space `ℝ`.
    filter_upwards [hCauchy] with ω hω
    have hcauchy : CauchySeq (fun n ↦ Xapprox n t ω) := by
      simpa using (hω.cauchySeq (show t ∈ Set.univ by simp))
    simpa [X] using hcauchy.tendsto_limUnder
  have hmod :
      AreModifications μ X (fun t : UnitIntervalTime ↦ Xtilde t) := by
    intro t
    -- Proof comment: at each deterministic time, the almost-sure limit `X t` and the `L²` limit
    -- `Xtilde t` must agree almost surely.
    simpa using
      fixedTimeAeEq_of_aeTendsto_and_tendstoL2
        (fun n ↦ hXapprox_meas t n)
        (hXtilde_meas t)
        (hXtendsto t)
        (hL2 t)
  have huni :
      ∀ᵐ ω ∂μ,
        TendstoUniformlyOn
          (fun n (t : UnitIntervalTime) ↦ Xapprox n t ω)
          (fun t ↦ X t ω)
          atTop
          Set.univ := by
    -- Proof comment: once the pointwise limit is fixed by `limUnder`, the uniform Cauchy event
    -- upgrades to uniform convergence on the whole interval subtype.
    filter_upwards [hCauchy] with ω hω
    refine hω.tendstoUniformlyOn_of_tendsto ?_
    intro t ht
    simpa [X] using (hω.cauchySeq ht).tendsto_limUnder
  have hcont :
      HasAlmostSurelyContinuousPaths μ X := by
    -- Proof comment: a uniform limit of continuous paths on the compact interval subtype is
    -- continuous pathwise.
    filter_upwards [huni] with ω hω
    have hωcont :
        ContinuousOn (fun t : UnitIntervalTime ↦ X t ω) Set.univ := by
      refine hω.continuousOn ?_
      exact Frequently.of_forall fun n ↦ (hXapprox_cont n ω).continuousOn
    simpa [HasAlmostSurelyContinuousPaths, processPath, continuousOn_univ] using hωcont
  exact ⟨X, hmod, hcont, huni⟩

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: the real interval subtype `[0,1] ⊆ ℝ` maps continuously into the
`NNReal` unit interval subtype. -/
private lemma continuous_realSubtypeToUnitIntervalTime :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      (⟨t.1.toNNReal, by
          constructor
          · simp
          · simpa using Real.toNNReal_mono t.2.2⟩ : UnitIntervalTime)) := by
  -- Proof comment: `Real.toNNReal` is continuous, and the interval-membership proof is purely
  -- propositional, so the subtype map inherits continuity from the coordinate map.
  exact
    Continuous.subtype_mk
      (by simpa using (continuous_real_toNNReal.comp continuous_subtype_val))
      (fun t ↦ by
        constructor
        · simp
        · simpa using Real.toNNReal_mono t.2.2)

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: two continuous modifications of the same process on `[0,1]`
coincide almost surely at every unit-interval time. -/
private lemma aeEqOn_unitInterval_of_continuous_modifications
    {X Y Z : UnitIntervalTime → Ω → ℝ}
    (hXZ : AreModifications μ X Z)
    (hYZ : AreModifications μ Y Z)
    (hXcont : HasAlmostSurelyContinuousPaths μ X)
    (hYcont : HasAlmostSurelyContinuousPaths μ Y) :
    ∀ᵐ ω ∂μ, Set.EqOn (fun t ↦ X t ω) (fun t ↦ Y t ω) Set.univ := by
  let toUnit : Set.Icc (0 : ℝ) 1 → UnitIntervalTime := fun t ↦
    ⟨t.1.toNNReal, by
      constructor
      · simp
      · simpa using Real.toNNReal_mono t.2.2⟩
  let Xreal : Set.Icc (0 : ℝ) 1 → Ω → ℝ := fun t ω ↦ X (toUnit t) ω
  let Yreal : Set.Icc (0 : ℝ) 1 → Ω → ℝ := fun t ω ↦ Y (toUnit t) ω
  have hXYreal : AreModifications μ Xreal Yreal := by
    intro t
    -- Proof comment: both restricted processes agree almost surely with the same restricted
    -- reference process `Z`, hence they are modifications of one another.
    filter_upwards [hXZ (toUnit t), hYZ (toUnit t)] with ω hX hY
    exact hX.trans hY.symm
  have hXrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) 1,
          ContinuousWithinAt (processPath Xreal ω) (Set.Ici t) t := by
    filter_upwards [hXcont] with ω hω
    intro t
    have hcont : Continuous (processPath Xreal ω) := by
      -- Proof comment: restricting a continuous unit-interval path along the real-subtype
      -- parameterization preserves continuity.
      simpa [Xreal, toUnit, processPath_apply] using
        hω.comp continuous_realSubtypeToUnitIntervalTime
    exact hcont.continuousWithinAt
  have hYrc :
      ∀ᵐ ω ∂μ,
        ∀ t : Set.Icc (0 : ℝ) 1,
          ContinuousWithinAt (processPath Yreal ω) (Set.Ici t) t := by
    filter_upwards [hYcont] with ω hω
    intro t
    have hcont : Continuous (processPath Yreal ω) := by
      -- Proof comment: the same reparameterization argument applies to the second
      -- modification.
      simpa [Yreal, toUnit, processPath_apply] using
        hω.comp continuous_realSubtypeToUnitIntervalTime
    exact hcont.continuousWithinAt
  have hInd :
      AreIndistinguishable μ Xreal Yreal := by
    -- Proof comment: Lemma 21.5 upgrades almost-sure equality at each deterministic time to
    -- pathwise equality on the whole interval because both restricted paths are almost surely
    -- continuous.
    exact
      ProbabilityTheory.indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
        μ
        Xreal
        Yreal
        hXYreal
        Set.ordConnected_Icc
        hXrc
        hYrc
  rcases hInd with ⟨N, hN_meas, hN_zero, hN_sub⟩
  have hNae : ∀ᵐ ω ∂μ, ω ∉ N := by
    rw [ae_iff]
    simpa using hN_zero
  filter_upwards [hNae] with ω hω
  intro t ht
  let tReal : Set.Icc (0 : ℝ) 1 := by
    refine ⟨((t : NNReal) : ℝ), ?_⟩
    constructor
    · positivity
    · exact_mod_cast t.2.2
  have htEq : Xreal tReal ω = Yreal tReal ω := by
    -- Proof comment: outside the indistinguishability null set, every real-subtype time
    -- coordinate agrees, including the coordinate corresponding to `t`.
    by_contra hneq
    exact hω ((hN_sub tReal) hneq)
  simpa [Xreal, Yreal, toUnit, tReal, Real.toNNReal_coe] using htEq

omit [IsProbabilityMeasure μ] in
private theorem isBrownianMotionOnUnitInterval_of_brownian_covariance_of_modification
    {X : UnitIntervalTime → Ω → ℝ}
    (hzero : X ⟨0, zero_mem_unitIntervalTime⟩ = 0)
    (hgauss : IsGaussianProcess (fun t : UnitIntervalTime ↦ Xtilde t) μ)
    (hmean_zero : ∀ t : UnitIntervalTime, ∫ ω, Xtilde t ω ∂μ = 0)
    (hcov : ∀ s t : UnitIntervalTime, cov[Xtilde s, Xtilde t; μ] = ((s.1 ⊓ t.1 : NNReal) : ℝ))
    (hmod : AreModifications μ X (fun t : UnitIntervalTime ↦ Xtilde t))
    (hcont : HasAlmostSurelyContinuousPaths μ X) :
    IsBrownianMotionOnUnitInterval μ X := by
  refine ⟨hzero, hgauss.congr (fun t ↦ (hmod t).symm), ?_, ?_, hcont⟩
  · intro t
    calc
      ∫ ω, X t ω ∂μ = ∫ ω, Xtilde t ω ∂μ := integral_congr_ae (hmod t)
      _ = 0 := hmean_zero t
  · intro s t
    rw [covariance_congr_ae (hmod s) (hmod t), hcov s t]

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: a continuous modification of `Xtilde` with the same Brownian
covariance data is Brownian motion once the time-zero value is pinned pointwise. -/
private theorem isBrownianMotion_of_brownian_covariance_of_modification
    {X : NNReal → Ω → ℝ}
    (hzero : X 0 = 0)
    (hgauss : IsGaussianProcess Xtilde μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, Xtilde t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[Xtilde s, Xtilde t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (hmod : AreModifications μ X Xtilde)
    (hcont : HasAlmostSurelyContinuousPaths μ X) :
    IsBrownianMotion μ X := by
  have hgaussX : IsGaussianProcess X μ := by
    -- Proof comment: Gaussian finite-dimensional laws are preserved under coordinatewise
    -- almost-sure equality.
    exact hgauss.congr (fun t ↦ (hmod t).symm)
  have hmean_zeroX : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0 := by
    -- Proof comment: the centered mean transfers along almost-sure equality at each time.
    intro t
    calc
      ∫ ω, X t ω ∂μ = ∫ ω, Xtilde t ω ∂μ := integral_congr_ae (hmod t)
      _ = 0 := hmean_zero t
  have hcovX : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    -- Proof comment: covariance is stable under almost-sure replacement of each coordinate.
    intro s t
    rw [covariance_congr_ae (hmod s) (hmod t), hcov s t]
  -- Proof comment: Theorem 21.11 closes the Brownian owner once the transported fields are in
  -- place.
  exact
    (isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance μ X).2
      ⟨hzero, hgaussX, hmean_zeroX, hcovX, hcont⟩

/-- Helper for Theorem 21.28: `edist^4` for real-valued increments is the `ENNReal.ofReal`
image of the quartic increment polynomial. -/
private lemma realEdist_pow_four_eq_ofReal_sub_pow_four (a b : ℝ) :
    edist a b ^ (4 : ℝ) = ENNReal.ofReal ((b - a) ^ 4) := by
  -- Proof comment: raise the real distance to the fourth power, rewrite through `|a - b|`,
  -- and then use that even powers ignore the sign of the increment.
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg (a - b))]
  congr 1
  have habs : |a - b| ^ 4 = (a - b) ^ 4 := by
    rw [show |a - b| ^ 4 = (|a - b| ^ 2) ^ 2 by ring,
      show (a - b) ^ 4 = ((a - b) ^ 2) ^ 2 by ring, sq_abs]
  calc
    |a - b| ^ 4 = (a - b) ^ 4 := habs
    _ = (b - a) ^ 4 := by ring_nf

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: a standard Gaussian variable has fourth moment `3`. -/
private lemma gaussianRealFourthMoment_eq_three
    {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 := by
  letI : IsProbabilityMeasure (μ.map Y) := by
    rw [hY.map_eq]
    infer_instance
  letI : IsProbabilityMeasure μ := μ.isProbabilityMeasure_of_map Y
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: the standard Gaussian fourth moment is the even-moment formula at `k = 2`.
    have hMoment :=
      gaussianReal_even_moments_eq_factorial_ratio hStdId 2
    norm_num at hMoment
    exact hMoment
  -- Proof comment: transport the quartic moment of `Y` to the canonical Gaussian owner measure.
  exact
    (hY.integral_comp ((continuous_pow 4).aestronglyMeasurable)).trans hStdFourth

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: a centered Gaussian random variable has fourth moment
`3 * Var[Y]^2`. -/
private lemma centeredGaussianFourthMoment_eq_three_mul_variance_sq
    {Y : Ω → ℝ} (hY : HasGaussianLaw Y μ) (hY_mean : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure μ := hY.isProbabilityMeasure
  let v : NNReal := Var[Y; μ].toNNReal
  have hLaw :
      HasLaw Y (gaussianReal (∫ ω, Y ω ∂μ) v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    calc
      μ.map Y = gaussianReal ((μ.map Y)[id]) Var[id; μ.map Y].toNNReal := by
        exact ProbabilityTheory.IsGaussian.eq_gaussianReal (μ.map Y) hY.isGaussian_map
      _ = gaussianReal (∫ ω, Y ω ∂μ) v := by
        -- Proof comment: rewrite the Gaussian owner parameters back in terms of the original
        -- random variable.
        congr 1
        · simpa using
            (integral_map hY.aemeasurable measurable_id'.aestronglyMeasurable :
              ∫ x : ℝ, id x ∂Measure.map Y μ = ∫ ω, id (Y ω) ∂μ)
        · simpa [v] using
            congrArg Real.toNNReal
              (variance_map measurable_id'.aemeasurable hY.aemeasurable :
                Var[id; μ.map Y] = Var[id ∘ Y; μ])
  have hLaw0 :
      HasLaw Y (gaussianReal 0 v) μ := by
    refine ⟨hY.aemeasurable, ?_⟩
    -- Proof comment: the centered hypothesis identifies the Gaussian mean parameter with `0`.
    simpa [v, hY_mean] using hLaw.map_eq
  let c : ℝ := Real.sqrt (v : ℝ)
  have hStdId : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) :=
    { aemeasurable := measurable_id'.aemeasurable
      map_eq := by simp }
  have hStdFourth :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 = 3 := by
    -- Proof comment: reuse the standard Gaussian quartic moment before scaling.
    simpa using gaussianRealFourthMoment_eq_three hStdId
  have hScaleLaw :
      HasLaw (fun x : ℝ ↦ c * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    -- Proof comment: `N(0, v)` is the image of the standard Gaussian under multiplication by
    -- `sqrt v`.
    simpa [c, sq_abs, Real.sq_sqrt] using
      gaussianReal_const_mul hStdId c
  have hFourthBase :
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
    calc
      ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 v
          = ∫ x : ℝ, (c * x) ^ (4 : ℕ) ∂gaussianReal 0 1 := by
              symm
              simpa [Function.comp] using
                (hScaleLaw.integral_comp ((continuous_pow 4).aestronglyMeasurable))
      _ = ∫ x : ℝ, c ^ (4 : ℕ) * x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [mul_pow]
      _ = c ^ (4 : ℕ) * ∫ x : ℝ, x ^ (4 : ℕ) ∂gaussianReal 0 1 := by
            rw [integral_const_mul]
      _ = c ^ (4 : ℕ) * 3 := by
            rw [hStdFourth]
      _ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
            have hv_nonneg : 0 ≤ (v : ℝ) := by
              exact_mod_cast v.2
            have hsq : c ^ (2 : ℕ) = (v : ℝ) := by
              simp [c, Real.sq_sqrt, hv_nonneg]
            have hpow : c ^ (4 : ℕ) = (v : ℝ) ^ (2 : ℕ) := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
            rw [hpow, mul_comm]
  calc
    ∫ ω, Y ω ^ (4 : ℕ) ∂μ = 3 * ((v : ℝ) ^ (2 : ℕ)) := by
      -- Proof comment: move the quartic moment to the Gaussian owner side and evaluate it there.
      exact
        ((hLaw0.integral_comp ((continuous_pow 4).aestronglyMeasurable)).trans hFourthBase)
    _ = 3 * Var[Y; μ] ^ (2 : ℕ) := by
          have hv : (v : ℝ) = Var[Y; μ] := by
            simp [v, variance_nonneg Y μ]
          rw [hv]

/-- Helper for Theorem 21.28: on an ordered pair of times in `Set.Icc (0,T)`, the squared subtype
distance is the squared real time gap. -/
private lemma subtypeIccEdistPowTwoEqOfLe
    {T : NNReal} {s t : Set.Icc (0 : NNReal) T} (hst : s.1 ≤ t.1) :
    edist s t ^ (2 : ℝ) = ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
  -- Proof comment: on the ordered branch, the ambient `NNReal` distance is just `t - s`, and
  -- squaring removes the remaining absolute value.
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast]
  rw [edist_dist, Subtype.dist_eq, NNReal.dist_eq]
  have hst_real : (s.1 : ℝ) ≤ t.1 := by
    exact_mod_cast hst
  have hgap_nonneg : 0 ≤ (t.1 : ℝ) - s.1 := sub_nonneg.mpr hst_real
  have habs : |(s.1 : ℝ) - t.1| = (t.1 : ℝ) - s.1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hst_real)]
    ring
  rw [habs, ← ENNReal.ofReal_pow hgap_nonneg]

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: Brownian covariance forces the quartic increment moment to be
`3 * (t - s)^2`. -/
private lemma brownianIncrementFourthMoment_eq_three_mul_sq
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {s t : NNReal} (hst : s ≤ t) :
    ∫ ω, (X t ω - X s ω) ^ (4 : ℕ) ∂μ =
      3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  let inc : Ω → ℝ := fun ω ↦ X t ω - X s ω
  have hLaw :
      HasLaw inc (gaussianReal 0 (t - s)) μ :=
    centeredGaussianIncrement_hasLaw_of_brownianCovariance hgauss hmean_zero hcov hst
  have hIncGaussian : HasGaussianLaw inc μ := hLaw.hasGaussianLaw
  have hMean : ∫ ω, inc ω ∂μ = 0 := by
    -- Proof comment: the increment law is the centered Gaussian `N(0, t - s)`, so its mean
    -- vanishes immediately.
    simpa [inc] using hLaw.integral_eq
  -- Proof comment: the centered Gaussian fourth-moment formula reduces the claim to the
  -- variance of the increment, which is exactly the Brownian time lag.
  calc
    ∫ ω, (X t ω - X s ω) ^ (4 : ℕ) ∂μ = 3 * Var[inc; μ] ^ (2 : ℕ) := by
      simpa [inc] using
        centeredGaussianFourthMoment_eq_three_mul_variance_sq hIncGaussian hMean
    _ = 3 * (((t - s : NNReal) : ℝ) ^ (2 : ℕ)) := by
      rw [show Var[inc; μ] = ((t - s : NNReal) : ℝ) by simpa [inc] using hLaw.variance_eq]

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: on an ordered pair of times in `Set.Icc (0,T)`, Brownian covariance
gives the quartic Kolmogorov bound with constant `3`. -/
private lemma brownianCovarianceKolmogorovOrderedPairBound
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    {T : NNReal} :
    ∀ {s t : Set.Icc (0 : NNReal) T}, s.1 ≤ t.1 →
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ) ≤
        ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
  intro s t hst
  let inc : Ω → ℝ := fun ω ↦ X t.1 ω - X s.1 ω
  letI : IsProbabilityMeasure μ := hgauss.isProbabilityMeasure
  have hIncGaussian : HasGaussianLaw inc μ := by
    -- Proof comment: the increment law is Gaussian because Brownian covariance determines a
    -- centered Gaussian increment of variance `t - s`.
    exact
      (centeredGaussianIncrement_hasLaw_of_brownianCovariance
        hgauss hmean_zero hcov hst).hasGaussianLaw
  have hIncMemLp : MemLp inc (4 : ℝ≥0∞) μ := hIncGaussian.memLp (by norm_num)
  have hinc_int : Integrable (fun ω ↦ inc ω ^ (4 : ℕ)) μ := by
    -- Proof comment: Gaussian variables have moments of all orders, so the quartic increment is
    -- integrable.
    refine (hIncMemLp.integrable_norm_pow').congr ?_
    filter_upwards with ω
    have habs : |inc ω| ^ 4 = inc ω ^ 4 := by
      rw [show |inc ω| ^ 4 = (|inc ω| ^ 2) ^ 2 by ring,
        show inc ω ^ 4 = (inc ω ^ 2) ^ 2 by ring, sq_abs]
    simpa [Real.norm_eq_abs] using habs
  have hedist_eq :
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (inc ω ^ (4 : ℕ)) ∂μ := by
    -- Proof comment: rewrite the metric fourth power into the quartic polynomial on the ordered
    -- real increment.
    refine lintegral_congr_ae ?_
    filter_upwards with ω
    simpa [inc] using realEdist_pow_four_eq_ofReal_sub_pow_four (X s.1 ω) (X t.1 ω)
  have hmoment :
      ∫ ω, inc ω ^ (4 : ℕ) ∂μ = 3 * (((t.1 - s.1 : NNReal) : ℝ) ^ (2 : ℕ)) := by
    -- Proof comment: the explicit fourth-moment identity is the Brownian covariance input to the
    -- Kolmogorov estimate.
    simpa [inc] using
      brownianIncrementFourthMoment_eq_three_mul_sq
        hgauss hmean_zero hcov hst
  calc
    ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
        = ENNReal.ofReal (∫ ω, inc ω ^ (4 : ℕ) ∂μ) := by
            rw [hedist_eq]
            symm
            exact
              MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinc_int
                (Filter.Eventually.of_forall fun ω ↦ by positivity)
    _ = ENNReal.ofReal (3 * (((t.1 - s.1 : NNReal) : ℝ) ^ (2 : ℕ))) := by
          rw [hmoment]
    _ = ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
          rw [NNReal.coe_sub hst]
    _ ≤ ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := le_rfl

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: Brownian covariance yields the quartic increment bound required on
every finite interval `[0,T]`. -/
private lemma brownianCovarianceKolmogorovOnIcc_quartic
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (T : NNReal) :
    ∀ s t : Set.Icc (0 : NNReal) T,
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ) ≤
        (3 : ℝ≥0∞) * edist s t ^ (2 : ℝ) := by
  intro s t
  -- Proof comment: reduce the interval estimate to the ordered-pair moment bound, and in the
  -- reversed branch swap the time pair and use symmetry of `edist`.
  by_cases hst : s.1 ≤ t.1
  · have hthree_nonneg : (0 : ℝ) ≤ 3 := by norm_num
    rw [subtypeIccEdistPowTwoEqOfLe hst]
    calc
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
          ≤ ENNReal.ofReal (3 * (((t.1 : ℝ) - s.1) ^ 2)) := by
              exact brownianCovarianceKolmogorovOrderedPairBound hgauss hmean_zero hcov hst
      _ = (3 : ℝ≥0∞) * ENNReal.ofReal (((t.1 : ℝ) - s.1) ^ 2) := by
            rw [ENNReal.ofReal_mul hthree_nonneg]
            norm_num
  · have hts : t.1 ≤ s.1 := le_of_not_ge hst
    have hthree_nonneg : (0 : ℝ) ≤ 3 := by norm_num
    rw [edist_comm, subtypeIccEdistPowTwoEqOfLe hts]
    calc
      ∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ (4 : ℝ) ∂μ
          = ∫⁻ ω, edist (X t.1 ω) (X s.1 ω) ^ (4 : ℝ) ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards with ω
              rw [edist_comm]
      _ ≤ ENNReal.ofReal (3 * (((s.1 : ℝ) - t.1) ^ 2)) := by
            simpa using
              (brownianCovarianceKolmogorovOrderedPairBound hgauss hmean_zero hcov hts :
                (∫⁻ ω, edist (X t.1 ω) (X s.1 ω) ^ (4 : ℝ) ∂μ) ≤
                  ENNReal.ofReal (3 * (((s.1 : ℝ) - t.1) ^ 2)))
      _ = (3 : ℝ≥0∞) * ENNReal.ofReal (((s.1 : ℝ) - t.1) ^ 2) := by
            rw [ENNReal.ofReal_mul hthree_nonneg]
            norm_num

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 21.28: the quartic Brownian increment bound on `[0, T]` matches the owner
Kolmogorov exponent spelling `q = 1 + 1`. -/
private lemma brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (T : NNReal) :
    ∀ s t : Set.Icc (0 : NNReal) T,
      (∫⁻ ω, edist (X s.1 ω) (X t.1 ω) ^ ((4 : ℝ≥0) : ℝ) ∂μ) ≤
        (3 : ℝ≥0∞) * edist s t ^ (1 + ((1 : ℝ≥0) : ℝ)) := by
  intro s t
  have hquartic :=
    brownianCovarianceKolmogorovOnIcc_quartic hgauss hmean_zero hcov T s t
  convert hquartic using 1
  · norm_num

/-- Helper for Theorem 21.28: after replacing the Brownian-covariance process by a measurable
version, Theorem 21.6 yields a continuous real-valued modification on `NNReal`. -/
private lemma existsContinuousRealModificationOfBrownianCovariance
    {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) :
    ∃ Y : NNReal → Ω → ℝ,
      AreModifications μ Y X ∧
        HasAlmostSurelyContinuousPaths μ Y := by
  -- Route correction: the missing `Items/...` owner was the wrong import path. The chapter-local
  -- Theorem 21.6 is available, so we can reuse the canonical Kolmogorov-Chentsov bridge here.
  let γ : ℝ≥0 := (1 : ℝ≥0) / 8
  have hγpos : 0 < γ := by
    norm_num [γ]
  have hγlt : (γ : ℝ) < (1 : ℝ) / 4 := by
    norm_num [γ]
  have hγle : γ ≤ 1 := by
    have h8 : (1 : ℝ≥0) ≤ 8 := by norm_num
    have h : ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1 := by
      exact div_le_self (by positivity : 0 ≤ (1 : ℝ≥0)) h8
    change ((1 : ℝ≥0) / 8 : ℝ≥0) ≤ 1
    exact h
  let Xm : NNReal → Ω → ℝ := fun t ↦ (hgauss.aemeasurable t).mk (X t)
  have hXmEq : ∀ t : NNReal, X t =ᵐ[μ] Xm t := by
    intro t
    simpa [Xm] using (hgauss.aemeasurable t).ae_eq_mk
  have hXmGauss : IsGaussianProcess Xm μ := by
    -- Proof comment: replacing each time slice by its measurable representative preserves the
    -- Gaussian finite-dimensional laws.
    exact hgauss.congr hXmEq
  have hXmMeanZero : ∀ t : NNReal, ∫ ω, Xm t ω ∂μ = 0 := by
    intro t
    -- Proof comment: the centered mean transfers along the fixed-time almost-sure equality
    -- between `X` and the measurable proxy `Xm`.
    calc
      ∫ ω, Xm t ω ∂μ = ∫ ω, X t ω ∂μ := by
        symm
        exact integral_congr_ae (hXmEq t)
      _ = 0 := hmean_zero t
  have hXmCov : ∀ s t : NNReal, cov[Xm s, Xm t; μ] = ((s ⊓ t : NNReal) : ℝ) := by
    intro s t
    -- Proof comment: covariance is stable under fixed-time almost-sure replacement of each
    -- coordinate.
    rw [← covariance_congr_ae (hXmEq s) (hXmEq t), hcov s t]
  have hkolm :
      ∀ T : NNReal, ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ Xm T α β C := by
    intro T
    refine ⟨(4 : ℝ≥0), (1 : ℝ≥0), (3 : ℝ≥0), ?_⟩
    refine ⟨by norm_num, by norm_num, ?_⟩
    exact
      IsKolmogorovProcess.mk_of_secondCountableTopology
        (fun t : Set.Icc (0 : NNReal) T ↦ (hgauss.aemeasurable t.1).measurable_mk)
        (brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
          hXmGauss hXmMeanZero hXmCov T)
        (by norm_num)
        (by norm_num)
  rcases exists_modification_with_locally_holder_paths hkolm with
    ⟨Y, hmod, hholder, -⟩
  refine ⟨Y, ?_, ?_⟩
  · intro t
    -- Proof comment: compose the measurable-proxy modification returned by Theorem 21.6 with the
    -- fixed-time almost-sure equality `X = Xm`.
    filter_upwards [hXmEq t, hmod t] with ω hωXm hωmod
    exact hωmod.symm.trans hωXm.symm
  let γIoc : Set.Ioc (0 : ℝ≥0) (1 : ℝ≥0) := ⟨γ, ⟨hγpos, hγle⟩⟩
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  -- Proof comment: Theorem 21.6 gives local Hölder control at exponent `1 / 8`, and any
  -- positive-exponent local Hölder path is continuous.
  have hloc : LocallyHolderWith γIoc (processPath Y ω) := by
    simpa [processPath_apply, γIoc, γ] using hholder γ hγpos
      (fun T ↦ by
        refine ⟨(4 : ℝ≥0), (1 : ℝ≥0), (3 : ℝ≥0), ?_, ?_⟩
        · refine ⟨by norm_num, by norm_num, ?_⟩
          exact
            IsKolmogorovProcess.mk_of_secondCountableTopology
              (fun t : Set.Icc (0 : NNReal) T ↦ (hgauss.aemeasurable t.1).measurable_mk)
              (brownianCovarianceKolmogorovOnIcc_quarticOwnerBound
                hXmGauss hXmMeanZero hXmCov T)
              (by norm_num)
              (by norm_num)
        · simpa using hγlt) ω
  exact
    continuous_of_locallyHolderWith hloc

-- Verified local owner choice: semantic search did not expose an existing chapter owner for the
-- Levy `L²` approximation construction, so this file packages the source-facing objects `X^n` and
-- `Xtilde` directly and states the public theorem using the interval-local Brownian owner on
-- `[0,1]`, matching the source's finite-horizon conclusion.
/-- Source-facing owner for the Levy `L²` approximation construction used in Theorem 21.28. Its
fields are the chapter processes `X^n` and `\tilde X` together with the deterministic-time
measurability, `L²` convergence, almost-sure uniform Cauchy control, and Brownian covariance data
from the construction. -/
structure BrownianL2Approximation (μ : Measure Ω) [IsProbabilityMeasure μ] where
  Xn : ℕ → NNReal → Ω → ℝ
  Xtilde : NNReal → Ω → ℝ
  hXn_cont :
    ∀ n : ℕ, ∀ ω : Ω,
      ContinuousOn (fun t : NNReal ↦ Xn n t ω) (Set.Icc (0 : NNReal) 1)
  hXn_meas :
    ∀ t : UnitIntervalTime, ∀ n : ℕ,
      AEStronglyMeasurable (fun ω ↦ Xn n t ω) μ
  hXtilde_meas :
    ∀ t : UnitIntervalTime, AEStronglyMeasurable (fun ω ↦ Xtilde t ω) μ
  hL2 :
    ∀ t : UnitIntervalTime,
      Tendsto
        (fun n ↦ eLpNorm (fun ω ↦ Xn n t ω - Xtilde t ω) (2 : ℝ≥0∞) μ)
        atTop (nhds 0)
  hCauchy :
    ∀ᵐ ω ∂μ,
      UniformCauchySeqOn
        (fun n (t : NNReal) ↦ Xn n t ω)
        atTop
        (Set.Icc (0 : NNReal) 1)
  hXtilde_zero : Xtilde 0 = 0
  hXtilde_gauss : IsGaussianProcess Xtilde μ
  hXtilde_mean_zero : ∀ t : NNReal, ∫ ω, Xtilde t ω ∂μ = 0
  hXtilde_cov :
    ∀ s t : NNReal, cov[Xtilde s, Xtilde t; μ] = ((s ⊓ t : NNReal) : ℝ)

/-- Theorem 21.28 [Brownian motion, L^2-approximation]: for the chapter Levy `L²` approximation
package `A = (X^n, \tilde X)`, there exists a continuous version `X` of `\tilde X` on `[0,1]`;
this `X` is Brownian motion on the unit interval, and the approximants `X^n` converge to `X`
uniformly on `[0,1]` almost surely. -/
theorem exists_continuous_version_with_uniform_limit_of_l2_approximants
    (A : BrownianL2Approximation μ) :
    ∃ X : UnitIntervalTime → Ω → ℝ,
      AreModifications μ X (fun t : UnitIntervalTime ↦ A.Xtilde t) ∧
        IsBrownianMotionOnUnitInterval μ X ∧
          ∀ᵐ ω ∂μ,
            TendstoUniformlyOn
              (fun n (t : UnitIntervalTime) ↦ A.Xn n t ω)
              (fun t : UnitIntervalTime ↦ X t ω)
              atTop
              Set.univ := by
  have hXn_cont_subtype :
      ∀ n : ℕ, ∀ ω : Ω,
        Continuous (fun t : UnitIntervalTime ↦ A.Xn n t ω) := by
    intro n ω
    -- Proof comment: restrict the ambient interval-continuous approximants to the unit-interval
    -- subtype expected by the continuous-version theorem.
    simpa [continuousOn_univ] using
      (A.hXn_cont n ω).comp_continuous continuous_subtype_val fun t ↦ t.2
  have hCauchy_subtype :
      ∀ᵐ ω ∂μ,
        UniformCauchySeqOn
          (fun n (t : UnitIntervalTime) ↦ A.Xn n t ω)
          atTop
          Set.univ := by
    -- Proof comment: transport the almost-sure uniform Cauchy control along the subtype
    -- inclusion `UnitIntervalTime ↪ NNReal`.
    filter_upwards [A.hCauchy] with ω hω
    simpa using hω.comp (fun t : UnitIntervalTime ↦ (t : NNReal))
  rcases
      exists_continuous_version_on_unitInterval_with_uniform_limit_of_l2_approximants
        hXn_cont_subtype
        A.hXn_meas
        A.hXtilde_meas
        A.hL2
        hCauchy_subtype with
    ⟨Xc, hmodXc, hcontXc, huniXc⟩
  rcases
      existsContinuousRealModificationOfBrownianCovariance
        A.hXtilde_gauss
        A.hXtilde_mean_zero
        A.hXtilde_cov with
    ⟨Y, hmodY, hcontY⟩
  have hYgauss : IsGaussianProcess Y μ := by
    -- Proof comment: the continuous modification inherits the Gaussian finite-dimensional laws of
    -- `A.Xtilde`.
    exact A.hXtilde_gauss.congr fun t ↦ (hmodY t).symm
  have hYstart : μ (Y 0 ⁻¹' ({0} : Set ℝ)) = 1 := by
    -- Proof comment: the modification agrees almost surely with the pinned time-zero slice of
    -- `A.Xtilde`, so the intermediate continuous version also starts from `0` almost surely.
    have hYzero : ∀ᵐ ω ∂μ, Y 0 ω = 0 := by
      simpa [A.hXtilde_zero] using hmodY 0
    exact
      (mem_ae_iff_prob_eq_one₀
        ((hYgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton 0))).1
        (by simpa using hYzero)
  let B : NNReal → Ω → ℝ := pinValueAtZero Y
  have hmodPin : AreModifications μ B Y := by
    -- Proof comment: pinning at time `0` preserves the process almost surely because `Y` already
    -- takes the value `0` there with probability one.
    simpa [B] using areModifications_pinValueAtZero hYgauss hYstart
  have hmodB : AreModifications μ B A.Xtilde := by
    -- Proof comment: compose the pinning modification with the existing continuous modification
    -- of `A.Xtilde`.
    intro t
    filter_upwards [hmodPin t, hmodY t] with ω hωPin hωY
    exact hωPin.trans hωY
  have hcontB : HasAlmostSurelyContinuousPaths μ B := by
    -- Proof comment: pinning at time `0` keeps the already-continuous paths continuous almost
    -- surely.
    simpa [B] using hasAlmostSurelyContinuousPaths_pinValueAtZero hYgauss hYstart hcontY
  have hBzero : B 0 = 0 := by
    -- Proof comment: the pinned process is definitionally fixed at the origin.
    funext ω
    simp [B, pinValueAtZero]
  have hBrownB : IsBrownianMotion μ B := by
    -- Proof comment: Theorem 21.11 now applies to the pinned continuous modification, since all
    -- Brownian covariance data transfer along the modification.
    exact
      isBrownianMotion_of_brownian_covariance_of_modification
        hBzero
        A.hXtilde_gauss
        A.hXtilde_mean_zero
        A.hXtilde_cov
        hmodB
        hcontB
  let X : UnitIntervalTime → Ω → ℝ := fun t ω ↦ B t ω
  have hmodX : AreModifications μ X (fun t : UnitIntervalTime ↦ A.Xtilde t) := by
    -- Proof comment: restricting the pinned Brownian version to the subtype preserves the
    -- modification relation on every deterministic time in `[0,1]`.
    intro t
    simpa [X] using hmodB t
  have hBrownX : IsBrownianMotionOnUnitInterval μ X := by
    -- Proof comment: Brownian motion on `NNReal` restricts to the unit interval without any new
    -- normalization work.
    simpa [X] using IsBrownianMotion.onUnitInterval hBrownB
  have hEqPaths :
      ∀ᵐ ω ∂μ, Set.EqOn (fun t ↦ Xc t ω) (fun t ↦ X t ω) Set.univ := by
    -- Proof comment: on `[0,1]`, the generic continuous version and the pinned Brownian version
    -- are two continuous modifications of the same target process, so they agree almost surely
    -- at every unit-interval time.
    exact
      aeEqOn_unitInterval_of_continuous_modifications
        hmodXc
        hmodX
        hcontXc
        hBrownX.2.2.2.2
  have huniX :
      ∀ᵐ ω ∂μ,
        TendstoUniformlyOn
          (fun n (t : UnitIntervalTime) ↦ A.Xn n t ω)
          (fun t : UnitIntervalTime ↦ X t ω)
          atTop
          Set.univ := by
    -- Proof comment: transfer the almost-sure uniform limit from the generic continuous version
    -- `Xc` to the Brownian version `X` using their almost-sure pathwise equality.
    filter_upwards [huniXc, hEqPaths] with ω hωuni hωeq
    exact hωuni.congr_right hωeq
  exact ⟨X, hmodX, hBrownX, huniX⟩

end BrownianApproximation

end ProbabilityTheory

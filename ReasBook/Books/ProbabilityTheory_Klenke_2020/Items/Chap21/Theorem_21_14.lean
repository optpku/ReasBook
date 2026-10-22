/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Lemma_11_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Filter
open scoped ENNReal ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The time-inversion transform of a real-valued process on `[0,∞)`. -/
noncomputable def timeInversion (B : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ if t = 0 then 0 else (t : ℝ) * B (t⁻¹) ω

/-- The time-inverted process is given by the textbook piecewise formula. -/
theorem timeInversion_apply
    (B : NNReal → Ω → ℝ) (t : NNReal) (ω : Ω) :
    timeInversion B t ω = if t = 0 then 0 else (t : ℝ) * B (t⁻¹) ω :=
  rfl

namespace IsBrownianMotion

variable [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.14: away from `0`, the time inversion process is the expected scalar
multiple of the inverted Brownian coordinate. -/
private lemma timeInversion_apply_ne_zero
    {B : NNReal → Ω → ℝ} {t : NNReal} (ht : t ≠ 0) :
    ProbabilityTheory.timeInversion B t = fun ω ↦ (t : ℝ) * B (t⁻¹) ω := by
  -- Proof comment: on the nonzero branch, the defining `if` reduces to the textbook formula.
  funext ω
  simp [ProbabilityTheory.timeInversion, ht]

/-- Helper for Theorem 21.14: time inversion preserves Gaussian finite-dimensional laws. -/
lemma timeInversion_isGaussianProcess
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsGaussianProcess (ProbabilityTheory.timeInversion B) μ := by
  -- Proof comment: every inverted coordinate is a scalar multiple of the single Brownian
  -- coordinate `B (t⁻¹)`, so Gaussianity is inherited from the Brownian process.
  let hGaussian : IsGaussianProcess B μ := IsBrownianMotion.isGaussianProcess hB
  refine hGaussian.of_isGaussianProcess ?_
  intro t
  refine ⟨{t⁻¹}, ?_, ?_⟩
  · refine
      { toFun := fun x ↦ (if t = 0 then 0 else (t : ℝ)) * x ⟨t⁻¹, by simp⟩
        map_add' := by
          intro x y
          simp [mul_add]
        map_smul' := by
          intro c x
          simp [smul_eq_mul, mul_left_comm]
        cont := by
          fun_prop }
  · intro ω
    simp [ProbabilityTheory.timeInversion]

/-- Helper for Theorem 21.14: every marginal of the time-inverted process is centered. -/
lemma timeInversion_mean_zero
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (t : NNReal) :
    ∫ ω, ProbabilityTheory.timeInversion B t ω ∂μ = 0 := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: rewrite the time-inverted marginal as a scalar multiple of `B (t⁻¹)` and use
  -- that Brownian marginals have mean `0`.
  by_cases ht : t = 0
  · subst ht
    simp [ProbabilityTheory.timeInversion]
  · rw [timeInversion_apply_ne_zero ht, integral_const_mul]
    rw [hB.mean_zero (t⁻¹)]
    ring

/-- Helper for Theorem 21.14: the time-inverted covariance kernel is still `s ⊓ t`. -/
lemma timeInversion_covariance_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (s t : NNReal) :
    cov[ProbabilityTheory.timeInversion B s, ProbabilityTheory.timeInversion B t; μ] =
      ((s ⊓ t : NNReal) : ℝ) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  -- Proof comment: after ordering the times, the Brownian covariance at inverse times is
  -- `t⁻¹`, and the prefactor `s * t` collapses this back to `s = s ⊓ t`.
  wlog hst : s ≤ t generalizing s t with hswap
  · rw [covariance_comm, inf_comm]
    exact hswap t s (le_of_not_ge hst)
  by_cases hs : s = 0
  · subst hs
    have hZero : ProbabilityTheory.timeInversion B 0 = 0 := by
      funext ω
      simp [ProbabilityTheory.timeInversion]
    rw [hZero, covariance_zero_left]
    simp
  by_cases ht : t = 0
  · subst ht
    exact (hs (le_antisymm hst bot_le)).elim
  have hs_pos : 0 < s := pos_iff_ne_zero.mpr hs
  have hInv : t⁻¹ ≤ s⁻¹ := inv_anti₀ hs_pos hst
  rw [timeInversion_apply_ne_zero hs, timeInversion_apply_ne_zero ht,
    covariance_const_mul_left,
    covariance_const_mul_right, IsBrownianMotion.covariance_eq hB (s⁻¹) (t⁻¹)]
  calc
    (s : ℝ) * ((t : ℝ) * (((s⁻¹ ⊓ t⁻¹ : NNReal) : ℝ)))
        = (s : ℝ) * ((t : ℝ) * (((t⁻¹ : NNReal) : ℝ))) := by
            rw [inf_eq_right.mpr hInv]
    _ = (s : ℝ) * 1 := by
          simp [ht]
    _ = (s : ℝ) := by ring
    _ = ((s ⊓ t : NNReal) : ℝ) := by
          simp [inf_eq_left.mpr hst]

/-- Helper for Theorem 21.14: the Brownian value at an integer time is the telescoping sum of the
preceding unit increments. -/
private lemma brownianIntegerSkeleton_eq_sum_unitIncrements
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (n : ℕ) :
    (fun ω ↦ B (n : NNReal) ω) =
      fun ω ↦ ∑ i ∈ Finset.range n, (B ((i + 1 : ℕ) : NNReal) ω - B (i : NNReal) ω) := by
  funext ω
  induction n with
  | zero =>
      -- Proof comment: the empty telescoping sum matches the Brownian initial value `B 0 = 0`.
      simp [hB.zero]
  | succ n ih =>
      -- Proof comment: split off the last increment and telescope the prefix sum by induction.
      calc
        B ((n + 1 : ℕ) : NNReal) ω =
            B (n : NNReal) ω + (B ((n + 1 : ℕ) : NNReal) ω - B (n : NNReal) ω) := by ring
        _ = (∑ i ∈ Finset.range n, (B ((i + 1 : ℕ) : NNReal) ω - B (i : NNReal) ω)) +
            (B ((n + 1 : ℕ) : NNReal) ω - B (n : NNReal) ω) := by
              rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1),
              (B ((i + 1 : ℕ) : NNReal) ω - B (i : NNReal) ω) := by
              rw [Finset.sum_range_succ]

/-- Helper for Theorem 21.14: the Brownian motion integer skeleton divided by time converges
almost surely to `0`. -/
private lemma brownianIntegerSkeleton_div_tendsto_zero_ae
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ B ((n + 1 : ℕ) : NNReal) ω / (n + 1 : ℝ)) atTop (nhds 0) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Y : ℕ → Ω → ℝ := fun n ω ↦ B ((n + 1 : ℕ) : NNReal) ω - B (n : NNReal) ω
  have hY0_law : HasLaw (Y 0) (gaussianReal 0 1) μ := by
    -- Proof comment: the first unit increment is just the time-`1` Brownian marginal because
    -- `B 0 = 0`.
    simpa [Y, hB.zero] using hB.gaussian_marginal (t := 1) (by positivity)
  have hY_integrable : Integrable (Y 0) μ := by
    -- Proof comment: a Brownian unit increment has finite second moment, hence finite first
    -- moment.
    exact hY0_law.hasGaussianLaw.memLp_two.integrable (by norm_num)
  have hY_pairwise : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    -- Proof comment: the unit increments along the monotone integer-time sequence are
    -- independent, so in particular they are pairwise independent.
    have hIndep : iIndepFun Y μ :=
      hB.indepIncrements.nat (fun i j hij ↦ by exact_mod_cast hij)
    intro i j hij
    exact hIndep.indepFun hij
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) μ μ := by
    -- Proof comment: stationary increments identify every unit increment with the first one.
    intro n
    simpa [Y, add_comm, add_left_comm, add_assoc, hB.zero] using
      hB.stationaryIncrements.identDistrib_increment (r := 0) (s := (1 : NNReal))
        (t := (n : NNReal))
  have hY_mean_zero : μ[Y 0] = 0 := by
    -- Proof comment: the first unit increment has the centered Gaussian law `N(0,1)`.
    simpa using hY0_law.integral_eq
  have hStrongLaw :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) atTop (nhds 0) := by
    -- Proof comment: apply the pairwise-independent strong law to the unit-increment sequence.
    simpa [hY_mean_zero] using ProbabilityTheory.strong_law_ae_real Y hY_integrable hY_pairwise
      hY_ident
  have hStrongLawShift :
      ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Y i ω) / (n + 1 : ℝ)) atTop (nhds 0) := by
    -- Proof comment: shifting the averaging index by one preserves the same `atTop` limit.
    filter_upwards [hStrongLaw] with ω hω
    have hSuccComp :
        (fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Y i ω) / (n + 1 : ℝ)) =
          (fun n : ℕ ↦ (∑ i ∈ Finset.range n, Y i ω) / n) ∘ fun n : ℕ ↦ n + 1 := by
      -- Proof comment: record the successor reindexing explicitly so the limit composition has
      -- the exact target normal form.
      funext n
      simp [Function.comp]
    simpa [hSuccComp, Function.comp] using hω.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hStrongLawShift] with ω hω
  have hRewrite :
      (fun n : ℕ ↦ B ((n + 1 : ℕ) : NNReal) ω / (n + 1 : ℝ)) =
        fun n : ℕ ↦ (∑ i ∈ Finset.range (n + 1), Y i ω) / (n + 1 : ℝ) := by
    funext n
    rw [show ∑ i ∈ Finset.range (n + 1), Y i ω = B ((n + 1 : ℕ) : NNReal) ω by
      simpa [Y] using
        (congrArg (fun g : Ω → ℝ ↦ g ω)
          (brownianIntegerSkeleton_eq_sum_unitIncrements (hB := hB) (n := n + 1))).symm]
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.of_eq hRewrite.symm) hω

/-- Helper for Theorem 21.14: shifting Brownian motion to a later starting time and recentering at
that starting value preserves the Brownian-motion structure. -/
private lemma brownianShift_sub
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (r : NNReal) :
    IsBrownianMotion μ (fun t ω ↦ B (r + t) ω - B r ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the recentered shifted process vanishes at the new origin by cancellation.
    funext ω
    simp
  · -- Proof comment: each increment of the shifted process is literally an increment of `B`
    -- along the translated time mesh.
    intro n t ht
    have hTranslated :
        ∀ i j, i ≤ j → (fun i ↦ r + t i) i ≤ (fun i ↦ r + t i) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) r
    simpa [add_assoc] using
      hB.indepIncrements n (fun i ↦ r + t i) hTranslated
  · -- Proof comment: stationary increments are unchanged by the deterministic time translation.
    intro u s t
    simpa [add_assoc, add_left_comm, add_comm] using
      hB.stationaryIncrements (r + u) s t
  · intro t ht
    -- Proof comment: the shifted increment has the same law as the increment from `0`, hence the
    -- same centered Gaussian marginal.
    have hId :
        IdentDistrib
          (fun ω ↦ B (r + t) ω - B r ω)
          (fun ω ↦ B t ω - B 0 ω)
          μ μ := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hB.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := r)
    have hLaw0 : HasLaw (fun ω ↦ B t ω - B 0 ω) (gaussianReal 0 t) μ := by
      simpa [hB.zero] using hB.gaussian_marginal ht
    exact hId.symm.hasLaw hLaw0
  · -- Proof comment: translate the time variable and subtract the constant starting value on each
    -- almost-surely continuous path.
    filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun t : NNReal ↦ B (r + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Theorem 21.14: negating a Brownian motion again yields a Brownian motion. -/
private lemma brownianNeg
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (fun t ω ↦ -B t ω) := by
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · -- Proof comment: the time-zero value stays `0` after negation.
    funext ω
    simp [hB.zero]
  · -- Proof comment: independent increments are preserved under the measurable additive map
    -- `x ↦ -x`.
    simpa using hB.indepIncrements.neg
  · -- Proof comment: every increment of `-B` is the negative of the corresponding increment of `B`,
    -- so the stationary-increment laws transport directly.
    intro r s t
    convert (hB.stationaryIncrements r s t).comp measurable_neg using 1
    · -- Proof comment: the negated increment of `B` is the increment of `-B`.
      funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
    · -- Proof comment: the same normalization applies to the translated reference increment.
      funext ω
      simp [Function.comp, sub_eq_add_neg, add_comm]
  · intro t ht
    -- Proof comment: centered Gaussian marginals are symmetric under negation.
    simpa using ProbabilityTheory.gaussianReal_neg (hB.gaussian_marginal ht)
  · -- Proof comment: pointwise negation preserves continuity of each sample path.
    filter_upwards [hB.continuous_paths] with ω hω
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hω.neg

/-- Helper for Theorem 21.14: on the `n`-th unit interval, the bad event that the Brownian
increment exceeds `√(n + 1)` in absolute value somewhere in the interval. -/
private def unitIntervalSqrtIncrementEvent
    (B : NNReal → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ u ∈ Set.Icc (0 : NNReal) 1,
      Real.sqrt (n + 1 : ℝ) <
        |B ((n : NNReal) + u) ω - B (n : NNReal) ω|}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((Finset.range ($n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ |($X k $ω)|)

/-- Helper for Theorem 21.14: the absolute value of a discrete martingale is a submartingale. -/
private lemma martingaleAbsSubmartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) :
    Submartingale (fun i ω ↦ |X i ω|) ℱ μ := by
  -- Proof comment: on `ℝ`, `|x| = x ⊔ (-x)`, and sup preserves the submartingale property.
  simpa [abs_eq_max_neg] using hX.submartingale.sup hX.neg.submartingale

/-- Helper for Theorem 21.14: Doob's maximal-event estimate for the absolute value of a discrete
martingale. -/
private lemma absMaxUpToL1EventBoundOfMartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ)
    {threshold : ℝ} (hthreshold : 0 < threshold) (n : ℕ) :
    ENNReal.ofReal threshold * μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω in {ω | threshold ≤ absMaxUpTo(X, n, ω)}, ENNReal.ofReal |X n ω| ∂μ := by
  let A : Set Ω := {ω | threshold ≤ absMaxUpTo(X, n, ω)}
  have hA_nonneg : 0 ≤ᵐ[μ.restrict A] fun ω ↦ |X n ω| := by
    filter_upwards with ω
    exact abs_nonneg (X n ω)
  have hsubAbs : Submartingale (fun i ω ↦ |X i ω|) ℱ μ := martingaleAbsSubmartingale hX
  have hboundReal :
      threshold * μ.real A ≤ ∫ ω in A, |X n ω| ∂μ := by
    exact
      (submartingale_maximal_event_expectation_bounds
        (X := fun i ω ↦ |X i ω|) hsubAbs n hthreshold).1
  have hAbsIntegrable : Integrable (fun ω ↦ |X n ω|) (μ.restrict A) := by
    simpa [Real.norm_eq_abs] using (hsubAbs.integrable n).norm.integrableOn
  have hlintegral :
      ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) =
        ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := μ.restrict A) hAbsIntegrable hA_nonneg]
  calc
    ENNReal.ofReal threshold * μ A = ENNReal.ofReal (threshold * μ.real A) := by
      rw [ENNReal.ofReal_mul hthreshold.le, MeasureTheory.ofReal_measureReal]
    _ ≤ ENNReal.ofReal (∫ ω in A, |X n ω| ∂μ) := ENNReal.ofReal_le_ofReal hboundReal
    _ = ∫⁻ ω in A, ENNReal.ofReal |X n ω| ∂μ := hlintegral

/-- Helper for Theorem 21.14: Doob's discrete `L^p` tail inequality for a real-valued martingale. -/
private theorem doobLpTailBoundOfMartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) {p threshold : ℝ}
    (hp : 1 ≤ p) (hthreshold : 0 < threshold) (n : ℕ) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ := by
  let A : Set Ω := {ω | threshold ≤ absMaxUpTo(X, n, ω)}
  let f : Ω → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal |X n ω|
  have hA_meas : MeasurableSet A := by
    refine measurableSet_le measurable_const ?_
    refine Finset.measurable_range_sup'' ?_
    intro k hk
    exact ((hX.stronglyMeasurable k).measurable.le (ℱ.le k)).abs
  have hXn_meas : Measurable fun ω ↦ X n ω := by
    exact (hX.stronglyMeasurable n).measurable.le (ℱ.le n)
  have hf_meas : AEMeasurable f μ := by
    exact (hXn_meas.abs.ennreal_ofReal).aemeasurable
  rcases eq_or_lt_of_le hp with hp_eq | hp1
  · subst hp_eq
    have hbound :=
      (absMaxUpToL1EventBoundOfMartingale (hX := hX) hthreshold n).trans
        (MeasureTheory.setLIntegral_le_lintegral A f)
    simpa [A, Real.rpow_one] using hbound
  · let q : ℝ := p / (p - 1)
    have hp0 : 0 ≤ p := le_of_lt (lt_of_lt_of_le zero_lt_one hp)
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
    let g : Ω → ℝ≥0∞ := Set.indicator A (fun _ ↦ (1 : ℝ≥0∞))
    have hg_meas : AEMeasurable g μ := by
      exact (measurable_const.indicator hA_meas).aemeasurable
    have hset_eq :
        ∫⁻ ω in A, f ω ∂μ =
          ∫⁻ ω, (f * g) ω ∂μ := by
      have hfg : (fun ω ↦ f ω * g ω) = Set.indicator A f := by
        funext ω
        by_cases hω : ω ∈ A
        · simp [g, hω]
        · simp [g, hω]
      simpa [Pi.mul_def, hfg] using (MeasureTheory.lintegral_indicator hA_meas (f := f)).symm
    have hgpow_eq : (fun ω ↦ g ω ^ q) = g := by
      have hqpos : 0 < q := hpq.symm.pos
      funext ω
      by_cases hω : ω ∈ A
      · simp [g, hω]
      · simpa [g, hω] using ENNReal.zero_rpow_of_pos hqpos
    have hfpow_eq :
        (fun ω ↦ f ω ^ p) = fun ω ↦ ENNReal.ofReal (Real.rpow |X n ω| p) := by
      funext ω
      simp [f, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (X n ω)) hp0]
    have hholder :
        ∫⁻ ω in A, f ω ∂μ ≤
          (∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p) *
            (μ A) ^ (1 / q) := by
      have hbase := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
      rw [← hset_eq] at hbase
      rw [hfpow_eq, hgpow_eq] at hbase
      have hg_int : ∫⁻ ω, g ω ∂μ = μ A := by
        simpa [g] using (MeasureTheory.lintegral_indicator_one (μ := μ) (s := A) hA_meas)
      rw [hg_int] at hbase
      exact hbase
    have hbridge :
        ENNReal.ofReal threshold * μ A ≤
          (∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p) *
            (μ A) ^ (1 / q) := by
      exact (absMaxUpToL1EventBoundOfMartingale (hX := hX) hthreshold n).trans hholder
    by_cases hA_zero : μ A = 0
    · rw [show μ {ω | threshold ≤ absMaxUpTo(X, n, ω)} = μ A by rfl, hA_zero]
      simp
    · have hA_top : μ A ≠ ∞ := measure_ne_top μ A
      have hA_factor : μ A = (μ A) ^ (1 / p) * (μ A) ^ (1 / q) := by
        rw [← ENNReal.rpow_add _ _ hA_zero hA_top]
        have hInvAdd : 1 / p + 1 / q = 1 := by
          simpa [one_div] using hpq.inv_add_inv_eq_one
        rw [hInvAdd, ENNReal.rpow_one]
      have hAq_pos : 0 < (μ A) ^ (1 / q) := by
        exact ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hA_zero) hA_top
      have hAq_top : (μ A) ^ (1 / q) ≠ ∞ := by
        exact ENNReal.rpow_ne_top_of_nonneg (le_of_lt (one_div_pos.mpr hpq.symm.pos)) hA_top
      have hcancel :
          ENNReal.ofReal threshold * (μ A) ^ (1 / p) ≤
            (∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p) := by
        have hbridge' :
            (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) * (μ A) ^ (1 / q) ≤
              (∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p) *
                (μ A) ^ (1 / q) := by
          calc
            (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) * (μ A) ^ (1 / q)
                = ENNReal.ofReal threshold * μ A := by
                    rw [mul_assoc, ← hA_factor]
            _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p) *
                  (μ A) ^ (1 / q) := hbridge
        exact (ENNReal.mul_le_mul_iff_left hAq_pos.ne' hAq_top).1 hbridge'
      have hpow := ENNReal.rpow_le_rpow hcancel hp0
      calc
        ENNReal.ofReal (Real.rpow threshold p) * μ A =
            (ENNReal.ofReal threshold * (μ A) ^ (1 / p)) ^ p := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
              rw [ENNReal.ofReal_rpow_of_nonneg hthreshold.le hp0]
              congr 1
              rw [← ENNReal.rpow_mul]
              have hpp : (1 / p) * p = 1 := by
                field_simp [hp1.ne']
              rw [hpp, ENNReal.rpow_one]
        _ ≤ ((∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ) ^ (1 / p)) ^ p := hpow
        _ = ∫⁻ ω, ENNReal.ofReal (Real.rpow |X n ω| p) ∂μ := by
              rw [← ENNReal.rpow_mul]
              have hpp : (1 / p) * p = 1 := by
                field_simp [hp1.ne']
              rw [hpp, ENNReal.rpow_one]

/-- Helper for Theorem 21.14: the sampled shifted Brownian path on the regular
`(m + 1)`-mesh of the `n`-th unit interval. -/
private noncomputable def unitIntervalGridSample
    (B : NNReal → Ω → ℝ) (n m : ℕ) : ℕ → Ω → ℝ :=
  fun k ω ↦ B ((n : NNReal) + (k : NNReal) / (m + 1)) ω - B (n : NNReal) ω

/-- Helper for Theorem 21.14: the regular-grid bad event is the sampled maximal event on the
`(m + 1)`-mesh of the `n`-th unit interval. -/
private def gridBadEvent
    (B : NNReal → Ω → ℝ) (n m : ℕ) : Set Ω :=
  {ω | Real.sqrt (n + 1 : ℝ) ≤ absMaxUpTo(unitIntervalGridSample B n m, m + 1, ω)}

/-- Helper for Theorem 21.14: the standard Gaussian fourth-moment tail constant used in the
discrete Doob estimate. -/
private noncomputable def standardGaussianFourthMoment : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (4 : ℕ)) ∂gaussianReal 0 1

/-- Helper for Theorem 21.14: the standard Gaussian fourth-moment constant is finite. -/
private lemma standardGaussianFourthMoment_ne_top :
    standardGaussianFourthMoment ≠ ⊤ := by
  have hMem : MemLp (fun x : ℝ ↦ x) (4 : ℕ) (gaussianReal 0 1) := by
    simpa using (IsGaussian.memLp_id (μ := gaussianReal 0 1) (p := (4 : ℕ)))
  have hInt : Integrable (fun x : ℝ ↦ |x| ^ (4 : ℕ)) (gaussianReal 0 1) := by
    simpa [Real.norm_eq_abs] using hMem.integrable_norm_pow (by norm_num)
  rw [standardGaussianFourthMoment, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt]
  · simp
  · exact ae_of_all _ fun x ↦ by positivity

/-- Helper for Theorem 21.14: the partial sums of consecutive differences recover a process that
starts at `0`. -/
private lemma partialSum_diff_eq
    {X : ℕ → Ω → ℝ} (hX0 : X 0 = 0) (k : ℕ) (ω : Ω) :
    partialSum (fun j ω ↦ X (j + 1) ω - X j ω) k ω = X k ω := by
  induction k with
  | zero =>
      -- Proof comment: the empty partial sum matches the prescribed initial value.
      simp [partialSum, hX0]
  | succ k ih =>
      -- Proof comment: append the next consecutive difference and telescope.
      change ∑ i ∈ Finset.range (k + 1), (X (i + 1) ω - X i ω) = X (k + 1) ω
      rw [Finset.sum_range_succ]
      have hih : ∑ i ∈ Finset.range k, (X (i + 1) ω - X i ω) = X k ω := by
        have hih' := ih
        rw [partialSum_apply] at hih'
        exact hih'
      rw [hih]
      ring

/-- Helper for Theorem 21.14: an ordered Brownian increment has the centered Gaussian law with
variance equal to the time lag. -/
private lemma brownianIncrement_hasLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {s t : NNReal} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ := by
  by_cases hEq : s = t
  · letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    -- Proof comment: a zero-length Brownian increment is the constant-zero variable.
    subst hEq
    have hConst : HasLaw (fun _ : Ω ↦ (0 : ℝ)) (gaussianReal 0 0) μ := by
      constructor
      · exact measurable_const.aemeasurable
      · rw [Measure.map_const]
        simp [gaussianReal_zero_var]
    simpa using hConst
  · let u : NNReal := t - s
    have hu_pos : 0 < u := by
      exact tsub_pos_of_lt (lt_of_le_of_ne hst hEq)
    have hLawU : HasLaw (B u) (gaussianReal 0 u) μ := hB.gaussian_marginal hu_pos
    have hLawZero : HasLaw (fun ω ↦ B (u + 0) ω - B 0 ω) (gaussianReal 0 u) μ := by
      have hLawBase : HasLaw (fun ω ↦ B u ω - B 0 ω) (gaussianReal 0 u) μ := by
        refine hLawU.congr ?_
        simp [hB.zero]
      simpa using hLawBase
    have hStationary := hB.stationaryIncrements 0 u s
    have hu_add : u + s = t := by
      simp [u, tsub_add_cancel_of_le hst]
    -- Proof comment: stationary increments transport the unit-origin increment law to `[s, t]`.
    simpa [u, hu_add, add_comm, add_left_comm, add_assoc] using hStationary.symm.hasLaw hLawZero

/-- Helper for Theorem 21.14: the upper-step index of a point in `[0,1]` belongs to the sampled
mesh range. -/
private lemma upperStepIndex_mem_range_of_mem_Icc
    {m : ℕ} {u : NNReal} (hu : u ∈ Set.Icc (0 : NNReal) 1) :
    MeasureTheory.upperStepIndex m u ∈ Finset.range (m + 2) := by
  have hu_mul :
      u * (m + 1 : NNReal) ≤ (m + 1 : NNReal) := by
    simpa using
      mul_le_mul_of_nonneg_right hu.2 (show 0 ≤ (m + 1 : NNReal) by positivity)
  have hk_le : MeasureTheory.upperStepIndex m u ≤ m + 1 := by
    rw [MeasureTheory.upperStepIndex]
    exact (Nat.ceil_le).2 (by simpa [Nat.cast_add, Nat.cast_one] using hu_mul)
  exact Finset.mem_range.mpr (lt_of_le_of_lt hk_le (Nat.lt_succ_self _))

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.14: the strict continuum exceedance event is contained in the liminf of
the sampled grid exceedance events on every path that is continuous on `[0,1]`. -/
private lemma unitIntervalSqrtIncrementEvent_mem_liminf_gridBadEvent
    {B : NNReal → Ω → ℝ} (n : ℕ) {ω : Ω}
    (hcont : Continuous (fun u : NNReal ↦ B ((n : NNReal) + u) ω - B (n : NNReal) ω))
    (hω : ω ∈ unitIntervalSqrtIncrementEvent B n) :
    ω ∈ Filter.liminf (fun m : ℕ ↦ gridBadEvent B n m) atTop := by
  rw [mem_liminf_iff_eventually_mem]
  rcases hω with ⟨u, hu, huStrict⟩
  let f : NNReal → ℝ := fun v ↦ B ((n : NNReal) + v) ω - B (n : NNReal) ω
  have hf_cont : Continuous f := hcont
  have hopen : IsOpen {v : NNReal | Real.sqrt (n + 1 : ℝ) < |f v|} :=
    isOpen_lt continuous_const hf_cont.abs
  have hnhds :
      {v : NNReal | Real.sqrt (n + 1 : ℝ) < |f v|} ∈ nhds u := by
    exact hopen.mem_nhds huStrict
  have hEventually :
      ∀ᶠ m : ℕ in atTop,
        Real.sqrt (n + 1 : ℝ) < |f (MeasureTheory.upperStepTime m u)| := by
    exact (MeasureTheory.tendsto_upperStepTime u).eventually hnhds
  filter_upwards [hEventually] with m hm
  have hk : MeasureTheory.upperStepIndex m u ∈ Finset.range (m + 2) :=
    upperStepIndex_mem_range_of_mem_Icc hu
  have hGrid :
      Real.sqrt (n + 1 : ℝ) ≤
        |unitIntervalGridSample B n m (MeasureTheory.upperStepIndex m u) ω| := by
    -- Proof comment: the upper-step mesh point stays inside the open strict-exceedance neighborhood
    -- of the witness, so the sampled value still exceeds the threshold.
    simpa [f, unitIntervalGridSample, MeasureTheory.upperStepTime] using le_of_lt hm
  -- Proof comment: the witness upper-step index is one of the mesh points entering the sampled
  -- running maximum.
  exact le_trans hGrid <|
    Finset.le_sup' (s := Finset.range (m + 2))
      (f := fun k ↦ |unitIntervalGridSample B n m k ω|) hk

/-- Helper for Theorem 21.14: the liminf of a sequence of sets has measure bounded by the liminf
of the sequence of measures. -/
private lemma measure_liminf_le_liminf_measure
    {μ : Measure Ω} (s : ℕ → Set Ω) :
    μ (Filter.liminf s atTop) ≤ Filter.liminf (fun n : ℕ ↦ μ (s n)) atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  let tails : ℕ → Set Ω := fun n ↦ ⋂ i ≥ n, s i
  have htails_mono : Monotone tails := by
    intro n m hnm ω hω
    simp only [tails, Set.mem_iInter] at hω ⊢
    intro i hi
    exact hω i (le_trans hnm hi)
  change μ (⋃ n : ℕ, tails n) ≤ _
  rw [htails_mono.measure_iUnion]
  refine iSup_le ?_
  intro n
  refine le_iSup_of_le n ?_
  refine le_iInf ?_
  intro i
  refine le_iInf ?_
  intro hi
  exact measure_mono <| by
    intro ω hω
    simp only [tails, Set.mem_iInter] at hω
    exact hω i hi

/-- Helper for Theorem 21.14: every regular-grid bad event on the `n`-th unit interval has a
uniform `O((n + 1)⁻²)` measure bound. -/
private lemma gridBadEvent_measure_le_invSq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (n m : ℕ) :
    μ (gridBadEvent B n m) ≤
      standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let W : NNReal → Ω → ℝ := fun t ω ↦ B ((n : NNReal) + t) ω - B (n : NNReal) ω
  let X : ℕ → Ω → ℝ := unitIntervalGridSample B n m
  let Y : ℕ → Ω → ℝ := fun j ω ↦ X (j + 1) ω - X j ω
  have hW : IsBrownianMotion μ W := brownianShift_sub hB (n : NNReal)
  have hX0 : X 0 = 0 := by
    -- Proof comment: the sampled shifted path starts from the shifted origin.
    funext ω
    simp [X, unitIntervalGridSample]
  have hX_meas : ∀ k, Measurable (X k) := by
    intro k
    simpa [W, X, unitIntervalGridSample] using
      (hW.stronglyMeasurable ((k : NNReal) / (m + 1))).measurable
  have hY_meas : ∀ j, Measurable (Y j) := by
    intro j
    exact (hX_meas (j + 1)).sub (hX_meas j)
  have hY_law :
      ∀ j, HasLaw (Y j) (gaussianReal 0 (((m + 1 : ℕ) : NNReal)⁻¹)) μ := by
    intro j
    have hst :
        ((j : ℕ) : NNReal) / (m + 1) ≤ ((j + 1 : ℕ) : NNReal) / (m + 1) := by
      gcongr
      exact_mod_cast Nat.le_succ j
    have hgap :
        ((j + 1 : ℕ) : NNReal) / (m + 1) - ((j : ℕ) : NNReal) / (m + 1) =
          (((m + 1 : ℕ) : NNReal)⁻¹) := by
      -- Proof comment: consecutive mesh points differ by exactly one mesh step.
      refine tsub_eq_of_eq_add ?_
      rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      ring
    have hLaw := brownianIncrement_hasLaw (hB := hW) hst
    rw [hgap] at hLaw
    simpa [W, X, Y, unitIntervalGridSample, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hLaw
  have hY_int : ∀ j, Integrable (Y j) μ := by
    intro j
    exact (hY_law j).hasGaussianLaw.integrable
  have hY_mean_zero : ∀ j, μ[Y j] = 0 := by
    intro j
    simpa using (hY_law j).integral_eq
  let τ : ℕ → NNReal := fun j ↦ (j : NNReal) / (m + 1)
  have hτmono : Monotone τ := by
    intro a b hab
    dsimp [τ]
    gcongr
  have hY_indep : iIndepFun Y μ := by
    -- Proof comment: the mesh increments are Brownian increments along a monotone deterministic
    -- time sequence, so they are independent.
    simpa [W, X, Y, τ, unitIntervalGridSample] using hW.indepIncrements.nat (t := τ) hτmono
  have hMart :
      Martingale (partialSum Y)
        (Filtration.natural (partialSum Y)
          (fun k ↦ (partialSum_measurable Y hY_meas k).stronglyMeasurable)) μ := by
    -- Proof comment: centered independent increments make the sampled partial sums a martingale in
    -- their natural filtration.
    exact independentCenteredPartialSums_martingale
      (Y := Y) (μ := μ) (hY_meas := hY_meas) hY_int hY_mean_zero hY_indep
  have hGridEq :
      gridBadEvent B n m =
        {ω | Real.sqrt (n + 1 : ℝ) ≤ absMaxUpTo(partialSum Y, m + 1, ω)} := by
    ext ω
    simp [gridBadEvent, X, Y, partialSum_diff_eq (X := X) hX0]
  have hTerminalLaw : HasLaw (partialSum Y (m + 1)) (gaussianReal 0 1) μ := by
    have hOnePos : 0 < (1 : NNReal) := by positivity
    have hLawW1 : HasLaw (W 1) (gaussianReal 0 1) μ := hW.gaussian_marginal hOnePos
    have hLawX : HasLaw (X (m + 1)) (gaussianReal 0 1) μ := by
      have hEqX : X (m + 1) = W 1 := by
        funext ω
        simp [W, X, unitIntervalGridSample]
      exact hLawW1.congr (Filter.EventuallyEq.of_eq hEqX)
    have hEq : partialSum Y (m + 1) = X (m + 1) := by
      funext ω
      simpa [Y] using (partialSum_diff_eq (X := X) hX0 (m + 1) ω)
    exact hLawX.congr (Filter.EventuallyEq.of_eq hEq)
  have hMoment :
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |partialSum Y (m + 1) ω| 4) ∂μ =
        standardGaussianFourthMoment := by
    -- Proof comment: the terminal sampled sum is exactly a standard Gaussian increment.
    have hPowMeas :
        AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (|x| ^ (4 : ℕ))) (gaussianReal 0 1) := by
      exact ((measurable_abs.pow_const 4).ennreal_ofReal).aemeasurable
    simpa [standardGaussianFourthMoment, Function.comp, Real.rpow_natCast] using
      hTerminalLaw.lintegral_comp
        hPowMeas
  have hThresholdPos : 0 < Real.sqrt (n + 1 : ℝ) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hDoob :
      ENNReal.ofReal (Real.rpow (Real.sqrt (n + 1 : ℝ)) 4) * μ (gridBadEvent B n m) ≤
        standardGaussianFourthMoment := by
    -- Proof comment: after identifying the sampled bad event with Doob's running-maximum event,
    -- the discrete `L⁴` maximal inequality reduces it to the terminal fourth moment.
    have hpFour : (1 : ℝ) ≤ 4 := by
      norm_num
    have hDoobBase :=
      doobLpTailBoundOfMartingale
        (μ := μ)
        (ℱ := Filtration.natural (partialSum Y)
          (fun k ↦ (partialSum_measurable Y hY_meas k).stronglyMeasurable))
        (X := partialSum Y)
        hMart
        (p := 4)
        (threshold := Real.sqrt (n + 1 : ℝ))
        hpFour
        hThresholdPos
        (m + 1)
    have hDoobSet :
        ENNReal.ofReal (Real.rpow (Real.sqrt (n + 1 : ℝ)) 4) * μ (gridBadEvent B n m) ≤
          ∫⁻ ω, ENNReal.ofReal (Real.rpow |partialSum Y (m + 1) ω| 4) ∂μ := by
      simpa [hGridEq] using hDoobBase
    exact hDoobSet.trans_eq hMoment
  have hPowEq :
      Real.rpow (Real.sqrt (n + 1 : ℝ)) 4 = ((n + 1 : ℝ) ^ (2 : ℕ)) := by
    have hn : 0 ≤ (n + 1 : ℝ) := by positivity
    have hsq : (Real.sqrt (n + 1 : ℝ)) ^ (2 : ℕ) = n + 1 := by
      simpa [pow_two] using Real.sq_sqrt hn
    calc
      Real.rpow (Real.sqrt (n + 1 : ℝ)) 4 = (Real.sqrt (n + 1 : ℝ)) ^ (4 : ℕ) := by
        exact Real.rpow_natCast (Real.sqrt (n + 1 : ℝ)) 4
      _ = ((Real.sqrt (n + 1 : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ) := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ = ((n + 1 : ℝ) ^ (2 : ℕ)) := by rw [hsq]
  let a : ℝ≥0∞ := ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ)))
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    simp
  have ha_inv :
      a⁻¹ = ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
    dsimp [a]
    rw [← ENNReal.ofReal_inv_of_pos]
    positivity
  have hDoob' : a * μ (gridBadEvent B n m) ≤ standardGaussianFourthMoment := by
    dsimp [a]
    rw [← hPowEq]
    exact hDoob
  calc
    μ (gridBadEvent B n m) = a⁻¹ * (a * μ (gridBadEvent B n m)) := by
      simpa [mul_assoc] using
        (ENNReal.inv_mul_cancel_left
          (a := a) (b := μ (gridBadEvent B n m)) ha0 ha_top).symm
    _ ≤ a⁻¹ * standardGaussianFourthMoment := by
      gcongr
    _ = standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
      rw [ha_inv, mul_comm]

/-- Helper for Theorem 21.14: the original continuum bad event inherits the same
`O((n + 1)⁻²)` measure bound as the sampled mesh events. -/
private lemma unitIntervalSqrtIncrementEvent_measure_le_invSq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    (n : ℕ) :
    μ (unitIntervalSqrtIncrementEvent B n) ≤
      standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
  let W : NNReal → Ω → ℝ := fun t ω ↦ B ((n : NNReal) + t) ω - B (n : NNReal) ω
  have hW : IsBrownianMotion μ W := brownianShift_sub hB (n : NNReal)
  let C : Set Ω := {ω | Continuous (fun u : NNReal ↦ W u ω)}
  have hC_ae : C =ᵐ[μ] Set.univ := by
    -- Proof comment: every shifted Brownian path is almost surely continuous on the full half-line.
    simpa [C, HasAlmostSurelyContinuousPaths, processPath, W] using hW.continuous_paths
  have hC_mem_ae : ∀ᵐ ω ∂μ, ω ∈ C := by
    filter_upwards [hC_ae] with ω hω
    exact hω.mpr trivial
  have hAeEq :
      unitIntervalSqrtIncrementEvent B n =ᵐ[μ]
        Set.inter (unitIntervalSqrtIncrementEvent B n) C := by
    filter_upwards [hC_mem_ae] with ω hωC
    by_cases hA : ω ∈ unitIntervalSqrtIncrementEvent B n
    · exact propext ⟨fun _ ↦ ⟨hA, hωC⟩, fun _ ↦ hA⟩
    · exact propext ⟨fun h' ↦ (hA h').elim, fun h' ↦ (hA h'.1).elim⟩
  have hSubset :
      Set.inter (unitIntervalSqrtIncrementEvent B n) C ⊆
        Filter.liminf (fun m : ℕ ↦ gridBadEvent B n m) atTop := by
    intro ω hω
    exact unitIntervalSqrtIncrementEvent_mem_liminf_gridBadEvent
      (B := B) n hω.2 hω.1
  have hLiminf :
      μ (Filter.liminf (fun m : ℕ ↦ gridBadEvent B n m) atTop) ≤
        standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
    calc
      μ (Filter.liminf (fun m : ℕ ↦ gridBadEvent B n m) atTop)
          ≤ Filter.liminf (fun m : ℕ ↦ μ (gridBadEvent B n m)) atTop :=
            measure_liminf_le_liminf_measure (μ := μ) (fun m ↦ gridBadEvent B n m)
      _ ≤ Filter.liminf
            (fun _ : ℕ ↦
              standardGaussianFourthMoment *
                ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) atTop := by
            exact Filter.liminf_le_liminf <|
              Eventually.of_forall fun m ↦ gridBadEvent_measure_le_invSq hB n m
      _ = standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
            simp
  calc
    μ (unitIntervalSqrtIncrementEvent B n)
        = μ (Set.inter (unitIntervalSqrtIncrementEvent B n) C) := MeasureTheory.measure_congr hAeEq
    _ ≤ μ (Filter.liminf (fun m : ℕ ↦ gridBadEvent B n m) atTop) := measure_mono hSubset
    _ ≤ standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := hLiminf

/-- Helper for Theorem 21.14: on the punctured neighborhood of `0`, the time-inversion branch
can be rewritten as the quotient `f (t⁻¹) / (t⁻¹)`. -/
private lemma timeInversionPath_eventuallyEq_divOnPunctured
    {f : NNReal → ℝ} :
    (fun t : NNReal ↦ if t = 0 then 0 else (t : ℝ) * f (t⁻¹))
      =ᶠ[nhdsWithin (0 : NNReal) ({0}ᶜ)]
        fun t : NNReal ↦ f (t⁻¹) / ((t⁻¹ : NNReal) : ℝ) := by
  -- Proof comment: inside the punctured filter, every point is nonzero, so `t = (t⁻¹)⁻¹`
  -- turns multiplication by `t` into division by `t⁻¹`.
  refine Filter.mem_of_superset self_mem_nhdsWithin ?_
  intro x hx
  have hx0 : x ≠ 0 := by
    simpa [Set.mem_compl_iff] using hx
  simp [hx0, div_eq_mul_inv, mul_comm]

/-- Helper for Theorem 21.14: the large unit-interval increment events form a summable family. -/
private lemma unitIntervalSqrtIncrementEvent_tsum_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    (∑' n : ℕ, μ (unitIntervalSqrtIncrementEvent B n)) ≠ ⊤ := by
  -- Route correction: avoid the later Chapter 21 reflection-principle import. The intended local
  -- route is to sample the shifted Brownian path `t ↦ B (n + t) - B n` on the regular mesh
  -- `k / (m + 1)`, apply the discrete partial-sum martingale plus `doobLp_tail_bound` with
  -- exponent `4`, use continuity together with `MeasureTheory.upperStepTime` to show that a strict
  -- unit-interval exceedance belongs to the liminf of the mesh events, and then compare the
  -- resulting uniform `C / (n + 1)^2` bound with the summable p-series.
  have hSeries :
      Summable (fun n : ℕ ↦ (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) := by
    -- Proof comment: the reciprocal-square p-series is summable.
    simpa [one_div] using ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num))
  have hDominated :
      (∑' n : ℕ,
        standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹)) ≠ ⊤ := by
    -- Proof comment: the majorant series is a finite constant times the reciprocal-square series.
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (standardGaussianFourthMoment_ne_top) hSeries.tsum_ofReal_ne_top
  have hCompare :
      (∑' n : ℕ, μ (unitIntervalSqrtIncrementEvent B n)) ≤
        ∑' n : ℕ,
          standardGaussianFourthMoment * ENNReal.ofReal (((n + 1 : ℝ) ^ (2 : ℕ))⁻¹) := by
    -- Proof comment: compare termwise with the discrete Doob majorant from the previous helper.
    refine ENNReal.tsum_le_tsum ?_
    intro n
    exact unitIntervalSqrtIncrementEvent_measure_le_invSq hB n
  exact ne_top_of_le_ne_top hDominated hCompare

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 21.14: once the `n`-th unit interval oscillation is bounded by
`√(n + 1)`, the Brownian quotient at any time in that interval is controlled by the next integer
skeleton value and the reciprocal square-root error term. -/
private lemma brownianDiv_floorBound
    {B : NNReal → Ω → ℝ} {ω : Ω} {s : NNReal} {n : ℕ}
    (hn : n = Nat.floor (s : ℝ))
    (hs : (1 : NNReal) ≤ s)
    (hOsc :
      |B s ω - B (n : NNReal) ω| ≤ Real.sqrt (n + 1 : ℝ))
    (hStep :
      |B ((n + 1 : ℕ) : NNReal) ω - B (n : NNReal) ω| ≤ Real.sqrt (n + 1 : ℝ)) :
    |B s ω| / (s : ℝ) ≤
      2 * (|B ((n + 1 : ℕ) : NNReal) ω| / (n + 1 : ℝ)) +
        4 * (Real.sqrt (n + 1 : ℝ))⁻¹ := by
  subst hn
  have hs_pos : 0 < (s : ℝ) := by
    have hs_pos_nn : (0 : NNReal) < s := lt_of_lt_of_le (by positivity) hs
    exact_mod_cast hs_pos_nn
  have hfloor_le : (Nat.floor (s : ℝ) : ℝ) ≤ (s : ℝ) := Nat.floor_le s.2
  have hInterval :
      (Nat.floor (s : ℝ) + 1 : ℝ) ≤ 2 * (s : ℝ) := by
    linarith [(Nat.floor (s : ℝ) : ℝ) ≤ s, hs]
  have hInv :
      (1 : ℝ) / (s : ℝ) ≤ 2 / (Nat.floor (s : ℝ) + 1 : ℝ) := by
    have hHalf :
        (Nat.floor (s : ℝ) + 1 : ℝ) / 2 ≤ (s : ℝ) := by
      linarith
    have hHalf_pos : 0 < (Nat.floor (s : ℝ) + 1 : ℝ) / 2 := by
      positivity
    have hOneDiv :
      (1 : ℝ) / (s : ℝ) ≤ 1 / ((Nat.floor (s : ℝ) + 1 : ℝ) / 2) :=
      one_div_le_one_div_of_le hHalf_pos hHalf
    calc
      (1 : ℝ) / (s : ℝ) ≤ 1 / ((Nat.floor (s : ℝ) + 1 : ℝ) / 2) := hOneDiv
      _ = 2 / (Nat.floor (s : ℝ) + 1 : ℝ) := by
            have hden_ne : (Nat.floor (s : ℝ) + 1 : ℝ) ≠ 0 := by positivity
            field_simp [hden_ne]
  have hCurrent :
      |B s ω| ≤ |B (Nat.floor (s : ℝ) : NNReal) ω| +
        |B s ω - B (Nat.floor (s : ℝ) : NNReal) ω| := by
    -- Proof comment: decompose `B s` into the left endpoint value plus the within-interval
    -- increment and apply the triangle inequality.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Real.norm_eq_abs] using
      (norm_add_le (B (Nat.floor (s : ℝ) : NNReal) ω)
        (B s ω - B (Nat.floor (s : ℝ) : NNReal) ω))
  have hFloor :
      |B (Nat.floor (s : ℝ) : NNReal) ω| ≤
        |B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
          |B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω -
            B (Nat.floor (s : ℝ) : NNReal) ω| := by
    -- Proof comment: rewrite the left endpoint as the next integer value minus the one-step
    -- increment, then apply the triangle inequality again.
    simpa [Real.norm_eq_abs] using
      (norm_sub_le
        (B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω)
        (B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω -
          B (Nat.floor (s : ℝ) : NNReal) ω))
  have hAbs :
      |B s ω| ≤
        |B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
          2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ) := by
    -- Proof comment: combine the left-endpoint bound with the two `√(n + 1)` oscillation bounds.
    linarith
  have hMain :
      |B s ω| / (s : ℝ) ≤
        (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
            2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ)) *
          (2 / (Nat.floor (s : ℝ) + 1 : ℝ)) := by
    -- Proof comment: compare the denominator `s` with the enclosing integer scale
    -- `Nat.floor s + 1`.
    have hScaleNonneg :
        0 ≤ |B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
          2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ) := by
      positivity
    calc
      |B s ω| / (s : ℝ) = |B s ω| * ((s : ℝ)⁻¹) := by
        rw [div_eq_mul_inv]
      _ ≤ (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
            2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ)) * ((s : ℝ)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hAbs (by positivity)
      _ ≤ (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
            2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ)) *
            (2 / (Nat.floor (s : ℝ) + 1 : ℝ)) := by
            simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hInv hScaleNonneg
  calc
    |B s ω| / (s : ℝ) ≤
        (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
            2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ)) *
          (2 / (Nat.floor (s : ℝ) + 1 : ℝ)) := hMain
    _ = 2 * (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| /
          (Nat.floor (s : ℝ) + 1 : ℝ)) +
        4 * (Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ))⁻¹ := by
          let c : ℝ := Nat.floor (s : ℝ) + 1
          have hc_pos : 0 < c := by
            dsimp [c]
            positivity
          have hc_nonneg : 0 ≤ c := hc_pos.le
          have hc_ne : c ≠ 0 := hc_pos.ne'
          calc
            (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| +
                2 * Real.sqrt (Nat.floor (s : ℝ) + 1 : ℝ)) *
                (2 / (Nat.floor (s : ℝ) + 1 : ℝ))
                = |B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| * (2 / c) +
                    2 * Real.sqrt c * (2 / c) := by
                      dsimp [c]
                      ring
            _ = 2 * (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| / c) +
                  4 * (Real.sqrt c / c) := by
                    field_simp [hc_ne]
                    ring
            _ = 2 * (|B ((Nat.floor (s : ℝ) + 1 : ℕ) : NNReal) ω| / c) +
                  4 * (Real.sqrt c)⁻¹ := by
                    have hSqrtPos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
                    rw [show c = (Real.sqrt c) ^ 2 by
                      nlinarith [Real.sq_sqrt hc_nonneg], pow_two]
                    field_simp [hSqrtPos.ne']
                    rw [Real.sqrt_sq_eq_abs, abs_of_pos hSqrtPos]
                    ring

/-- Helper for Theorem 21.14: Brownian paths are almost surely sublinear at infinity. -/
lemma brownian_div_tendsto_zero_atTop_ae
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, Tendsto (fun s : NNReal ↦ B s ω / (s : ℝ)) atTop (nhds 0) :=
  by
  have hInteger :
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ B ((n + 1 : ℕ) : NNReal) ω / (n + 1 : ℝ)) atTop (nhds 0) :=
    brownianIntegerSkeleton_div_tendsto_zero_ae hB
  have hBad :
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ unitIntervalSqrtIncrementEvent B n := by
    simpa using
      (MeasureTheory.ae_eventually_notMem
        (μ := μ) (s := unitIntervalSqrtIncrementEvent B)
        (unitIntervalSqrtIncrementEvent_tsum_ne_top hB))
  have hInvSqrt :
      Tendsto (fun n : ℕ ↦ 4 * (Real.sqrt (n + 1 : ℝ))⁻¹) atTop (nhds 0) := by
    have hSqrt :
        Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℝ)) atTop atTop := by
      have hCastSucc :
          Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
        have hComp :
            (fun n : ℕ ↦ (n + 1 : ℝ)) = (fun n : ℕ ↦ (n : ℝ)) ∘ fun n : ℕ ↦ n + 1 := by
          funext n
          simp [Function.comp]
        rw [hComp]
        exact
          (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).comp
            (tendsto_add_atTop_nat 1)
      exact Real.tendsto_sqrt_atTop.comp hCastSucc
    have hInv :
        Tendsto (fun n : ℕ ↦ (Real.sqrt (n + 1 : ℝ))⁻¹) atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hSqrt
    simpa [mul_comm] using (tendsto_const_nhds.mul hInv)
  -- Proof comment: after first Borel-Cantelli, only finitely many unit intervals contain an
  -- increment larger than `√(n + 1)`, so on the almost-sure good event the floor decomposition
  -- `s = ⌊s⌋ + (s - ⌊s⌋)` gives
  -- `|B s| / s ≤ 2 * |B ⌊s⌋| / (⌊s⌋ + 1) + 2 / √(⌊s⌋ + 1)` for large `s`.
  -- The integer-skeleton strong law and the deterministic denominator comparison then force the
  -- full Brownian quotient to converge to `0`.
  filter_upwards [hInteger, hBad] with ω hωInteger hωBad
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨NInteger, hNInteger⟩ := Metric.tendsto_atTop.1 hωInteger (ε / 4) (by positivity)
  obtain ⟨NInvSqrt, hNInvSqrt⟩ := Metric.tendsto_atTop.1 hInvSqrt (ε / 2) (by positivity)
  rcases Filter.eventually_atTop.1 hωBad with ⟨NBad, hNBad⟩
  let N : ℕ := max 1 (max NBad (max NInteger NInvSqrt))
  refine ⟨(N + 1 : ℕ), ?_⟩
  intro s hs
  let n : ℕ := Nat.floor (s : ℝ)
  have hN_ge_one : 1 ≤ N := by
    simp [N]
  have hs_one : (1 : NNReal) ≤ s := by
    have hNatSucc : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    exact le_trans (show (1 : NNReal) ≤ (N + 1 : ℕ) by exact_mod_cast hNatSucc) hs
  have hN_le_n : N ≤ n := by
    apply Nat.le_floor
    exact_mod_cast
      (le_trans (show (N : NNReal) ≤ (N + 1 : ℕ) by exact_mod_cast Nat.le_succ N) hs)
  have hBad_n : ω ∉ unitIntervalSqrtIncrementEvent B n :=
    hNBad n (le_trans (by simp [N]) hN_le_n)
  have hOsc :
      |B s ω - B (n : NNReal) ω| ≤ Real.sqrt (n + 1 : ℝ) := by
    by_contra hgt
    apply hBad_n
    have hn_le_s : (n : NNReal) ≤ s := by
      exact_mod_cast Nat.floor_le s.2
    have hs_le :
          s ≤ ((n + 1 : ℕ) : NNReal) := by
        exact_mod_cast (Nat.lt_floor_add_one (s : ℝ)).le
    refine ⟨s - n, ?_, ?_⟩
    · constructor
      · exact zero_le _
      · refine NNReal.coe_le_coe.mp ?_
        rw [NNReal.coe_sub hn_le_s]
        have hn_real : (n : ℝ) ≤ s := by
          exact_mod_cast hn_le_s
        have hs_real : (s : ℝ) ≤ (n : ℝ) + 1 := by
          exact_mod_cast hs_le
        have hSubReal : (s : ℝ) - (n : ℝ) ≤ 1 := by
          linarith
        simpa using hSubReal
    simpa [unitIntervalSqrtIncrementEvent, add_tsub_cancel_of_le hn_le_s]
      using hgt
  have hStep :
      |B ((n + 1 : ℕ) : NNReal) ω - B (n : NNReal) ω| ≤ Real.sqrt (n + 1 : ℝ) := by
    by_contra hgt
    apply hBad_n
    refine ⟨1, by simp, ?_⟩
    simpa [unitIntervalSqrtIncrementEvent, Nat.cast_add, add_assoc] using hgt
  have hFloorBound :=
    brownianDiv_floorBound (B := B) (ω := ω) (s := s) (n := n) rfl hs_one hOsc hStep
  have hIntegerSmall :
      |B ((n + 1 : ℕ) : NNReal) ω| / (n + 1 : ℝ) < ε / 4 := by
    have := hNInteger n (le_trans (by simp [N]) hN_le_n)
    have hDenPos : 0 < (n + 1 : ℝ) := by positivity
    simpa [Real.dist_eq, abs_div, abs_of_pos hDenPos] using this
  have hInvSqrtSmall :
      4 * (Real.sqrt (n + 1 : ℝ))⁻¹ < ε / 2 := by
    have := hNInvSqrt n (le_trans (by simp [N]) hN_le_n)
    have hSqrtPos : 0 < Real.sqrt (n + 1 : ℝ) := by
      exact Real.sqrt_pos.mpr (by positivity)
    simpa [Real.dist_eq, abs_of_pos hSqrtPos] using this
  have hAbsSmall : |B s ω| / (s : ℝ) < ε := by
    linarith
  have hs_pos : 0 < (s : ℝ) := by
    have hs_pos_nn : (0 : NNReal) < s := lt_of_lt_of_le (by positivity) hs_one
    exact_mod_cast hs_pos_nn
  simpa [Real.dist_eq, abs_div, abs_of_pos hs_pos] using hAbsSmall

/-- Helper for Theorem 21.14: sublinear growth at infinity turns into continuity of the inverted
path at `0`. -/
lemma continuous_timeInversionPath_of_continuous_of_tendsto_div_atTop
    {f : NNReal → ℝ} (hf : Continuous f)
    (hsub : Tendsto (fun s : NNReal ↦ f s / (s : ℝ)) atTop (nhds 0)) :
    Continuous (fun t : NNReal ↦ if t = 0 then 0 else (t : ℝ) * f (t⁻¹)) :=
  by
  -- Route correction: rewrite the positive branch as `f (t⁻¹) / (t⁻¹)` so the continuity at `0`
  -- is a direct transport of the `atTop` limit through inversion.
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    have hPunctured :
        nhdsWithin (0 : NNReal) ({0}ᶜ) = nhdsWithin (0 : NNReal) (Set.Ioi (0 : NNReal)) := by
      change nhdsWithin (0 : NNReal) ({0} : Set NNReal)ᶜ =
        nhdsWithin (0 : NNReal) (Set.Ioi (0 : NNReal))
      congr 1
      ext x
      simp [pos_iff_ne_zero]
    have hRewrite :
        (fun t : NNReal ↦ if t = 0 then 0 else (t : ℝ) * f (t⁻¹))
          =ᶠ[nhdsWithin (0 : NNReal) ({0}ᶜ)]
            fun t : NNReal ↦ f (t⁻¹) / ((t⁻¹ : NNReal) : ℝ) := by
      exact timeInversionPath_eventuallyEq_divOnPunctured (f := f)
    have hInv :
        Tendsto (fun x : NNReal ↦ x⁻¹) (nhdsWithin (0 : NNReal) ({0}ᶜ)) atTop := by
      rw [hPunctured]
      simpa using (tendsto_inv_nhdsGT_zero : Tendsto (fun x : NNReal ↦ x⁻¹)
        (nhdsWithin (0 : NNReal) (Set.Ioi (0 : NNReal))) atTop)
    -- Proof comment: after the branch rewrite, continuity at `0` is exactly the prescribed
    -- sublinear-decay limit composed with inversion.
    refine continuousAt_iff_punctured_nhds.2 ?_
    simpa using Filter.Tendsto.congr' hRewrite.symm (hsub.comp hInv)
  · have hInv : ContinuousAt (fun x : NNReal ↦ x⁻¹) t :=
      (continuousOn_inv₀.continuousAt (by simpa using ht))
    have hCore : ContinuousAt (fun x : NNReal ↦ (x : ℝ) * f (x⁻¹)) t :=
      NNReal.continuous_coe.continuousAt.mul (hf.continuousAt.comp hInv)
    have hRewrite :
        (fun x : NNReal ↦ if x = 0 then 0 else (x : ℝ) * f (x⁻¹))
          =ᶠ[nhds t] fun x : NNReal ↦ (x : ℝ) * f (x⁻¹) := by
      have hAwayFromZero : ({0}ᶜ : Set NNReal) ∈ nhds t :=
        IsOpen.mem_nhds isOpen_compl_singleton (by simpa [Set.mem_compl_iff] using ht)
      refine Filter.mem_of_superset hAwayFromZero ?_
      intro x hx
      have hx0 : x ≠ 0 := by
        simpa [Set.mem_compl_iff] using hx
      simp [hx0]
    -- Proof comment: away from `0`, the `if` branch is locally constant and the core expression
    -- is a product of continuous factors.
    exact hCore.congr_of_eventuallyEq hRewrite

/-- Helper for Theorem 21.14: the time-inverted Brownian motion has almost surely continuous
sample paths. -/
lemma timeInversion_hasAlmostSurelyContinuousPaths
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    HasAlmostSurelyContinuousPaths μ (ProbabilityTheory.timeInversion B) := by
  -- Proof comment: combine almost-sure continuity of Brownian paths with the sublinear-growth
  -- estimate, then apply the deterministic continuity transport lemma samplewise.
  filter_upwards [hB.continuous_paths, brownian_div_tendsto_zero_atTop_ae hB] with ω hcont hsub
  simpa [HasAlmostSurelyContinuousPaths, processPath, ProbabilityTheory.timeInversion] using
    continuous_timeInversionPath_of_continuous_of_tendsto_div_atTop
      (f := fun s ↦ B s ω) hcont hsub

-- Proof sketch: view `timeInversion B` as a centered Gaussian process with covariance
-- kernel `s ⊓ t`, using the Brownian-motion characterization from Theorem 21.11. Continuity away
-- from `0` is immediate from continuity of `B`, and continuity at `0` follows from the large-time
-- asymptotics of `t⁻¹ • B t` together with the reflection-principle estimate from the textbook.
/-- Theorem 21.14: if `B` is a Brownian motion, then the process
`X_t = t B_{1 / t}` for `t > 0` and `X_0 = 0` is again a Brownian motion. -/
theorem timeInversion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    IsBrownianMotion μ (ProbabilityTheory.timeInversion B) := by
  -- Proof comment: invoke the Brownian characterization by centered Gaussianity, covariance, and
  -- almost sure continuity, then discharge each field with the dedicated helper lemmas above.
  rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
  refine ⟨?_, timeInversion_isGaussianProcess hB, timeInversion_mean_zero hB,
    timeInversion_covariance_eq hB, timeInversion_hasAlmostSurelyContinuousPaths hB⟩
  -- Proof comment: the defining branch at time `0` is the constant value `0`.
  funext ω
  simp [ProbabilityTheory.timeInversion]

end IsBrownianMotion

end ProbabilityTheory

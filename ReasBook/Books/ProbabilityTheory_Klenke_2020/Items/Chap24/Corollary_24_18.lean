/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_12Core
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Example_24_19.LaplaceCore

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.FiniteMeasure
open scoped MeasureTheory ENNReal Topology

noncomputable section

namespace MeasureTheory.FiniteMeasure

/-- Helper for Corollary 24.18: the log-Laplace transform of a probability measure on `[0, ∞)`. -/
def logLaplaceTransform (μ : ProbabilityMeasure NNReal) (t : NNReal) : ℝ :=
  -Real.log (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal))

/-- Helper for Corollary 24.18: the subordinator Lévy--Khinchin representation predicate on
`[0, ∞)`. -/
def HasSubordinatorLevyKhinchinRepresentation
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal) : Prop :=
  ν {0} = 0 ∧
    Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν ∧
    ∀ t : NNReal,
      logLaplaceTransform μ t =
        ((α : ℝ) * (t : ℝ)) +
          ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν

end MeasureTheory.FiniteMeasure

namespace MeasureTheory.ProbabilityMeasure

/-- The stochastic order on probability laws on `[0, ∞)` tested against bounded measurable
increasing real-valued functions. -/
def NNRealStochasticLE (μ₁ μ₂ : ProbabilityMeasure NNReal) : Prop :=
  ∀ ⦃f : NNReal → ℝ⦄, Monotone f →
    Bornology.IsBounded (Set.range f) →
    Measurable f →
    ∫ x, f x ∂(μ₁ : Measure NNReal) ≤ ∫ x, f x ∂(μ₂ : Measure NNReal)

-- Proof sketch: for every admissible increasing test function `f`, both sides of the defining
-- inequality are the same integral when the two laws coincide.
/-- The stochastic order on `[0, ∞)` is reflexive. -/
theorem nnrealStochasticLE_refl (μ : ProbabilityMeasure NNReal) :
    NNRealStochasticLE μ μ := by
  intro f _ _ _
  -- Proof comment: both sides are the same integral against the same law.
  exact le_rfl

/-- Helper for Corollary 24.18: Lebesgue measure on `[0, ∞)` transported to `NNReal`. -/
private def nnrealLebesgue : Measure NNReal :=
  Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Helper for Corollary 24.18: the basic Poisson-exponential kernel is bounded by
`x ↦ min (1, x)` on `[0, ∞)`. -/
private lemma one_sub_expNeg_le_min_one (x : ℝ) :
    1 - Real.exp (-x) ≤ min 1 x := by
  -- Proof comment: the tangent-line estimate gives the `≤ x` half.
  have hx_le : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  -- Proof comment: positivity of the exponential gives the uniform `≤ 1` half.
  have h_one : 1 - Real.exp (-x) ≤ 1 := by
    have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
    linarith
  exact le_min h_one hx_le

/-- Helper for Corollary 24.18: the small scales `(n + 1)⁻¹` used in the Laplace limit
argument. -/
private def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Corollary 24.18: the kernel `t ↦ exp (-t)` on `ℝ≥0∞`, extended by `0` at `∞`. -/
private def ennrealExpNeg (t : ℝ≥0∞) : ℝ :=
  if t = ⊤ then 0 else Real.exp (-t.toReal)

/-- Helper for Corollary 24.18: away from `⊤`, `ennrealExpNeg` is the ordinary exponential
kernel. -/
private lemma ennrealExpNeg_of_ne_top {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    ennrealExpNeg t = Real.exp (-t.toReal) := by
  -- Proof comment: on the finite branch, the definition unfolds directly.
  simp [ennrealExpNeg, ht]

/-- Helper for Corollary 24.18: `ennrealExpNeg` is measurable on `ℝ≥0∞`. -/
private lemma measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) := by
    fun_prop
  -- Proof comment: rewrite `ennrealExpNeg` as a piecewise finite exponential.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (∞ : ℝ≥0∞)) hcore)

/-- Helper for Corollary 24.18: `ennrealExpNeg` is pointwise nonnegative. -/
private lemma ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ∞
  · -- Proof comment: at `∞` the kernel is exactly `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: away from `∞`, the kernel is an ordinary exponential.
    simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Corollary 24.18: `ennrealExpNeg` is bounded above by `1`. -/
private lemma ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ∞
  · -- Proof comment: the `∞` branch is `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: on finite inputs the exponent is nonpositive.
    have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Corollary 24.18: the small Laplace scales converge pointwise to the finiteness
indicator on `ℝ≥0∞`. -/
private lemma ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ∞ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ∞
  · -- Proof comment: positive scales keep `∞` fixed, so the kernel is constantly `0`.
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
  · -- Proof comment: on finite inputs, continuity of the exponential at `0` gives the limit.
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
          fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal)) := by
      funext n
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ∞ :=
        ENNReal.mul_ne_top (by simp [invSuccScaleReal]) hy
      have hs_nonneg : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
      change Real.exp (-((ENNReal.ofReal (invSuccScaleReal n)).toReal * y.toReal)) = _
      rw [ENNReal.toReal_ofReal hs_nonneg]
    rw [hrewrite]
    simpa [hy] using hexp

/-- Helper for Corollary 24.18: small-scale Laplace expectations converge to the probability of
the finiteness event. -/
private lemma laplaceInvSucc_tendsto_measureFinite
    {β : Type*} [MeasurableSpace β] {μ : Measure β} [IsFiniteMeasure μ] {Y : β → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ∞}).toReal) := by
  let A : Set β := {a | Y a < ∞}
  let G : β → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    exact (measurable_ennrealExpNeg.comp (measurable_const.mul hY)).aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ a ∂μ, ‖ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with a
    have hnonneg : 0 ≤ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) :=
      ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ≤ 1 :=
      ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ a ∂μ, Filter.Tendsto
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a))
        Filter.atTop (nhds (G a)) := by
    filter_upwards with a
    by_cases ha : Y a = ∞
    · simpa [G, A, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · have ha' : Y a < ∞ := lt_top_iff_ne_top.mpr ha
      simpa [G, A, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : β ↦ (1 : ℝ)) hF_meas (integrable_const 1) h_bound h_lim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hG_integral : ∫ a, G a ∂μ = (μ A).toReal := by
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hG_integral] using hDCT

/-- Helper for Corollary 24.18: scaling the Poisson-exponential kernel by `s ≤ 1` preserves the
domination by `x ↦ min (1, x)`. -/
private lemma poissonExpKernel_scale_le_minOne
    (s : ℝ) (hs1 : s ≤ 1) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) := by
  have hmul_le : s * (x : ℝ) ≤ (x : ℝ) := by
    nlinarith [x.2, hs1]
  calc
    1 - Real.exp (-(s * (x : ℝ))) ≤ min 1 (s * (x : ℝ)) := one_sub_expNeg_le_min_one _
    _ ≤ min 1 (x : ℝ) := min_le_min le_rfl hmul_le

/-- Helper for Corollary 24.18: the scaled Poisson-exponential kernel is the `ENNReal` lift of
the ordinary real kernel. -/
private lemma poissonLaplaceKernel_scale_eq_ofReal (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (s * (x : ℝ)))) =
      ENNReal.ofReal (1 - Real.exp (-(s * (x : ℝ)))) := by
  have hmul_nonneg : 0 ≤ s * (x : ℝ) := by
    nlinarith [hs, x.2]
  have hExpNonneg : 0 ≤ Real.exp (-(s * (x : ℝ))) := Real.exp_nonneg _
  simp [ennrealExpNeg, hmul_nonneg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Corollary 24.18: under truncated first-moment integrability, the small Laplace
exponents converge to `0`. -/
private lemma poissonLaplaceExponent_invSucc_tendstoZero
    (ν : Measure NNReal)
    (hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν)
      Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h_meas :
      ∀ n, AEStronglyMeasurable
        (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
    intro n
    have h : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
      fun_prop
    exact h.aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ x : NNReal ∂ν,
        ‖1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))‖ ≤ min (1 : ℝ) (x : ℝ) := by
    intro n
    filter_upwards with x
    have hs1 : invSuccScaleReal n ≤ 1 := by
      have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      have hs0 : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [x.2, hs0]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hle : 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_minOne (invSuccScaleReal n) hs1 x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ x : NNReal ∂ν,
        Filter.Tendsto
          (fun n : ℕ ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) Filter.atTop
          (nhds 0) := by
    filter_upwards with x
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * (x : ℝ)) Filter.atTop
          (nhds (0 * (x : ℝ))) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ 1 - Real.exp (-r)) := by
      simpa using continuous_const.sub (Real.continuous_exp.comp continuous_neg)
    simpa using hcont.continuousAt.tendsto.comp hmul
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) h_meas hInt h_bound h_lim

/-- Helper for Corollary 24.18: for `s ≥ 0`, the scaled Bernstein kernel is dominated by
`max (1, s) * min (1, x)`. -/
private lemma poissonExpKernel_scale_le_maxMulMinOne
    (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
  by_cases hx1 : (x : ℝ) ≤ 1
  · calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ s * (x : ℝ) := by
        refine le_trans (one_sub_expNeg_le_min_one (s * (x : ℝ))) ?_
        exact min_le_right _ _
      _ ≤ max 1 s * (x : ℝ) := by
        nlinarith [le_max_right 1 s, x.2]
      _ = max 1 s * min (1 : ℝ) (x : ℝ) := by
        rw [min_eq_right hx1]
  · have hx1' : 1 ≤ (x : ℝ) := le_of_not_ge hx1
    calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ 1 := by
        have hpos : 0 < Real.exp (-(s * (x : ℝ))) := Real.exp_pos _
        linarith
      _ ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
        simpa [min_eq_left hx1'] using (le_max_left (1 : ℝ) s)

/-- Helper for Corollary 24.18: an almost-sure ordered coupling on a common space yields
`NNRealStochasticLE`. -/
private theorem orderedHasLaw_imp_nnrealStochasticLE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y₁ Y₂ : Ω → NNReal} {μ₁ μ₂ : ProbabilityMeasure NNReal}
    (hY₁ : HasLaw Y₁ (μ₁ : Measure NNReal) P)
    (hY₂ : HasLaw Y₂ (μ₂ : Measure NNReal) P)
    (hOrdered : ∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) :
    NNRealStochasticLE μ₁ μ₂ := by
  letI : IsFiniteMeasure P := hY₁.isFiniteMeasure
  intro f hf_mono hf_bdd hf_meas
  obtain ⟨C, hC⟩ := hf_bdd.subset_closedBall 0
  have hfst_mem_Icc : ∀ ω : Ω, f (Y₁ ω) ∈ Set.Icc (-C) C := by
    intro ω
    have hωBall : f (Y₁ ω) ∈ Metric.closedBall (0 : ℝ) C := hC ⟨Y₁ ω, rfl⟩
    have hωAbs : |f (Y₁ ω)| ≤ C := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hωBall
    simpa [Set.mem_Icc, abs_le] using hωAbs
  have hsnd_mem_Icc : ∀ ω : Ω, f (Y₂ ω) ∈ Set.Icc (-C) C := by
    intro ω
    have hωBall : f (Y₂ ω) ∈ Metric.closedBall (0 : ℝ) C := hC ⟨Y₂ ω, rfl⟩
    have hωAbs : |f (Y₂ ω)| ≤ C := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hωBall
    simpa [Set.mem_Icc, abs_le] using hωAbs
  have hInt₁ : Integrable (fun ω : Ω ↦ f (Y₁ ω)) P := by
    -- Proof comment: bounded range turns the first pulled-back test function into an integrable
    -- random variable on the finite ambient measure `P`.
    refine MeasureTheory.Integrable.of_mem_Icc (-C) C
      (hf_meas.comp_aemeasurable hY₁.aemeasurable) ?_
    exact Filter.Eventually.of_forall hfst_mem_Icc
  have hInt₂ : Integrable (fun ω : Ω ↦ f (Y₂ ω)) P := by
    -- Proof comment: the same bounded-range argument applies to the second marginal.
    refine MeasureTheory.Integrable.of_mem_Icc (-C) C
      (hf_meas.comp_aemeasurable hY₂.aemeasurable) ?_
    exact Filter.Eventually.of_forall hsnd_mem_Icc
  have hPointwise :
      (fun ω : Ω ↦ f (Y₁ ω)) ≤ᵐ[P] fun ω ↦ f (Y₂ ω) := by
    -- Proof comment: monotonicity of `f` pushes the almost-sure order through the coupling.
    filter_upwards [hOrdered] with ω hω
    exact hf_mono hω
  have hEq₁ :
      ∫ x, f x ∂(μ₁ : Measure NNReal) = ∫ ω, f (Y₁ ω) ∂P := by
    simpa [Function.comp] using
      (hY₁.integral_comp hf_meas.aestronglyMeasurable).symm
  have hEq₂ :
      ∫ x, f x ∂(μ₂ : Measure NNReal) = ∫ ω, f (Y₂ ω) ∂P := by
    simpa [Function.comp] using
      (hY₂.integral_comp hf_meas.aestronglyMeasurable).symm
  calc
    ∫ x, f x ∂(μ₁ : Measure NNReal) = ∫ ω, f (Y₁ ω) ∂P := hEq₁
    _ ≤ ∫ ω, f (Y₂ ω) ∂P := MeasureTheory.integral_mono_ae hInt₁ hInt₂ hPointwise
    _ = ∫ x, f x ∂(μ₂ : Measure NNReal) := hEq₂.symm

/-- Helper for Corollary 24.18: the positive tail-sublevel set at level `y` attached to a measure
on `NNReal`. -/
private def positiveTailSublevelSet (ν : Measure NNReal) (y : NNReal) : Set NNReal :=
  {x : NNReal | 0 < x ∧ ν (Set.Ici x) ≤ (y : ℝ≥0∞)}

/-- Helper for Corollary 24.18: every positive tail-sublevel set is bounded below by `0`. -/
private lemma bddBelow_positiveTailSublevelSet
    (ν : Measure NNReal) (y : NNReal) :
    BddBelow (positiveTailSublevelSet ν y) := by
  -- Proof comment: every element of the positive tail-sublevel set is strictly positive, hence in
  -- particular above the lower bound `0`.
  refine ⟨0, ?_⟩
  intro x hx
  exact le_of_lt hx.1

/-- Helper for Corollary 24.18: the positive tail comparison hypothesis turns the `ν₂`
tail-sublevel set at level `y` into a subset of the corresponding `ν₁` sublevel set. -/
private lemma positiveTailSublevelSet_subset_of_tail_le
    {ν₁ ν₂ : Measure NNReal}
    (hν : ∀ x : NNReal, 0 < x → ν₁ (Set.Ici x) ≤ ν₂ (Set.Ici x))
    (y : NNReal) :
    positiveTailSublevelSet ν₂ y ⊆ positiveTailSublevelSet ν₁ y := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  exact (hν x hx.1).trans hx.2

/-- Helper for Corollary 24.18: once the `ν₂` positive tail-sublevel set at level `y` is
nonempty, the corresponding infima are ordered in the direction needed for the eventual coupling
integrands. -/
private lemma csInf_positiveTailSublevelSet_le_of_tail_le
    {ν₁ ν₂ : Measure NNReal}
    (hν : ∀ x : NNReal, 0 < x → ν₁ (Set.Ici x) ≤ ν₂ (Set.Ici x))
    {y : NNReal}
    (hnonempty : Set.Nonempty (positiveTailSublevelSet ν₂ y)) :
    sInf (positiveTailSublevelSet ν₁ y) ≤ sInf (positiveTailSublevelSet ν₂ y) := by
  -- Proof comment: the `ν₂` sublevel set sits inside the `ν₁` sublevel set, so conditional
  -- completeness orders their infima contravariantly.
  exact csInf_le_csInf
    (bddBelow_positiveTailSublevelSet ν₁ y)
    hnonempty
    (positiveTailSublevelSet_subset_of_tail_le hν y)

/-- Helper for Corollary 24.18: every positive level `y` admits a positive point whose `ν`-tail
has already dropped below `y` once `ν` comes from a subordinator Lévy--Khinchin representation. -/
private lemma positiveTailSublevelSet_nonempty_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    {y : NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (hy : 0 < y) :
    Set.Nonempty (positiveTailSublevelSet ν y) := by
  have hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := hrep.2.1
  have hmin_meas :
      AEStronglyMeasurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
    -- Proof comment: the truncation kernel is an ordinary measurable real-valued map on `NNReal`.
    have hmeas : Measurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hmin_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ min (1 : ℝ) (x : ℝ) :=
    Filter.Eventually.of_forall fun x ↦ le_min zero_le_one x.2
  have htail_one_lt_top : ν (Set.Ici (1 : NNReal)) < ∞ := by
    have hlintegral_ne_top :
        ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν ≠ ∞ :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmin_meas hmin_nonneg).2 hInt
    have hlintegral_lt_top :
        ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν < ∞ :=
      lt_top_iff_ne_top.mpr hlintegral_ne_top
    have htail_le :
        ν (Set.Ici (1 : NNReal)) ≤
          ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν := by
      calc
        ν (Set.Ici (1 : NNReal))
            = ∫⁻ x, Set.indicator (Set.Ici (1 : NNReal)) (fun _ ↦ (1 : ℝ≥0∞)) x ∂ν := by
                simpa using
                  (MeasureTheory.lintegral_indicator_one (μ := ν) measurableSet_Ici)
        _ ≤ ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν := by
              refine MeasureTheory.lintegral_mono fun x ↦ ?_
              by_cases hx : x ∈ Set.Ici (1 : NNReal)
              · have hx_one : (1 : ℝ) ≤ (x : ℝ) := by
                  exact_mod_cast hx
                simp [hx, min_eq_left hx_one]
              · simp [hx]
    exact lt_of_le_of_lt htail_le hlintegral_lt_top
  let tails : ℕ → Set NNReal := fun n ↦ Set.Ici ((n + 1 : ℕ) : NNReal)
  have htails_meas : ∀ n : ℕ, NullMeasurableSet (tails n) ν :=
    fun _ ↦ measurableSet_Ici.nullMeasurableSet
  have htails_anti : Antitone tails := by
    intro m n hmn
    exact Set.Ici_subset_Ici.2 <| by exact_mod_cast Nat.succ_le_succ hmn
  have htails_empty : (⋂ n : ℕ, tails n) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    rcases exists_nat_gt x with ⟨n, hn⟩
    have hxn : ((n + 1 : ℕ) : NNReal) ≤ x := by
      exact Set.mem_iInter.mp hx n
    have hn' : x < ((n + 1 : ℕ) : NNReal) := by
      exact lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n)
    exact not_lt_of_ge hxn hn'
  have htail_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ν (tails n)) Filter.atTop (nhds 0) := by
    -- Proof comment: the tails `[(n+1), ∞)` decrease to `∅`, so continuity from above forces
    -- their masses to vanish once we know the first tail has finite mass.
    have htail_tendsto' :
        Filter.Tendsto (fun n : ℕ ↦ ν (tails n)) Filter.atTop
          (nhds (ν (⋂ n : ℕ, tails n))) := by
      simpa [tails] using
        MeasureTheory.tendsto_measure_iInter_atTop htails_meas htails_anti
          ⟨0, by simpa [tails] using htail_one_lt_top.ne⟩
    have hinter_zero : ν (⋂ n : ℕ, tails n) = 0 := by
      simpa [htails_empty]
    simpa [hinter_zero] using htail_tendsto'
  have hy_enn : (0 : ℝ≥0∞) < (y : ℝ≥0∞) := by
    exact_mod_cast hy
  obtain ⟨n, hn⟩ := (htail_tendsto.eventually (Iio_mem_nhds hy_enn)).exists
  refine ⟨((n + 1 : ℕ) : NNReal), ?_⟩
  refine ⟨by positivity, ?_⟩
  exact le_of_lt hn

/-- Helper for Corollary 24.18: integrability of `x ↦ min (1, x)` gives finite mass on the
positive tails `((n + 1)⁻¹, ∞)`. -/
private lemma measure_Ioi_invSucc_lt_top_of_integrableMin
    {ν : Measure NNReal}
    (hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν) (n : ℕ) :
    ν (Set.Ioi (1 / (n + 1 : NNReal))) < ∞ := by
  have hpos : (0 : ℝ) < (1 / (n + 1 : NNReal) : NNReal) := by
    positivity
  have hfinite := hInt.measure_norm_ge_lt_top hpos
  refine lt_of_le_of_lt (measure_mono ?_) hfinite
  intro x hx
  change (1 / (n + 1 : NNReal) : ℝ) ≤ ‖min (1 : ℝ) (x : ℝ)‖
  have hx' : (1 / (n + 1 : NNReal) : ℝ) < (x : ℝ) := hx
  have hle_one_nn : (1 / (n + 1 : NNReal)) ≤ (1 : NNReal) := by
    have htmp : (1 / (n + 1 : NNReal)) ≤ 1 / (1 : NNReal) := by
      refine one_div_le_one_div_of_le (show (0 : NNReal) < 1 by norm_num) ?_
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    simpa using htmp
  have hle_one : (1 / (n + 1 : NNReal) : ℝ) ≤ 1 := by
    exact_mod_cast hle_one_nn
  have hnonneg : 0 ≤ min (1 : ℝ) (x : ℝ) := by
    positivity
  rw [Real.norm_of_nonneg hnonneg]
  exact le_min hle_one hx'.le

/-- Helper for Corollary 24.18: integrability of the truncation kernel forces every positive tail
`ν [x, ∞)` to be finite. -/
private lemma tailIci_lt_top_of_integrableMin
    {ν : Measure NNReal}
    (hInt : Integrable (fun z : NNReal ↦ min (1 : ℝ) (z : ℝ)) ν)
    {x : NNReal} (hx : 0 < x) :
    ν (Set.Ici x) < ∞ := by
  have hx_real : 0 < (x : ℝ) := by
    exact_mod_cast hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx_real
  have hn' : (1 / (n + 1 : NNReal)) < x := by
    exact_mod_cast hn
  have htail_lt_top :
      ν (Set.Ioi (1 / (n + 1 : NNReal))) < ∞ :=
    measure_Ioi_invSucc_lt_top_of_integrableMin hInt n
  refine lt_of_le_of_lt (measure_mono ?_) htail_lt_top
  intro z hz
  exact lt_of_lt_of_le hn' hz

/-- Helper for Corollary 24.18: integrability of the truncation kernel also forces every open
positive tail `ν (x, ∞)` to be finite. -/
private lemma tailIoi_lt_top_of_integrableMin
    {ν : Measure NNReal}
    (hInt : Integrable (fun z : NNReal ↦ min (1 : ℝ) (z : ℝ)) ν)
    {x : NNReal} (hx : 0 < x) :
    ν (Set.Ioi x) < ∞ := by
  -- Proof comment: the open tail is contained in the corresponding closed tail.
  exact lt_of_le_of_lt (measure_mono Set.Ioi_subset_Ici_self)
    (tailIci_lt_top_of_integrableMin hInt hx)

/-- Helper for Corollary 24.18: `nnrealLebesgue` gives the expected length to left-open intervals
of `NNReal`. -/
private lemma nnrealLebesgue_Iio (a : NNReal) :
    nnrealLebesgue (Set.Iio a) = (a : ℝ≥0∞) := by
  have hpreimage :
      Real.toNNReal ⁻¹' Set.Iio a ∩ Set.Ici (0 : ℝ) = Set.Ico (0 : ℝ) a := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_mem, hx_nonneg⟩
      refine ⟨hx_nonneg, ?_⟩
      exact (Real.toNNReal_lt_iff_lt_coe hx_nonneg).1 hx_mem
    · intro hx
      rcases hx with ⟨hx_nonneg, hx_lt⟩
      refine ⟨?_, hx_nonneg⟩
      exact (Real.toNNReal_lt_iff_lt_coe hx_nonneg).2 hx_lt
  -- Proof comment: rewrite the transported interval back to the real interval `[0, a)`.
  rw [nnrealLebesgue, Measure.map_apply measurable_real_toNNReal measurableSet_Iio]
  rw [Measure.restrict_apply (measurable_real_toNNReal measurableSet_Iio), hpreimage,
    Real.volume_Ico]
  simpa using (ENNReal.ofReal_coe_nnreal (p := a))

/-- Helper for Corollary 24.18: `nnrealLebesgue` gives the same length to closed left intervals,
since singleton endpoints have zero mass. -/
private lemma nnrealLebesgue_Iic (a : NNReal) :
    nnrealLebesgue (Set.Iic a) = (a : ℝ≥0∞) := by
  have hpreimage :
      Real.toNNReal ⁻¹' Set.Iic a ∩ Set.Ici (0 : ℝ) = Set.Icc (0 : ℝ) a := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_mem, hx_nonneg⟩
      refine ⟨hx_nonneg, ?_⟩
      exact (Real.toNNReal_le_iff_le_coe).1 hx_mem
    · intro hx
      rcases hx with ⟨hx_nonneg, hx_le⟩
      refine ⟨?_, hx_nonneg⟩
      exact (Real.toNNReal_le_iff_le_coe).2 hx_le
  -- Proof comment: the transported closed interval is the real interval `[0, a]`, whose length
  -- is still `a`.
  rw [nnrealLebesgue, Measure.map_apply measurable_real_toNNReal measurableSet_Iic]
  rw [Measure.restrict_apply (measurable_real_toNNReal measurableSet_Iic), hpreimage,
    Real.volume_Icc]
  simpa using (ENNReal.ofReal_coe_nnreal (p := a))

/-- Helper for Corollary 24.18: removing the null singleton `{0}` does not change the
`nnrealLebesgue`-mass of `(0, a)`. -/
private lemma nnrealLebesgue_Ioo_zero_left (a : NNReal) :
    nnrealLebesgue (Set.Ioo (0 : NNReal) a) = (a : ℝ≥0∞) := by
  by_cases ha : a = 0
  · subst ha
    simp [nnrealLebesgue]
  · have ha_pos : 0 < a := bot_lt_iff_ne_bot.mpr ha
    have hIic_zero : Set.Iic (0 : NNReal) = ({0} : Set NNReal) := by
      ext y
      simp [Set.mem_Iic]
    have hzero : nnrealLebesgue ({0} : Set NNReal) = 0 := by
      simpa [hIic_zero] using nnrealLebesgue_Iic (0 : NNReal)
    have hdisj : Disjoint (Set.Ioo (0 : NNReal) a) ({0} : Set NNReal) := by
      refine Set.disjoint_singleton_right.2 ?_
      simp
    have hunion :
        Set.Ioo (0 : NNReal) a ∪ ({0} : Set NNReal) = Set.Iio a := by
      ext y
      constructor
      · intro hy
        rcases hy with hy | hy
        · exact hy.2
        · have hy0 : y = 0 := by simpa using hy
          simpa [hy0] using ha_pos
      · intro hy
        by_cases hy0 : y = 0
        · exact Or.inr <| by simpa [hy0]
        · have hy_pos : 0 < y := bot_lt_iff_ne_bot.mpr hy0
          exact Or.inl ⟨hy_pos, hy⟩
    calc
      nnrealLebesgue (Set.Ioo (0 : NNReal) a)
          = nnrealLebesgue (Set.Ioo (0 : NNReal) a) + nnrealLebesgue ({0} : Set NNReal) := by
              rw [hzero, add_zero]
      _ = nnrealLebesgue (Set.Ioo (0 : NNReal) a ∪ ({0} : Set NNReal)) := by
            symm
            rw [measure_union hdisj (measurableSet_singleton (x := (0 : NNReal)))]
      _ = nnrealLebesgue (Set.Iio a) := by rw [hunion]
      _ = (a : ℝ≥0∞) := nnrealLebesgue_Iio a

/-- Helper for Corollary 24.18: bounded measurable subsets of `NNReal` have finite
`nnrealLebesgue`-mass. -/
private lemma nnrealLebesgue_lt_top_of_isBounded
    (A : Set NNReal) (_hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    nnrealLebesgue A < ∞ := by
  obtain ⟨R, hR⟩ := hA_bdd.subset_closedBall (0 : NNReal)
  let Rnn : NNReal := Real.toNNReal R
  have hsubset : A ⊆ Set.Iic Rnn := by
    intro x hx
    have hx_closed : x ∈ Metric.closedBall (0 : NNReal) R := hR hx
    have hx_le_R : (x : ℝ) ≤ R := by
      simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg x.2] using hx_closed
    simpa [Rnn] using Real.toNNReal_le_toNNReal hx_le_R
  calc
    nnrealLebesgue A ≤ nnrealLebesgue (Set.Iic Rnn) := measure_mono hsubset
    _ = (Rnn : ℝ≥0∞) := nnrealLebesgue_Iic Rnn
    _ < ∞ := by simp

/-- Helper for Corollary 24.18: the transported Lebesgue measure on `NNReal` is boundedly finite,
so it can serve as the common source intensity for the Poisson coupling. -/
private def nnrealLebesgueBoundedlyFinite : BoundedlyFiniteMeasure NNReal :=
  ⟨nnrealLebesgue, nnrealLebesgue_lt_top_of_isBounded⟩

/-- Helper for Corollary 24.18: the common coupling integrand is the infimum generalized inverse
of the positive tail function, with value `0` at level `0`. -/
private def tailQuantile (ν : Measure NNReal) (y : NNReal) : NNReal :=
  if hy : y = 0 then 0 else sInf (positiveTailSublevelSet ν y)

/-- Helper for Corollary 24.18: if `a ≤ b + (n + 1)⁻¹` for every `n`, then already `a ≤ b`. -/
private lemma le_of_forall_le_add_invSucc
    {a b : NNReal}
    (h : ∀ n : ℕ, a ≤ b + 1 / (n + 1 : NNReal)) :
    a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  have hdiff : 0 < (a : ℝ) - (b : ℝ) := by
    exact sub_pos.mpr <| by exact_mod_cast hba
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdiff
  have hlt_real : (b : ℝ) + 1 / (n + 1 : ℝ) < (a : ℝ) := by
    linarith
  have hlt : b + 1 / (n + 1 : NNReal) < a := by
    exact_mod_cast hlt_real
  exact not_lt_of_ge (h n) hlt

/-- Helper for Corollary 24.18: the closed tails `ν [x + (n + 1)⁻¹, ∞)` increase to the open
tail `ν (x, ∞)` as the cutoff approaches `x` from the right. -/
private lemma tendsto_tailIci_add_invSucc_atTop
    {ν : Measure NNReal} (x : NNReal) :
    Filter.Tendsto
      (fun n : ℕ ↦ ν (Set.Ici (x + 1 / (n + 1 : NNReal))))
      Filter.atTop (nhds (ν (Set.Ioi x))) := by
  let tails : ℕ → Set NNReal := fun n ↦ Set.Ici (x + 1 / (n + 1 : NNReal))
  have hmono : Monotone tails := by
    intro m n hmn z hz
    change x + 1 / (m + 1 : NNReal) ≤ z at hz
    change x + 1 / (n + 1 : NNReal) ≤ z
    have hm_pos : (0 : NNReal) < (m : NNReal) + 1 := by
      positivity
    have hdiv :
        1 / (n + 1 : NNReal) ≤ 1 / (m + 1 : NNReal) := by
      refine one_div_le_one_div_of_le hm_pos ?_
      exact_mod_cast Nat.succ_le_succ hmn
    exact le_trans (by simpa [add_comm] using add_le_add_left hdiv x) hz
  have hUnion : (⋃ n : ℕ, tails n) = Set.Ioi x := by
    ext z
    constructor
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨n, hn⟩
      have hpos : (0 : NNReal) < 1 / (n + 1 : NNReal) := by
        positivity
      have hx_lt : x < x + 1 / (n + 1 : NNReal) := lt_add_of_pos_right x hpos
      exact lt_of_lt_of_le hx_lt hn
    · intro hz
      have hdiff : 0 < (z : ℝ) - (x : ℝ) := by
        exact sub_pos.mpr <| by exact_mod_cast hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdiff
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      have hlt_real : (x : ℝ) + 1 / (n + 1 : ℝ) < (z : ℝ) := by
        linarith
      have hlt_nn : x + 1 / (n + 1 : NNReal) < z := by
        exact_mod_cast hlt_real
      exact le_of_lt hlt_nn
  -- Proof comment: continuity from below applies to the increasing closed tails.
  have htail :
      Filter.Tendsto (fun n : ℕ ↦ ν (tails n)) Filter.atTop (nhds (ν (Set.Ioi x))) := by
    simpa [hUnion] using (MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν) hmono)
  simpa [tails] using htail

/-- Helper for Corollary 24.18: positive tail control at a given `x` bounds the quantile from
above by `x`. -/
private lemma tailQuantile_le_of_tail_le
    {ν : Measure NNReal} {x y : NNReal}
    (hx : 0 < x) (hy : 0 < y)
    (hxy : ν (Set.Ici x) ≤ (y : ℝ≥0∞)) :
    tailQuantile ν y ≤ x := by
  have hx_mem : x ∈ positiveTailSublevelSet ν y := ⟨hx, hxy⟩
  -- Proof comment: once `x` belongs to the positive tail-sublevel set, its infimum is bounded
  -- above by `x`.
  simp [tailQuantile, ne_of_gt hy]
  exact csInf_le (bddBelow_positiveTailSublevelSet ν y) hx_mem

/-- Helper for Corollary 24.18: if `x` still lies strictly below the quantile level, then the
tail at `x` must still dominate the level `y`. -/
private lemma tailLevel_lt_of_lt_tailQuantile
    {ν : Measure NNReal} {x y : NNReal}
    (hx : 0 < x) (hy : 0 < y)
    (hqx : x < tailQuantile ν y) :
    (y : ℝ≥0∞) < ν (Set.Ici x) := by
  by_contra hnot
  have hx_mem : x ∈ positiveTailSublevelSet ν y := ⟨hx, le_of_not_gt hnot⟩
  have hq_le : tailQuantile ν y ≤ x := by
    -- Proof comment: `x` would then lie in the sublevel set, contradicting that it is strictly
    -- below the infimum quantile level.
    simp [tailQuantile, ne_of_gt hy]
    exact csInf_le (bddBelow_positiveTailSublevelSet ν y) hx_mem
  exact not_lt_of_ge hq_le hqx

/-- Helper for Corollary 24.18: if the tail at `x` is still strictly above the level `y`, then
`x` is a lower bound for the quantile set and hence lies below the generalized inverse. -/
private lemma le_tailQuantile_of_tail_lt
    {ν : Measure NNReal} {x y : NNReal}
    (hx : 0 < x) (hy : 0 < y)
    (hnonempty : Set.Nonempty (positiveTailSublevelSet ν y))
    (hxy : (y : ℝ≥0∞) < ν (Set.Ici x)) :
    x ≤ tailQuantile ν y := by
  simp [tailQuantile, ne_of_gt hy]
  refine le_csInf hnonempty ?_
  intro z hz
  by_contra hzx
  have hzx_lt : z < x := lt_of_not_ge hzx
  have hz_tail :
      ν (Set.Ici x) ≤ ν (Set.Ici z) := by
    exact measure_mono <| Set.Ici_subset_Ici.2 hzx_lt.le
  exact not_lt_of_ge (hz_tail.trans hz.2) hxy

/-- Helper for Corollary 24.18: the lower tail-quantile transport is correct away from the
artificial level `y = 0` normalization. -/
private lemma tailQuantile_superlevel_lower_transport_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : 0 < x) :
    Set.Ioo (0 : NNReal) ((ν (Set.Ici x)).toNNReal) ⊆
      {y : NNReal | x ≤ tailQuantile ν y} := by
  intro y hy
  have htail_lt_top : ν (Set.Ici x) < ∞ :=
    tailIci_lt_top_of_integrableMin hrep.2.1 hx
  have hy_tail :
      (y : ℝ≥0∞) < ν (Set.Ici x) := by
    have hy_tail' :
        (y : ℝ≥0∞) < (((ν (Set.Ici x)).toNNReal : NNReal) : ℝ≥0∞) := by
      exact_mod_cast hy.2
    simpa [ENNReal.coe_toNNReal htail_lt_top.ne] using hy_tail'
  -- Proof comment: once the tail level at `x` strictly dominates the base level `y`, the earlier
  -- quantile lower-bound lemma puts `x` below the generalized inverse.
  exact le_tailQuantile_of_tail_lt hx hy.1
    (positiveTailSublevelSet_nonempty_of_rep hrep hy.1) hy_tail

/-- Helper for Corollary 24.18: the corrected lower sandwich already identifies the full lower
mass needed for the common-base transport route. -/
private lemma tailQuantile_superlevel_measure_ge_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : 0 < x) :
    ν (Set.Ici x) ≤ nnrealLebesgue {y : NNReal | x ≤ tailQuantile ν y} := by
  have htail_lt_top : ν (Set.Ici x) < ∞ :=
    tailIci_lt_top_of_integrableMin hrep.2.1 hx
  have hsubset :
      Set.Ioo (0 : NNReal) ((ν (Set.Ici x)).toNNReal) ⊆
        {y : NNReal | x ≤ tailQuantile ν y} :=
    tailQuantile_superlevel_lower_transport_of_rep hrep hx
  calc
    ν (Set.Ici x)
        = nnrealLebesgue (Set.Ioo (0 : NNReal) ((ν (Set.Ici x)).toNNReal)) := by
            rw [nnrealLebesgue_Ioo_zero_left]
            simp [ENNReal.coe_toNNReal htail_lt_top.ne]
    _ ≤ nnrealLebesgue {y : NNReal | x ≤ tailQuantile ν y} := measure_mono hsubset

/-- Helper for Corollary 24.18: the positive-tail order assumption turns into the pointwise order
of the corresponding tail quantiles. -/
private lemma tailQuantile_le_of_tail_order
    {μ₂ : ProbabilityMeasure NNReal} {α₂ : NNReal}
    {ν₁ ν₂ : Measure NNReal}
    (hrep₂ : HasSubordinatorLevyKhinchinRepresentation μ₂ α₂ ν₂)
    (hν : ∀ x : NNReal, 0 < x → ν₁ (Set.Ici x) ≤ ν₂ (Set.Ici x))
    (y : NNReal) :
    tailQuantile ν₁ y ≤ tailQuantile ν₂ y := by
  by_cases hy : y = 0
  · -- Proof comment: both generalized inverses are normalized to `0` at the zero level.
    simp [tailQuantile, hy]
  · have hy_pos : 0 < y := bot_lt_iff_ne_bot.mpr hy
    -- Proof comment: at positive levels, the ordered sublevel-set inclusion compares the two
    -- defining infima directly.
    simp [tailQuantile, hy]
    exact csInf_positiveTailSublevelSet_le_of_tail_le hν
      (positiveTailSublevelSet_nonempty_of_rep hrep₂ hy_pos)

/-- Helper for Corollary 24.18: for a fixed Lévy representation, the tail quantile is antitone on
positive levels. This is the monotonicity needed later when turning the quantile map into a
measurable deterministic Poisson integrand. -/
private lemma tailQuantile_antitoneOn_Ioi_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    AntitoneOn (tailQuantile ν) (Set.Ioi (0 : NNReal)) := by
  intro y₁ hy₁ y₂ hy₂ hy₁₂
  have hsubset :
      positiveTailSublevelSet ν y₁ ⊆ positiveTailSublevelSet ν y₂ := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (show (y₁ : ℝ≥0∞) ≤ y₂ by exact_mod_cast hy₁₂)⟩
  have hy₁_pos : 0 < y₁ := hy₁
  have hy₂_pos : 0 < y₂ := hy₂
  -- Proof comment: increasing the tail level enlarges the admissible sublevel set, so the
  -- corresponding infimum quantile can only move downward.
  simpa [tailQuantile, hy₁_pos.ne', hy₂_pos.ne'] using
    (csInf_le_csInf
      (bddBelow_positiveTailSublevelSet ν y₂)
      (positiveTailSublevelSet_nonempty_of_rep hrep hy₁_pos)
      hsubset)

/-- Helper for Corollary 24.18: for positive thresholds, the strict superlevel set of the tail
quantile is exactly the interval determined by the open tail mass `ν (x, ∞)`. -/
private lemma tailQuantile_strictSuperlevel_eq_Ioo_tailIoi_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : 0 < x) :
    {y : NNReal | x < tailQuantile ν y} =
      Set.Ioo (0 : NNReal) ((ν (Set.Ioi x)).toNNReal) := by
  have htailIoi_lt_top : ν (Set.Ioi x) < ∞ :=
    tailIoi_lt_top_of_integrableMin hrep.2.1 hx
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [tailQuantile, hy0] at hy
    have hy_pos : 0 < y := bot_lt_iff_ne_bot.mpr hy0
    refine ⟨hy_pos, ?_⟩
    by_contra hnot
    have hy_tail :
        ν (Set.Ioi x) ≤ (y : ℝ≥0∞) := by
      have hy_tail' :
          (((ν (Set.Ioi x)).toNNReal : NNReal) : ℝ≥0∞) ≤ (y : ℝ≥0∞) := by
        exact_mod_cast le_of_not_gt hnot
      simpa [ENNReal.coe_toNNReal htailIoi_lt_top.ne] using hy_tail'
    have hApprox :
        ∀ n : ℕ, tailQuantile ν y ≤ x + 1 / (n + 1 : NNReal) := by
      intro n
      have hx_n : 0 < x + 1 / (n + 1 : NNReal) := by positivity
      have htail_n :
          ν (Set.Ici (x + 1 / (n + 1 : NNReal))) ≤ (y : ℝ≥0∞) := by
        calc
          ν (Set.Ici (x + 1 / (n + 1 : NNReal))) ≤ ν (Set.Ioi x) := by
            refine measure_mono ?_
            intro z hz
            have hpos : (0 : NNReal) < 1 / (n + 1 : NNReal) := by
              positivity
            have hx_lt' : x < x + 1 / (n + 1 : NNReal) := lt_add_of_pos_right x hpos
            exact lt_of_lt_of_le hx_lt' hz
          _ ≤ (y : ℝ≥0∞) := hy_tail
      -- Proof comment: every cutoff slightly to the right of `x` already lies in the sublevel
      -- set at level `y`, so the quantile stays below all of them.
      exact tailQuantile_le_of_tail_le hx_n hy_pos htail_n
    exact not_lt_of_ge (le_of_forall_le_add_invSucc hApprox) hy
  · intro hy
    have hy_tail :
        (y : ℝ≥0∞) < ν (Set.Ioi x) := by
      have hy_tail' :
          (y : ℝ≥0∞) <
            ((((ν (Set.Ioi x)).toNNReal : NNReal) : ℝ≥0∞)) := by
        exact_mod_cast hy.2
      simpa [ENNReal.coe_toNNReal htailIoi_lt_top.ne] using hy_tail'
    have hEventually :
        ∀ᶠ n : ℕ in Filter.atTop,
          (y : ℝ≥0∞) < ν (Set.Ici (x + 1 / (n + 1 : NNReal))) := by
      exact (tendsto_tailIci_add_invSucc_atTop (ν := ν) x).eventually (Ioi_mem_nhds hy_tail)
    obtain ⟨n, hn⟩ := hEventually.exists
    have hx_n : 0 < x + 1 / (n + 1 : NNReal) := by positivity
    have hlower :
        x + 1 / (n + 1 : NNReal) ≤ tailQuantile ν y :=
      le_tailQuantile_of_tail_lt hx_n hy.1
        (positiveTailSublevelSet_nonempty_of_rep hrep hy.1) hn
    have hpos : (0 : NNReal) < 1 / (n + 1 : NNReal) := by
      positivity
    have hx_lt' : x < x + 1 / (n + 1 : NNReal) := lt_add_of_pos_right x hpos
    exact lt_of_lt_of_le hx_lt' hlower

/-- Helper for Corollary 24.18: the strict superlevel set of the tail quantile has
`nnrealLebesgue`-mass exactly equal to the open tail mass `ν (x, ∞)`. -/
private lemma tailQuantile_strictSuperlevel_measure_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : 0 < x) :
    nnrealLebesgue {y : NNReal | x < tailQuantile ν y} = ν (Set.Ioi x) := by
  have htailIoi_lt_top : ν (Set.Ioi x) < ∞ :=
    tailIoi_lt_top_of_integrableMin hrep.2.1 hx
  -- Proof comment: once the superlevel set is normalized to an interval, `nnrealLebesgue`
  -- computes its length directly.
  rw [tailQuantile_strictSuperlevel_eq_Ioo_tailIoi_of_rep hrep hx, nnrealLebesgue_Ioo_zero_left]
  simpa [ENNReal.coe_toNNReal htailIoi_lt_top.ne]

/-- Helper for Corollary 24.18: the tail quantile is a measurable deterministic integrand on the
common `nnrealLebesgue` base space. -/
private lemma measurable_tailQuantile_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    Measurable (tailQuantile ν) := by
  refine measurable_of_Ioi ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    change MeasurableSet {y : NNReal | 0 < tailQuantile ν y}
    have hunion :
        {y : NNReal | 0 < tailQuantile ν y} =
          ⋃ n : ℕ, {y : NNReal | (1 / (n + 1 : NNReal)) < tailQuantile ν y} := by
      ext y
      constructor
      · intro hy
        have hy_real : 0 < ((tailQuantile ν y : NNReal) : ℝ) := by
          exact_mod_cast hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy_real
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        exact_mod_cast hn
      · intro hy
        rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
        have hzero_lt : (0 : NNReal) < 1 / (n + 1 : NNReal) := by
          positivity
        exact lt_trans hzero_lt hn
    rw [hunion]
    refine MeasurableSet.iUnion fun n ↦ ?_
    have hn_pos : (0 : NNReal) < 1 / (n + 1 : NNReal) := by
      positivity
    rw [tailQuantile_strictSuperlevel_eq_Ioo_tailIoi_of_rep hrep hn_pos]
    exact measurableSet_Ioo
  · have hx_pos : 0 < x := bot_lt_iff_ne_bot.mpr hx
    change MeasurableSet {y : NNReal | x < tailQuantile ν y}
    rw [tailQuantile_strictSuperlevel_eq_Ioo_tailIoi_of_rep hrep hx_pos]
    exact measurableSet_Ioo

/-- Helper for Corollary 24.18: the strict superlevel mass transport for `tailQuantile ν`
extends from `NNReal` thresholds to positive real thresholds. -/
private lemma tailQuantile_strictSuperlevel_realMeasure_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : ℝ} (hx : 0 < x) :
    nnrealLebesgue {y : NNReal | x < (tailQuantile ν y : ℝ)} =
      ν {z : NNReal | x < (z : ℝ)} := by
  have hxnn : 0 < Real.toNNReal x := by
    simpa [Real.toNNReal_of_nonneg hx.le] using hx
  have hleft :
      {y : NNReal | x < (tailQuantile ν y : ℝ)} =
        {y : NNReal | Real.toNNReal x < tailQuantile ν y} := by
    ext y
    constructor
    · intro hy
      exact (Real.toNNReal_lt_iff_lt_coe hx.le).2 hy
    · intro hy
      exact (Real.toNNReal_lt_iff_lt_coe hx.le).1 hy
  have hright :
      {z : NNReal | x < (z : ℝ)} = Set.Ioi (Real.toNNReal x) := by
    ext z
    constructor
    · intro hz
      exact (Real.toNNReal_lt_iff_lt_coe hx.le).2 hz
    · intro hz
      exact (Real.toNNReal_lt_iff_lt_coe hx.le).1 hz
  rw [hleft, tailQuantile_strictSuperlevel_measure_eq_of_rep hrep hxnn, hright]

/-- Helper for Corollary 24.18: the superlevel sets of the truncated tail quantile match the
superlevel sets of the truncated identity under the `ν`-transport. -/
private lemma tailQuantile_minTruncation_superlevel_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {t : ℝ} (ht : 0 < t) :
    nnrealLebesgue {y : NNReal | t < min (1 : ℝ) (tailQuantile ν y : ℝ)} =
      ν {x : NNReal | t < min (1 : ℝ) (x : ℝ)} := by
  by_cases ht1 : t < 1
  · have hleft :
        {y : NNReal | t < min (1 : ℝ) (tailQuantile ν y : ℝ)} =
          {y : NNReal | t < (tailQuantile ν y : ℝ)} := by
        ext y
        constructor
        · intro hy
          change t < min (1 : ℝ) (tailQuantile ν y : ℝ) at hy
          change t < (tailQuantile ν y : ℝ)
          exact lt_of_lt_of_le hy (min_le_right _ _)
        · intro hy
          change t < (tailQuantile ν y : ℝ) at hy
          change t < min (1 : ℝ) (tailQuantile ν y : ℝ)
          exact lt_min ht1 hy
    have hright :
        {x : NNReal | t < min (1 : ℝ) (x : ℝ)} =
          {x : NNReal | t < (x : ℝ)} := by
        ext x
        constructor
        · intro hx
          change t < min (1 : ℝ) (x : ℝ) at hx
          change t < (x : ℝ)
          exact lt_of_lt_of_le hx (min_le_right _ _)
        · intro hx
          change t < (x : ℝ) at hx
          change t < min (1 : ℝ) (x : ℝ)
          exact lt_min ht1 hx
    rw [hleft, hright, tailQuantile_strictSuperlevel_realMeasure_eq_of_rep hrep ht]
  · have hleft :
        {y : NNReal | t < min (1 : ℝ) (tailQuantile ν y : ℝ)} = ∅ := by
      ext y
      constructor
      · intro hy
        change t < min (1 : ℝ) (tailQuantile ν y : ℝ) at hy
        exact (ht1 (lt_of_lt_of_le hy (min_le_left _ _))).elim
      · intro hy
        cases hy
    have hright :
        {x : NNReal | t < min (1 : ℝ) (x : ℝ)} = ∅ := by
      ext x
      constructor
      · intro hx
        change t < min (1 : ℝ) (x : ℝ) at hx
        exact (ht1 (lt_of_lt_of_le hx (min_le_left _ _))).elim
      · intro hx
        cases hx
    rw [hleft, hright]
    simp

/-- Helper for Corollary 24.18: the real-valued tail quantile is measurable on the common
base space. -/
private lemma measurable_tailQuantile_real_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    Measurable (fun y : NNReal ↦ (tailQuantile ν y : ℝ)) := by
  exact measurable_coe_nnreal_real.comp (measurable_tailQuantile_of_rep hrep)

/-- Helper for Corollary 24.18: the layer-cake representation for `min (1, tailQuantile ν)`
matches the corresponding representation for `min (1, x)` under `ν`. -/
private lemma tailQuantile_minTruncation_lintegral_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    ∫⁻ y, ENNReal.ofReal (min (1 : ℝ) (tailQuantile ν y : ℝ)) ∂nnrealLebesgue =
      ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν := by
  have hleft_nonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ) :=
    Filter.Eventually.of_forall fun y ↦ le_min zero_le_one (tailQuantile ν y).2
  have hleft_meas :
      AEMeasurable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) nnrealLebesgue := by
    have hmeas : Measurable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) := by
      exact measurable_const.min (measurable_tailQuantile_real_of_rep hrep)
    exact hmeas.aemeasurable
  have hright_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ min (1 : ℝ) (x : ℝ) :=
    Filter.Eventually.of_forall fun x ↦ le_min zero_le_one x.2
  have hright_meas :
      AEMeasurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) := by
      exact measurable_const.min measurable_coe_nnreal_real
    exact hmeas.aemeasurable
  calc
    ∫⁻ y, ENNReal.ofReal (min (1 : ℝ) (tailQuantile ν y : ℝ)) ∂nnrealLebesgue
        = ∫⁻ t in Set.Ioi (0 : ℝ),
            nnrealLebesgue {y : NNReal | t < min (1 : ℝ) (tailQuantile ν y : ℝ)} := by
              exact MeasureTheory.lintegral_eq_lintegral_meas_lt _ hleft_nonneg hleft_meas
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ν {x : NNReal | t < min (1 : ℝ) (x : ℝ)} := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact tailQuantile_minTruncation_superlevel_eq_of_rep hrep ht
    _ = ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) (x : ℝ)) ∂ν := by
          symm
          exact MeasureTheory.lintegral_eq_lintegral_meas_lt _ hright_nonneg hright_meas

/-- Helper for Corollary 24.18: the common-base tail quantile satisfies the same truncated
first-moment integrability as the original Lévy measure. -/
private lemma tailQuantile_integrableMin_nnrealLebesgue
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    Integrable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) nnrealLebesgue := by
  have hmeas :
      AEStronglyMeasurable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) nnrealLebesgue := by
    have hmeas' : Measurable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) := by
      exact measurable_const.min (measurable_tailQuantile_real_of_rep hrep)
    exact hmeas'.aestronglyMeasurable
  have hnonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ) :=
    Filter.Eventually.of_forall fun y ↦ le_min zero_le_one (tailQuantile ν y).2
  have hlintegral_ne_top :
      ∫⁻ y, ENNReal.ofReal (min (1 : ℝ) (tailQuantile ν y : ℝ)) ∂nnrealLebesgue ≠ ∞ := by
    rw [tailQuantile_minTruncation_lintegral_eq_of_rep hrep]
    have hmeas' :
        AEStronglyMeasurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
      have hmeas'' : Measurable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) := by
        exact measurable_const.min measurable_coe_nnreal_real
      exact hmeas''.aestronglyMeasurable
    have hnonneg' :
        0 ≤ᵐ[ν] fun x : NNReal ↦ min (1 : ℝ) (x : ℝ) :=
      Filter.Eventually.of_forall fun x ↦ le_min zero_le_one x.2
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas' hnonneg').2 hrep.2.1
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1 hlintegral_ne_top

/-- Helper for Corollary 24.18: the Bernstein kernel is an interval integral of its positive
derivative. -/
private lemma bernsteinKernel_eq_intervalIntegral (t x : NNReal) :
    ∫ s in (0 : ℝ)..(x : ℝ), (t : ℝ) * Real.exp (-((t : ℝ) * s)) =
      1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
  let F : ℝ → ℝ := fun s ↦ 1 - Real.exp (-((t : ℝ) * s))
  have hcont :
      ContinuousOn F (Set.Icc (0 : ℝ) (x : ℝ)) := by
    refine Continuous.continuousOn ?_
    dsimp [F]
    fun_prop
  have hderiv :
      ∀ s ∈ Set.Ioo (0 : ℝ) (x : ℝ),
        HasDerivAt F
          ((t : ℝ) * Real.exp (-((t : ℝ) * s))) s := by
    intro s hs
    have hInner : HasDerivAt (fun r : ℝ ↦ -((t : ℝ) * r)) (-(t : ℝ)) s := by
      simpa [mul_comm] using (((hasDerivAt_id s).const_mul (t : ℝ)).neg)
    have hExp :
        HasDerivAt (fun r : ℝ ↦ Real.exp (-((t : ℝ) * r)))
          (Real.exp (-((t : ℝ) * s)) * (-(t : ℝ))) s := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_exp (-((t : ℝ) * s))).comp s hInner
    -- Proof comment: differentiating `1 - exp (-t s)` produces the positive Bernstein density.
    convert (hasDerivAt_const s (1 : ℝ)).sub hExp using 1 <;> ring
  have hint :
      IntervalIntegrable (fun s : ℝ ↦ (t : ℝ) * Real.exp (-((t : ℝ) * s))) volume 0 (x : ℝ) := by
    have hkernelCont : Continuous (fun s : ℝ ↦ (t : ℝ) * Real.exp (-((t : ℝ) * s))) := by
      fun_prop
    exact hkernelCont.intervalIntegrable 0 (x : ℝ)
  -- Proof comment: apply the fundamental theorem of calculus to the explicit antiderivative.
  calc
    ∫ s in (0 : ℝ)..(x : ℝ), (t : ℝ) * Real.exp (-((t : ℝ) * s)) = F (x : ℝ) - F 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.2 hcont hderiv hint
    _ = 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
      simp [F]

/-- Helper for Corollary 24.18: the Bernstein kernel is pointwise nonnegative on `[0, ∞)`. -/
private lemma bernsteinKernel_nonneg (t : NNReal) (x : NNReal) :
    0 ≤ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
  have hle : Real.exp (-((t : ℝ) * (x : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith [t.2, x.2]
  exact sub_nonneg.mpr hle

/-- Helper for Corollary 24.18: the Bernstein kernel is measurable on `NNReal`. -/
private lemma bernsteinKernel_measurable (t : NNReal) :
    Measurable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) := by
  fun_prop

/-- Helper for Corollary 24.18: truncated first-moment integrability controls the Bernstein
kernel `x ↦ 1 - exp (-t x)`. -/
private lemma bernsteinKernel_integrable_of_integrableMin
    {ρ : Measure NNReal} (t : NNReal)
    (hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ρ) :
    Integrable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ρ := by
  have hdom :
      Integrable (fun x : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ)) ρ :=
    hInt.const_mul (max 1 (t : ℝ))
  refine Integrable.mono' hdom (bernsteinKernel_measurable t).aestronglyMeasurable ?_
  filter_upwards with x
  have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := bernsteinKernel_nonneg t x
  have hle :
      1 - Real.exp (-((t : ℝ) * (x : ℝ))) ≤
        max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ) :=
    poissonExpKernel_scale_le_maxMulMinOne (t : ℝ) t.2 x
  simpa [Real.norm_of_nonneg hnonneg] using hle

/-- Helper for Corollary 24.18: the Bernstein kernel of the transported tail quantile is
integrable on the common `nnrealLebesgue` base space. -/
private lemma tailQuantile_bernsteinKernel_integrable_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) (t : NNReal) :
    Integrable
      (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))))
      nnrealLebesgue := by
  have hmeas :
      AEStronglyMeasurable
        (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))))
        nnrealLebesgue := by
    have htail_meas : Measurable (fun y : NNReal ↦ (tailQuantile ν y : ℝ)) :=
      measurable_tailQuantile_real_of_rep hrep
    have hmeas' :
        Measurable
          (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) := by
      exact measurable_const.sub
        (Real.continuous_exp.measurable.comp ((measurable_const.mul htail_meas).neg))
    exact hmeas'.aestronglyMeasurable
  have hdom :
      Integrable
        (fun y : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (tailQuantile ν y : ℝ))
        nnrealLebesgue :=
    (tailQuantile_integrableMin_nnrealLebesgue hrep).const_mul (max 1 (t : ℝ))
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards with y
  have hnonneg :
      0 ≤ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) :=
    bernsteinKernel_nonneg t (tailQuantile ν y)
  have hle :
      1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) ≤
        max 1 (t : ℝ) * min (1 : ℝ) (tailQuantile ν y : ℝ) :=
    poissonExpKernel_scale_le_maxMulMinOne (t : ℝ) t.2 (tailQuantile ν y)
  simpa [Real.norm_of_nonneg hnonneg] using hle

/-- Helper for Corollary 24.18: centering the Bernstein kernel by subtracting `1` flips the sign
of its integral. -/
private lemma bernsteinKernel_centeredIntegral_eq_neg
    {ρ : Measure NNReal} {f : NNReal → ℝ} :
    ∫ x : NNReal, (Real.exp (-f x) - 1) ∂ρ =
      -∫ x : NNReal, (1 - Real.exp (-f x)) ∂ρ := by
  have hEq :
      (fun x : NNReal ↦ Real.exp (-f x) - 1) =
        fun x : NNReal ↦ -(1 - Real.exp (-f x)) := by
    funext x
    ring
  rw [hEq, integral_neg]

/-- Helper for Corollary 24.18: the Bernstein kernel has the same `nnrealLebesgue` integral after
transport through the tail quantile as it has under the original Lévy measure. -/
private lemma tailQuantile_bernsteinKernel_lintegral_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (t : NNReal) :
    ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue =
      ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
  let g : ℝ → ℝ := fun s ↦ (t : ℝ) * Real.exp (-((t : ℝ) * s))
  have hg_cont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg_intble : ∀ s > 0, IntervalIntegrable g volume 0 s := by
    intro s _hs
    exact hg_cont.intervalIntegrable 0 s
  have hg_nonneg :
      ∀ᵐ s ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg t.2 (Real.exp_nonneg _)
  have htail_nonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ (tailQuantile ν y : ℝ) :=
    Filter.Eventually.of_forall fun y ↦ (tailQuantile ν y).2
  have htail_meas :
      AEMeasurable (fun y : NNReal ↦ (tailQuantile ν y : ℝ)) nnrealLebesgue := by
    exact (measurable_tailQuantile_real_of_rep hrep).aemeasurable
  have hid_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ (x : ℝ) :=
    Filter.Eventually.of_forall fun x ↦ x.2
  have hid_meas :
      AEMeasurable (fun x : NNReal ↦ (x : ℝ)) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ (x : ℝ)) := by
      fun_prop
    exact hmeas.aemeasurable
  calc
    ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue
        = ∫⁻ y,
            ENNReal.ofReal
              (∫ s in (0 : ℝ)..(tailQuantile ν y : ℝ), g s) ∂nnrealLebesgue := by
                refine lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
                simpa [g] using congrArg ENNReal.ofReal
                  (bernsteinKernel_eq_intervalIntegral t (tailQuantile ν y)).symm
    _ = ∫⁻ s in Set.Ioi (0 : ℝ),
            nnrealLebesgue {y : NNReal | s < (tailQuantile ν y : ℝ)} * ENNReal.ofReal (g s) := by
          exact MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul _ htail_nonneg htail_meas
            hg_intble hg_nonneg
    _ = ∫⁻ s in Set.Ioi (0 : ℝ),
            ν {x : NNReal | s < (x : ℝ)} * ENNReal.ofReal (g s) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
          rw [tailQuantile_strictSuperlevel_realMeasure_eq_of_rep hrep hs]
    _ = ∫⁻ x, ENNReal.ofReal (∫ s in (0 : ℝ)..(x : ℝ), g s) ∂ν := by
          symm
          exact MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul _ hid_nonneg hid_meas
            hg_intble hg_nonneg
    _ = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
          refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          simpa [g] using congrArg ENNReal.ofReal (bernsteinKernel_eq_intervalIntegral t x)

/-- Helper for Corollary 24.18: the Bernstein-kernel integral of `tailQuantile ν` over the common
base space equals the canonical Lévy exponent integral over `ν`. -/
private lemma tailQuantile_bernsteinKernelIntegral_eq_of_rep
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (t : NNReal) :
    ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue =
      ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
  have hIntBase :
      Integrable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))))
        nnrealLebesgue :=
    tailQuantile_bernsteinKernel_integrable_of_rep hrep t
  have hIntNu :
      Integrable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ν :=
    bernsteinKernel_integrable_of_integrableMin t hrep.2.1
  have hNonnegBase :
      0 ≤ᵐ[nnrealLebesgue]
        fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) :=
    Filter.Eventually.of_forall fun y ↦ bernsteinKernel_nonneg t (tailQuantile ν y)
  have hNonnegNu :
      0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) :=
    Filter.Eventually.of_forall fun x ↦ bernsteinKernel_nonneg t x
  have hEq :
      ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue) =
        ENNReal.ofReal
          (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
    calc
      ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue)
          =
        ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))))
          ∂nnrealLebesgue := by
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntBase hNonnegBase
      _ = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν :=
            tailQuantile_bernsteinKernel_lintegral_eq_of_rep hrep t
      _ =
        ENNReal.ofReal
          (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntNu hNonnegNu
  have hLeftNonneg :
      0 ≤ ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue :=
    integral_nonneg_of_ae hNonnegBase
  have hRightNonneg :
      0 ≤ ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν :=
    integral_nonneg_of_ae hNonnegNu
  have hEqReal := congrArg ENNReal.toReal hEq
  simpa [ENNReal.toReal_ofReal hLeftNonneg, ENNReal.toReal_ofReal hRightNonneg] using hEqReal

/-- Helper for Corollary 24.18: a nonzero simple-function fiber lies inside the support of the
simple function. -/
private lemma simpleFuncFiber_subset_support
    {β : Type*} [Zero β] {s : MeasureTheory.SimpleFunc NNReal β} {r : β} (hr : r ≠ 0) :
    s ⁻¹' {r} ⊆ Function.support s := by
  intro x hx
  have hsx : s x = r := by
    simpa using hx
  -- Proof comment: a point in a nonzero fiber cannot be outside the support.
  simpa [Function.mem_support, hsx] using hr

/-- Helper for Corollary 24.18: a finite nonnegative step function integrates to the matching
finite sum of cell masses. -/
private lemma stepLintegral_eq_fintypeSum
    {ι : Type*} [Fintype ι] {ν : Measure NNReal} (A : ι → Set NNReal) (a : ι → NNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫⁻ x, ∑ i, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν =
      ∑ i, (a i : ℝ≥0∞) * ν (A i) := by
  classical
  calc
    ∫⁻ x, ∑ i, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν
      = ∑ i, ∫⁻ x, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν := by
          simpa using
            (lintegral_finset_sum Finset.univ
              (fun i _ ↦
                (show Measurable (fun x ↦ (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x) from
                  measurable_const.indicator (hA i))))
    _ = ∑ i, (a i : ℝ≥0∞) * ν (A i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [lintegral_indicator_const (hA i)]

/-- Helper for Corollary 24.18: a finite real step function with finite cell masses integrates to
the matching finite real sum. -/
private lemma stepIntegral_eq_fintypeSum
    {ι : Type*} [Fintype ι] {ν : Measure NNReal} (A : ι → Set NNReal) (c : ι → ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hA_finite : ∀ i, ν (A i) ≠ ⊤) :
    ∫ x, ∑ i, (A i).indicator (fun _ ↦ c i) x ∂ν =
      ∑ i, c i * (ν (A i)).toReal := by
  classical
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_indicator_const (c i) (hA i), measureReal_def]
    simpa [smul_eq_mul, mul_comm]
  · intro i _
    have hAi_lt_top : ν (A i) < ∞ := lt_top_iff_ne_top.mpr (hA_finite i)
    have hIntOn : IntegrableOn (fun _ : NNReal ↦ c i) (A i) ν := by
      refine IntegrableOn.of_bound hAi_lt_top stronglyMeasurable_const.aestronglyMeasurable ‖c i‖ ?_
      exact Filter.Eventually.of_forall fun _ ↦ le_rfl
    -- Proof comment: finite measure of each cell makes the constant-on-cell summand integrable.
    exact hIntOn.integrable_indicator (hA i)

/-- Helper for Corollary 24.18: bounded-cell count variables of the common-base Poisson process
are almost surely finite. -/
private lemma poissonPointProcess_count_ae_ltTop
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {A : Set NNReal} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    ∀ᵐ ω ∂(P : Measure Ω), X ω A < ∞ := by
  have hA_finite : nnrealLebesgue A ≠ ∞ :=
    (nnrealLebesgue_lt_top_of_isBounded A hA hA_bdd).ne
  have hLaw :
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (nnrealLebesgue A).toNNReal))
        (P : Measure Ω) :=
    hX.2.2.2 hA hA_bdd hA_finite
  have hNatLaw :
      HasLaw (fun n : ℕ ↦ (n : ℝ≥0∞))
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (nnrealLebesgue A).toNNReal))
        (poissonMeasure (nnrealLebesgue A).toNNReal) := by
    refine ⟨(measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).aemeasurable, ?_⟩
    rfl
  have hFiniteMap :
      ∀ᵐ x ∂(Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞))
        (poissonMeasure (nnrealLebesgue A).toNNReal)), x < ∞ := by
    -- Proof comment: every point in the pushed Poisson law comes from a natural-number count.
    exact (hNatLaw.ae_iff (p := fun x : ℝ≥0∞ ↦ x < ∞) (by fun_prop)).1 <|
      Filter.Eventually.of_forall fun n : ℕ ↦ by
        exact ENNReal.natCast_lt_top n
  -- Proof comment: transport the finiteness event from the explicit Poisson count law back to the
  -- bounded-cell count variable of the Poisson point process.
  exact (hLaw.ae_iff (p := fun x : ℝ≥0∞ ↦ x < ∞) (by fun_prop)).2 hFiniteMap

/-- Helper for Corollary 24.18: a simple nonnegative integrand with bounded support already
satisfies the finite-cell Laplace transform formula on the common-base Poisson process. -/
private lemma simpleFuncLaplaceTransformNNReal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    (s : MeasureTheory.SimpleFunc NNReal NNReal)
    (hsupport_bdd : Bornology.IsBounded (Function.support s)) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (s y : ENNReal) ∂ X ω) ∂(P : Measure Ω) =
      Real.exp (∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂nnrealLebesgue) := by
  classical
  let values : Finset NNReal := s.range.filter fun r ↦ r ≠ 0
  let ι := {r : NNReal // r ∈ values}
  letI : Fintype ι := Finset.fintypeCoeSort values
  let A : ι → Set NNReal := fun i ↦ s ⁻¹' {i.1}
  let a : ι → NNReal := fun i ↦ i.1
  have hA : ∀ i : ι, MeasurableSet (A i) := by
    intro i
    simpa [A] using s.measurableSet_preimage ({i.1} : Set NNReal)
  have hA_bdd : ∀ i : ι, Bornology.IsBounded (A i) := by
    intro i
    refine hsupport_bdd.subset ?_
    intro x hx
    exact simpleFuncFiber_subset_support (r := i.1) (Finset.mem_filter.mp i.2).2 hx
  have hA_finite : ∀ i : ι, nnrealLebesgue (A i) ≠ ∞ := by
    intro i
    exact (nnrealLebesgue_lt_top_of_isBounded _ (hA i) (hA_bdd i)).ne
  have hdisj : Pairwise (fun i j : ι ↦ Disjoint (A i) (A j)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' ↦ ?_
    apply hij
    apply Subtype.ext
    have hxi : s x = i.1 := by
      simpa [A] using hx
    have hxj : s x = j.1 := by
      simpa [A] using hx'
    exact hxi.symm.trans hxj
  have hsampleFun :
      (fun y : NNReal ↦ ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y) =
        fun y ↦ (s y : ℝ≥0∞) := by
    funext y
    by_cases hy0 : s y = 0
    · have hterm_zero :
          ∀ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y = 0 := by
        intro i
        have hne0 : i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
        have hy_not : y ∉ A i := by
          intro hy
          have hsy : s y = i.1 := by
            simpa [A] using hy
          exact hne0 (hsy.symm.trans hy0)
        simp [A, a, hy_not]
      simp [hy0, hterm_zero]
    · let i0 : ι := ⟨s y, Finset.mem_filter.2 ⟨s.mem_range_self y, hy0⟩⟩
      have hsum :
          ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y = (a i0 : ℝ≥0∞) := by
        rw [Finset.sum_eq_single i0]
        · simp [A, a, i0]
        · intro j hj hji
          have hy_not : y ∉ A j := by
            intro hy
            have hsy : s y = j.1 := by
              simpa [A] using hy
            exact hji (Subtype.ext (by simpa [i0] using hsy.symm))
          simp [A, a, hy_not]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      simpa [a, i0] using hsum
  have hcenteredFun :
      (fun y : NNReal ↦
        ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y) =
        fun y ↦ Real.exp (-(s y : ℝ)) - 1 := by
    funext y
    by_cases hy0 : s y = 0
    · have hterm_zero :
          ∀ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y = 0 := by
        intro i
        have hne0 : i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
        have hy_not : y ∉ A i := by
          intro hy
          have hsy : s y = i.1 := by
            simpa [A] using hy
          exact hne0 (hsy.symm.trans hy0)
        simp [A, a, hy_not]
      simp [hy0, hterm_zero]
    · let i0 : ι := ⟨s y, Finset.mem_filter.2 ⟨s.mem_range_self y, hy0⟩⟩
      have hsum :
          ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y =
            Real.exp (-(a i0 : ℝ)) - 1 := by
        rw [Finset.sum_eq_single i0]
        · simp [A, a, i0]
        · intro j hj hji
          have hy_not : y ∉ A j := by
            intro hy
            have hsy : s y = j.1 := by
              simpa [A] using hy
            exact hji (Subtype.ext (by simpa [i0] using hsy.symm))
          simp [A, a, hy_not]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      simpa [a, i0] using hsum
  have hFiniteAll :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ i : ι, X ω (A i) < ∞ := by
    rw [ae_all_iff]
    intro i
    exact poissonPointProcess_count_ae_ltTop P X hX (hA i) (hA_bdd i)
  have hsampleSum :
      ∀ ω,
        ∫⁻ y, (s y : ℝ≥0∞) ∂ X ω =
          ∑ i : ι, (a i : ℝ≥0∞) * X ω (A i) := by
    intro ω
    calc
      ∫⁻ y, (s y : ℝ≥0∞) ∂ X ω
          = ∫⁻ y, ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y ∂ X ω := by
              rw [← hsampleFun]
      _ = ∑ i : ι, (a i : ℝ≥0∞) * X ω (A i) := stepLintegral_eq_fintypeSum A a hA
  have hIntensitySum :
      ∑ i : ι, (nnrealLebesgue (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1) =
        ∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂nnrealLebesgue := by
    calc
      ∑ i : ι, (nnrealLebesgue (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)
          = ∫ y : NNReal,
              ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y
              ∂nnrealLebesgue := by
                symm
                simpa [mul_comm] using
                  stepIntegral_eq_fintypeSum A (fun i ↦ Real.exp (-(a i : ℝ)) - 1) hA hA_finite
      _ = ∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂nnrealLebesgue := by
            simpa [hcenteredFun]
  have hraw :
      ∫ ω, Real.exp (-∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) =
        Real.exp (∑ i : ι, (nnrealLebesgue (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
    -- Proof comment: on the finitely many nonzero fibers of `s`, the imported finite-cell Laplace
    -- identity gives the common-base PPP transform exactly.
    simpa [A, a] using
      ProbabilityTheory.disjointBoundedStepLaplaceTransformNNReal P nnrealLebesgue X hX
        A a hA hA_bdd hdisj
  calc
    ∫ ω, ennrealExpNeg (∫⁻ y, (s y : ENNReal) ∂ X ω) ∂(P : Measure Ω)
        = ∫ ω, Real.exp (-∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) := by
            refine integral_congr_ae ?_
            filter_upwards [hFiniteAll] with ω hω
            have hsum_ne_top :
                (∑ i : ι, (a i : ℝ≥0∞) * X ω (A i)) ≠ ∞ := by
              exact (ENNReal.sum_lt_top.mpr fun i _ ↦ ENNReal.mul_lt_top (by simp [a]) (hω i)).ne
            have hsum_toReal :
                (∑ i : ι, (a i : ℝ≥0∞) * X ω (A i)).toReal =
                  ∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal := by
              rw [ENNReal.toReal_sum]
              · refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [ENNReal.toReal_mul]
                simp [a]
              · intro i _
                exact (ENNReal.mul_lt_top (by simp [a]) (hω i)).ne
            rw [hsampleSum ω, ennrealExpNeg, if_neg hsum_ne_top, hsum_toReal]
    _ = Real.exp (∑ i : ι, (nnrealLebesgue (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := hraw
    _ = Real.exp (∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂nnrealLebesgue) := by
          rw [hIntensitySum]

-- Helper for Corollary 24.18: the next theorem records the common-base deterministic PPP
-- Laplace transform in the specialized `NNReal` setting.
/-- Helper for Corollary 24.18: the standard cutoff of a nonnegative kernel to the box
`[0, n] × [0, n]`. -/
private def truncationKernel (g : NNReal → NNReal) (n : ℕ) (y : NNReal) : NNReal :=
  if y ≤ n then min (g y) n else 0

/-- Helper for Corollary 24.18: the cutoff kernels increase pointwise with the truncation level. -/
private lemma truncationKernel_mono
    (g : NNReal → NNReal) {n m : ℕ} (hnm : n ≤ m) (y : NNReal) :
    truncationKernel g n y ≤ truncationKernel g m y := by
  by_cases hyn : y ≤ n
  · have hnm' : (n : NNReal) ≤ m := by
      exact_mod_cast hnm
    have hym : y ≤ m := le_trans hyn hnm'
    simpa [truncationKernel, hyn, hym] using min_le_min_left (g y) hnm'
  · by_cases hym : y ≤ m
    · simp [truncationKernel, hyn, hym]
    · simp [truncationKernel, hyn, hym]

/-- Helper for Corollary 24.18: every fixed point is eventually untouched by the cutoff kernel. -/
private lemma iSup_truncationKernel_eq
    (g : NNReal → NNReal) (y : NNReal) :
    (⨆ n : ℕ, (truncationKernel g n y : ℝ≥0∞)) = g y := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n ↦ ?_
    by_cases hyn : y ≤ n
    · simp [truncationKernel, hyn]
    · simp [truncationKernel, hyn]
  · rcases exists_nat_gt (max (y : ℝ) (g y : ℝ)) with ⟨n, hn⟩
    have hy_le : y ≤ n := by
      exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
    have hg_le : g y ≤ n := by
      exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
    refine le_iSup_of_le n ?_
    simp [truncationKernel, hy_le, min_eq_left hg_le]

/-- Helper for Corollary 24.18: a nonnegative `ℝ≥0∞`-valued kernel bounded by `1` and supported
in a bounded set has finite `nnrealLebesgue`-mass. -/
private lemma lintegral_ltTop_of_support_bounded_le_one
    {h : NNReal → ℝ≥0∞}
    (hsupport_bdd : Bornology.IsBounded (Function.support h))
    (h_le_one : ∀ y, h y ≤ 1) :
    ∫⁻ y, h y ∂nnrealLebesgue < ∞ := by
  rcases hsupport_bdd.subset_closedBall (0 : NNReal) with ⟨r, hr⟩
  have hpoint :
      ∀ y,
        h y ≤ Set.indicator (Metric.closedBall (0 : NNReal) r)
          (fun _ ↦ (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : NNReal) r
    · simpa [hy] using h_le_one y
    · have hy_not_support : y ∉ Function.support h := by
        intro hy_support
        exact hy (hr hy_support)
      have hh0 : h y = 0 := by
        simpa [Function.mem_support] using hy_not_support
      simp [hy, hh0]
  calc
    ∫⁻ y, h y ∂nnrealLebesgue
        ≤ ∫⁻ y,
            Set.indicator (Metric.closedBall (0 : NNReal) r)
              (fun _ ↦ (1 : ℝ≥0∞)) y ∂nnrealLebesgue := by
              exact MeasureTheory.lintegral_mono hpoint
    _ = nnrealLebesgue (Metric.closedBall (0 : NNReal) r) := by
          rw [MeasureTheory.lintegral_indicator_const (Metric.isClosed_closedBall.measurableSet)]
          simp
    _ < ∞ := by
          exact nnrealLebesgue_lt_top_of_isBounded _ (Metric.isClosed_closedBall.measurableSet)
            Metric.isBounded_closedBall

/-- Helper for Corollary 24.18: the Poisson exponent kernel vanishes whenever the underlying
nonnegative kernel vanishes. -/
private lemma support_poissonLaplaceKernel_subset_support
    {g : NNReal → ℝ≥0∞} :
    Function.support
        (fun y : NNReal ↦
          (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))) ⊆
      Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have hkernel0 :
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y)) = 0 := by
    simp [hg0, ennrealExpNeg]
  exact hy hkernel0

/-- Helper for Corollary 24.18: on finite `ℝ≥0∞` values, the Poisson exponent kernel is the
`ENNReal` lift of the real Bernstein kernel. -/
private lemma poissonLaplaceKernel_eq_ofReal_of_neTop
    {z : ℝ≥0∞} (hz : z ≠ ∞) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg z) =
      ENNReal.ofReal (1 - Real.exp (-z.toReal)) := by
  have hExpNonneg : 0 ≤ Real.exp (-z.toReal) := Real.exp_nonneg _
  simp [ennrealExpNeg, hz, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Corollary 24.18: the Poisson exponent kernel is monotone on finite
`ℝ≥0∞`-arguments. -/
private lemma poissonLaplaceKernel_mono
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hab : a ≤ b) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg a) ≤
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg b) := by
  have htoReal : a.toReal ≤ b.toReal := ENNReal.toReal_mono hb hab
  have hreal : 1 - Real.exp (-a.toReal) ≤ 1 - Real.exp (-b.toReal) := by
    have hExp : Real.exp (-b.toReal) ≤ Real.exp (-a.toReal) := by
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [poissonLaplaceKernel_eq_ofReal_of_neTop ha, poissonLaplaceKernel_eq_ofReal_of_neTop hb]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Helper for Corollary 24.18: if a monotone sequence of finite `ℝ≥0∞` values has supremum
`a`, then applying `ennrealExpNeg` preserves the limit. -/
private lemma tendsto_ennrealExpNeg_of_monotone_iSup
    {u : ℕ → ℝ≥0∞} (hu_mono : Monotone u) (hu_finite : ∀ n, u n ≠ ∞)
    {a : ℝ≥0∞} (ha : (⨆ n, u n) = a) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (u n)) Filter.atTop (nhds (ennrealExpNeg a)) := by
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds a) := by
    rw [← ha]
    exact tendsto_atTop_iSup hu_mono
  by_cases ha_top : a = ∞
  · have hcoe_top :
        Filter.Tendsto (fun n : ℕ ↦ (((u n).toNNReal : NNReal) : ℝ≥0∞))
          Filter.atTop (nhds ∞) := by
      have hcoe :
          (fun n : ℕ ↦ (((u n).toNNReal : NNReal) : ℝ≥0∞)) = u := by
        funext n
        exact ENNReal.coe_toNNReal (hu_finite n)
      simpa [ha_top, hcoe] using hu_tendsto
    have htoNN_top : Filter.Tendsto (fun n : ℕ ↦ (u n).toNNReal) Filter.atTop Filter.atTop :=
      (ENNReal.tendsto_coe_nhds_top).1 hcoe_top
    have htoReal_top : Filter.Tendsto (fun n : ℕ ↦ (u n).toReal) Filter.atTop Filter.atTop := by
      have hcoeReal :
          Filter.Tendsto (fun n : ℕ ↦ ((u n).toNNReal : ℝ)) Filter.atTop Filter.atTop :=
        (NNReal.tendsto_coe_atTop).2 htoNN_top
      simpa [ENNReal.coe_toNNReal_eq_toReal] using hcoeReal
    have hExpZero :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-((u n).toReal))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp htoReal_top
    have hseq :
        (fun n : ℕ ↦ ennrealExpNeg (u n)) = fun n : ℕ ↦ Real.exp (-((u n).toReal)) := by
      funext n
      rw [ennrealExpNeg, if_neg (hu_finite n)]
    rw [ha_top, ennrealExpNeg]
    simp only [if_pos rfl]
    simpa [hseq] using hExpZero
  · have htoReal :
        Filter.Tendsto (fun n : ℕ ↦ (u n).toReal) Filter.atTop (nhds a.toReal) :=
      (ENNReal.tendsto_toReal ha_top).comp hu_tendsto
    have hExp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-((u n).toReal))) Filter.atTop
          (nhds (Real.exp (-a.toReal))) := by
      have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      exact hcont.continuousAt.tendsto.comp htoReal
    have hseq :
        (fun n : ℕ ↦ ennrealExpNeg (u n)) = fun n : ℕ ↦ Real.exp (-((u n).toReal)) := by
      funext n
      rw [ennrealExpNeg, if_neg (hu_finite n)]
    have hlim : ennrealExpNeg a = Real.exp (-a.toReal) := by
      rw [ennrealExpNeg, if_neg ha_top]
    rw [hlim]
    simpa [hseq] using hExp

/-- Helper for Corollary 24.18: the standard cutoff `y ↦ if y ≤ n then min (g y) n else 0`
has bounded support inside `[0, n]`. -/
private lemma truncationSupport_isBounded
    (g : NNReal → NNReal) (n : ℕ) :
    Bornology.IsBounded
      (Function.support (truncationKernel g n)) := by
  have hsubset :
      Function.support (truncationKernel g n) ⊆
        Metric.closedBall (0 : NNReal) n := by
    intro y hy
    have hy_le : y ≤ n := by
      by_cases hyn : y ≤ n
      · exact hyn
      · exfalso
        exact hy (by simp [truncationKernel, hyn])
    -- Proof comment: outside `[0, n]` the cutoff vanishes, so every support point lies in the
    -- closed ball of radius `n` around `0`.
    simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hy_le
  exact Metric.isBounded_closedBall.subset hsubset

/-- Helper for Corollary 24.18: coercing a nonnegative real-valued kernel to `ℝ≥0∞` preserves
its support. -/
private lemma support_coe_nnreal_ennreal
    (g : NNReal → NNReal) :
    Function.support (fun y : NNReal ↦ (g y : ℝ≥0∞)) = Function.support g := by
  ext y
  simp [Function.mem_support]

/-- Helper for Corollary 24.18: the cutoff kernel is measurable whenever the original kernel is
measurable. -/
private lemma measurable_truncationKernel
    {g : NNReal → NNReal} (hg_meas : Measurable g) (n : ℕ) :
    Measurable (truncationKernel g n) := by
  have hmin : Measurable fun y : NNReal ↦ min (g y) n := hg_meas.min measurable_const
  simpa [truncationKernel] using
    hmin.piecewise (measurableSet_le measurable_id measurable_const) measurable_const

/-- Helper for Corollary 24.18: the `ENNReal` simple approximation vanishes wherever the target
function vanishes. -/
private lemma eapprox_eq_zero_of_eq_zero
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) {y : NNReal} (hy : g y = 0) :
    (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 := by
  apply le_antisymm
  · calc
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y
          ≤ ⨆ m,
              (MeasureTheory.SimpleFunc.eapprox g m : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y := by
              exact le_iSup
                (fun m ↦
                  (MeasureTheory.SimpleFunc.eapprox g m :
                    MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y)
                n
      _ = 0 := by
            simpa [hy] using MeasureTheory.SimpleFunc.iSup_eapprox_apply hg_meas y
  · exact bot_le

/-- Helper for Corollary 24.18: each simple approximation is supported inside the support of the
target function. -/
private lemma support_eapprox_subset_support
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) :
    Function.support (MeasureTheory.SimpleFunc.eapprox g n) ⊆ Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have happrox0 :
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 :=
    eapprox_eq_zero_of_eq_zero hg_meas n hg0
  exact hy happrox0

/-- Helper for Corollary 24.18: after converting the finite `ENNReal` simple approximation values
to `NNReal`, the support still stays inside the support of the original function. -/
private lemma support_eapproxToNNReal_subset_support
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) :
    Function.support ((MeasureTheory.SimpleFunc.eapprox g n).map ENNReal.toNNReal) ⊆
      Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have happrox0 :
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 :=
    eapprox_eq_zero_of_eq_zero hg_meas n hg0
  have hmap0 :
      ((MeasureTheory.SimpleFunc.eapprox g n).map ENNReal.toNNReal) y = 0 := by
    rw [MeasureTheory.SimpleFunc.map_apply, happrox0]
    simp
  exact hy hmap0

/-- Helper for Corollary 24.18: a bounded-support simple `ℝ≥0∞`-valued kernel with finite values
already satisfies the executable common-base Laplace identity in the `ennrealExpNeg` normal
form. -/
private lemma simpleFuncLaplaceTransformENNRealFiniteSupport
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    (s : MeasureTheory.SimpleFunc NNReal ℝ≥0∞)
    (hsupport_bdd : Bornology.IsBounded (Function.support s))
    (hsfinite : ∀ y, s y ≠ ∞) :
    ∫ ω, ennrealExpNeg (∫⁻ y, s y ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂nnrealLebesgue) := by
  let sNN : MeasureTheory.SimpleFunc NNReal NNReal := s.map ENNReal.toNNReal
  have hsNN_support_bdd :
      Bornology.IsBounded (Function.support sNN) := by
    refine hsupport_bdd.subset ?_
    intro y hy
    by_contra hsy
    have hs0 : s y = 0 := by
      simpa [Function.mem_support] using hsy
    have hsNN0 : sNN y = 0 := by
      rw [MeasureTheory.SimpleFunc.map_apply, hs0]
      simp [sNN]
    exact hy hsNN0
  have hsNN_eq : ∀ y, ((sNN y : NNReal) : ℝ≥0∞) = s y := by
    intro y
    rw [MeasureTheory.SimpleFunc.map_apply]
    simpa [sNN] using ENNReal.coe_toNNReal (hsfinite y)
  have hsNN_eq' : ∀ y, s y = ((sNN y : NNReal) : ℝ≥0∞) := by
    intro y
    symm
    exact hsNN_eq y
  have hkernel_nonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ)) := by
    filter_upwards with y
    have hle : Real.exp (-(sNN y : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [(sNN y).2]
    exact sub_nonneg.mpr hle
  have hkernel_meas :
      AEStronglyMeasurable (fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) nnrealLebesgue := by
    have hmeas : Measurable (fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_rewrite :
      ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂nnrealLebesgue := by
    refine lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
    calc
      ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ)))
          = ENNReal.ofReal (1 - Real.exp (-(s y).toReal)) := by
              have hs_toReal : (sNN y : ℝ) = (s y).toReal := by
                simpa using congrArg ENNReal.toReal (hsNN_eq y)
              rw [hs_toReal]
      _ = (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) := by
            symm
            exact poissonLaplaceKernel_eq_ofReal_of_neTop (hsfinite y)
  have hkernel_finite :
      ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂nnrealLebesgue < ∞ := by
    refine lintegral_ltTop_of_support_bounded_le_one ?_ ?_
    · refine hsupport_bdd.subset ?_
      intro y hy
      exact support_poissonLaplaceKernel_subset_support hy
    · intro y
      exact tsub_le_self
  have hkernel_integral :
      ∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue =
        ENNReal.toReal
          (∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue) :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hkernel_nonneg hkernel_meas
  have hkernel_finite' :
      ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue < ∞ := by
    rw [hkernel_rewrite]
    exact hkernel_finite
  calc
    ∫ ω, ennrealExpNeg (∫⁻ y, s y ∂ X ω) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (∫⁻ y, (sNN y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) := by
            congr 1
            funext ω
            congr 1
            exact lintegral_congr_ae <| Filter.Eventually.of_forall hsNN_eq'
    _ = Real.exp (∫ y : NNReal, (Real.exp (-(sNN y : ℝ)) - 1) ∂nnrealLebesgue) := by
          simpa [sNN] using simpleFuncLaplaceTransformNNReal P X hX sNN hsNN_support_bdd
    _ = Real.exp (-∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue) := by
          rw [bernsteinKernel_centeredIntegral_eq_neg]
    _ =
      ennrealExpNeg
        (∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂nnrealLebesgue) := by
          rw [ennrealExpNeg, if_neg hkernel_finite'.ne, ← hkernel_integral]
    _ =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂nnrealLebesgue) := by
          rw [hkernel_rewrite]

/-- Helper for Corollary 24.18: a bounded measurable deterministic Poisson integrand with bounded
support satisfies the executable common-base Laplace formula. -/
private theorem boundedSupportLaplaceTransformENNReal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hsupport_bdd : Bornology.IsBounded (Function.support g))
    (R : NNReal) (hbound : ∀ y, g y ≤ R) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂nnrealLebesgue) := by
  let gENN : NNReal → ℝ≥0∞ := fun y ↦ (g y : ℝ≥0∞)
  let s : ℕ → MeasureTheory.SimpleFunc NNReal ℝ≥0∞ := MeasureTheory.SimpleFunc.eapprox gENN
  have hgENN_meas : Measurable gENN := measurable_coe_nnreal_ennreal.comp hg_meas
  have hsFormula :
      ∀ k,
        ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)) ∂nnrealLebesgue) := by
    intro k
    refine simpleFuncLaplaceTransformENNRealFiniteSupport P X hX (s k) ?_ ?_
    · refine hsupport_bdd.subset ?_
      intro y hy
      simpa [gENN, support_coe_nnreal_ennreal g] using
        support_eapprox_subset_support hgENN_meas k hy
    · intro y
      exact (MeasureTheory.SimpleFunc.eapprox_lt_top gENN k y).ne
  rcases hsupport_bdd.subset_closedBall (0 : NNReal) with ⟨r, hr⟩
  let B : Set NNReal := Metric.closedBall (0 : NNReal) r
  have hB_meas : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hCountBall :
      ∀ᵐ ω ∂(P : Measure Ω), X ω B < ∞ :=
    poissonPointProcess_count_ae_ltTop P X hX hB_meas Metric.isBounded_closedBall
  have hg_bound_ball :
      ∀ y, gENN y ≤ Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ B
    · simpa [gENN, B, hy] using
        (show (g y : ℝ≥0∞) ≤ (R : ℝ≥0∞) by exact_mod_cast hbound y)
    · have hy_not_support : y ∉ Function.support g := by
        intro hy_support
        exact hy (hr hy_support)
      have hg0 : g y = 0 := by
        simpa [Function.mem_support] using hy_not_support
      simp [gENN, B, hy, hg0]
  have hs_bound_ball :
      ∀ k y, s k y ≤ Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y := by
    intro k y
    by_cases hy : y ∈ B
    · have hs_le_g : s k y ≤ gENN y := by
        calc
          s k y ≤ ⨆ m, s m y := le_iSup (fun m ↦ s m y) k
          _ = gENN y := by
                simpa [s, gENN] using MeasureTheory.SimpleFunc.iSup_eapprox_apply hgENN_meas y
      exact hs_le_g.trans (by simpa [B, hy] using hg_bound_ball y)
    · have hy_not_support_g : y ∉ Function.support g := by
        intro hy_support
        exact hy (hr hy_support)
      have hy_not_support_s : y ∉ Function.support (s k) := by
        intro hy_support
        exact hy_not_support_g <| by
          simpa [gENN, support_coe_nnreal_ennreal g] using
            support_eapprox_subset_support hgENN_meas k hy_support
      have hs0 : s k y = 0 := by
        simpa [Function.mem_support] using hy_not_support_s
      simp [B, hy, hs0]
  have hLeft_meas :
      ∀ k,
        AEStronglyMeasurable
          (fun ω ↦ ennrealExpNeg (∫⁻ y, s k y ∂ X ω)) (P : Measure Ω) := by
    intro k
    refine (measurable_ennrealExpNeg.comp ?_).aestronglyMeasurable
    refine (Measure.measurable_lintegral (s k).measurable).comp ?_
    exact hX.1.measurable
  have hLeft_bound :
      ∀ k,
        ∀ᵐ ω ∂(P : Measure Ω), ‖ennrealExpNeg (∫⁻ y, s k y ∂ X ω)‖ ≤ (1 : ℝ) := by
    intro k
    filter_upwards with ω
    have hnonneg : 0 ≤ ennrealExpNeg (∫⁻ y, s k y ∂ X ω) := ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ≤ 1 := ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLeft_lim :
      ∀ᵐ ω ∂(P : Measure Ω),
        Filter.Tendsto (fun k : ℕ ↦ ennrealExpNeg (∫⁻ y, s k y ∂ X ω))
          Filter.atTop (nhds (ennrealExpNeg (∫⁻ y, gENN y ∂ X ω))) := by
    filter_upwards [hCountBall] with ω hω
    let u : ℕ → ℝ≥0∞ := fun k ↦ ∫⁻ y, s k y ∂ X ω
    have hu_mono : Monotone u := by
      intro i j hij
      exact MeasureTheory.lintegral_mono fun y ↦ MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y
    have hu_finite : ∀ k, u k ≠ ∞ := by
      intro k
      have hu_le :
          u k ≤ ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω := by
        exact MeasureTheory.lintegral_mono (hs_bound_ball k)
      have hBoundedCell :
          ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω = (R : ℝ≥0∞) * X ω B := by
        rw [MeasureTheory.lintegral_indicator_const hB_meas]
      have hBoundedCell_lt :
          ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω < ∞ := by
        simpa [hBoundedCell] using ENNReal.mul_lt_top (by simp) hω
      refine (lt_of_le_of_lt ?_ hBoundedCell_lt).ne
      · simpa [u, hBoundedCell] using hu_le
    have hu_iSup : (⨆ k, u k) = ∫⁻ y, gENN y ∂ X ω := by
      calc
        (⨆ k, u k) = ⨆ k, (s k).lintegral (X ω) := by
          congr with k
          simpa [u] using (s k).lintegral_eq_lintegral (X ω)
        _ = ∫⁻ y, gENN y ∂ X ω := (MeasureTheory.lintegral_eq_iSup_eapprox_lintegral hgENN_meas).symm
    simpa [u, gENN] using tendsto_ennrealExpNeg_of_monotone_iSup hu_mono hu_finite hu_iSup
  have hLeft_tendsto :
      Filter.Tendsto
        (fun k : ℕ ↦ ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω))
        Filter.atTop
        (nhds (∫ ω, ennrealExpNeg (∫⁻ y, gENN y ∂ X ω) ∂(P : Measure Ω))) := by
    simpa [gENN] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : Ω ↦ (1 : ℝ)) hLeft_meas (integrable_const 1) hLeft_bound hLeft_lim
  let v : ℕ → ℝ≥0∞ := fun k ↦
    ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)) ∂nnrealLebesgue
  have hv_mono : Monotone v := by
    intro i j hij
    refine MeasureTheory.lintegral_mono fun y ↦ ?_
    exact poissonLaplaceKernel_mono
      (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
      (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
      (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y)
  have hv_finite : ∀ k, v k ≠ ∞ := by
    intro k
    have hkernel_support_bdd :
        Bornology.IsBounded
          (Function.support
            (fun y : NNReal ↦
              (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)))) := by
      refine hsupport_bdd.subset ?_
      intro y hy
      exact
        (by
          simpa [gENN, support_coe_nnreal_ennreal g] using
            support_eapprox_subset_support hgENN_meas k
              (support_poissonLaplaceKernel_subset_support hy))
    exact (lintegral_ltTop_of_support_bounded_le_one hkernel_support_bdd
      (fun y ↦ tsub_le_self)).ne
  have hv_iSup :
      (⨆ k, v k) =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂nnrealLebesgue := by
    calc
      (⨆ k, v k)
          =
        ∫⁻ y, ⨆ k, ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y))) ∂nnrealLebesgue := by
              symm
              exact MeasureTheory.lintegral_iSup
                (fun k ↦ by
                  exact measurable_const.sub
                    (ENNReal.measurable_ofReal.comp
                      (measurable_ennrealExpNeg.comp (s k).measurable)))
                (fun i j hij y ↦
                  poissonLaplaceKernel_mono
                    (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
                    (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
                    (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y))
      _ =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂nnrealLebesgue := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          let w : ℕ → ℝ≥0∞ := fun k ↦
            (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y))
          have hw_mono : Monotone w := by
            intro i j hij
            exact poissonLaplaceKernel_mono
              (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
              (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
              (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y)
          have hgENN_ne_top : gENN y ≠ ∞ := by
            simp [gENN]
          have hw_tendsto :
              Filter.Tendsto w Filter.atTop
                (nhds ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)))) := by
            have hs_tendsto :
                Filter.Tendsto (fun k : ℕ ↦ s k y) Filter.atTop (nhds (gENN y)) := by
              simpa [s, gENN] using MeasureTheory.SimpleFunc.tendsto_eapprox hgENN_meas y
            have hs_toReal_tendsto :
                Filter.Tendsto (fun k : ℕ ↦ (s k y).toReal) Filter.atTop (nhds (g y : ℝ)) := by
              exact (ENNReal.tendsto_toReal hgENN_ne_top).comp hs_tendsto
            have hkernel_tendsto :
                Filter.Tendsto
                  (fun k : ℕ ↦ ENNReal.ofReal (1 - Real.exp (-((s k y).toReal))))
                  Filter.atTop (nhds (ENNReal.ofReal (1 - Real.exp (-(g y : ℝ))))) := by
              have hcont : Continuous (fun r : ℝ ↦ ENNReal.ofReal (1 - Real.exp (-r))) :=
                ENNReal.continuous_ofReal.comp
                  (continuous_const.sub (Real.continuous_exp.comp continuous_neg))
              exact hcont.continuousAt.tendsto.comp hs_toReal_tendsto
            have hw_seq :
                (fun k : ℕ ↦ w k) =
                  fun k : ℕ ↦ ENNReal.ofReal (1 - Real.exp (-((s k y).toReal))) := by
              funext k
              simpa [w] using
                (poissonLaplaceKernel_eq_ofReal_of_neTop
                  (MeasureTheory.SimpleFunc.eapprox_lt_top gENN k y).ne)
            have hw_lim :
                (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) =
                  ENNReal.ofReal (1 - Real.exp (-(g y : ℝ))) := by
              simpa [gENN] using
                poissonLaplaceKernel_eq_ofReal_of_neTop hgENN_ne_top
            rw [hw_lim]
            simpa [w, hw_seq] using hkernel_tendsto
          exact tendsto_nhds_unique (tendsto_atTop_iSup hw_mono) hw_tendsto
  have hRight_tendsto :
      Filter.Tendsto (fun k : ℕ ↦ ennrealExpNeg (v k)) Filter.atTop
        (nhds
          (ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂nnrealLebesgue))) := by
    exact tendsto_ennrealExpNeg_of_monotone_iSup hv_mono hv_finite hv_iSup
  have hSeqEq :
      (fun k : ℕ ↦ ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω)) =
        (fun k : ℕ ↦ ennrealExpNeg (v k)) := by
    funext k
    simpa [v] using hsFormula k
  rw [hSeqEq] at hLeft_tendsto
  exact tendsto_nhds_unique hLeft_tendsto hRight_tendsto

/-- Helper for Corollary 24.18: the missing executable common-base `ENNReal` Laplace bridge for
deterministic Poisson integrands. -/
private theorem deterministicPoissonIntegral_laplaceTransformENNReal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞))
          ∂nnrealLebesgue) := by
  -- Route correction: `poisson_point_process_laplaceTransform` is only a source-facing `Prop`,
  -- so the executable bridge is rebuilt here from bounded-support simple approximations and
  -- monotone cutoff limits.
  let gCut : ℕ → NNReal → NNReal := fun n y ↦ truncationKernel g n y
  have hgCut_meas : ∀ n, Measurable (gCut n) := by
    intro n
    simpa [gCut] using measurable_truncationKernel hg_meas n
  have hCutFormula :
      ∀ n,
        ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞))
              ∂nnrealLebesgue) := by
    intro n
    refine boundedSupportLaplaceTransformENNReal P X hX (hgCut_meas n)
      (truncationSupport_isBounded g n) n ?_
    intro y
    by_cases hyn : y ≤ n
    · simp [gCut, truncationKernel, hyn]
    · simp [gCut, truncationKernel, hyn]
  have hCountAll :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ n : ℕ, X ω (Metric.closedBall (0 : NNReal) n) < ∞ := by
    rw [ae_all_iff]
    intro n
    exact poissonPointProcess_count_ae_ltTop P X hX
      (Metric.isClosed_closedBall.measurableSet) Metric.isBounded_closedBall
  have hLeft_meas :
      ∀ n,
        AEStronglyMeasurable
          (fun ω ↦ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω)) (P : Measure Ω) := by
    intro n
    refine (measurable_ennrealExpNeg.comp ?_).aestronglyMeasurable
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp (hgCut_meas n))).comp ?_
    exact hX.1.measurable
  have hLeft_bound :
      ∀ n,
        ∀ᵐ ω ∂(P : Measure Ω),
          ‖ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with ω
    have hnonneg : 0 ≤ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) := ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ≤ 1 := ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLeft_lim :
      ∀ᵐ ω ∂(P : Measure Ω),
        Filter.Tendsto
          (fun n : ℕ ↦ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω))
          Filter.atTop (nhds (ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω))) := by
    filter_upwards [hCountAll] with ω hω
    let u : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω
    have hu_mono : Monotone u := by
      intro i j hij
      exact MeasureTheory.lintegral_mono fun y ↦ by
        have hmono : gCut i y ≤ gCut j y := by
          simpa [gCut] using truncationKernel_mono g hij y
        simpa using (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
          exact_mod_cast hmono)
    have hu_finite : ∀ n, u n ≠ ∞ := by
      intro n
      have hu_le :
          u n ≤ ∫⁻ y,
            Set.indicator (Metric.closedBall (0 : NNReal) n)
              (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω := by
        refine MeasureTheory.lintegral_mono fun y ↦ ?_
        by_cases hyn : y ∈ Metric.closedBall (0 : NNReal) n
        · have hy_le : y ≤ n := by
            simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hyn
          simp [gCut, truncationKernel, hy_le, hyn]
        · have hy_not : ¬ y ≤ n := by
            intro hy_le
            exact hyn (by
              simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hy_le)
          simp [gCut, truncationKernel, hy_not, hyn]
      have hCell :
          ∫⁻ y,
              Set.indicator (Metric.closedBall (0 : NNReal) n)
                (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω =
            (n : ℝ≥0∞) * X ω (Metric.closedBall (0 : NNReal) n) := by
        rw [MeasureTheory.lintegral_indicator_const (Metric.isClosed_closedBall.measurableSet)]
      have hCell_lt :
          ∫⁻ y,
              Set.indicator (Metric.closedBall (0 : NNReal) n)
                (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω < ∞ := by
        simpa [hCell] using ENNReal.mul_lt_top (by simp) (hω n)
      refine (lt_of_le_of_lt ?_ hCell_lt).ne
      · simpa [u, hCell] using hu_le
    have hu_iSup : (⨆ n, u n) = ∫⁻ y, (g y : ℝ≥0∞) ∂ X ω := by
      calc
        (⨆ n, u n) = ∫⁻ y, ⨆ n, (gCut n y : ℝ≥0∞) ∂ X ω := by
          symm
          exact MeasureTheory.lintegral_iSup
            (fun n ↦ measurable_coe_nnreal_ennreal.comp (hgCut_meas n))
            (fun i j hij y ↦ by
              have hmono : gCut i y ≤ gCut j y := by
                simpa [gCut] using truncationKernel_mono g hij y
              simpa using (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
                exact_mod_cast hmono))
        _ = ∫⁻ y, (g y : ℝ≥0∞) ∂ X ω := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simpa [gCut] using iSup_truncationKernel_eq g y
    simpa [u] using tendsto_ennrealExpNeg_of_monotone_iSup hu_mono hu_finite hu_iSup
  have hLeft_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω))
        Filter.atTop
        (nhds (∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω))) := by
    simpa [gCut] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : Ω ↦ (1 : ℝ)) hLeft_meas (integrable_const 1) hLeft_bound hLeft_lim
  let v : ℕ → ℝ≥0∞ := fun n ↦
    ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)) ∂nnrealLebesgue
  have hv_mono : Monotone v := by
    intro i j hij
    refine MeasureTheory.lintegral_mono fun y ↦ ?_
    have hmono : gCut i y ≤ gCut j y := by
      simpa [gCut] using truncationKernel_mono g hij y
    exact poissonLaplaceKernel_mono (by simp) (by simp) <| by
      simpa using (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
        exact_mod_cast hmono)
  have hv_finite : ∀ n, v n ≠ ∞ := by
    intro n
    have hkernel_support_bdd :
        Bornology.IsBounded
          (Function.support
            (fun y : NNReal ↦
              (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)))) := by
      refine (truncationSupport_isBounded g n).subset ?_
      intro y hy
      simpa [gCut, support_coe_nnreal_ennreal (truncationKernel g n)] using
        support_poissonLaplaceKernel_subset_support hy
    exact (lintegral_ltTop_of_support_bounded_le_one hkernel_support_bdd
      (fun y ↦ tsub_le_self)).ne
  have hv_iSup :
      (⨆ n, v n) =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂nnrealLebesgue := by
    calc
      (⨆ n, v n)
          =
        ∫⁻ y, ⨆ n, ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)))
          ∂nnrealLebesgue := by
              symm
              exact MeasureTheory.lintegral_iSup
                (fun n ↦ by
                  exact measurable_const.sub
                    (ENNReal.measurable_ofReal.comp
                      (measurable_ennrealExpNeg.comp
                        (measurable_coe_nnreal_ennreal.comp (hgCut_meas n)))))
                (fun i j hij y ↦
                  by
                    have hmono : gCut i y ≤ gCut j y := by
                      simpa [gCut] using truncationKernel_mono g hij y
                    exact poissonLaplaceKernel_mono (by simp) (by simp)
                      (by
                        simpa using
                          (show ((gCut i y : NNReal) : ℝ≥0∞) ≤
                              ((gCut j y : NNReal) : ℝ≥0∞) by
                            exact_mod_cast hmono)))
      _ =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂nnrealLebesgue := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          refine le_antisymm ?_ ?_
          · exact iSup_le fun n ↦
              by
                have hle : gCut n y ≤ g y := by
                  simpa [gCut] using
                    (show truncationKernel g n y ≤ g y by
                      by_cases hyn : y ≤ n
                      · simp [truncationKernel, hyn]
                      · simp [truncationKernel, hyn])
                exact poissonLaplaceKernel_mono (by simp) (by simp) <| by
                  simpa using
                    (show ((gCut n y : NNReal) : ℝ≥0∞) ≤ (g y : ℝ≥0∞) by
                      exact_mod_cast hle)
          · rcases exists_nat_gt (max (y : ℝ) (g y : ℝ)) with ⟨n, hn⟩
            have hy_le : y ≤ n := by
              exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
            have hg_le : g y ≤ n := by
              exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
            refine le_iSup_of_le n ?_
            simp [gCut, truncationKernel, hy_le, min_eq_left hg_le]
  have hRight_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (v n)) Filter.atTop
        (nhds
          (ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞))
              ∂nnrealLebesgue))) := by
    exact tendsto_ennrealExpNeg_of_monotone_iSup hv_mono hv_finite hv_iSup
  have hSeqEq :
      (fun n : ℕ ↦
          ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω)) =
        (fun n : ℕ ↦ ennrealExpNeg (v n)) := by
    funext n
    simpa [v] using hCutFormula n
  rw [hSeqEq] at hLeft_tendsto
  exact tendsto_nhds_unique hLeft_tendsto hRight_tendsto

/-- Helper for Corollary 24.18: a measurable deterministic Poisson integrand with integrable
truncation has almost surely finite integral on the common base PPP. -/
private theorem deterministicPoissonIntegral_ae_ltTop_of_integrableMin
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hg_int : Integrable (fun y : NNReal ↦ min (1 : ℝ) (g y : ℝ)) nnrealLebesgue) :
    ∀ᵐ ω ∂(P : Measure Ω), (∫⁻ y, (g y : ENNReal) ∂ X ω) < ∞ := by
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ y, (g y : ENNReal) ∂ X ω
  let A : Set Ω := {ω | Y ω < ∞}
  let scaledG : ℕ → NonnegativeMeasurableFunction NNReal := fun n ↦
    ⟨fun y ↦ ENNReal.ofReal (invSuccScaleReal n) * g y,
      measurable_const.mul (measurable_coe_nnreal_ennreal.comp hg_meas)⟩
  let scaledExponent : ℕ → ℝ≥0∞ := fun n ↦
    ∫⁻ y,
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledG n y)) ∂nnrealLebesgue
  have hY_meas : Measurable Y := by
    -- Proof comment: the deterministic integral is measurable because the random measure map is.
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp hg_meas)).comp ?_
    exact hX.1.measurable
  have hA_meas : MeasurableSet A := measurableSet_lt hY_meas measurable_const
  have hs_nonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      positivity
    simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
  have hs_le_one : ∀ n, invSuccScaleReal n ≤ 1 := by
    intro n
    have hn : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith
    simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
  have hkernel_meas :
      ∀ n, AEStronglyMeasurable
        (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) nnrealLebesgue := by
    intro n
    have h : Measurable (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) := by
      fun_prop
    exact h.aestronglyMeasurable
  have hkernel_nonneg :
      ∀ n,
        0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) := by
    intro n
    filter_upwards with y
    have harg_nonneg : 0 ≤ invSuccScaleReal n * (g y : ℝ) := by
      nlinarith [hs_nonneg n, (g y).2]
    have hle : Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    exact sub_nonneg.mpr hle
  have hkernel_int :
      ∀ n,
        Integrable (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))))
          nnrealLebesgue := by
    intro n
    -- Proof comment: each scaled kernel is dominated by the truncated first-moment integrand.
    refine Integrable.mono' hg_int (hkernel_meas n) ?_
    filter_upwards with y
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) := by
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (g y : ℝ) := by
        nlinarith [hs_nonneg n, (g y).2]
      have hle : Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ min (1 : ℝ) (g y : ℝ) :=
      poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) (g y)
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      ∀ n,
        scaledExponent n =
          ENNReal.ofReal
            (∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue) := by
    intro n
    calc
      scaledExponent n
          =
        ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              simpa [scaledExponent, scaledG, ENNReal.ofReal_mul, hs_nonneg n] using
                poissonLaplaceKernel_scale_eq_ofReal (invSuccScaleReal n) (hs_nonneg n) (g y)
      _ =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hkernel_int n)
              (hkernel_nonneg n)
  have hLeft :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
          (P : Measure Ω))
        Filter.atTop (nhds ((P : Measure Ω) A).toReal) :=
    laplaceInvSucc_tendsto_measureFinite hY_meas
  have hRight :
      Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) Filter.atTop (nhds 1) := by
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) =
          (fun n : ℕ ↦
            Real.exp
              (-(∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))))
                  ∂nnrealLebesgue))) := by
      funext n
      have hIntegral_nonneg :
          0 ≤
            ∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue :=
        integral_nonneg_of_ae (hkernel_nonneg n)
      have hscaled_ne_top : scaledExponent n ≠ ∞ := by
        rw [hscaledExponent_eq n]
        exact ENNReal.ofReal_ne_top
      rw [ennrealExpNeg, if_neg hscaled_ne_top, hscaledExponent_eq n, ENNReal.toReal_ofReal
        hIntegral_nonneg]
    rw [hrewrite]
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    have hExponentZero :
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue)
          Filter.atTop (nhds 0) := by
      have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
        change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      have h_meas :
          ∀ n, AEStronglyMeasurable
            (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) nnrealLebesgue := by
        intro n
        exact hkernel_meas n
      have h_bound :
          ∀ n, ∀ᵐ y : NNReal ∂nnrealLebesgue,
            ‖1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))‖ ≤ min (1 : ℝ) (g y : ℝ) := by
        intro n
        filter_upwards with y
        have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) := by
          have harg_nonneg : 0 ≤ invSuccScaleReal n * (g y : ℝ) := by
            nlinarith [hs_nonneg n, (g y).2]
          have hle : Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ 1 := by
            refine Real.exp_le_one_iff.mpr ?_
            linarith
          exact sub_nonneg.mpr hle
        have hle :
            1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ min (1 : ℝ) (g y : ℝ) :=
          poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) (g y)
        simpa [Real.norm_of_nonneg hnonneg] using hle
      have h_lim :
          ∀ᵐ y : NNReal ∂nnrealLebesgue,
            Filter.Tendsto
              (fun n : ℕ ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) Filter.atTop
              (nhds 0) := by
        filter_upwards with y
        have hmul :
            Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * (g y : ℝ)) Filter.atTop
              (nhds (0 * (g y : ℝ))) := by
          exact hs.mul tendsto_const_nhds
        have hcontKernel : Continuous (fun r : ℝ ↦ 1 - Real.exp (-r)) := by
          simpa using continuous_const.sub (Real.continuous_exp.comp continuous_neg)
        simpa using hcontKernel.continuousAt.tendsto.comp hmul
      -- Proof comment: dominated convergence makes the deterministic exponent vanish.
      simpa using
        MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun y : NNReal ↦ min (1 : ℝ) (g y : ℝ)) h_meas hg_int h_bound h_lim
    simpa using hcont.continuousAt.tendsto.comp hExponentZero
  have hLaplaceScaled :
      ∀ n,
        ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω) =
          ennrealExpNeg (scaledExponent n) := by
    intro n
    -- Proof comment: specialize the PPP Laplace transform to the scaled deterministic integrand.
    have hlintegral :
        (fun ω ↦ ∫⁻ y, scaledG n y ∂ X ω) =
          (fun ω ↦ ENNReal.ofReal (invSuccScaleReal n) * Y ω) := by
      funext ω
      simpa [scaledG, Y] using
        (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (invSuccScaleReal n))
          (fun y : NNReal ↦ (g y : ℝ≥0∞))
          ENNReal.ofReal_ne_top)
    have hraw :
        ∫ ω, ennrealExpNeg (∫⁻ y, scaledG n y ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg (scaledExponent n) := by
      let c : NNReal := ⟨invSuccScaleReal n, hs_nonneg n⟩
      let scaledKernel : NNReal → NNReal :=
        fun y ↦ c * g y
      have hscaledKernel_meas : Measurable scaledKernel := by
        simpa [scaledKernel] using measurable_const.mul hg_meas
      have hc : (c : ℝ≥0∞) = ENNReal.ofReal (invSuccScaleReal n) := by
        simpa [c] using ENNReal.coe_nnreal_eq c
      simpa [scaledExponent, scaledG, scaledKernel, c, hc, ENNReal.ofReal_mul, hs_nonneg n] using
        (deterministicPoissonIntegral_laplaceTransformENNReal
          (P := P) (X := X) hX (g := scaledKernel) hscaledKernel_meas)
    have hleftRewrite :
        (fun ω ↦ ennrealExpNeg (∫⁻ y, scaledG n y ∂ X ω)) =
          (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)) := by
      funext ω
      simpa using congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    simpa [hleftRewrite] using hraw
  have hLeftOne :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
          (P : Measure Ω))
        Filter.atTop (nhds 1) := by
    simpa [hLaplaceScaled] using hRight
  have hToRealOne : ((P : Measure Ω) A).toReal = 1 :=
    tendsto_nhds_unique hLeft hLeftOne
  have hPA : (P : Measure Ω) A = 1 :=
    (ENNReal.toReal_eq_one_iff ((P : Measure Ω) A)).mp hToRealOne
  exact (mem_ae_iff_prob_eq_one hA_meas).2 hPA

/-- Helper for Corollary 24.18: the common-base deterministic Poisson integral satisfies the
standard Laplace transform formula once its truncation kernel is integrable. -/
private theorem deterministicPoissonIntegral_laplaceFormula
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hg_int : Integrable (fun y : NNReal ↦ min (1 : ℝ) (g y : ℝ)) nnrealLebesgue) :
    ∀ t : NNReal,
      ∫ ω, Real.exp (-((t : ℝ) * (∫⁻ y, (g y : ENNReal) ∂ X ω).toReal)) ∂(P : Measure Ω) =
        Real.exp (∫ y : NNReal, (Real.exp (-((t : ℝ) * (g y : ℝ))) - 1) ∂nnrealLebesgue) := by
  intro t
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ y, (g y : ENNReal) ∂ X ω
  let scaledG : NonnegativeMeasurableFunction NNReal :=
    ⟨fun y ↦ ENNReal.ofReal (t : ℝ) * g y,
      measurable_const.mul (measurable_coe_nnreal_ennreal.comp hg_meas)⟩
  let scaledExponent : ℝ≥0∞ := ∫⁻ y,
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledG y)) ∂nnrealLebesgue
  have hY_meas : Measurable Y := by
    -- Proof comment: measurability is inherited from the random-measure map.
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp hg_meas)).comp ?_
    exact hX.1.measurable
  have hAeFinite :
      ∀ᵐ ω ∂(P : Measure Ω), Y ω < ∞ :=
    deterministicPoissonIntegral_ae_ltTop_of_integrableMin P X hX hg_meas hg_int
  have hs_nonneg : 0 ≤ (t : ℝ) := t.2
  have hkernel_meas :
      AEStronglyMeasurable
        (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) nnrealLebesgue := by
    have hmeas : Measurable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_nonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ))) := by
    filter_upwards with y
    have hle : Real.exp (-((t : ℝ) * (g y : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [t.2, (g y).2]
    exact sub_nonneg.mpr hle
  have hkernel_int :
      Integrable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) nnrealLebesgue := by
    have hdom :
        Integrable (fun y : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (g y : ℝ)) nnrealLebesgue :=
      hg_int.const_mul (max 1 (t : ℝ))
    refine Integrable.mono' hdom hkernel_meas ?_
    filter_upwards with y
    have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (g y : ℝ))) := by
      have hle : Real.exp (-((t : ℝ) * (g y : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [t.2, (g y).2]
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-((t : ℝ) * (g y : ℝ))) ≤
          max 1 (t : ℝ) * min (1 : ℝ) (g y : ℝ) :=
      poissonExpKernel_scale_le_maxMulMinOne (t : ℝ) hs_nonneg (g y)
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      scaledExponent =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) := by
    calc
      scaledExponent
          =
        ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              simpa [scaledExponent, scaledG, ENNReal.ofReal_mul, hs_nonneg] using
                poissonLaplaceKernel_scale_eq_ofReal (t : ℝ) hs_nonneg (g y)
      _ =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
  have hraw :
      ∫ ω, ennrealExpNeg (∫⁻ y, scaledG y ∂ X ω) ∂(P : Measure Ω) =
        ennrealExpNeg scaledExponent := by
    let scaledKernel : NNReal → NNReal := fun y ↦ t * g y
    have hscaledKernel_meas : Measurable scaledKernel := by
      simpa [scaledKernel] using measurable_const.mul hg_meas
    simpa [scaledExponent, scaledG, scaledKernel, ENNReal.ofReal_mul, hs_nonneg] using
      (deterministicPoissonIntegral_laplaceTransformENNReal
        (P := P) (X := X) hX (g := scaledKernel) hscaledKernel_meas)
  have hlintegral :
      (fun ω ↦ ∫⁻ y, scaledG y ∂ X ω) =
        fun ω ↦ ENNReal.ofReal (t : ℝ) * Y ω := by
    funext ω
    simpa [scaledG, Y] using
      (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (t : ℝ))
        (fun y : NNReal ↦ (g y : ℝ≥0∞))
        ENNReal.ofReal_ne_top)
  have hleft_ae :
      (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω)) =ᵐ[(P : Measure Ω)]
        (fun ω ↦ Real.exp (-((t : ℝ) * (Y ω).toReal))) := by
    filter_upwards [hAeFinite] with ω hω
    have hω_ne_top : Y ω ≠ ∞ := lt_top_iff_ne_top.mp hω
    have hmul_ne_top : ENNReal.ofReal (t : ℝ) * Y ω ≠ ∞ :=
      ENNReal.mul_ne_top (by simp [t.2]) hω_ne_top
    rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
    simpa using congrArg (fun r : ℝ ↦ Real.exp (-(r * (Y ω).toReal)))
      (ENNReal.toReal_ofReal t.2)
  calc
    ∫ ω, Real.exp (-((t : ℝ) * (∫⁻ y, (g y : ENNReal) ∂ X ω).toReal)) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω) ∂(P : Measure Ω) := by
            -- Proof comment: on the almost-sure finite event, `ennrealExpNeg` becomes the
            -- ordinary exponential.
            symm
            exact integral_congr_ae hleft_ae
    _ = ∫ ω, ennrealExpNeg (∫⁻ y, scaledG y ∂ X ω) ∂(P : Measure Ω) := by
          congr 1
          funext ω
          symm
          exact congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    _ = ennrealExpNeg scaledExponent := hraw
    _ = Real.exp (∫ y : NNReal, (Real.exp (-((t : ℝ) * (g y : ℝ))) - 1) ∂nnrealLebesgue) := by
          rw [hscaledExponent_eq, ennrealExpNeg]
          have hIntegral_nonneg :
              0 ≤ ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue :=
            integral_nonneg_of_ae hkernel_nonneg
          simp [hIntegral_nonneg]
          rw [show
              -(∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) =
                ∫ y : NNReal, -(1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue by
                symm
                exact integral_neg (f := fun y : NNReal ↦
                  1 - Real.exp (-((t : ℝ) * (g y : ℝ))))]
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          ring

/-- Helper for Corollary 24.18: the common-base tail-quantile Poisson integral is almost surely
finite under a subordinator Lévy--Khinchin representation. -/
private lemma tailQuantileIntegral_ae_ltTop_of_rep
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    ∀ᵐ ω ∂(P : Measure Ω), (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω) < ∞ := by
  -- Route correction: reuse the repaired common-base finiteness theorem instead of rebuilding
  -- the bad `ennrealExpNeg` bridge locally.
  simpa using
    deterministicPoissonIntegral_ae_ltTop_of_integrableMin
      P X hX (g := tailQuantile ν)
      (measurable_tailQuantile_of_rep hrep)
      (tailQuantile_integrableMin_nnrealLebesgue hrep)

/-- Helper for Corollary 24.18: the tail-quantile integral on the common base Poisson point
process satisfies the expected Laplace transform formula. -/
private lemma tailQuantileIntegral_laplaceFormula_of_rep
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    ∀ t : NNReal,
      ∫ ω, Real.exp (-((t : ℝ) * (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp
          (∫ y : NNReal, (Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) - 1)
            ∂nnrealLebesgue) := by
  intro t
  -- Route correction: specialize the repaired real-valued common-base Laplace formula to the
  -- tail-quantile kernel and keep the downstream law-identification proof unchanged.
  simpa using
    deterministicPoissonIntegral_laplaceFormula
      P X hX (g := tailQuantile ν)
      (measurable_tailQuantile_of_rep hrep)
      (tailQuantile_integrableMin_nnrealLebesgue hrep) t

/-- Helper for Corollary 24.18: the tail-quantile integral over one common base Poisson point
process has the prescribed Lévy--Khinchin law. -/
private lemma tailQuantileIntegral_hasLaw_of_rep
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    HasLaw
      (fun ω ↦ α + (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toNNReal)
      (μ : Measure NNReal) (P : Measure Ω) := by
  -- Route correction: the image-process route is still unavailable because the image intensity of
  -- `tailQuantile ν` need not be locally finite near `0`. The proof therefore stays on the
  -- common `nnrealLebesgue` PPP and identifies the pushforward law by Laplace transforms.
  let ξ : Ω → NNReal := fun ω ↦
    α + (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toNNReal
  have htail_meas : Measurable (tailQuantile ν) := measurable_tailQuantile_of_rep hrep
  have hIntegral_meas :
      Measurable (fun ω ↦ ∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω) := by
    -- Proof comment: measurability comes from the random-measure map and the measurable
    -- deterministic tail quantile.
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp htail_meas)).comp ?_
    exact hX.1.measurable
  have hξ_meas : Measurable ξ := by
    -- Proof comment: `toNNReal` turns the extended integral into the finite-valued random
    -- variable used in the coupling.
    simpa [ξ] using measurable_const.add (ENNReal.measurable_toNNReal.comp hIntegral_meas)
  let μξ : ProbabilityMeasure NNReal := ProbabilityMeasure.map P hξ_meas.aemeasurable
  have hLawXi : HasLaw ξ (μξ : Measure NNReal) (P : Measure Ω) := by
    refine ⟨hξ_meas.aemeasurable, ?_⟩
    rfl
  have htail_int :
      Integrable (fun y : NNReal ↦ min (1 : ℝ) (tailQuantile ν y : ℝ)) nnrealLebesgue :=
    tailQuantile_integrableMin_nnrealLebesgue hrep
  have hLaplaceXi :
      ∀ t : NNReal,
        ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μξ : Measure NNReal) =
          Real.exp
            (-(((α : ℝ) * (t : ℝ)) +
              ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν)) := by
    intro t
    have hkernel_meas :
        AEStronglyMeasurable
          (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))))
          (μξ : Measure NNReal) := by
      have hmeas : Measurable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ)))) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    have hLaplaceMap :
        ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μξ : Measure NNReal) =
          ∫ ω, Real.exp (-((t : ℝ) * (ξ ω : ℝ))) ∂(P : Measure Ω) := by
      symm
      exact hLawXi.integral_comp hkernel_meas
    have hSplit :
        ∫ ω, Real.exp (-((t : ℝ) * (ξ ω : ℝ))) ∂(P : Measure Ω) =
          Real.exp (-((t : ℝ) * (α : ℝ))) *
            ∫ ω,
              Real.exp
                (-((t : ℝ) *
                  (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal)) ∂(P : Measure Ω) := by
      calc
        ∫ ω, Real.exp (-((t : ℝ) * (ξ ω : ℝ))) ∂(P : Measure Ω)
            =
          ∫ ω,
            Real.exp (-((t : ℝ) * (α : ℝ))) *
              Real.exp
                (-((t : ℝ) * (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal)) ∂
            (P : Measure Ω) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              simp [ξ, ENNReal.coe_toNNReal_eq_toReal, mul_add, Real.exp_add, mul_comm,
                mul_left_comm, mul_assoc]
        _ =
          Real.exp (-((t : ℝ) * (α : ℝ))) *
            ∫ ω,
              Real.exp
                (-((t : ℝ) * (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal)) ∂
              (P : Measure Ω) := by
                rw [integral_const_mul]
    have hIntegralLaw :
        ∫ ω,
          Real.exp
            (-((t : ℝ) * (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal)) ∂
          (P : Measure Ω) =
            Real.exp
              (∫ y : NNReal,
                (Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) - 1) ∂nnrealLebesgue) := by
      simpa using tailQuantileIntegral_laplaceFormula_of_rep P X hX hrep t
    have hkernel_eq :
        ∫ y : NNReal, (Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) - 1) ∂nnrealLebesgue =
          -∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂nnrealLebesgue := by
      simpa using
        (bernsteinKernel_centeredIntegral_eq_neg
          (ρ := nnrealLebesgue)
          (f := fun y : NNReal ↦ (t : ℝ) * (tailQuantile ν y : ℝ)))
    calc
      ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μξ : Measure NNReal)
          = ∫ ω, Real.exp (-((t : ℝ) * (ξ ω : ℝ))) ∂(P : Measure Ω) := hLaplaceMap
      _ = Real.exp (-((t : ℝ) * (α : ℝ))) *
            ∫ ω,
              Real.exp
                (-((t : ℝ) * (∫⁻ y, (tailQuantile ν y : ENNReal) ∂ X ω).toReal)) ∂
              (P : Measure Ω) := hSplit
      _ = Real.exp (-((t : ℝ) * (α : ℝ))) *
            Real.exp
              (∫ y : NNReal,
                (Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ))) - 1) ∂nnrealLebesgue) := by
              rw [hIntegralLaw]
      _ = Real.exp
            (-(((α : ℝ) * (t : ℝ)) +
              ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (tailQuantile ν y : ℝ)))) ∂
                nnrealLebesgue)) := by
              rw [hkernel_eq, ← Real.exp_add]
              congr 1
              ring
      _ = Real.exp
            (-(((α : ℝ) * (t : ℝ)) +
              ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν)) := by
              rw [tailQuantile_bernsteinKernelIntegral_eq_of_rep hrep t]
  have hLaplaceMu :
      ∀ t : NNReal,
        ∫ x : NNReal, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) =
          Real.exp
            (-(((α : ℝ) * (t : ℝ)) +
              ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν)) := by
    intro t
    let f : NNReal → ℝ := fun x ↦ Real.exp (-((t : ℝ) * (x : ℝ)))
    have hf_meas : AEStronglyMeasurable f (μ : Measure NNReal) := by
      have hmeas : Measurable f := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    have hf_int : Integrable f (μ : Measure NNReal) := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hf_meas ?_
      filter_upwards with x
      have hnonneg : 0 ≤ f x := (Real.exp_pos _).le
      have hle : f x ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [t.2, x.2]
      simpa [f, Real.norm_of_nonneg hnonneg] using hle
    have hf_nonneg : ∀ x : NNReal, 0 ≤ f x := fun x ↦ (Real.exp_pos _).le
    have hsupp : Function.support f = Set.univ := by
      ext x
      simp [f, Real.exp_pos]
    have hLaplacePos :
        0 < ∫ x : NNReal, f x ∂(μ : Measure NNReal) := by
      rw [MeasureTheory.integral_pos_iff_support_of_nonneg hf_nonneg hf_int, hsupp]
      simpa using (show (0 : ℝ≥0∞) < (μ : Measure NNReal) Set.univ by simp)
    have hlog :
        logLaplaceTransform μ t =
          ((α : ℝ) * (t : ℝ)) +
            ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν :=
      hrep.2.2 t
    rw [logLaplaceTransform] at hlog
    have hlog' :
        Real.log (∫ x : NNReal, f x ∂(μ : Measure NNReal)) =
          -(((α : ℝ) * (t : ℝ)) +
            ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
      -- Proof comment: negate the log-Laplace identity once to isolate the ordinary logarithm.
      simpa using congrArg Neg.neg hlog
    have hExp := congrArg Real.exp hlog'
    simpa [f, Real.exp_log hLaplacePos] using hExp
  have hMeasureEqFinite : μξ.toFiniteMeasure = μ.toFiniteMeasure := by
    refine (MeasureTheory.FiniteMeasure.ext_iff_laplaceTransform_eq _ _).2 ?_
    intro t
    rw [MeasureTheory.FiniteMeasure.laplaceTransform_def,
      MeasureTheory.FiniteMeasure.laplaceTransform_def]
    exact (hLaplaceXi t).trans (hLaplaceMu t).symm
  have hMeasureEq : (μξ : Measure NNReal) = (μ : Measure NNReal) := by
    exact congrArg (fun ρ : FiniteMeasure NNReal ↦ (ρ : Measure NNReal)) hMeasureEqFinite
  -- Proof comment: the pushforward law of `ξ` is `μξ`; the Laplace comparison identifies `μξ`
  -- with the target law `μ`.
  simpa [ξ, hMeasureEq] using hLawXi

-- Proof sketch: represent each law by the Chapter 16 Lévy--Khinchin data `(αᵢ, νᵢ)` and use the
-- Poisson-point-process construction from Theorems 24.16 and 24.17. Pushing one Poisson point
-- process with Lebesgue intensity through the generalized inverse of the tail functions
-- `x ↦ νᵢ (Set.Ici x)` gives coupled random variables with laws `μᵢ`; the tail comparison forces
-- the first inverse and hence the first random variable to be pointwise smaller. The resulting
-- almost sure order implies stochastic order.
/-- Corollary 24.18: if two infinitely divisible probability laws on `[0, ∞)` have
Lévy--Khinchin data `(α₁, ν₁)` and `(α₂, ν₂)` with `α₁ ≤ α₂` and
`ν₁([x, ∞)) ≤ ν₂([x, ∞))` for every `x > 0`, then the first law is stochastically smaller than
the second. On `NNReal`, the tail sets `[x, ∞)` are represented by `Set.Ici x`. -/
theorem levyKhinchin_tail_order_implies_nnrealStochasticLE
    {μ₁ μ₂ : ProbabilityMeasure NNReal} {α₁ α₂ : NNReal} {ν₁ ν₂ : Measure NNReal}
    (hrep₁ : HasSubordinatorLevyKhinchinRepresentation μ₁ α₁ ν₁)
    (hrep₂ : HasSubordinatorLevyKhinchinRepresentation μ₂ α₂ ν₂)
    (hα : α₁ ≤ α₂)
    (hν : ∀ x : NNReal, 0 < x → ν₁ (Set.Ici x) ≤ ν₂ (Set.Ici x)) :
    NNRealStochasticLE μ₁ μ₂ := by
  have hTailQuantile :
      ∀ y : NNReal, tailQuantile ν₁ y ≤ tailQuantile ν₂ y := by
    intro y
    exact tailQuantile_le_of_tail_order hrep₂ hν y
  obtain ⟨Ω, hΩ, P, X, hX_raw⟩ :
      ∃ (Ω : Type) (hΩ : MeasurableSpace Ω) (P : @ProbabilityMeasure Ω hΩ)
        (X : Ω → Measure NNReal), ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X :=
    ProbabilityTheory.exists_poisson_point_process_with_intensity_measure
      nnrealLebesgueBoundedlyFinite
  letI : MeasurableSpace Ω := hΩ
  have hX :
      ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X := by
    simpa using hX_raw
  let Y₁ : Ω → NNReal := fun ω ↦
    α₁ + (∫⁻ y, (tailQuantile ν₁ y : ENNReal) ∂ X ω).toNNReal
  let Y₂ : Ω → NNReal := fun ω ↦
    α₂ + (∫⁻ y, (tailQuantile ν₂ y : ENNReal) ∂ X ω).toNNReal
  have hLaw₁ : HasLaw Y₁ (μ₁ : Measure NNReal) (P : Measure Ω) := by
    -- Proof comment: the whole law-identification burden is now isolated in the common-base
    -- tail-quantile integral package.
    simpa [Y₁] using tailQuantileIntegral_hasLaw_of_rep P X hX hrep₁
  have hLaw₂ : HasLaw Y₂ (μ₂ : Measure NNReal) (P : Measure Ω) := by
    -- Proof comment: the same common-base law package is used for the second Lévy pair.
    simpa [Y₂] using tailQuantileIntegral_hasLaw_of_rep P X hX hrep₂
  have hOrdered : ∀ᵐ ω ∂(P : Measure Ω), Y₁ ω ≤ Y₂ ω := by
    -- Proof comment: the pointwise tail-quantile order and the deterministic drift order imply
    -- pathwise order of the two coupled Poisson integrals on the shared base process.
    have hfinite₁ :
        ∀ᵐ ω ∂(P : Measure Ω), (∫⁻ y, (tailQuantile ν₁ y : ENNReal) ∂ X ω) < ∞ :=
      tailQuantileIntegral_ae_ltTop_of_rep P X hX hrep₁
    have hfinite₂ :
        ∀ᵐ ω ∂(P : Measure Ω), (∫⁻ y, (tailQuantile ν₂ y : ENNReal) ∂ X ω) < ∞ :=
      tailQuantileIntegral_ae_ltTop_of_rep P X hX hrep₂
    filter_upwards [hfinite₁, hfinite₂] with ω hω₁ hω₂
    dsimp [Y₁, Y₂]
    refine add_le_add hα ?_
    refine
      (ENNReal.toNNReal_le_toNNReal
        (lt_top_iff_ne_top.mp hω₁)
        (lt_top_iff_ne_top.mp hω₂)).2 ?_
    refine lintegral_mono fun y ↦ ?_
    exact ENNReal.coe_le_coe.2 (hTailQuantile y)
  -- Proof comment: after packaging both laws on one space, the stochastic-order conclusion is the
  -- general ordered-coupling lemma proved at the beginning of the file.
  exact orderedHasLaw_imp_nnrealStochasticLE hLaw₁ hLaw₂ hOrdered

end MeasureTheory.ProbabilityMeasure

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 24.17: the extended-real Laplace kernel is `0` at `∞` and otherwise
equals `exp (-t.toReal)`. -/
private def ennrealExpNeg (t : ℝ≥0∞) : ℝ :=
  if t = ∞ then 0 else Real.exp (-t.toReal)

/-- Helper for Theorem 24.17: the extended-real Laplace kernel vanishes at `∞`. -/
private lemma ennrealExpNeg_top : ennrealExpNeg ∞ = 0 := by
  simp [ennrealExpNeg]

/-- Helper for Theorem 24.17: the extended-real Laplace kernel is `0` at `∞` and otherwise
equals `exp (-t.toReal)`. -/
private def ennrealExpNeg (t : ℝ≥0∞) : ℝ :=
  if t = ∞ then 0 else Real.exp (-t.toReal)

/-- Helper for Theorem 24.17: the extended-real Laplace kernel vanishes at `∞`. -/
private lemma ennrealExpNeg_top : ennrealExpNeg ∞ = 0 := by
  simp [ennrealExpNeg]

/-- A Poisson point process on `ℝ≥0` with intensity measure `ν` is a random measure with
independent increments whose bounded measurable-set counts have the corresponding Poisson laws. -/
def IsPoissonPointProcessOnNNReal
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal) : Prop :=
  IsRandomMeasure P X ∧
    HasIndependentIncrements P X ∧
    IsLocallyFiniteMeasure ν ∧
    ∀ ⦃A : Set NNReal⦄, MeasurableSet A → Bornology.IsBounded A → ν A ≠ ∞ →
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
        (P : Measure Ω)

-- Proof sketch: unfold `IsPoissonPointProcessOnNNReal`; the statement is exactly the conjunction
-- of the random-measure property, independent increments, local finiteness of `ν`, and the
-- Poisson law for every bounded measurable-set count.
/-- Unfolding `IsPoissonPointProcessOnNNReal` gives the random-measure, independent-increments,
local-finiteness, and Poisson marginal clauses. -/
theorem isPoissonPointProcessOnNNReal_iff
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal) :
    IsPoissonPointProcessOnNNReal ν P X ↔
      IsRandomMeasure P X ∧
        HasIndependentIncrements P X ∧
        IsLocallyFiniteMeasure ν ∧
        ∀ ⦃A : Set NNReal⦄, MeasurableSet A → Bornology.IsBounded A → ν A ≠ ∞ →
          HasLaw (fun ω ↦ X ω A)
            (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
            (P : Measure Ω) := by
  -- Proof comment: the theorem is the direct unfolding of the defining conjunction.
  rfl

/-- The Poisson stochastic integral `∫ x X(dx)` of a random measure on `ℝ≥0` with respect to the
identity integrand. -/
def poissonPointIntegral (X : Ω → Measure NNReal) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ∂X ω

-- Proof sketch: unfold `poissonPointIntegral`; it is exactly the `lintegral` of the identity
-- function against the random measure `X ω`.
/-- Unfolding `poissonPointIntegral` gives the textbook random sum `∫ x X(dx)` as a nonnegative
Lebesgue integral. -/
theorem poissonPointIntegral_def (X : Ω → Measure NNReal) (ω : Ω) :
    poissonPointIntegral X ω = ∫⁻ x, (x : ℝ≥0∞) ∂X ω := by
  -- Proof comment: the stochastic integral notation is defined by this `lintegral`.
  rfl

/-- Helper for Theorem 24.17: the Poisson Laplace kernel is bounded above by the textbook
truncation kernel `x ↦ min 1 x` on `[0, ∞)`. -/
private lemma one_sub_expNeg_le_min_one (x : ℝ) :
    1 - Real.exp (-x) ≤ min 1 x := by
  -- Proof comment: the standard tangent-line bound gives the `≤ x` half of the truncation
  -- comparison.
  have hx_le : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  -- Proof comment: positivity of the exponential gives the uniform `≤ 1` half.
  have h_one : 1 - Real.exp (-x) ≤ 1 := by
    have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
    linarith
  exact le_min h_one hx_le

/-- Helper for Theorem 24.17: the fixed lower-comparison constant in the Laplace-kernel estimate
is strictly positive. -/
private lemma poissonExpKernelLowerConst_pos :
    0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
  -- Proof comment: `exp (-1/2)` is strictly below `1`, so the displayed gap is positive.
  have hhalf_neg : -(1 / 2 : ℝ) < 0 := by
    norm_num
  have hlt : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    calc
      Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr hhalf_neg
      _ = 1 := by simp
  linarith

/-- Helper for Theorem 24.17: on `[0, 1]`, the Poisson Laplace kernel dominates a fixed positive
multiple of `x`. -/
private lemma poissonExpKernel_lower_on_unitInterval
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ 1 - Real.exp (-x) := by
  by_cases hhalf : x ≤ 1 / 2
  · -- Proof comment: for small `x`, the quadratic remainder bound for `exp (-x)` yields a
    -- linear lower estimate.
    have habs_arg : |(-x : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hrem :
        |Real.exp (-x) - 1 + x| ≤ x ^ 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, pow_two] using
        (Real.abs_exp_sub_one_sub_id_le habs_arg)
    have hquad :
        Real.exp (-x) - 1 + x ≤ x ^ 2 := by
      exact le_trans (le_abs_self _) hrem
    have hhalfCoeff : 1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      have hExpLower : 1 - (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) :=
        Real.one_sub_le_exp_neg (1 / 2 : ℝ)
      linarith
    have hcoeffMul : (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ x / 2 := by
      nlinarith
    have hlinear : x / 2 ≤ x - x ^ 2 := by
      nlinarith
    linarith
  · -- Proof comment: once `x` is bounded away from `0`, monotonicity of the Laplace kernel
    -- gives a uniform positive lower bound, and `x ≤ 1` turns that into the required multiple.
    have hhalf_lt : 1 / 2 < x := by
      linarith
    have hmono :
        Real.exp (-x) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hconst_le :
        1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 - Real.exp (-x) := by
      linarith
    have hcoeff_nonneg : 0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
      exact le_of_lt poissonExpKernelLowerConst_pos
    have hmul_le :
        (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
      nlinarith
    exact le_trans hmul_le hconst_le

/-- Helper for Theorem 24.17: the Poisson Laplace kernel dominates a fixed positive multiple of
the truncation kernel `x ↦ min 1 x` on `[0, ∞)`. -/
private lemma poissonExpKernel_lower_mul_min (x : ℝ) (hx : 0 ≤ x) :
    (1 - Real.exp (-(1 / 2 : ℝ))) * min 1 x ≤ 1 - Real.exp (-x) := by
  by_cases hx1 : x ≤ 1
  · -- Proof comment: on `[0, 1]` the truncation kernel is just `x`, so the unit-interval lower
    -- bound applies directly.
    simpa [min_eq_right hx1] using poissonExpKernel_lower_on_unitInterval x hx hx1
  · -- Proof comment: on `[1, ∞)` the truncation kernel is constantly `1`, and monotonicity gives
    -- the same fixed lower bound.
    have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hmono :
        Real.exp (-x) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hconst_le :
        1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 - Real.exp (-x) := by
      linarith
    simpa [min_eq_left hx1'] using hconst_le

/-- Helper for Theorem 24.17: the Poisson stochastic integral is measurable because it is the
`lintegral` of the identity against the measurable random-measure map. -/
private lemma poissonPointIntegral_measurable
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X) :
    Measurable (poissonPointIntegral X) := by
  rcases (isPoissonPointProcessOnNNReal_iff ν P X).1 hX with ⟨hRandom, _, _, _⟩
  -- Proof comment: compose the measurable measure-evaluation map `μ ↦ ∫ x ∂μ` with the random
  -- measure `X`.
  simpa [poissonPointIntegral_def] using
    (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp hRandom.measurable

/-- Helper for Theorem 24.17: on `ℝ≥0`, the Laplace kernel from Theorem 24.14 is the `ENNReal`
lift of the real kernel `x ↦ 1 - exp (-x)`. -/
private lemma poissonLaplaceKernel_eq_ofReal (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (x : ℝ≥0∞)) =
      ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) := by
  -- Proof comment: `x` is finite, so `ennrealExpNeg x` reduces to the ordinary exponential and
  -- the remaining subtraction is an `ofReal_sub` rewrite.
  have hExpNonneg : 0 ≤ Real.exp (-(x : ℝ)) := Real.exp_nonneg _
  simp [ennrealExpNeg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Theorem 24.17: the Laplace exponent kernel is integrable exactly when the textbook
truncation kernel `x ↦ min 1 x` is integrable. -/
private lemma poissonLaplaceKernel_integrable_iff
    (ν : Measure NNReal) :
    Integrable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν ↔
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
  let k : NNReal → ℝ := fun x ↦ 1 - Real.exp (-(x : ℝ))
  let m : NNReal → ℝ := fun x ↦ min (1 : ℝ) (x : ℝ)
  have hk_nonneg : ∀ x : NNReal, 0 ≤ k x := by
    intro x
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by simpa using x.2))
  have hm_nonneg : ∀ x : NNReal, 0 ≤ m x := by
    intro x
    exact le_min zero_le_one x.2
  have hk_meas : AEStronglyMeasurable k ν := by
    have hk_meas' : Measurable k := by
      fun_prop
    exact hk_meas'.aestronglyMeasurable
  have hm_meas : AEStronglyMeasurable m ν := by
    have hm_meas' : Measurable m := by
      fun_prop
    exact hm_meas'.aestronglyMeasurable
  constructor
  · intro hk
    -- Proof comment: the upper comparison `k ≤ min 1 x` turns integrability of the Laplace kernel
    -- into integrability of the truncation kernel after one rescaling.
    have hscaled :
        Integrable (fun x : NNReal ↦ (1 - Real.exp (-(1 / 2 : ℝ))) * m x) ν := by
      refine Integrable.mono' hk (hm_meas.const_mul _) ?_
      filter_upwards with x
      have hconst_nonneg : 0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) :=
        le_of_lt poissonExpKernelLowerConst_pos
      have hx :
          (1 - Real.exp (-(1 / 2 : ℝ))) * m x ≤ k x :=
        poissonExpKernel_lower_mul_min (x : ℝ) x.2
      have hx' : |1 - Real.exp (-(1 / 2 : ℝ))| * m x ≤ k x := by
        rw [abs_of_nonneg hconst_nonneg]
        exact hx
      simpa [k, m, Real.norm_eq_abs, Real.norm_of_nonneg (hk_nonneg x),
        Real.norm_of_nonneg (hm_nonneg x)] using hx'
    have hconst_ne : (1 - Real.exp (-(1 / 2 : ℝ))) ≠ 0 := by
      linarith [poissonExpKernelLowerConst_pos]
    -- Proof comment: divide by the strictly positive comparison constant to recover `min 1 x`.
    have hm' :
        Integrable
          (fun x : NNReal ↦
            (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ *
              ((1 - Real.exp (-(1 / 2 : ℝ))) * m x)) ν :=
      hscaled.const_mul (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹
    convert hm' using 1
    funext x
    field_simp [hconst_ne]
    ring
  · intro hm
    -- Proof comment: the pointwise upper bound `k ≤ min 1 x` makes the reverse integrability
    -- implication immediate.
    refine Integrable.mono' hm hk_meas ?_
    filter_upwards with x
    have hx : k x ≤ m x := one_sub_expNeg_le_min_one (x : ℝ)
    simpa [k, m, Real.norm_of_nonneg (hk_nonneg x), Real.norm_of_nonneg (hm_nonneg x)] using hx

/-- Helper for Theorem 24.17: the small Laplace scales are `s_n = (n + 1)⁻¹` on `ℝ`. -/
private def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Theorem 24.17: the kernel `ennrealExpNeg` is measurable on `ℝ≥0∞`. -/
private lemma measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) := by
    fun_prop
  -- Proof comment: rewrite the `if t = ∞` definition as a singleton-piecewise function.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (∞ : ℝ≥0∞)) hcore)

/-- Helper for Theorem 24.17: the extended-real Laplace kernel is pointwise nonnegative. -/
private lemma ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ∞
  · -- Proof comment: at `∞` the kernel is exactly `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: away from `∞`, the kernel is an ordinary exponential.
    simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Theorem 24.17: the extended-real Laplace kernel is bounded above by `1`. -/
private lemma ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ∞
  · -- Proof comment: the `∞` value is `0`, so the bound is immediate.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: on finite inputs the exponent is nonpositive, hence its exponential is at
    -- most `1`.
    have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Theorem 24.17: the scaled Laplace kernel tends to the finiteness indicator on
`ℝ≥0∞`. -/
private lemma ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ∞ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ∞
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
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ∞ :=
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

/-- Helper for Theorem 24.17: the small-scale Laplace expectations converge to the probability
that the extended-real variable is finite. -/
private lemma poissonPointIntegralLaplace_invSucc_tendsto_measureFinite
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {Y : α → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ∞}).toReal) := by
  let A : Set α := {a | Y a < ∞}
  let G : α → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    -- Proof comment: measurability comes from the measurable kernel and the measurable variable
    -- `Y`.
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
    · -- Proof comment: at `∞` the pointwise limit is `0`, matching the indicator complement.
      simpa [G, A, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · -- Proof comment: at finite points the pointwise limit is `1`, matching the indicator.
      have ha' : Y a < ∞ := lt_top_iff_ne_top.mpr ha
      simpa [G, A, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : α ↦ (1 : ℝ)) hF_meas (integrable_const 1) h_bound h_lim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hG_integral : ∫ a, G a ∂μ = (μ A).toReal := by
    -- Proof comment: integrating the indicator of `A` against the finite measure recovers `μ A`.
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hG_integral] using hDCT

/-- Helper for Theorem 24.17: scaling the textbook kernel by a factor `s ≤ 1` preserves the
domination by `x ↦ min 1 x`. -/
private lemma poissonExpKernel_scale_le_minOne
    (s : ℝ) (hs1 : s ≤ 1) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) := by
  -- Proof comment: `min 1 ·` is monotone in its second argument, and `s * x ≤ x` when `s ≤ 1`
  -- and `x ≥ 0`.
  have hmul_le : s * (x : ℝ) ≤ (x : ℝ) := by
    nlinarith [x.2, hs1]
  calc
    1 - Real.exp (-(s * (x : ℝ))) ≤ min 1 (s * (x : ℝ)) := one_sub_expNeg_le_min_one _
    _ ≤ min 1 (x : ℝ) := min_le_min le_rfl hmul_le

/-- Helper for Theorem 24.17: the scaled Poisson Laplace kernel is the `ENNReal` lift of the
ordinary real kernel. -/
private lemma poissonLaplaceKernel_scale_eq_ofReal (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (s * (x : ℝ)))) =
      ENNReal.ofReal (1 - Real.exp (-(s * (x : ℝ)))) := by
  have hmul_nonneg : 0 ≤ s * (x : ℝ) := by
    nlinarith [hs, x.2]
  have hExpNonneg : 0 ≤ Real.exp (-(s * (x : ℝ))) := Real.exp_nonneg _
  -- Proof comment: finite `ENNReal.ofReal` inputs reduce the extended-real kernel back to the
  -- ordinary exponential.
  simp [ennrealExpNeg, hmul_nonneg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Theorem 24.17: the scaled Laplace exponents converge to `0` under the Lévy
integrability condition. -/
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
      have hn : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      have hs0 : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
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
    -- Proof comment: for each fixed `x`, the scale tends to `0`, so the real kernel tends to
    -- `1 - exp 0 = 0`.
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

/-- Helper for Theorem 24.17: for `s ≥ 0`, the scaled Bernstein kernel is dominated by
`max 1 s * min 1 x`. -/
private lemma poissonExpKernel_scale_le_max_mul_minOne
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

-- Proof sketch: decompose the integral into the large-jump and small-jump parts as in the
-- textbook proof, use the Poisson law on `[1, ∞)` for the large jumps, and control the small-jump
-- piece by its first moment and variance. This yields the implications `(iii) → (ii)`, `(ii) →
-- (i)`, and `(i) → (iii)`, which are then packaged as a TFAE.
/-- Theorem 24.17: for a Poisson point process `X ∼ PPP_ν` on `ℝ≥0`, the following are
equivalent: (i) the Poisson stochastic integral `∫ x X(dx)` is finite with positive probability;
(ii) it is finite almost surely; and (iii) the Lévy integrability condition
`∫ min (1, x) dν < ∞` holds. -/
theorem poissonPointIntegral_finite_tfae
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X) :
    List.TFAE
      [ 0 < (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞}
      , (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1
      , Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν
      ] := by
  let Y : Ω → ℝ≥0∞ := poissonPointIntegral X
  let A : Set Ω := {ω | Y ω < ∞}
  let laplaceEvent : Ω → ℝ :=
    Set.indicator A fun ω ↦ Real.exp (-(Y ω).toReal)
  let idNNReal : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ (x : ℝ≥0∞), measurable_coe_nnreal_ennreal⟩
  let exponent : ℝ≥0∞ :=
    ∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg ((idNNReal x : ℝ≥0∞))) ∂ν
  have hPPP : ProbabilityTheory.IsPoissonPointProcess ν P X := by
    simpa [IsPoissonPointProcessOnNNReal, ProbabilityTheory.IsPoissonPointProcess] using hX
  have hY_meas : Measurable Y := poissonPointIntegral_measurable hX
  have hA_meas : MeasurableSet A := measurableSet_lt hY_meas measurable_const
  have hlaplaceEvent_eq :
      (fun ω ↦ ennrealExpNeg (Y ω)) = laplaceEvent := by
    funext ω
    by_cases hω : Y ω = ∞
    · have hω' : ω ∉ A := by simpa [A, Y] using hω
      simp [laplaceEvent, A, hω, hω', ennrealExpNeg_top]
    · have hω' : ω ∈ A := by
        simpa [A, Y, lt_top_iff_ne_top] using hω
      simp [laplaceEvent, A, hω', ennrealExpNeg, hω]
  have hlaplaceEvent_nonneg : ∀ ω, 0 ≤ laplaceEvent ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
      exact le_of_lt (Real.exp_pos _)
    · simp [laplaceEvent, hω]
  have hlaplaceEvent_meas : AEStronglyMeasurable laplaceEvent (P : Measure Ω) := by
    have hcore : Measurable (fun ω ↦ Real.exp (-(Y ω).toReal)) := by
      have htoReal : Measurable (fun ω ↦ (Y ω).toReal) :=
        ENNReal.measurable_toReal.comp hY_meas
      fun_prop
    exact (hcore.stronglyMeasurable.indicator hA_meas).aestronglyMeasurable
  have hlaplaceEvent_integrable : Integrable laplaceEvent (P : Measure Ω) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hlaplaceEvent_meas ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · have htoReal_nonneg : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
      have hle : Real.exp (-(Y ω).toReal) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      simp [laplaceEvent, hω, abs_of_nonneg (hlaplaceEvent_nonneg ω), hle]
    · simp [laplaceEvent, hω]
  have hsupport :
      Function.support laplaceEvent = A := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
    · simp [laplaceEvent, hω]
  have hleft_pos :
      0 < ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) ↔ 0 < (P : Measure Ω) A := by
    rw [hlaplaceEvent_eq, MeasureTheory.integral_pos_iff_support_of_nonneg
      hlaplaceEvent_nonneg hlaplaceEvent_integrable, hsupport]
  have hLaplaceOne :
      ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) = ennrealExpNeg exponent := by
    -- Proof comment: specialize Theorem 24.14 to the identity test function on `ℝ≥0`.
    simpa [Y, exponent, idNNReal, poissonPointIntegral_def] using
      poisson_point_process_laplaceTransform P ν X hPPP idNNReal
  have hexponent_eq :
      exponent =
        ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) ∂ν := by
    -- Proof comment: on finite `NNReal` points, the Poisson exponent kernel is exactly the
    -- `ENNReal` lift of `1 - exp (-x)`.
    refine lintegral_congr_ae ?_
    filter_upwards with x
    simpa [exponent, idNNReal] using poissonLaplaceKernel_eq_ofReal x
  have hkernel_nonneg : 0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ)) :=
    Filter.Eventually.of_forall fun x ↦
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by simpa using x.2))
  have hkernel_meas :
      AEStronglyMeasurable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hright_pos :
      0 < ennrealExpNeg exponent ↔
        Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
    have hexponent_finite :
        exponent ≠ ∞ ↔ Integrable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν := by
      rw [hexponent_eq]
      exact MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hkernel_meas hkernel_nonneg
    have hExpPos : 0 < ennrealExpNeg exponent ↔ exponent ≠ ∞ := by
      by_cases htop : exponent = ∞
      · simp [ennrealExpNeg, htop]
      · simp [ennrealExpNeg, htop, Real.exp_pos]
    exact hExpPos.trans <| hexponent_finite.trans (poissonLaplaceKernel_integrable_iff ν)
  tfae_have 1 → 3 := by
    -- Proof comment: the `s = 1` Laplace identity turns positive finiteness probability into the
    -- finiteness of the exponent kernel, which is exactly the textbook integrability condition.
    intro hPos
    exact hright_pos.mp <| by
      rw [← hLaplaceOne]
      exact hleft_pos.mpr hPos
  tfae_have 2 → 1 := by
    -- Proof comment: probability one immediately implies strictly positive probability.
    intro hAlmostSure
    rw [hAlmostSure]
    positivity
  tfae_have 3 → 1 := by
    -- Proof comment: the same `s = 1` Laplace identity runs in reverse and yields a strictly
    -- positive Laplace expectation, hence positive finiteness probability.
    intro hInt
    exact hleft_pos.mp <| by
      rw [hLaplaceOne]
      exact hright_pos.mpr hInt
  tfae_have 3 → 2 := by
    intro hInt
    let scaledId : ℕ → NonnegativeMeasurableFunction NNReal := fun n ↦
      ⟨fun x ↦ ENNReal.ofReal (invSuccScaleReal n) * x,
        measurable_const.mul measurable_coe_nnreal_ennreal⟩
    let scaledExponent : ℕ → ℝ≥0∞ := fun n ↦
      ∫⁻ x,
        (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId n x)) ∂ν
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
          (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
      intro n
      have h : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
        fun_prop
      exact h.aestronglyMeasurable
    have hkernel_nonneg :
        ∀ n, 0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      intro n
      filter_upwards with x
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [hs_nonneg n, x.2]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hkernel_int :
        ∀ n, Integrable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
      intro n
      -- Proof comment: each scaled kernel is dominated by the textbook truncation kernel.
      refine Integrable.mono' hInt (hkernel_meas n) ?_
      filter_upwards with x
      have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
        have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
          nlinarith [hs_nonneg n, x.2]
        have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          linarith
        exact sub_nonneg.mpr hle
      have hle :
          1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
        poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) x
      simpa [Real.norm_of_nonneg hnonneg] using hle
    have hscaledExponent_eq :
        ∀ n,
          scaledExponent n =
            ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν) := by
      intro n
      calc
        scaledExponent n
            = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν := by
                refine lintegral_congr_ae ?_
                filter_upwards with x
                -- Proof comment: rewrite the scaled `ENNReal` Laplace kernel into the real kernel
                -- used in the dominated-convergence lemma.
                simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg n] using
                  poissonLaplaceKernel_scale_eq_ofReal (invSuccScaleReal n) (hs_nonneg n) x
        _ = ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (hkernel_int n) (hkernel_nonneg n)
    have hLeft :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
            (P : Measure Ω))
          Filter.atTop (nhds ((P : Measure Ω) A).toReal) :=
      poissonPointIntegralLaplace_invSucc_tendsto_measureFinite (μ := (P : Measure Ω)) hY_meas
    have hRight :
        Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) Filter.atTop (nhds 1) := by
      have hrewrite :
          (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) =
            (fun n : ℕ ↦
              Real.exp
                (-(∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν))) := by
        funext n
        have hIntegral_nonneg :
            0 ≤ ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν :=
          integral_nonneg_of_ae (hkernel_nonneg n)
        rw [hscaledExponent_eq n, ennrealExpNeg]
        simp [hIntegral_nonneg]
      rw [hrewrite]
      -- Proof comment: the exponent-side dominated-convergence lemma makes the exponential limit
      -- collapse to `exp 0 = 1`.
      have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      simpa using hcont.continuousAt.tendsto.comp
        (poissonLaplaceExponent_invSucc_tendstoZero ν hInt)
    have hLaplaceScaled :
        ∀ n,
          ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
      intro n
      -- Proof comment: this is Theorem 24.14 specialized to the scaled identity test function.
      have hlintegral :
          (fun ω ↦ ∫⁻ x, scaledId n x ∂X ω) =
            (fun ω ↦ ENNReal.ofReal (invSuccScaleReal n) * Y ω) := by
        funext ω
        simpa [scaledId, Y, poissonPointIntegral_def] using
          (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (invSuccScaleReal n))
            (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
      have hraw :
          ∫ ω, ennrealExpNeg (∫⁻ x, scaledId n x ∂X ω) ∂(P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
        simpa [scaledExponent] using
          poisson_point_process_laplaceTransform P ν X hPPP (scaledId n)
      have hleftRewrite :
          (fun ω ↦ ennrealExpNeg (∫⁻ x, scaledId n x ∂X ω)) =
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
    exact (ENNReal.toReal_eq_one_iff ((P : Measure Ω) A)).mp hToRealOne
  tfae_finish

-- Proof sketch: apply the Poisson random-measure Laplace formula with the identity test function
-- `x ↦ t x` to compute the Laplace transform of `∫ x X(dx)` and identify the exponent with the
-- standard Poisson/Lévy integral `∫ (e^{-tx} - 1) ν(dx)`.
/-- The Laplace transform of the Poisson stochastic integral is given by the canonical exponential
formula determined by the intensity measure `ν`. -/
theorem poissonPointIntegral_laplaceFormula
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X)
    (hfinite : (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1) :
    ∀ t : NNReal,
      ∫ ω,
          Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) := by
  intro t
  let Y : Ω → ℝ≥0∞ := poissonPointIntegral X
  let scaledId : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ ENNReal.ofReal (t : ℝ) * x,
      measurable_const.mul measurable_coe_nnreal_ennreal⟩
  let scaledExponent : ℝ≥0∞ := ∫⁻ x,
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId x)) ∂ν
  have hPPP : ProbabilityTheory.IsPoissonPointProcess ν P X := by
    simpa [IsPoissonPointProcessOnNNReal, ProbabilityTheory.IsPoissonPointProcess] using hX
  have hInt :
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν :=
    ((poissonPointIntegral_finite_tfae hX).out 1 2).mp hfinite
  have hY_meas : Measurable Y := poissonPointIntegral_measurable hX
  have hA_meas : MeasurableSet {ω | Y ω < ∞} := measurableSet_lt hY_meas measurable_const
  have hAeFinite : ∀ᵐ ω ∂(P : Measure Ω), Y ω < ∞ :=
    (mem_ae_iff_prob_eq_one hA_meas).2 hfinite
  have hs_nonneg : 0 ≤ (t : ℝ) := t.2
  have hkernel_meas :
      AEStronglyMeasurable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
    filter_upwards with x
    have hle : Real.exp (-((t : ℝ) * (x : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [t.2, x.2]
    exact sub_nonneg.mpr hle
  have hkernel_int :
      Integrable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ν := by
    have hdom :
        Integrable (fun x : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ)) ν :=
      hInt.const_mul (max 1 (t : ℝ))
    refine Integrable.mono' hdom hkernel_meas ?_
    filter_upwards with x
    have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
      have hle : Real.exp (-((t : ℝ) * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [t.2, x.2]
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-((t : ℝ) * (x : ℝ))) ≤
          max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_max_mul_minOne (t : ℝ) hs_nonneg x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      scaledExponent =
        ENNReal.ofReal (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
    calc
      scaledExponent
          = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
              refine lintegral_congr_ae ?_
              filter_upwards with x
              simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg] using
                poissonLaplaceKernel_scale_eq_ofReal (t : ℝ) hs_nonneg x
      _ = ENNReal.ofReal (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
  have hraw :
      ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂X ω) ∂(P : Measure Ω) =
        ennrealExpNeg scaledExponent := by
    simpa [scaledExponent] using
      poisson_point_process_laplaceTransform P ν X hPPP scaledId
  have hlintegral :
      (fun ω ↦ ∫⁻ x, scaledId x ∂X ω) =
        fun ω ↦ ENNReal.ofReal (t : ℝ) * Y ω := by
    funext ω
    simpa [scaledId, Y, poissonPointIntegral_def] using
      (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (t : ℝ))
        (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
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
  have hcentered :
      Integrable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ν := by
    have hneg : Integrable (fun x : NNReal ↦ -(1 - Real.exp (-((t : ℝ) * (x : ℝ))))) ν :=
      hkernel_int.neg
    convert hneg using 1
    funext x
    ring
  calc
    ∫ ω, Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal)) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω) ∂(P : Measure Ω) := by
            symm
            exact integral_congr_ae hleft_ae
    _ = ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂X ω) ∂(P : Measure Ω) := by
          congr 1
          funext ω
          symm
          exact congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    _ = ennrealExpNeg scaledExponent := hraw
    _ = Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) := by
          rw [hscaledExponent_eq, ennrealExpNeg]
          have hIntegral_nonneg :
              0 ≤ ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν :=
            integral_nonneg_of_ae hkernel_nonneg
          simp [hIntegral_nonneg]
          rw [show -(∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) =
              ∫ x : NNReal, -(1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν by
                symm
                exact integral_neg (f := fun x : NNReal ↦
                  1 - Real.exp (-((t : ℝ) * (x : ℝ))))]
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          ring

-- Proof sketch: in the almost-surely finite regime, the real-valued version of the Poisson
-- stochastic integral is completely characterized here by the same Laplace-transform formula.
/-- If the Poisson stochastic integral is almost surely finite, then its real-valued version
shares the Poisson/Lévy Laplace-transform formula. -/
theorem poissonPointIntegral_toReal_isInfinitelyDivisible
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X)
    (hfinite : (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1) :
    ∀ t : NNReal,
      ∫ ω,
          Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) := by
  exact poissonPointIntegral_laplaceFormula hX hfinite

end ProbabilityTheory

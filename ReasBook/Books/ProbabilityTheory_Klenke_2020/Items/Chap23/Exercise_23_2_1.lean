/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 23.2.1: the right-neighborhood filter `𝓝[>] (0 : ℝ)` is nontrivial, so
its liminf/limsup expressions have the expected order-theoretic behavior. -/
private instance positiveNhdsWithinZero_neBot :
    NeBot (𝓝[>] (0 : ℝ)) := by
  infer_instance

/-- The quadratic rate function `x ↦ x^2 / 2` valued in `ℝ≥0∞`. -/
noncomputable def gaussianQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (x ^ 2 / 2)

/-- The same quadratic rate function viewed in `EReal` for the variational bounds. -/
noncomputable def gaussianQuadraticRateFunctionEReal (x : ℝ) : EReal :=
  gaussianQuadraticRateFunction x

/-- The small-variance centered Gaussian law `μ_ε = N(0, ε)` for positive `ε`. -/
noncomputable def centeredGaussianSmallVarianceLaw (ε : ℝ) : Measure ℝ :=
  gaussianReal 0 (Real.toNNReal ε)

/-- The exponential rate expression `ε log μ_ε(s)` used in the LDP bounds. -/
noncomputable def centeredGaussianSmallVarianceExponent (s : Set ℝ) (ε : ℝ) : EReal :=
  (ε : EReal) * ENNReal.log (centeredGaussianSmallVarianceLaw ε s)

/-- Helper for Exercise 23.2.1: enlarging the underlying event can only increase the scaled
logarithmic mass when `ε > 0`. -/
private theorem centeredGaussianSmallVarianceExponent_mono {s t : Set ℝ} (hst : s ⊆ t)
    {ε : ℝ} (hε : 0 < ε) :
    centeredGaussianSmallVarianceExponent s ε ≤ centeredGaussianSmallVarianceExponent t ε := by
  -- Proof comment: monotonicity of the measure passes through `ENNReal.log`, and the positive
  -- prefactor `ε` preserves the order.
  rw [centeredGaussianSmallVarianceExponent, centeredGaussianSmallVarianceExponent]
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  exact mul_le_mul_of_nonneg_left
    (ENNReal.log_le_log (measure_mono hst)) hεE

/-- Helper for Exercise 23.2.1: viewed in `EReal`, the Gaussian quadratic rate is the ordinary real
quadratic `x^2 / 2`. -/
private theorem gaussianQuadraticRateFunctionEReal_eq_half_sq (x : ℝ) :
    gaussianQuadraticRateFunctionEReal x = ((x ^ 2 / 2 : ℝ) : EReal) := by
  -- Proof comment: `x ^ 2 / 2` is nonnegative, so the `ENNReal.ofReal` coercion is the same as
  -- the direct real-to-`EReal` coercion.
  have hx : 0 ≤ x ^ 2 / 2 := by
    positivity
  rw [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction,
    ENNReal.ofReal_eq_coe_nnreal hx]
  rfl

/-- Helper for Exercise 23.2.1: every positive-variance scaled logarithmic mass is nonpositive
because a probability measure assigns mass at most `1` to every set. -/
private theorem centeredGaussianSmallVarianceExponent_nonpos {s : Set ℝ} {ε : ℝ} (hε : 0 < ε) :
    centeredGaussianSmallVarianceExponent s ε ≤ 0 := by
  -- Proof comment: `μ_ε s ≤ 1` gives `log μ_ε s ≤ 0`, and multiplying by the positive parameter
  -- keeps the inequality direction.
  rw [centeredGaussianSmallVarianceExponent]
  have hmass : centeredGaussianSmallVarianceLaw ε s ≤ 1 := by
    calc
      centeredGaussianSmallVarianceLaw ε s ≤ centeredGaussianSmallVarianceLaw ε Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := by
        simp [centeredGaussianSmallVarianceLaw]
  have hlog : ENNReal.log (centeredGaussianSmallVarianceLaw ε s) ≤ 0 := by
    simpa using
      (ENNReal.log_le_log hmass : ENNReal.log (centeredGaussianSmallVarianceLaw ε s) ≤
        ENNReal.log (1 : ENNReal))
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  exact mul_nonpos_of_nonneg_of_nonpos hεE hlog

/-- Helper for Exercise 23.2.1: the two-sided Gaussian tail outside `[-r, r]` is bounded by the
standard Chernoff estimate `2 * exp (-r^2 / (2ε))`. -/
private theorem centeredGaussianSmallVarianceLaw_symmetricTail_real_le {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) :
    (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r) ∪ Set.Ici r) ≤
      2 * Real.exp (-(r ^ 2) / (2 * ε)) := by
  letI : IsFiniteMeasure (centeredGaussianSmallVarianceLaw ε) := by
    dsimp [centeredGaussianSmallVarianceLaw]
    infer_instance
  have hIntRight :
      Integrable (fun x : ℝ ↦ Real.exp ((r / ε) * x)) (centeredGaussianSmallVarianceLaw ε) := by
    -- Proof comment: the Gaussian mgf is finite for every real parameter, so the positive-tail
    -- Chernoff bound is available at the optimizing slope `r / ε`.
    simpa [centeredGaussianSmallVarianceLaw, Real.toNNReal_of_nonneg hε.le] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal ε) (t := r / ε))
  have hIntLeft :
      Integrable (fun x : ℝ ↦ Real.exp ((-r / ε) * x)) (centeredGaussianSmallVarianceLaw ε) := by
    -- Proof comment: the same mgf input controls the left tail after flipping the sign of the
    -- Chernoff parameter.
    simpa [centeredGaussianSmallVarianceLaw, Real.toNNReal_of_nonneg hε.le] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := Real.toNNReal ε) (t := -r / ε))
  have hRight :
      (centeredGaussianSmallVarianceLaw ε).real (Set.Ici r) ≤
        Real.exp (-(r ^ 2) / (2 * ε)) := by
    have hChernoff :
        (centeredGaussianSmallVarianceLaw ε).real (Set.Ici r) ≤
          Real.exp (-(r / ε) * r) * mgf id (centeredGaussianSmallVarianceLaw ε) (r / ε) := by
      -- Proof comment: apply the standard upper-tail Chernoff estimate to the identity random
      -- variable under the Gaussian law.
      simpa [Set.Ici] using
        (measure_ge_le_exp_mul_mgf (μ := centeredGaussianSmallVarianceLaw ε) (X := id)
          (ε := r) (t := r / ε) (show 0 ≤ r / ε by positivity) hIntRight)
    have hεne : ε ≠ 0 := ne_of_gt hε
    calc
      (centeredGaussianSmallVarianceLaw ε).real (Set.Ici r) ≤
          Real.exp (-(r / ε) * r) * mgf id (centeredGaussianSmallVarianceLaw ε) (r / ε) :=
        hChernoff
      _ = Real.exp (-(r ^ 2) / (2 * ε)) := by
        -- Proof comment: the Gaussian mgf closes the optimized exponent exactly.
        rw [centeredGaussianSmallVarianceLaw, mgf_id_gaussianReal]
        simp only [neg_mul, zero_mul, Real.coe_toNNReal', zero_add]
        rw [max_eq_left hε.le]
        rw [← Real.exp_add]
        congr 1
        field_simp [hεne]
        ring
  have hLeft :
      (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r)) ≤
        Real.exp (-(r ^ 2) / (2 * ε)) := by
    have hChernoff :
        (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r)) ≤
          Real.exp (-(-r / ε) * (-r)) * mgf id (centeredGaussianSmallVarianceLaw ε) (-r / ε) := by
      -- Proof comment: apply the lower-tail Chernoff estimate with the negative optimizing slope.
      simpa [Set.Iic] using
        (measure_le_le_exp_mul_mgf (μ := centeredGaussianSmallVarianceLaw ε) (X := id)
          (ε := -r) (t := -r / ε)
          (show -r / ε ≤ 0 by
            exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)
          hIntLeft)
    have hεne : ε ≠ 0 := ne_of_gt hε
    calc
      (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r)) ≤
          Real.exp (-(-r / ε) * (-r)) * mgf id (centeredGaussianSmallVarianceLaw ε) (-r / ε) :=
        hChernoff
      _ = Real.exp (-(r ^ 2) / (2 * ε)) := by
        -- Proof comment: the left-tail optimization gives the same quadratic exponent.
        rw [centeredGaussianSmallVarianceLaw, mgf_id_gaussianReal]
        simp only [mul_neg, neg_mul, neg_neg, zero_mul, Real.coe_toNNReal', zero_add]
        rw [max_eq_left hε.le]
        rw [← Real.exp_add]
        congr 1
        field_simp [hεne]
        ring
  calc
    (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r) ∪ Set.Ici r) ≤
        (centeredGaussianSmallVarianceLaw ε).real (Set.Iic (-r)) +
          (centeredGaussianSmallVarianceLaw ε).real (Set.Ici r) :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-(r ^ 2) / (2 * ε)) + Real.exp (-(r ^ 2) / (2 * ε)) :=
      add_le_add hLeft hRight
    _ = 2 * Real.exp (-(r ^ 2) / (2 * ε)) := by ring

/-- Helper for Exercise 23.2.1: the scaled logarithmic mass of the symmetric tail event is bounded
above by the quadratic rate `-r^2 / 2`, up to the vanishing prefactor `ε log 2`. -/
private theorem centeredGaussianSmallVarianceExponent_symmetricTail_le {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) :
    centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε ≤
      ((ε * Real.log 2 - r ^ 2 / 2 : ℝ) : EReal) := by
  letI : IsFiniteMeasure (centeredGaussianSmallVarianceLaw ε) := by
    dsimp [centeredGaussianSmallVarianceLaw]
    infer_instance
  let tail : Set ℝ := Set.Iic (-r) ∪ Set.Ici r
  let bound : ℝ := 2 * Real.exp (-(r ^ 2) / (2 * ε))
  have hBoundReal :
      (centeredGaussianSmallVarianceLaw ε).real tail ≤ bound := by
    -- Proof comment: use the already established real-valued Chernoff estimate for the symmetric
    -- Gaussian tail.
    simpa [tail, bound] using centeredGaussianSmallVarianceLaw_symmetricTail_real_le hr hε
  have hBoundNonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hBoundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have hMeasureNeTop : centeredGaussianSmallVarianceLaw ε tail ≠ ∞ := by
    exact measure_ne_top _ _
  have hMassENN :
      centeredGaussianSmallVarianceLaw ε tail ≤ ENNReal.ofReal bound := by
    -- Proof comment: convert the real-valued tail estimate back to the original `ENNReal` mass.
    refine (ENNReal.le_ofReal_iff_toReal_le hMeasureNeTop hBoundNonneg).2 ?_
    simpa [Measure.real] using hBoundReal
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  calc
    centeredGaussianSmallVarianceExponent tail ε =
        (ε : EReal) * ENNReal.log (centeredGaussianSmallVarianceLaw ε tail) := by
      rw [centeredGaussianSmallVarianceExponent]
    _ ≤ (ε : EReal) * ENNReal.log (ENNReal.ofReal bound) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hMassENN) hεE
    _ = ((ε * Real.log bound : ℝ) : EReal) := by
      rw [ENNReal.log_ofReal_of_pos hBoundPos, ← EReal.coe_mul]
    _ = ((ε * Real.log 2 - r ^ 2 / 2 : ℝ) : EReal) := by
      -- Proof comment: split the logarithm into the constant `log 2` part and the optimized
      -- Gaussian exponent, then simplify the linear term in `ε`.
      congr 1
      dsimp [bound]
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
      field_simp [hε.ne']
      ring

/-- Helper for Exercise 23.2.1: the limsup of the symmetric tail logarithmic mass is bounded by
`-r^2 / 2`. -/
private theorem centeredGaussianSmallVarianceExponent_symmetricTail_upperBound {r : ℝ}
    (hr : 0 < r) :
    Filter.limsup (centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r))
        (𝓝[>] (0 : ℝ)) ≤
      -((((r ^ 2) / 2 : ℝ) : EReal)) := by
  let upperApprox : ℝ → EReal := fun ε ↦ ((ε * Real.log 2 - r ^ 2 / 2 : ℝ) : EReal)
  have hEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε ≤ upperApprox ε := by
    -- Proof comment: the pointwise tail estimate already holds for every sufficiently small
    -- positive variance parameter.
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := by
      simpa using hε
    simpa [upperApprox] using centeredGaussianSmallVarianceExponent_symmetricTail_le hr hεpos
  have hUpperApproxTendstoReal :
      Tendsto (fun ε : ℝ ↦ ε * Real.log 2 - r ^ 2 / 2) (𝓝[>] (0 : ℝ))
        (𝓝 (-(r ^ 2 / 2 : ℝ))) := by
    -- Proof comment: the error term `ε log 2` vanishes at `0`, so the real-valued approximation
    -- converges to the quadratic tail rate.
    have hCont : Continuous fun ε : ℝ ↦ ε * Real.log 2 - r ^ 2 / 2 := by
      continuity
    have hCont0 : ContinuousAt (fun ε : ℝ ↦ ε * Real.log 2 - r ^ 2 / 2) 0 :=
      hCont.continuousAt
    simpa using hCont0.continuousWithinAt.tendsto
  have hUpperApproxTendsto :
      Tendsto upperApprox (𝓝[>] (0 : ℝ)) (𝓝 (-((((r ^ 2) / 2 : ℝ) : EReal)))) := by
    -- Proof comment: the eventual upper approximation stays in the finite real part of `EReal`,
    -- so the ordinary real limit transports directly.
    simpa [upperApprox] using (EReal.tendsto_coe.2 hUpperApproxTendstoReal)
  calc
    Filter.limsup (centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r))
        (𝓝[>] (0 : ℝ)) ≤
      Filter.limsup upperApprox (𝓝[>] (0 : ℝ)) :=
      limsup_le_limsup hEventually
    _ = -((((r ^ 2) / 2 : ℝ) : EReal)) :=
      hUpperApproxTendsto.limsup_eq

/-- Helper for Exercise 23.2.1: the finite sublevel sets of `x ↦ x^2 / 2` are exactly symmetric
compact intervals. -/
theorem gaussianQuadraticRateFunction_sublevel_eq_Icc (a : ℝ≥0) :
    gaussianQuadraticRateFunction ⁻¹' Set.Iic (a : ℝ≥0∞) =
      Set.Icc (-Real.sqrt (2 * a)) (Real.sqrt (2 * a)) := by
  ext x
  constructor
  · intro hx
    -- Convert the `ℝ≥0∞` bound back to an ordinary real quadratic inequality.
    have hx' : x ^ 2 / 2 ≤ (a : ℝ) := by
      exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hx
    have hsq : x ^ 2 ≤ 2 * (a : ℝ) := by
      nlinarith
    -- The quadratic bound forces `x` into the corresponding interval.
    exact ⟨Real.neg_sqrt_le_of_sq_le hsq, Real.le_sqrt_of_sq_le hsq⟩
  · rintro ⟨hxlo, hxhi⟩
    -- The interval description gives a uniform quadratic upper bound.
    have hsq : x ^ 2 ≤ 2 * (a : ℝ) := by
      exact (Real.sq_le (by positivity)).2 ⟨hxlo, hxhi⟩
    have hx' : x ^ 2 / 2 ≤ (a : ℝ) := by
      nlinarith
    exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).2 hx'

/-- Helper for Exercise 23.2.1: every nondegenerate centered Gaussian law on `ℝ` is atomless at
the origin, so the singleton `{0}` has zero mass. -/
theorem centeredGaussianSmallVarianceLaw_singletonZero {ε : ℝ} (hε : 0 < ε) :
    centeredGaussianSmallVarianceLaw ε ({0} : Set ℝ) = 0 := by
  have hVarPos : 0 < Real.toNNReal ε := by
    rw [Real.toNNReal_of_nonneg hε.le]
    exact hε
  have hNoAtoms : NoAtoms (centeredGaussianSmallVarianceLaw ε) := by
    simpa [centeredGaussianSmallVarianceLaw] using
      (noAtoms_gaussianReal (μ := 0) (v := Real.toNNReal ε) (ne_of_gt hVarPos))
  letI : NoAtoms (centeredGaussianSmallVarianceLaw ε) := hNoAtoms
  exact measure_singleton (μ := centeredGaussianSmallVarianceLaw ε) (0 : ℝ)

-- Proof sketch: the map `x ↦ x ^ 2 / 2` is continuous on `ℝ`, hence lower semicontinuous after
-- composing with `ENNReal.ofReal`; its finite sublevel sets are closed bounded intervals, so they
-- are compact by Heine--Borel.
/-- Exercise 23.2.1 (1): the quadratic map `I(x) = x^2 / 2`, viewed as an `ℝ≥0∞`-valued map, is a
good rate function on `ℝ`: it is lower semicontinuous and every finite sublevel set is compact. -/
theorem gaussianQuadraticRateFunction_isGood :
    IsGoodRateFunction gaussianQuadraticRateFunction := by
  refine ⟨?_, ?_⟩
  · -- The rate function is continuous, hence lower semicontinuous.
    have hcont : Continuous gaussianQuadraticRateFunction := by
      simpa [gaussianQuadraticRateFunction] using
        (ENNReal.continuous_ofReal.comp ((continuous_id.pow 2).div_const (2 : ℝ)))
    simpa using hcont.lowerSemicontinuous
  · intro a
    -- Rewrite the sublevel set as a compact interval.
    rw [gaussianQuadraticRateFunction_sublevel_eq_Icc]
    exact isCompact_Icc

/-- Helper for Exercise 23.2.1: on a compact interval centered at `x`, the Gaussian density is
uniformly bounded below by its value at the farthest endpoint `|x| + δ`. -/
private theorem gaussianPDFReal_lowerBound_on_Icc {x δ ε y : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hy : y ∈ Set.Icc (x - δ) (x + δ)) :
    (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε)) ≤
      gaussianPDFReal 0 (Real.toNNReal ε) y := by
  -- Proof comment: points in `Icc (x - δ) (x + δ)` satisfy `|y| ≤ |x| + δ`, so the Gaussian
  -- exponent at `y` is bounded below by the exponent at the farthest endpoint.
  have hyAbs : |y| ≤ |x| + δ := by
    have hLower : -(|x| + δ) ≤ y := by
      linarith [hy.1, neg_abs_le x]
    have hUpper : y ≤ |x| + δ := by
      linarith [hy.2, le_abs_self x]
    exact abs_le.2 ⟨hLower, hUpper⟩
  have hySqAbs : |y| ^ 2 ≤ (|x| + δ) ^ 2 := by
    have hRadiusNonneg : 0 ≤ |x| + δ := by positivity
    nlinarith [hyAbs, abs_nonneg y, hRadiusNonneg]
  have hySq : y ^ 2 ≤ (|x| + δ) ^ 2 := by
    simpa [sq_abs] using hySqAbs
  rw [gaussianPDFReal_def, Real.toNNReal_of_nonneg hε.le]
  have hExp :
      Real.exp (-((|x| + δ) ^ 2) / (2 * ε)) ≤ Real.exp (-(y ^ 2) / (2 * ε)) := by
    apply Real.exp_le_exp.mpr
    have hDiv : y ^ 2 / (2 * ε) ≤ (|x| + δ) ^ 2 / (2 * ε) := by
      exact div_le_div_of_nonneg_right hySq (by positivity)
    have hNegDiv : -((|x| + δ) ^ 2 / (2 * ε)) ≤ -(y ^ 2 / (2 * ε)) := neg_le_neg hDiv
    simpa [neg_div] using hNegDiv
  have hCoeff : 0 ≤ (Real.sqrt (2 * Real.pi * ε))⁻¹ := by
    positivity
  simpa [sub_zero] using mul_le_mul_of_nonneg_left hExp hCoeff

/-- Helper for Exercise 23.2.1: on a compact interval centered at `x`, the Gaussian density is
uniformly bounded below by its value at the farthest endpoint `|x| + δ`. -/
private theorem centeredGaussianSmallVarianceLaw_Icc_lowerDensityBound {x δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ENNReal.ofReal
      (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹ *
        Real.exp (-((|x| + δ) ^ 2) / (2 * ε))) ≤
      centeredGaussianSmallVarianceLaw ε (Set.Icc (x - δ) (x + δ)) := by
  -- Route correction: rewrite the Gaussian mass into a real interval integral first, prove the
  -- constant floor there, and only then return to `ENNReal.ofReal`.
  have hεnn : (Real.toNNReal ε : ℝ≥0) ≠ 0 := by
    have hεnnPos : (0 : ℝ≥0) < Real.toNNReal ε := by
      simpa [Real.toNNReal_of_nonneg hε.le] using hε
    exact ne_of_gt hεnnPos
  have hOrder : x - δ ≤ x + δ := by
    linarith
  rw [centeredGaussianSmallVarianceLaw, gaussianReal_apply_eq_integral 0 hεnn]
  apply ENNReal.ofReal_le_ofReal
  have hIntConst :
      IntervalIntegrable
        (fun _ : ℝ ↦
          (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε)))
        volume (x - δ) (x + δ) := by
    exact
      (intervalIntegrable_const :
        IntervalIntegrable
          (fun _ : ℝ ↦
            (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε)))
          volume (x - δ) (x + δ))
  have hIntPdf :
      IntervalIntegrable (gaussianPDFReal 0 (Real.toNNReal ε)) volume (x - δ) (x + δ) := by
    simpa using (integrable_gaussianPDFReal 0 (Real.toNNReal ε)).intervalIntegrable
  have hIntegral :
      ∫ y in x - δ..x + δ,
          (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε))
        ≤ ∫ y in x - δ..x + δ, gaussianPDFReal 0 (Real.toNNReal ε) y := by
    -- Proof comment: monotonicity of interval integrals turns the pointwise density floor into an
    -- interval mass lower bound.
    refine intervalIntegral.integral_mono_on hOrder hIntConst hIntPdf ?_
    intro y hy
    exact gaussianPDFReal_lowerBound_on_Icc hδ hε hy
  calc
    2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε))
        = ∫ y in x - δ..x + δ,
            (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
    _ ≤ ∫ y in x - δ..x + δ, gaussianPDFReal 0 (Real.toNNReal ε) y := hIntegral
    _ = ∫ y in Set.Icc (x - δ) (x + δ), gaussianPDFReal 0 (Real.toNNReal ε) y := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hOrder]

/-- Helper for Exercise 23.2.1: the explicit interval mass lower bound turns into a corresponding
lower bound for the scaled logarithmic exponent. -/
private theorem centeredGaussianSmallVarianceExponent_Icc_lowerApprox {x δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ((ε * Real.log (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹) -
        (|x| + δ) ^ 2 / 2 : ℝ) : EReal) ≤
      centeredGaussianSmallVarianceExponent (Set.Icc (x - δ) (x + δ)) ε := by
  -- Proof comment: transport the explicit interval mass floor through `ENNReal.log` exactly once,
  -- then simplify the logarithm of the Gaussian lower bound.
  let bound : ℝ :=
    2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-((|x| + δ) ^ 2) / (2 * ε))
  have hMassENN :
      ENNReal.ofReal bound ≤ centeredGaussianSmallVarianceLaw ε (Set.Icc (x - δ) (x + δ)) := by
    simpa [bound] using centeredGaussianSmallVarianceLaw_Icc_lowerDensityBound (x := x) hδ hε
  have hBoundPos : 0 < bound := by
    dsimp [bound]
    positivity
  have hPrefactorPos : 0 < 2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹ := by
    positivity
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  calc
    ((ε * Real.log (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹) -
        (|x| + δ) ^ 2 / 2 : ℝ) : EReal)
        = ((ε * Real.log bound : ℝ) : EReal) := by
          -- Proof comment: split the logarithm of the lower bound into the prefactor term and the
          -- Gaussian exponential term, then simplify the resulting linear expression in `ε`.
          congr 1
          dsimp [bound]
          rw [Real.log_mul hPrefactorPos.ne' (Real.exp_pos _).ne', Real.log_exp]
          field_simp [hε.ne']
          ring
    _ = (ε : EReal) * ENNReal.log (ENNReal.ofReal bound) := by
          rw [ENNReal.log_ofReal_of_pos hBoundPos, ← EReal.coe_mul]
    _ ≤ (ε : EReal) * ENNReal.log
          (centeredGaussianSmallVarianceLaw ε (Set.Icc (x - δ) (x + δ))) := by
          exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hMassENN) hεE
    _ = centeredGaussianSmallVarianceExponent (Set.Icc (x - δ) (x + δ)) ε := by
          rw [centeredGaussianSmallVarianceExponent]

/-- Helper for Exercise 23.2.1: the interval lower approximation converges to the quadratic rate
`-((|x| + δ)^2 / 2)` as `ε ↓ 0`. -/
private theorem centeredGaussianSmallVarianceExponent_Icc_lowerBound {x δ : ℝ} (hδ : 0 < δ) :
    -((((|x| + δ) ^ 2) / 2 : ℝ) : EReal) ≤
      Filter.liminf (centeredGaussianSmallVarianceExponent (Set.Icc (x - δ) (x + δ)))
        (𝓝[>] (0 : ℝ)) := by
  -- Proof comment: compare the interval exponent with its explicit lower approximation, then show
  -- that the lower approximation converges to the quadratic rate because the `ε` and `ε log ε`
  -- error terms vanish at `0`.
  let lowerApprox : ℝ → EReal := fun ε ↦
    ((ε * Real.log (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹) -
        (|x| + δ) ^ 2 / 2 : ℝ) : EReal)
  have hEventuallyCompare :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        lowerApprox ε ≤
          centeredGaussianSmallVarianceExponent (Set.Icc (x - δ) (x + δ)) ε := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    simpa [lowerApprox] using centeredGaussianSmallVarianceExponent_Icc_lowerApprox (x := x) hδ hε
  have hRewriteEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ε * Real.log (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹) - (|x| + δ) ^ 2 / 2 =
          ε * (Real.log (2 * δ) - Real.log (2 * Real.pi) / 2) -
            (1 / 2 : ℝ) * (Real.log ε * ε) - (|x| + δ) ^ 2 / 2 := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hTwoDeltaNe : 2 * δ ≠ 0 := by
      positivity
    have hTwoPiNe : 2 * Real.pi ≠ 0 := by
      positivity
    have hTwoPiPos : 0 < 2 * Real.pi * ε := by
      have hTwoPiPos' : 0 < 2 * Real.pi := by positivity
      simpa [mul_assoc, mul_left_comm, mul_comm] using mul_pos hTwoPiPos' hε
    rw [Real.log_mul hTwoDeltaNe]
    · rw [Real.log_inv, Real.log_sqrt hTwoPiPos.le, Real.log_mul hTwoPiNe hε.ne']
      ring
    · positivity
  have hConstTendsto :
      Tendsto
        (fun ε : ℝ ↦ ε * (Real.log (2 * δ) - Real.log (2 * Real.pi) / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hCont :
        Continuous (fun ε : ℝ ↦ ε * (Real.log (2 * δ) - Real.log (2 * Real.pi) / 2)) := by
      continuity
    have hCont0 :
        ContinuousAt (fun ε : ℝ ↦ ε * (Real.log (2 * δ) - Real.log (2 * Real.pi) / 2)) 0 :=
      hCont.continuousAt
    simpa using hCont0.continuousWithinAt.tendsto
  have hLogTendsto :
      Tendsto (fun ε : ℝ ↦ (1 / 2 : ℝ) * (Real.log ε * ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hLogCore :
        Tendsto (fun ε : ℝ ↦ Real.log ε * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa [Real.rpow_one, mul_comm] using
        (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2))).mul
        hLogCore)
  have hApproxReal :
      Tendsto
        (fun ε : ℝ ↦ ε * Real.log (2 * δ * (Real.sqrt (2 * Real.pi * ε))⁻¹) -
          (|x| + δ) ^ 2 / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (-((|x| + δ) ^ 2 / 2 : ℝ))) := by
    have hMain :
        Tendsto
          (fun ε : ℝ ↦
            ε * (Real.log (2 * δ) - Real.log (2 * Real.pi) / 2) -
              (1 / 2 : ℝ) * (Real.log ε * ε) - (|x| + δ) ^ 2 / 2)
          (𝓝[>] (0 : ℝ)) (𝓝 (-((|x| + δ) ^ 2 / 2 : ℝ))) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        ((hConstTendsto.sub hLogTendsto).sub_const ((|x| + δ) ^ 2 / 2))
    exact Filter.Tendsto.congr' (hRewriteEventually.mono fun _ hEq ↦ hEq.symm) hMain
  have hApproxTendsto :
      Tendsto lowerApprox (𝓝[>] (0 : ℝ))
        (𝓝 (-((((|x| + δ) ^ 2) / 2 : ℝ) : EReal))) := by
    simpa [lowerApprox] using (EReal.tendsto_coe.2 hApproxReal)
  calc
    -((((|x| + δ) ^ 2) / 2 : ℝ) : EReal) =
        Filter.liminf lowerApprox (𝓝[>] (0 : ℝ)) := hApproxTendsto.liminf_eq.symm
    _ ≤ Filter.liminf (centeredGaussianSmallVarianceExponent (Set.Icc (x - δ) (x + δ)))
          (𝓝[>] (0 : ℝ)) :=
        liminf_le_liminf hEventuallyCompare

/-- Helper for Exercise 23.2.1: a closed set in `ℝ` missing `0` stays a positive distance away
from the origin. -/
private theorem exists_pos_le_abs_of_isClosed_of_zero_not_mem {F : Set ℝ} (hF : IsClosed F)
    (h0 : (0 : ℝ) ∉ F) :
    ∃ r > 0, ∀ x ∈ F, r ≤ |x| := by
  have hnhds : Fᶜ ∈ 𝓝 (0 : ℝ) := hF.isOpen_compl.mem_nhds (by simpa using h0)
  rw [Metric.mem_nhds_iff] at hnhds
  rcases hnhds with ⟨r, hrpos, hrsub⟩
  refine ⟨r, hrpos, ?_⟩
  intro x hx
  -- Proof comment: any point of `F` cannot lie in the open ball around `0` that avoids `F`,
  -- so its absolute value is at least the chosen radius.
  by_contra hxlt
  have hxball : x ∈ Metric.ball (0 : ℝ) r := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hxlt
  exact (hrsub hxball) hx

/-- Helper for Exercise 23.2.1: any strict upper-bound test value above
`-sInf (gaussianQuadraticRateFunctionEReal '' F)` can be converted into a symmetric tail cutoff
for the closed set `F`. -/
private theorem exists_symmetricTailSubset_of_lt_rateInf_closed {F : Set ℝ} {y : ℝ}
    (hF : IsClosed F) (hFne : F.Nonempty) (h0 : (0 : ℝ) ∉ F)
    (hy : ((y : EReal)) > -sInf (gaussianQuadraticRateFunctionEReal '' F)) :
    ∃ r > 0, F ⊆ Set.Iic (-r) ∪ Set.Ici r ∧ -((((r ^ 2) / 2 : ℝ) : EReal)) < (y : EReal) := by
  by_cases hyPos : 0 < y
  · rcases exists_pos_le_abs_of_isClosed_of_zero_not_mem hF h0 with ⟨r, hr, hrabs⟩
    refine ⟨r, hr, ?_, ?_⟩
    · intro x hx
      have hxabs : r ≤ |x| := hrabs x hx
      -- Proof comment: a lower bound on `|x|` rules out the open interval `(-r, r)`, hence `x`
      -- lies in one of the two closed tails.
      by_cases hxle : x ≤ -r
      · exact Or.inl hxle
      · have hxr : r ≤ x := by
          by_contra hxr
          have hxIoo : x ∈ Set.Ioo (-r) r := by
            exact ⟨lt_of_not_ge hxle, lt_of_not_ge hxr⟩
          have hlt : |x| < r := by
            exact (abs_lt.2 hxIoo)
          exact (not_lt_of_ge hxabs) hlt
        exact Or.inr hxr
    · -- Proof comment: when `y` is already positive, any symmetric tail cutoff gives a negative
      -- exponent, hence it is automatically strictly below `y`.
      have hnonneg : 0 ≤ ((r ^ 2) / 2 : ℝ) := by positivity
      have hltReal : -((r ^ 2) / 2 : ℝ) < y := by
        nlinarith
      have hltE : (((-((r ^ 2) / 2 : ℝ)) : ℝ) : EReal) < (y : EReal) := by
        exact_mod_cast hltReal
      simpa using hltE
  · have hyInf : (((-y : ℝ)) : EReal) < sInf (gaussianQuadraticRateFunctionEReal '' F) := by
      simpa using EReal.neg_strictAnti hy
    rcases hFne with ⟨x₀, hx₀⟩
    rcases exists_between hyInf with ⟨z, hyz, hzInf⟩
    have hzTop : z ≠ ⊤ := by
      exact ne_top_of_lt (lt_of_lt_of_le hzInf (sInf_le ⟨x₀, hx₀, rfl⟩))
    have hzBot : z ≠ ⊥ := ne_bot_of_gt hyz
    let a : ℝ := z.toReal
    have haEq : ((a : ℝ) : EReal) = z := by
      simpa [a] using EReal.coe_toReal hzTop hzBot
    have haPos : 0 < a := by
      have hnonneg : 0 ≤ -y := by
        nlinarith [le_of_not_gt hyPos]
      have hlt : (0 : EReal) < (a : ℝ) := by
        rw [haEq]
        exact lt_of_le_of_lt (by exact_mod_cast hnonneg) hyz
      exact_mod_cast hlt
    let r : ℝ := Real.sqrt (2 * a)
    have hrPos : 0 < r := by
      dsimp [r]
      apply Real.sqrt_pos.2
      positivity
    refine ⟨r, hrPos, ?_, ?_⟩
    · intro x hx
      have haxE : ((a : ℝ) : EReal) < gaussianQuadraticRateFunctionEReal x := by
        rw [haEq]
        exact lt_of_lt_of_le hzInf (sInf_le ⟨x, hx, rfl⟩)
      have hax : a < x ^ 2 / 2 := by
        rw [gaussianQuadraticRateFunctionEReal_eq_half_sq x] at haxE
        exact_mod_cast haxE
      have hrSq : r ^ 2 = 2 * a := by
        dsimp [r]
        rw [Real.sq_sqrt]
        positivity
      have hsq : r ^ 2 < |x| ^ 2 := by
        have : r ^ 2 < x ^ 2 := by
          nlinarith [hax, hrSq]
        simpa [sq_abs] using this
      have hxabs : r < |x| := by
        nlinarith [hsq, hrPos, abs_nonneg x]
      -- Proof comment: the strict quadratic lower bound forces `|x|` past the cutoff radius, so
      -- `x` belongs to one of the two closed tails.
      by_cases hxle : x ≤ -r
      · exact Or.inl hxle
      · have hxr : r ≤ x := by
          by_contra hxr
          have hxIoo : x ∈ Set.Ioo (-r) r := by
            exact ⟨lt_of_not_ge hxle, lt_of_not_ge hxr⟩
          have hlt : |x| < r := by
            exact (abs_lt.2 hxIoo)
          exact (not_le_of_gt hxabs) hlt.le
        exact Or.inr hxr
    · -- Proof comment: the extra gap `a > -y` turns the quadratic tail rate at `r` into a strict
      -- inequality below the test value `y`.
      have hay : -y < a := by
        rw [← haEq] at hyz
        exact_mod_cast hyz
      have hrSq : r ^ 2 = 2 * a := by
        dsimp [r]
        rw [Real.sq_sqrt]
        positivity
      have hltReal : -((r ^ 2) / 2 : ℝ) < y := by
        nlinarith
      exact_mod_cast hltReal

-- Proof sketch: evaluate the Gaussian cumulant generating function, derive the exponential lower
-- bound by the standard Laplace-Varadhan argument, and identify the Legendre transform with
-- `x ↦ x^2 / 2` as `ε ↓ 0`.
/-- Exercise 23.2.1 (2): for every open set `G ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP lower bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_lowerBound :
    ∀ G : Set ℝ, IsOpen G →
      -sInf (gaussianQuadraticRateFunctionEReal '' G) ≤
        Filter.liminf (centeredGaussianSmallVarianceExponent G) (𝓝[>] (0 : ℝ)) := by
  intro G hG
  by_cases hEmpty : G = ∅
  · simp [hEmpty]
  have hGne : G.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
  rw [Filter.le_liminf_iff']
  intro y hy
  by_cases hyBot : y = ⊥
  · -- Proof comment: the bottom comparison value is eventually below every exponent term.
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    simp [hyBot]
  have hyTop : y ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hy le_top)
  let yr : ℝ := y.toReal
  have hyr : ((yr : ℝ) : EReal) = y := by
    simpa [yr] using EReal.coe_toReal hyTop hyBot
  have hyInf : sInf (gaussianQuadraticRateFunctionEReal '' G) < -y := by
    simpa using EReal.neg_strictAnti hy
  obtain ⟨z, hzInf, hzy⟩ := exists_between hyInf
  obtain ⟨w, hwImage, hwz⟩ :=
    exists_lt_of_csInf_lt (s := gaussianQuadraticRateFunctionEReal '' G)
      (show (gaussianQuadraticRateFunctionEReal '' G).Nonempty from
        hGne.image gaussianQuadraticRateFunctionEReal)
      hzInf
  rcases hwImage with ⟨x, hxG, rfl⟩
  have hyRate : y < -gaussianQuadraticRateFunctionEReal x := by
    have hyzNeg : y < -z := by
      simpa using EReal.neg_strictAnti hzy
    have hzwNeg : -z < -gaussianQuadraticRateFunctionEReal x := by
      simpa using EReal.neg_strictAnti hwz
    exact hyzNeg.trans hzwNeg
  have hyRateReal : yr < -(x ^ 2 / 2 : ℝ) := by
    have hyRateE :
        ((yr : ℝ) : EReal) < -(((x ^ 2 / 2 : ℝ) : EReal)) := by
      rw [hyr]
      simpa [gaussianQuadraticRateFunctionEReal_eq_half_sq x] using hyRate
    exact_mod_cast hyRateE
  rcases Metric.isOpen_iff.mp hG x hxG with ⟨r, hrPos, hrSub⟩
  let rateAround : ℝ → ℝ := fun d ↦ -(((|x| + d) ^ 2) / 2)
  have hRateCont : Continuous rateAround := by
    continuity
  have hRateAtZero : yr < rateAround 0 := by
    simpa [rateAround, sq_abs] using hyRateReal
  have hRateOpen : IsOpen (rateAround ⁻¹' Set.Ioi yr) := by
    exact isOpen_Ioi.preimage hRateCont
  have hRateZeroMem : (0 : ℝ) ∈ rateAround ⁻¹' Set.Ioi yr := by
    simpa [rateAround] using hRateAtZero
  rcases Metric.isOpen_iff.mp hRateOpen 0 hRateZeroMem with ⟨ρ, hρPos, hρSub⟩
  let d : ℝ := min (r / 2) (ρ / 2)
  have hdPos : 0 < d := by
    have hrHalfPos : 0 < r / 2 := by
      positivity
    have hRhoHalfPos : 0 < ρ / 2 := by
      positivity
    dsimp [d]
    exact lt_min hrHalfPos hRhoHalfPos
  have hdLtR : d < r := by
    have hdLe : d ≤ r / 2 := by
      dsimp [d]
      exact min_le_left _ _
    nlinarith
  have hdLtRho : d < ρ := by
    have hdLe : d ≤ ρ / 2 := by
      dsimp [d]
      exact min_le_right _ _
    nlinarith
  have hRateAtDReal : yr < rateAround d := by
    have hBall0 : d ∈ Metric.ball (0 : ℝ) ρ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hdPos.le] using hdLtRho
    exact hρSub hBall0
  have hRateAtD :
      y < -((((|x| + d) ^ 2) / 2 : ℝ) : EReal) := by
    rw [← hyr]
    dsimp [rateAround] at hRateAtDReal
    exact_mod_cast hRateAtDReal
  have hIccSubset : Set.Icc (x - d) (x + d) ⊆ G := by
    -- Proof comment: every point of the chosen interval stays inside the open ball furnished by
    -- openness of `G`, so the whole interval lies in `G`.
    intro t ht
    have hAbs : |t - x| ≤ d := by
      refine abs_le.2 ?_
      constructor <;> linarith [ht.1, ht.2]
    have hBall : t ∈ Metric.ball x r := by
      simpa [Metric.mem_ball, Real.dist_eq] using lt_of_le_of_lt hAbs hdLtR
    exact hrSub hBall
  have hIntervalLiminf :
      y < Filter.liminf
        (centeredGaussianSmallVarianceExponent (Set.Icc (x - d) (x + d)))
        (𝓝[>] (0 : ℝ)) := by
    exact lt_of_lt_of_le hRateAtD
      (centeredGaussianSmallVarianceExponent_Icc_lowerBound (x := x) (δ := d) hdPos)
  have hEventuallyInterval :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        y < centeredGaussianSmallVarianceExponent (Set.Icc (x - d) (x + d)) ε := by
    exact eventually_lt_of_lt_liminf hIntervalLiminf
  have hEventuallyMono :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        centeredGaussianSmallVarianceExponent (Set.Icc (x - d) (x + d)) ε ≤
          centeredGaussianSmallVarianceExponent G ε := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    exact centeredGaussianSmallVarianceExponent_mono hIccSubset hε
  filter_upwards [hEventuallyInterval, hEventuallyMono] with ε hyε hMono
  exact hyε.le.trans hMono

-- Proof sketch: apply Gaussian tail estimates or exponential Chebyshev bounds on closed sets,
-- optimize the exponent, and obtain the negative infimum of the quadratic rate function.
/-- Exercise 23.2.1 (3): for every closed set `F ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP upper bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_upperBound :
    ∀ F : Set ℝ, IsClosed F →
      Filter.limsup (centeredGaussianSmallVarianceExponent F) (𝓝[>] (0 : ℝ)) ≤
        -sInf (gaussianQuadraticRateFunctionEReal '' F) := by
  intro F hF
  by_cases hEmpty : F = ∅
  · have hEventually :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          centeredGaussianSmallVarianceExponent (∅ : Set ℝ) ε = ⊥ := by
      -- Proof comment: the empty set has Gaussian mass `0`, hence its scaled logarithmic mass is
      -- eventually `-∞`.
      filter_upwards [eventually_mem_nhdsWithin] with ε hε
      have hεE : 0 < (ε : EReal) := by
        exact_mod_cast hε
      have hEmptyExp :
          centeredGaussianSmallVarianceExponent (∅ : Set ℝ) ε = (ε : EReal) * ⊥ := by
        rw [centeredGaussianSmallVarianceExponent]
        simp [centeredGaussianSmallVarianceLaw]
      rw [hEmptyExp]
      simpa using EReal.mul_bot_of_pos hεE
    have hEmptyLimsup :
        Filter.limsup (centeredGaussianSmallVarianceExponent (∅ : Set ℝ)) (𝓝[>] (0 : ℝ)) ≤
          -sInf (gaussianQuadraticRateFunctionEReal '' (∅ : Set ℝ)) := by
      rw [Filter.limsup_congr hEventually]
      simp
    simpa [hEmpty] using hEmptyLimsup
  by_cases h0 : (0 : ℝ) ∈ F
  · have hEventually :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), centeredGaussianSmallVarianceExponent F ε ≤ 0 := by
      -- Proof comment: every event has probability at most `1`, so the scaled log-masses are
      -- eventually nonpositive.
      filter_upwards [eventually_mem_nhdsWithin] with ε hε
      exact centeredGaussianSmallVarianceExponent_nonpos hε
    have hLimsupNonpos :
        Filter.limsup (centeredGaussianSmallVarianceExponent F) (𝓝[>] (0 : ℝ)) ≤ 0 :=
      limsup_le_of_le
        (hf := by
          simpa [Filter.IsCoboundedUnder] using
            (Filter.isCobounded_le_of_bot :
              (Filter.map (centeredGaussianSmallVarianceExponent F) (𝓝[>] (0 : ℝ))).IsCobounded
                (· ≤ ·)))
        hEventually
    have hZeroMem : (0 : EReal) ∈ gaussianQuadraticRateFunctionEReal '' F := by
      refine ⟨0, h0, ?_⟩
      simp [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction]
    have hRateNonneg :
        ∀ z ∈ gaussianQuadraticRateFunctionEReal '' F, (0 : EReal) ≤ z := by
      rintro z ⟨x, hx, rfl⟩
      rw [gaussianQuadraticRateFunctionEReal_eq_half_sq x]
      positivity
    have hsInfEq : sInf (gaussianQuadraticRateFunctionEReal '' F) = (0 : EReal) := by
      refine le_antisymm (sInf_le hZeroMem) (le_sInf hRateNonneg)
    simpa [hsInfEq] using hLimsupNonpos
  have hFne : F.Nonempty := by
    by_contra hFne
    exact hEmpty (Set.not_nonempty_iff_eq_empty.mp hFne)
  rw [Filter.limsup_le_iff']
  intro y hy
  by_cases hyTop : y = ⊤
  · simp [hyTop]
  obtain ⟨z, hzLeft, hzRight⟩ := exists_between hy
  have hzBot : z ≠ ⊥ := ne_bot_of_gt hzLeft
  have hzTop : z ≠ ⊤ := ne_top_of_lt (hzRight.trans_le le_top)
  let yz : ℝ := z.toReal
  have hyz : ((yz : ℝ) : EReal) > -sInf (gaussianQuadraticRateFunctionEReal '' F) := by
    -- Proof comment: choose a finite real test value strictly between the target upper bound and
    -- the ambient comparison point `y`.
    rw [EReal.coe_toReal hzTop hzBot]
    exact hzLeft
  rcases exists_symmetricTailSubset_of_lt_rateInf_closed hF hFne h0 hyz with
    ⟨r, hr, hSubset, hTailRateLt⟩
  have hMonoEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        centeredGaussianSmallVarianceExponent F ε ≤
          centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε := by
    -- Proof comment: once the closed set is contained in the symmetric tail event, monotonicity
    -- transfers the tail estimate to `F`.
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    exact centeredGaussianSmallVarianceExponent_mono hSubset hε
  have hTailEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε < z := by
    have hTailLimsupLt :
        Filter.limsup
            (centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r))
            (𝓝[>] (0 : ℝ)) < z := by
      -- Proof comment: the symmetric-tail limsup is already strictly below the chosen comparison
      -- point by the cutoff lemma.
      rw [← EReal.coe_toReal hzTop hzBot]
      exact (centeredGaussianSmallVarianceExponent_symmetricTail_upperBound hr).trans_lt hTailRateLt
    exact eventually_lt_of_limsup_lt hTailLimsupLt
  filter_upwards [hMonoEventually, hTailEventually] with ε hεMono hεTail
  exact hεMono.trans (hεTail.le.trans hzRight.le)

-- Proof sketch: choose the closed set `{0}`. Since every nondegenerate Gaussian `N(0, ε)` is
-- atomless, `μ_ε({0}) = 0` for all `ε > 0`, so the left-hand side is `-∞`, while the rate side is
-- `-I(0) = 0`.
/-- Exercise 23.2.1 (4): the closed set `{0}` gives a strict instance of the LDP upper bound for
`μ_ε = N(0, ε)`, so equality need not hold in (LDP 2). -/
theorem centeredGaussianSmallVariance_ldp_upperBound_strictAtSingletonZero :
    Filter.limsup (centeredGaussianSmallVarianceExponent ({0} : Set ℝ)) (𝓝[>] (0 : ℝ)) <
      -sInf (gaussianQuadraticRateFunctionEReal '' ({0} : Set ℝ)) := by
  have hEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), centeredGaussianSmallVarianceExponent ({0} : Set ℝ) ε = ⊥ := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hExp :
        centeredGaussianSmallVarianceExponent ({0} : Set ℝ) ε =
          (ε : EReal) * ⊥ := by
      -- The singleton mass vanishes for every positive variance.
      rw [centeredGaussianSmallVarianceExponent, centeredGaussianSmallVarianceLaw_singletonZero hε,
        ENNReal.log_zero]
    have hεE : 0 < (ε : EReal) := by
      exact_mod_cast hε
    -- Multiplying a positive coefficient by `⊥` keeps the exponent at `⊥`.
    rw [hExp]
    simpa using EReal.mul_bot_of_pos hεE
  have hRateImage :
      gaussianQuadraticRateFunctionEReal '' ({0} : Set ℝ) = ({0} : Set EReal) := by
    -- The rate function takes the value `0` at the unique point of the singleton.
    ext y
    simp [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction]
  -- Compare `-∞` on the left with the exact rate value `0` on the right.
  have hLimsupEq :
      Filter.limsup (centeredGaussianSmallVarianceExponent ({0} : Set ℝ)) (𝓝[>] (0 : ℝ)) = ⊥ := by
    rw [Filter.limsup_congr hEventually, Filter.limsup_const_bot]
  rw [hLimsupEq, hRateImage, sInf_singleton, neg_zero]
  simp

end ProbabilityTheory

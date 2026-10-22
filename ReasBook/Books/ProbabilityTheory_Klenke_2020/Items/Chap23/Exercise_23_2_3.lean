/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- Helper for Exercise 23.2.3: the positive-parameter filter is nontrivial because `ε > 0`
approaches `0` from the right along a nonempty neighborhood basis. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Exercise 23.2.3: the Gaussian branch centered at `m`. -/
private def shiftedGaussianFamily (m : ℝ) (ε : PositiveParameter) : Measure ℝ :=
  gaussianReal m (Real.toNNReal (ε : ℝ))

/-- Helper for Exercise 23.2.3: the quadratic branch rate centered at `m`. -/
private def shiftedQuadraticRate (m x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((x - m) ^ (2 : ℕ)) / 2)

/-- Helper for Exercise 23.2.3: the fixed logarithmic correction from the branch weight `1 / 2`.
-/
private def halfWeightCorrection (ε : PositiveParameter) : EReal :=
  ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞)

/-- Helper for Exercise 23.2.3: forgetting the positivity subtype sends the positive-parameter
filter back to the standard right-neighborhood filter at `0`. -/
private theorem map_positiveParameterFilter :
    Filter.map ((↑) : PositiveParameter → ℝ) positiveParameterFilter = 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `positiveParameterFilter` is defined as the comap of the subtype coercion, and
  -- the coercion range is exactly `(0, ∞)`, which is a member of `𝓝[>] 0`.
  rw [positiveParameterFilter]
  refine Filter.map_comap_of_mem ?_
  simpa [PositiveParameter, Subtype.range_coe] using
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))

/-- The Gaussian-mixture family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` from the exercise, indexed by `ε > 0`. -/
def twoPointGaussianMixtureMeasureFamily (ε : PositiveParameter) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
    (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε)

/-- The rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)` from the exercise, valued in
`ℝ≥0∞`. -/
def twoWellQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)))

/-- Helper for Exercise 23.2.3: enlarging the underlying set can only increase the scaled
logarithmic mass. -/
private theorem scaledLogMassAlong_mono
    (μ : PositiveParameter → Measure ℝ) {s t : Set ℝ} (hst : s ⊆ t) (ε : PositiveParameter) :
    scaledLogMassAlong μ id s ε ≤ scaledLogMassAlong μ id t ε := by
  -- Proof comment: expand the logarithmic mass once, then use monotonicity of measure and of
  -- `ENNReal.log`.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (measure_mono hst)) hε

/-- Helper for Exercise 23.2.3: every shifted Gaussian scaled logarithmic mass is nonpositive,
because each branch is a probability measure. -/
private theorem shiftedGaussianExponent_nonpos (m : ℝ) {s : Set ℝ} (ε : PositiveParameter) :
    scaledLogMassAlong (shiftedGaussianFamily m) id s ε ≤ 0 := by
  -- Proof comment: every event has branch mass at most `1`, so its logarithm is nonpositive and
  -- the positive coefficient `ε` preserves the order.
  rw [scaledLogMassAlong_def]
  have hmass : shiftedGaussianFamily m ε s ≤ 1 := by
    calc
      shiftedGaussianFamily m ε s ≤ shiftedGaussianFamily m ε Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := by
        simp [shiftedGaussianFamily]
  have hlog : ENNReal.log (shiftedGaussianFamily m ε s) ≤ 0 := by
    simpa using
      (ENNReal.log_le_log hmass :
        ENNReal.log (shiftedGaussianFamily m ε s) ≤ ENNReal.log (1 : ℝ≥0∞))
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  exact mul_nonpos_of_nonneg_of_nonpos hε hlog

-- Proof sketch: unfold `twoPointGaussianMixtureMeasureFamily`; this is exactly the textbook
-- definition of the
-- Gaussian mixture `μ_ε`.
/-- Expanding `twoPointGaussianMixtureMeasureFamily` gives the explicit symmetric mixture of the
two Gaussian
laws centered at `-1` and `1` with variance parameter `ε`. -/
theorem twoPointGaussianMixtureMeasureFamily_def (ε : PositiveParameter) :
    twoPointGaussianMixtureMeasureFamily ε =
      (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
        (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε) := by
  -- This is just the defining expansion of the mixture family.
  rfl

/-- Each Gaussian mixture `μ_ε` is a probability measure. -/
theorem twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure (ε : PositiveParameter) :
    IsProbabilityMeasure (twoPointGaussianMixtureMeasureFamily ε) := by
  refine ⟨by
    simp [twoPointGaussianMixtureMeasureFamily, one_div, ENNReal.inv_two_add_inv_two]
  ⟩

-- Proof sketch: unfold `twoWellQuadraticRateFunction`; the statement is exactly the explicit
-- formula
-- displayed in the exercise, rewritten as an `ℝ≥0∞`-valued function.
/-- Expanding `twoWellQuadraticRateFunction` gives the explicit formula
`x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem twoWellQuadraticRateFunction_def (x : ℝ) :
    twoWellQuadraticRateFunction x =
      ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ))) := by
  -- This is the defining formula for the two-well quadratic rate.
  rfl

/-- Helper for Exercise 23.2.3: the finite sublevel sets of the two-well quadratic rate are the
union of the compact intervals around the wells at `-1` and `1`. -/
theorem twoWellQuadraticRateFunction_sublevel_eq_union_Icc (a : ℝ≥0) :
    twoWellQuadraticRateFunction ⁻¹' Set.Iic (a : ℝ≥0∞) =
      Set.Icc (-1 - Real.sqrt (2 * (a : ℝ))) (-1 + Real.sqrt (2 * (a : ℝ))) ∪
        Set.Icc (1 - Real.sqrt (2 * (a : ℝ))) (1 + Real.sqrt (2 * (a : ℝ))) := by
  ext x
  constructor
  · intro hx
    -- Convert the `ℝ≥0∞` inequality into the corresponding real quadratic bound.
    have hx' :
        ((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ (a : ℝ) := by
      exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hx
    have hmin : min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ 2 * (a : ℝ) := by
      nlinarith
    rcases min_le_iff.mp hmin with hleft | hright
    · -- If the left branch is cheaper, `x` lies in the interval around `-1`.
      have hleftBounds :
          -Real.sqrt (2 * (a : ℝ)) ≤ x + 1 ∧ x + 1 ≤ Real.sqrt (2 * (a : ℝ)) := by
        exact (Real.sq_le (by positivity)).mp hleft
      rcases hleftBounds with ⟨hlo, hhi⟩
      exact Or.inl ⟨by nlinarith, by nlinarith⟩
    · -- If the right branch is cheaper, `x` lies in the interval around `1`.
      have hrightBounds :
          -Real.sqrt (2 * (a : ℝ)) ≤ x - 1 ∧ x - 1 ≤ Real.sqrt (2 * (a : ℝ)) := by
        exact (Real.sq_le (by positivity)).mp hright
      rcases hrightBounds with ⟨hlo, hhi⟩
      exact Or.inr ⟨by nlinarith, by nlinarith⟩
  · intro hx
    rcases hx with hx | hx
    · -- Membership in the left interval gives a quadratic bound for the left branch.
      have hleft :
          (x + 1) ^ (2 : ℕ) ≤ 2 * (a : ℝ) := by
        refine (Real.sq_le (by positivity)).mpr ?_
        rcases hx with ⟨hlo, hhi⟩
        exact ⟨by nlinarith, by nlinarith⟩
      have hmin : min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ 2 * (a : ℝ) := by
        exact le_trans (min_le_left _ _) hleft
      have hx' :
          ((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ (a : ℝ) := by
        nlinarith
      exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).2 hx'
    · -- Membership in the right interval gives the symmetric quadratic bound.
      have hright :
          (x - 1) ^ (2 : ℕ) ≤ 2 * (a : ℝ) := by
        refine (Real.sq_le (by positivity)).mpr ?_
        rcases hx with ⟨hlo, hhi⟩
        exact ⟨by nlinarith, by nlinarith⟩
      have hmin : min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ 2 * (a : ℝ) := by
        exact le_trans (min_le_right _ _) hright
      have hx' :
          ((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)) ≤ (a : ℝ) := by
        nlinarith
      exact (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).2 hx'

/-- The two-well quadratic rate function is a good rate function on `ℝ`. -/
instance instIsGoodRateFunctionTwoWellQuadraticRateFunction :
    IsGoodRateFunction twoWellQuadraticRateFunction := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the two-well quadratic cost is continuous as the minimum of two continuous
    -- quadratics, so its `ENNReal.ofReal` lift is lower semicontinuous.
    have hEq :
        twoWellQuadraticRateFunction =
          fun x : ℝ ↦
            min (ENNReal.ofReal (((x + 1) ^ (2 : ℕ)) / 2))
              (ENNReal.ofReal (((x - 1) ^ (2 : ℕ)) / 2)) := by
      funext x
      let a : ℝ := (x + 1) ^ (2 : ℕ)
      let b : ℝ := (x - 1) ^ (2 : ℕ)
      rcases le_total a b with hab | hba
      · rw [twoWellQuadraticRateFunction, min_eq_left hab, min_eq_left]
        · congr 1
          dsimp [a]
          ring
        · exact ENNReal.ofReal_le_ofReal <| by
            dsimp [a, b] at hab ⊢
            nlinarith
      · rw [twoWellQuadraticRateFunction, min_eq_right hba, min_eq_right]
        · congr 1
          dsimp [b]
          ring
        · exact ENNReal.ofReal_le_ofReal <| by
            dsimp [a, b] at hba ⊢
            nlinarith
    have hcontLeft :
        Continuous fun x : ℝ ↦ ENNReal.ofReal (((x + 1) ^ (2 : ℕ)) / 2) := by
      simpa using
        (ENNReal.continuous_ofReal.comp
          (((continuous_id.add_const 1).pow 2).div_const (2 : ℝ)))
    have hcontRight :
        Continuous fun x : ℝ ↦ ENNReal.ofReal (((x - 1) ^ (2 : ℕ)) / 2) := by
      simpa using
        (ENNReal.continuous_ofReal.comp
          (((continuous_id.add_const (-1)).pow 2).div_const (2 : ℝ)))
    rw [hEq]
    exact (hcontLeft.min hcontRight).lowerSemicontinuous
  · intro a
    -- Proof comment: the explicit sublevel description is a union of two compact intervals.
    rw [twoWellQuadraticRateFunction_sublevel_eq_union_Icc]
    exact isCompact_Icc.union isCompact_Icc

/-- Helper for Exercise 23.2.3: the centered quadratic rate `x ↦ x^2 / 2`, viewed in `ℝ≥0∞`. -/
private def gaussianQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (x ^ 2 / 2)

/-- Helper for Exercise 23.2.3: the centered quadratic rate viewed in `EReal`. -/
private def gaussianQuadraticRateFunctionEReal (x : ℝ) : EReal :=
  gaussianQuadraticRateFunction x

/-- Helper for Exercise 23.2.3: the centered small-variance Gaussian family indexed by real
parameters. -/
private def centeredGaussianSmallVarianceLaw (ε : ℝ) : Measure ℝ :=
  gaussianReal 0 (Real.toNNReal ε)

/-- Helper for Exercise 23.2.3: the centered scaled logarithmic mass `ε log μ_ε(s)`. -/
private def centeredGaussianSmallVarianceExponent (s : Set ℝ) (ε : ℝ) : EReal :=
  (ε : EReal) * ENNReal.log (centeredGaussianSmallVarianceLaw ε s)

/-- Helper for Exercise 23.2.3: the centered small-variance Gaussian family reindexed by positive
parameters. -/
private def centeredGaussianPositiveFamily (ε : PositiveParameter) : Measure ℝ :=
  centeredGaussianSmallVarianceLaw (ε : ℝ)

/-- Helper for Exercise 23.2.3: enlarging the underlying event can only increase the centered
scaled logarithmic mass when the variance parameter is positive. -/
private theorem centeredGaussianSmallVarianceExponent_mono {s t : Set ℝ} (hst : s ⊆ t)
    {ε : ℝ} (hε : 0 < ε) :
    centeredGaussianSmallVarianceExponent s ε ≤ centeredGaussianSmallVarianceExponent t ε := by
  -- Proof comment: monotonicity of the measure passes through `ENNReal.log`, and the positive
  -- prefactor `ε` preserves the order.
  rw [centeredGaussianSmallVarianceExponent, centeredGaussianSmallVarianceExponent]
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (measure_mono hst)) hεE

/-- Helper for Exercise 23.2.3: viewed in `EReal`, the centered quadratic rate is the ordinary
real quadratic `x^2 / 2`. -/
private theorem gaussianQuadraticRateFunctionEReal_eq_half_sq (x : ℝ) :
    gaussianQuadraticRateFunctionEReal x = ((x ^ 2 / 2 : ℝ) : EReal) := by
  -- Proof comment: `x ^ 2 / 2` is nonnegative, so the `ENNReal.ofReal` coercion is the same as
  -- the direct real-to-`EReal` coercion.
  have hx : 0 ≤ x ^ 2 / 2 := by
    positivity
  rw [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction,
    ENNReal.ofReal_eq_coe_nnreal hx]
  rfl

/-- Helper for Exercise 23.2.3: every centered scaled logarithmic mass is nonpositive because a
probability measure assigns mass at most `1` to every event. -/
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
      (ENNReal.log_le_log hmass :
        ENNReal.log (centeredGaussianSmallVarianceLaw ε s) ≤ ENNReal.log (1 : ENNReal))
  have hεE : 0 ≤ (ε : EReal) := by
    exact_mod_cast le_of_lt hε
  exact mul_nonpos_of_nonneg_of_nonpos hεE hlog

/-- Helper for Exercise 23.2.3: reindexing the centered exponent by positive parameters is just
composition with the subtype coercion. -/
private theorem centeredGaussianPositiveExponent_eq (s : Set ℝ) :
    scaledLogMassAlong centeredGaussianPositiveFamily id s =
      centeredGaussianSmallVarianceExponent s ∘ ((↑) : PositiveParameter → ℝ) := by
  -- Proof comment: both sides expand to the same term `ε * log μ_ε(s)` once the subtype coercion
  -- is unfolded.
  funext ε
  rfl

/-- Helper for Exercise 23.2.3: the two-sided centered Gaussian tail outside `[-r, r]` is bounded
by the standard Chernoff estimate `2 * exp (-r^2 / (2ε))`. -/
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
      -- variable under the centered Gaussian law.
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

/-- Helper for Exercise 23.2.3: the scaled logarithmic mass of the symmetric tail event is bounded
above by the quadratic rate `-r^2 / 2`, up to the vanishing prefactor `ε log 2`. -/
private theorem centeredGaussianSmallVarianceExponent_symmetricTail_le {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) :
    centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε ≤
      ((ε * Real.log 2 - r ^ 2 / 2 : ℝ) : EReal) := by
  let tail : Set ℝ := Set.Iic (-r) ∪ Set.Ici r
  let bound : ℝ := 2 * Real.exp (-(r ^ 2) / (2 * ε))
  letI : IsFiniteMeasure (centeredGaussianSmallVarianceLaw ε) := by
    dsimp [centeredGaussianSmallVarianceLaw]
    infer_instance
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

/-- Helper for Exercise 23.2.3: the limsup of the symmetric tail logarithmic mass is bounded by
`-r^2 / 2`. -/
private theorem centeredGaussianSmallVarianceExponent_symmetricTail_upperBound
    {r : ℝ} (hr : 0 < r) :
    Filter.limsup
        (centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r))
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

/-- Helper for Exercise 23.2.3: on a compact interval centered at `x`, the Gaussian density is
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

/-- Helper for Exercise 23.2.3: on a compact interval centered at `x`, the centered Gaussian mass
admits a uniform density lower bound. -/
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

/-- Helper for Exercise 23.2.3: the explicit interval mass lower bound turns into a corresponding
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

/-- Helper for Exercise 23.2.3: the interval lower approximation converges to the quadratic rate
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
    have hεpos : 0 < ε := by
      simpa using hε
    have hTwoDeltaNe : 2 * δ ≠ 0 := by
      positivity
    have hTwoPiNe : 2 * Real.pi ≠ 0 := by
      positivity
    have hTwoPiPos : 0 < 2 * Real.pi * ε := by
      nlinarith [Real.pi_pos, hεpos]
    rw [Real.log_mul hTwoDeltaNe]
    · rw [Real.log_inv, Real.log_sqrt hTwoPiPos.le, Real.log_mul hTwoPiNe hεpos.ne']
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

/-- Helper for Exercise 23.2.3: a closed set in `ℝ` missing `0` stays a positive distance away
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

/-- Helper for Exercise 23.2.3: any strict upper-bound test value above
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
  · have hyNonpos : y ≤ 0 := le_of_not_gt hyPos
    have hyInf : (((-y : ℝ)) : EReal) < sInf (gaussianQuadraticRateFunctionEReal '' F) := by
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
      have hnonneg : 0 ≤ -y := by nlinarith
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

/-- Helper for Exercise 23.2.3: the centered Gaussian open-set lower bound on the real
right-neighborhood filter. -/
private theorem centeredGaussianSmallVariance_openLowerBound_real {U : Set ℝ} (hU : IsOpen U) :
    -sInf (gaussianQuadraticRateFunctionEReal '' U) ≤
      Filter.liminf (centeredGaussianSmallVarianceExponent U) (𝓝[>] (0 : ℝ)) := by
  by_cases hEmpty : U = ∅
  · simp [hEmpty]
  have hUne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
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
  have hyInf : sInf (gaussianQuadraticRateFunctionEReal '' U) < -y := by
    simpa using EReal.neg_strictAnti hy
  obtain ⟨z, hzInf, hzy⟩ := exists_between hyInf
  obtain ⟨w, hwImage, hwz⟩ :=
    exists_lt_of_csInf_lt (s := gaussianQuadraticRateFunctionEReal '' U)
      (show (gaussianQuadraticRateFunctionEReal '' U).Nonempty from
        hUne.image gaussianQuadraticRateFunctionEReal)
      hzInf
  rcases hwImage with ⟨x, hxU, rfl⟩
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
  rcases Metric.isOpen_iff.mp hU x hxU with ⟨r, hrPos, hrSub⟩
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
    have hrHalfPos : 0 < r / 2 := by positivity
    have hRhoHalfPos : 0 < ρ / 2 := by positivity
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
  have hIccSubset : Set.Icc (x - d) (x + d) ⊆ U := by
    -- Proof comment: every point of the chosen interval stays inside the open ball furnished by
    -- openness of `U`, so the whole interval lies in `U`.
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
          centeredGaussianSmallVarianceExponent U ε := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    exact centeredGaussianSmallVarianceExponent_mono hIccSubset hε
  filter_upwards [hEventuallyInterval, hEventuallyMono] with ε hyε hMono
  exact hyε.le.trans hMono

/-- Helper for Exercise 23.2.3: the centered Gaussian closed-set upper bound on the real
right-neighborhood filter. -/
private theorem centeredGaussianSmallVariance_closedUpperBound_real {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup (centeredGaussianSmallVarianceExponent C) (𝓝[>] (0 : ℝ)) ≤
      -sInf (gaussianQuadraticRateFunctionEReal '' C) := by
  by_cases hEmpty : C = ∅
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
  by_cases h0 : (0 : ℝ) ∈ C
  · have hEventually :
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), centeredGaussianSmallVarianceExponent C ε ≤ 0 := by
      -- Proof comment: every event has probability at most `1`, so the scaled log-masses are
      -- eventually nonpositive.
      filter_upwards [eventually_mem_nhdsWithin] with ε hε
      exact centeredGaussianSmallVarianceExponent_nonpos hε
    have hLimsupNonpos :
        Filter.limsup (centeredGaussianSmallVarianceExponent C) (𝓝[>] (0 : ℝ)) ≤ 0 :=
      limsup_le_of_le
        (hf := by
          simpa [Filter.IsCoboundedUnder] using
            (Filter.isCobounded_le_of_bot :
              (Filter.map (centeredGaussianSmallVarianceExponent C) (𝓝[>] (0 : ℝ))).IsCobounded
                (· ≤ ·)))
        hEventually
    have hZeroMem : (0 : EReal) ∈ gaussianQuadraticRateFunctionEReal '' C := by
      refine ⟨0, h0, ?_⟩
      simp [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction]
    have hRateNonneg :
        ∀ z ∈ gaussianQuadraticRateFunctionEReal '' C, (0 : EReal) ≤ z := by
      rintro z ⟨x, hx, rfl⟩
      rw [gaussianQuadraticRateFunctionEReal_eq_half_sq x]
      positivity
    have hsInfEq : sInf (gaussianQuadraticRateFunctionEReal '' C) = (0 : EReal) := by
      refine le_antisymm (sInf_le hZeroMem) (le_sInf hRateNonneg)
    simpa [hsInfEq] using hLimsupNonpos
  have hCne : C.Nonempty := by
    by_contra hCne
    exact hEmpty (Set.not_nonempty_iff_eq_empty.mp hCne)
  rw [Filter.limsup_le_iff']
  intro y hy
  by_cases hyTop : y = ⊤
  · simp [hyTop]
  obtain ⟨z, hzLeft, hzRight⟩ := exists_between hy
  have hzBot : z ≠ ⊥ := ne_bot_of_gt hzLeft
  have hzTop : z ≠ ⊤ := ne_top_of_lt (hzRight.trans_le le_top)
  let yz : ℝ := z.toReal
  have hyz : ((yz : ℝ) : EReal) > -sInf (gaussianQuadraticRateFunctionEReal '' C) := by
    -- Proof comment: choose a finite real test value strictly between the target upper bound and
    -- the ambient comparison point `y`.
    rw [EReal.coe_toReal hzTop hzBot]
    exact hzLeft
  rcases exists_symmetricTailSubset_of_lt_rateInf_closed hC hCne h0 hyz with
    ⟨r, hr, hSubset, hTailRateLt⟩
  have hMonoEventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        centeredGaussianSmallVarianceExponent C ε ≤
          centeredGaussianSmallVarianceExponent (Set.Iic (-r) ∪ Set.Ici r) ε := by
    -- Proof comment: once the closed set is contained in the symmetric tail event, monotonicity
    -- transfers the tail estimate to `C`.
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

/-- Helper for Exercise 23.2.3: the interval lower bound transported to the positive-parameter
filter. -/
private theorem centeredGaussianPositive_intervalLiminfLowerBound {x δ : ℝ} (hδ : 0 < δ) :
    -((((|x| + δ) ^ 2) / 2 : ℝ) : EReal) ≤
      Filter.liminf (scaledLogMassAlong centeredGaussianPositiveFamily id (Set.Icc (x - δ) (x + δ)))
        positiveParameterFilter := by
  -- Route correction: keep the analytic proof on `𝓝[>] (0 : ℝ)` and transport it once through
  -- the subtype coercion.
  rw [centeredGaussianPositiveExponent_eq]
  rw [Filter.liminf_comp, map_positiveParameterFilter]
  exact centeredGaussianSmallVarianceExponent_Icc_lowerBound (x := x) (δ := δ) hδ

/-- Helper for Exercise 23.2.3: the symmetric-tail limsup bound transported to the
positive-parameter filter. -/
private theorem centeredGaussianPositive_symmetricTailLimsupUpperBound {r : ℝ} (hr : 0 < r) :
    Filter.limsup (scaledLogMassAlong centeredGaussianPositiveFamily id (Set.Iic (-r) ∪ Set.Ici r))
        positiveParameterFilter ≤
      -((((r ^ 2) / 2 : ℝ) : EReal)) := by
  -- Route correction: keep the analytic proof on `𝓝[>] (0 : ℝ)` and transport it once through
  -- the subtype coercion.
  rw [centeredGaussianPositiveExponent_eq]
  rw [Filter.limsup_comp, map_positiveParameterFilter]
  exact centeredGaussianSmallVarianceExponent_symmetricTail_upperBound hr

/-- Helper for Exercise 23.2.3: the centered Gaussian open-set LDP lower bound rewritten on the
positive-parameter filter. -/
private theorem centeredGaussianPositive_openLowerBound {U : Set ℝ} (hU : IsOpen U) :
    -sInf (gaussianQuadraticRateFunctionEReal '' U) ≤
      Filter.liminf (scaledLogMassAlong centeredGaussianPositiveFamily id U)
        positiveParameterFilter := by
  -- Route correction: keep the centered proof on the simpler real-parameter surface and transport
  -- it to `positiveParameterFilter` only once through the coercion map.
  rw [centeredGaussianPositiveExponent_eq]
  rw [Filter.liminf_comp, map_positiveParameterFilter]
  exact centeredGaussianSmallVariance_openLowerBound_real hU

/-- Helper for Exercise 23.2.3: the centered Gaussian closed-set LDP upper bound rewritten on the
positive-parameter filter. -/
private theorem centeredGaussianPositive_closedUpperBound {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup (scaledLogMassAlong centeredGaussianPositiveFamily id C) positiveParameterFilter ≤
      -sInf (gaussianQuadraticRateFunctionEReal '' C) := by
  -- Route correction: keep the centered proof on the simpler real-parameter surface and transport
  -- it to `positiveParameterFilter` only once through the coercion map.
  rw [centeredGaussianPositiveExponent_eq]
  rw [Filter.limsup_comp, map_positiveParameterFilter]
  exact centeredGaussianSmallVariance_closedUpperBound_real hC

/-- Helper for Exercise 23.2.3: the shifted Gaussian branch is the translated centered branch on
measurable events. -/
private theorem shiftedGaussianFamily_apply_eq_centeredPreimage (m : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) (ε : PositiveParameter) :
    shiftedGaussianFamily m ε s =
      centeredGaussianSmallVarianceLaw (ε : ℝ) (((fun x : ℝ ↦ x + m) ⁻¹' s)) := by
  -- Proof comment: rewrite `N(m, ε)` as the pushforward of `N(0, ε)` under `x ↦ x + m`, then
  -- evaluate the mapped measure on the event `s`.
  have hmap :
      (centeredGaussianSmallVarianceLaw (ε : ℝ)).map (fun x : ℝ ↦ x + m) =
        shiftedGaussianFamily m ε := by
    simpa [centeredGaussianSmallVarianceLaw, shiftedGaussianFamily] using
      (ProbabilityTheory.gaussianReal_map_add_const
        (μ := (0 : ℝ)) (v := Real.toNNReal (ε : ℝ)) (y := m))
  rw [← hmap]
  rw [Measure.map_apply (by fun_prop) hs]

/-- Helper for Exercise 23.2.3: translating the event by `x ↦ x + m` transports the centered
quadratic image to the shifted branch-rate image. -/
private theorem centeredRateImage_preimage_add_const (m : ℝ) (s : Set ℝ) :
    gaussianQuadraticRateFunctionEReal '' ((fun x : ℝ ↦ x + m) ⁻¹' s) =
      (fun x : ℝ ↦ (shiftedQuadraticRate m x : EReal)) '' s := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + m, hx, ?_⟩
    simp [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction, shiftedQuadraticRate]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - m, ?_, ?_⟩
    · simpa using hx
    · simp [gaussianQuadraticRateFunctionEReal, gaussianQuadraticRateFunction,
        shiftedQuadraticRate]

/-- Helper for Exercise 23.2.3: each shifted Gaussian branch should satisfy the open-set LDP lower
bound with its quadratic branch rate. -/
private theorem shiftedGaussian_openLowerBound (m : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate m x : EReal)) '' U) ≤
      Filter.liminf
        (scaledLogMassAlong (shiftedGaussianFamily m) id U) positiveParameterFilter := by
  -- Route correction: use the local centered Gaussian LDP layer and transport it through the
  -- translation `x ↦ x + m`.
  let V : Set ℝ := ((fun x : ℝ ↦ x + m) ⁻¹' U)
  have hV : IsOpen V := by
    simpa [V] using hU.preimage (continuous_id.add_const m)
  have hCentered :
      -sInf (gaussianQuadraticRateFunctionEReal '' V) ≤
        Filter.liminf (scaledLogMassAlong centeredGaussianPositiveFamily id V)
          positiveParameterFilter :=
    centeredGaussianPositive_openLowerBound hV
  have hMass :
      scaledLogMassAlong centeredGaussianPositiveFamily id V =
        scaledLogMassAlong (shiftedGaussianFamily m) id U := by
    funext ε
    rw [scaledLogMassAlong_def, scaledLogMassAlong_def,
      shiftedGaussianFamily_apply_eq_centeredPreimage (m := m) (s := U) hU.measurableSet ε]
    rfl
  have hRate :
      gaussianQuadraticRateFunctionEReal '' V =
        (fun x : ℝ ↦ (shiftedQuadraticRate m x : EReal)) '' U := by
    simpa [V] using centeredRateImage_preimage_add_const m U
  rw [hRate, hMass] at hCentered
  exact hCentered

/-- Helper for Exercise 23.2.3: each shifted Gaussian branch should satisfy the closed-set LDP
upper bound with its quadratic branch rate. -/
private theorem shiftedGaussian_closedUpperBound (m : ℝ) {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup (scaledLogMassAlong (shiftedGaussianFamily m) id C) positiveParameterFilter ≤
      -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate m x : EReal)) '' C) := by
  -- Route correction: keep the proof on the translation route, but use the local centered closed
  -- bound instead of the unavailable imported exercise module.
  let V : Set ℝ := ((fun x : ℝ ↦ x + m) ⁻¹' C)
  have hV : IsClosed V := by
    simpa [V] using hC.preimage (continuous_id.add_const m)
  have hCentered :
      Filter.limsup (scaledLogMassAlong centeredGaussianPositiveFamily id V)
        positiveParameterFilter ≤
      -sInf (gaussianQuadraticRateFunctionEReal '' V) :=
    centeredGaussianPositive_closedUpperBound hV
  have hMass :
      scaledLogMassAlong centeredGaussianPositiveFamily id V =
        scaledLogMassAlong (shiftedGaussianFamily m) id C := by
    funext ε
    rw [scaledLogMassAlong_def, scaledLogMassAlong_def,
      shiftedGaussianFamily_apply_eq_centeredPreimage (m := m) (s := C) hC.measurableSet ε]
    rfl
  have hRate :
      gaussianQuadraticRateFunctionEReal '' V =
        (fun x : ℝ ↦ (shiftedQuadraticRate m x : EReal)) '' C := by
    simpa [V] using centeredRateImage_preimage_add_const m C
  rw [hMass, hRate] at hCentered
  exact hCentered

/-- Helper for Exercise 23.2.3: the two-well rate is the pointwise minimum of the left and right
quadratic branch rates. -/
private theorem shiftedQuadraticRate_negOne (x : ℝ) :
    shiftedQuadraticRate (-1) x = ENNReal.ofReal (((x + 1) ^ (2 : ℕ)) / 2) := by
  -- Proof comment: unfold the centered quadratic branch and normalize `x - (-1)` to `x + 1`.
  rw [shiftedQuadraticRate]
  congr 1
  ring_nf

/-- Helper for Exercise 23.2.3: the right branch rate is the quadratic cost around the well at
`1`. -/
private theorem shiftedQuadraticRate_one (x : ℝ) :
    shiftedQuadraticRate 1 x = ENNReal.ofReal (((x - 1) ^ (2 : ℕ)) / 2) := by
  -- Proof comment: the branch centered at `1` already has the target normal form.
  rfl

/-- Helper for Exercise 23.2.3: the two-well rate is the pointwise minimum of the left and right
quadratic branch rates. -/
private theorem twoWellQuadraticRateFunction_eq_min_shiftedRates (x : ℝ) :
    twoWellQuadraticRateFunction x =
      min (shiftedQuadraticRate (-1) x) (shiftedQuadraticRate 1 x) := by
  -- Proof comment: compare the left and right quadratic wells pointwise and normalize the branch
  -- that realizes the minimum.
  let a : ℝ := (x + 1) ^ (2 : ℕ)
  let b : ℝ := (x - 1) ^ (2 : ℕ)
  rcases le_total a b with hab | hba
  · rw [twoWellQuadraticRateFunction, shiftedQuadraticRate_negOne, shiftedQuadraticRate_one,
      min_eq_left hab, min_eq_left]
    · congr 1
      dsimp [a]
      ring
    · exact ENNReal.ofReal_le_ofReal <| by
        dsimp [a, b] at hab ⊢
        nlinarith
  · rw [twoWellQuadraticRateFunction, shiftedQuadraticRate_negOne, shiftedQuadraticRate_one,
      min_eq_right hba, min_eq_right]
    · congr 1
      dsimp [b]
      ring
    · exact ENNReal.ofReal_le_ofReal <| by
        dsimp [a, b] at hba ⊢
        nlinarith

/-- Helper for Exercise 23.2.3: taking the infimum over the two-well rate on a set is the same as
taking the minimum of the two branch infima. -/
private theorem sInf_image_twoWellQuadraticRate_eq_min (s : Set ℝ) :
    sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' s) =
      min (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' s))
        (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' s)) := by
  -- Route correction: prove only the exact infimum identity actually encoded by the pointwise
  -- minimum formula, rather than searching for a stronger global normalization theorem.
  refine le_antisymm ?_ ?_
  · -- Proof comment: the infimum of the minimum is below each branch infimum separately.
    refine le_min ?_ ?_
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      have hminMem :
          min (shiftedQuadraticRate (-1) x : EReal) (shiftedQuadraticRate 1 x : EReal) ∈
            (fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' s := by
        refine ⟨x, hx, ?_⟩
        exact congrArg (fun z : ℝ≥0∞ ↦ (z : EReal))
          (twoWellQuadraticRateFunction_eq_min_shiftedRates x)
      exact (sInf_le hminMem).trans (min_le_left _ _)
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      have hminMem :
          min (shiftedQuadraticRate (-1) x : EReal) (shiftedQuadraticRate 1 x : EReal) ∈
            (fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' s := by
        refine ⟨x, hx, ?_⟩
        exact congrArg (fun z : ℝ≥0∞ ↦ (z : EReal))
          (twoWellQuadraticRateFunction_eq_min_shiftedRates x)
      exact (sInf_le hminMem).trans (min_le_right _ _)
  · -- Proof comment: each branch infimum is below the corresponding branch value at every point
    -- of `s`, so their minimum is below the two-well value there.
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    calc
      min (sInf ((fun x ↦ (shiftedQuadraticRate (-1) x : EReal)) '' s))
          (sInf ((fun x ↦ (shiftedQuadraticRate 1 x : EReal)) '' s)) ≤
          min (shiftedQuadraticRate (-1) x : EReal) (shiftedQuadraticRate 1 x : EReal) := by
            exact min_le_min
              (sInf_le ⟨x, hx, rfl⟩)
              (sInf_le ⟨x, hx, rfl⟩)
      _ = (twoWellQuadraticRateFunction x : EReal) := by
            exact (congrArg (fun z : ℝ≥0∞ ↦ (z : EReal))
              (twoWellQuadraticRateFunction_eq_min_shiftedRates x)).symm

/-- Helper for Exercise 23.2.3: averaging two nonnegative masses with equal weights never exceeds
their maximum. -/
private theorem halfAdd_halfMul_le_max (a b : ℝ≥0∞) :
    (1 / 2 : ℝ≥0∞) * a + (1 / 2 : ℝ≥0∞) * b ≤ max a b := by
  -- Proof comment: both weighted terms are bounded by the same weighted maximum, and the two
  -- weights add up to `1`.
  calc
    (1 / 2 : ℝ≥0∞) * a + (1 / 2 : ℝ≥0∞) * b ≤
        (1 / 2 : ℝ≥0∞) * max a b + (1 / 2 : ℝ≥0∞) * max a b := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
    _ = max a b := by
      have hhalf : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
        simpa [one_div] using ENNReal.inv_two_add_inv_two
      rw [← add_mul, hhalf, one_mul]

/-- Helper for Exercise 23.2.3: the fixed branch-weight correction `ε log(1 / 2)` vanishes in the
small-noise limit. -/
private theorem halfWeightCorrection_tendsto_zero :
    Tendsto halfWeightCorrection positiveParameterFilter (nhds (0 : EReal)) := by
  -- Proof comment: the deterministic correction is exactly the constant-log term from
  -- `ENNReal.tendsto_smallNoiseLogConst`, reindexed by positive parameters.
  have hbase :
      Tendsto (fun ε : ℝ ↦ (ε : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
        (𝓝[>] (0 : ℝ)) (nhds (0 : EReal)) :=
    ENNReal.tendsto_smallNoiseLogConst (b := (1 / 2 : ℝ≥0∞)) (by norm_num) (by simp)
  have hcoe : Tendsto ((↑) : PositiveParameter → ℝ) positiveParameterFilter (𝓝[>] (0 : ℝ)) := by
    rw [positiveParameterFilter]
    exact Filter.map_comap_le
  change Tendsto
    (fun ε : PositiveParameter => ((ε : ℝ) : EReal) * ENNReal.log (1 / 2 : ℝ≥0∞))
    positiveParameterFilter (nhds (0 : EReal))
  simpa using hbase.comp hcoe

/-- Helper for Exercise 23.2.3: a selected Gaussian branch contributes to the mixture up to the
vanishing logarithmic correction from its weight `1 / 2`. -/
private theorem branchExponent_add_halfWeightCorrection_le_mixture (m : ℝ)
    (hm : m = -1 ∨ m = 1) {s : Set ℝ} :
    ∀ ε : PositiveParameter,
      scaledLogMassAlong (shiftedGaussianFamily m) id s ε + halfWeightCorrection ε ≤
        scaledLogMassAlong (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id s ε := by
  intro ε
  -- Proof comment: the chosen branch contributes with weight `1 / 2` inside the mixture, so the
  -- logarithmic exponent differs only by the additive correction `ε log (1 / 2)`.
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hmass :
      (1 / 2 : ℝ≥0∞) * shiftedGaussianFamily m ε s ≤ twoPointGaussianMixtureMeasureFamily ε s := by
    rcases hm with rfl | rfl <;>
      simp [twoPointGaussianMixtureMeasureFamily, shiftedGaussianFamily, add_comm]
  calc
    scaledLogMassAlong (shiftedGaussianFamily m) id s ε + halfWeightCorrection ε
        = ((ε : ℝ) : EReal) *
            (ENNReal.log (shiftedGaussianFamily m ε s) + ENNReal.log (1 / 2 : ℝ≥0∞)) := by
              rw [scaledLogMassAlong_def, halfWeightCorrection]
              simp only [id_eq, one_div]
              rw [← EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = ((ε : ℝ) : EReal) * ENNReal.log
          ((1 / 2 : ℝ≥0∞) * shiftedGaussianFamily m ε s) := by
            rw [ENNReal.log_mul_add, add_comm]
    _ ≤ ((ε : ℝ) : EReal) * ENNReal.log (twoPointGaussianMixtureMeasureFamily ε s) := by
          exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hmass) hε
    _ = scaledLogMassAlong (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id s ε := by
          simp [scaledLogMassAlong_def]

/-- Helper for Exercise 23.2.3: the mixture exponent is pointwise bounded above by the maximum of
the two branch exponents. -/
private theorem mixtureExponent_le_maxBranches {s : Set ℝ} :
    ∀ ε : PositiveParameter,
      scaledLogMassAlong (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id s ε ≤
        max (scaledLogMassAlong (shiftedGaussianFamily (-1)) id s ε)
          (scaledLogMassAlong (shiftedGaussianFamily 1) id s ε) := by
  intro ε
  -- Proof comment: the event mass under the mixture is bounded by the maximum branch mass, and
  -- multiplication by the nonnegative parameter preserves the order and the `max`.
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hmass :
      twoPointGaussianMixtureMeasureFamily ε s ≤
        max (shiftedGaussianFamily (-1) ε s) (shiftedGaussianFamily 1 ε s) := by
    simpa [twoPointGaussianMixtureMeasureFamily, shiftedGaussianFamily] using
      (halfAdd_halfMul_le_max (gaussianReal (-1) (Real.toNNReal ε) s)
        (gaussianReal 1 (Real.toNNReal ε) s))
  have hmul : Monotone fun x : EReal ↦ ((ε : ℝ) : EReal) * x :=
    monotone_mul_left_of_nonneg hε
  calc
    scaledLogMassAlong (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id s ε
        = ((ε : ℝ) : EReal) * ENNReal.log (twoPointGaussianMixtureMeasureFamily ε s) := by
            simp [scaledLogMassAlong_def]
    _ ≤ ((ε : ℝ) : EReal) *
        max (ENNReal.log (shiftedGaussianFamily (-1) ε s))
          (ENNReal.log (shiftedGaussianFamily 1 ε s)) := by
            exact mul_le_mul_of_nonneg_left
              ((ENNReal.log_le_log hmass).trans <| le_of_eq ENNReal.log_monotone.map_max) hε
    _ = max (((ε : ℝ) : EReal) * ENNReal.log (shiftedGaussianFamily (-1) ε s))
          (((ε : ℝ) : EReal) * ENNReal.log (shiftedGaussianFamily 1 ε s)) := by
            rw [hmul.map_max]
    _ = max (scaledLogMassAlong (shiftedGaussianFamily (-1)) id s ε)
          (scaledLogMassAlong (shiftedGaussianFamily 1) id s ε) := by
            simp [scaledLogMassAlong_def]

/-- Helper for Exercise 23.2.3: the open-set LDP lower bound for the symmetric Gaussian mixture. -/
private theorem twoPointGaussianMixture_openLowerBound {U : Set ℝ} (hU : IsOpen U) :
    -sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' U) ≤
      Filter.liminf (scaledLogMassAlong
        (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter := by
  have hCorrection :
      Filter.liminf halfWeightCorrection positiveParameterFilter = 0 :=
    halfWeightCorrection_tendsto_zero.liminf_eq
  have hLeftBranch :
      -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U) ≤
        Filter.liminf (scaledLogMassAlong
          (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter := by
    -- Proof comment: add the vanishing branch-weight correction to the left-branch lower bound,
    -- then compare the corrected branch exponent with the mixture exponent.
    calc
      -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U)
          = -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U) + 0 := by
              simp
      _ = -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U) +
            Filter.liminf halfWeightCorrection positiveParameterFilter := by
              rw [hCorrection]
      _ ≤ Filter.liminf (scaledLogMassAlong (shiftedGaussianFamily (-1)) id U)
            positiveParameterFilter +
            Filter.liminf halfWeightCorrection positiveParameterFilter := by
              simpa [add_comm] using
                add_le_add_left
                  (shiftedGaussian_openLowerBound (-1) hU)
                  (Filter.liminf halfWeightCorrection positiveParameterFilter)
      _ ≤ Filter.liminf
            (fun ε : PositiveParameter ↦
              scaledLogMassAlong (shiftedGaussianFamily (-1)) id U ε +
                halfWeightCorrection ε)
            positiveParameterFilter := by
              simpa using
                (EReal.le_liminf_add
                  (u := scaledLogMassAlong (shiftedGaussianFamily (-1)) id U)
                  (v := halfWeightCorrection) (f := positiveParameterFilter))
      _ ≤ Filter.liminf (scaledLogMassAlong
            (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter := by
              exact liminf_le_liminf <|
                Eventually.of_forall fun ε ↦
                  branchExponent_add_halfWeightCorrection_le_mixture (-1) (Or.inl rfl) ε
  have hRightBranch :
      -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U) ≤
        Filter.liminf (scaledLogMassAlong
          (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter := by
    -- Proof comment: the same comparison applies to the right branch centered at `1`.
    calc
      -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U)
          = -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U) + 0 := by
              simp
      _ = -sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U) +
            Filter.liminf halfWeightCorrection positiveParameterFilter := by
              rw [hCorrection]
      _ ≤ Filter.liminf (scaledLogMassAlong (shiftedGaussianFamily 1) id U)
            positiveParameterFilter +
            Filter.liminf halfWeightCorrection positiveParameterFilter := by
              simpa [add_comm] using
                add_le_add_left
                  (shiftedGaussian_openLowerBound 1 hU)
                  (Filter.liminf halfWeightCorrection positiveParameterFilter)
      _ ≤ Filter.liminf
            (fun ε : PositiveParameter ↦
              scaledLogMassAlong (shiftedGaussianFamily 1) id U ε +
                halfWeightCorrection ε)
            positiveParameterFilter := by
              simpa using
                (EReal.le_liminf_add
                  (u := scaledLogMassAlong (shiftedGaussianFamily 1) id U)
                  (v := halfWeightCorrection) (f := positiveParameterFilter))
      _ ≤ Filter.liminf (scaledLogMassAlong
            (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter := by
              exact liminf_le_liminf <|
                Eventually.of_forall fun ε ↦
                  branchExponent_add_halfWeightCorrection_le_mixture 1 (Or.inr rfl) ε
  have hRate :
      -sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' U) =
        max (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U))
          (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U)) := by
    -- Proof comment: the exact `sInf = min` identity turns the target into the maximum of the
    -- two branch lower bounds.
    rw [sInf_image_twoWellQuadraticRate_eq_min]
    simpa using
      (EReal.max_neg_neg
        (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U))
        (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U))).symm
  calc
    -sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' U)
        = max (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' U))
            (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' U)) := hRate
    _ ≤ Filter.liminf (scaledLogMassAlong
          (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id U) positiveParameterFilter :=
      max_le hLeftBranch hRightBranch

/-- Helper for Exercise 23.2.3: the closed-set LDP upper bound for the symmetric Gaussian
mixture. -/
private theorem twoPointGaussianMixture_closedUpperBound {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup (scaledLogMassAlong
      (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id C) positiveParameterFilter ≤
      -sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' C) := by
  -- Proof comment: the mixture exponent is bounded by the pointwise maximum of the branch
  -- exponents, and `limsup` of that maximum is the maximum of the branch `limsup`s.
  calc
    Filter.limsup (scaledLogMassAlong
      (fun ε ↦ twoPointGaussianMixtureMeasureFamily ε) id C) positiveParameterFilter
        ≤ Filter.limsup
            (fun ε : PositiveParameter ↦
              max (scaledLogMassAlong (shiftedGaussianFamily (-1)) id C ε)
                (scaledLogMassAlong (shiftedGaussianFamily 1) id C ε))
            positiveParameterFilter := by
              exact limsup_le_limsup <|
                Eventually.of_forall fun ε ↦ mixtureExponent_le_maxBranches (s := C) ε
    _ = max
          (Filter.limsup (scaledLogMassAlong (shiftedGaussianFamily (-1)) id C)
            positiveParameterFilter)
          (Filter.limsup (scaledLogMassAlong (shiftedGaussianFamily 1) id C)
            positiveParameterFilter) := by
              simpa using
                (limsup_max
                  (f := positiveParameterFilter)
                  (u := scaledLogMassAlong (shiftedGaussianFamily (-1)) id C)
                  (v := scaledLogMassAlong (shiftedGaussianFamily 1) id C))
    _ ≤ max
          (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' C))
          (-sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' C)) := by
            exact max_le_max
              (shiftedGaussian_closedUpperBound (-1) hC)
              (shiftedGaussian_closedUpperBound 1 hC)
    _ = -sInf ((fun x : ℝ ↦ (twoWellQuadraticRateFunction x : EReal)) '' C) := by
          rw [sInf_image_twoWellQuadraticRate_eq_min]
          simpa using
            (EReal.max_neg_neg
              (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate (-1) x : EReal)) '' C))
              (sInf ((fun x : ℝ ↦ (shiftedQuadraticRate 1 x : EReal)) '' C)))

-- Proof sketch: on each side of the origin, the family is a small-variance Gaussian perturbation
-- of one of the two atoms `-1` and `1`, so the local Gaussian LDP gives the quadratic costs
-- `(x + 1)^2 / 2` and `(x - 1)^2 / 2`; exponential asymptotics for the symmetric mixture are then
-- governed by the larger exponential term, which yields the minimum of the two costs.
/-- Exercise 23.2.3: the family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` satisfies the large deviations principle on `ℝ` as
`ε ↓ 0`, with rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem gaussianMixture_smallVariance_satisfiesLDP :
    HasLargeDeviationsPrinciple
      (fun ε ↦
        ⟨twoPointGaussianMixtureMeasureFamily ε,
          twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure ε⟩)
      twoWellQuadraticRateFunction := by
  -- The proof is organized into the standard LDP fields: lower semicontinuity is already provided
  -- by the good-rate-function instance, and the open/closed bounds were established above.
  refine
    { lowerSemicontinuous :=
        (instIsGoodRateFunctionTwoWellQuadraticRateFunction).lowerSemicontinuous
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    -- The open bound is the branchwise lower estimate combined with the two-well minimum formula.
    simpa using twoPointGaussianMixture_openLowerBound hU
  · intro C hC
    -- The closed bound is the branchwise upper estimate combined with the same rate comparison.
    simpa using twoPointGaussianMixture_closedUpperBound hC

end ProbabilityTheory

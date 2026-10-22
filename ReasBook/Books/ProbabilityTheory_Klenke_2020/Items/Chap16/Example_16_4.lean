/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

/-- The logarithmic jump measure with masses `((1 - p)^(k + 1)) / (k + 1)` at the positive
integers `k + 1`, viewed as a measure on `ℝ`. -/
noncomputable def logarithmicJumpMeasure (p : ℝ) : Measure ℝ :=
  Measure.sum
    (fun k : ℕ ↦
      ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) •
        Measure.dirac (((k + 1 : ℕ) : ℝ)))

-- Proof sketch: in the defining weighted Dirac sum, only the atom at `k + 1` contributes to the
-- singleton `{k + 1}`.
/-- The logarithmic jump measure assigns mass `((1 - p)^(k + 1)) / (k + 1)` to the atom `k + 1`.
-/
theorem logarithmicJumpMeasure_apply_natSucc (p : ℝ) (k : ℕ) :
    logarithmicJumpMeasure p {(((k + 1 : ℕ) : ℝ))} =
      ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
  -- Proof comment: evaluate the defining weighted Dirac sum on the singleton `{k + 1}` and use
  -- that all atoms except the `k`th one vanish on this singleton.
  rw [logarithmicJumpMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single k]
  · simp [Measure.smul_apply, smul_eq_mul]
  · intro i hi
    simp [Measure.smul_apply, smul_eq_mul, hi]

-- Proof sketch: substitute `k = 0` into the defining formula and simplify the zeroth binomial
-- coefficient and the zeroth power in the canonical mass formula `negativeBinomialMass`.
/-- The atom at `0` in the canonical negative-binomial mass formula is `p^r`. -/
theorem negativeBinomialMass_zero (r p : ℝ) :
    negativeBinomialMass r p 0 = p ^ r := by
  -- Proof comment: the zeroth generalized binomial coefficient and both zeroth powers simplify to
  -- `1`, leaving only the factor `p ^ r`.
  simp [negativeBinomialMass]

-- Proof sketch: unfold the pushforward of the canonical `ℕ`-valued negative-binomial measure,
-- then expand that measure by its singleton masses.
/-- The real-valued negative-binomial law is the weighted Dirac sum with coefficients
`negativeBinomialMass r p k` at the atoms `k ∈ ℕ ⊂ ℝ`. -/
theorem negativeBinomialMeasure_map_def (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    (negativeBinomialMeasure r p hr hp hp_le_one).map (fun k : ℕ ↦ (k : ℝ)) =
      Measure.sum
        (fun k : ℕ ↦
          ENNReal.ofReal (negativeBinomialMass r p k) • Measure.dirac ((k : ℝ))) := by
  -- Proof comment: compare both measures on measurable sets, rewrite the pushforward through the
  -- PMF owner, and expand both sides into the same singleton-weighted series.
  ext s hs
  have hs_pre : MeasurableSet ((fun k : ℕ ↦ (k : ℝ)) ⁻¹' s) :=
    MeasurableEmbedding.natCast.measurable hs
  rw [Measure.map_apply (μ := negativeBinomialMeasure r p hr hp hp_le_one)
    (f := fun k : ℕ ↦ (k : ℝ)) (hf := MeasurableEmbedding.natCast.measurable) hs]
  calc
    (negativeBinomialPMF r p hr hp hp_le_one).toMeasure ((fun k : ℕ ↦ (k : ℝ)) ⁻¹' s)
        = ∑' k : ℕ,
            (((fun k : ℕ ↦ (k : ℝ)) ⁻¹' s).indicator
              (negativeBinomialPMF r p hr hp hp_le_one)) k := by
              simpa [negativeBinomialMeasure] using
                (PMF.toMeasure_apply (p := negativeBinomialPMF r p hr hp hp_le_one)
                  (s := (fun k : ℕ ↦ (k : ℝ)) ⁻¹' s) hs_pre)
    _ = ∑' k : ℕ, ENNReal.ofReal (negativeBinomialMass r p k) * s.indicator 1 (k : ℝ) := by
          refine tsum_congr fun k ↦ ?_
          by_cases hk : (k : ℝ) ∈ s
          · simp [Set.indicator, hk]
            rfl
          · simp [Set.indicator, hk]
    _ = (Measure.sum fun k : ℕ ↦
            ENNReal.ofReal (negativeBinomialMass r p k) • Measure.dirac ((k : ℝ))) s := by
          symm
          rw [Measure.sum_apply _ hs]
          refine tsum_congr fun k ↦ ?_
          simp [Measure.smul_apply, smul_eq_mul]

-- Proof sketch: for `0 < p ≤ 1`, the logarithmic series
-- `∑_{k ≥ 0} (1 - p)^(k + 1) / (k + 1)` converges to `-log p`, so the total mass of
-- `logarithmicJumpMeasure p` is finite.
theorem logarithmicJumpMeasure_isFiniteMeasure (p : ℝ) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    IsFiniteMeasure (logarithmicJumpMeasure p) := by
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have hq_lt_one : 1 - p < 1 := by linarith
  have hq_abs_lt_one : |1 - p| < 1 := by
    simpa [abs_of_nonneg hq_nonneg] using hq_lt_one
  have hseries :
      HasSum (fun k : ℕ ↦ (1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (-Real.log p) := by
    -- Proof comment: this is the textbook logarithmic-series identity evaluated at `1 - p`.
    simpa using (Real.hasSum_pow_div_log_of_abs_lt_one hq_abs_lt_one)
  refine ⟨?_⟩
  -- Proof comment: the total mass is the `ENNReal.ofReal` image of the convergent logarithmic
  -- series, hence it is finite.
  rw [logarithmicJumpMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have hmass :
      (∑' i : ℕ,
          (ENNReal.ofReal ((1 - p) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) •
            Measure.dirac (((i + 1 : ℕ) : ℝ)))
            Set.univ) =
        ∑' i : ℕ, ENNReal.ofReal ((1 - p) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) := by
    refine tsum_congr fun i ↦ ?_
    simp [Measure.smul_apply, smul_eq_mul]
  rw [hmass]
  have htsum :
      (∑' i : ℕ, ENNReal.ofReal ((1 - p) ^ (i + 1) / ((i + 1 : ℕ) : ℝ))) =
        ENNReal.ofReal (-Real.log p) := by
    calc
      (∑' i : ℕ, ENNReal.ofReal ((1 - p) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)))
          = ENNReal.ofReal (∑' i : ℕ, (1 - p) ^ (i + 1) / ((i + 1 : ℕ) : ℝ)) := by
              symm
              exact ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) hseries.summable
      _ = ENNReal.ofReal (-Real.log p) := by
            rw [hseries.tsum_eq]
  rw [htsum]
  simp

private theorem scaledLogarithmicJumpMeasure_isFiniteMeasure
    (r p : ℝ) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) := by
  letI := logarithmicJumpMeasure_isFiniteMeasure p hp hp_le_one
  infer_instance

/-- Helper for Example 16.4: integrating the Lévy exponent kernel against
`logarithmicJumpMeasure p` unfolds to the weighted atomic series of its defining Dirac sum. -/
private theorem integral_complexExpSub_one_logarithmicJump_series
    (p : ℝ) (hp_le_one : p ≤ 1) (t : ℝ) :
    ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂logarithmicJumpMeasure p =
      ∑' k : ℕ,
        ((((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          (Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I) - 1) := by
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have hcoeff_nonneg :
      ∀ k : ℕ, 0 ≤ (1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
    intro k
    positivity
  have hcoeff_ne_top :
      ∀ k : ℕ, ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) ≠ ∞ := by
    intro k
    simp
  -- Proof comment: the measure is already a sum of weighted Dirac masses, so the Bochner
  -- integral reduces termwise to the corresponding atomic values.
  rw [logarithmicJumpMeasure]
  calc
    ∫ x, (Complex.exp (t * x * Complex.I) - 1)
        ∂Measure.sum
          (fun k : ℕ ↦
            ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) •
              Measure.dirac (((k + 1 : ℕ) : ℝ))) =
      ∑' k : ℕ,
        (ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ))).toReal •
          (Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I) - 1) := by
            simpa using
              (MeasureTheory.integral_sum_dirac
                (f := fun x : ℝ ↦ Complex.exp (t * x * Complex.I) - 1)
                (x := fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ)))
                (c := fun k : ℕ ↦
                  ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)))
                hcoeff_ne_top)
    _ = ∑' k : ℕ,
        ((((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          (Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I) - 1) := by
            refine tsum_congr fun k ↦ ?_
            rw [ENNReal.toReal_ofReal (hcoeff_nonneg k)]
            simp

/-- Helper for Example 16.4: the `k`th Fourier atom of the logarithmic-jump series is the
standard logarithmic-series monomial for `((q : ℂ) * exp (tI))^(k + 1) / (k + 1)`. -/
private theorem logarithmicJumpExponentSummand_eq (q t : ℝ) (k : ℕ) :
    ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I)) =
      (((((q : ℂ) * Complex.exp (t * Complex.I)) ^ (k + 1))) / ((k + 1 : ℕ) : ℂ)) := by
  have hexp :
      Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I) =
        (Complex.exp (t * Complex.I)) ^ (k + 1) := by
    have hmul :
        (t * ((k + 1 : ℕ) : ℝ) : ℂ) * Complex.I =
          ((k + 1 : ℕ) : ℂ) * (t * Complex.I) := by
      ac_rfl
    rw [hmul, Complex.exp_nat_mul]
  -- Proof comment: rewrite the oscillatory factor as a power of `exp (tI)` and then collect the
  -- real coefficient into the same `(k + 1)`st power.
  calc
    ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I)) =
      ((((q : ℂ) ^ (k + 1)) / ((k + 1 : ℕ) : ℂ)) *
        (Complex.exp (t * Complex.I)) ^ (k + 1)) := by
          rw [hexp]
          simp [div_eq_mul_inv]
    _ = ((((q : ℂ) ^ (k + 1)) * (Complex.exp (t * Complex.I)) ^ (k + 1)) *
        (((k + 1 : ℕ) : ℂ)⁻¹)) := by
          rw [div_eq_mul_inv]
          ac_rfl
    _ = (((((q : ℂ) * Complex.exp (t * Complex.I)) ^ (k + 1))) / ((k + 1 : ℕ) : ℂ)) := by
          rw [← mul_pow, div_eq_mul_inv]

/-- Helper for Example 16.4: the complex part of the logarithmic-jump exponent is the standard
Taylor expansion of `-Complex.log (1 - ((q : ℂ) * exp (tI)))`. -/
private theorem logarithmicJumpComplexSeries_hasSum (q t : ℝ)
    (hz : ‖((q : ℂ) * Complex.exp (t * Complex.I))‖ < 1) :
    HasSum
      (fun k : ℕ ↦
        ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
          Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I)))
      (-Complex.log (1 - ((q : ℂ) * Complex.exp (t * Complex.I)))) := by
  have hshift :
      HasSum
        (fun k : ℕ ↦
          (((q : ℂ) * Complex.exp (t * Complex.I)) ^ (k + 1)) / ((k + 1 : ℕ) : ℂ))
        (-Complex.log (1 - ((q : ℂ) * Complex.exp (t * Complex.I)))) := by
    -- Proof comment: the complex logarithm series already starts with a zero `n = 0` term, so
    -- shifting the index by one preserves the sum.
    simpa using
      (hasSum_nat_add_iff' 1).2
        (Complex.hasSum_taylorSeries_neg_log
          (z := ((q : ℂ) * Complex.exp (t * Complex.I))) hz)
  -- Proof comment: the previous algebraic normalization identifies each atomic Fourier term with
  -- the shifted Taylor-series summand.
  refine hshift.congr_fun ?_
  intro k
  simpa using logarithmicJumpExponentSummand_eq q t k

/-- Helper for Example 16.4: the Lévy exponent of `logarithmicJumpMeasure p` is the difference
between the complex and real logarithmic-series sums. -/
private theorem integral_complexExpSub_one_logarithmicJump
    (p : ℝ) (hp : 0 < p) (hp_le_one : p ≤ 1) (t : ℝ) :
    ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂logarithmicJumpMeasure p =
      (Real.log p : ℂ) -
        Complex.log (1 - (((1 - p : ℝ) : ℂ) * Complex.exp (t * Complex.I))) := by
  let q : ℝ := 1 - p
  let z : ℂ := ((q : ℂ) * Complex.exp (t * Complex.I))
  have hq_nonneg : 0 ≤ q := by
    simpa [q] using sub_nonneg.mpr hp_le_one
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have hq_abs_lt_one : |q| < 1 := by
    simpa [abs_of_nonneg hq_nonneg] using hq_lt_one
  have hz_norm : ‖z‖ < 1 := by
    -- Proof comment: multiplying the real ratio `q` by `exp (tI)` preserves its norm, so the
    -- complex parameter remains in the open unit disk.
    change ‖((q : ℂ) * Complex.exp (t * Complex.I))‖ < 1
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hq_abs_lt_one
  have hcomplex :
      HasSum
        (fun k : ℕ ↦
          ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
            Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I)))
        (-Complex.log (1 - z)) := by
    simpa [q, z] using logarithmicJumpComplexSeries_hasSum q t hz_norm
  have hreal :
      HasSum (fun k : ℕ ↦ q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (-Real.log p) := by
    -- Proof comment: the remaining scalar series is exactly the real logarithmic expansion used
    -- earlier to prove finiteness of the jump measure.
    simpa [q] using (Real.hasSum_pow_div_log_of_abs_lt_one hq_abs_lt_one)
  have hrealC :
      HasSum
        (fun k : ℕ ↦ ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ)))
        ((-Real.log p : ℝ) : ℂ) := by
    exact (Complex.hasSum_ofReal).2 hreal
  have hdiffSeries :
      HasSum
        (fun k : ℕ ↦
          ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
              Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I)) -
            ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ)))
        ((Real.log p : ℂ) - Complex.log (1 - z)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcomplex.sub hrealC
  have hdiff :
      HasSum
        (fun k : ℕ ↦
          ((((q ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (t * ((k + 1 : ℕ) : ℝ) * Complex.I) - 1)))
        ((Real.log p : ℂ) - Complex.log (1 - z)) := by
    -- Proof comment: rewrite the difference of the two series termwise as the shared coefficient
    -- times `exp (it(k + 1)) - 1`.
    refine hdiffSeries.congr_fun ?_
    intro k
    rw [mul_sub, mul_one]
  -- Proof comment: combine the atomic integral expansion with the termwise difference of the two
  -- logarithmic series to identify the exponent explicitly.
  rw [integral_complexExpSub_one_logarithmicJump_series p hp_le_one t]
  simpa [q, z] using hdiff.tsum_eq

/-- Helper for Example 16.4: the compound-Poisson law driven by the logarithmic jump measure has
the negative-binomial characteristic function. -/
private theorem charFun_compoundPoisson_logarithmicJump
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) (t : ℝ) :
    letI : IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) :=
      scaledLogarithmicJumpMeasure_isFiniteMeasure r p hp hp_le_one
    charFun (compoundPoissonMeasure ((Real.toNNReal r) • logarithmicJumpMeasure p) : Measure ℝ) t =
      (p : ℂ) ^ (r : ℂ) *
        (1 - (((1 - p : ℝ) : ℂ) * Complex.exp (t * Complex.I))) ^ (-r : ℂ) := by
  let z : ℂ := (((1 - p : ℝ) : ℂ) * Complex.exp (t * Complex.I))
  have hq_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have hq_lt_one : 1 - p < 1 := by
    linarith
  have hz_norm : ‖z‖ < 1 := by
    -- Proof comment: the jump parameter is `1 - p`, and multiplying by `exp (it)` preserves the
    -- norm, so the complex ratio stays inside the open unit disk.
    change ‖(((1 - p : ℝ) : ℂ) * Complex.exp (t * Complex.I))‖ < 1
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simpa [abs_of_nonneg hq_nonneg] using hq_lt_one
  have hz_ne : 1 - z ≠ 0 := by
    -- Proof comment: `‖z‖ < 1` excludes the singular point `z = 1` needed for the `cpow`
    -- normalization.
    refine sub_ne_zero.mpr ?_
    intro hz_one
    have hnorm_one : ‖z‖ = 1 := by
      simpa [hz_one] using (norm_one : ‖(1 : ℂ)‖ = 1)
    linarith [hz_norm, hnorm_one]
  rw [charFun_compoundPoissonMeasure]
  -- Proof comment: pull the scalar rate out of the exponent integral and substitute the Lévy
  -- exponent computed for the logarithmic jump measure.
  change
    Complex.exp
      (∫ x, (Complex.exp (t * x * Complex.I) - 1)
        ∂(((Real.toNNReal r : NNReal) : ℝ≥0∞) • logarithmicJumpMeasure p)) =
      (p : ℂ) ^ (r : ℂ) * (1 - z) ^ (-r : ℂ)
  rw [integral_smul_measure]
  rw [integral_complexExpSub_one_logarithmicJump p hp hp_le_one t]
  change
    Complex.exp (((((Real.toNNReal r : NNReal) : ℝ) : ℂ) *
      ((Real.log p : ℂ) - Complex.log (1 - z)))) =
      (p : ℂ) ^ (r : ℂ) * (1 - z) ^ (-r : ℂ)
  rw [Real.toNNReal_of_nonneg hr.le]
  rw [mul_sub, sub_eq_add_neg, Complex.exp_add]
  have hpowp : (p : ℂ) ^ (r : ℂ) = Complex.exp ((r : ℂ) * (Real.log p : ℂ)) := by
    -- Proof comment: on the positive real axis, complex powers reduce to the exponential of the
    -- real logarithm.
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hp)), Complex.ofReal_log hp.le]
    ring
  have hpowz : (1 - z) ^ (-r : ℂ) = Complex.exp (-((r : ℂ) * Complex.log (1 - z))) := by
    -- Proof comment: the nonvanishing of `1 - z` lets us expand the second complex power by
    -- definition and match the exponent exactly.
    rw [Complex.cpow_def_of_ne_zero hz_ne]
    ring
  rw [hpowp, hpowz]
  simp

-- Proof sketch: compute the singleton masses of the negative-binomial law, identify the candidate
-- jump measure from the `r ↓ 0` limit, evaluate the compound-Poisson characteristic function as
-- the logarithmic series from the example, and conclude by uniqueness of finite measures from
-- their characteristic functions. The source parameterization by rate `r` and jump measure is
-- realized through the canonical owner `compoundPoissonMeasure` applied to the finite intensity
-- measure `(Real.toNNReal r) • logarithmicJumpMeasure p`.
/-- Example 16.4: for `r > 0` and `p ∈ (0,1]`, the negative-binomial law equals the
canonical compound-Poisson law whose intensity measure is
`(Real.toNNReal r) • logarithmicJumpMeasure p`, where the jump measure has mass
`((1 - p)^k) / k` at each positive integer `k`. -/
theorem negativeBinomialMeasure_map_eq_compoundPoisson_logarithmicJump
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    (negativeBinomialMeasure r p hr hp hp_le_one).map (fun k : ℕ ↦ (k : ℝ)) =
      letI : IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) :=
        scaledLogarithmicJumpMeasure_isFiniteMeasure r p hp hp_le_one
      (compoundPoissonMeasure ((Real.toNNReal r) • logarithmicJumpMeasure p) : Measure ℝ) := by
  letI : IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) :=
    scaledLogarithmicJumpMeasure_isFiniteMeasure r p hp hp_le_one
  -- Proof comment: both measures are finite, so equality follows once their characteristic
  -- functions are identified with the same negative-binomial closed form.
  refine Measure.ext_of_charFun ?_
  ext t
  -- Proof comment: reuse the earlier negative-binomial characteristic-function theorem on the
  -- left, and the local compound-Poisson normalization lemma on the right.
  rw [charFun_negativeBinomialMeasure r p hr hp hp_le_one t]
  simpa using (charFun_compoundPoisson_logarithmicJump r p hr hp hp_le_one t).symm

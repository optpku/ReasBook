/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_3_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_50
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The explicit coefficient formula attached to the Fourier-basis construction of Brownian motion
from Example 21.29: the zeroth coefficient is the constant-mode Gaussian coordinate, and the
positive-frequency coefficients are the Fourier coordinates scaled by `1 / (nπ)` after integrating
the basis functions `b₀(x) = 1` and `bₙ(x) = √2 cos(nπx)` from `0` to `t`. The public
source-facing coefficient owner for Exercise 21.5.5 is
`paleyWienerBrownianFourierCoefficients` below. -/
def brownianFourierCoefficients (ξ : ℕ → Lp ℝ 2 μ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | n + 1 => fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi))

@[simp] theorem brownianFourierCoefficients_zero (ξ : ℕ → Lp ℝ 2 μ) :
    brownianFourierCoefficients ξ 0 = ξ 0 :=
  rfl

@[simp] theorem brownianFourierCoefficients_succ (ξ : ℕ → Lp ℝ 2 μ) (n : ℕ) :
    brownianFourierCoefficients ξ (n + 1) =
      fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi)) :=
  rfl

-- Semantic recall note: no existing mathlib/project owner for these Brownian Fourier-basis
-- coefficients showed up, so the source-facing sequence stays a thin alias of the explicit formula.
/-- The source-facing coefficient sequence `(Aₙ)` from Exercise 21.5.5: the Fourier-basis
coefficients attached to the Example 21.29 Paley--Wiener construction of Brownian motion. -/
def paleyWienerBrownianFourierCoefficients (ξ : ℕ → Lp ℝ 2 μ) : ℕ → Ω → ℝ :=
  brownianFourierCoefficients ξ

/-- Helper for Exercise 21.5.5: the source-facing Example 21.29 Fourier coefficients are given by
the explicit formula `brownianFourierCoefficients ξ`. -/
@[simp] theorem paleyWienerBrownianFourierCoefficients_eq_brownianFourierCoefficients
    (ξ : ℕ → Lp ℝ 2 μ) :
    paleyWienerBrownianFourierCoefficients ξ = brownianFourierCoefficients ξ :=
  rfl

section BrownianFourierCoefficients

variable [IsProbabilityMeasure μ]
variable (ξ : ℕ → Lp ℝ 2 μ)

/-- Helper for Exercise 21.5.5: multiplying a positive-frequency coefficient by `((n + 1)π)`
recovers the underlying Gaussian coordinate. -/
lemma scaledBrownianFourierCoefficients_succ_eq
    (n : ℕ) (ω : Ω) :
    ((n + 1 : ℝ) * Real.pi) * brownianFourierCoefficients ξ (n + 1) ω = ξ (n + 1) ω := by
  -- Proof comment: unfold the positive-frequency coefficient and cancel the deterministic scale.
  rw [brownianFourierCoefficients_succ]
  field_simp [Real.pi_ne_zero]

/-- Helper for Exercise 21.5.5: each positive-frequency coefficient is a centered Gaussian whose
variance is `1 / (((n + 1) * π)^2)`. -/
lemma brownianFourierCoefficients_succ_hasLaw
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    HasLaw
      (brownianFourierCoefficients ξ (n + 1))
      (gaussianReal 0
        (1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
          by positivity⟩))
      μ := by
  -- Proof comment: transport the standard Gaussian law of `ξ (n + 1)` through division by the
  -- deterministic scale `((n + 1)π)`.
  simpa [brownianFourierCoefficients_succ] using
    (ProbabilityTheory.gaussianReal_div_const
      (hLaw (n + 1)) (((n + 1 : ℝ) * Real.pi)))

/-- Helper for Exercise 21.5.5: the centered Gaussian law with variance `v` has second moment `v`
when viewed as an `ENNReal` integral. -/
lemma gaussianReal_lintegral_sq_zero
    (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂gaussianReal 0 v = v := by
  -- Proof comment: the second moment equals variance plus the squared mean, and the centered
  -- Gaussian mean vanishes.
  have hmem : MemLp id 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal' 2 (by simp)
  have hint : Integrable (fun x : ℝ ↦ x ^ (2 : ℕ)) (gaussianReal 0 v) := by
    simpa [pow_two] using hmem.integrable_sq
  have hsecond : ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v = v := by
    have hvar :
        Var[id; gaussianReal 0 v] =
          ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v -
            (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := by
      simpa [pow_two] using (variance_eq_sub hmem)
    have hrewrite :
        ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v =
          Var[id; gaussianReal 0 v] + (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := by
      linarith
    calc
      ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v
          = Var[id; gaussianReal 0 v] + (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := hrewrite
      _ = v + (0 : ℝ) ^ (2 : ℕ) := by
            rw [variance_id_gaussianReal, integral_id_gaussianReal]
      _ = v := by simp
  -- Proof comment: rewrite the nonnegative real integral as the corresponding `lintegral`.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint]
  · simpa using congrArg ENNReal.ofReal hsecond
  · exact ae_of_all _ fun x ↦ sq_nonneg x

/-- Helper for Exercise 21.5.5: the zeroth Brownian Fourier coefficient has deterministic square
moment `1`. -/
lemma brownianFourierCoefficients_zero_sqMoment_lintegral_eq
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    ∫⁻ ω, ENNReal.ofReal ((brownianFourierCoefficients ξ 0 ω) ^ (2 : ℕ)) ∂μ =
      ENNReal.ofReal (1 : ℝ) := by
  -- Proof comment: the zeroth mode is exactly `ξ 0`, so its square moment is the standard
  -- Gaussian second moment.
  calc
    ∫⁻ ω, ENNReal.ofReal ((brownianFourierCoefficients ξ 0 ω) ^ (2 : ℕ)) ∂μ
        = ∫⁻ ω, ENNReal.ofReal ((ξ 0 ω) ^ (2 : ℕ)) ∂μ := by
            simp [brownianFourierCoefficients_zero]
    _ = ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂gaussianReal 0 1 := by
          simpa [Function.comp] using
            (hLaw 0).lintegral_comp
              ((by fun_prop : AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 : ℕ)))
                (gaussianReal 0 1)))
    _ = ENNReal.ofReal (1 : ℝ) := by
          simpa using gaussianReal_lintegral_sq_zero (1 : ℝ≥0)

/-- Helper for Exercise 21.5.5: every positive-frequency Brownian Fourier coefficient has square
moment `1 / (((n + 1) * π)^2)`. -/
lemma brownianFourierCoefficients_succ_sqMoment_lintegral_eq
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((brownianFourierCoefficients ξ (n + 1) ω) ^ (2 : ℕ)) ∂μ =
      ENNReal.ofReal (1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
  -- Proof comment: move the square moment to the transported Gaussian law, then read off the
  -- centered-Gaussian second moment from `gaussianReal_lintegral_sq_zero`.
  calc
    ∫⁻ ω, ENNReal.ofReal ((brownianFourierCoefficients ξ (n + 1) ω) ^ (2 : ℕ)) ∂μ
        = ∫⁻ x, ENNReal.ofReal (x ^ (2 : ℕ)) ∂
            gaussianReal 0
              (1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
                by positivity⟩) := by
            simpa [Function.comp] using
              (brownianFourierCoefficients_succ_hasLaw ξ hLaw n).lintegral_comp
                ((by
                  fun_prop :
                    AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (x ^ (2 : ℕ)))
                      (gaussianReal 0
                        (1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
                          by positivity⟩))))
    _ = ((1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
          by positivity⟩ : ℝ≥0) : ℝ≥0∞) := by
          simpa using
            gaussianReal_lintegral_sq_zero
              (1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
                by positivity⟩)
    _ = ENNReal.ofReal
          (((1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)),
            by positivity⟩ : ℝ≥0) : ℝ)) := by
          rw [ENNReal.coe_nnreal_eq]
    _ = ENNReal.ofReal (1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
          simp

/-- Helper for Exercise 21.5.5: each positive-frequency coefficient is measurable. -/
lemma brownianFourierCoefficients_succ_measurable
    (n : ℕ) :
    Measurable (brownianFourierCoefficients ξ (n + 1)) := by
  -- Proof comment: the coefficient is the measurable Gaussian coordinate divided by a fixed
  -- deterministic constant.
  simpa [brownianFourierCoefficients_succ] using
    (Lp.stronglyMeasurable (ξ (n + 1))).measurable.div_const
      (((n + 1 : ℝ) * Real.pi))

/-- Helper for Exercise 21.5.5: the shifted positive-frequency coefficient sequence inherits
independence from the Gaussian coordinates. -/
lemma brownianFourierCoefficients_succ_iIndepFun
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ) :
    iIndepFun (fun n ↦ brownianFourierCoefficients ξ (n + 1)) μ := by
  have hshift : iIndepFun (fun n ↦ (ξ (n + 1) : Ω → ℝ)) μ :=
    hξ_indep.precomp Nat.succ_injective
  -- Proof comment: applying the deterministic scaling map coordinatewise preserves independence.
  simpa [brownianFourierCoefficients_succ] using
    hshift.comp
      (fun n ↦ fun x : ℝ ↦ x / (((n + 1 : ℝ) * Real.pi)))
      (fun n ↦ measurable_id.div_const (((n + 1 : ℝ) * Real.pi)))

/-- Helper for Exercise 21.5.5: the reciprocals of the positive-mode deterministic square moments
form a summable tail. -/
lemma brownianFourierCoefficients_positiveTailSqSummable :
    Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
  have hnat : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).congr ?_
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [abs_of_nonneg hn]
  have hpi :
      Summable (fun n : ℕ ↦ (Real.pi)⁻¹ ^ (2 : ℕ) * (1 / ((n + 1 : ℝ) ^ (2 : ℕ)))) :=
    hnat.mul_left ((Real.pi)⁻¹ ^ (2 : ℕ))
  refine hpi.congr ?_
  intro n
  field_simp [Real.pi_ne_zero]

/-- Helper for Exercise 21.5.5: the shifted harmonic series stays non-summable. -/
lemma not_summable_one_div_nat_succ :
    ¬ Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
  intro hsum
  have hsum' : Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ (1 : ℝ)) := by
    refine hsum.congr ?_
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [abs_of_nonneg hn]
  have : (1 : ℝ) < 1 := (Real.summable_one_div_nat_add_rpow 1 1).1 hsum'
  norm_num at this

/-- Helper for Exercise 21.5.5: the centered Gaussian second moment in ordinary-integral form
equals the variance parameter. -/
lemma gaussianReal_integral_sq_zero
    (v : ℝ≥0) :
    ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v = v := by
  have hmem : MemLp id 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal' 2 (by simp)
  have hvar :
      Var[id; gaussianReal 0 v] =
        ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v -
          (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := by
    simpa [pow_two] using (variance_eq_sub hmem)
  have hrewrite :
      ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v =
        Var[id; gaussianReal 0 v] + (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := by
    linarith
  -- Proof comment: for a centered Gaussian, the mean vanishes and the variance is exactly `v`.
  calc
    ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v
        = Var[id; gaussianReal 0 v] + (∫ x, x ∂gaussianReal 0 v) ^ (2 : ℕ) := hrewrite
    _ = v + (0 : ℝ) ^ (2 : ℕ) := by rw [variance_id_gaussianReal, integral_id_gaussianReal]
    _ = v := by simp

/-- Helper for Exercise 21.5.5: the square of each positive-frequency coefficient is integrable. -/
lemma brownianFourierCoefficients_succ_sqIntegrable
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    Integrable (fun ω ↦ (brownianFourierCoefficients ξ (n + 1) ω) ^ (2 : ℕ)) μ := by
  let v : ℝ≥0 :=
    1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)), by positivity⟩
  have hgauss_sq : Integrable (fun x : ℝ ↦ x ^ (2 : ℕ)) (gaussianReal 0 v) := by
    have hmem : MemLp id 2 (gaussianReal 0 v) :=
      memLp_id_gaussianReal' 2 (by simp)
    simpa [pow_two] using hmem.integrable_sq
  -- Proof comment: transfer the Gaussian square integrability through the coefficient law.
  exact
    (brownianFourierCoefficients_succ_hasLaw ξ hLaw n).measurePreserving
      (brownianFourierCoefficients_succ_measurable ξ n)
      |>.integrable_comp_of_integrable hgauss_sq

/-- Helper for Exercise 21.5.5: the ordinary square expectation of each positive-frequency
coefficient is `1 / (((n + 1) * π)^2)`. -/
lemma brownianFourierCoefficients_succ_sqIntegral_eq
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    μ[fun ω ↦ (brownianFourierCoefficients ξ (n + 1) ω) ^ (2 : ℕ)] =
      1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
  let v : ℝ≥0 :=
    1 / ⟨(((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)), by positivity⟩
  -- Proof comment: move the square integral to the transported Gaussian law and read off the
  -- centered-Gaussian second moment.
  calc
    μ[fun ω ↦ (brownianFourierCoefficients ξ (n + 1) ω) ^ (2 : ℕ)]
        = ∫ x, x ^ (2 : ℕ) ∂gaussianReal 0 v := by
            simpa [v, Function.comp_def] using
              (brownianFourierCoefficients_succ_hasLaw ξ hLaw n).integral_comp
                ((by
                  fun_prop :
                    AEStronglyMeasurable (fun x : ℝ ↦ x ^ (2 : ℕ)) (gaussianReal 0 v)))
    _ = v := gaussianReal_integral_sq_zero v
    _ = 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
          simp [v]

/-- Helper for Exercise 21.5.5: the large-jump probability of each positive-frequency coefficient
is bounded by its second moment. -/
lemma brownianFourierCoefficients_succ_largeJumpProb_le
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    μ.real {ω | 1 < |brownianFourierCoefficients ξ (n + 1) ω|} ≤
      1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
  let X : Ω → ℝ := brownianFourierCoefficients ξ (n + 1)
  have hX_sq_int : Integrable (fun ω ↦ X ω ^ (2 : ℕ)) μ := by
    simpa [X] using brownianFourierCoefficients_succ_sqIntegrable ξ hLaw n
  have hmarkov :
      μ.real {ω | (1 : ℝ) ≤ X ω ^ (2 : ℕ)} ≤ μ[fun ω ↦ X ω ^ (2 : ℕ)] := by
    simpa [one_mul] using
      (MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (μ := μ) (f := fun ω ↦ X ω ^ (2 : ℕ))
        (ae_of_all _ fun ω ↦ sq_nonneg (X ω)) hX_sq_int 1)
  have hsubset :
      {ω | 1 < |X ω|} ⊆ {ω | (1 : ℝ) ≤ X ω ^ (2 : ℕ)} := by
    intro ω hω
    have hω' : 1 < |X ω| := by simpa using hω
    have habs_sq : 1 ≤ |X ω| ^ (2 : ℕ) := by
      nlinarith [le_of_lt hω']
    simpa [pow_two, sq_abs] using habs_sq
  -- Proof comment: Chebyshev's first inequality turns the square moment into a tail bound.
  calc
    μ.real {ω | 1 < |brownianFourierCoefficients ξ (n + 1) ω|} = μ.real {ω | 1 < |X ω|} := by
      rfl
    _ ≤ μ.real {ω | (1 : ℝ) ≤ X ω ^ (2 : ℕ)} := measureReal_mono hsubset
    _ ≤ μ[fun ω ↦ X ω ^ (2 : ℕ)] := hmarkov
    _ = 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
          simpa [X] using brownianFourierCoefficients_succ_sqIntegral_eq ξ hLaw n

/-- Helper for Exercise 21.5.5: the truncated variance of each positive-frequency coefficient is
bounded by the same deterministic second moment. -/
lemma brownianFourierCoefficients_succ_truncatedVariance_le
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    Var[Set.indicator
          {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
          (brownianFourierCoefficients ξ (n + 1)); μ] ≤
      1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
  let X : Ω → ℝ := brownianFourierCoefficients ξ (n + 1)
  let Y : Ω → ℝ := Set.indicator {ω | |X ω| ≤ 1} X
  have hX_sq_int : Integrable (fun ω ↦ X ω ^ (2 : ℕ)) μ := by
    simpa [X] using brownianFourierCoefficients_succ_sqIntegrable ξ hLaw n
  have hY_meas : Measurable Y := by
    have hset : MeasurableSet {ω | |X ω| ≤ 1} :=
      measurableSet_le (brownianFourierCoefficients_succ_measurable ξ n).abs measurable_const
    exact (brownianFourierCoefficients_succ_measurable ξ n).indicator hset
  have hY_aesm : AEStronglyMeasurable Y μ := hY_meas.aestronglyMeasurable
  have hY_sq_le : ∀ ω, Y ω ^ (2 : ℕ) ≤ X ω ^ (2 : ℕ) := by
    intro ω
    by_cases hω : |X ω| ≤ 1
    · simp [Y, hω]
    · simp [Y, hω, sq_nonneg]
  have hY_sq_int : Integrable (fun ω ↦ Y ω ^ (2 : ℕ)) μ := by
    refine Integrable.mono' hX_sq_int ((hY_meas.pow_const (2 : ℕ)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hY_sq_nonneg : 0 ≤ Y ω ^ (2 : ℕ) := by positivity
    simpa [Real.norm_of_nonneg hY_sq_nonneg, Real.norm_of_nonneg (sq_nonneg (X ω))] using
      hY_sq_le ω
  have hvar_le : Var[Y; μ] ≤ μ[fun ω ↦ Y ω ^ (2 : ℕ)] :=
    ProbabilityTheory.variance_le_expectation_sq hY_aesm
  have hsq_le : μ[fun ω ↦ Y ω ^ (2 : ℕ)] ≤ μ[fun ω ↦ X ω ^ (2 : ℕ)] :=
    integral_mono_ae hY_sq_int hX_sq_int <| Filter.Eventually.of_forall hY_sq_le
  -- Proof comment: the truncated variable is pointwise dominated by the original coefficient, so
  -- its variance is bounded by the deterministic square moment.
  calc
    Var[Set.indicator {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
          (brownianFourierCoefficients ξ (n + 1)); μ]
        = Var[Y; μ] := by rfl
    _ ≤ μ[fun ω ↦ Y ω ^ (2 : ℕ)] := hvar_le
    _ ≤ μ[fun ω ↦ X ω ^ (2 : ℕ)] := hsq_le
    _ = 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ)) := by
          simpa [X] using brownianFourierCoefficients_succ_sqIntegral_eq ξ hLaw n

/-- Helper for Exercise 21.5.5: the deterministic square-moment sequence of the Brownian Fourier
coefficients is summable. -/
lemma brownianFourierCoefficients_sqMomentSeries_summable :
    Summable
      (fun n : ℕ ↦
        match n with
        | 0 => (1 : ℝ)
        | n + 1 => 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
  -- Proof comment: split off the zeroth coefficient and factor the positive tail by `π⁻²`.
  rw [← summable_nat_add_iff 1]
  have hnat :
      Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℝ) ^ (2 : ℕ))) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).congr ?_
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [abs_of_nonneg hn]
  have hpi :
      Summable (fun n : ℕ ↦ (Real.pi)⁻¹ ^ (2 : ℕ) * (1 / ((n + 1 : ℝ) ^ (2 : ℕ)))) :=
    hnat.mul_left ((Real.pi)⁻¹ ^ (2 : ℕ))
  refine hpi.congr ?_
  intro n
  field_simp [Real.pi_ne_zero]

/-- Helper for Exercise 21.5.5: the deterministic second moments of the Brownian Fourier
coefficients are `1` at index `0` and `1 / (((n + 1) * π)^2)` on the positive-frequency tail. -/
lemma brownianFourierCoefficients_sqMoment_lintegral_eq
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((brownianFourierCoefficients ξ n ω) ^ (2 : ℕ)) ∂μ =
      ENNReal.ofReal
        (match n with
        | 0 => (1 : ℝ)
        | n + 1 => 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
  -- Proof comment: reduce to the isolated zero-mode and positive-tail formulas.
  cases n with
  | zero =>
      simpa using brownianFourierCoefficients_zero_sqMoment_lintegral_eq ξ hLaw
  | succ n =>
      simpa using brownianFourierCoefficients_succ_sqMoment_lintegral_eq ξ hLaw n

/-- Helper for Exercise 21.5.5: a nonnegative real series is summable exactly when its partial
sums admit a uniform natural-number bound. -/
lemma summable_iff_exists_nat_partialSum_bound_of_nonneg
    (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n) :
    Summable f ↔ ∃ M : ℕ, ∀ n : ℕ, ∑ i ∈ Finset.range n, f i ≤ M := by
  constructor
  · intro hf
    -- Proof comment: summability bounds every finite partial sum by the total sum, so rounding
    -- that deterministic bound up to a natural number gives the source-facing formulation.
    refine ⟨Nat.ceil (∑' n, f n), fun n ↦ ?_⟩
    refine le_trans (hf.sum_le_tsum (Finset.range n) fun i _hi ↦ hf_nonneg i) ?_
    exact_mod_cast Nat.le_ceil (∑' n, f n)
  · rintro ⟨M, hM⟩
    -- Proof comment: bounded nonnegative partial sums are the canonical real-series criterion for
    -- summability.
    exact summable_of_sum_range_le hf_nonneg hM

/-- Helper for Exercise 21.5.5: a nonnegative real series is summable exactly when every tail has
uniformly bounded finite partial sums. -/
lemma summable_iff_forall_nat_tail_bounded_partialSums_of_nonneg
    (f : ℕ → ℝ) (hf_nonneg : ∀ n, 0 ≤ f n) :
    Summable f ↔
      ∀ N : ℕ, ∃ M : ℕ, ∀ m : ℕ, ∑ i ∈ Finset.range m, f (i + N) ≤ M := by
  constructor
  · intro hf N
    -- Proof comment: each tail is summable by the standard shift lemma, so the bounded-partial
    -- sum criterion applies to the shifted sequence.
    have htail : Summable (fun n : ℕ ↦ f (n + N)) := (_root_.summable_nat_add_iff N).2 hf
    exact
      (summable_iff_exists_nat_partialSum_bound_of_nonneg
        (fun n ↦ f (n + N)) fun n ↦ hf_nonneg (n + N)).1 htail
  · intro htail
    -- Proof comment: the original series is the zero-th tail.
    simpa using
      (summable_iff_exists_nat_partialSum_bound_of_nonneg f hf_nonneg).2 (htail 0)

/-- Helper for Exercise 21.5.5: each finite partial sum of a tail process is measurable in the
corresponding tail `σ`-algebra. -/
lemma tailPartialSum_measurableFromTail
    (X : ℕ → Ω → ℝ) (N m : ℕ) :
    Measurable[⨆ i : ℕ, ⨆ _ : i ∈ Set.Ici N, MeasurableSpace.comap (X i) (borel ℝ)]
      (fun ω ↦ ∑ j ∈ Finset.range m, X (j + N) ω) := by
  let tailSpace : MeasurableSpace Ω :=
    ⨆ i : ℕ, ⨆ _ : i ∈ Set.Ici N, MeasurableSpace.comap (X i) (borel ℝ)
  -- Proof comment: every summand only depends on one tail coordinate, so the finite sum remains
  -- measurable in the same tail stage.
  have hcoord : ∀ j ∈ Finset.range m, Measurable[tailSpace] (fun ω ↦ X (j + N) ω) := by
    intro j hj
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le (j + N) <| le_iSup_of_le (by simp [Set.mem_Ici]) le_rfl
  simpa [tailSpace] using Finset.measurable_sum (Finset.range m) hcoord

/-- Helper for Exercise 21.5.5: each finite partial sum of a shifted process is measurable in the
shifted tail `σ`-algebra indexed by the new origin. -/
lemma tailPartialSum_measurableFromShiftedTail
    (X : ℕ → Ω → ℝ) (N m : ℕ) :
    Measurable[⨆ i : ℕ, MeasurableSpace.comap (X (i + N)) (borel ℝ)]
      (fun ω ↦ ∑ j ∈ Finset.range m, X (j + N) ω) := by
  let tailSpace : MeasurableSpace Ω := ⨆ i : ℕ, MeasurableSpace.comap (X (i + N)) (borel ℝ)
  -- Proof comment: after fixing the shift `N`, each summand is one of the generating tail
  -- coordinates for the shifted filtration.
  have hcoord : ∀ j ∈ Finset.range m, Measurable[tailSpace] (fun ω ↦ X (j + N) ω) := by
    intro j hj
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le j le_rfl
  simpa [tailSpace] using Finset.measurable_sum (Finset.range m) hcoord

/-- Helper for Exercise 21.5.5: for a nonnegative real process, the pointwise summability event is
measurable in the tail `σ`-algebra generated by the coordinates. -/
lemma measurableSet_tail_summable_of_nonneg
    (X : ℕ → Ω → ℝ) (hX_meas : ∀ n, Measurable (X n)) (hX_nonneg : ∀ n ω, 0 ≤ X n ω) :
    MeasurableSet[limsup (fun n ↦ MeasurableSpace.comap (X n) (borel ℝ)) atTop]
      {ω | Summable (fun n ↦ X n ω)} := by
  -- Route correction: rather than keeping the witness bound dependent on all tails at once, fix a
  -- single tail stage `N` after rewriting `limsup`; then the summability event is just the
  -- summability event of the shifted process `n ↦ X (n + N)`.
  rw [Filter.limsup_eq_iInf_iSup_of_nat', MeasurableSpace.measurableSet_iInf]
  intro N
  let tailSpace : MeasurableSpace Ω := ⨆ i : ℕ, MeasurableSpace.comap (X (i + N)) (borel ℝ)
  change MeasurableSet[tailSpace] {ω | Summable (fun n ↦ X n ω)}
  have hshift :
      {ω | Summable (fun n ↦ X n ω)} = {ω | Summable (fun n ↦ X (n + N) ω)} := by
    ext ω
    constructor
    · intro hω
      exact (_root_.summable_nat_add_iff N).2 hω
    · intro hω
      exact (_root_.summable_nat_add_iff N).1 hω
  rw [hshift]
  have hbound :
      {ω | Summable (fun n ↦ X (n + N) ω)} =
        ⋃ M : ℕ, {ω | ∀ m : ℕ, ∑ j ∈ Finset.range m, X (j + N) ω ≤ M} := by
    ext ω
    constructor
    · intro hω
      rcases
        (summable_iff_exists_nat_partialSum_bound_of_nonneg
          (fun n ↦ X (n + N) ω) (fun n ↦ hX_nonneg (n + N) ω)).1 hω with
        ⟨M, hM⟩
      exact Set.mem_iUnion.2 ⟨M, hM⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨M, hM⟩
      exact
        (summable_iff_exists_nat_partialSum_bound_of_nonneg
          (fun n ↦ X (n + N) ω) (fun n ↦ hX_nonneg (n + N) ω)).2 ⟨M, hM⟩
  rw [hbound]
  refine MeasurableSet.iUnion fun M ↦ ?_
  have hforall_eq :
      {ω | ∀ m : ℕ, ∑ j ∈ Finset.range m, X (j + N) ω ≤ M} =
        ⋂ m : ℕ, {ω | ∑ j ∈ Finset.range m, X (j + N) ω ≤ M} := by
    ext ω
    simp
  rw [hforall_eq]
  refine MeasurableSet.iInter fun m : ℕ ↦ ?_
  -- Proof comment: each bounded partial-sum constraint is measurable in the fixed tail stage.
  exact measurableSet_le (tailPartialSum_measurableFromShiftedTail X N m) measurable_const

/-- Helper for Exercise 21.5.5: every centered Gaussian odd truncation has mean zero. -/
lemma standardGaussian_truncatedScaledMeanZero (a : ℝ) :
    ∫ x, Set.indicator {x : ℝ | |x / a| ≤ 1} (fun x ↦ x / a) x ∂gaussianReal 0 1 = 0 := by
  let ν : Measure ℝ := gaussianReal (0 : ℝ) 1
  let g : ℝ → ℝ := Set.indicator {x : ℝ | |x / a| ≤ 1} (fun x ↦ x / a)
  have hmap : ν.map (fun x : ℝ ↦ -x) = ν := by
    simpa [ν] using gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal))
  have hset : MeasurableSet {x : ℝ | |x / a| ≤ 1} := by
    exact (measurable_abs.comp (measurable_id.div_const a)) measurableSet_Iic
  have hg_meas : Measurable g := by
    simpa [g] using (measurable_id.div_const a).indicator hset
  have hsymm :
      ∫ x, g (-x) ∂ν = ∫ x, g x ∂ν := by
    -- Proof comment: the centered Gaussian law is invariant under `x ↦ -x`.
    simpa [g, Function.comp_def] using
      (HasLaw.integral_comp
        (X := fun x : ℝ ↦ -x) (μ := ν) (P := ν) (f := g)
        ⟨by fun_prop, hmap⟩ hg_meas.aestronglyMeasurable)
  have hodd : ∀ x : ℝ, g (-x) = -g x := by
    intro x
    by_cases hx : |x / a| ≤ 1
    · have hnegx : |(-x) / a| ≤ 1 := by simpa [abs_neg, neg_div] using hx
      simp [g, hx, hnegx, neg_div]
    · have hnegx : ¬ |(-x) / a| ≤ 1 := by simpa [abs_neg, neg_div] using hx
      simp [g, hx, hnegx]
  have hself : ∫ x, g x ∂ν = -∫ x, g x ∂ν := by
    calc
      ∫ x, g x ∂ν = ∫ x, g (-x) ∂ν := hsymm.symm
      _ = ∫ x, -g x ∂ν := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall hodd
      _ = -∫ x, g x ∂ν := by rw [integral_neg]
  linarith

/-- Helper for Exercise 21.5.5: the truncated centered coefficient at level `1` has expectation
zero. -/
lemma brownianFourierCoefficients_succ_truncatedMeanZero
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    μ[Set.indicator
        {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
        (brownianFourierCoefficients ξ (n + 1))] = 0 := by
  let a : ℝ := ((n + 1 : ℝ) * Real.pi)
  let g : ℝ → ℝ := Set.indicator {x : ℝ | |x / a| ≤ 1} (fun x ↦ x / a)
  have hg_meas : Measurable g := by
    have hset : MeasurableSet {x : ℝ | |x / a| ≤ 1} := by
      exact (measurable_abs.comp (measurable_id.div_const a)) measurableSet_Iic
    simpa [g] using (measurable_id.div_const a).indicator hset
  -- Proof comment: rewrite the truncated coefficient expectation as a standard Gaussian integral
  -- for `ξ (n + 1)`, then use the odd symmetry of the truncation.
  calc
    μ[Set.indicator
        {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
        (brownianFourierCoefficients ξ (n + 1))]
        = ∫ x, g x ∂gaussianReal 0 1 := by
            simpa [a, g, brownianFourierCoefficients_succ, Function.comp_def] using
              (hLaw (n + 1)).integral_comp hg_meas.aestronglyMeasurable
    _ = 0 := standardGaussian_truncatedScaledMeanZero a

/-- Helper for Exercise 21.5.5: the standard Gaussian assigns positive mass to `(1 / 2, 1)`. -/
lemma gaussianReal_Ioo_half_one_pos :
    0 < gaussianReal 0 1 (Set.Ioo (1 / 2) 1) := by
  have hne : gaussianReal 0 1 (Set.Ioo (1 / 2) 1) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo (1 / 2) 1) = 0 :=
      gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero
    have hvol_pos : 0 < (volume : Measure ℝ) (Set.Ioo (1 / 2) 1) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      norm_num
    exact hvol_pos.ne' hvol_zero
  exact lt_of_le_of_ne bot_le hne.symm

/-- Helper for Exercise 21.5.5: the standard Gaussian truncated absolute first moment is strictly
positive. -/
lemma standardGaussian_truncatedAbsMeanPos :
    0 <
      ∫ x, Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|) x ∂gaussianReal 0 1 := by
  let ν : Measure ℝ := gaussianReal 0 1
  let f : ℝ → ℝ := Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|)
  have hf_meas : Measurable f := by
    have hset : MeasurableSet {x : ℝ | |x| ≤ 1} := measurable_abs measurableSet_Iic
    simpa [f] using measurable_abs.indicator hset
  have hf_nonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    by_cases hx : |x| ≤ 1
    · simp [f, hx, abs_nonneg]
    · simp [f, hx]
  have hf_int : Integrable f ν := by
    -- Proof comment: the truncation is bounded by the integrable constant function `1`.
    refine Integrable.mono' (g := fun _ : ℝ ↦ (1 : ℝ)) (integrable_const 1)
      hf_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : |x| ≤ 1
    · simpa [Real.norm_eq_abs, f, hx] using hx
    · simp [f, hx]
  have hset_lower :
      (1 / 2 : ℝ) * ν.real (Set.Ioo (1 / 2) 1) ≤ ∫ x in Set.Ioo (1 / 2) 1, f x ∂ν := by
    -- Proof comment: on `(1 / 2, 1)` the truncation equals `|x|`, which is bounded below by
    -- `1 / 2`.
    refine setIntegral_ge_of_const_le_real measurableSet_Ioo (measure_ne_top _ _) ?_
      hf_int.integrableOn
    intro x hx
    have hx_nonneg : 0 ≤ x := le_of_lt (lt_trans (by norm_num) hx.1)
    have hx_mem : |x| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      exact hx.2.le
    have hx_lower : (1 / 2 : ℝ) ≤ |x| := by
      rw [abs_of_nonneg hx_nonneg]
      exact hx.1.le
    simpa [f, hx_mem] using hx_lower
  have hrestrict_le : ∫ x in Set.Ioo (1 / 2) 1, f x ∂ν ≤ ∫ x, f x ∂ν := by
    -- Proof comment: restricting the measure to a subset can only decrease the integral of a
    -- nonnegative integrable function.
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ hf_nonneg) hf_int
  have hmass_real_pos : 0 < ν.real (Set.Ioo (1 / 2) 1) := by
    exact ENNReal.toReal_pos gaussianReal_Ioo_half_one_pos.ne' (measure_ne_top _ _)
  have hconst_pos : 0 < (1 / 2 : ℝ) * ν.real (Set.Ioo (1 / 2) 1) := by
    have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
    exact mul_pos hhalf hmass_real_pos
  exact lt_of_lt_of_le hconst_pos (hset_lower.trans hrestrict_le)

/-- Helper for Exercise 21.5.5: the truncated absolute expectation of the `(n + 1)`st coefficient
dominates the fixed positive standard-Gaussian constant divided by `((n + 1)π)`. -/
lemma brownianFourierCoefficients_succ_truncatedAbsExpectation_ge
    (hLaw : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (n : ℕ) :
    (∫ x, Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|) x ∂gaussianReal 0 1) /
        (((n + 1 : ℝ) * Real.pi)) ≤
      μ[Set.indicator
          {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
          (fun ω ↦ |brownianFourierCoefficients ξ (n + 1) ω|)] := by
  let a : ℝ := ((n + 1 : ℝ) * Real.pi)
  let base : ℝ → ℝ := Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|)
  let g : ℝ → ℝ := Set.indicator {x : ℝ | |x / a| ≤ 1} (fun x ↦ |x / a|)
  let h : ℝ → ℝ := fun x ↦ base x / a
  have ha_pos : 0 < a := by
    -- Proof comment: the Fourier scaling constant is positive on the positive-frequency tail.
    dsimp [a]
    positivity
  have ha_one : 1 ≤ a := by
    -- Proof comment: `a = (n + 1)π` dominates `1` because `π > 1`.
    dsimp [a]
    nlinarith [Real.pi_gt_three]
  have hbase_meas : Measurable base := by
    have hset : MeasurableSet {x : ℝ | |x| ≤ 1} := measurable_abs measurableSet_Iic
    simpa [base] using measurable_abs.indicator hset
  have hg_meas : Measurable g := by
    have hset : MeasurableSet {x : ℝ | |x / a| ≤ 1} := by
      exact (measurable_abs.comp (measurable_id.div_const a)) measurableSet_Iic
    simpa [g] using (measurable_abs.comp (measurable_id.div_const a)).indicator hset
  have hh_meas : Measurable h := by
    simpa [h] using hbase_meas.div_const a
  have habs_int : Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 1) := by
    -- Proof comment: the standard Gaussian has finite first absolute moment because it is
    -- square-integrable on a probability space.
    have hid_int : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) := by
      exact
        (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2 (by simp)).integrable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa [Real.norm_eq_abs] using
      (integrable_norm_iff (show AEStronglyMeasurable (fun x : ℝ ↦ x) (gaussianReal 0 1) by
        fun_prop)).2 hid_int
  have hg_int : Integrable g (gaussianReal 0 1) := by
    -- Proof comment: the scaled truncation is pointwise dominated by `|x|`.
    refine Integrable.mono' habs_int hg_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : |x / a| ≤ 1
    · simp [Real.norm_eq_abs, g, hx]
      rw [abs_div, abs_of_pos ha_pos]
      exact div_le_self (abs_nonneg x) ha_one
    · simp [g, hx]
  have hh_int : Integrable h (gaussianReal 0 1) := by
    -- Proof comment: the comparison function is again bounded by `|x|`.
    refine Integrable.mono' habs_int hh_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : |x| ≤ 1
    · simpa [Real.norm_eq_abs, h, base, hx, abs_of_pos ha_pos] using
        (div_le_self (abs_nonneg x) ha_one)
    · simp [h, base, hx]
  have hcompare : ∀ x : ℝ, h x ≤ g x := by
    intro x
    by_cases hx : |x| ≤ 1
    · have hx_scaled : |x / a| ≤ 1 := by
        rw [abs_div, abs_of_pos ha_pos]
        exact (div_le_iff₀ ha_pos).2 (by simpa using (le_trans hx ha_one))
      have hhx : h x = |x| / a := by
        simp [h, base, hx]
      have hgx : g x = |x / a| := by
        simp [g, hx_scaled]
      have hgx' : g x = |x| / a := by
        rw [hgx, abs_div]
        simpa [abs_of_pos ha_pos]
      rw [hhx, hgx']
    · by_cases hx_scaled : |x / a| ≤ 1
      · simp [h, g, base, hx, hx_scaled]
      · simp [h, g, base, hx, hx_scaled]
  -- Proof comment: first identify the coefficient expectation with a Gaussian integral, then
  -- compare it to the fixed truncated absolute moment divided by the deterministic scale `a`.
  calc
    (∫ x, Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|) x ∂gaussianReal 0 1) / a
        = ∫ x, h x ∂gaussianReal 0 1 := by
            simpa [h, base] using (integral_div a base).symm
    _ ≤ ∫ x, g x ∂gaussianReal 0 1 := by
          exact integral_mono_ae hh_int hg_int (Filter.Eventually.of_forall hcompare)
    _ = μ[Set.indicator
            {ω | |brownianFourierCoefficients ξ (n + 1) ω| ≤ 1}
            (fun ω ↦ |brownianFourierCoefficients ξ (n + 1) ω|)] := by
          symm
          simpa [a, g, brownianFourierCoefficients_succ, Function.comp_def] using
            (hLaw (n + 1)).integral_comp hg_meas.aestronglyMeasurable

-- Proof sketch: the source-facing Example 21.29 coefficients are given by the explicit helper
-- sequence `brownianFourierCoefficients ξ`. Its zeroth term is the zeroth Gaussian coordinate, and
-- for `n ≥ 1` the coefficient is `ξₙ / (nπ)`. Hence the second moments are `1` at `n = 0` and
-- `1 / (π² n²)` for positive modes, which is summable. Tonelli or monotone convergence gives
-- integrability of `∑ (Aₙ)²`, forcing almost-sure square summability.
/-- Part (1) of Exercise 21.5.5: the Fourier-basis coefficients in the Example 21.29
construction of Brownian motion are almost surely square-summable. -/
theorem brownianFourierCoefficients_sqSummable_ae
    (hξ_gaussian : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      Summable
        (fun n ↦ (paleyWienerBrownianFourierCoefficients ξ n ω) ^ (2 : ℕ)) := by
  let A := paleyWienerBrownianFourierCoefficients ξ
  have hMeas :
      ∀ n, AEMeasurable (fun ω ↦ ENNReal.ofReal ((A n ω) ^ (2 : ℕ))) μ := by
    intro n
    -- Proof comment: each coefficient is measurable, and squaring plus `ENNReal.ofReal`
    -- preserves almost-everywhere measurability.
    cases n with
    | zero =>
        simpa [A, paleyWienerBrownianFourierCoefficients, brownianFourierCoefficients_zero] using
          ((((Lp.stronglyMeasurable (ξ 0)).measurable.aemeasurable).pow_const
            (2 : ℕ)).ennreal_ofReal)
    | succ n =>
        simpa [A, paleyWienerBrownianFourierCoefficients, brownianFourierCoefficients_succ] using
          ((((Lp.stronglyMeasurable (ξ (n + 1))).measurable.div_const
            (((n + 1 : ℝ) * Real.pi))).aemeasurable).pow_const
              (2 : ℕ)).ennreal_ofReal
  have hSeriesLintegral_ne_top :
      (∫⁻ ω, ∑' n : ℕ, ENNReal.ofReal ((A n ω) ^ (2 : ℕ)) ∂μ) ≠ ⊤ := by
    -- Proof comment: Tonelli rewrites the total square-energy integral as the deterministic
    -- series of second moments, and those moments are summable.
    rw [MeasureTheory.lintegral_tsum hMeas]
    have hMoments :
        (∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((A n ω) ^ (2 : ℕ)) ∂μ) =
          ∑' n : ℕ,
            ENNReal.ofReal
              (match n with
              | 0 => (1 : ℝ)
              | n + 1 => 1 / (((n + 1 : ℝ) * Real.pi) ^ (2 : ℕ))) := by
      refine tsum_congr fun n ↦ ?_
      simpa [A, paleyWienerBrownianFourierCoefficients] using
        brownianFourierCoefficients_sqMoment_lintegral_eq ξ hξ_gaussian n
    rw [hMoments]
    exact brownianFourierCoefficients_sqMomentSeries_summable.tsum_ofReal_ne_top
  -- Proof comment: an a.e.-finite `ENNReal` square series converts back to an ordinary summable
  -- nonnegative real series pointwise.
  refine
    (MeasureTheory.ae_lt_top'
      (AEMeasurable.ennreal_tsum hMeas) hSeriesLintegral_ne_top).mono ?_
  intro ω hω
  have hω_ne_top : (∑' n : ℕ, ENNReal.ofReal ((A n ω) ^ (2 : ℕ))) ≠ ⊤ := hω.ne
  have hsum :
      Summable (fun n : ℕ ↦ (ENNReal.ofReal ((A n ω) ^ (2 : ℕ))).toReal) :=
    ENNReal.summable_toReal hω_ne_top
  convert hsum using 1
  ext n
  symm
  exact ENNReal.toReal_ofReal (by simpa [pow_two] using sq_nonneg (A n ω))

-- Proof sketch: the source-facing Example 21.29 coefficients differ from the explicit helper
-- sequence only by the definitional bridge above. The positive-mode coefficients are independent
-- centered Gaussians with standard deviation comparable to `1 / n`. Kolmogorov's three-series
-- theorem applied to `paleyWienerBrownianFourierCoefficients ξ` yields
-- almost-sure divergence of the nonnegative series `∑ |Aₙ|`, and adding the zeroth term does not
-- change the divergence conclusion.
/-- Exercise 21.5.5 (2): the series of absolute values of the Brownian Fourier coefficients
diverges to `+∞` almost surely. -/
theorem brownianFourierCoefficients_absPartialSums_tendsto_atTop_ae
    (hξ_gaussian : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦
          ∑ k ∈ Finset.range (n + 1),
            |paleyWienerBrownianFourierCoefficients ξ k ω|)
        atTop atTop := by
  let A := paleyWienerBrownianFourierCoefficients ξ
  let c : ℝ :=
    ∫ x, Set.indicator {x : ℝ | |x| ≤ 1} (fun x ↦ |x|) x ∂gaussianReal 0 1
  have hc_pos : 0 < c := by
    simpa [c] using standardGaussian_truncatedAbsMeanPos
  have hA_tail_meas : ∀ n, Measurable (fun ω ↦ A (n + 1) ω) := by
    intro n
    -- Proof comment: the shifted coefficient sequence is just the measurable positive-frequency
    -- Brownian Fourier tail.
    simpa [A, paleyWienerBrownianFourierCoefficients] using
      brownianFourierCoefficients_succ_measurable ξ n
  have hA_tail_indep : iIndepFun (fun n ↦ fun ω ↦ A (n + 1) ω) μ := by
    simpa [A, paleyWienerBrownianFourierCoefficients] using
      brownianFourierCoefficients_succ_iIndepFun ξ hξ_indep
  have hB_meas : ∀ n, Measurable (fun ω ↦ |A (n + 1) ω|) := by
    intro n
    exact (hA_tail_meas n).abs
  have hB_indep : iIndepFun (fun n ↦ fun ω ↦ |A (n + 1) ω|) μ := by
    simpa using hA_tail_indep.comp (fun _ ↦ fun x : ℝ ↦ |x|) (fun _ ↦ measurable_abs)
  let truncAbs : ℕ → ℝ := fun n ↦
    μ[Set.indicator {ω | |(|A (n + 1) ω|)| ≤ 1} (fun ω ↦ |A (n + 1) ω|)]
  have htruncAbs_nonneg : ∀ n : ℕ, 0 ≤ truncAbs n := by
    intro n
    exact integral_nonneg fun ω ↦ Set.indicator_apply_nonneg fun _ ↦ abs_nonneg _
  have hlower_le : ∀ n : ℕ, c / (((n + 1 : ℝ) * Real.pi)) ≤ truncAbs n := by
    intro n
    simpa [A, c, truncAbs, paleyWienerBrownianFourierCoefficients] using
      brownianFourierCoefficients_succ_truncatedAbsExpectation_ge ξ hξ_gaussian n
  have hnot_harmonic_shift : ¬ Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) := by
    exact not_summable_one_div_nat_succ
  have hnot_lower : ¬ Summable (fun n : ℕ ↦ c / (((n + 1 : ℝ) * Real.pi))) := by
    intro hsum
    have hcpi_pos : 0 < c / Real.pi := by
      positivity
    have hsum' : Summable (fun n : ℕ ↦ (c / Real.pi) * (1 / (n + 1 : ℝ))) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsum
    exact hnot_harmonic_shift ((summable_mul_left_iff hcpi_pos.ne').1 hsum')
  have htruncAbs_notSummable : ¬ Summable truncAbs := by
    intro hsum
    exact hnot_lower (hsum.of_nonneg_of_le (fun n : ℕ ↦ by positivity) hlower_le)
  have hthree :=
    ae_summable_iff_three_series_conditions
      μ 1 (by norm_num) (fun n ω ↦ |A n ω|) hB_meas hB_indep
  have hnot_ae_summable : ¬ ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦ |A (n + 1) ω|) := by
    intro hsum
    exact htruncAbs_notSummable (hthree.mp hsum).2.1
  let E : Set Ω := {ω | Summable (fun n : ℕ ↦ |A (n + 1) ω|)}
  have hE_tail :
      MeasurableSet[limsup (fun n ↦ MeasurableSpace.comap (fun ω ↦ |A (n + 1) ω|) (borel ℝ))
        atTop] E := by
    simpa [E] using
      measurableSet_tail_summable_of_nonneg
        (fun n ω ↦ |A (n + 1) ω|) hB_meas (fun n ω ↦ abs_nonneg _)
  have htail_le :
      limsup (fun n ↦ MeasurableSpace.comap (fun ω ↦ |A (n + 1) ω|) (borel ℝ)) atTop ≤
        ‹MeasurableSpace Ω› := by
    exact limsup_le_iSup.trans <| iSup_le fun n ↦ (hB_meas n).comap_le
  have hE_meas : MeasurableSet E := htail_le _ hE_tail
  have hE_zero_or_one : μ E = 0 ∨ μ E = 1 :=
    ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n ↦ (hB_meas n).comap_le) hB_indep.iIndep hE_tail
  have hE_ne_one : μ E ≠ 1 := by
    intro hE_one
    have hE_comp_zero : μ Eᶜ = 0 := by
      have hE_ne_top : μ E ≠ ⊤ := by rw [hE_one]; simp
      simpa [hE_one, IsProbabilityMeasure.measure_univ] using measure_compl hE_meas hE_ne_top
    have hE_ae : ∀ᵐ ω ∂μ, ω ∈ E := by
      rw [ae_iff]
      simpa using hE_comp_zero
    exact hnot_ae_summable (by simpa [E] using hE_ae)
  have hE_zero : μ E = 0 := by
    rcases hE_zero_or_one with hE_zero | hE_one
    · exact hE_zero
    · exact (hE_ne_one hE_one).elim
  have htail_notSummable_ae : ∀ᵐ ω ∂μ, ¬ Summable (fun n : ℕ ↦ |A (n + 1) ω|) := by
    rw [ae_iff]
    simpa [E] using hE_zero
  filter_upwards [htail_notSummable_ae] with ω hω
  have htail_tendsto :
      Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, |A (j + 1) ω|) atTop atTop := by
    rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
    · exact hω
    · intro n
      exact abs_nonneg _
  have hfull_tendsto :
      Tendsto (fun n : ℕ ↦ |A 0 ω| + ∑ j ∈ Finset.range n, |A (j + 1) ω|) atTop atTop :=
    tendsto_atTop_add_const_left atTop (|A 0 ω|) htail_tendsto
  -- Proof comment: splitting off the fixed zeroth term converts tail divergence into the stated
  -- divergence of the full absolute partial sums.
  convert hfull_tendsto using 1
  ext n
  simpa [A, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (Finset.sum_range_add (fun k ↦ |A k ω|) 1 n)

-- Proof sketch: the source-facing Example 21.29 coefficients form an independent centered Gaussian
-- sequence with summable variances, namely `1` at index `0` and `1 / (π² n²)` on the positive
-- modes. Kolmogorov's three-series theorem therefore gives almost-sure convergence of `∑ Aₙ`.
/-- Part (3) of Exercise 21.5.5: the Fourier-basis coefficient series in the Example 21.29
construction of Brownian motion converges almost surely. -/
theorem brownianFourierCoefficients_summable_ae
    (hξ_gaussian : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ) :
    ∀ᵐ ω ∂μ,
      Summable (fun n ↦ paleyWienerBrownianFourierCoefficients ξ n ω) := by
  let A := paleyWienerBrownianFourierCoefficients ξ
  have hA_tail_meas : ∀ n, Measurable (fun ω ↦ A (n + 1) ω) := by
    intro n
    -- Proof comment: the shifted series is the measurable positive-frequency Fourier tail.
    simpa [A, paleyWienerBrownianFourierCoefficients] using
      brownianFourierCoefficients_succ_measurable ξ n
  have hA_tail_indep : iIndepFun (fun n ↦ fun ω ↦ A (n + 1) ω) μ := by
    simpa [A, paleyWienerBrownianFourierCoefficients] using
      brownianFourierCoefficients_succ_iIndepFun ξ hξ_indep
  have hthree :
      (∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦ A (n + 1) ω)) ↔
        Summable (fun n : ℕ ↦ μ.real {ω | 1 < |A (n + 1) ω|}) ∧
          Summable
            (fun n : ℕ ↦
              μ[Set.indicator {ω | |A (n + 1) ω| ≤ 1} (A (n + 1))]) ∧
            Summable
              (fun n : ℕ ↦
                Var[Set.indicator {ω | |A (n + 1) ω| ≤ 1} (A (n + 1)); μ]) :=
    ae_summable_iff_three_series_conditions
      μ 1 (by norm_num) A hA_tail_meas hA_tail_indep
  have hconds :
      Summable (fun n : ℕ ↦ μ.real {ω | 1 < |A (n + 1) ω|}) ∧
        Summable
          (fun n : ℕ ↦
            μ[Set.indicator {ω | |A (n + 1) ω| ≤ 1} (A (n + 1))]) ∧
          Summable
            (fun n : ℕ ↦ Var[Set.indicator {ω | |A (n + 1) ω| ≤ 1} (A (n + 1)); μ]) := by
    have hsq_tail := brownianFourierCoefficients_positiveTailSqSummable
    constructor
    · -- Proof comment: the large-jump probabilities are dominated termwise by the square moments.
      refine hsq_tail.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
      simpa [A, paleyWienerBrownianFourierCoefficients] using
        brownianFourierCoefficients_succ_largeJumpProb_le ξ hξ_gaussian n
    constructor
    · -- Proof comment: the truncated centered expectations vanish termwise.
      refine (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ))).congr ?_
      intro n
      simpa [A, paleyWienerBrownianFourierCoefficients] using
        (brownianFourierCoefficients_succ_truncatedMeanZero ξ hξ_gaussian n).symm
    · -- Proof comment: the truncated variances are bounded by the same summable square-moment tail.
      refine hsq_tail.of_nonneg_of_le (fun n ↦ variance_nonneg _ _) fun n ↦ ?_
      simpa [A, paleyWienerBrownianFourierCoefficients] using
        brownianFourierCoefficients_succ_truncatedVariance_le ξ hξ_gaussian n
  have htail : ∀ᵐ ω ∂μ, Summable (fun n : ℕ ↦ A (n + 1) ω) := hthree.mpr hconds
  filter_upwards [htail] with ω hω
  -- Proof comment: adding back the deterministic zeroth term preserves summability.
  exact (_root_.summable_nat_add_iff 1).1 hω

end BrownianFourierCoefficients

end ProbabilityTheory

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_1_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_37
import Mathlib.Analysis.Fourier.Notation

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory FourierTransform

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 15.51: the normalization factor `√Var[X 1; P]` is strictly positive. -/
private lemma berryEsseenSigmaPos
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_var : 0 < Var[X 1; P]) :
    0 < Real.sqrt (Var[X 1; P]) := by
  -- Proof comment: positivity of the variance gives a nonzero normalization scale.
  exact Real.sqrt_pos.2 hX_var

/-- Helper for Theorem 15.51: `standardizedPartialSum` coincides with the textbook normalized sum
of the rescaled variables `X (k + 1) / √Var[X 1; P]`. -/
private lemma standardizedPartialSum_eq_normalizedSum
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P]) (n : ℕ) :
    standardizedPartialSum P (fun k ↦ X (k + 1)) n =
      fun ω ↦
        (Real.sqrt (n : ℝ))⁻¹ *
          ∑ k ∈ Finset.range n, X (k + 1) ω / Real.sqrt (Var[X 1; P]) := by
  funext ω
  have hσ0 : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hVar_nonneg : 0 ≤ Var[X 1; P] := le_of_lt hX_var
  -- Proof comment: unfold the owner normalization and split `√(n * Var)` into `√n * √Var`.
  calc
    standardizedPartialSum P (fun k ↦ X (k + 1)) n ω
        = (Real.sqrt (n * Var[X 1; P]))⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) ω := by
            simp [standardizedPartialSum, hX_mean]
    _ = ((Real.sqrt (n : ℝ) * Real.sqrt (Var[X 1; P]))⁻¹) *
          ∑ k ∈ Finset.range n, X (k + 1) ω := by
            rw [show (n * Var[X 1; P] : ℝ) = (n : ℝ) * Var[X 1; P] by norm_num,
              Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity)]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          ((∑ k ∈ Finset.range n, X (k + 1) ω) / Real.sqrt (Var[X 1; P])) := by
            field_simp [hσ0]
    _ = (Real.sqrt (n : ℝ))⁻¹ *
          ∑ k ∈ Finset.range n, X (k + 1) ω / Real.sqrt (Var[X 1; P]) := by
            rw [Finset.sum_div]

/-- Helper for Theorem 15.51: the characteristic function of the standardized partial-sum law is
the `n`th power of the characteristic function of the normalized one-step law evaluated at
`t / √n`. -/
private lemma iidSucc_charFun_standardizedPartialSum_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P]) (n : ℕ+) (t : ℝ) :
    charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
      (charFun (P.map (fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])))
          ((Real.sqrt (n : ℝ))⁻¹ * t)) ^ (n : ℕ) := by
  let Y : ℕ → Ω → ℝ := fun k ω ↦ X (k + 1) ω / Real.sqrt (Var[X 1; P])
  have hY_indep : iIndepFun Y P := by
    -- Proof comment: independence is preserved by the common measurable scaling map.
    simpa [Y] using
      hX_iid.iIndepFun.comp
        (fun _ x ↦ x / Real.sqrt (Var[X 1; P]))
        (fun _ ↦ MeasurableDiv.measurable_div_const _)
  have hY_ident : ∀ k : ℕ, IdentDistrib (Y k) (Y 0) P P := by
    intro k
    -- Proof comment: identical distribution is preserved by applying the same measurable map.
    simpa [Y] using
      (hX_iid.identDistrib k 0).div_const (Real.sqrt (Var[X 1; P]))
  have hsum :
      standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ) =
        fun ω ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range (n : ℕ), Y k ω :=
    standardizedPartialSum_eq_normalizedSum P X hX_mean hX_var (n : ℕ)
  -- Proof comment: rewrite the standardized sum into the CLT normal form and apply the iid
  -- characteristic-function product formula.
  calc
    charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t
        = charFun (P.map (fun ω ↦
            (Real.sqrt (n : ℝ))⁻¹ * ∑ k ∈ Finset.range (n : ℕ), Y k ω)) t := by
              rw [Measure.map_congr (Filter.Eventually.of_forall fun ω ↦ congrFun hsum ω)]
    _ = (charFun (P.map (Y 0)) ((Real.sqrt (n : ℝ))⁻¹ * t)) ^ (n : ℕ) := by
          simpa using
            ProbabilityTheory.charFun_inv_sqrt_mul_sum
              (P := P) (X := Y) hY_indep hY_ident (n := (n : ℕ)) (t := t)
    _ =
        (charFun (P.map (fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])))
          ((Real.sqrt (n : ℝ))⁻¹ * t)) ^ (n : ℕ) := by
            rfl

/-- Helper for Theorem 15.51: the normalized one-step entry `X 1 / √Var[X 1; P]` is centered. -/
private lemma normalizedEntryMean_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P]) :
    P[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])] = 0 := by
  -- Proof comment: rewrite the normalization as multiplication by a deterministic reciprocal.
  have hσ0 : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  calc
    P[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])]
        = P[fun ω ↦ (Real.sqrt (Var[X 1; P]))⁻¹ * X 1 ω] := by
            simp [div_eq_mul_inv, mul_comm]
    _ = (Real.sqrt (Var[X 1; P]))⁻¹ * P[X 1] := by
          rw [integral_const_mul]
    _ = 0 := by
          rw [hX_mean, mul_zero]

/-- Helper for Theorem 15.51: scaling by `1 / √Var[X 1; P]` normalizes the variance to `1`. -/
private lemma normalizedEntryVariance_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_var : 0 < Var[X 1; P]) :
    Var[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P]); P] = 1 := by
  have hσ0 : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hσsq : Real.sqrt (Var[X 1; P]) ^ (2 : ℕ) = Var[X 1; P] := by
    simp [Real.sq_sqrt (le_of_lt hX_var)]
  -- Proof comment: express the normalized entry as a scalar multiple and use variance homogeneity.
  calc
    Var[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P]); P]
        = Var[X 1; P] * (Real.sqrt (Var[X 1; P]))⁻¹ ^ (2 : ℕ) := by
            rw [show (fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])) =
                fun ω ↦ X 1 ω * (Real.sqrt (Var[X 1; P]))⁻¹ by
                  ext ω
                  simp [div_eq_mul_inv]]
            rw [variance_mul_const]
    _ = 1 := by
          rw [inv_pow, hσsq]
          field_simp [hσ0]

/-- Helper for Theorem 15.51: the normalized third absolute moment is the original one divided by
`(√Var[X 1; P])³`. -/
private lemma normalizedEntryThirdMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P) :
    Integrable (fun ω ↦ |X 1 ω / Real.sqrt (Var[X 1; P])| ^ (3 : ℕ)) P ∧
      absoluteMoment (fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])) 3 P =
        absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
  let σ : ℝ := Real.sqrt (Var[X 1; P])
  have hσ_pos : 0 < σ := berryEsseenSigmaPos P X hX_var
  have hScaled :
      (fun ω ↦ |X 1 ω / σ| ^ (3 : ℕ)) = fun ω ↦ |X 1 ω| ^ (3 : ℕ) / σ ^ (3 : ℕ) := by
    funext ω
    rw [abs_div, abs_of_pos hσ_pos, div_pow]
  refine ⟨?_, ?_⟩
  · -- Proof comment: after rewriting the normalized absolute cube, this is just constant scaling.
    rw [hScaled]
    exact hX_third.div_const (σ ^ (3 : ℕ))
  · -- Proof comment: rewrite both absolute moments as expectations and pull out the scale factor.
    rw [absoluteMoment_eq_expectation_abs_pow, absoluteMoment_eq_expectation_abs_pow, hScaled]
    simpa [σ] using
      (MeasureTheory.integral_div (σ ^ (3 : ℕ)) (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) (μ := P))

/-- Helper for Theorem 15.51: the normalized one-step entry has mean `0`, variance `1`, and the
expected cubic absolute-moment scaling. -/
private lemma normalizedEntryMomentFacts
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P) :
    P[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])] = 0 ∧
      Var[fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P]); P] = 1 ∧
      Integrable (fun ω ↦ |X 1 ω / Real.sqrt (Var[X 1; P])| ^ (3 : ℕ)) P ∧
      absoluteMoment (fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])) 3 P =
        absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
  -- Proof comment: bundle the normalization identities so the main theorem need not repeat them.
  rcases normalizedEntryThirdMoment P X hX_var hX_third with ⟨hInt, hMoment⟩
  exact ⟨normalizedEntryMean_zero P X hX_mean hX_var, normalizedEntryVariance_one P X hX_var,
    hInt, hMoment⟩

/-- Helper for Theorem 15.51: a finite third absolute moment forces integrability of the entry. -/
private lemma integrable_of_integrable_absThird
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P) :
    Integrable Y P := by
  -- Proof comment: a finite third absolute moment gives `Y ∈ L^3`, hence also `Y ∈ L^1`.
  have hY_memLp3 : MeasureTheory.MemLp Y (3 : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hY_meas.aestronglyMeasurable]
    · simpa [Real.norm_eq_abs] using hY_third
    · norm_num
    · norm_num
  have hY_memLp1 : MeasureTheory.MemLp Y (1 : ENNReal) P :=
    hY_memLp3.mono_exponent (show (1 : ENNReal) ≤ 3 by norm_num)
  exact MeasureTheory.memLp_one_iff_integrable.mp hY_memLp1

/-- Helper for Theorem 15.51: a finite third absolute moment also gives integrability of the
quadratic moment. -/
private lemma integrable_sq_of_integrable_absThird
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P) :
    Integrable (fun ω ↦ Y ω ^ (2 : ℕ)) P := by
  -- Proof comment: pass from `L^3` to `L^2`, then use the dedicated square-integrability API.
  have hY_memLp3 : MeasureTheory.MemLp Y (3 : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hY_meas.aestronglyMeasurable]
    · simpa [Real.norm_eq_abs] using hY_third
    · norm_num
    · norm_num
  have hY_memLp2 : MeasureTheory.MemLp Y (2 : ENNReal) P :=
    hY_memLp3.mono_exponent (show (2 : ENNReal) ≤ 3 by norm_num)
  simpa using hY_memLp2.integrable_sq

/-- Helper for Theorem 15.51: for a centered variance-one entry, the second moment equals `1`. -/
private lemma centeredSecondMoment_eq_one
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1) :
    ∫ ω, Y ω ^ (2 : ℕ) ∂P = 1 := by
  -- Proof comment: `Var[Y] = E[Y^2]` under centering, so the variance normalization fixes the
  -- quadratic coefficient in the Taylor expansion.
  rw [← hY_var]
  exact (ProbabilityTheory.variance_of_integral_eq_zero hY_meas hY_mean).symm

/-- Helper for Theorem 15.51: the quadratic Taylor polynomial of the normalized entry's
characteristic function is `1 - u² / 2`. -/
private lemma charFunQuadraticTaylorAtZero
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (u : ℝ) :
    taylorWithinEval (charFun (P.map Y)) 2 Set.univ 0 u =
      1 - (u : ℂ) ^ (2 : ℕ) / 2 := by
  -- Proof comment: the pushforward-law Taylor formula collapses to the centered variance-one
  -- polynomial once the second moment is normalized to `1`.
  have hY_second : P[fun ω ↦ Y ω ^ (2 : ℕ)] = 1 :=
    centeredSecondMoment_eq_one P Y hY_meas hY_mean hY_var
  simpa [Pi.pow_apply] using
    (MeasureTheory.taylorWithinEval_charFun_two_zero' hY_meas hY_mean hY_second u)

/-- Helper for Theorem 15.51: the remainder after truncating `exp (t * I)` at second order is
bounded by `|t|³ / 6`. -/
private lemma normExpMulISecondTaylorSumRemainder_le
    (t : ℝ) :
    ‖Complex.exp (((t : ℝ) : ℂ) * Complex.I) -
        (1 + ((t : ℂ) * Complex.I) + ((((t : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))‖ ≤
      |t| ^ (3 : ℕ) / 6 := by
  -- Proof comment: this is the order-three Taylor remainder estimate specialized to the scalar
  -- oscillatory exponential.
  simpa [Finset.sum_range_succ, div_eq_mul_inv, Nat.factorial, sub_eq_add_neg, mul_assoc,
    mul_left_comm, mul_comm] using
    norm_exp_mul_I_sub_taylor_sum_le (t := t) (n := 3)

/-- Helper for Theorem 15.51: squaring the phase `z * I` only changes the sign of `z² / 2`. -/
private lemma complexMulI_sq_div_two
    (z : ℂ) :
    ((z * Complex.I) ^ (2 : ℕ)) / 2 = -(z ^ (2 : ℕ)) / 2 := by
  calc
    ((z * Complex.I) ^ (2 : ℕ)) / 2 =
        (z ^ (2 : ℕ) * (Complex.I ^ (2 : ℕ))) / 2 := by
          simp [pow_two, mul_left_comm, mul_comm]
    _ = (z ^ (2 : ℕ) * (-1 : ℂ)) / 2 := by
          simp [pow_two]
    _ = -(z ^ (2 : ℕ)) / 2 := by
          ring

/-- Helper for Theorem 15.51: the norm of a real difference viewed in `ℂ` is the corresponding
absolute value on `ℝ`. -/
private lemma complexNorm_ofRealSub_eq_abs
    (a b : ℝ) :
    ‖((a : ℂ) - (b : ℂ))‖ = |a - b| := by
  simpa using (Complex.norm_real (a - b))

/-- Helper for Theorem 15.51: after using the centered and variance-one moment identities, the
quadratic defect of `charFun (P.map Y)` is the integral of the pointwise second-order Taylor
remainder on the original probability space. -/
private lemma charFunQuadraticDefect_eq_integralSecondTaylorRemainder
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    (u : ℝ) :
    charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2) =
      ∫ ω,
        (Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I) -
          (1 + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
            (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))) ∂P := by
  have hY_int : Integrable Y P :=
    integrable_of_integrable_absThird P Y hY_meas hY_third
  have hY_sq_int : Integrable (fun ω ↦ Y ω ^ (2 : ℕ)) P :=
    integrable_sq_of_integrable_absThird P Y hY_meas hY_third
  have hY_second : ∫ ω, Y ω ^ (2 : ℕ) ∂P = 1 :=
    centeredSecondMoment_eq_one P Y hY_meas hY_mean hY_var
  have hExpMapAEMeas :
      AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (u * x * Complex.I)) (P.map Y) := by
    -- Proof comment: the oscillatory exponential kernel is measurable on the pushforward space.
    refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
    simpa using
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
  have hExpIntMap :
      Integrable (fun x : ℝ ↦ Complex.exp (u * x * Complex.I)) (P.map Y) := by
    -- Proof comment: the oscillatory exponential has unit norm, so it is integrable on a
    -- probability space.
    refine Integrable.of_bound hExpMapAEMeas 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (u * x)).le
  have hExpInt :
      Integrable (fun ω ↦ Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I)) P := by
    simpa using hExpIntMap.comp_aemeasurable hY_meas
  have hLinearInt :
      Integrable (fun ω ↦ (((u * Y ω : ℝ) : ℂ) * Complex.I)) P := by
    have hConst :
        Integrable (fun ω ↦ ((u : ℂ) * Complex.I) * (Y ω : ℂ)) P :=
      hY_int.ofReal.const_mul ((u : ℂ) * Complex.I)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hConst
  have hQuadEq :
      (fun ω ↦ ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2) =
        fun ω ↦ (-((u : ℂ) ^ (2 : ℕ)) / 2) * (((Y ω ^ (2 : ℕ) : ℝ) : ℂ)) := by
    funext ω
    rw [complexMulI_sq_div_two]
    simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hQuadInt :
      Integrable (fun ω ↦ ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2) P := by
    rw [hQuadEq]
    exact hY_sq_int.ofReal.const_mul (-((u : ℂ) ^ (2 : ℕ)) / 2)
  have hMeanZero :
      ∫ ω, (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
    have hOfReal :
        ∫ ω, (Y ω : ℂ) ∂P = ((∫ ω, Y ω ∂P : ℝ) : ℂ) := by
      simpa using (integral_complex_ofReal (μ := P) (f := fun ω ↦ Y ω))
    calc
      ∫ ω, (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω, ((u : ℂ) * Complex.I) * (Y ω : ℂ) ∂P := by
            congr with ω
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ((u : ℂ) * Complex.I) * ∫ ω, (Y ω : ℂ) ∂P := by
            simpa using
              (integral_const_mul (μ := P) ((u : ℂ) * Complex.I) (fun ω ↦ (Y ω : ℂ)))
      _ = ((u : ℂ) * Complex.I) * ((∫ ω, Y ω ∂P : ℝ) : ℂ) := by
            rw [hOfReal]
      _ = 0 := by
            simp [hY_mean]
  have hQuadEval :
      ∫ ω, ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2 ∂P = -((u : ℂ) ^ (2 : ℕ)) / 2 := by
    have hSqOfReal :
        ∫ ω, (((Y ω ^ (2 : ℕ) : ℝ) : ℂ)) ∂P = ((∫ ω, Y ω ^ (2 : ℕ) ∂P : ℝ) : ℂ) := by
      simpa using (integral_complex_ofReal (μ := P) (f := fun ω ↦ Y ω ^ (2 : ℕ)))
    calc
      ∫ ω, ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2 ∂P =
          ∫ ω, (-((u : ℂ) ^ (2 : ℕ)) / 2) * (((Y ω ^ (2 : ℕ) : ℝ) : ℂ)) ∂P := by
            rw [hQuadEq]
      _ = (-((u : ℂ) ^ (2 : ℕ)) / 2) * ∫ ω, (((Y ω ^ (2 : ℕ) : ℝ) : ℂ)) ∂P := by
            simpa using
              (integral_const_mul (μ := P) (-((u : ℂ) ^ (2 : ℕ)) / 2)
                (fun ω ↦ (((Y ω ^ (2 : ℕ) : ℝ) : ℂ))))
      _ = (-((u : ℂ) ^ (2 : ℕ)) / 2) * (1 : ℂ) := by
            rw [hSqOfReal, hY_second]
            simp
      _ = -((u : ℂ) ^ (2 : ℕ)) / 2 := by
            ring
  have hLinQuadInt :
      Integrable (fun ω ↦
        (((u * Y ω : ℝ) : ℂ) * Complex.I) +
          (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) P :=
    hLinearInt.add hQuadInt
  have hPolyInt :
      Integrable (fun ω ↦
        (1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
          (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) P := by
    -- Proof comment: the Taylor polynomial is integrable because each coefficient term is.
    simpa [add_assoc] using (integrable_const (1 : ℂ)).add hLinQuadInt
  have hPolyEval :
      ∫ ω,
          ((1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
            (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P =
        1 - (u : ℂ) ^ (2 : ℕ) / 2 := by
    -- Proof comment: centering kills the linear term and the variance normalization fixes the
    -- quadratic coefficient.
    calc
      ∫ ω,
          ((1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
            (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P =
          ∫ ω, (1 : ℂ) ∂P + ∫ ω, (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P +
            ∫ ω, ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2 ∂P := by
              have hConstSplit :
                  ∫ ω,
                      ((1 : ℂ) +
                        ((((u * Y ω : ℝ) : ℂ) * Complex.I) +
                          (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))) ∂P =
                    ∫ ω, (1 : ℂ) ∂P +
                      ∫ ω,
                        ((((u * Y ω : ℝ) : ℂ) * Complex.I) +
                          (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P := by
                    simpa using
                      (integral_add (μ := P) (f := fun _ ↦ (1 : ℂ))
                        (g := fun ω ↦
                          (((u * Y ω : ℝ) : ℂ) * Complex.I) +
                            (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))
                        (integrable_const (1 : ℂ)) hLinQuadInt)
              have hLinQuadSplit :
                  ∫ ω,
                      ((((u * Y ω : ℝ) : ℂ) * Complex.I) +
                        (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P =
                    ∫ ω, (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P +
                      ∫ ω, ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2 ∂P := by
                    simpa using
                      (integral_add (μ := P)
                        (f := fun ω ↦ (((u * Y ω : ℝ) : ℂ) * Complex.I))
                        (g := fun ω ↦ ((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)
                        hLinearInt hQuadInt)
              rw [show
                (∫ ω,
                    ((1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
                      (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P) =
                  ∫ ω,
                    ((1 : ℂ) +
                      ((((u * Y ω : ℝ) : ℂ) * Complex.I) +
                        (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))) ∂P by
                congr with ω
                ring]
              rw [hConstSplit, hLinQuadSplit]
              ring
      _ = 1 + 0 + (-((u : ℂ) ^ (2 : ℕ)) / 2) := by
            rw [hMeanZero, hQuadEval]
            simp
      _ = 1 - (u : ℂ) ^ (2 : ℕ) / 2 := by
            ring
  -- Proof comment: rewrite the defect as the difference of two integrals and merge them into a
  -- single integral over the pointwise Taylor remainder.
  calc
    charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2) =
        ∫ ω, Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P -
          ∫ ω,
            ((1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
              (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2)) ∂P := by
          have hExpRewrite :
              ∫ x, Complex.exp (u * x * Complex.I) ∂P.map Y =
                ∫ ω, Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I) ∂P := by
                  rw [integral_map hY_meas hExpMapAEMeas]
                  refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
                  simp [mul_assoc, mul_left_comm, mul_comm]
          rw [MeasureTheory.charFun_apply_real]
          rw [hExpRewrite]
          rw [hPolyEval]
    _ =
        ∫ ω,
          (Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I) -
            ((1 : ℂ) + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
              (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))) ∂P := by
          symm
          rw [integral_sub hExpInt hPolyInt]

/-- Helper for Theorem 15.51: a centered, variance-one entry with finite third absolute moment has
the expected cubic Taylor remainder for its characteristic function. -/
private lemma normalizedEntryCharFunCubicRemainder
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    (u : ℝ) :
    ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ ≤
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 := by
  let R : Ω → ℂ := fun ω ↦
    Complex.exp (((u * Y ω : ℝ) : ℂ) * Complex.I) -
      (1 + (((u * Y ω : ℝ) : ℂ) * Complex.I) +
        (((((u * Y ω : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ)) / 2))
  have hMajorantEq :
      (fun ω ↦ |u * Y ω| ^ (3 : ℕ) / 6) =
        fun ω ↦ (|u| ^ (3 : ℕ) / 6) * |Y ω| ^ (3 : ℕ) := by
    funext ω
    rw [abs_mul, mul_pow]
    ring
  have hMajorantInt : Integrable (fun ω ↦ |u * Y ω| ^ (3 : ℕ) / 6) P := by
    -- Proof comment: the pointwise Taylor majorant is the third absolute moment scaled by `|u|³`.
    rw [hMajorantEq]
    exact hY_third.const_mul (|u| ^ (3 : ℕ) / 6)
  have hPointwise :
      ∀ᵐ ω ∂P,
        ‖R ω‖ ≤
          |u * Y ω| ^ (3 : ℕ) / 6 := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    simpa [R] using normExpMulISecondTaylorSumRemainder_le (u * Y ω)
  -- Proof comment: after the bridge lemma, the scalar third-order Taylor remainder integrates
  -- directly to the textbook cubic absolute-moment bound.
  rw [charFunQuadraticDefect_eq_integralSecondTaylorRemainder
    P Y hY_meas hY_mean hY_var hY_third u]
  calc
    ‖∫ ω, R ω ∂P‖
        ≤ ∫ ω, |u * Y ω| ^ (3 : ℕ) / 6 ∂P := by
            exact MeasureTheory.norm_integral_le_of_norm_le hMajorantInt hPointwise
    _ = (|u| ^ (3 : ℕ) / 6) * ∫ ω, |Y ω| ^ (3 : ℕ) ∂P := by
          rw [hMajorantEq, integral_const_mul]
    _ = absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 := by
          rw [absoluteMoment_eq_expectation_abs_pow]
          ring

/-- Helper for Theorem 15.51: a centered variance-one entry on a probability space has third
absolute moment at least `1`. -/
private lemma one_le_absoluteMoment_three_of_variance_one
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P) :
    1 ≤ absoluteMoment Y 3 P := by
  have hY_memLp3 : MemLp Y 3 P := by
    -- Proof comment: the finite third absolute moment is exactly the `L³` condition.
    rw [← MeasureTheory.integrable_norm_rpow_iff hY_meas.aestronglyMeasurable]
    · simpa [Real.norm_eq_abs] using hY_third
    · norm_num
    · norm_num
  have hY_memLp2 : MemLp Y 2 P :=
    hY_memLp3.mono_exponent (show (2 : ENNReal) ≤ 3 by norm_num)
  have hcompare : eLpNorm Y 2 P ≤ eLpNorm Y 3 P :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (show (2 : ENNReal) ≤ 3 by norm_num) hY_meas.aestronglyMeasurable
  have htwo : eLpNorm Y 2 P = ENNReal.ofReal 1 := by
    have hY_second : P[fun ω ↦ Y ω ^ (2 : ℕ)] = 1 :=
      centeredSecondMoment_eq_one P Y hY_meas hY_mean hY_var
    -- Proof comment: the `L²` norm is the square root of the normalized second moment.
    calc
      eLpNorm Y 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, (Y ω) ^ (2 : ℕ) ∂P)) := by
        simpa [Real.sqrt_eq_rpow, one_div, sq_abs] using
          (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hY_memLp2)
      _ = ENNReal.ofReal 1 := by
        simp [hY_second]
  have hthree :
      eLpNorm Y 3 P = ENNReal.ofReal ((absoluteMoment Y 3 P) ^ (1 / (3 : ℝ))) := by
    -- Proof comment: rewrite the `L³` norm in terms of the textbook third absolute moment.
    calc
      eLpNorm Y 3 P = ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ (3 : ℝ) ∂P) ^ (1 / (3 : ℝ))) := by
        simpa [one_div] using
          (MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top hY_memLp3)
      _ = ENNReal.ofReal ((absoluteMoment Y 3 P) ^ (1 / (3 : ℝ))) := by
        rw [absoluteMoment_eq_expectation_abs_pow]
        simp [Real.norm_eq_abs]
  rw [htwo, hthree] at hcompare
  have hMoment_nonneg : 0 ≤ absoluteMoment Y 3 P := by
    rw [absoluteMoment_eq_expectation_abs_pow]
    positivity
  have hroot : (1 : ℝ) ≤ (absoluteMoment Y 3 P) ^ (1 / (3 : ℝ)) := by
    -- Proof comment: convert the `ENNReal` seminorm comparison back to a real inequality.
    exact
      (ENNReal.ofReal_le_ofReal_iff
        (show 0 ≤ (absoluteMoment Y 3 P) ^ (1 / (3 : ℝ)) by positivity)).mp <| by
          simpa using hcompare
  have hpow :
      (1 : ℝ) ^ (3 : ℕ) ≤ ((absoluteMoment Y 3 P) ^ (1 / (3 : ℝ))) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hroot 3
  calc
    1 = (1 : ℝ) ^ (3 : ℕ) := by norm_num
    _ ≤ ((absoluteMoment Y 3 P) ^ (1 / (3 : ℝ))) ^ (3 : ℕ) := hpow
    _ = absoluteMoment Y 3 P ^ (1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hMoment_nonneg]
      norm_num
    _ = absoluteMoment Y 3 P := by
      rw [Real.rpow_one]

/-- Helper for Theorem 15.51: on the small-frequency window `|u| ≤ absoluteMoment Y 3 P⁻¹`, the
characteristic function of a centered variance-one entry is subGaussian. -/
private lemma normalizedEntryCharFunSubGaussian
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    {u : ℝ} (hu : |u| ≤ (absoluteMoment Y 3 P)⁻¹) :
    ‖charFun (P.map Y) u‖ ≤ Real.exp (-(u ^ (2 : ℕ)) / 3) := by
  -- Route correction: stay on the cubic-remainder surface and absorb the Taylor defect directly
  -- into the quadratic proxy instead of reopening the downstream proxy/Gaussian block.
  have hMoment_ge_one : 1 ≤ absoluteMoment Y 3 P :=
    one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_third
  have hMoment_pos : 0 < absoluteMoment Y 3 P := by
    linarith
  have hMomentInv_le_one : (absoluteMoment Y 3 P)⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hMoment_ge_one
  have hu_le_one : |u| ≤ 1 := le_trans hu hMomentInv_le_one
  have hMomentMulU_le_one : absoluteMoment Y 3 P * |u| ≤ 1 := by
    calc
      absoluteMoment Y 3 P * |u| ≤ absoluteMoment Y 3 P * (absoluteMoment Y 3 P)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hu (by linarith)
      _ = 1 := by
        rw [mul_inv_cancel₀ hMoment_pos.ne']
  have hu_sq_le_one : u ^ (2 : ℕ) ≤ 1 := by
    nlinarith [sq_abs u, hu_le_one, abs_nonneg u]
  have hProxy_nonneg : 0 ≤ 1 - u ^ (2 : ℕ) / 2 := by
    nlinarith
  have hProxy_norm :
      ‖(1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ)‖ = 1 - u ^ (2 : ℕ) / 2 := by
    rw [show (1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) = ((1 - u ^ (2 : ℕ) / 2 : ℝ) : ℂ) by norm_num]
    simpa [Real.norm_of_nonneg hProxy_nonneg] using
      (Complex.ofRealLI.norm_map (1 - u ^ (2 : ℕ) / 2))
  have hCubicRemainder :=
    normalizedEntryCharFunCubicRemainder P Y hY_meas hY_mean hY_var hY_third u
  have hCubicAbsorb :
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 ≤ |u| ^ (2 : ℕ) / 6 := by
    -- Proof comment: the window condition gives `absoluteMoment Y 3 P * |u| ≤ 1`.
    calc
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 =
          (absoluteMoment Y 3 P * |u|) * (|u| ^ (2 : ℕ) / 6) := by
            ring
      _ ≤ 1 * (|u| ^ (2 : ℕ) / 6) := by
            exact mul_le_mul_of_nonneg_right hMomentMulU_le_one (by positivity)
      _ = |u| ^ (2 : ℕ) / 6 := by
            ring
  -- Proof comment: compare `charFun (P.map Y) u` with the quadratic proxy `1 - u² / 2` and then
  -- absorb the cubic remainder on the normalized frequency window.
  calc
    ‖charFun (P.map Y) u‖ =
        ‖(charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)) + (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := by
          congr 1
          ring
    _ ≤ ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ +
          ‖(1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 + (1 - u ^ (2 : ℕ) / 2) := by
          rw [hProxy_norm]
          exact add_le_add hCubicRemainder le_rfl
    _ ≤ |u| ^ (2 : ℕ) / 6 + (1 - u ^ (2 : ℕ) / 2) := by
          exact add_le_add hCubicAbsorb le_rfl
    _ = 1 - u ^ (2 : ℕ) / 3 := by
          rw [sq_abs]
          ring
    _ ≤ Real.exp (-(u ^ (2 : ℕ)) / 3) := by
          nlinarith [Real.add_one_le_exp (-(u ^ (2 : ℕ)) / 3)]

/-- Helper for Theorem 15.51: on the normalized small-frequency window, the one-step
characteristic function stays in the principal-branch ball around `1`. -/
private lemma normalizedEntryCharFunSubOneBound
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    {u : ℝ} (hu : |u| ≤ (absoluteMoment Y 3 P)⁻¹) :
    ‖charFun (P.map Y) u - 1‖ ≤ 2 * u ^ (2 : ℕ) / 3 := by
  have hMoment_ge_one : 1 ≤ absoluteMoment Y 3 P :=
    one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_third
  have hMoment_pos : 0 < absoluteMoment Y 3 P := by
    linarith
  have hMomentInv_le_one : (absoluteMoment Y 3 P)⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hMoment_ge_one
  have hu_le_one : |u| ≤ 1 := le_trans hu hMomentInv_le_one
  have hMomentMulU_le_one : absoluteMoment Y 3 P * |u| ≤ 1 := by
    calc
      absoluteMoment Y 3 P * |u| ≤ absoluteMoment Y 3 P * (absoluteMoment Y 3 P)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hu (by linarith)
      _ = 1 := by
        rw [mul_inv_cancel₀ hMoment_pos.ne']
  have hQuadNorm :
      ‖((1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) - 1)‖ = u ^ (2 : ℕ) / 2 := by
    have hu_sq_half_nonneg : 0 ≤ u ^ (2 : ℕ) / 2 := by
      positivity
    calc
      ‖((1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) - 1)‖ = ‖-((u : ℂ) ^ (2 : ℕ) / 2)‖ := by
        congr 1
        ring
      _ = ‖(((u ^ (2 : ℕ) / 2 : ℝ)) : ℂ)‖ := by
        rw [norm_neg]
        norm_num
      _ = u ^ (2 : ℕ) / 2 := by
        simpa [Real.norm_of_nonneg hu_sq_half_nonneg] using
          (Complex.ofRealLI.norm_map (u ^ (2 : ℕ) / 2))
  have hCubicRemainder :=
    normalizedEntryCharFunCubicRemainder P Y hY_meas hY_mean hY_var hY_third u
  have hCubicAbsorb :
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 ≤ u ^ (2 : ℕ) / 6 := by
    -- Proof comment: factor out one `|u|` and use the normalized-window estimate
    -- `absoluteMoment Y 3 P * |u| ≤ 1`.
    calc
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 =
          (absoluteMoment Y 3 P * |u|) * (|u| ^ (2 : ℕ) / 6) := by
            ring
      _ ≤ 1 * (|u| ^ (2 : ℕ) / 6) := by
            exact mul_le_mul_of_nonneg_right hMomentMulU_le_one (by positivity)
      _ = u ^ (2 : ℕ) / 6 := by
            rw [sq_abs]
            ring
  -- Proof comment: split `charFun (P.map Y) u - 1` through the quadratic proxy and absorb the
  -- cubic defect into the quadratic term on the normalized window.
  calc
    ‖charFun (P.map Y) u - 1‖ =
        ‖(charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)) +
            (((1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) - 1))‖ := by
          congr 1
          ring
    _ ≤ ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ +
          ‖((1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 + u ^ (2 : ℕ) / 2 := by
          rw [hQuadNorm]
          exact add_le_add hCubicRemainder le_rfl
    _ ≤ u ^ (2 : ℕ) / 6 + u ^ (2 : ℕ) / 2 := by
          exact add_le_add hCubicAbsorb le_rfl
    _ = 2 * u ^ (2 : ℕ) / 3 := by
          ring

/-- Helper for Theorem 15.51: on the normalized small-frequency window, the logarithm of the
one-step characteristic function differs from the Gaussian exponent `-u² / 2` by a cubic error. -/
private lemma normalizedEntryLogCharFunGaussianApprox
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    {u : ℝ} (hu : |u| ≤ (absoluteMoment Y 3 P)⁻¹) :
    ‖Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2‖ ≤
      absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
  let z : ℂ := charFun (P.map Y) u - 1
  have hMoment_ge_one : 1 ≤ absoluteMoment Y 3 P :=
    one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_third
  have hMoment_pos : 0 < absoluteMoment Y 3 P := by
    linarith
  have hMomentInv_le_one : (absoluteMoment Y 3 P)⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hMoment_ge_one
  have hu_le_one : |u| ≤ 1 := le_trans hu hMomentInv_le_one
  have hu_sq_le_one : u ^ (2 : ℕ) ≤ 1 := by
    nlinarith [sq_abs u, hu_le_one, abs_nonneg u]
  have hz_bound :
      ‖z‖ ≤ 2 * u ^ (2 : ℕ) / 3 := by
    simpa [z] using normalizedEntryCharFunSubOneBound P Y hY_meas hY_mean hY_var hY_third hu
  have hz_bound_abs :
      ‖z‖ ≤ 2 * |u| ^ (2 : ℕ) / 3 := by
    simpa [sq_abs] using hz_bound
  have hz_two_thirds : ‖z‖ ≤ (2 : ℝ) / 3 := by
    nlinarith
  have hz_lt_one : ‖z‖ < 1 := by
    nlinarith
  have hInv_le_three : (1 - ‖z‖)⁻¹ ≤ 3 := by
    have hThird : (1 : ℝ) / 3 ≤ 1 - ‖z‖ := by
      nlinarith
    simpa using one_div_le_one_div_of_le (show 0 < (1 : ℝ) / 3 by norm_num) hThird
  have hOneAdd : 1 + z = charFun (P.map Y) u := by
    dsimp [z]
    ring
  have hDefectRewrite :
      charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2) = z + ((u : ℂ) ^ (2 : ℕ)) / 2 := by
    dsimp [z]
    ring
  have hLogNearOne :
      ‖Complex.log (1 + z) - z‖ ≤ (2 / 3 : ℝ) * absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
    have hFourth_le_moment :
        |u| ^ (4 : ℕ) ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
      calc
        |u| ^ (4 : ℕ) = |u| * |u| ^ (3 : ℕ) := by
          ring
        _ ≤ 1 * |u| ^ (3 : ℕ) := by
              gcongr
        _ ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
              simpa using
                (mul_le_mul_of_nonneg_right hMoment_ge_one
                  (show 0 ≤ |u| ^ (3 : ℕ) by positivity))
    -- Proof comment: the principal-branch logarithm contributes a quadratic error in `z`, and the
    -- normalized window turns this into another cubic `|u|³` term.
    have hz_sq_le :
        ‖z‖ ^ (2 : ℕ) ≤ (2 * |u| ^ (2 : ℕ) / 3) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg z) hz_bound_abs 2
    have hOneSub_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz_lt_one
    have hHalfInv_nonneg : 0 ≤ (1 - ‖z‖)⁻¹ / 2 := by
      have hInv_nonneg : 0 ≤ (1 - ‖z‖)⁻¹ := inv_nonneg.mpr (le_of_lt hOneSub_pos)
      positivity
    have hHalfInv_le : (1 - ‖z‖)⁻¹ / 2 ≤ 3 / 2 := by
      nlinarith
    have hFactor_nonneg : 0 ≤ (2 * |u| ^ (2 : ℕ) / 3) ^ (2 : ℕ) := by
      positivity
    calc
      ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ (2 : ℕ) * (1 - ‖z‖)⁻¹ / 2 :=
        Complex.norm_log_one_add_sub_self_le hz_lt_one
      _ = (‖z‖ ^ (2 : ℕ)) * ((1 - ‖z‖)⁻¹ / 2) := by
            ring
      _ ≤ (2 * |u| ^ (2 : ℕ) / 3) ^ (2 : ℕ) * ((1 - ‖z‖)⁻¹ / 2) := by
            exact mul_le_mul_of_nonneg_right hz_sq_le hHalfInv_nonneg
      _ ≤ (2 * |u| ^ (2 : ℕ) / 3) ^ (2 : ℕ) * (3 / 2) := by
            exact mul_le_mul_of_nonneg_left hHalfInv_le hFactor_nonneg
      _ = (2 / 3 : ℝ) * |u| ^ (4 : ℕ) := by
            ring
      _ ≤ (2 / 3 : ℝ) * absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
            have hTwoThird_nonneg : 0 ≤ (2 / 3 : ℝ) := by
              norm_num
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left hFourth_le_moment hTwoThird_nonneg)
  have hCubicRemainder :=
    normalizedEntryCharFunCubicRemainder P Y hY_meas hY_mean hY_var hY_third u
  have hSplit :
      Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2 =
        (Complex.log (1 + z) - z) + (charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)) := by
    calc
      Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2 =
          Complex.log (1 + z) + ((u : ℂ) ^ (2 : ℕ)) / 2 := by
            rw [← hOneAdd]
      _ = (Complex.log (1 + z) - z) + (z + ((u : ℂ) ^ (2 : ℕ)) / 2) := by
            ring
      _ = (Complex.log (1 + z) - z) +
            (charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)) := by
            rw [hDefectRewrite]
  -- Proof comment: split the logarithmic defect into the principal-branch Taylor remainder and
  -- the already proved cubic characteristic-function remainder.
  rw [hSplit]
  calc
    ‖(Complex.log (1 + z) - z) + (charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2))‖ ≤
        ‖Complex.log (1 + z) - z‖ +
          ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := norm_add_le _ _
    _ ≤ (2 / 3 : ℝ) * absoluteMoment Y 3 P * |u| ^ (3 : ℕ) +
          absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 := by
            exact add_le_add hLogNearOne hCubicRemainder
    _ ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
          have hMain_nonneg : 0 ≤ absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
            positivity
          nlinarith

/-- Helper for Theorem 15.51: on the normalized small-frequency window, the one-step
characteristic function never vanishes, so the principal logarithm can be exponentiated back
exactly. -/
private lemma normalizedEntryCharFun_ne_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY_meas : AEMeasurable Y P)
    (hY_mean : P[Y] = 0)
    (hY_var : Var[Y; P] = 1)
    (hY_third : Integrable (fun ω ↦ |Y ω| ^ (3 : ℕ)) P)
    {u : ℝ} (hu : |u| ≤ (absoluteMoment Y 3 P)⁻¹) :
    charFun (P.map Y) u ≠ 0 := by
  have hMoment_ge_one : 1 ≤ absoluteMoment Y 3 P :=
    one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_third
  have hMomentInv_le_one : (absoluteMoment Y 3 P)⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hMoment_ge_one
  have hu_le_one : |u| ≤ 1 := le_trans hu hMomentInv_le_one
  have hSubOne :
      ‖charFun (P.map Y) u - 1‖ ≤ 2 * u ^ (2 : ℕ) / 3 := by
    simpa using normalizedEntryCharFunSubOneBound P Y hY_meas hY_mean hY_var hY_third hu
  have hSubOne_lt : ‖charFun (P.map Y) u - 1‖ < 1 := by
    have hUpper : 2 * u ^ (2 : ℕ) / 3 < 1 := by
      nlinarith [sq_abs u, hu_le_one, abs_nonneg u]
    exact lt_of_le_of_lt hSubOne hUpper
  -- Proof comment: a point within distance strictly less than `1` from `1` cannot be the origin.
  intro hzero
  have hNormOne : ‖charFun (P.map Y) u - 1‖ = 1 := by
    simpa [hzero] using (norm_one : ‖(1 : ℂ)‖ = 1)
  linarith

/-- Helper for Theorem 15.51: on the natural Berry--Esseen window, the standardized-sum
characteristic function can be rewritten exactly as `exp (n * log φ_Y(u))` on the principal
branch. -/
private lemma standardizedLawCharFun_eq_exp_log
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
    let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
    charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
      Complex.exp ((n : ℂ) * Complex.log (charFun (P.map Y) u)) := by
  dsimp
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is measurable and the
    -- normalization factor is constant.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
    ⟨hY_mean, hY_var, hY_int, hY_moment⟩
  have hLawRewrite :
      charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
        (charFun (P.map Y) u) ^ (n : ℕ) := by
    -- Proof comment: rewrite the standardized-sum law as the `n`th power of the normalized entry.
    simpa [Y, u] using
      iidSucc_charFun_standardizedPartialSum_eq P X hX_iid hX_mean hX_var n t
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hu_eq : u = t / Real.sqrt (n : ℝ) := by
    simp [u, div_eq_mul_inv, mul_comm]
  have hu_window_raw : |u| ≤ β⁻¹ := by
    calc
      |u| = |t| / Real.sqrt (n : ℝ) := by
        rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ))]
      _ ≤ β⁻¹ := by
        rw [div_le_iff₀ hsqrt_n_pos]
        simpa [β, mul_assoc, mul_left_comm, mul_comm] using ht
  have hu_window : |u| ≤ (absoluteMoment Y 3 P)⁻¹ := by
    simpa [β, Y] using (hY_moment ▸ hu_window_raw)
  have hNonzero :
      charFun (P.map Y) u ≠ 0 :=
    normalizedEntryCharFun_ne_zero P Y hY_meas hY_mean hY_var hY_int hu_window
  -- Proof comment: the normalized one-step characteristic function stays inside the principal
  -- branch, so exponentiating its logarithm recovers the exact `n`th power.
  calc
    charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
      (charFun (P.map Y) u) ^ (n : ℕ) := hLawRewrite
    _ = (Complex.exp (Complex.log (charFun (P.map Y) u))) ^ (n : ℕ) := by
          rw [Complex.exp_log hNonzero]
    _ = Complex.exp ((n : ℂ) * Complex.log (charFun (P.map Y) u)) := by
          symm
          simpa using Complex.exp_nat_mul (Complex.log (charFun (P.map Y) u)) (n := (n : ℕ))

/-- Helper for Theorem 15.51: on the natural Berry--Esseen window, the exponent
`n * log φ_Y(u)` differs from the Gaussian exponent `-t² / 2` by the expected cubic defect
`β |t|³ / √n`. -/
private lemma standardizedLawGaussianExponentDefectBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
    let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
    ‖((n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  dsimp
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is measurable and the
    -- normalization factor is constant.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
    ⟨hY_mean, hY_var, hY_int, hY_moment⟩
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n_pos
  have hσ_ne : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hu_eq : u = t / Real.sqrt (n : ℝ) := by
    simp [u, div_eq_mul_inv, mul_comm]
  have hu_window_raw : |u| ≤ β⁻¹ := by
    calc
      |u| = |t| / Real.sqrt (n : ℝ) := by
        rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ))]
      _ ≤ β⁻¹ := by
        rw [div_le_iff₀ hsqrt_n_pos]
        simpa [β, mul_assoc, mul_left_comm, mul_comm] using ht
  have hu_window : |u| ≤ (absoluteMoment Y 3 P)⁻¹ := by
    simpa [β, Y] using (hY_moment ▸ hu_window_raw)
  have hLog :
      ‖Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2‖ ≤
        absoluteMoment Y 3 P * |u| ^ (3 : ℕ) := by
    simpa using normalizedEntryLogCharFunGaussianApprox P Y hY_meas hY_mean hY_var hY_int hu_window
  have hu_abs_pow :
      |u| ^ (3 : ℕ) = |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ) := by
    rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ)), div_pow]
  have hsqrt_cube :
      Real.sqrt (n : ℝ) ^ (3 : ℕ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ^ (3 : ℕ) =
          Real.sqrt (n : ℝ) ^ (2 : ℕ) * Real.sqrt (n : ℝ) := by ring
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
            rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  -- Proof comment: multiply the cubic logarithmic defect by `n` and simplify the scaling
  -- `u = t / √n` exactly.
  calc
    ‖((n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))‖ =
      (n : ℝ) * ‖Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2‖ := by
        simpa using
          (norm_mul
            (n : ℂ)
            (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))
    _ ≤ (n : ℝ) * (absoluteMoment Y 3 P * |u| ^ (3 : ℕ)) := by
          gcongr
    _ = (n : ℝ) *
          (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) *
            (|t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ))) := by
          rw [hY_moment, hu_abs_pow]
    _ = absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
          rw [hsqrt_cube]
          field_simp [hσ_ne, hsqrt_n_ne]

/-- Helper for Theorem 15.51: if `‖z‖` and `‖w‖` are bounded by `r`, then the `n`th-power map is
Lipschitz with contraction factor `r^(n-1)`. -/
private lemma normPowSubPow_le_mul_geom
    {z w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * r ^ (n - 1) * ‖z - w‖ := by
  cases n with
  | zero =>
      -- Proof comment: the zeroth power is constant, so the defect vanishes exactly.
      simp
  | succ m =>
      have hfactor :
          (z - w) * ∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i) =
            z ^ (m + 1) - w ^ (m + 1) := by
        -- Proof comment: factor the power difference through the geometric sum.
        simpa using (Commute.all z w).mul_geom_sum₂ (m + 1)
      have hterm :
          ∀ i ∈ Finset.range (m + 1), ‖z ^ i * w ^ (m - i)‖ ≤ r ^ m := by
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hzpow : ‖z ^ i‖ ≤ r ^ i := by
          calc
            ‖z ^ i‖ = ‖z‖ ^ i := by simpa using Complex.norm_pow z i
            _ ≤ r ^ i := pow_le_pow_left₀ (norm_nonneg _) hz i
        have hwpow : ‖w ^ (m - i)‖ ≤ r ^ (m - i) := by
          calc
            ‖w ^ (m - i)‖ = ‖w‖ ^ (m - i) := by simpa using Complex.norm_pow w (m - i)
            _ ≤ r ^ (m - i) := pow_le_pow_left₀ (norm_nonneg _) hw (m - i)
        calc
          ‖z ^ i * w ^ (m - i)‖ ≤ ‖z ^ i‖ * ‖w ^ (m - i)‖ := norm_mul_le _ _
          _ ≤ r ^ i * r ^ (m - i) := by
                exact mul_le_mul hzpow hwpow (by positivity) (by positivity)
          _ = r ^ m := by
                rw [← pow_add, Nat.add_sub_of_le hi']
      have hsum :
          ‖∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i)‖ ≤ (m + 1 : ℝ) * r ^ m := by
        calc
          ‖∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i)‖ ≤
              Finset.sum (Finset.range (m + 1)) (fun i ↦ ‖z ^ i * w ^ (m - i)‖) := norm_sum_le _ _
          _ ≤ Finset.sum (Finset.range (m + 1)) (fun _i ↦ r ^ m) := by
                exact Finset.sum_le_sum hterm
          _ = (m + 1 : ℝ) * r ^ m := by
                simp
      have hmain :
          ‖z ^ (m + 1) - w ^ (m + 1)‖ ≤ ‖z - w‖ * ((m + 1 : ℝ) * r ^ m) := by
        calc
          ‖z ^ (m + 1) - w ^ (m + 1)‖ =
              ‖(z - w) * ∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i)‖ := by
                rw [← hfactor]
          _ ≤ ‖z - w‖ * ‖∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i)‖ := by
                simpa [mul_comm] using
                  norm_mul_le (z - w) (∑ i ∈ Finset.range (m + 1), z ^ i * w ^ (m - i))
          _ ≤ ‖z - w‖ * ((m + 1 : ℝ) * r ^ m) := by
                exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
/-- Helper for Theorem 15.51: inside the closed unit disk, taking the `n`th power is
`n`-Lipschitz with respect to the complex norm. -/
private lemma norm_pow_sub_pow_le_nat_mul_norm_sub
    {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ‖z - w‖ := by
  -- Proof comment: specialize the geometric Lipschitz estimate to radius `r = 1`.
  simpa using normPowSubPow_le_mul_geom (r := 1) (z := z) (w := w)
    (show 0 ≤ (1 : ℝ) by positivity) hz hw n

/-- Helper for Theorem 15.51: on the natural Berry--Esseen frequency window
`|t| ≤ √(2 n)`, the characteristic function of the standardized partial-sum law stays within
`O(|t|^3 / √n)` of the `n`th power of its quadratic Gaussian proxy. -/
private lemma standardizedLawCharFunWindowBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (2 * (n : ℝ))) :
    ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is and the scale is constant.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
    ⟨hY_mean, hY_var, hY_int, hY_moment⟩
  have hLawRewrite :
      charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
        (charFun (P.map Y) u) ^ (n : ℕ) := by
    -- Proof comment: rewrite the standardized-sum law as the `n`th power of the normalized entry.
    simpa [Y, u] using
      iidSucc_charFun_standardizedPartialSum_eq P X hX_iid hX_mean hX_var n t
  have hCubic :
      ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ ≤
        absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 := by
    simpa using normalizedEntryCharFunCubicRemainder P Y hY_meas hY_mean hY_var hY_int u
  have hCharFun_norm : ‖charFun (P.map Y) u‖ ≤ 1 := by
    have hMap_univ : (P.map Y) Set.univ = 1 := by
      rw [Measure.map_apply_of_aemeasurable hY_meas MeasurableSet.univ, Set.preimage_univ,
        measure_univ]
    calc
      ‖charFun (P.map Y) u‖ ≤ (P.map Y).real Set.univ := norm_charFun_le (μ := P.map Y) u
      _ = 1 := by simpa [MeasureTheory.Measure.real_def] using congrArg ENNReal.toReal hMap_univ
  have hu_eq : u = t / Real.sqrt (n : ℝ) := by
    simp [u, div_eq_mul_inv, mul_comm]
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hu_abs : |u| ≤ Real.sqrt 2 := by
    have hsqrt_two_n : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) := by
      rw [mul_comm, Real.sqrt_mul (show 0 ≤ (n : ℝ) by positivity), mul_comm]
    calc
      |u| = |t| / Real.sqrt (n : ℝ) := by
        rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ))]
      _ ≤ Real.sqrt 2 := by
        rw [div_le_iff₀ hsqrt_n_pos]
        calc
          |t| ≤ Real.sqrt (2 * (n : ℝ)) := ht
          _ = Real.sqrt 2 * Real.sqrt (n : ℝ) := hsqrt_two_n
  have hu_sq_le_two : u ^ (2 : ℕ) ≤ 2 := by
    have hu_sq :
        |u| ^ (2 : ℕ) ≤ (Real.sqrt 2) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (abs_nonneg u) hu_abs 2
    rw [sq_abs] at hu_sq
    nlinarith [hu_sq, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  have hProxy_nonneg : 0 ≤ 1 - u ^ (2 : ℕ) / 2 := by
    nlinarith
  have hProxy_norm :
      ‖(1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ)‖ ≤ 1 := by
    have hProxy_real :
        (1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) = ((1 - u ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
      norm_num
    rw [hProxy_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hProxy_nonneg]
    nlinarith
  have hPow :
      ‖(charFun (P.map Y) u) ^ (n : ℕ) - (1 - (u : ℂ) ^ (2 : ℕ) / 2) ^ (n : ℕ)‖ ≤
        (n : ℝ) * ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := by
    -- Proof comment: the `n`th-power map is Lipschitz on the closed unit disk.
    simpa using
      norm_pow_sub_pow_le_nat_mul_norm_sub
        (z := charFun (P.map Y) u) (w := 1 - (u : ℂ) ^ (2 : ℕ) / 2)
        hCharFun_norm hProxy_norm (n := (n : ℕ))
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n_pos
  have hσ_ne : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hu_abs_pow :
      |u| ^ (3 : ℕ) = |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ) := by
    rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ)), div_pow]
  have hsqrt_cube :
      Real.sqrt (n : ℝ) ^ (3 : ℕ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ^ (3 : ℕ) =
          Real.sqrt (n : ℝ) ^ (2 : ℕ) * Real.sqrt (n : ℝ) := by ring
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
            rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  -- Proof comment: combine the one-step cubic remainder with the power-map contraction and then
  -- simplify the `u = t / √n` scaling.
  calc
    ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ =
      ‖(charFun (P.map Y) u) ^ (n : ℕ) - (1 - (u : ℂ) ^ (2 : ℕ) / 2) ^ (n : ℕ)‖ := by
        rw [hLawRewrite]
        simp [u]
    _ ≤ (n : ℝ) * ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := hPow
    _ ≤ (n : ℝ) * (absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6) := by
          gcongr
    _ = (n : ℝ) *
          (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) *
            (|t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ)) / 6) := by
          rw [hY_moment, hu_abs_pow]
    _ = absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
          rw [hsqrt_cube]
          field_simp [hσ_ne, hsqrt_n_ne]

/-- Helper for Theorem 15.51: the already proved cubic window estimate controls the smoothing
quotient integrand after division by `t`, but only with a polynomial `|t|²` majorant. -/
private lemma standardizedLawCharFunQuotientWindowBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (2 * (n : ℝ))) :
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)) / t‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
  by_cases ht0 : t = 0
  · -- Proof comment: the quotient has a removable singularity, and both sides vanish at `t = 0`.
    simp [ht0]
  have hWindow :=
    standardizedLawCharFunWindowBound P X hX_iid hX_mean hX_var hX_third n ht
  have htabs_pos : 0 < |t| := abs_pos.mpr ht0
  have hσ_ne : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n_pos
  -- Proof comment: divide the already proved undivided estimate by the positive factor `|t|`.
  calc
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)) / t‖ =
      ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ / |t| := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤
        (absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))) / |t| := by
          exact div_le_div_of_nonneg_right hWindow (le_of_lt htabs_pos)
    _ = absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
          field_simp [hσ_ne, hsqrt_n_ne, abs_ne_zero.mpr ht0]

/-- Helper for Theorem 15.51: on the genuine small-frequency Berry--Esseen window determined by
the normalized third moment, the smoothing quotient carries the subGaussian damping already proved
for the normalized one-step characteristic function. -/
private lemma standardizedLawCharFunQuotientSmallWindowDampedBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)) / t‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  by_cases ht0 : t = 0
  · -- Proof comment: the quotient has a removable singularity, and both sides vanish at `t = 0`.
    simp [ht0]
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is and the scale is fixed.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
    ⟨hY_mean, hY_var, hY_int, hY_moment⟩
  have hLawRewrite :
      charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t =
        (charFun (P.map Y) u) ^ (n : ℕ) := by
    -- Proof comment: rewrite the standardized-sum law as the `n`th power of the normalized entry.
    simpa [Y, u] using
      iidSucc_charFun_standardizedPartialSum_eq P X hX_iid hX_mean hX_var n t
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_n_pos
  have hσ_ne : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hu_eq : u = t / Real.sqrt (n : ℝ) := by
    simp [u, div_eq_mul_inv, mul_comm]
  have hu_window_raw : |u| ≤ β⁻¹ := by
    calc
      |u| = |t| / Real.sqrt (n : ℝ) := by
        rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ))]
      _ ≤ β⁻¹ := by
        rw [div_le_iff₀ hsqrt_n_pos]
        simpa [β, mul_assoc, mul_left_comm, mul_comm] using ht
  have hu_window : |u| ≤ (absoluteMoment Y 3 P)⁻¹ := by
    simpa [β, Y] using (hY_moment ▸ hu_window_raw)
  have hMoment_ge_one : 1 ≤ absoluteMoment Y 3 P :=
    one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_int
  have hMomentInv_le_one : (absoluteMoment Y 3 P)⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hMoment_ge_one
  have hu_le_one : |u| ≤ 1 := le_trans hu_window hMomentInv_le_one
  have hCubic :
      ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ ≤
        absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6 := by
    simpa using normalizedEntryCharFunCubicRemainder P Y hY_meas hY_mean hY_var hY_int u
  have hCharFun_damp : ‖charFun (P.map Y) u‖ ≤ Real.exp (-(u ^ (2 : ℕ)) / 3) := by
    exact normalizedEntryCharFunSubGaussian P Y hY_meas hY_mean hY_var hY_int hu_window
  have hProxy_nonneg : 0 ≤ 1 - u ^ (2 : ℕ) / 2 := by
    nlinarith [sq_abs u, hu_le_one, abs_nonneg u]
  have hProxy_damp :
      ‖(1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ)‖ ≤ Real.exp (-(u ^ (2 : ℕ)) / 3) := by
    have hProxy_real :
        (1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ) = ((1 - u ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
      norm_num
    calc
      ‖(1 - (u : ℂ) ^ (2 : ℕ) / 2 : ℂ)‖ = 1 - u ^ (2 : ℕ) / 2 := by
        rw [hProxy_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hProxy_nonneg]
      _ ≤ 1 - u ^ (2 : ℕ) / 3 := by
        nlinarith [sq_nonneg u]
      _ ≤ Real.exp (-(u ^ (2 : ℕ)) / 3) := by
        nlinarith [Real.add_one_le_exp (-(u ^ (2 : ℕ)) / 3)]
  have hPow :
      ‖(charFun (P.map Y) u) ^ (n : ℕ) - (1 - (u : ℂ) ^ (2 : ℕ) / 2) ^ (n : ℕ)‖ ≤
        (n : ℝ) * Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) *
          ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := by
    -- Proof comment: the `n`th-power map contracts with the common subGaussian radius.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      normPowSubPow_le_mul_geom
        (z := charFun (P.map Y) u)
        (w := 1 - (u : ℂ) ^ (2 : ℕ) / 2)
        (r := Real.exp (-(u ^ (2 : ℕ)) / 3))
        (by positivity)
        hCharFun_damp hProxy_damp (n := (n : ℕ))
  have hu_abs_pow :
      |u| ^ (3 : ℕ) = |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ) := by
    rw [hu_eq, abs_div, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (n : ℝ)), div_pow]
  have hsqrt_cube :
      Real.sqrt (n : ℝ) ^ (3 : ℕ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) ^ (3 : ℕ) =
          Real.sqrt (n : ℝ) ^ (2 : ℕ) * Real.sqrt (n : ℝ) := by ring
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by
            rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  have hUndivided :
      ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) *
            Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
    -- Proof comment: combine the one-step cubic defect with the damped power-map contraction and
    -- then simplify the `u = t / √n` scaling.
    calc
      ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ =
        ‖(charFun (P.map Y) u) ^ (n : ℕ) - (1 - (u : ℂ) ^ (2 : ℕ) / 2) ^ (n : ℕ)‖ := by
          rw [hLawRewrite]
          simp [u]
      _ ≤ (n : ℝ) * Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) *
            ‖charFun (P.map Y) u - (1 - (u : ℂ) ^ (2 : ℕ) / 2)‖ := hPow
      _ ≤ (n : ℝ) * Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) *
            (absoluteMoment Y 3 P * |u| ^ (3 : ℕ) / 6) := by
            gcongr
      _ =
          (n : ℝ) * Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) *
            (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) *
              (|t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ^ (3 : ℕ)) / 6) := by
            rw [hY_moment, hu_abs_pow]
      _ = absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) *
            Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
            rw [hsqrt_cube]
            field_simp [hσ_ne, hsqrt_n_ne]
  have htabs_pos : 0 < |t| := abs_pos.mpr ht0
  -- Proof comment: divide the damped undivided estimate by the positive factor `|t|`.
  calc
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)) / t‖ =
      ‖charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
          (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)‖ / |t| := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤
        (absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) *
            Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))) / |t| := by
          exact div_le_div_of_nonneg_right hUndivided (le_of_lt htabs_pos)
    _ = absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-(u ^ (2 : ℕ)) / 3) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
          field_simp [hσ_ne, hsqrt_n_ne, abs_ne_zero.mpr ht0]
    _ = absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
          have hExpArg :
              -(u ^ (2 : ℕ)) / 3 = -((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3) := by
            rw [show u ^ (2 : ℕ) = (((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) by simp [u]]
            ring
          rw [hExpArg]

/-- Helper for Theorem 15.51: every centered interval of radius `a` under the standard Gaussian
has mass at most the interval length times the peak of the Gaussian density. -/
private lemma gaussianIntervalMeasure_le_peak
    (x a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 1).real (Set.Icc (x - a) (x + a)) ≤
      2 * a / Real.sqrt (2 * Real.pi) := by
  have hmeasure :
      (gaussianReal 0 1).real (Set.Icc (x - a) (x + a)) =
        ∫ y in Set.Icc (x - a) (x + a),
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) y := by
    -- Proof comment: rewrite the Gaussian interval mass using its explicit density.
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.gaussianReal_apply_eq_integral
      (0 : ℝ) (v := (1 : NNReal)) one_ne_zero (Set.Icc (x - a) (x + a))]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦
      ProbabilityTheory.gaussianPDFReal_nonneg (0 : ℝ) (1 : NNReal) y)]
  have hbound :
      ∫ y in Set.Icc (x - a) (x + a),
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) y ≤
        ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hIcc_ne_top : volume (Set.Icc (x - a) (x + a)) ≠ ⊤ := by
      rw [Real.volume_Icc]
      simp
    -- Proof comment: dominate the density pointwise by the standard Gaussian peak.
    refine MeasureTheory.setIntegral_mono_on
      (ProbabilityTheory.integrable_gaussianPDFReal (0 : ℝ) (1 : NNReal)).integrableOn
      (MeasureTheory.integrableOn_const
        (s := Set.Icc (x - a) (x + a))
        (μ := volume)
        (C := (Real.sqrt (2 * Real.pi))⁻¹)
        (hs := hIcc_ne_top))
      measurableSet_Icc ?_
    intro y hy
    simpa using gaussianPDFReal_le_peak (hε := one_ne_zero) y 0
  calc
    (gaussianReal 0 1).real (Set.Icc (x - a) (x + a))
        = ∫ y in Set.Icc (x - a) (x + a),
            ProbabilityTheory.gaussianPDFReal (0 : ℝ) (1 : NNReal) y := hmeasure
    _ ≤ ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := hbound
    _ = ((x + a) - (x - a)) * (Real.sqrt (2 * Real.pi))⁻¹ := by
          -- Proof comment: integrating a constant over the interval contributes its length.
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le]
          · rw [smul_eq_mul]
          · linarith
    _ = 2 * a / Real.sqrt (2 * Real.pi) := by
          ring_nf
/-- Helper for Theorem 15.51: on the natural Berry--Esseen smoothing scale `a = 1 / T`, the
standard Gaussian interval error is `O(T⁻¹)`. -/
private lemma gaussianIntervalMeasure_le_invCutoff
    (x T : ℝ) (hT : 0 < T) :
    (gaussianReal 0 1).real (Set.Icc (x - T⁻¹) (x + T⁻¹)) ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  -- Proof comment: specialize the radius bound to `a = T⁻¹` and normalize the scalar factors.
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    gaussianIntervalMeasure_le_peak x T⁻¹ (by positivity : 0 ≤ T⁻¹)
/-- Helper for Theorem 15.51: the standard Gaussian cdf can change by at most `O(T⁻¹)` across an
interval of radius `1 / T`. -/
private lemma gaussianCdfWindow_le_invCutoff
    (x T : ℝ) (hT : 0 < T) :
    cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹) ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hIoc :
      (gaussianReal 0 1) (Set.Ioc (x - T⁻¹) (x + T⁻¹)) =
        ENNReal.ofReal
          (cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹)) := by
    -- Proof comment: the cdf induces the Gaussian law, so interval masses are cdf increments.
    simpa [ProbabilityTheory.measure_cdf (μ := gaussianReal 0 1)] using
      (ProbabilityTheory.cdf (gaussianReal 0 1)).measure_Ioc (x - T⁻¹) (x + T⁻¹)
  have hdiff_nonneg :
      0 ≤ cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹) := by
    -- Proof comment: cdfs are monotone, and the right endpoint is larger than the left endpoint.
    refine sub_nonneg.mpr ?_
    exact ProbabilityTheory.monotone_cdf (μ := gaussianReal 0 1) (by
      have hTinv_pos : 0 < T⁻¹ := by positivity
      linarith)
  have hIoc_le :
      ENNReal.ofReal
          (cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹)) ≤
        (gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
    -- Proof comment: the half-open window is contained in the closed interval with the same endpoints.
    have hsubset : Set.Ioc (x - T⁻¹) (x + T⁻¹) ⊆ Set.Icc (x - T⁻¹) (x + T⁻¹) := by
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2⟩
    simpa [hIoc] using
      (measure_mono (μ := gaussianReal 0 1) hsubset)
  have hreal_le :
      cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹) ≤
        ((gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := by
    -- Proof comment: pass back from `ENNReal` to the real-valued interval mass.
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hIoc_le
  calc
    cdf (gaussianReal 0 1) (x + T⁻¹) - cdf (gaussianReal 0 1) (x - T⁻¹) ≤
        ((gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := hreal_le
    _ = (gaussianReal 0 1).real (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
          rw [MeasureTheory.Measure.real_def]
    _ ≤ (2 / Real.sqrt (2 * Real.pi)) / T := gaussianIntervalMeasure_le_invCutoff x T hT
/-- Helper for Theorem 15.51: on `[0, 1 / 2]`, the logarithmic remainder
`log (1 - x)⁻¹ - x` is already quadratic. -/
private lemma logInvOneSub_sub_self_le_sq
    {x : ℝ} (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    Real.log ((1 - x)⁻¹) - x ≤ x ^ (2 : ℕ) := by
  have hbase_pos : 0 < 1 - x := by
    linarith
  have hx_abs : |-x| ≤ 1 / 2 := by
    simpa [abs_of_nonneg hx_nonneg] using hx_half
  have hcomplex :=
    Complex.norm_log_one_add_sub_self_le (z := ((-x : ℝ) : ℂ))
      (by
        have hx_lt_one : |-x| < 1 := lt_of_le_of_lt hx_abs (by norm_num)
        simpa [Complex.norm_real, Real.norm_eq_abs] using hx_lt_one)
  have hlog :
      Complex.log (1 + ((-x : ℝ) : ℂ)) = ((Real.log (1 - x) : ℝ) : ℂ) := by
    rw [show (1 + ((-x : ℝ) : ℂ) : ℂ) = ((1 - x : ℝ) : ℂ) by
      simp [sub_eq_add_neg]]
    exact (Complex.ofReal_log (show 0 ≤ 1 - x by linarith)).symm
  have hnorm :
      ‖((Real.log (1 - x) : ℝ) : ℂ) + ((x : ℝ) : ℂ)‖ ≤
        ‖((-x : ℝ) : ℂ)‖ ^ (2 : ℕ) * (1 - ‖((-x : ℝ) : ℂ)‖)⁻¹ / 2 := by
    rw [← hlog]
    simpa using hcomplex
  have haux : |Real.log (1 - x) + x| ≤ x ^ (2 : ℕ) * (1 - x)⁻¹ / 2 := by
    -- Proof comment: rewrite the complex bound back on the real line.
    rw [← show ‖((Real.log (1 - x) + x : ℝ) : ℂ)‖ = |Real.log (1 - x) + x| by
      simpa [Real.norm_eq_abs] using (Complex.norm_real (Real.log (1 - x) + x))]
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx_nonneg] using hnorm
  have hinv : (1 - x)⁻¹ / 2 ≤ (1 : ℝ) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - x := by
      linarith
    have hinv_le_two : (1 - x)⁻¹ ≤ 2 := by
      simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num) hhalf
    exact (div_le_one (by norm_num : (0 : ℝ) < 2)).2 hinv_le_two
  have hlog_eq : Real.log ((1 - x)⁻¹) - x = -(Real.log (1 - x) + x) := by
    rw [Real.log_inv]
    ring
  rw [hlog_eq]
  calc
    -(Real.log (1 - x) + x) ≤ |Real.log (1 - x) + x| := neg_le_abs _
    _ ≤ x ^ (2 : ℕ) * (1 - x)⁻¹ / 2 := haux
    _ = x ^ (2 : ℕ) * ((1 - x)⁻¹ / 2) := by ring
    _ ≤ x ^ (2 : ℕ) * 1 := by
          exact mul_le_mul_of_nonneg_left hinv (show 0 ≤ x ^ (2 : ℕ) by positivity)
    _ = x ^ (2 : ℕ) := by ring

/-- Helper for Theorem 15.51: on `[0, 1 / 2]`, the quadratic proxy never exceeds the matching
Gaussian exponential. -/
private lemma oneSubPow_le_expNegMul
    (n : ℕ+) {x : ℝ} (hx_half : x ≤ 1 / 2) :
    (1 - x) ^ (n : ℕ) ≤ Real.exp (-(n : ℝ) * x) := by
  have hbase_nonneg : 0 ≤ 1 - x := by
    linarith
  have hbase : 1 - x ≤ Real.exp (-x) := by
    simpa using Real.one_sub_le_exp_neg x
  calc
    (1 - x) ^ (n : ℕ) ≤ (Real.exp (-x)) ^ (n : ℕ) := by
          exact pow_le_pow_left₀ hbase_nonneg hbase (n : ℕ)
    _ = Real.exp (-(n : ℝ) * x) := by
          rw [← Real.exp_nat_mul]
          ring

/-- Helper for Theorem 15.51: on `[0, 1 / 2]`, the quadratic proxy differs from the matching
Gaussian exponential by at most `n * x²` times the Gaussian factor. -/
private lemma expNegMul_sub_oneSubPow_le_weighted
    (n : ℕ+) {x : ℝ} (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) ≤
      (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) := by
  let δ : ℝ := Real.log ((1 - x)⁻¹) - x
  have hbase_pos : 0 < 1 - x := by
    linarith
  have hδ_nonneg : 0 ≤ δ := by
    have hlog : Real.log (1 - x) ≤ -x := by
      exact (Real.log_le_iff_le_exp hbase_pos).2 <| by
        simpa using Real.one_sub_le_exp_neg x
    dsimp [δ]
    rw [Real.log_inv]
    linarith
  have hδ_le : δ ≤ x ^ (2 : ℕ) := by
    simpa [δ] using logInvOneSub_sub_self_le_sq hx_nonneg hx_half
  have hproxy_exp :
      (1 - x) ^ (n : ℕ) =
        Real.exp (-(n : ℝ) * x) * Real.exp (-((n : ℝ) * δ)) := by
    have hδ_eq : Real.log (1 - x) = -(x + δ) := by
      dsimp [δ]
      rw [Real.log_inv]
      ring
    calc
      (1 - x) ^ (n : ℕ) = Real.exp ((n : ℝ) * Real.log (1 - x)) := by
            symm
            rw [show Real.exp ((n : ℝ) * Real.log (1 - x)) =
                Real.exp (Real.log (1 - x)) ^ (n : ℕ) by
                  simpa [mul_comm] using
                    (Real.exp_nat_mul (Real.log (1 - x)) (n := (n : ℕ)))]
            rw [Real.exp_log hbase_pos]
      _ = Real.exp (-(n : ℝ) * x + -((n : ℝ) * δ)) := by
            congr 1
            rw [hδ_eq]
            ring
      _ = Real.exp (-(n : ℝ) * x) * Real.exp (-((n : ℝ) * δ)) := by
            rw [Real.exp_add]
  have hOneSubExp : 1 - Real.exp (-((n : ℝ) * δ)) ≤ (n : ℝ) * δ := by
    have hbase : 1 - ((n : ℝ) * δ) ≤ Real.exp (-((n : ℝ) * δ)) := by
      simpa using Real.one_sub_le_exp_neg ((n : ℝ) * δ)
    nlinarith
  calc
    Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) =
        Real.exp (-(n : ℝ) * x) * (1 - Real.exp (-((n : ℝ) * δ))) := by
          rw [hproxy_exp]
          ring
    _ ≤ Real.exp (-(n : ℝ) * x) * ((n : ℝ) * δ) := by
          exact mul_le_mul_of_nonneg_left hOneSubExp (by positivity)
    _ ≤ Real.exp (-(n : ℝ) * x) * ((n : ℝ) * x ^ (2 : ℕ)) := by
          gcongr
    _ = (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) := by
          ring
/-- Helper for Theorem 15.51: on the eventual Berry--Esseen cutoff window `|t| ≤ √n`, compare the
quadratic proxy `(1 - t^2 / (2 n))^n` with the standard Gaussian characteristic function. -/
private lemma quadraticProxyPow_sub_gaussianCharFun_le
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (n : ℝ)) :
    ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t‖ ≤
      |t| ^ (4 : ℕ) / (4 * (n : ℝ)) := by
  let x : ℝ := t ^ (2 : ℕ) / (2 * (n : ℝ))
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have ht_sq : t ^ (2 : ℕ) ≤ (n : ℝ) := by
    have habs_sq : |t| ^ (2 : ℕ) ≤ (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    rw [sq_abs, Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)] at habs_sq
    exact habs_sq
  have hx_half : x ≤ 1 / 2 := by
    dsimp [x]
    have hden_pos : 0 < 2 * (n : ℝ) := by positivity
    exact (div_le_iff₀ hden_pos).2 (by nlinarith)
  have hpow_le :
      (1 - x) ^ (n : ℕ) ≤ Real.exp (-(n : ℝ) * x) :=
    oneSubPow_le_expNegMul n hx_half
  have hproxy_real :
      (((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 2 = x := by
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    dsimp [x]
    field_simp [hsqrt_ne, hn_ne]
    rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
    ring
  have hproxy_base :
      (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2) : ℂ) = ((1 - x : ℝ) : ℂ) := by
    have hcomplex :
        ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2 : ℂ) = ((x : ℝ) : ℂ) := by
      exact_mod_cast hproxy_real
    rw [hcomplex]
    simp
  have hgauss :
      charFun (gaussianReal 0 1) t = ((Real.exp (-(t ^ (2 : ℕ) / 2)) : ℝ) : ℂ) := by
    simpa [ProbabilityTheory.charFun_gaussianReal, neg_div]
  have hnorm_eq :
      ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
          charFun (gaussianReal 0 1) t‖ =
        Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) := by
    rw [hproxy_base, hgauss]
    have hexp_arg : -(n : ℝ) * x = -(t ^ (2 : ℕ) / 2) := by
      dsimp [x]
      field_simp [hn_ne]
    rw [show (Real.exp (-(t ^ (2 : ℕ) / 2)) : ℝ) = Real.exp (-(n : ℝ) * x) by
      rw [hexp_arg]]
    rw [show (((1 - x : ℝ) : ℂ) ^ (n : ℕ) - ((Real.exp (-(n : ℝ) * x) : ℝ) : ℂ)) =
        (((1 - x) ^ (n : ℕ) - Real.exp (-(n : ℝ) * x) : ℝ) : ℂ) by simp]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr hpow_le
  have hweighted_real :
      Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) ≤
        (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) :=
    expNegMul_sub_oneSubPow_le_weighted n hx_nonneg hx_half
  have hexp_le_one : Real.exp (-(n : ℝ) * x) ≤ 1 := by
    have hnonneg : 0 ≤ (n : ℝ) * x := by positivity
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hcoeff_le :
      (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) ≤
        (n : ℝ) * x ^ (2 : ℕ) := by
    have hnonneg : 0 ≤ (n : ℝ) * x ^ (2 : ℕ) := by positivity
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hexp_le_one hnonneg)
  have habs_two : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by
    simpa using (sq_abs t)
  have habs_four : |t| ^ (4 : ℕ) = (t ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, habs_two]
  have hcoeff :
      (n : ℝ) * x ^ (2 : ℕ) = |t| ^ (4 : ℕ) / (4 * (n : ℝ)) := by
    dsimp [x]
    rw [habs_four]
    field_simp [hn_ne]
    ring_nf
  -- Proof comment: pass to the real proxy parameter `x = t² / (2n)`, use the positive ordering
  -- between the proxy and the Gaussian exponential, then clear the elementary algebra.
  calc
    ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t‖ = Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) := hnorm_eq
    _ ≤ (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) := hweighted_real
    _ ≤ (n : ℝ) * x ^ (2 : ℕ) := hcoeff_le
    _ = |t| ^ (4 : ℕ) / (4 * (n : ℝ)) := hcoeff
/-- Helper for Theorem 15.51: the current proxy-to-Gaussian comparison also yields a quotient-level
bound after dividing by `t`, again only with a polynomial `|t|³ / n` majorant. -/
private lemma quadraticProxyGaussianQuotientWindowBound
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (n : ℝ)) :
    ‖((1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t) / t‖ ≤
      |t| ^ (3 : ℕ) / (4 * (n : ℝ)) := by
  by_cases ht0 : t = 0
  · -- Proof comment: the quotient has a removable singularity, and the polynomial majorant vanishes.
    simp [ht0]
  have hbase := quadraticProxyPow_sub_gaussianCharFun_le (n := n) (t := t) ht
  have htabs_pos : 0 < |t| := abs_pos.mpr ht0
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  -- Proof comment: divide the undivided comparison by the positive factor `|t|`.
  calc
    ‖((1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t) / t‖ =
      ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
          charFun (gaussianReal 0 1) t‖ / |t| := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (|t| ^ (4 : ℕ) / (4 * (n : ℝ))) / |t| := by
          exact div_le_div_of_nonneg_right hbase (le_of_lt htabs_pos)
    _ = |t| ^ (3 : ℕ) / (4 * (n : ℝ)) := by
          field_simp [abs_ne_zero.mpr ht0, hn_ne]
/-- Helper for Theorem 15.51: the proxy-to-Gaussian comparison keeps the Gaussian damping factor
when written on the raw, undivided characteristic-function surface. -/
private lemma quadraticProxyPow_sub_gaussianCharFun_weighted_le
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (n : ℝ)) :
    ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t‖ ≤
      |t| ^ (4 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
  let x : ℝ := t ^ (2 : ℕ) / (2 * (n : ℝ))
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have ht_sq : t ^ (2 : ℕ) ≤ (n : ℝ) := by
    have habs_sq : |t| ^ (2 : ℕ) ≤ (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (abs_nonneg t) ht 2
    rw [sq_abs, Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)] at habs_sq
    exact habs_sq
  have hx_half : x ≤ 1 / 2 := by
    dsimp [x]
    have hden_pos : 0 < 2 * (n : ℝ) := by positivity
    exact (div_le_iff₀ hden_pos).2 (by nlinarith)
  have hpow_le :
      (1 - x) ^ (n : ℕ) ≤ Real.exp (-(n : ℝ) * x) :=
    oneSubPow_le_expNegMul n hx_half
  have hproxy_real :
      (((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 2 = x := by
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    dsimp [x]
    field_simp [hsqrt_ne, hn_ne]
    rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
    ring
  have hproxy_base :
      (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2) : ℂ) = ((1 - x : ℝ) : ℂ) := by
    have hcomplex :
        ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2 : ℂ) = ((x : ℝ) : ℂ) := by
      exact_mod_cast hproxy_real
    rw [hcomplex]
    simp
  have hgauss :
      charFun (gaussianReal 0 1) t = ((Real.exp (-(t ^ (2 : ℕ) / 2)) : ℝ) : ℂ) := by
    simpa [ProbabilityTheory.charFun_gaussianReal, neg_div]
  have hnorm_eq :
      ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
          charFun (gaussianReal 0 1) t‖ =
        Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) := by
    rw [hproxy_base, hgauss]
    have hexp_arg : -(n : ℝ) * x = -(t ^ (2 : ℕ) / 2) := by
      dsimp [x]
      field_simp [hn_ne]
    rw [show (Real.exp (-(t ^ (2 : ℕ) / 2)) : ℝ) = Real.exp (-(n : ℝ) * x) by
      rw [hexp_arg]]
    rw [show (((1 - x : ℝ) : ℂ) ^ (n : ℕ) - ((Real.exp (-(n : ℝ) * x) : ℝ) : ℂ)) =
        (((1 - x) ^ (n : ℕ) - Real.exp (-(n : ℝ) * x) : ℝ) : ℂ) by simp]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr hpow_le
  have hweighted_real :
      Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) ≤
        (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) :=
    expNegMul_sub_oneSubPow_le_weighted n hx_nonneg hx_half
  have hcoeff :
      (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) =
        |t| ^ (4 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
    have hexp_arg : -(n : ℝ) * x = -(t ^ (2 : ℕ) / 2) := by
      dsimp [x]
      field_simp [hn_ne]
    rw [hexp_arg]
    dsimp [x]
    have habs_two : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by
      simpa using (sq_abs t)
    have habs_four : |t| ^ (4 : ℕ) = (t ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, habs_two]
    rw [habs_four]
    field_simp [hn_ne]
    ring_nf
  -- Proof comment: rewrite both terms on the real surface `x = t² / (2n)` and apply the sharp
  -- logarithmic remainder bound to control the proxy defect with the Gaussian damping factor.
  calc
    ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t‖ = Real.exp (-(n : ℝ) * x) - (1 - x) ^ (n : ℕ) := hnorm_eq
    _ ≤ (n : ℝ) * x ^ (2 : ℕ) * Real.exp (-(n : ℝ) * x) := hweighted_real
    _ = |t| ^ (4 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := hcoeff
/-- Helper for Theorem 15.51: after dividing by `t`, the proxy-to-Gaussian comparison still
retains the Gaussian exponential damping. -/
private lemma quadraticProxyGaussianQuotientWeightedBound
    (n : ℕ+) {t : ℝ} (ht : |t| ≤ Real.sqrt (n : ℝ)) :
    ‖((1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
        charFun (gaussianReal 0 1) t) / t‖ ≤
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
  by_cases ht0 : t = 0
  · -- Proof comment: the quotient has a removable singularity, and the weighted majorant vanishes.
    simp [ht0]
  have hweighted := quadraticProxyPow_sub_gaussianCharFun_weighted_le (n := n) (t := t) ht
  have htabs_pos : 0 < |t| := abs_pos.mpr ht0
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  -- Proof comment: divide the weighted undivided comparison by the positive factor `|t|`.
  calc
    ‖((1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
          charFun (gaussianReal 0 1) t) / t‖ =
      ‖(1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ) -
          charFun (gaussianReal 0 1) t‖ / |t| := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤
        (|t| ^ (4 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))) / |t| := by
          exact div_le_div_of_nonneg_right hweighted (le_of_lt htabs_pos)
    _ = |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
          field_simp [abs_ne_zero.mpr ht0, hn_ne]
/-- Helper for Theorem 15.51: on the natural Berry--Esseen cutoff window, the quotient integrand
splits into the already-controlled law-to-proxy term and the weighted proxy-to-Gaussian term. -/
private lemma standardizedLawGaussianQuotientWindowSplitBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        charFun (gaussianReal 0 1) t) / t‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
  -- Route correction: the old proxy/window route is now used only for the final triangle split.
  -- The law-to-proxy and proxy-to-Gaussian estimates are consumed as separate black boxes here.
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let q : ℂ := (1 - ((((Real.sqrt (n : ℝ))⁻¹ * t : ℂ) ^ (2 : ℕ)) / 2)) ^ (n : ℕ)
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is and the scale is constant.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  have hβ_ge_one : 1 ≤ β := by
    rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
      ⟨hY_mean, hY_var, hY_int, hY_moment⟩
    calc
      1 ≤ absoluteMoment Y 3 P :=
        one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_int
      _ = β := by simpa [β, Y] using hY_moment
  have hβ_inv_le_one : β⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hβ_ge_one
  have ht_proxy : |t| ≤ Real.sqrt (n : ℝ) := by
    calc
      |t| ≤ Real.sqrt (n : ℝ) * β⁻¹ := by
        simpa [β] using ht
      _ ≤ Real.sqrt (n : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hβ_inv_le_one (by positivity)
      _ = Real.sqrt (n : ℝ) := by ring
  have hLaw :
      ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) / t‖ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) := by
    simpa [β, q] using
      standardizedLawCharFunQuotientSmallWindowDampedBound
        P X hX_iid hX_mean hX_var hX_third n ht
  have hProxy :
      ‖(q - charFun (gaussianReal 0 1) t) / t‖ ≤
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
    simpa [q] using quadraticProxyGaussianQuotientWeightedBound (n := n) (t := t) ht_proxy
  have hSplit :
      ((charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
            charFun (gaussianReal 0 1) t) /
          t : ℂ) =
        (charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) / t +
          (q - charFun (gaussianReal 0 1) t) / t := by
    -- Proof comment: insert the quadratic proxy and distribute the common division by `t`.
    calc
      ((charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
              charFun (gaussianReal 0 1) t) /
            t : ℂ) =
          (((charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) +
                (q - charFun (gaussianReal 0 1) t)) /
              t : ℂ) := by
            congr 1
            ring
      _ =
          (charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) / t +
            (q - charFun (gaussianReal 0 1) t) / t := by
            rw [add_div]
  rw [hSplit]
  -- Proof comment: the norm of the total quotient is bounded by the sum of the two established
  -- pointwise majorants.
  calc
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) / t +
        (q - charFun (gaussianReal 0 1) t) / t‖ ≤
      ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t - q) / t‖ +
        ‖(q - charFun (gaussianReal 0 1) t) / t‖ := norm_add_le _ _
    _ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
          exact add_le_add hLaw hProxy
/-- Helper for Theorem 15.51: the normalized Berry--Esseen scale
`absoluteMoment (X 1) 3 P / (√Var[X 1; P])^3` is at least `1`. -/
private lemma berryEsseenThirdMomentScale_ge_one
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P) :
    1 ≤ absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  have hY_meas : AEMeasurable Y P := by
    -- Proof comment: the normalized entry is measurable because `X 1` is and the scale is constant.
    simpa [Y] using
      ((hX_iid.identDistrib 0 0).aemeasurable_fst.div_const (Real.sqrt (Var[X 1; P])))
  rcases normalizedEntryMomentFacts P X hX_mean hX_var hX_third with
    ⟨hY_mean, hY_var, hY_int, hY_moment⟩
  calc
    1 ≤ absoluteMoment Y 3 P :=
      one_le_absoluteMoment_three_of_variance_one P Y hY_meas hY_mean hY_var hY_int
    _ = absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := hY_moment
/-- Helper for Theorem 15.51: the Gaussian cutoff error `O(T⁻¹)` is already bounded by the
normalized third-moment scale once `T = √n`. -/
private lemma berryEsseenGaussianCutoffBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    (2 / Real.sqrt (2 * Real.pi)) / Real.sqrt (n : ℝ) ≤
      (2 / Real.sqrt (2 * Real.pi)) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ : 1 ≤ β := berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hconst_nonneg : 0 ≤ (2 / Real.sqrt (2 * Real.pi)) / Real.sqrt (n : ℝ) := by
    positivity
  -- Proof comment: once the normalized third-moment scale is at least `1`, the cutoff term is
  -- dominated by multiplying the same prefactor by `β`.
  have hmul := mul_le_mul_of_nonneg_left hβ hconst_nonneg
  simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
/-- Helper for Theorem 15.51: the natural Berry--Esseen cutoff
`Tn = √n * (absoluteMoment (X 1) 3 P / (√Var[X 1; P])^3)⁻¹` rewrites the Gaussian window term
exactly into the normalized third-moment scale. -/
private lemma berryEsseenCutoffAtNaturalWindow
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    (2 / Real.sqrt (2 * Real.pi)) / Tn =
      (2 / Real.sqrt (2 * Real.pi)) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ : 1 ≤ β := berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  -- Proof comment: substitute the natural cutoff `Tn = √n / β` and clear denominators.
  field_simp [β, hβ_pos.ne', hsqrt_pos.ne']
/-- Helper for Theorem 15.51: if `0 ≤ T`, then every point of the unordered window `Ι (-T) T`
already lies in the closed symmetric interval `Set.Icc (-T) T`. -/
private lemma memIcc_of_memSymmetricuIoc
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Set.uIoc (-T) T) :
    t ∈ Set.Icc (-T) T := by
  -- Proof comment: on a nonnegative symmetric window, `Ι (-T) T` is just `Ioc (-T) T`.
  rw [Set.uIoc_of_le (by linarith)] at ht
  exact Set.Ioc_subset_Icc_self ht
/-- Helper for Theorem 15.51: on the natural cutoff interval, the quotient integrand is already
dominated by the split law/proxy and proxy/Gaussian majorants proved pointwise above. -/
private lemma standardizedLawGaussianQuotientIntegral_le_splitMajorant
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let Tn : ℝ :=
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹
    ∫ t in -Tn..Tn,
        ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
            charFun (gaussianReal 0 1) t) / t‖ ≤
      ∫ t in -Tn..Tn,
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
  let Tn : ℝ :=
    Real.sqrt (n : ℝ) *
      (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹
  let f : ℝ → ℝ := fun t ↦
    ‖(charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        charFun (gaussianReal 0 1) t) / t‖
  let g : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ : 1 ≤ β := by
    -- Proof comment: the natural Berry--Esseen scale is already known to be at least `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hTn_nonneg : 0 ≤ Tn := by
    -- Proof comment: the natural cutoff is nonnegative because both factors are nonnegative.
    dsimp [Tn]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hMajorantInt : IntervalIntegrable g volume (-Tn) Tn := by
    -- Proof comment: the explicit split majorant is continuous, hence interval-integrable.
    refine Continuous.intervalIntegrable ?_ (-Tn) Tn
    fun_prop
  have hWindow_le : -Tn ≤ Tn := by
    linarith
  have hQuotientMeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc (-Tn) Tn)) := by
    -- Proof comment: the quotient integrand is measurable because characteristic functions are
    -- continuous and division by the real coordinate is a measurable operation on `ℂ`.
    dsimp [f]
    refine (measurable_norm.comp ?_).aestronglyMeasurable
    refine
      ((MeasureTheory.continuous_charFun
          (μ := P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ)))).measurable.sub
        (MeasureTheory.continuous_charFun (μ := gaussianReal 0 1)).measurable).div
        (Complex.measurable_ofReal.comp measurable_id)
  have hQuotientInt : IntervalIntegrable f volume (-Tn) Tn := by
    -- Proof comment: dominate the quotient surface by the interval-integrable split majorant.
    refine hMajorantInt.mono_fun' hQuotientMeas ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have htIcc : t ∈ Set.Icc (-Tn) Tn := by
      exact memIcc_of_memSymmetricuIoc hTn_nonneg <| by
        simpa [Tn] using ht
    have ht_abs : |t| ≤ Tn := abs_le.mpr htIcc
    simpa [f, g, Tn] using
      standardizedLawGaussianQuotientWindowSplitBound
        P X hX_iid hX_mean hX_var hX_third n ht_abs
  -- Proof comment: apply interval monotonicity on the natural symmetric window.
  simpa [f, g, Tn] using
    (intervalIntegral.integral_mono_on
      (μ := volume) (a := -Tn) (b := Tn) (f := f) (g := g)
      hWindow_le hQuotientInt hMajorantInt
      (fun t ht ↦ by
        have ht_abs : |t| ≤ Tn := abs_le.mpr ht
        simpa [f, g, Tn] using
          standardizedLawGaussianQuotientWindowSplitBound
            P X hX_iid hX_mean hX_var hX_third n ht_abs))

/-- Helper for Theorem 15.51: the split-majorant argument also provides interval-integrability of
the quotient kernel on the natural cutoff window. -/
private lemma standardizedLawGaussianQuotientIntervalIntegrable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let Tn : ℝ :=
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹
    IntervalIntegrable
      (fun t ↦
        ((charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
            charFun (gaussianReal 0 1) t) / t : ℂ))
      volume (-Tn) Tn := by
  let Tn : ℝ :=
    Real.sqrt (n : ℝ) *
      (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹
  let f : ℝ → ℂ := fun t ↦
    (charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ))) t -
        charFun (gaussianReal 0 1) t) / t
  let g : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ : 1 ≤ β := by
    -- Proof comment: the natural Berry--Esseen scale is already known to be at least `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hTn_nonneg : 0 ≤ Tn := by
    -- Proof comment: the natural cutoff is nonnegative because both factors are nonnegative.
    dsimp [Tn]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hMajorantInt : IntervalIntegrable g volume (-Tn) Tn := by
    -- Proof comment: the explicit split majorant is continuous, hence interval-integrable.
    refine Continuous.intervalIntegrable ?_ (-Tn) Tn
    fun_prop
  have hQuotientMeas : AEStronglyMeasurable f (volume.restrict (Set.uIoc (-Tn) Tn)) := by
    -- Proof comment: the quotient kernel is measurable because characteristic functions are
    -- continuous and division by the real coordinate is measurable on `ℂ`.
    dsimp [f]
    refine
      ((MeasureTheory.continuous_charFun
          (μ := P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) (n : ℕ)))).measurable.sub
        (MeasureTheory.continuous_charFun (μ := gaussianReal 0 1)).measurable).div
        (Complex.measurable_ofReal.comp measurable_id) |>.aestronglyMeasurable
  -- Proof comment: dominate the quotient kernel by the interval-integrable split majorant.
  refine hMajorantInt.mono_fun' hQuotientMeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  refine Filter.Eventually.of_forall fun t ht ↦ ?_
  have htIcc : t ∈ Set.Icc (-Tn) Tn := by
    exact memIcc_of_memSymmetricuIoc hTn_nonneg <| by
      simpa [Tn] using ht
  have ht_abs : |t| ≤ Tn := abs_le.mpr htIcc
  simpa [f, g, Tn] using
    standardizedLawGaussianQuotientWindowSplitBound
      P X hX_iid hX_mean hX_var hX_third n ht_abs

/-- Helper for Theorem 15.51: multiplying the natural-window quotient kernel by the Gaussian
damping factor `exp (-t² / 2)` preserves interval integrability. -/
private lemma standardizedLawGaussianDampedQuotientIntervalIntegrable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ :=
      Real.sqrt (n : ℝ) * β⁻¹
    IntervalIntegrable
      (fun t ↦
        (((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
      volume (-Tn) Tn := by
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let Tn : ℝ :=
    Real.sqrt (n : ℝ) * β⁻¹
  have hQuotientInt :
      IntervalIntegrable
        (fun t ↦ ((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ))
        volume (-Tn) Tn := by
    -- Proof comment: the undamped quotient kernel is already integrable on the natural window.
    simpa [μn, β, Tn] using
      standardizedLawGaussianQuotientIntervalIntegrable
        P X hX_iid hX_mean hX_var hX_third n
  have hDampCont :
      Continuous (fun t : ℝ ↦ Complex.exp (-(t ^ (2 : ℕ) / 2))) := by
    -- Proof comment: the Gaussian damping factor is continuous on the whole real line.
    fun_prop
  -- Proof comment: multiply the established quotient kernel by the continuous damping factor on
  -- the compact symmetric window.
  simpa [μn, β, Tn, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hQuotientInt.continuousOn_mul hDampCont.continuousOn

/-- Helper for Theorem 15.51: the Gaussian-damped quotient kernel stays interval-integrable on
the doubled Berry--Esseen window `[-2 * √n / β, 2 * √n / β]`. -/
private lemma standardizedLawGaussianDampedQuotientIntervalIntegrableScaleTwo
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
    IntervalIntegrable
      (fun t ↦
        (((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
      volume (-Tn) Tn := by
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
  let f : ℝ → ℂ := fun t ↦
    (((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale is still at least `1`, so the natural
    -- and doubled windows are both positive.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hT0_pos : 0 < T0 := by
    -- Proof comment: the natural cutoff `T0 = √n / β` is positive because both factors are.
    dsimp [T0]
    exact mul_pos (by positivity) (inv_pos.mpr hβ_pos)
  have hInner :
      IntervalIntegrable f volume (-T0) T0 := by
    -- Proof comment: reuse the already proved damped quotient integrability on the natural
    -- Berry--Esseen window.
    simpa [f, μn, β, T0] using
      standardizedLawGaussianDampedQuotientIntervalIntegrable
        P X hX_iid hX_mean hX_var hX_third n
  have hLeftCont :
      ContinuousOn f (Set.Icc (-(2 * T0)) (-T0)) := by
    -- Proof comment: on the negative outer annulus the denominator never vanishes, so the damped
    -- quotient kernel is continuous there.
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    refine ContinuousAt.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · have ht_le : t ≤ -T0 := ht.2
      exact_mod_cast (show t ≠ 0 by linarith [ht_le, hT0_pos])
  have hRightCont :
      ContinuousOn f (Set.Icc T0 (2 * T0)) := by
    -- Proof comment: the same continuity argument applies on the positive outer annulus.
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    refine ContinuousAt.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · have ht_ge : T0 ≤ t := ht.1
      exact_mod_cast (show t ≠ 0 by linarith [ht_ge, hT0_pos])
  have hLeft :
      IntervalIntegrable f volume (-(2 * T0)) (-T0) := by
    -- Proof comment: continuity on the compact negative annulus gives interval integrability.
    exact hLeftCont.intervalIntegrable_of_Icc (by nlinarith)
  have hRight :
      IntervalIntegrable f volume T0 (2 * T0) := by
    -- Proof comment: continuity on the compact positive annulus gives interval integrability.
    exact hRightCont.intervalIntegrable_of_Icc (by nlinarith)
  -- Proof comment: glue the two outer annuli to the already integrable natural window.
  simpa [f, β, Tn, T0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hLeft.trans (hInner.trans hRight)

/-- Helper for Theorem 15.51: the weighted Gaussian proxy integral on a symmetric interval has an
explicit antiderivative. -/
private lemma proxyGaussianWeightedMajorantIntegral_eq
    (n : ℕ+) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) =
      (1 - (T ^ (2 : ℕ) / 2 + 1) * Real.exp (-(T ^ (2 : ℕ)) / 2)) / (n : ℝ) := by
  let f : ℝ → ℝ := fun t ↦ |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  let F : ℝ → ℝ := fun t ↦
    (1 - (t ^ (2 : ℕ) / 2 + 1) * Real.exp (-(t ^ (2 : ℕ)) / 2)) / (n : ℝ)
  have hIntLeft : IntervalIntegrable f volume (-T) 0 := by
    -- Proof comment: the weighted Gaussian proxy kernel is continuous, hence integrable, on each
    -- compact subinterval.
    refine Continuous.intervalIntegrable ?_ (-T) 0
    continuity
  have hIntRight : IntervalIntegrable f volume 0 T := by
    -- Proof comment: the same continuity argument gives interval integrability on `[0, T]`.
    refine Continuous.intervalIntegrable ?_ 0 T
    continuity
  have hEven : ∫ t in -T..0, f t = ∫ t in 0..T, f t := by
    -- Proof comment: the proxy kernel is even, so the left half-window matches the right one
    -- after the change of variables `t ↦ -t`.
    calc
      ∫ t in -T..0, f t = ∫ t in -T..0, f (-t) := by
        congr with t
        dsimp [f]
        simp [pow_two]
      _ = ∫ t in 0..T, f t := by
        simpa using (intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := 0))
  have hSplit :
      ∫ t in -T..T, f t = 2 * ∫ t in 0..T, f t := by
    -- Proof comment: split the symmetric interval at `0` and then identify the two halves by
    -- evenness.
    have hAdj :
        ∫ t in -T..T, f t = (∫ t in -T..0, f t) + ∫ t in 0..T, f t := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals (f := f) hIntLeft hIntRight).symm
    have hDup :
        (∫ t in -T..0, f t) + ∫ t in 0..T, f t =
          (∫ t in 0..T, f t) + ∫ t in 0..T, f t := by
      simpa using congrArg (fun z : ℝ => z + ∫ t in 0..T, f t) hEven
    calc
      ∫ t in -T..T, f t = (∫ t in -T..0, f t) + ∫ t in 0..T, f t := hAdj
      _ = (∫ t in 0..T, f t) + ∫ t in 0..T, f t := hDup
      _ = 2 * ∫ t in 0..T, f t := by
        nlinarith
  have hScale :
      2 * ∫ t in 0..T, f t =
        ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (2 * (n : ℝ)) := by
    -- Proof comment: on `[0, T]`, the absolute value drops and the factor `2` removes the `4` in
    -- the denominator.
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht_nonneg : 0 ≤ t := ht.1
    dsimp [f]
    rw [abs_of_nonneg ht_nonneg]
    field_simp
    ring
  have hDeriv :
      ∀ x ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt F
          (x ^ (3 : ℕ) * Real.exp (-(x ^ (2 : ℕ)) / 2) / (2 * (n : ℝ)))
          x := by
    intro x hx
    have hPoly :
        HasDerivAt (fun y : ℝ ↦ y ^ (2 : ℕ) / 2 + 1) x x := by
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_pow 2 x).div_const (2 : ℝ)).add_const 1)
    have hExpArg :
        HasDerivAt (fun y : ℝ ↦ -(y ^ (2 : ℕ)) / 2) (-x) x := by
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_pow 2 x).neg).div_const (2 : ℝ))
    have hExp :
        HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ (2 : ℕ)) / 2))
          (-x * Real.exp (-(x ^ (2 : ℕ)) / 2)) x := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.hasDerivAt_exp (-(x ^ (2 : ℕ)) / 2)).comp x hExpArg
    have hProd :
        HasDerivAt
          (fun y : ℝ ↦ (y ^ (2 : ℕ) / 2 + 1) * Real.exp (-(y ^ (2 : ℕ)) / 2))
          (-(x ^ (3 : ℕ)) * Real.exp (-(x ^ (2 : ℕ)) / 2) / 2)
          x := by
      have hRaw := hPoly.mul hExp
      convert hRaw using 1 <;> ring
    have hOneSub :
        HasDerivAt
          (fun y : ℝ ↦ 1 - (y ^ (2 : ℕ) / 2 + 1) * Real.exp (-(y ^ (2 : ℕ)) / 2))
          (x ^ (3 : ℕ) * Real.exp (-(x ^ (2 : ℕ)) / 2) / 2)
          x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub hProd using 1 <;> ring
    simpa [F, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hOneSub.div_const (n : ℝ)
  have hIntPrimitive :
      IntervalIntegrable
        (fun t ↦ t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (2 * (n : ℝ)))
        volume 0 T := by
    -- Proof comment: the differentiated half-window kernel is continuous on the compact interval.
    refine Continuous.intervalIntegrable ?_ 0 T
    continuity
  have hFTC :
      ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (2 * (n : ℝ)) =
        F T - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hIntPrimitive
  calc
    ∫ t in -T..T, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) = ∫ t in -T..T, f t := by
      rfl
    _ = 2 * ∫ t in 0..T, f t := hSplit
    _ = ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (2 * (n : ℝ)) := hScale
    _ = F T - F 0 := hFTC
    _ = (1 - (T ^ (2 : ℕ) / 2 + 1) * Real.exp (-(T ^ (2 : ℕ)) / 2)) / (n : ℝ) := by
      simp [F]

/-- Helper for Theorem 15.51: the two middle proxy bands are dominated by the full symmetric proxy
window, so the exact antiderivative on `[-T0, T0]` also controls their sum. -/
private lemma proxyGaussianMiddleBandIntegral_le_full
    (n : ℕ+) {R T0 : ℝ} (hR_nonneg : 0 ≤ R) (hR_le_T0 : R ≤ T0) :
    let proxy : ℝ → ℝ := fun t ↦
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
    (∫ t in -T0..-R, proxy t) + ∫ t in R..T0, proxy t ≤
      ∫ t in -T0..T0, proxy t := by
  dsimp
  let proxy : ℝ → ℝ := fun t ↦
    |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  have hT0_nonneg : 0 ≤ T0 := le_trans hR_nonneg hR_le_T0
  have hLeftInt : IntervalIntegrable proxy volume (-T0) (-R) := by
    -- Proof comment: the proxy kernel is continuous, so it is integrable on the left middle band.
    refine Continuous.intervalIntegrable ?_ (-T0) (-R)
    continuity
  have hInnerInt : IntervalIntegrable proxy volume (-R) R := by
    -- Proof comment: the same continuity argument gives integrability on the symmetric inner core.
    refine Continuous.intervalIntegrable ?_ (-R) R
    continuity
  have hRightInt : IntervalIntegrable proxy volume R T0 := by
    -- Proof comment: continuity also handles the right middle band.
    refine Continuous.intervalIntegrable ?_ R T0
    continuity
  have hSplitLeft :
      ∫ t in -T0..R, proxy t =
        (∫ t in -T0..-R, proxy t) + ∫ t in -R..R, proxy t := by
    -- Proof comment: first split the left half of the symmetric window at `-R`.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := proxy) hLeftInt hInnerInt).symm
  have hSplitAll :
      ∫ t in -T0..T0, proxy t =
        (∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
    -- Proof comment: then split the remaining right half at `R`.
    calc
      ∫ t in -T0..T0, proxy t =
          (∫ t in -T0..R, proxy t) + ∫ t in R..T0, proxy t := by
            simpa using
              (intervalIntegral.integral_add_adjacent_intervals
                (f := proxy) (hLeftInt.trans hInnerInt) hRightInt).symm
      _ =
          ((∫ t in -T0..-R, proxy t) + ∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
            rw [hSplitLeft]
      _ =
          (∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
            ring
  have hInnerNonneg : 0 ≤ ∫ t in -R..R, proxy t := by
    -- Proof comment: the proxy kernel is nonnegative on the symmetric inner core.
    exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ by positivity)
  calc
    (∫ t in -T0..-R, proxy t) + ∫ t in R..T0, proxy t ≤
        ((∫ t in -T0..-R, proxy t) + (∫ t in R..T0, proxy t)) +
          (∫ t in -R..R, proxy t) := by
          linarith
    _ = ∫ t in -T0..T0, proxy t := by
          rw [hSplitAll]
          ring

/-- Helper for Theorem 15.51: the weighted proxy-to-Gaussian majorant contributes at most `1 / n`
on any symmetric cutoff interval. -/
private lemma proxyGaussianWeightedMajorantIntegral_le_one_div
    (n : ℕ+) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) ≤
      1 / (n : ℝ) := by
  -- Proof comment: use the explicit antiderivative and discard the nonnegative exponential tail.
  rw [proxyGaussianWeightedMajorantIntegral_eq n hT]
  have htail_nonneg :
      0 ≤ (T ^ (2 : ℕ) / 2 + 1) * Real.exp (-(T ^ (2 : ℕ)) / 2) := by
    positivity
  have hn_pos : 0 < (n : ℝ) := by positivity
  exact (div_le_div_iff₀ hn_pos hn_pos).2 (by nlinarith)

/-- Helper for Theorem 15.51: the twice-damped proxy majorant `|t|³ * exp (-t²) / (4n)` also has
an explicit symmetric antiderivative. -/
private lemma proxyGaussianDampedMajorantIntegral_eq
    (n : ℕ+) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ)) =
      (1 - (T ^ (2 : ℕ) + 1) * Real.exp (-(T ^ (2 : ℕ)))) / (4 * (n : ℝ)) := by
  let f : ℝ → ℝ := fun t ↦ |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ))
  let F : ℝ → ℝ := fun t ↦
    (1 - (t ^ (2 : ℕ) + 1) * Real.exp (-(t ^ (2 : ℕ)))) / (4 * (n : ℝ))
  have hIntLeft : IntervalIntegrable f volume (-T) 0 := by
    -- Proof comment: the twice-damped proxy kernel is continuous on each compact half-window.
    refine Continuous.intervalIntegrable ?_ (-T) 0
    continuity
  have hIntRight : IntervalIntegrable f volume 0 T := by
    -- Proof comment: the same continuity argument gives integrability on the right half-window.
    refine Continuous.intervalIntegrable ?_ 0 T
    continuity
  have hEven : ∫ t in -T..0, f t = ∫ t in 0..T, f t := by
    -- Proof comment: the kernel is even, so the left and right half-window integrals coincide.
    calc
      ∫ t in -T..0, f t = ∫ t in -T..0, f (-t) := by
        congr with t
        dsimp [f]
        simp [pow_two]
      _ = ∫ t in 0..T, f t := by
        simpa using (intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := 0))
  have hSplit :
      ∫ t in -T..T, f t = 2 * ∫ t in 0..T, f t := by
    -- Proof comment: split the symmetric interval at `0` and identify the two halves by
    -- evenness.
    have hAdj :
        ∫ t in -T..T, f t = (∫ t in -T..0, f t) + ∫ t in 0..T, f t := by
      simpa using
        (intervalIntegral.integral_add_adjacent_intervals (f := f) hIntLeft hIntRight).symm
    have hDup :
        (∫ t in -T..0, f t) + ∫ t in 0..T, f t =
          (∫ t in 0..T, f t) + ∫ t in 0..T, f t := by
      simpa using congrArg (fun z : ℝ => z + ∫ t in 0..T, f t) hEven
    calc
      ∫ t in -T..T, f t = (∫ t in -T..0, f t) + ∫ t in 0..T, f t := hAdj
      _ = (∫ t in 0..T, f t) + ∫ t in 0..T, f t := hDup
      _ = 2 * ∫ t in 0..T, f t := by
        nlinarith
  have hScale :
      2 * ∫ t in 0..T, f t =
        ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (2 * (n : ℝ)) := by
    -- Proof comment: on `[0, T]`, the absolute value drops and the symmetric doubling removes
    -- the factor `4` in the denominator.
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht_nonneg : 0 ≤ t := ht.1
    dsimp [f]
    rw [abs_of_nonneg ht_nonneg]
    field_simp
    ring
  have hDeriv :
      ∀ x ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt F
          (x ^ (3 : ℕ) * Real.exp (-(x ^ (2 : ℕ))) / (2 * (n : ℝ)))
          x := by
    intro x hx
    have hPoly :
        HasDerivAt (fun y : ℝ ↦ y ^ (2 : ℕ) + 1) (2 * x) x := by
      simpa [pow_two] using ((hasDerivAt_pow 2 x).add_const 1)
    have hExpArg :
        HasDerivAt (fun y : ℝ ↦ -(y ^ (2 : ℕ))) (-2 * x) x := by
      simpa [pow_two] using ((hasDerivAt_pow 2 x).neg)
    have hExp :
        HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ (2 : ℕ))))
          ((-2 * x) * Real.exp (-(x ^ (2 : ℕ)))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_exp (-(x ^ (2 : ℕ)))).comp x hExpArg
    have hProd :
        HasDerivAt
          (fun y : ℝ ↦ (y ^ (2 : ℕ) + 1) * Real.exp (-(y ^ (2 : ℕ))))
          (-(2 * x ^ (3 : ℕ)) * Real.exp (-(x ^ (2 : ℕ)))) x := by
      have hRaw := hPoly.mul hExp
      convert hRaw using 1 <;> ring
    have hOneSub :
        HasDerivAt
          (fun y : ℝ ↦ 1 - (y ^ (2 : ℕ) + 1) * Real.exp (-(y ^ (2 : ℕ))))
          (2 * x ^ (3 : ℕ) * Real.exp (-(x ^ (2 : ℕ)))) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub hProd using 1 <;> ring
    -- Proof comment: divide the primitive by the constant `4 * n` and normalize the scalar
    -- algebra explicitly so the derivative matches the displayed integrand.
    convert hOneSub.div_const (4 * (n : ℝ)) using 1 <;> ring
  have hIntPrimitive :
      IntervalIntegrable
        (fun t ↦ t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (2 * (n : ℝ)))
        volume 0 T := by
    -- Proof comment: the primitive-side integrand is continuous on the compact interval.
    refine Continuous.intervalIntegrable ?_ 0 T
    continuity
  have hFTC :
      ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (2 * (n : ℝ)) =
        F T - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hIntPrimitive
  calc
    ∫ t in -T..T, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ)) =
        ∫ t in -T..T, f t := by
          rfl
    _ = 2 * ∫ t in 0..T, f t := hSplit
    _ = ∫ t in 0..T, t ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (2 * (n : ℝ)) := hScale
    _ = F T - F 0 := hFTC
    _ = (1 - (T ^ (2 : ℕ) + 1) * Real.exp (-(T ^ (2 : ℕ)))) / (4 * (n : ℝ)) := by
          simp [F]

/-- Helper for Theorem 15.51: at the scaled cutoff
`Tn = c * √n * (absoluteMoment (X 1) 3 P / (√Var[X 1; P])^3)⁻¹`, the Gaussian window term picks
up the explicit factor `1 / c`. -/
private lemma berryEsseenCutoffAtScale
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    {c : ℝ} (hc : 0 < c) (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := c * Real.sqrt (n : ℝ) * β⁻¹
    (2 / Real.sqrt (2 * Real.pi)) / Tn =
      ((2 / Real.sqrt (2 * Real.pi)) / c) *
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ : 1 ≤ β := by
    -- Proof comment: reuse the normalized third-moment lower bound before clearing denominators.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  -- Proof comment: substitute `Tn = c * √n / β` and clear the positive scalar factors.
  field_simp [β, hc.ne', hβ_pos.ne', hsqrt_pos.ne']

/-- Helper for Theorem 15.51: at the scaled cutoff
`Tn = c * √n * (absoluteMoment (X 1) 3 P / (√Var[X 1; P])^3)⁻¹`, the proxy/Gaussian majorant
and the Gaussian cutoff term admit an exact closed form. -/
private lemma berryEsseenProxyAndCutoffAtScale_eq
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    {c : ℝ} (hc : 0 < c) (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := c * Real.sqrt (n : ℝ) * β⁻¹
    let proxyMajorant : ℝ → ℝ := fun t ↦
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
    (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, proxyMajorant t) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn =
    (1 / (2 * Real.pi)) *
        ((1 - (Tn ^ (2 : ℕ) / 2 + 1) * Real.exp (-(Tn ^ (2 : ℕ)) / 2)) / (n : ℝ)) +
      ((2 / Real.sqrt (2 * Real.pi)) / c) *
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let Tn : ℝ := c * Real.sqrt (n : ℝ) * β⁻¹
  let proxyMajorant : ℝ → ℝ := fun t ↦
    |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  have hβ : 1 ≤ β := by
    -- Proof comment: the scaled cutoff is nonnegative because the normalized third-moment scale
    -- remains at least `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hTn_nonneg : 0 ≤ Tn := by
    -- Proof comment: the scaled cutoff is a product of nonnegative factors.
    dsimp [Tn]
    exact
      mul_nonneg
        (mul_nonneg (le_of_lt hc) (by positivity))
        (inv_nonneg.mpr (le_of_lt hβ_pos))
  -- Proof comment: rewrite the proxy contribution by the explicit antiderivative and the cutoff
  -- term by the scale-aware scalar identity.
  rw [proxyGaussianWeightedMajorantIntegral_eq n hTn_nonneg]
  rw [berryEsseenCutoffAtScale P X hX_iid hX_mean hX_var hX_third hc n]
/-- Helper for Theorem 15.51: a nondegenerate Gaussian smoothing has cdf equal to the left-ray
integral of its explicit density. -/
private lemma gaussianSmoothedLaw_cdf_eq_setIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {ε : NNReal} (hε : ε ≠ 0) (x : ℝ) :
    cdf (μ ∗ gaussianReal (0 : ℝ) ε) x =
      ∫ y in Set.Iic x, (gaussianSmoothedDensity μ ε y).toReal ∂volume := by
  -- Proof comment: rewrite the smoothed law as a `withDensity` measure and convert the finite
  -- restricted `lintegral` into the displayed set integral of the density's `toReal`.
  rw [ProbabilityTheory.cdf_eq_real]
  rw [gaussianSmoothedLaw_eq_withDensity (μ := μ) hε]
  rw [MeasureTheory.Measure.real_def, withDensity_apply _ measurableSet_Iic]
  have hmeas :
      AEMeasurable (gaussianSmoothedDensity μ ε) (volume.restrict (Set.Iic x)) := by
    exact (measurable_gaussianSmoothedDensity (μ := μ) ε).aemeasurable
  have htop :
      ∀ᵐ y ∂(volume.restrict (Set.Iic x)), gaussianSmoothedDensity μ ε y < ⊤ := by
    exact Filter.Eventually.of_forall fun y ↦ gaussianSmoothedDensity_lt_top (μ := μ) hε y
  simpa using
    (MeasureTheory.integral_toReal (μ := volume.restrict (Set.Iic x)) hmeas htop).symm

/-- Helper for Theorem 15.51: every once-Gaussian-smoothed density is pointwise bounded by the
standard Gaussian peak `1 / √(2π)`. -/
private lemma gaussianSmoothedDensityToReal_le_peak
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (gaussianSmoothedDensity μ 1 x).toReal ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  have hbound :
      gaussianSmoothedDensity μ 1 x ≤
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) := by
    calc
      gaussianSmoothedDensity μ 1 x = ∫⁻ y, gaussianPDF y 1 x ∂μ := rfl
      _ ≤ ∫⁻ y, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) ∂μ := by
            refine lintegral_mono fun y ↦ ?_
            -- Proof comment: dominate the smoothing kernel pointwise by the standard Gaussian
            -- peak before integrating against the probability law.
            simpa using
              (ENNReal.ofReal_le_ofReal
                (gaussianPDFReal_le_peak (hε := one_ne_zero) x y))
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * μ Set.univ := by
            rw [lintegral_const]
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) := by
            simp [measure_univ]
  -- Proof comment: convert the `ENNReal` peak bound to the displayed real-valued density bound.
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-- Helper for Theorem 15.51: the once-Gaussian-smoothed law assigns every centered interval of
radius `a` mass at most its length times the standard Gaussian peak. -/
private lemma gaussianSmoothedIntervalMeasure_le_peak
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x a : ℝ) (ha : 0 ≤ a) :
    (μ ∗ gaussianReal 0 1).real (Set.Icc (x - a) (x + a)) ≤
      2 * a / Real.sqrt (2 * Real.pi) := by
  have hmeasure :
      (μ ∗ gaussianReal 0 1).real (Set.Icc (x - a) (x + a)) =
        ∫ y in Set.Icc (x - a) (x + a), (gaussianSmoothedDensity μ 1 y).toReal ∂volume := by
    -- Proof comment: rewrite the once-smoothed law as `withDensity` and convert the finite
    -- interval mass into the corresponding density integral.
    rw [gaussianSmoothedLaw_eq_withDensity (μ := μ) one_ne_zero]
    rw [MeasureTheory.Measure.real_def, withDensity_apply _ measurableSet_Icc]
    have hmeas :
        AEMeasurable (gaussianSmoothedDensity μ 1) (volume.restrict (Set.Icc (x - a) (x + a))) := by
      exact (measurable_gaussianSmoothedDensity (μ := μ) 1).aemeasurable
    have htop :
        ∀ᵐ y ∂(volume.restrict (Set.Icc (x - a) (x + a))), gaussianSmoothedDensity μ 1 y < ⊤ := by
      exact Filter.Eventually.of_forall fun y ↦ gaussianSmoothedDensity_lt_top (μ := μ) one_ne_zero y
    simpa using
      (MeasureTheory.integral_toReal
        (μ := volume.restrict (Set.Icc (x - a) (x + a))) hmeas htop).symm
  have hIcc_ne_top : volume (Set.Icc (x - a) (x + a)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    simp
  have hbound :
      ∫ y in Set.Icc (x - a) (x + a), (gaussianSmoothedDensity μ 1 y).toReal ∂volume ≤
        ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := by
    -- Proof comment: the smoothed density is uniformly bounded by the standard Gaussian peak on
    -- the whole line, so certainly on the interval window.
    refine MeasureTheory.setIntegral_mono_on
      (integrable_gaussianSmoothedDensityToReal (μ := μ) (hε := one_ne_zero)).integrableOn
      (MeasureTheory.integrableOn_const
        (s := Set.Icc (x - a) (x + a))
        (μ := volume)
        (C := (Real.sqrt (2 * Real.pi))⁻¹)
        (hs := hIcc_ne_top))
      measurableSet_Icc ?_
    intro y hy
    exact gaussianSmoothedDensityToReal_le_peak (μ := μ) y
  calc
    (μ ∗ gaussianReal 0 1).real (Set.Icc (x - a) (x + a)) =
        ∫ y in Set.Icc (x - a) (x + a), (gaussianSmoothedDensity μ 1 y).toReal ∂volume := hmeasure
    _ ≤ ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := hbound
    _ = ((x + a) - (x - a)) * (Real.sqrt (2 * Real.pi))⁻¹ := by
          -- Proof comment: integrating the constant peak bound contributes exactly the interval
          -- length.
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le]
          · rw [smul_eq_mul]
          · linarith
    _ = 2 * a / Real.sqrt (2 * Real.pi) := by
          ring_nf

/-- Helper for Theorem 15.51: once-Gaussian-smoothed cdfs change by at most `O(T⁻¹)` across a
window of radius `1 / T`. -/
private lemma gaussianSmoothedCdfWindow_le_invCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) (hT : 0 < T) :
    cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hIoc :
      (μ ∗ gaussianReal 0 1) (Set.Ioc (x - T⁻¹) (x + T⁻¹)) =
        ENNReal.ofReal
          (cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹)) := by
    -- Proof comment: cdf increments recover the smoothed interval mass on the half-open window.
    simpa [ProbabilityTheory.measure_cdf (μ := μ ∗ gaussianReal 0 1)] using
      (ProbabilityTheory.cdf (μ ∗ gaussianReal 0 1)).measure_Ioc (x - T⁻¹) (x + T⁻¹)
  have hdiff_nonneg :
      0 ≤ cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) := by
    -- Proof comment: the once-smoothed cdf is monotone in the evaluation point.
    refine sub_nonneg.mpr ?_
    exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by
      have hTinv_pos : 0 < T⁻¹ := by positivity
      linarith)
  have hIoc_le :
      ENNReal.ofReal
          (cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹)) ≤
        (μ ∗ gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
    -- Proof comment: enlarge the half-open window to the closed interval with the same endpoints.
    have hsubset : Set.Ioc (x - T⁻¹) (x + T⁻¹) ⊆ Set.Icc (x - T⁻¹) (x + T⁻¹) := by
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2⟩
    simpa [hIoc] using
      (measure_mono (μ := μ ∗ gaussianReal 0 1) hsubset)
  have hreal_le :
      cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) ≤
        ((μ ∗ gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := by
    -- Proof comment: pass the interval-mass comparison back from `ENNReal` to `ℝ`.
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top (μ ∗ gaussianReal 0 1) _)).mp hIoc_le
  calc
    cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) ≤
        ((μ ∗ gaussianReal 0 1) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := hreal_le
    _ = (μ ∗ gaussianReal 0 1).real (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
          rw [MeasureTheory.Measure.real_def]
    _ ≤ (2 / Real.sqrt (2 * Real.pi)) / T := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            gaussianSmoothedIntervalMeasure_le_peak (μ := μ) x T⁻¹ (by positivity : 0 ≤ T⁻¹)
/-- Helper for Theorem 15.51: every variance-`1 + ε` centered Gaussian interval already obeys the
standard peak bound `1 / √(2π)`. -/
private lemma gaussianIntervalMeasure_one_addVariance_le_peak
    (x a : ℝ) (ha : 0 ≤ a) (ε : NNReal) :
    (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)).real (Set.Icc (x - a) (x + a)) ≤
      2 * a / Real.sqrt (2 * Real.pi) := by
  have hε_pos : 0 < (1 : NNReal) + ε := by
    positivity
  have hε_ne : (1 : NNReal) + ε ≠ 0 := ne_of_gt hε_pos
  have hpeak :
      (Real.sqrt (2 * Real.pi * (((1 : NNReal) + ε : NNReal) : ℝ)))⁻¹ ≤
        (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hone : (1 : ℝ) ≤ (((1 : NNReal) + ε : NNReal) : ℝ) := by
      exact_mod_cast (le_add_of_nonneg_right ε.2)
    have hmul :
        2 * Real.pi ≤ 2 * Real.pi * ((((1 : NNReal) + ε : NNReal) : ℝ)) := by
      nlinarith [Real.pi_pos, hone]
    have hsqrt :
        Real.sqrt (2 * Real.pi) ≤
          Real.sqrt (2 * Real.pi * ((((1 : NNReal) + ε : NNReal) : ℝ))) := by
      exact Real.sqrt_le_sqrt hmul
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (2 * Real.pi) by positivity) hsqrt)
  have hmeasure :
      (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)).real (Set.Icc (x - a) (x + a)) =
        ∫ y in Set.Icc (x - a) (x + a),
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) ((1 : NNReal) + ε) y := by
    -- Proof comment: rewrite the widened Gaussian interval mass using its explicit density.
    rw [MeasureTheory.Measure.real_def, ProbabilityTheory.gaussianReal_apply_eq_integral
      (0 : ℝ) (v := (1 : NNReal) + ε) hε_ne (Set.Icc (x - a) (x + a))]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦
      ProbabilityTheory.gaussianPDFReal_nonneg (0 : ℝ) ((1 : NNReal) + ε) y)]
  have hbound :
      ∫ y in Set.Icc (x - a) (x + a),
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) ((1 : NNReal) + ε) y ≤
        ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hIcc_ne_top : volume (Set.Icc (x - a) (x + a)) ≠ ⊤ := by
      rw [Real.volume_Icc]
      simp
    -- Proof comment: the broader Gaussian has no higher peak than the standard Gaussian.
    refine MeasureTheory.setIntegral_mono_on
      (ProbabilityTheory.integrable_gaussianPDFReal (0 : ℝ) ((1 : NNReal) + ε)).integrableOn
      (MeasureTheory.integrableOn_const
        (s := Set.Icc (x - a) (x + a))
        (μ := volume)
        (C := (Real.sqrt (2 * Real.pi))⁻¹)
        (hs := hIcc_ne_top))
      measurableSet_Icc ?_
    intro y hy
    exact
      le_trans
        (gaussianPDFReal_le_peak (hε := hε_ne) y 0)
        hpeak
  calc
    (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)).real (Set.Icc (x - a) (x + a))
        = ∫ y in Set.Icc (x - a) (x + a),
            ProbabilityTheory.gaussianPDFReal (0 : ℝ) ((1 : NNReal) + ε) y := hmeasure
    _ ≤ ∫ y in Set.Icc (x - a) (x + a), (Real.sqrt (2 * Real.pi))⁻¹ := hbound
    _ = ((x + a) - (x - a)) * (Real.sqrt (2 * Real.pi))⁻¹ := by
          -- Proof comment: integrating the uniform peak bound contributes the interval length.
          rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le]
          · rw [smul_eq_mul]
          · linarith
    _ = 2 * a / Real.sqrt (2 * Real.pi) := by
          ring_nf
/-- Helper for Theorem 15.51: smoothing the standard Gaussian by another standard Gaussian gives
the centered variance-`2` Gaussian. -/
private lemma standardGaussian_conv_standardGaussian :
    ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1) = gaussianReal 0 2 := by
  -- Proof comment: convolution adds Gaussian means and variances.
  convert
    (ProbabilityTheory.gaussianReal_conv_gaussianReal
      (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ)) (v₁ := (1 : NNReal)) (v₂ := (1 : NNReal))) using 1
  norm_num
/-- Helper for Theorem 15.51: the Gaussian-damped Fourier kernel on the common difference surface
between `μ` and the standard Gaussian is integrable. -/
private lemma integrable_gaussianSmoothedDifferenceKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun s : ℝ ↦
      (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
        Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
  have hε1 : (1 : NNReal) ≠ 0 := one_ne_zero
  have hμ :
      Integrable (fun s : ℝ ↦
        charFun μ (-2 * Real.pi * s) *
          Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
    -- Proof comment: Exercise 15.1.6 already proves Gaussian damping integrability for every
    -- probability law at smoothing variance `1`.
    simpa using integrable_dampedScaledCharFun (μ := μ) (ε := (1 : NNReal)) (hε := hε1)
  have hGauss :
      Integrable (fun s : ℝ ↦
        charFun (gaussianReal 0 1) (-2 * Real.pi * s) *
          Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
    -- Proof comment: the same damping lemma applies to the Gaussian comparator.
    simpa using
      integrable_dampedScaledCharFun (μ := (gaussianReal 0 1 : Measure ℝ))
        (ε := (1 : NNReal)) (hε := hε1)
  -- Proof comment: the target kernel is the difference of those two damped characteristic-function
  -- surfaces.
  simpa [sub_mul] using hμ.sub hGauss

/-- Helper for Theorem 15.51: on integrable kernels, inverse Fourier transform turns subtraction
into subtraction. -/
private lemma fourierInvSub_ofIntegrable
    {f g : ℝ → ℂ} (_hf : Integrable f) (_hg : Integrable g) :
    𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  -- Proof comment: use the explicit inverse-Fourier integral formula and commute subtraction
  -- through the phase-weighted integral.
  funext w
  let phase : ℝ → ℂ := fun v ↦
    Complex.exp (((2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * Complex.I)
  have hphase_meas : AEStronglyMeasurable phase := by
    fun_prop
  have hphase_bound : ∀ᵐ v ∂volume, ‖phase v‖ ≤ (1 : ℝ) := by
    filter_upwards with v
    have hphase_norm : ‖phase v‖ = 1 := by
      simpa [phase, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * inner ℝ v w))
    rw [hphase_norm]
  have hphase_f : Integrable (fun v : ℝ ↦ phase v * f v) := by
    exact _hf.bdd_mul hphase_meas hphase_bound
  have hphase_g : Integrable (fun v : ℝ ↦ phase v * g v) := by
    exact _hg.bdd_mul hphase_meas hphase_bound
  calc
    𝓕⁻ (f - g) w = ∫ v, phase v * (f v - g v) := by
      rw [Real.fourierInv_eq']
      simp [phase, smul_eq_mul]
    _ = ∫ v, (phase v * f v) - (phase v * g v) := by
      congr with v
      ring
    _ = (∫ v, phase v * f v) - ∫ v, phase v * g v := by
      rw [integral_sub hphase_f hphase_g]
    _ = 𝓕⁻ f w - 𝓕⁻ g w := by
      rw [Real.fourierInv_eq', Real.fourierInv_eq']
      simp [phase, smul_eq_mul]

/-- Helper for Theorem 15.51: the Gaussian-smoothed density difference between `μ` and the
standard Gaussian lives on the common damped characteristic-function difference surface. -/
private lemma gaussianSmoothedDensityDifference_eq_fourierInv_dampedScaledCharFunSub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (fun x : ℝ ↦
      ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) -
        ((gaussianSmoothedDensity (gaussianReal 0 1) 1 x).toReal : ℂ)) =
      𝓕⁻ (fun s : ℝ ↦
        (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
          Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
  let f : ℝ → ℂ := fun s ↦
    charFun μ (-2 * Real.pi * s) *
      Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))
  let g : ℝ → ℂ := fun s ↦
    charFun (gaussianReal 0 1) (-2 * Real.pi * s) *
      Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))
  have hf : Integrable f := by
    -- Proof comment: Exercise 15.1.6 already proves integrability of each damped kernel.
    simpa [f] using
      integrable_dampedScaledCharFun (μ := μ) (ε := (1 : NNReal)) (hε := one_ne_zero)
  have hg : Integrable g := by
    -- Proof comment: the Gaussian comparator satisfies the same damped-kernel integrability.
    simpa [g] using
      integrable_dampedScaledCharFun
        (μ := (gaussianReal 0 1 : Measure ℝ)) (ε := (1 : NNReal)) (hε := one_ne_zero)
  -- Route correction: package the subtraction at the owner Fourier level instead of unfolding
  -- `Real.fourierInv_eq` and chasing integral-level subtraction by hand.
  calc
    (fun x : ℝ ↦
        ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) -
          ((gaussianSmoothedDensity (gaussianReal 0 1) 1 x).toReal : ℂ)) =
      𝓕⁻ f - 𝓕⁻ g := by
        funext x
        rw [show ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) = (𝓕⁻ f) x by
              simpa [f] using
                congrFun
                  (gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun
                    (μ := μ) (ε := (1 : NNReal)) one_ne_zero) x,
            show ((gaussianSmoothedDensity (gaussianReal 0 1) 1 x).toReal : ℂ) = (𝓕⁻ g) x by
              simpa [g] using
                congrFun
                  (gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun
                    (μ := (gaussianReal 0 1 : Measure ℝ)) (ε := (1 : NNReal)) one_ne_zero) x]
        rfl
    _ = 𝓕⁻ (f - g) := by
          symm
          exact fourierInvSub_ofIntegrable hf hg
    _ = 𝓕⁻ (fun s : ℝ ↦
          (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
            Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
          congr 1
          funext s
          dsimp [f, g]
          ring
/-- Helper for Theorem 15.51: after one Gaussian smoothing, the cdf difference is bounded by the
left-ray integral of the smoothed density difference. -/
private lemma gaussianSmoothedCdfDifference_le_densityDifferenceIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) x -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| ≤
      ∫ y in Set.Iic x,
        ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
            ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ)‖ ∂volume := by
  let f : ℝ → ℂ := fun y ↦
    ((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
      ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ)
  have hμ_cdf :
      cdf (μ ∗ gaussianReal 0 1) x =
        ∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume :=
    gaussianSmoothedLaw_cdf_eq_setIntegral (μ := μ) (hε := one_ne_zero) x
  have hGauss_cdf :
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x =
        ∫ y in Set.Iic x, (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume :=
    gaussianSmoothedLaw_cdf_eq_setIntegral
      (μ := (gaussianReal 0 1 : Measure ℝ)) (hε := one_ne_zero) x
  have hμ_int :
      Integrable (fun y ↦ ((gaussianSmoothedDensity μ 1 y).toReal : ℂ))
        (volume.restrict (Set.Iic x)) := by
    simpa using
      (gaussianSmoothedDensityToReal_regular (μ := μ) (hε := one_ne_zero)).2.integrableOn
  have hGauss_int :
      Integrable (fun y ↦ ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ))
        (volume.restrict (Set.Iic x)) := by
    simpa using
      (gaussianSmoothedDensityToReal_regular
        (μ := (gaussianReal 0 1 : Measure ℝ)) (hε := one_ne_zero)).2.integrableOn
  -- Proof comment: identify each smoothed cdf with its density integral, combine the difference
  -- into a single complex set integral, and bound it by the integral of its pointwise norm.
  calc
    |cdf (μ ∗ gaussianReal 0 1) x -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| =
        ‖(((cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) : ℝ) : ℂ)‖ := by
          symm
          simpa [Complex.norm_real, Real.norm_eq_abs] using
            (Complex.ofRealLI.norm_map
              (cdf (μ ∗ gaussianReal 0 1) x -
                cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x))
    _ = ‖∫ y in Set.Iic x, f y ∂volume‖ := by
          rw [hμ_cdf, hGauss_cdf]
          have hIntegral :
              (((∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume) -
                  ∫ y in Set.Iic x,
                    (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume : ℝ) : ℂ) =
                ∫ y in Set.Iic x, f y ∂volume := by
            have hμ_ofReal :
                ∫ y in Set.Iic x, ((gaussianSmoothedDensity μ 1 y).toReal : ℂ) ∂volume =
                  ((∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume : ℝ) : ℂ) := by
              simpa using
                (integral_complex_ofReal
                  (μ := volume.restrict (Set.Iic x))
                  (f := fun y ↦ (gaussianSmoothedDensity μ 1 y).toReal))
            have hGauss_ofReal :
                ∫ y in Set.Iic x,
                    ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ) ∂volume =
                  ((∫ y in Set.Iic x,
                      (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume : ℝ) : ℂ) := by
              simpa using
                (integral_complex_ofReal
                  (μ := volume.restrict (Set.Iic x))
                  (f := fun y ↦ (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal))
            rw [integral_sub hμ_int hGauss_int]
            rw [Complex.ofReal_sub, ← hμ_ofReal, ← hGauss_ofReal]
          rw [hIntegral]
    _ ≤ ∫ y in Set.Iic x, ‖f y‖ ∂volume := by
          simpa [f] using
            (norm_integral_le_integral_norm
              (μ := volume.restrict (Set.Iic x)) (f := f))
/-- Helper for Theorem 15.51: the once-smoothed cdf difference is already controlled by the
inverse Fourier transform on the common damped characteristic-function difference surface. -/
private lemma gaussianSmoothedCdfDifference_le_fourierInvDifferenceIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) x -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| ≤
      ∫ y in Set.Iic x,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
  -- Proof comment: rewrite the smoothed-density difference using the Fourier inversion identity
  -- already packaged above, then reuse the previous cdf bound verbatim.
  have hRewrite :
      (∫ y in Set.Iic x,
          ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
              ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ)‖ ∂volume) =
        ∫ y in Set.Iic x,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
    exact congrArg
      (fun f : ℝ → ℂ => ∫ y in Set.Iic x, ‖f y‖ ∂volume)
      (gaussianSmoothedDensityDifference_eq_fourierInv_dampedScaledCharFunSub (μ := μ))
  calc
    |cdf (μ ∗ gaussianReal 0 1) x -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| ≤
      ∫ y in Set.Iic x,
        ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
            ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ)‖ ∂volume :=
      gaussianSmoothedCdfDifference_le_densityDifferenceIntegral (μ := μ) x
    _ = ∫ y in Set.Iic x,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := hRewrite

/-- Helper for Theorem 15.51: the Gaussian-smoothed density difference between two probability
laws lives on the common damped characteristic-function difference surface. -/
private lemma smoothedDensityDifference_eq_fourierInv_dampedScaledCharFunSub_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (fun x : ℝ ↦
      ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) -
        ((gaussianSmoothedDensity ν 1 x).toReal : ℂ)) =
      𝓕⁻ (fun s : ℝ ↦
        (charFun μ (-2 * Real.pi * s) - charFun ν (-2 * Real.pi * s)) *
          Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
  let f : ℝ → ℂ := fun s ↦
    charFun μ (-2 * Real.pi * s) *
      Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))
  let g : ℝ → ℂ := fun s ↦
    charFun ν (-2 * Real.pi * s) *
      Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))
  have hf : Integrable f := by
    -- Proof comment: Exercise 15.1.6 already proves integrability of each damped kernel.
    simpa [f] using
      integrable_dampedScaledCharFun (μ := μ) (ε := (1 : NNReal)) (hε := one_ne_zero)
  have hg : Integrable g := by
    -- Proof comment: the same damped-kernel integrability applies to the comparison law `ν`.
    simpa [g] using
      integrable_dampedScaledCharFun (μ := ν) (ε := (1 : NNReal)) (hε := one_ne_zero)
  -- Proof comment: package the two smoothed densities as inverse Fourier transforms first, then
  -- combine them by the generic subtraction lemma on the Fourier side.
  calc
    (fun x : ℝ ↦
        ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) -
          ((gaussianSmoothedDensity ν 1 x).toReal : ℂ)) =
      𝓕⁻ f - 𝓕⁻ g := by
        funext x
        rw [show ((gaussianSmoothedDensity μ 1 x).toReal : ℂ) = (𝓕⁻ f) x by
              simpa [f] using
                congrFun
                  (gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun
                    (μ := μ) (ε := (1 : NNReal)) one_ne_zero) x,
            show ((gaussianSmoothedDensity ν 1 x).toReal : ℂ) = (𝓕⁻ g) x by
              simpa [g] using
                congrFun
                  (gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun
                    (μ := ν) (ε := (1 : NNReal)) one_ne_zero) x]
        rfl
    _ = 𝓕⁻ (f - g) := by
          symm
          exact fourierInvSub_ofIntegrable hf hg
    _ = 𝓕⁻ (fun s : ℝ ↦
          (charFun μ (-2 * Real.pi * s) - charFun ν (-2 * Real.pi * s)) *
            Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) := by
          congr 1
          funext s
          dsimp [f, g]
          ring

/-- Helper for Theorem 15.51: after one Gaussian smoothing, the cdf difference between two
probability laws is bounded by the left-ray integral of their smoothed density difference. -/
private lemma smoothedCdfDifference_le_densityDifferenceIntegral_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x| ≤
      ∫ y in Set.Iic x,
        ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
            ((gaussianSmoothedDensity ν 1 y).toReal : ℂ)‖ ∂volume := by
  let f : ℝ → ℂ := fun y ↦
    ((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
      ((gaussianSmoothedDensity ν 1 y).toReal : ℂ)
  have hμ_cdf :
      cdf (μ ∗ gaussianReal 0 1) x =
        ∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume :=
    gaussianSmoothedLaw_cdf_eq_setIntegral (μ := μ) (hε := one_ne_zero) x
  have hν_cdf :
      cdf (ν ∗ gaussianReal 0 1) x =
        ∫ y in Set.Iic x, (gaussianSmoothedDensity ν 1 y).toReal ∂volume :=
    gaussianSmoothedLaw_cdf_eq_setIntegral (μ := ν) (hε := one_ne_zero) x
  have hμ_int :
      Integrable (fun y ↦ ((gaussianSmoothedDensity μ 1 y).toReal : ℂ))
        (volume.restrict (Set.Iic x)) := by
    simpa using
      (gaussianSmoothedDensityToReal_regular (μ := μ) (hε := one_ne_zero)).2.integrableOn
  have hν_int :
      Integrable (fun y ↦ ((gaussianSmoothedDensity ν 1 y).toReal : ℂ))
        (volume.restrict (Set.Iic x)) := by
    simpa using
      (gaussianSmoothedDensityToReal_regular (μ := ν) (hε := one_ne_zero)).2.integrableOn
  -- Proof comment: identify each smoothed cdf with its density integral, combine the difference
  -- into one complex set integral, and majorize that integral by the integral of its pointwise
  -- norm.
  calc
    |cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x| =
        ‖(((cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x : ℝ) : ℂ))‖ := by
          symm
          simpa [Complex.norm_real, Real.norm_eq_abs] using
            (Complex.ofRealLI.norm_map
              (cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x))
    _ = ‖∫ y in Set.Iic x, f y ∂volume‖ := by
          rw [hμ_cdf, hν_cdf]
          have hIntegral :
              (((∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume) -
                  ∫ y in Set.Iic x, (gaussianSmoothedDensity ν 1 y).toReal ∂volume : ℝ) : ℂ) =
                ∫ y in Set.Iic x, f y ∂volume := by
            have hμ_ofReal :
                ∫ y in Set.Iic x, ((gaussianSmoothedDensity μ 1 y).toReal : ℂ) ∂volume =
                  ((∫ y in Set.Iic x, (gaussianSmoothedDensity μ 1 y).toReal ∂volume : ℝ) : ℂ) := by
              simpa using
                (integral_complex_ofReal
                  (μ := volume.restrict (Set.Iic x))
                  (f := fun y ↦ (gaussianSmoothedDensity μ 1 y).toReal))
            have hν_ofReal :
                ∫ y in Set.Iic x, ((gaussianSmoothedDensity ν 1 y).toReal : ℂ) ∂volume =
                  ((∫ y in Set.Iic x, (gaussianSmoothedDensity ν 1 y).toReal ∂volume : ℝ) : ℂ) := by
              simpa using
                (integral_complex_ofReal
                  (μ := volume.restrict (Set.Iic x))
                  (f := fun y ↦ (gaussianSmoothedDensity ν 1 y).toReal))
            rw [integral_sub hμ_int hν_int]
            rw [Complex.ofReal_sub, ← hμ_ofReal, ← hν_ofReal]
          rw [hIntegral]
    _ ≤ ∫ y in Set.Iic x, ‖f y‖ ∂volume := by
          simpa [f] using
            (norm_integral_le_integral_norm
              (μ := volume.restrict (Set.Iic x)) (f := f))

/-- Helper for Theorem 15.51: the once-smoothed cdf difference between two probability laws is
already controlled by the inverse Fourier transform on their common damped
characteristic-function difference surface. -/
private lemma smoothedCdfDifference_le_fourierInvDifferenceIntegral_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x| ≤
      ∫ y in Set.Iic x,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μ (-2 * Real.pi * s) - charFun ν (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
  -- Proof comment: rewrite the compare-version smoothed density difference by Fourier inversion
  -- and then reuse the preceding cdf bound unchanged.
  have hRewrite :
      (∫ y in Set.Iic x,
          ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
              ((gaussianSmoothedDensity ν 1 y).toReal : ℂ)‖ ∂volume) =
        ∫ y in Set.Iic x,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun ν (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
    exact congrArg
      (fun f : ℝ → ℂ ↦ ∫ y in Set.Iic x, ‖f y‖ ∂volume)
      (smoothedDensityDifference_eq_fourierInv_dampedScaledCharFunSub_compare
        (μ := μ) (ν := ν))
  calc
    |cdf (μ ∗ gaussianReal 0 1) x - cdf (ν ∗ gaussianReal 0 1) x| ≤
      ∫ y in Set.Iic x,
        ‖((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
            ((gaussianSmoothedDensity ν 1 y).toReal : ℂ)‖ ∂volume :=
      smoothedCdfDifference_le_densityDifferenceIntegral_compare (μ := μ) (ν := ν) x
    _ = ∫ y in Set.Iic x,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun ν (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := hRewrite

/-- Helper for Theorem 15.51: translating a law by `-x` moves the cdf evaluation at `x` to the
origin. -/
private lemma cdf_map_sub_const_eq_cdf_add
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x z : ℝ) :
    cdf (μ.map (fun y : ℝ ↦ y - x)) z = cdf μ (z + x) := by
  -- Proof comment: evaluate the translated cdf on `(-∞, z]` and rewrite its preimage as
  -- `(-∞, z + x]` in the original coordinates.
  letI : IsProbabilityMeasure (μ.map (fun y : ℝ ↦ y - x)) :=
    Measure.isProbabilityMeasure_map
      ((measurable_id.sub measurable_const).aemeasurable :
        AEMeasurable (fun y : ℝ ↦ y - x) μ)
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
  rw [Measure.map_apply (μ := μ) (f := fun y : ℝ ↦ y - x)
    (measurable_id.sub measurable_const) measurableSet_Iic]
  have hPreimage : (fun y : ℝ ↦ y - x) ⁻¹' Set.Iic z = Set.Iic (z + x) := by
    ext y
    simp [sub_le_iff_le_add]
  rw [hPreimage]

/-- Helper for Theorem 15.51: translating a law by `-x` moves the cdf evaluation at `x` to the
origin. -/
private lemma cdf_map_sub_const_zero_eq_cdf
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (μ.map (fun y : ℝ ↦ y - x)) 0 = cdf μ x := by
  -- Proof comment: this is the `z = 0` specialization of the arbitrary-endpoint translation API.
  simpa using cdf_map_sub_const_eq_cdf_add (μ := μ) x 0

/-- Helper for Theorem 15.51: translating both comparison laws by `-x` recenters their cdf gap at
the origin. -/
private lemma cdfGap_eq_translatedCdfGapAtZero
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : ℝ) :
    |cdf μ x - cdf ν x| =
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 - cdf (ν.map (fun y : ℝ ↦ y - x)) 0| := by
  -- Proof comment: translate each law separately so the common evaluation point becomes `0`.
  rw [cdf_map_sub_const_zero_eq_cdf (μ := μ) x, cdf_map_sub_const_zero_eq_cdf (μ := ν) x]

/-- Helper for Theorem 15.51: translating a law by `-x` multiplies its characteristic function by
the corresponding phase factor. -/
private lemma charFun_map_sub_const_eq_phaseMul
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x t : ℝ) :
    charFun (μ.map (fun y : ℝ ↦ y - x)) t =
      charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I) := by
  -- Proof comment: subtraction by `x` is translation by `-x`, so the owner translation formula
  -- gives the characteristic function exactly.
  calc
    charFun (μ.map (fun y : ℝ ↦ y - x)) t =
        charFun μ t * Complex.exp (-((((inner ℝ x t : ℝ) : ℂ)) * Complex.I)) := by
          simpa [sub_eq_add_neg] using
            (MeasureTheory.charFun_map_add_const (μ := μ) (-x) t)
    _ = charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I) := by
          have hinner : inner ℝ x t = x * t := by
            change t * x = x * t
            ring
          have hExpArg :
              (-((((inner ℝ x t : ℝ) : ℂ)) * Complex.I) : ℂ) =
                (((-x) * t : ℝ) : ℂ) * Complex.I := by
            rw [hinner]
            simpa [mul_assoc, mul_left_comm, mul_comm]
          rw [hExpArg]

/-- Helper for Theorem 15.51: translating both laws by `-x` absorbs the oscillatory phase in the
window integral into their characteristic-function difference. -/
private lemma translatedCharFunDifferenceWindow_eq_centeredWindow
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x T : ℝ) :
    ∫ t in -T..T,
        (charFun (μ.map (fun y : ℝ ↦ y - x)) t -
            charFun (ν.map (fun y : ℝ ↦ y - x)) t) =
      ∫ t in -T..T,
        (charFun μ t - charFun ν t) * Complex.exp (((-x) * t : ℝ) * Complex.I) := by
  -- Proof comment: translate each characteristic function, then factor the common oscillatory
  -- phase out of the pointwise difference.
  congr with t
  rw [charFun_map_sub_const_eq_phaseMul, charFun_map_sub_const_eq_phaseMul]
  ring
/-- Helper for Theorem 15.51: the symmetric frequency-window integral of the translated phase of a
characteristic function is the corresponding sinc average of the original law. -/
private lemma integral_shiftedCharFunWindow_eq_sincAverage
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) (hr : 0 < r) :
    ∫ t in -r..r, charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
      2 * r * ∫ y, Real.sinc (r * (y - x)) ∂μ := by
  let ν : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  have hWindow :
      ∫ t in -r..r, charFun ν t = 2 * r * ∫ y, Real.sinc (r * y) ∂ν := by
    simpa [ν] using MeasureTheory.integral_charFun_Icc (μ := ν) hr
  have hMap :
      ∫ y, Real.sinc (r * y) ∂ν = ∫ y, Real.sinc (r * (y - x)) ∂μ := by
    dsimp [ν]
    simpa [sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_map
        (μ := μ)
        (φ := fun y : ℝ ↦ y - x)
        (f := fun y : ℝ ↦ Real.sinc (r * y))
        (measurable_id.sub measurable_const).aemeasurable
        (by fun_prop :
          AEStronglyMeasurable (fun y : ℝ ↦ Real.sinc (r * y))
            (Measure.map (fun y ↦ y - x) μ)))
  -- Proof comment: apply `integral_charFun_Icc` to the translated law `μ.map (fun y ↦ y - x)`,
  -- then rewrite both the characteristic function and the sinc average back in the original
  -- coordinates.
  calc
    ∫ t in -r..r, charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I)
        = ∫ t in -r..r, charFun ν t := by
            congr with t
            rw [charFun_map_sub_const_eq_phaseMul]
    _ = 2 * r * ∫ y, Real.sinc (r * y) ∂ν := hWindow
    _ = 2 * r * ∫ y, Real.sinc (r * (y - x)) ∂μ := by rw [hMap]

/-- Helper for Theorem 15.51: for two probability laws, the shifted sinc averages differ by at
most the symmetric window integral of the characteristic-function difference. -/
private lemma shiftedSincAverageDifference_le_windowNormIntegral_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x r : ℝ) (hr : 0 < r) :
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂ν| ≤
      (1 / (2 * r)) *
        ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := by
  let A : ℝ := ∫ y, Real.sinc (r * (y - x)) ∂μ
  let B : ℝ := ∫ y, Real.sinc (r * (y - x)) ∂ν
  let h : ℝ → ℂ := fun t ↦
    (charFun μ t - charFun ν t) *
      Complex.exp (((-x) * t : ℝ) * Complex.I)
  have hμ :
      ∫ t in -r..r, charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
        2 * r * A := by
    -- Proof comment: rewrite the translated window integral for `μ` as the corresponding sinc
    -- average.
    simpa [A] using integral_shiftedCharFunWindow_eq_sincAverage (μ := μ) x r hr
  have hν :
      ∫ t in -r..r, charFun ν t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
        2 * r * B := by
    -- Proof comment: the same translated-window identity holds for the comparison law `ν`.
    simpa [B] using integral_shiftedCharFunWindow_eq_sincAverage (μ := ν) x r hr
  have hIntμ :
      IntervalIntegrable
        (fun t ↦ charFun μ t * Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-r) r := by
    -- Proof comment: the translated characteristic-function integrand for `μ` is continuous on
    -- the compact frequency window.
    refine Continuous.intervalIntegrable ?_ (-r) r
    fun_prop
  have hIntν :
      IntervalIntegrable
        (fun t ↦ charFun ν t * Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-r) r := by
    -- Proof comment: the same continuity argument applies to the comparison law `ν`.
    refine Continuous.intervalIntegrable ?_ (-r) r
    fun_prop
  have hRewrite :
      ∫ t in -r..r, h t = ((2 * r : ℝ) : ℂ) * (((A - B : ℝ) : ℂ)) := by
    -- Proof comment: subtract the two translated-window identities and factor the common phase.
    simp only [h, sub_mul]
    rw [intervalIntegral.integral_sub hIntμ hIntν, hμ, hν]
    simp [A, B, Complex.ofReal_sub, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_add, mul_assoc, mul_left_comm, mul_comm]
  have hNormWindow :
      ‖∫ t in -r..r, h t‖ ≤ ∫ t in -r..r, ‖h t‖ := by
    exact intervalIntegral.norm_integral_le_integral_norm (by linarith : -r ≤ r)
  have hNormIntegrand :
      ∫ t in -r..r, ‖h t‖ =
        ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := by
    -- Proof comment: the oscillatory phase has unit norm, so it disappears from the majorant.
    congr with t
    rw [show h t =
        (charFun μ t - charFun ν t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I) by rfl]
    rw [norm_mul]
    have hphase :
        ‖Complex.exp (((-x) * t : ℝ) * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (((-x) * t : ℝ)))
    rw [hphase, mul_one]
  have hScale :
      ‖((2 * r : ℝ) : ℂ) * (((A - B : ℝ) : ℂ))‖ = (2 * r) * |A - B| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * r)]
  have hScaled :
      (2 * r) * |A - B| ≤ ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := by
    rw [← hScale, ← hRewrite]
    calc
      ‖∫ t in -r..r, h t‖ ≤ ∫ t in -r..r, ‖h t‖ := hNormWindow
      _ = ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := hNormIntegrand
  have hScaled' :
      |A - B| * (2 * r) ≤ ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := by
    calc
      |A - B| * (2 * r) = (2 * r) * |A - B| := by ring
      _ ≤ ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := hScaled
  have hFinal :
      |A - B| ≤
        (1 / (2 * r)) *
          ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := by
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (le_div_iff₀ (by positivity : 0 < 2 * r)).2 hScaled'
  simpa [A, B] using hFinal

/-- Helper for Theorem 15.51: the shifted sinc averages of a law and the standard Gaussian differ
by at most the symmetric window integral of the characteristic-function difference. -/
private lemma shiftedSincAverageDifference_le_windowNormIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) (hr : 0 < r) :
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂(gaussianReal 0 1)| ≤
      (1 / (2 * r)) *
        ∫ t in -r..r, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ := by
  -- Proof comment: this is the Gaussian specialization of the preceding two-measure window
  -- comparison theorem, so reusing that theorem avoids repeating the same Fourier-window proof.
  simpa using
    shiftedSincAverageDifference_le_windowNormIntegral_compare
      (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x r hr

/-- Helper for Theorem 15.51: the shifted sinc-average difference is also controlled directly on
the quotient surface `((charFun μ - charFun (gaussianReal 0 1)) / t)`. -/
private lemma shiftedSincAverageDifference_le_quotientWindowIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) (hr : 0 < r)
    (hQuotientInt :
      IntervalIntegrable
        (fun t ↦ ((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ))
        volume (-r) r) :
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂(gaussianReal 0 1)| ≤
      (1 / 2) *
        ∫ t in -r..r, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
  have hSinc :
      |∫ y, Real.sinc (r * (y - x)) ∂μ -
          ∫ y, Real.sinc (r * (y - x)) ∂(gaussianReal 0 1)| ≤
        (1 / (2 * r)) *
          ∫ t in -r..r, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ :=
    shiftedSincAverageDifference_le_windowNormIntegral (μ := μ) x r hr
  have hWindowInt :
      IntervalIntegrable
        (fun t ↦ ‖charFun μ t - charFun (gaussianReal 0 1) t‖)
        volume (-r) r := by
    -- Proof comment: the raw characteristic-function difference is continuous on the compact
    -- window.
    refine Continuous.intervalIntegrable ?_ (-r) r
    fun_prop
  have hScaledQuotientInt :
      IntervalIntegrable
        (fun t ↦ r * ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖)
        volume (-r) r := by
    -- Proof comment: multiply the interval-integrable quotient norm by the fixed window radius.
    simpa using hQuotientInt.norm.const_mul r
  have hWindowLe :
      ∫ t in -r..r, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ ≤
        ∫ t in -r..r, r * ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
    -- Proof comment: on `[-r, r]`, the factor `|t|` is bounded by `r`, so `‖Δ(t)‖ ≤ r‖Δ(t)/t‖`.
    refine
      intervalIntegral.integral_mono_on
        (μ := volume) (a := -r) (b := r)
        (f := fun t ↦ ‖charFun μ t - charFun (gaussianReal 0 1) t‖)
        (g := fun t ↦ r * ‖((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ)‖)
        (by linarith) hWindowInt hScaledQuotientInt ?_
    intro t ht
    by_cases ht0 : t = 0
    · -- Proof comment: at the origin both characteristic functions equal `1`, so the quotient
      -- bound is trivial.
      simp [ht0]
    · have hMul :
          ((t : ℂ) * ((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ)) =
            charFun μ t - charFun (gaussianReal 0 1) t := by
        field_simp [ht0]
      have ht_abs : |t| ≤ r := abs_le.mpr ht
      calc
        ‖charFun μ t - charFun (gaussianReal 0 1) t‖
            = ‖(t : ℂ) * ((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ := by
                rw [hMul]
        _ = |t| * ‖((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ r * ‖((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ := by
              gcongr
  have hQuotientRewrite :
      ∫ t in -r..r, r * ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ =
        r * ∫ t in -r..r, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
    -- Proof comment: pull the constant window radius outside the interval integral.
    simpa using
      (intervalIntegral.integral_const_mul
        (a := -r) (b := r)
        (r := r)
        (f := fun t ↦ ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖))
  calc
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂(gaussianReal 0 1)| ≤
      (1 / (2 * r)) *
        ∫ t in -r..r, ‖charFun μ t - charFun (gaussianReal 0 1) t‖ := hSinc
    _ ≤ (1 / (2 * r)) *
          ∫ t in -r..r, r * ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
          gcongr
    _ = (1 / 2) *
          ∫ t in -r..r, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
          rw [hQuotientRewrite]
          field_simp [ne_of_gt hr]

/-- Helper for Theorem 15.51: the shifted sinc-average difference for two probability laws is
also controlled directly on the quotient surface `((charFun μ - charFun ν) / t)`. -/
private lemma shiftedSincAverageDifference_le_quotientWindowIntegral_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x r : ℝ) (hr : 0 < r)
    (hQuotientInt :
      IntervalIntegrable
        (fun t ↦ ((charFun μ t - charFun ν t) / t : ℂ))
        volume (-r) r) :
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂ν| ≤
      (1 / 2) *
        ∫ t in -r..r, ‖(charFun μ t - charFun ν t) / t‖ := by
  have hSinc :
      |∫ y, Real.sinc (r * (y - x)) ∂μ -
          ∫ y, Real.sinc (r * (y - x)) ∂ν| ≤
        (1 / (2 * r)) *
          ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ :=
    shiftedSincAverageDifference_le_windowNormIntegral_compare
      (μ := μ) (ν := ν) x r hr
  have hWindowInt :
      IntervalIntegrable
        (fun t ↦ ‖charFun μ t - charFun ν t‖)
        volume (-r) r := by
    -- Proof comment: the raw characteristic-function difference stays continuous on the compact
    -- window.
    refine Continuous.intervalIntegrable ?_ (-r) r
    fun_prop
  have hScaledQuotientInt :
      IntervalIntegrable
        (fun t ↦ r * ‖(charFun μ t - charFun ν t) / t‖)
        volume (-r) r := by
    -- Proof comment: multiplying the interval-integrable quotient norm by the fixed radius
    -- preserves interval integrability.
    simpa using hQuotientInt.norm.const_mul r
  have hWindowLe :
      ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ ≤
        ∫ t in -r..r, r * ‖(charFun μ t - charFun ν t) / t‖ := by
    -- Proof comment: on `[-r, r]`, the factor `|t|` is bounded by `r`, so `‖Δ(t)‖ ≤ r‖Δ(t)/t‖`.
    refine
      intervalIntegral.integral_mono_on
        (μ := volume) (a := -r) (b := r)
        (f := fun t ↦ ‖charFun μ t - charFun ν t‖)
        (g := fun t ↦ r * ‖((charFun μ t - charFun ν t) / t : ℂ)‖)
        (by linarith) hWindowInt hScaledQuotientInt ?_
    intro t ht
    by_cases ht0 : t = 0
    · -- Proof comment: at the origin both characteristic functions equal `1`, so the quotient
      -- majorant is trivial.
      simp [ht0]
    · have hMul :
          ((t : ℂ) * ((charFun μ t - charFun ν t) / t : ℂ)) =
            charFun μ t - charFun ν t := by
        field_simp [ht0]
      have ht_abs : |t| ≤ r := abs_le.mpr ht
      calc
        ‖charFun μ t - charFun ν t‖
            = ‖(t : ℂ) * ((charFun μ t - charFun ν t) / t : ℂ)‖ := by
                rw [hMul]
        _ = |t| * ‖((charFun μ t - charFun ν t) / t : ℂ)‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ r * ‖((charFun μ t - charFun ν t) / t : ℂ)‖ := by
              gcongr
  have hQuotientRewrite :
      ∫ t in -r..r, r * ‖(charFun μ t - charFun ν t) / t‖ =
        r * ∫ t in -r..r, ‖(charFun μ t - charFun ν t) / t‖ := by
    -- Proof comment: pull the constant radius outside the interval integral.
    simpa using
      (intervalIntegral.integral_const_mul
        (a := -r) (b := r)
        (r := r)
        (f := fun t ↦ ‖(charFun μ t - charFun ν t) / t‖))
  calc
    |∫ y, Real.sinc (r * (y - x)) ∂μ -
        ∫ y, Real.sinc (r * (y - x)) ∂ν| ≤
      (1 / (2 * r)) *
        ∫ t in -r..r, ‖charFun μ t - charFun ν t‖ := hSinc
    _ ≤ (1 / (2 * r)) *
          ∫ t in -r..r, r * ‖(charFun μ t - charFun ν t) / t‖ := by
          gcongr
    _ = (1 / 2) *
          ∫ t in -r..r, ‖(charFun μ t - charFun ν t) / t‖ := by
          rw [hQuotientRewrite]
          field_simp [ne_of_gt hr]

/-- Helper for Theorem 15.51: after Gaussian smoothing, the standard Gaussian comparator still
changes by at most `O(T⁻¹)` on a window of radius `1 / T`. -/
private lemma gaussianSmoothedStandardGaussianCdfWindow_le_invCutoff
    (x T : ℝ) (hT : 0 < T) (ε : NNReal) :
    cdf (((gaussianReal (0 : ℝ) (1 : NNReal) : Measure ℝ) ∗ gaussianReal (0 : ℝ) ε)) (x + T⁻¹) -
        cdf (((gaussianReal (0 : ℝ) (1 : NNReal) : Measure ℝ) ∗ gaussianReal (0 : ℝ) ε))
          (x - T⁻¹) ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hconv :
      (((gaussianReal (0 : ℝ) (1 : NNReal) : Measure ℝ) ∗ gaussianReal (0 : ℝ) ε)) =
        gaussianReal (0 : ℝ) ((1 : NNReal) + ε) := by
    -- Proof comment: the smoothed standard Gaussian is still Gaussian with variance `1 + ε`.
    simpa using
      (ProbabilityTheory.gaussianReal_conv_gaussianReal
        (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ)) (v₁ := (1 : NNReal)) (v₂ := ε))
  rw [hconv]
  have hIoc :
      (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (Set.Ioc (x - T⁻¹) (x + T⁻¹)) =
        ENNReal.ofReal
          (cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x + T⁻¹) -
            cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x - T⁻¹)) := by
    -- Proof comment: cdf increments recover the Gaussian mass of the corresponding interval.
    simpa [ProbabilityTheory.measure_cdf (μ := gaussianReal (0 : ℝ) ((1 : NNReal) + ε))] using
      (ProbabilityTheory.cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε))).measure_Ioc
        (x - T⁻¹) (x + T⁻¹)
  have hdiff_nonneg :
      0 ≤
        cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x + T⁻¹) -
          cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x - T⁻¹) := by
    -- Proof comment: the convolved Gaussian cdf is monotone in the evaluation point.
    refine sub_nonneg.mpr ?_
    exact ProbabilityTheory.monotone_cdf (μ := gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (by
      have hTinv_pos : 0 < T⁻¹ := by positivity
      linarith)
  have hIoc_le :
      ENNReal.ofReal
          (cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x + T⁻¹) -
            cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x - T⁻¹)) ≤
        (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
    -- Proof comment: enlarge the half-open interval to the closed interval with the same endpoints.
    have hsubset : Set.Ioc (x - T⁻¹) (x + T⁻¹) ⊆ Set.Icc (x - T⁻¹) (x + T⁻¹) := by
      intro y hy
      exact ⟨le_of_lt hy.1, hy.2⟩
    simpa [hIoc] using
      (measure_mono (μ := gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) hsubset)
  have hreal_le :
      cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x + T⁻¹) -
          cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x - T⁻¹) ≤
        ((gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := by
    -- Proof comment: move the interval-mass comparison back from `ENNReal` to `ℝ`.
    exact
      (ENNReal.ofReal_le_iff_le_toReal
        (measure_ne_top (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) _)).mp hIoc_le
  calc
    cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x + T⁻¹) -
        cdf (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (x - T⁻¹) ≤
      ((gaussianReal (0 : ℝ) ((1 : NNReal) + ε)) (Set.Icc (x - T⁻¹) (x + T⁻¹))).toReal := hreal_le
    _ = (gaussianReal (0 : ℝ) ((1 : NNReal) + ε)).real (Set.Icc (x - T⁻¹) (x + T⁻¹)) := by
          rw [MeasureTheory.Measure.real_def]
    _ ≤ (2 / Real.sqrt (2 * Real.pi)) / T := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            gaussianIntervalMeasure_one_addVariance_le_peak x T⁻¹ (by positivity : 0 ≤ T⁻¹) ε
/-- Helper for Theorem 15.51: translating a standard Gaussian by `y` shifts the left ray
`(-∞, x]` to `(-∞, x - y]`. -/
private lemma diracGaussianConv_apply_Iic
    (y x : ℝ) :
    (Measure.dirac y ∗ gaussianReal 0 1) (Set.Iic x) =
      (gaussianReal 0 1 : Measure ℝ) (Set.Iic (x - y)) := by
  -- Proof comment: convolving `δ_y` with the Gaussian translates the Gaussian by `y`, and the
  -- preimage of `(-∞, x]` under that translation is `(-∞, x - y]`.
  rw [Measure.dirac_conv]
  have hmap :
      (Measure.map (fun z : ℝ ↦ y + z) (gaussianReal 0 1)) (Set.Iic x) =
        (gaussianReal 0 1 : Measure ℝ) ((fun z : ℝ ↦ y + z) ⁻¹' Set.Iic x) := by
    simpa using
      (Measure.map_apply
        (μ := (gaussianReal 0 1 : Measure ℝ))
        (f := fun z : ℝ ↦ y + z)
        (s := Set.Iic x)
        (measurable_const.add measurable_id)
        measurableSet_Iic)
  rw [hmap]
  congr 1
  ext z
  simp
/-- Helper for Theorem 15.51: an unsmoothed cdf value is controlled by the once-Gaussian-smoothed
left ray at a right shift, up to the standard Gaussian right tail. -/
private lemma smoothingRightShiftEventCover
    (x a : ℝ) :
    Set.Iic x ×ˢ (Set.univ : Set ℝ) ⊆
      {p : ℝ × ℝ | p.1 + p.2 ≤ x + a} ∪ ((Set.univ : Set ℝ) ×ˢ Set.Ioi a) := by
  intro p hp
  rcases hp with ⟨hp₁, hp₂⟩
  by_cases hpTail : p.2 ∈ Set.Ioi a
  · -- Proof comment: if the Gaussian increment lands in the right tail, the covering is immediate.
    exact Or.inr ⟨hp₂, hpTail⟩
  · -- Proof comment: otherwise the increment is at most `a`, so adding it to `p.1 ≤ x` keeps the
    -- shifted sum inside `(-∞, x + a]`.
    left
    have hp₁_le : p.1 ≤ x := hp₁
    have hp₂_le : p.2 ≤ a := by simpa [Set.mem_Ioi, not_lt] using hpTail
    dsimp
    linarith

/-- Helper for Theorem 15.51: an unsmoothed cdf value is controlled by the once-Gaussian-smoothed
left ray at a right shift, up to the standard Gaussian right tail. -/
private lemma cdf_le_convolvedCdf_add_rightTail
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x a : ℝ) :
    cdf μ x ≤
      cdf (μ ∗ ν) (x + a) +
        ν.real (Set.Ioi a) := by
  have hrect :
      (μ.prod ν) (Set.Iic x ×ˢ (Set.univ : Set ℝ)) = μ (Set.Iic x) := by
    -- Proof comment: the product law of the event `Y ≤ x` and the full comparison coordinate is
    -- just the original left-ray mass because the second factor has total mass `1`.
    rw [Measure.prod_prod]
    simp
  have hconv :
      (μ.prod ν) {p : ℝ × ℝ | p.1 + p.2 ≤ x + a} = (μ ∗ ν) (Set.Iic (x + a)) := by
    -- Proof comment: additive convolution is the pushforward of the product law under addition.
    rw [Measure.conv, Measure.map_apply (measurable_fst.add measurable_snd) measurableSet_Iic]
    rfl
  have htail :
      (μ.prod ν) ((Set.univ : Set ℝ) ×ˢ Set.Ioi a) = ν (Set.Ioi a) := by
    -- Proof comment: the right-tail event depends only on the comparison coordinate.
    rw [Measure.prod_prod]
    simp
  have hle_enn :
      μ (Set.Iic x) ≤ (μ ∗ ν) (Set.Iic (x + a)) + ν (Set.Ioi a) := by
    -- Proof comment: the covering lemma pushes the left ray into the shifted smoothed left ray
    -- plus the comparison right tail.
    rw [← hrect, ← hconv, ← htail]
    exact le_trans (measure_mono (smoothingRightShiftEventCover x a)) (measure_union_le _ _)
  have hsum_ne_top :
      (μ ∗ ν) (Set.Iic (x + a)) + ν (Set.Ioi a) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top (μ ∗ ν) _, measure_ne_top ν _⟩
  have hle_real :
      (μ (Set.Iic x)).toReal ≤ ((μ ∗ ν) (Set.Iic (x + a))).toReal + (ν (Set.Ioi a)).toReal := by
    have htmp :
        (μ (Set.Iic x)).toReal ≤ ((μ ∗ ν) (Set.Iic (x + a)) + ν (Set.Ioi a)).toReal := by
      exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) hsum_ne_top).2 hle_enn
    simpa [ENNReal.toReal_add, measure_ne_top (μ ∗ ν) _, measure_ne_top ν _] using htmp
  simpa [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def] using hle_real

/-- Helper for Theorem 15.51: an unsmoothed cdf value is controlled by the once-Gaussian-smoothed
left ray at a right shift, up to the standard Gaussian right tail. -/
private lemma cdf_le_gaussianSmoothedCdf_add_rightTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x a : ℝ) :
    cdf μ x ≤
      cdf (μ ∗ gaussianReal 0 1) (x + a) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi a) := by
  -- Proof comment: this is the Gaussian specialization of the general convolved right-tail
  -- comparison.
  simpa using
    cdf_le_convolvedCdf_add_rightTail (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x a

/-- Helper for Theorem 15.51: the once-smoothed left ray at a left shift is covered by the
unsmoothed left ray together with the Gaussian left tail. -/
private lemma smoothingLeftShiftEventCover
    (x a : ℝ) :
    {p : ℝ × ℝ | p.1 + p.2 ≤ x - a} ⊆
      (Set.Iic x ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ Set.Iic (-a)) := by
  intro p hp
  by_cases hpLeft : p.1 ≤ x
  · -- Proof comment: when the first coordinate already lies in `(-∞, x]`, the event is in the
    -- unsmoothed left ray regardless of the Gaussian increment.
    exact Or.inl ⟨hpLeft, Set.mem_univ _⟩
  · -- Proof comment: otherwise `p.1 > x`, so the inequality `p.1 + p.2 ≤ x - a` forces the
    -- Gaussian increment into the left tail `(-∞, -a]`.
    right
    have hpLeft_lt : x < p.1 := by simpa [not_le] using hpLeft
    have hpSum : p.1 + p.2 ≤ x - a := hp
    have hpTail : p.2 ≤ -a := by
      by_contra hpTail
      have hpTail_lt : -a < p.2 := by simpa [not_le] using hpTail
      linarith
    exact ⟨Set.mem_univ _, hpTail⟩

/-- Helper for Theorem 15.51: a once-Gaussian-smoothed left ray at a left shift is controlled by
the unsmoothed cdf plus the standard Gaussian left tail. -/
private lemma convolvedCdf_sub_le_cdf_add_leftTail
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x a : ℝ) :
    cdf (μ ∗ ν) (x - a) ≤
      cdf μ x + ν.real (Set.Iic (-a)) := by
  have hconv :
      (μ.prod ν) {p : ℝ × ℝ | p.1 + p.2 ≤ x - a} = (μ ∗ ν) (Set.Iic (x - a)) := by
    -- Proof comment: rewrite the smoothed left-ray event on the product space.
    rw [Measure.conv, Measure.map_apply (measurable_fst.add measurable_snd) measurableSet_Iic]
    rfl
  have hrect :
      (μ.prod ν) (Set.Iic x ×ˢ (Set.univ : Set ℝ)) = μ (Set.Iic x) := by
    -- Proof comment: the unsmoothed left-ray event ignores the second coordinate.
    rw [Measure.prod_prod]
    simp
  have htail :
      (μ.prod ν) ((Set.univ : Set ℝ) ×ˢ Set.Iic (-a)) = ν (Set.Iic (-a)) := by
    -- Proof comment: the second covering event is exactly the left tail of the comparison law.
    rw [Measure.prod_prod]
    simp
  have hle_enn :
      (μ ∗ ν) (Set.Iic (x - a)) ≤ μ (Set.Iic x) + ν (Set.Iic (-a)) := by
    -- Proof comment: cover the shifted smoothed left ray by the unsmoothed left ray and the left
    -- tail of the comparison coordinate.
    rw [← hconv, ← hrect, ← htail]
    exact le_trans (measure_mono (smoothingLeftShiftEventCover x a)) (measure_union_le _ _)
  have hsum_ne_top :
      μ (Set.Iic x) + ν (Set.Iic (-a)) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top ν _⟩
  have hle_real :
      ((μ ∗ ν) (Set.Iic (x - a))).toReal ≤ (μ (Set.Iic x)).toReal + (ν (Set.Iic (-a))).toReal := by
    have htmp :
        ((μ ∗ ν) (Set.Iic (x - a))).toReal ≤ (μ (Set.Iic x) + ν (Set.Iic (-a))).toReal := by
      exact (ENNReal.toReal_le_toReal (measure_ne_top (μ ∗ ν) _) hsum_ne_top).2 hle_enn
    simpa [ENNReal.toReal_add, measure_ne_top μ _, measure_ne_top ν _] using htmp
  simpa [ProbabilityTheory.cdf_eq_real, MeasureTheory.Measure.real_def] using hle_real

/-- Helper for Theorem 15.51: a once-Gaussian-smoothed left ray at a left shift is controlled by
the unsmoothed cdf plus the standard Gaussian left tail. -/
private lemma gaussianSmoothedCdf_sub_le_cdf_add_leftTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x a : ℝ) :
    cdf (μ ∗ gaussianReal 0 1) (x - a) ≤
      cdf μ x + (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-a)) := by
  -- Proof comment: this is the Gaussian specialization of the general convolved left-tail
  -- comparison.
  simpa using
    convolvedCdf_sub_le_cdf_add_leftTail (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x a
/-- Helper for Theorem 15.51: comparing an unsmoothed cdf gap with a common once-smoothed
comparison surface produces an exact pointwise bridge, but it still carries the two one-sided
tails of the smoothing law. -/
private lemma shiftedSmoothingBridge_compare
    (μ ν κ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (x a : ℝ) (ha : 0 ≤ a) :
    |cdf μ x - cdf ν x| ≤
      |cdf (μ ∗ κ) (x + a) - cdf (ν ∗ κ) (x + a)| +
        |cdf (μ ∗ κ) (x - a) - cdf (ν ∗ κ) (x - a)| +
        (cdf (ν ∗ κ) (x + a) - cdf (ν ∗ κ) (x - a)) +
        κ.real (Set.Ioi a) +
        κ.real (Set.Iic (-a)) := by
  let A : ℝ := cdf μ x
  let B : ℝ := cdf ν x
  let Cp : ℝ := cdf (μ ∗ κ) (x + a)
  let Dp : ℝ := cdf (ν ∗ κ) (x + a)
  let Cm : ℝ := cdf (μ ∗ κ) (x - a)
  let Dm : ℝ := cdf (ν ∗ κ) (x - a)
  let R : ℝ := κ.real (Set.Ioi a)
  let L : ℝ := κ.real (Set.Iic (-a))
  have hA_upper : A ≤ Cp + R := by
    -- Proof comment: move `cdf μ x` to the smoothed right endpoint and pay the smoothing right
    -- tail.
    simpa [A, Cp, R] using cdf_le_convolvedCdf_add_rightTail (μ := μ) (ν := κ) x a
  have hB_upper : B ≤ Dp + R := by
    -- Proof comment: apply the same right-shift comparison to the comparator law `ν`.
    simpa [B, Dp, R] using cdf_le_convolvedCdf_add_rightTail (μ := ν) (ν := κ) x a
  have hA_lower : Cm ≤ A + L := by
    -- Proof comment: the left-shifted smoothed law of `μ` sits below the unsmoothed cdf plus the
    -- smoothing left tail.
    simpa [A, Cm, L] using convolvedCdf_sub_le_cdf_add_leftTail (μ := μ) (ν := κ) x a
  have hB_lower : Dm ≤ B + L := by
    -- Proof comment: the same left-tail comparison holds for the comparator law `ν`.
    simpa [B, Dm, L] using convolvedCdf_sub_le_cdf_add_leftTail (μ := ν) (ν := κ) x a
  have hWindow_nonneg : 0 ≤ Dp - Dm := by
    -- Proof comment: the smoothed comparator cdf is monotone, and `x - a ≤ x + a` because
    -- `a ≥ 0`.
    refine sub_nonneg.mpr ?_
    dsimp [Dp, Dm]
    exact ProbabilityTheory.monotone_cdf (μ := ν ∗ κ) (by linarith)
  have hR_nonneg : 0 ≤ R := by
    positivity
  have hL_nonneg : 0 ≤ L := by
    positivity
  have hUpper :
      A - B ≤ |Cp - Dp| + (Dp - Dm) + R + L := by
    have hCp : Cp - Dp ≤ |Cp - Dp| := by
      exact le_abs_self (Cp - Dp)
    linarith
  have hLower :
      B - A ≤ |Cm - Dm| + (Dp - Dm) + R + L := by
    have hCm : Dm - Cm ≤ |Cm - Dm| := by
      simpa [abs_sub_comm] using le_abs_self (Dm - Cm)
    linarith
  have hUpperSum :
      A - B ≤ |Cp - Dp| + |Cm - Dm| + (Dp - Dm) + R + L := by
    linarith [hUpper, abs_nonneg (Cm - Dm)]
  have hLowerSum :
      B - A ≤ |Cp - Dp| + |Cm - Dm| + (Dp - Dm) + R + L := by
    linarith [hLower, abs_nonneg (Cp - Dp)]
  have hAbs :
      |A - B| ≤ |Cp - Dp| + |Cm - Dm| + (Dp - Dm) + R + L := by
    refine abs_le.mpr ?_
    constructor
    · linarith
    · exact hUpperSum
  simpa [A, B, Cp, Dp, Cm, Dm, R, L] using hAbs

/-- Helper for Theorem 15.51: comparing an unsmoothed cdf gap with the once-smoothed Gaussian gap
at the two shifted endpoints produces an exact pointwise bridge, but it still carries the two
one-sided Gaussian smoothing tails. -/
private lemma gaussianEsseenShiftedSmoothingBridge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x a : ℝ) (ha : 0 ≤ a) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      |cdf (μ ∗ gaussianReal 0 1) (x + a) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + a)| +
        |cdf (μ ∗ gaussianReal 0 1) (x - a) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - a)| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + a) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - a)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi a) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-a)) := by
  -- Proof comment: specialize the generic shifted smoothing bridge to the Gaussian comparator and
  -- Gaussian smoothing kernel.
  simpa using
    shiftedSmoothingBridge_compare
      (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) (κ := (gaussianReal 0 1 : Measure ℝ))
      x a ha
/-- Helper for Theorem 15.51: after specializing the shifted smoothing bridge to `a = 1 / T`, the
Gaussian comparator window contributes the expected `O(T⁻¹)` term; the only remaining obstruction
is the pair of one-sided Gaussian smoothing tails. -/
private lemma gaussianEsseenShiftedSmoothingBridge_le_invCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| +
        |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| +
        (2 / Real.sqrt (2 * Real.pi)) / T +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  have hbridge :=
    gaussianEsseenShiftedSmoothingBridge (μ := μ) x T⁻¹ (by positivity : 0 ≤ T⁻¹)
  have hwindow :=
    gaussianSmoothedStandardGaussianCdfWindow_le_invCutoff x T hT (1 : NNReal)
  -- Proof comment: specialize the shifted smoothing bridge to `a = T⁻¹` and replace the Gaussian
  -- comparator window increment by the explicit `O(T⁻¹)` bound.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| +
          |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          simpa using hbridge
    _ ≤
        |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| +
          |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| +
          (2 / Real.sqrt (2 * Real.pi)) / T +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          gcongr
/-- Helper for Theorem 15.51: the shifted Gaussian smoothing bridge does lift to `sSup`, but only
with two shifted smoothed-cdf terms and the explicit one-sided Gaussian tails still present. -/
private lemma gaussianEsseenShiftedSmoothingSupBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T) :
    sSup (Set.range fun x : ℝ ↦ |cdf μ x - cdf (gaussianReal 0 1) x|) ≤
      2 *
          sSup
            (Set.range fun x : ℝ ↦
              |cdf (μ ∗ gaussianReal 0 1) x -
                  cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x|) +
        (2 / Real.sqrt (2 * Real.pi)) / T +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  let S : Set ℝ :=
    Set.range fun x : ℝ ↦
      |cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x|
  have hSBdd : BddAbove S := by
    refine ⟨2, ?_⟩
    rintro y ⟨x, rfl⟩
    have hμ_nonneg : 0 ≤ cdf (μ ∗ gaussianReal 0 1) x := ProbabilityTheory.cdf_nonneg _ _
    have hν_nonneg :
        0 ≤ cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x := by
      exact ProbabilityTheory.cdf_nonneg _ _
    have hμ_one : cdf (μ ∗ gaussianReal 0 1) x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
    have hν_one :
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x ≤ 1 := by
      exact ProbabilityTheory.cdf_le_one _ _
    calc
      |cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| ≤
        |cdf (μ ∗ gaussianReal 0 1) x| +
          |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| := by
            simpa using
              (abs_sub_le
                (cdf (μ ∗ gaussianReal 0 1) x)
                0
                (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x))
      _ = cdf (μ ∗ gaussianReal 0 1) x +
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x := by
            rw [abs_of_nonneg hμ_nonneg, abs_of_nonneg hν_nonneg]
      _ ≤ 2 := by
            linarith
  -- Proof comment: lift the pointwise shifted bridge to `sSup`, bounding each shifted smoothed
  -- term by the same supremum because both shifts stay inside the same range set.
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨x, rfl⟩
  have hpoint := gaussianEsseenShiftedSmoothingBridge_le_invCutoff (μ := μ) hT x
  have hplus : |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| ≤ sSup S := by
    exact le_csSup hSBdd ⟨x + T⁻¹, rfl⟩
  have hminus : |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| ≤ sSup S := by
    exact le_csSup hSBdd ⟨x - T⁻¹, rfl⟩
  dsimp [S] at hplus hminus
  linarith
/-- Helper for Theorem 15.51: the remaining owner-level bridge should package the direct Esseen
smoothing inequality on the Fourier quotient/window surface, with only the Gaussian `O(T⁻¹)`
remainder left outside the integral term. -/
private lemma gaussianSmoothedFourierInvDifferenceIntegral_le_two
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    ∫ y in Set.Iic x,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume ≤
      2 := by
  let f : ℝ → ℂ := fun y ↦
    ((gaussianSmoothedDensity μ 1 y).toReal : ℂ) -
      ((gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal : ℂ)
  have hRewrite :
      (∫ y in Set.Iic x,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume) =
        ∫ y in Set.Iic x, ‖f y‖ ∂volume := by
    simpa [f] using
      congrArg
        (fun g : ℝ → ℂ ↦ ∫ y in Set.Iic x, ‖g y‖ ∂volume)
        (gaussianSmoothedDensityDifference_eq_fourierInv_dampedScaledCharFunSub (μ := μ)).symm
  have hμ_int :
      Integrable (fun y ↦ (gaussianSmoothedDensity μ 1 y).toReal)
        (volume.restrict (Set.Iic x)) := by
    simpa using (integrable_gaussianSmoothedDensityToReal (μ := μ) (hε := one_ne_zero)).integrableOn
  have hGauss_int :
      Integrable (fun y ↦ (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal)
        (volume.restrict (Set.Iic x)) := by
    simpa using
      (integrable_gaussianSmoothedDensityToReal
        (μ := (gaussianReal 0 1 : Measure ℝ)) (hε := one_ne_zero)).integrableOn
  have hNormInt :
      Integrable (fun y ↦ ‖f y‖) (volume.restrict (Set.Iic x)) := by
    exact (hμ_int.ofReal.sub hGauss_int.ofReal).norm
  have hSumInt :
      Integrable
        (fun y ↦
          (gaussianSmoothedDensity μ 1 y).toReal +
            (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal)
        (volume.restrict (Set.Iic x)) := by
    exact hμ_int.add hGauss_int
  have hNorm_le :
      ∫ y in Set.Iic x, ‖f y‖ ∂volume ≤
        ∫ y in Set.Iic x,
          (gaussianSmoothedDensity μ 1 y).toReal +
            (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume := by
    -- Proof comment: bound the norm of the density difference by the sum of the two nonnegative
    -- smoothed densities pointwise on the left ray.
    refine
      MeasureTheory.setIntegral_mono_on hNormInt hSumInt measurableSet_Iic ?_
    intro y hy
    have hμ_nonneg : 0 ≤ (gaussianSmoothedDensity μ 1 y).toReal := ENNReal.toReal_nonneg
    have hGauss_nonneg :
        0 ≤ (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal := ENNReal.toReal_nonneg
    calc
      ‖f y‖ =
          |(gaussianSmoothedDensity μ 1 y).toReal -
              (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal| := by
            simpa [f] using
              complexNorm_ofRealSub_eq_abs
                (a := (gaussianSmoothedDensity μ 1 y).toReal)
                (b := (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal)
      _ ≤ |(gaussianSmoothedDensity μ 1 y).toReal| +
            |(gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal| := by
            simpa using
              (abs_sub_le
                (gaussianSmoothedDensity μ 1 y).toReal
                0
                (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal)
      _ =
          (gaussianSmoothedDensity μ 1 y).toReal +
            (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal := by
            rw [abs_of_nonneg hμ_nonneg, abs_of_nonneg hGauss_nonneg]
  have hSumRewrite :
      ∫ y in Set.Iic x,
          (gaussianSmoothedDensity μ 1 y).toReal +
            (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume =
        cdf (μ ∗ gaussianReal 0 1) x +
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x := by
    -- Proof comment: split the left-ray density integral and identify each piece with the
    -- corresponding smoothed cdf.
    rw [MeasureTheory.integral_add hμ_int hGauss_int]
    rw [gaussianSmoothedLaw_cdf_eq_setIntegral (μ := μ) (hε := one_ne_zero) x]
    rw [gaussianSmoothedLaw_cdf_eq_setIntegral
      (μ := (gaussianReal 0 1 : Measure ℝ)) (hε := one_ne_zero) x]
  calc
    ∫ y in Set.Iic x,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume =
      ∫ y in Set.Iic x, ‖f y‖ ∂volume := hRewrite
    _ ≤ ∫ y in Set.Iic x,
          (gaussianSmoothedDensity μ 1 y).toReal +
            (gaussianSmoothedDensity (gaussianReal 0 1) 1 y).toReal ∂volume := hNorm_le
    _ = cdf (μ ∗ gaussianReal 0 1) x +
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x := hSumRewrite
    _ ≤ 2 := by
          have hμ_one : cdf (μ ∗ gaussianReal 0 1) x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
          have hGauss_one :
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x ≤ 1 := by
            exact ProbabilityTheory.cdf_le_one _ _
          linarith

/-- Helper for Theorem 15.51: the once-smoothed Fourier inversion surface already controls the two
shifted Gaussian-smoothed cdf values that appear in the owner-level shifted smoothing bridge. -/
private lemma cdfGap_le_quotientWindowIntegral_add_gaussianCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (x : ℝ) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (∫ y in Set.Iic (x + T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume) +
        (∫ y in Set.Iic (x - T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume) +
        (2 / Real.sqrt (2 * Real.pi)) / T +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  -- Route correction: stop asking the raw sinc/window estimate to prove a cdf theorem. The file's
  -- executable owner surface is the once-smoothed Gaussian/Fourier bridge, so plug that into the
  -- already proved shifted smoothing comparison.
  have hShift := gaussianEsseenShiftedSmoothingBridge_le_invCutoff (μ := μ) hT x
  have hPlus :
      |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| ≤
        ∫ y in Set.Iic (x + T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
    exact gaussianSmoothedCdfDifference_le_fourierInvDifferenceIntegral (μ := μ) (x + T⁻¹)
  have hMinus :
      |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| ≤
        ∫ y in Set.Iic (x - T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
    exact gaussianSmoothedCdfDifference_le_fourierInvDifferenceIntegral (μ := μ) (x - T⁻¹)
  linarith

/-- Helper for Theorem 15.51: once the pointwise truncated-sign bridge is available, taking the
supremum over `x` gives the owner-level direct Esseen smoothing bound. -/
private lemma gaussianEsseenDirectSmoothingSupBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T) :
    sSup (Set.range fun x : ℝ ↦ |cdf μ x - cdf (gaussianReal 0 1) x|) ≤
      2 *
          sSup
            (Set.range fun x : ℝ ↦
              ∫ y in Set.Iic x,
                ‖𝓕⁻ (fun s : ℝ ↦
                    (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                      Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume) +
        (2 / Real.sqrt (2 * Real.pi)) / T +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  let R : Set ℝ :=
    Set.range fun x : ℝ ↦
      ∫ y in Set.Iic x,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume
  have hRBdd : BddAbove R := by
    refine ⟨2, ?_⟩
    rintro y ⟨x, rfl⟩
    exact gaussianSmoothedFourierInvDifferenceIntegral_le_two (μ := μ) x
  -- Proof comment: the shifted smoothing comparison is now controlled by the once-smoothed
  -- Fourier surface at the two shifted endpoints, and both lie under the same supremum.
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨x, rfl⟩
  have hPoint := cdfGap_le_quotientWindowIntegral_add_gaussianCutoff (μ := μ) hT x
  have hPlus :
      ∫ y in Set.Iic (x + T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume ≤
        sSup R := by
    exact le_csSup hRBdd ⟨x + T⁻¹, rfl⟩
  have hMinus :
      ∫ y in Set.Iic (x - T⁻¹),
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μ (-2 * Real.pi * s) - charFun (gaussianReal 0 1) (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume ≤
        sSup R := by
    exact le_csSup hRBdd ⟨x - T⁻¹, rfl⟩
  dsimp [R] at hPlus hMinus
  linarith

/-- Helper for Theorem 15.51: every direct Esseen smoothing surface is bounded below by the
Gaussian cutoff term alone, because the quotient integral is nonnegative. -/
private lemma gaussianEsseenDirectSurface_ge_cutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (hQuotientInt :
      IntervalIntegrable
        (fun t ↦ ((charFun μ t - charFun (gaussianReal 0 1) t) / t : ℂ))
        volume (-T) T) :
    (2 / Real.sqrt (2 * Real.pi)) / T ≤
      (1 / (2 * Real.pi)) *
          (∫ t in -T..T, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖) +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hIntegral_nonneg :
      0 ≤ ∫ t in -T..T, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖ := by
    -- Proof comment: the quotient integrand is a norm, so its symmetric interval integral is
    -- nonnegative.
    exact
      intervalIntegral.integral_nonneg (by linarith)
        (fun _ _ ↦ norm_nonneg _)
  have hPrefactor_nonneg :
      0 ≤
        (1 / (2 * Real.pi)) *
          (∫ t in -T..T, ‖(charFun μ t - charFun (gaussianReal 0 1) t) / t‖) := by
    -- Proof comment: multiply the nonnegative quotient integral by the positive Esseen constant.
    exact mul_nonneg (by positivity) hIntegral_nonneg
  linarith

/-- Helper for Theorem 15.51: the cutoff coefficient at scale `c = 1 / 2` already exceeds the
final Berry--Esseen constant `0.8`. -/
private lemma halfScaleCutoffCoefficient_gt_target :
    (0.8 : ℝ) < (2 / Real.sqrt (2 * Real.pi)) / (1 / 2 : ℝ) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) := by
    positivity
  have hsqrt_lt_three : Real.sqrt (2 * Real.pi) < 3 := by
    -- Proof comment: `π < 4` gives `2π < 8 < 9`, so the denominator is strictly below `3`.
    nlinarith [Real.pi_lt_four, hsqrt_nonneg,
      Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)]
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
    positivity
  have hrewrite :
      (2 / Real.sqrt (2 * Real.pi)) / (1 / 2 : ℝ) = 4 / Real.sqrt (2 * Real.pi) := by
    field_simp [hsqrt_pos.ne']
    ring
  rw [hrewrite]
  have htarget : (0.8 : ℝ) = 4 / 5 := by
    norm_num
  rw [htarget]
  refine (lt_div_iff₀ hsqrt_pos).2 ?_
  nlinarith [hsqrt_lt_three]

/-- Helper for Theorem 15.51: on the natural cutoff window, the already proved proxy/Gaussian
majorant together with the Gaussian cutoff contribute at most the explicit stale constant
`(1 / (2π) + 2 / √(2π)) * β / √n`. -/
private lemma berryEsseenNaturalWindowProxyAndCutoffBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
    ((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
      absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let Tn : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  have hβ : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale is already known to dominate `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hTn_nonneg : 0 ≤ Tn := by
    -- Proof comment: the natural cutoff is nonnegative because both `√n` and `β⁻¹` are.
    dsimp [Tn]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hProxyIntegral :
      ∫ t in -Tn..Tn, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) ≤
        1 / (n : ℝ) := by
    -- Proof comment: the weighted proxy/Gaussian contribution is already integrated explicitly.
    exact proxyGaussianWeightedMajorantIntegral_le_one_div (n := n) hTn_nonneg
  have hProxyTerm :
      (1 / (2 * Real.pi)) *
          (∫ t in -Tn..Tn, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))) ≤
        (1 / (2 * Real.pi)) * (1 / (n : ℝ)) := by
    -- Proof comment: multiply the proxy-integral bound by the positive Esseen prefactor.
    exact mul_le_mul_of_nonneg_left hProxyIntegral (by positivity)
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast n.2
  have hsqrt_ge_one : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hn_ge_one
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hInvSqrt_le_one : (Real.sqrt (n : ℝ))⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hsqrt_ge_one
  have hOneDivNat_le_invSqrt :
      1 / (n : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
    -- Proof comment: write `1 / n` as `1 / √n * 1 / √n`, then use `1 / √n ≤ 1`.
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    calc
      1 / (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ := by
        field_simp [hsqrt_ne]
        rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hInvSqrt_le_one (inv_nonneg.mpr (le_of_lt hsqrt_pos))
      _ = (Real.sqrt (n : ℝ))⁻¹ := by ring
  have hOneDivNat_le_scaled :
      1 / (n : ℝ) ≤ β / Real.sqrt (n : ℝ) := by
    -- Proof comment: the natural third-moment scale `β` is at least `1`.
    calc
      1 / (n : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := hOneDivNat_le_invSqrt
      _ ≤ β * (Real.sqrt (n : ℝ))⁻¹ := by
        simpa [one_mul] using
          (mul_le_mul_of_nonneg_right hβ (inv_nonneg.mpr (le_of_lt hsqrt_pos)))
      _ = β / Real.sqrt (n : ℝ) := by
        rw [div_eq_mul_inv]
  have hProxyScaled :
      (1 / (2 * Real.pi)) * (1 / (n : ℝ)) ≤
        (1 / (2 * Real.pi)) * (β / Real.sqrt (n : ℝ)) := by
    -- Proof comment: transport the previous scalar inequality through the positive prefactor.
    exact mul_le_mul_of_nonneg_left hOneDivNat_le_scaled (by positivity)
  have hCutoff :
      (2 / Real.sqrt (2 * Real.pi)) / Tn =
        (2 / Real.sqrt (2 * Real.pi)) * (β / Real.sqrt (n : ℝ)) := by
    -- Proof comment: the natural cutoff `Tn = √n / β` rewrites the Gaussian term exactly.
    simpa [β, Tn, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      berryEsseenCutoffAtNaturalWindow P X hX_iid hX_mean hX_var hX_third n
  -- Proof comment: combine the proxy-integral estimate with the exact natural-cutoff rewrite.
  calc
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn, |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
        (1 / (2 * Real.pi)) * (1 / (n : ℝ)) +
          (2 / Real.sqrt (2 * Real.pi)) / Tn := by
          exact add_le_add hProxyTerm le_rfl
    _ ≤ (1 / (2 * Real.pi)) * (β / Real.sqrt (n : ℝ)) +
          (2 / Real.sqrt (2 * Real.pi)) / Tn := by
          exact add_le_add hProxyScaled le_rfl
    _ = ((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
          (β / Real.sqrt (n : ℝ)) := by
          rw [hCutoff]
          ring
    _ = ((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
          absoluteMoment (X 1) 3 P /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
          simpa [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 15.51: on the natural cutoff window, the proof now reduces the full
quotient-window term to the residual law-majorant integral plus the already closed
proxy-and-cutoff contribution. -/
private lemma berryEsseenNaturalWindowEstimate
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let lawMajorant : ℝ → ℝ := fun t ↦
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn, ‖(charFun μn t - charFun (gaussianReal 0 1) t) / t‖) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
    (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, lawMajorant t) +
      (((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let Tn : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let lawMajorant : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
  let proxyMajorant : ℝ → ℝ := fun t ↦
    |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  have hSplit :
      ∫ t in -Tn..Tn, ‖(charFun μn t - charFun (gaussianReal 0 1) t) / t‖ ≤
        ∫ t in -Tn..Tn, lawMajorant t + proxyMajorant t := by
    -- Proof comment: the established split-majorant theorem already controls the quotient integral
    -- by the sum of the law/proxy and proxy/Gaussian majorants.
    simpa [μn, β, Tn, lawMajorant, proxyMajorant] using
      standardizedLawGaussianQuotientIntegral_le_splitMajorant
        P X hX_iid hX_mean hX_var hX_third n
  have hMajorantSplit :
      ∫ t in -Tn..Tn, lawMajorant t + proxyMajorant t =
        (∫ t in -Tn..Tn, lawMajorant t) + ∫ t in -Tn..Tn, proxyMajorant t := by
    -- Proof comment: separate the two continuous majorants so the already closed proxy/Gaussian
    -- contribution can be consumed as a black box.
    have hLawInt : IntervalIntegrable lawMajorant volume (-Tn) Tn := by
      exact Continuous.intervalIntegrable (μ := volume) (a := -Tn) (b := Tn)
        (by continuity : Continuous lawMajorant)
    have hProxyInt : IntervalIntegrable proxyMajorant volume (-Tn) Tn := by
      exact Continuous.intervalIntegrable (μ := volume) (a := -Tn) (b := Tn)
        (by continuity : Continuous proxyMajorant)
    simpa using intervalIntegral.integral_add hLawInt hProxyInt
  have hProxyAndCutoff :
      (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, proxyMajorant t) +
        (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
      ((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
    -- Proof comment: the proxy/Gaussian part is already completely quantified by the new helper.
    simpa [β, Tn, proxyMajorant] using
      berryEsseenNaturalWindowProxyAndCutoffBound
        P X hX_iid hX_mean hX_var hX_third n
  have hReduced :
      (1 / (2 * Real.pi)) *
          (∫ t in -Tn..Tn, ‖(charFun μn t - charFun (gaussianReal 0 1) t) / t‖) +
        (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
      (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, lawMajorant t) +
        (((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
          absoluteMoment (X 1) 3 P /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
    -- Proof comment: after splitting the majorant integral, only the law/proxy term remains
    -- outside the already closed proxy/Gaussian contribution.
    calc
      (1 / (2 * Real.pi)) *
          (∫ t in -Tn..Tn, ‖(charFun μn t - charFun (gaussianReal 0 1) t) / t‖) +
        (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
          (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, lawMajorant t + proxyMajorant t) +
            (2 / Real.sqrt (2 * Real.pi)) / Tn := by
            exact add_le_add (mul_le_mul_of_nonneg_left hSplit (by positivity)) le_rfl
      _ = (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, lawMajorant t) +
            ((1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, proxyMajorant t) +
              (2 / Real.sqrt (2 * Real.pi)) / Tn) := by
            rw [hMajorantSplit]
            ring
      _ ≤ (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, lawMajorant t) +
            (((1 / (2 * Real.pi)) + (2 / Real.sqrt (2 * Real.pi))) *
              absoluteMoment (X 1) 3 P /
                (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
            exact add_le_add le_rfl hProxyAndCutoff
  -- Proof comment: the current natural-window route is now completely reduced to the explicit
  -- law-majorant term plus the closed proxy-and-cutoff coefficient.
  exact hReduced

/-- Helper for Theorem 15.51: convolving both laws with `gaussianReal 0 1` multiplies their
characteristic-function difference by the common Gaussian factor `exp (-(t²) / 2)`. -/
private lemma smoothedQuotientKernel_eq_dampedKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ((charFun (μ ∗ gaussianReal 0 1) t -
        charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) / t : ℂ) =
      (((charFun μ t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) := by
  have hGauss :
      charFun (gaussianReal (0 : ℝ) (1 : NNReal)) t =
        Complex.exp (-(t ^ (2 : ℕ) / 2)) := by
    simpa using
      (ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) t)
  -- Proof comment: rewrite each smoothed characteristic function as a convolution product and
  -- factor out the common Gaussian characteristic function.
  rw [MeasureTheory.charFun_conv, MeasureTheory.charFun_conv, hGauss]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Helper for Theorem 15.51: the damped quotient-kernel integrability hypothesis transfers to the
once-smoothed characteristic-function difference surface by the convolution rewrite above. -/
private lemma smoothedQuotientKernel_intervalIntegrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ}
    (hDampedInt :
      IntervalIntegrable
        (fun t ↦
          (((charFun μ t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
        volume (-T) T) :
    IntervalIntegrable
      (fun t ↦
        ((charFun (μ ∗ gaussianReal 0 1) t -
            charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) / t : ℂ))
      volume (-T) T := by
  -- Proof comment: transfer interval integrability across the exact convolution/damping
  -- normalization of the quotient kernel.
  refine hDampedInt.congr ?_
  intro t ht
  symm
  exact smoothedQuotientKernel_eq_dampedKernel (μ := μ) t

/-- Helper for Theorem 15.51: once the quotient comparison is generalized to two probability
laws, the shifted sinc averages of the once-smoothed law and the once-smoothed Gaussian comparator
are controlled directly by the damped quotient kernel of the original law. -/
private lemma smoothedShiftedSincAverageDifference_le_dampedQuotientWindowIntegral
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) (hr : 0 < r)
    (hDampedInt :
      IntervalIntegrable
        (fun t ↦
          (((charFun μ t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
        volume (-r) r) :
    |∫ y, Real.sinc (r * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
        ∫ y, Real.sinc (r * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| ≤
      (1 / 2) *
        ∫ t in -r..r,
          ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ := by
  have hSmoothedInt :
      IntervalIntegrable
        (fun t ↦
          ((charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) / t : ℂ))
        volume (-r) r := by
    -- Proof comment: transfer the original damped quotient-kernel integrability to the once-
    -- smoothed comparison surface.
    simpa using smoothedQuotientKernel_intervalIntegrable (μ := μ) (T := r) hDampedInt
  have hCompare :=
    shiftedSincAverageDifference_le_quotientWindowIntegral_compare
      (μ := μ ∗ gaussianReal 0 1)
      (ν := ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
      x r hr hSmoothedInt
  -- Proof comment: use the generalized two-measure quotient-window comparison, then rewrite the
  -- smoothed quotient kernel back to the original damped surface pointwise.
  calc
    |∫ y, Real.sinc (r * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
        ∫ y, Real.sinc (r * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| ≤
      (1 / 2) *
        ∫ t in -r..r,
          ‖((charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) / t : ℂ)‖ :=
        hCompare
    _ = (1 / 2) *
          ∫ t in -r..r,
            ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
                Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ := by
          congr 1
          refine intervalIntegral.integral_congr_ae ?_
          refine Filter.Eventually.of_forall fun t ↦ ?_
          intro _
          rw [smoothedQuotientKernel_eq_dampedKernel (μ := μ) t]

/-- Helper for Theorem 15.51: the once-smoothed truncated Fourier window is exactly the
shifted-sinc average difference of the two smoothed comparison laws. -/
private lemma smoothedShiftedSincDifference_eq_truncatedFourierWindow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) (hT : 0 < T) :
    ∫ t in -T..T,
        (charFun (μ ∗ gaussianReal 0 1) t -
            charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I) =
      ((2 * T : ℝ) : ℂ) *
        (((∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
            ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) :
              ℝ) : ℂ)) := by
  let A : ℝ := ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1)
  let B : ℝ := ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
  let h : ℝ → ℂ := fun t ↦
    (charFun (μ ∗ gaussianReal 0 1) t -
        charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
      Complex.exp (((-x) * t : ℝ) * Complex.I)
  have hμ :
      ∫ t in -T..T,
          charFun (μ ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
        (2 * T : ℂ) * ((A : ℝ) : ℂ) := by
    -- Proof comment: rewrite the shifted window integral for the once-smoothed law as its
    -- corresponding shifted-sinc average.
    simpa [A] using
      integral_shiftedCharFunWindow_eq_sincAverage (μ := μ ∗ gaussianReal 0 1) x T hT
  have hGauss :
      ∫ t in -T..T,
          charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t *
            Complex.exp (((-x) * t : ℝ) * Complex.I) =
        (2 * T : ℂ) * ((B : ℝ) : ℂ) := by
    -- Proof comment: the same shifted-window rewrite holds for the once-smoothed Gaussian
    -- comparator.
    simpa [B] using
      integral_shiftedCharFunWindow_eq_sincAverage
        (μ := ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x T hT
  have hIntμ :
      IntervalIntegrable
        (fun t ↦
          charFun (μ ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-T) T := by
    -- Proof comment: the shifted characteristic-function integrand is continuous on the compact
    -- window.
    refine Continuous.intervalIntegrable ?_ (-T) T
    fun_prop
  have hIntGauss :
      IntervalIntegrable
        (fun t ↦
          charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t *
            Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-T) T := by
    -- Proof comment: the same continuity argument applies to the smoothed Gaussian comparator.
    refine Continuous.intervalIntegrable ?_ (-T) T
    fun_prop
  -- Proof comment: subtract the two shifted-window identities and factor the common `2 * T`
  -- coefficient into the difference of the two shifted-sinc averages.
  calc
    ∫ t in -T..T, h t =
        ((2 * T : ℝ) : ℂ) * (((A - B : ℝ) : ℂ)) := by
          simp only [h, sub_mul]
          rw [intervalIntegral.integral_sub hIntμ hIntGauss, hμ, hGauss]
          simp [A, B, Complex.ofReal_sub, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc, mul_add, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ((2 * T : ℝ) : ℂ) *
          (((∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) : ℝ) : ℂ)) := by
          simp [A, B]

/-- Helper for Theorem 15.51: the once-smoothed truncated Fourier window norm is exactly `2 * T`
times the absolute shifted-sinc average gap on the smoothed comparison surface. -/
private lemma smoothedTruncatedWindowNorm_eq_twoMul_absSincGap
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (x : ℝ) :
    let D : ℝ :=
      ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
        ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
    ‖∫ t in -T..T,
        (charFun (μ ∗ gaussianReal 0 1) t -
            charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I)‖ =
      (2 * T) * |D| := by
  let D : ℝ :=
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
  -- Proof comment: rewrite the truncated Fourier window as the once-smoothed shifted-sinc
  -- difference and collapse the complex norm to the real absolute value of the sinc gap.
  rw [smoothedShiftedSincDifference_eq_truncatedFourierWindow (μ := μ) x T hT]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < 2 * T)]

/-- Helper for Theorem 15.51: the once-smoothed truncated Fourier window for two smoothed
comparison laws is exactly the shifted-sinc average difference of those two smoothed laws. -/
private lemma smoothedShiftedSincDifference_eq_truncatedFourierWindow_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x T : ℝ) (hT : 0 < T) :
    ∫ t in -T..T,
        (charFun (μ ∗ gaussianReal 0 1) t -
            charFun (ν ∗ gaussianReal 0 1) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I) =
      ((2 * T : ℝ) : ℂ) *
        (((∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
            ∫ y, Real.sinc (T * (y - x)) ∂(ν ∗ gaussianReal 0 1) : ℝ) : ℂ)) := by
  let A : ℝ := ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1)
  let B : ℝ := ∫ y, Real.sinc (T * (y - x)) ∂(ν ∗ gaussianReal 0 1)
  let h : ℝ → ℂ := fun t ↦
    (charFun (μ ∗ gaussianReal 0 1) t - charFun (ν ∗ gaussianReal 0 1) t) *
      Complex.exp (((-x) * t : ℝ) * Complex.I)
  have hμ :
      ∫ t in -T..T,
          charFun (μ ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
        (2 * T : ℂ) * ((A : ℝ) : ℂ) := by
    -- Proof comment: rewrite the shifted window integral for the once-smoothed law `μ` as its
    -- corresponding shifted-sinc average.
    simpa [A] using
      integral_shiftedCharFunWindow_eq_sincAverage (μ := μ ∗ gaussianReal 0 1) x T hT
  have hν :
      ∫ t in -T..T,
          charFun (ν ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I) =
        (2 * T : ℂ) * ((B : ℝ) : ℂ) := by
    -- Proof comment: the same shifted-window rewrite holds for the once-smoothed comparison law
    -- `ν`.
    simpa [B] using
      integral_shiftedCharFunWindow_eq_sincAverage (μ := ν ∗ gaussianReal 0 1) x T hT
  have hIntμ :
      IntervalIntegrable
        (fun t ↦
          charFun (μ ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-T) T := by
    -- Proof comment: the shifted characteristic-function integrand for `μ` is continuous on the
    -- compact frequency window.
    refine Continuous.intervalIntegrable ?_ (-T) T
    fun_prop
  have hIntν :
      IntervalIntegrable
        (fun t ↦
          charFun (ν ∗ gaussianReal 0 1) t * Complex.exp (((-x) * t : ℝ) * Complex.I))
        volume (-T) T := by
    -- Proof comment: the same continuity argument applies to the once-smoothed comparison law
    -- `ν`.
    refine Continuous.intervalIntegrable ?_ (-T) T
    fun_prop
  -- Proof comment: subtract the two shifted-window identities and factor the common `2 * T`
  -- coefficient into the difference of the two shifted-sinc averages.
  calc
    ∫ t in -T..T, h t =
        ((2 * T : ℝ) : ℂ) * (((A - B : ℝ) : ℂ)) := by
          simp only [h, sub_mul]
          rw [intervalIntegral.integral_sub hIntμ hIntν, hμ, hν]
          simp [A, B, Complex.ofReal_sub, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc, mul_add, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ((2 * T : ℝ) : ℂ) *
          (((∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂(ν ∗ gaussianReal 0 1) : ℝ) : ℂ)) := by
          simp [A, B]

/-- Helper for Theorem 15.51: the compare-version once-smoothed truncated Fourier window norm is
exactly `2 * T` times the absolute shifted-sinc average gap on the smoothed comparison surface. -/
private lemma smoothedTruncatedWindowNorm_eq_twoMul_absSincGap_compare
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    let D : ℝ :=
      ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
        ∫ y, Real.sinc (T * (y - x)) ∂(ν ∗ gaussianReal 0 1)
    ‖∫ t in -T..T,
        (charFun (μ ∗ gaussianReal 0 1) t -
            charFun (ν ∗ gaussianReal 0 1) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I)‖ =
      (2 * T) * |D| := by
  let D : ℝ :=
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * (y - x)) ∂(ν ∗ gaussianReal 0 1)
  -- Proof comment: rewrite the compare-version truncated Fourier window as the exact smoothed
  -- shifted-sinc gap and then collapse the complex norm to the corresponding real absolute value.
  rw [smoothedShiftedSincDifference_eq_truncatedFourierWindow_compare
    (μ := μ) (ν := ν) x T hT]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < 2 * T)]

/-- Helper for Theorem 15.51: the truncated-window prefactor `1 / (2 * π * T)` matches the
canonical sinc-surface prefactor `1 / π` after the `2 * T` normalization is substituted. -/
private lemma smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv
    {T D : ℝ} (hT : 0 < T) :
    (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) = (1 / Real.pi) * |D| := by
  -- Proof comment: clear the positive cutoff scale `T` from the truncated-window normalization.
  field_simp [Real.pi_ne_zero, ne_of_gt hT]

/-- Helper for Theorem 15.51: on the exact once-smoothed comparison surface, the truncated-window
integral vanishes identically for the standard Gaussian law. -/
private lemma smoothedTruncatedWindowSurface_eq_zero_of_standardGaussian
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    ‖∫ t in -T..T,
        (charFun ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1) t -
            charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I)‖ = 0 := by
  -- Proof comment: on the standard Gaussian law the two once-smoothed comparison surfaces agree
  -- pointwise, so the truncated-window integrand is identically zero.
  simp

/-- Helper for Theorem 15.51: translating a law by `-x` commutes with one more convolution by the
standard Gaussian. -/
private lemma map_sub_const_conv_standardGaussian_eq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    (μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1 =
      (μ ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - x) := by
  have hTranslate :
      μ.map (fun y : ℝ ↦ y - x) = Measure.dirac (-x) ∗ μ := by
    -- Proof comment: translating by `-x` is convolution with the Dirac mass at `-x`.
    simpa [sub_eq_add_neg, add_comm] using (Measure.dirac_conv (-x) μ).symm
  -- Proof comment: after rewriting the translation as a Dirac convolution, associativity moves
  -- the deterministic shift to the outside of the once-smoothed law.
  calc
    (μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1
        = (Measure.dirac (-x) ∗ μ) ∗ gaussianReal 0 1 := by
            rw [hTranslate]
    _ = Measure.dirac (-x) ∗ (μ ∗ gaussianReal 0 1) := by
          rw [Measure.conv_assoc]
    _ = (μ ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - x) := by
          simpa [sub_eq_add_neg, add_comm] using
            (Measure.dirac_conv (-x) (μ ∗ gaussianReal 0 1))

/-- Helper for Theorem 15.51: after translating the standard Gaussian by `-x`, the once-smoothed
Gaussian comparator still changes by at most `O(T⁻¹)` on `[-T⁻¹, T⁻¹]`. -/
private lemma translatedStandardGaussianSmoothedCdfWindow_le_invCutoff
    (x T : ℝ) (hT : 0 < T) :
    cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹) ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hRewrite :
      (((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1) =
        ((((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)).map (fun y : ℝ ↦ y - x)) := by
    -- Proof comment: the translated Gaussian comparator is the translated once-smoothed Gaussian.
    simpa using
      map_sub_const_conv_standardGaussian_eq (μ := (gaussianReal 0 1 : Measure ℝ)) x
  -- Proof comment: rewrite both translated endpoints back to the centered variance-two Gaussian
  -- window at center `x`, then invoke the existing Gaussian window estimate.
  rw [hRewrite]
  rw [cdf_map_sub_const_eq_cdf_add (μ := ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
      x (T⁻¹)]
  rw [cdf_map_sub_const_eq_cdf_add (μ := ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
      x (-T⁻¹)]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    gaussianSmoothedStandardGaussianCdfWindow_le_invCutoff x T hT (1 : NNReal)

/-- Helper for Theorem 15.51: moving a once-smoothed cdf evaluation by at most `T⁻¹` changes it by
at most the standard `O(T⁻¹)` cutoff term. -/
private lemma smoothedCdf_shift_abs_le_invCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T δ : ℝ} (hT : 0 < T)
    (hδ : |δ| ≤ T⁻¹) (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| ≤
      (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hWindow := gaussianSmoothedCdfWindow_le_invCutoff (μ := μ) x T hT
  have hδ_left : -T⁻¹ ≤ δ := by
    have hδ' : -T⁻¹ ≤ δ ∧ δ ≤ T⁻¹ := by simpa [abs_le] using hδ
    exact hδ'.1
  have hδ_right : δ ≤ T⁻¹ := by
    have hδ' : -T⁻¹ ≤ δ ∧ δ ≤ T⁻¹ := by simpa [abs_le] using hδ
    exact hδ'.2
  by_cases hδ_nonneg : 0 ≤ δ
  · have hmono_center :
        cdf (μ ∗ gaussianReal 0 1) x ≤ cdf (μ ∗ gaussianReal 0 1) (x + δ) := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    have hmono_right :
        cdf (μ ∗ gaussianReal 0 1) (x + δ) ≤ cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    have hmono_left :
        cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) ≤ cdf (μ ∗ gaussianReal 0 1) x := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    -- Proof comment: for a nonnegative shift, the local increment is dominated by the full
    -- once-smoothed window increment on `[x - T⁻¹, x + T⁻¹]`.
    rw [abs_of_nonneg (sub_nonneg.mpr hmono_center)]
    linarith
  · have hδ_nonpos : δ ≤ 0 := le_of_not_ge hδ_nonneg
    have hmono_center :
        cdf (μ ∗ gaussianReal 0 1) (x + δ) ≤ cdf (μ ∗ gaussianReal 0 1) x := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    have hmono_right :
        cdf (μ ∗ gaussianReal 0 1) x ≤ cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    have hmono_left :
        cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) ≤ cdf (μ ∗ gaussianReal 0 1) (x + δ) := by
      exact ProbabilityTheory.monotone_cdf (μ := μ ∗ gaussianReal 0 1) (by linarith)
    -- Proof comment: for a nonpositive shift, the same full-window increment controls the local
    -- drop after reversing the subtraction.
    rw [abs_of_nonpos (sub_nonpos.mpr hmono_center)]
    linarith

/-- Helper for Theorem 15.51: any shifted once-smoothed cdf gap with `|δ| ≤ T⁻¹` can be recentered
at `x` by paying one explicit cutoff term for each of the two smoothed laws. -/
private lemma smoothedCdfGap_shift_le_center_add_twoCutoffs
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T δ : ℝ} (hT : 0 < T)
    (hδ : |δ| ≤ T⁻¹) (x : ℝ) :
    |cdf (μ ∗ gaussianReal 0 1) (x + δ) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| ≤
      |cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
        2 * ((2 / Real.sqrt (2 * Real.pi)) / T) := by
  have hμShift :=
    smoothedCdf_shift_abs_le_invCutoff (μ := μ) hT hδ x
  have hGaussShift :=
    smoothedCdf_shift_abs_le_invCutoff (μ := (gaussianReal 0 1 : Measure ℝ)) hT hδ x
  have hTriangleOuter :
      |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
          (cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ))| ≤
        |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)| +
          |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
    -- Proof comment: apply the triangle inequality once to separate the last shifted Gaussian
    -- increment from the centered gap.
    have hLower :
        -(|(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)| +
          |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)|) ≤
          (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) +
            (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)) := by
      nlinarith [neg_abs_le ((cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
        (cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)),
        neg_abs_le (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ))]
    have hUpper :
        (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) +
            (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)) ≤
          |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
              (cdf (μ ∗ gaussianReal 0 1) x -
                cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)| +
            |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
      nlinarith [le_abs_self ((cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
        (cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)),
        le_abs_self (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ))]
    exact abs_le.mpr ⟨hLower, hUpper⟩
  have hTriangleInner :
      |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
          (cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)| ≤
        |cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
          |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| := by
    -- Proof comment: apply the triangle inequality once more to separate the centered gap from
    -- the local shift of the once-smoothed law.
    have hLower :
        -(|cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
          |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x|) ≤
          (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) := by
      nlinarith [neg_abs_le (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x),
        neg_abs_le (cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)]
    have hUpper :
        (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
            (cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) ≤
          |cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
            |cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| := by
      nlinarith [le_abs_self (cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x),
        le_abs_self (cdf (μ ∗ gaussianReal 0 1) x -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)]
    exact abs_le.mpr ⟨hLower, hUpper⟩
  -- Proof comment: insert the centered once-smoothed cdf gap between the two shifted endpoints
  -- and bound the two resulting local shifts by the previously proved cutoff estimate.
  calc
    |cdf (μ ∗ gaussianReal 0 1) (x + δ) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| =
      |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
          (cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ))| := by
          ring_nf
    _ ≤
        |cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
          |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
          calc
            |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
                (cdf (μ ∗ gaussianReal 0 1) x -
                  cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x) +
                (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
                  cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ))| ≤
                |(cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x) +
                    (cdf (μ ∗ gaussianReal 0 1) x -
                      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x)| +
                  |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
                    cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
                  exact hTriangleOuter
            _ ≤
                (|cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
                    |cdf (μ ∗ gaussianReal 0 1) x -
                      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x|) +
                  |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
                    cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
                  exact add_le_add hTriangleInner le_rfl
            _ =
                |cdf (μ ∗ gaussianReal 0 1) (x + δ) - cdf (μ ∗ gaussianReal 0 1) x| +
                  |cdf (μ ∗ gaussianReal 0 1) x -
                    cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
                  |cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x -
                    cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + δ)| := by
                  ring
    _ ≤
        (2 / Real.sqrt (2 * Real.pi)) / T +
          |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          (2 / Real.sqrt (2 * Real.pi)) / T := by
          exact add_le_add (add_le_add hμShift le_rfl) (by
            simpa [abs_sub_comm] using hGaussShift)
    _ =
        |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          2 * ((2 / Real.sqrt (2 * Real.pi)) / T) := by
          ring

/-- Helper for Theorem 15.51: the centered once-smoothed sinc surface is the actual owner-level
pointwise smoothing bridge. -/
private lemma cdfGap_le_twoMul_centeredSmoothedGap_add_tailBundle
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (x : ℝ) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      2 *
          |cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
        5 * ((2 / Real.sqrt (2 * Real.pi)) / T) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  have hShift :=
    gaussianEsseenShiftedSmoothingBridge_le_invCutoff (μ := μ) hT x
  have hδPlus : |T⁻¹| ≤ T⁻¹ := by
    rw [abs_of_pos (by positivity : 0 < T⁻¹)]
  have hδMinus : |-T⁻¹| ≤ T⁻¹ := by
    simpa using hδPlus
  have hPlus :
      |cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| ≤
        |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          2 * ((2 / Real.sqrt (2 * Real.pi)) / T) := by
    -- Proof comment: recenter the right-shifted once-smoothed cdf gap at `x`.
    simpa using
      smoothedCdfGap_shift_le_center_add_twoCutoffs
        (μ := μ) (T := T) (δ := T⁻¹) hT hδPlus x
  have hMinus :
      |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)| ≤
        |cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          2 * ((2 / Real.sqrt (2 * Real.pi)) / T) := by
    -- Proof comment: the same recentering estimate controls the left-shifted smoothed gap.
    simpa using
      smoothedCdfGap_shift_le_center_add_twoCutoffs
        (μ := μ) (T := T) (δ := -T⁻¹) hT hδMinus x
  -- Proof comment: this packages the entire currently proved coarse route. It is useful as a
  -- negative certificate: the existing shifted-endpoint API still spends four extra cutoff terms
  -- and the two one-sided Gaussian tails, so it cannot close the desired centered theorem.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (|cdf (μ ∗ gaussianReal 0 1) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹)| +
          |cdf (μ ∗ gaussianReal 0 1) (x - T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)|) +
          (2 / Real.sqrt (2 * Real.pi)) / T +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          simpa [add_assoc, add_left_comm, add_comm] using hShift
    _ ≤
        (|cdf (μ ∗ gaussianReal 0 1) x -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          2 * ((2 / Real.sqrt (2 * Real.pi)) / T)) +
          (|cdf (μ ∗ gaussianReal 0 1) x -
              cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
            2 * ((2 / Real.sqrt (2 * Real.pi)) / T)) +
          (2 / Real.sqrt (2 * Real.pi)) / T +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          gcongr
    _ =
        2 *
            |cdf (μ ∗ gaussianReal 0 1) x -
                cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x| +
          5 * ((2 / Real.sqrt (2 * Real.pi)) / T) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          ring

/-- Helper for Theorem 15.51: the truncated-window surface is the actual owner-level same-`x`
pointwise smoothing bridge. -/
private lemma translatedCdfSubAtZero_le_shiftedSmoothedUpper_addGaussianWindowAndTails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹)| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  let A : ℝ := cdf μShift 0
  let B : ℝ := cdf νShift 0
  let Cp : ℝ := cdf (μShift ∗ gaussianReal 0 1) (T⁻¹)
  let Dp : ℝ := cdf (νShift ∗ gaussianReal 0 1) (T⁻¹)
  let Dm : ℝ := cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)
  let R : ℝ := (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹))
  let L : ℝ := (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹))
  have hA_upper : A ≤ Cp + R := by
    -- Proof comment: move the translated law to the once-smoothed right endpoint and pay the
    -- Gaussian right tail.
    simpa [A, Cp, R, μShift] using
      cdf_le_convolvedCdf_add_rightTail
        (μ := μShift) (ν := (gaussianReal 0 1 : Measure ℝ)) 0 T⁻¹
  have hB_lower : Dm ≤ B + L := by
    -- Proof comment: compare the translated Gaussian left endpoint back to the unsmoothed cdf and
    -- pay the Gaussian left tail.
    simpa [B, Dm, L, νShift] using
      convolvedCdf_sub_le_cdf_add_leftTail
        (μ := νShift) (ν := (gaussianReal 0 1 : Measure ℝ)) 0 T⁻¹
  have hCompare : Cp - Dp ≤ |Cp - Dp| := by
    -- Proof comment: discard the sign of the shifted smoothed gap at the right endpoint.
    exact le_abs_self (Cp - Dp)
  -- Proof comment: combine the right-shift control for `μ`, the left-shift control for the
  -- translated Gaussian comparator, and the comparator window between the two Gaussian endpoints.
  linarith

/-- Helper for Theorem 15.51: the reverse one-sided translated cdf gap is controlled by the left
shifted smoothed gap, the translated Gaussian comparator window, and the Gaussian tails. -/
private lemma translatedCdfSubAtZero_reverse_le_shiftedSmoothedLower_addGaussianWindowAndTails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
        cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  let A : ℝ := cdf μShift 0
  let B : ℝ := cdf νShift 0
  let Cm : ℝ := cdf (μShift ∗ gaussianReal 0 1) (-T⁻¹)
  let Dp : ℝ := cdf (νShift ∗ gaussianReal 0 1) (T⁻¹)
  let Dm : ℝ := cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)
  let R : ℝ := (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹))
  let L : ℝ := (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹))
  have hB_upper : B ≤ Dp + R := by
    -- Proof comment: move the translated Gaussian cdf to the once-smoothed right endpoint and pay
    -- the Gaussian right tail.
    simpa [B, Dp, R, νShift] using
      cdf_le_convolvedCdf_add_rightTail
        (μ := νShift) (ν := (gaussianReal 0 1 : Measure ℝ)) 0 T⁻¹
  have hA_lower : Cm ≤ A + L := by
    -- Proof comment: compare the translated law's once-smoothed left endpoint back to the
    -- unsmoothed cdf and pay the Gaussian left tail.
    simpa [A, Cm, L, μShift] using
      convolvedCdf_sub_le_cdf_add_leftTail
        (μ := μShift) (ν := (gaussianReal 0 1 : Measure ℝ)) 0 T⁻¹
  have hCompare : Dm - Cm ≤ |Cm - Dm| := by
    -- Proof comment: discard the sign of the shifted smoothed gap at the left endpoint.
    simpa [abs_sub_comm] using le_abs_self (Dm - Cm)
  -- Proof comment: combine the shifted Gaussian upper control, the shifted translated-law lower
  -- control, and the translated Gaussian comparator window.
  linarith

/-- Helper for Theorem 15.51: translating both laws to the origin commutes with the generic
shifted smoothing bridge, so the coarse shifted-endpoint surface can be specialized without
repeating the directional decomposition. -/
private lemma translatedOriginShiftedSmoothingBridge_compare
    (μ ν κ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 - cdf (ν.map (fun y : ℝ ↦ y - x)) 0| ≤
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ κ)) (T⁻¹) -
          cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ κ)) (T⁻¹)| +
        |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ κ)) (-T⁻¹) -
            cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ κ)) (-T⁻¹)| +
        (cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ κ)) (T⁻¹) -
          cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ κ)) (-T⁻¹)) +
        κ.real (Set.Ioi (T⁻¹)) +
        κ.real (Set.Iic (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := ν.map (fun y : ℝ ↦ y - x)
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) ν)
  -- Proof comment: specialize the generic shifted smoothing bridge at the translated origin with
  -- shift size `T⁻¹`; this records the entire stale surface in one reusable compare theorem.
  simpa [μShift, νShift] using
    shiftedSmoothingBridge_compare
      (μ := μShift) (ν := νShift) (κ := κ) 0 T⁻¹ (by positivity : 0 ≤ T⁻¹)

/-- Helper for Theorem 15.51: combining the two directional translated smoothing inequalities gives
the absolute translated cdf gap, still on the stale shifted-endpoint surface with Gaussian tails.
-/
private lemma translatedCdfGapAtZero_le_shiftedSmoothedPair_addGaussianWindowAndTails
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹)| +
        |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  -- Proof comment: the stale translated Gaussian theorem is just the generic translated compare
  -- bridge specialized to the Gaussian comparator and Gaussian smoothing law.
  simpa using
    translatedOriginShiftedSmoothingBridge_compare
      (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) (κ := (gaussianReal 0 1 : Measure ℝ))
      hT x

/-- Helper for Theorem 15.51: after translating both laws to the origin, the once-smoothed cdf
gap is already controlled by the exact compare-version inverse-Fourier surface at `0`. -/
private lemma translatedGaussianOriginFourierWindowBridge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0| ≤
      ∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  have hBase :
      |cdf (μShift ∗ gaussianReal 0 1) 0 - cdf (νShift ∗ gaussianReal 0 1) 0| ≤
        ∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μShift (-2 * Real.pi * s) - charFun νShift (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := by
    -- Proof comment: specialize the compare-version smoothed cdf/Fourier bridge exactly at the
    -- translated laws and the origin.
    simpa [μShift, νShift] using
      smoothedCdfDifference_le_fourierInvDifferenceIntegral_compare
        (μ := μShift) (ν := νShift) 0
  have hKernel :
      (fun s : ℝ ↦
          (charFun μShift (-2 * Real.pi * s) - charFun νShift (-2 * Real.pi * s)) *
            Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) =
        (fun s : ℝ ↦
            charFun (μShift ∗ gaussianReal 0 1) (-2 * Real.pi * s) -
              charFun (νShift ∗ gaussianReal 0 1) (-2 * Real.pi * s)) := by
    funext s
    have hGauss :
        charFun (gaussianReal (0 : ℝ) (1 : NNReal)) (-2 * Real.pi * s) =
          Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2)) := by
      -- Proof comment: evaluate the standard Gaussian characteristic function directly at the
      -- scaled negative frequency and normalize the exponent.
      have hGaussBase :
          charFun (gaussianReal (0 : ℝ) (1 : NNReal)) (-2 * Real.pi * s) =
            Complex.exp (-(((-2 * Real.pi * s) ^ (2 : ℕ)) / 2)) := by
        simpa using
          (ProbabilityTheory.charFun_gaussianReal
            (μ := (0 : ℝ)) (v := (1 : NNReal)) (-2 * Real.pi * s))
      have hExp :
          (((-2 * Real.pi * s : ℝ) ^ (2 : ℕ)) / 2) = (2 * Real.pi ^ 2 : ℝ) * s ^ 2 := by
        ring_nf
      have hExpNeg :
          -(((-2 * Real.pi * s : ℝ) ^ (2 : ℕ)) / 2) = -((2 * Real.pi ^ 2 : ℝ) * s ^ 2) := by
        exact congrArg Neg.neg hExp
      have hExpNegC :
          -(((-2 * Real.pi * s : ℂ) ^ (2 : ℕ)) / 2) =
            -((((2 * Real.pi ^ 2 : ℝ) : ℂ) * (s : ℂ) ^ (2 : ℕ))) := by
        exact_mod_cast hExpNeg
      calc
        charFun (gaussianReal (0 : ℝ) (1 : NNReal)) (-2 * Real.pi * s) =
            Complex.exp (-(((-2 * Real.pi * s) ^ (2 : ℕ)) / 2)) := hGaussBase
        _ = Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2)) := by
              exact congrArg Complex.exp hExpNegC
    -- Proof comment: rewrite both once-smoothed characteristic functions as convolution products
    -- and factor out the common Gaussian multiplier.
    rw [MeasureTheory.charFun_conv, MeasureTheory.charFun_conv, hGauss]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add,
      mul_assoc, mul_left_comm, mul_comm]
  have hRewrite :
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              (charFun μShift (-2 * Real.pi * s) - charFun νShift (-2 * Real.pi * s)) *
                Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume) =
        ∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (μShift ∗ gaussianReal 0 1) (-2 * Real.pi * s) -
                charFun (νShift ∗ gaussianReal 0 1) (-2 * Real.pi * s)) y‖ ∂volume := by
    -- Proof comment: once the Fourier kernels match pointwise, the left-ray inverse-Fourier
    -- integral matches verbatim.
    exact congrArg
      (fun f : ℝ → ℂ ↦ ∫ y in Set.Iic 0, ‖𝓕⁻ f y‖ ∂volume)
      hKernel
  calc
    |cdf (μShift ∗ gaussianReal 0 1) 0 - cdf (νShift ∗ gaussianReal 0 1) 0| ≤
      ∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            (charFun μShift (-2 * Real.pi * s) - charFun νShift (-2 * Real.pi * s)) *
              Complex.exp (-((2 * Real.pi ^ 2 : ℝ) * s ^ 2))) y‖ ∂volume := hBase
    _ =
      ∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (μShift ∗ gaussianReal 0 1) (-2 * Real.pi * s) -
              charFun (νShift ∗ gaussianReal 0 1) (-2 * Real.pi * s)) y‖ ∂volume := hRewrite

/-- Helper for Theorem 15.51: the upper one-sided translated once-smoothed cdf gap at the origin
is controlled by the same left-ray inverse-Fourier surface as the absolute translated gap. -/
private lemma translatedSmoothedCdfSubAtZero_le_fourierWindow_compare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 ≤
      ∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume := by
  have hAbs := translatedGaussianOriginFourierWindowBridge (μ := μ) x
  -- Proof comment: the positive one-sided gap is bounded by its absolute value, so the proved
  -- absolute translated Fourier bridge immediately supplies the directional estimate.
  exact le_trans (le_abs_self _) hAbs

/-- Helper for Theorem 15.51: the reverse one-sided translated once-smoothed cdf gap at the
origin is controlled by the same left-ray inverse-Fourier surface as the absolute translated gap.
-/
private lemma translatedSmoothedCdfSubAtZero_reverse_le_fourierWindow_compare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
        cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 ≤
      ∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume := by
  have hAbs := translatedGaussianOriginFourierWindowBridge (μ := μ) x
  -- Proof comment: the reverse one-sided gap is the negative of the forward difference, and the
  -- absolute translated Fourier bridge again dominates it.
  have hNeg :
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
          cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 ≤
        |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              0| := by
    -- Proof comment: rewrite the reverse difference as the negative of the forward one before
    -- bounding it by the absolute value.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (neg_le_abs
        (cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) 0 -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            0))
  exact le_trans hNeg hAbs

/-- Helper for Theorem 15.51: evaluating the translated once-smoothed comparison gap at an
endpoint `a` is the same as evaluating the same smoothed comparison at the origin after shifting
the translation parameter from `x` to `x + a`. -/
private lemma translatedSmoothedCdfGapAt_eq_originGap_shifted
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x a : ℝ) :
    |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) a -
        cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) a| =
      |cdf (((μ.map (fun y : ℝ ↦ y - (x + a))) ∗ gaussianReal 0 1)) 0 -
          cdf (((ν.map (fun y : ℝ ↦ y - (x + a))) ∗ gaussianReal 0 1)) 0| := by
  have hμx :
      ((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1) =
        (μ ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - x) := by
    -- Proof comment: move the outer Gaussian smoothing through the translated law once.
    simpa using map_sub_const_conv_standardGaussian_eq (μ := μ) x
  have hνx :
      ((ν.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1) =
        (ν ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - x) := by
    -- Proof comment: the same translation/smoothing commutation holds for the comparison law.
    simpa using map_sub_const_conv_standardGaussian_eq (μ := ν) x
  have hμxa :
      ((μ.map (fun y : ℝ ↦ y - (x + a))) ∗ gaussianReal 0 1) =
        (μ ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - (x + a)) := by
    -- Proof comment: apply the same commutation rule after shifting the translation parameter.
    simpa using map_sub_const_conv_standardGaussian_eq (μ := μ) (x + a)
  have hνxa :
      ((ν.map (fun y : ℝ ↦ y - (x + a))) ∗ gaussianReal 0 1) =
        (ν ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - (x + a)) := by
    -- Proof comment: again commute translation and smoothing for the comparison law `ν`.
    simpa using map_sub_const_conv_standardGaussian_eq (μ := ν) (x + a)
  -- Proof comment: after rewriting both smoothed translated laws as translated smoothed laws, the
  -- endpoint `a` becomes the origin for the translation parameter `x + a`.
  rw [hμx, hνx, hμxa, hνxa]
  rw [cdf_map_sub_const_eq_cdf_add (μ := μ ∗ gaussianReal 0 1) x a]
  rw [cdf_map_sub_const_eq_cdf_add (μ := ν ∗ gaussianReal 0 1) x a]
  rw [cdf_map_sub_const_eq_cdf_add (μ := μ ∗ gaussianReal 0 1) (x + a) 0]
  rw [cdf_map_sub_const_eq_cdf_add (μ := ν ∗ gaussianReal 0 1) (x + a) 0]
  ring_nf

/-- Helper for Theorem 15.51: the exact translated once-smoothed comparison window is just the
centered once-smoothed comparison window with the expected oscillatory phase factor. -/
private lemma translatedSmoothedCompareWindow_eq_centeredPhaseWindow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    ∫ t in -T..T,
        (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
            charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
              gaussianReal 0 1)) t) =
      ∫ t in -T..T,
        (charFun (μ ∗ gaussianReal 0 1) t -
            charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
          Complex.exp (((-x) * t : ℝ) * Complex.I) := by
  have hμ :
      ((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1) =
        (μ ∗ gaussianReal 0 1).map (fun y : ℝ ↦ y - x) := by
    -- Proof comment: commute the outer Gaussian smoothing through the translated input law once.
    simpa using map_sub_const_conv_standardGaussian_eq (μ := μ) x
  have hν :
      ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) =
        (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)).map (fun y : ℝ ↦ y - x) := by
    -- Proof comment: the translated Gaussian comparator obeys the same smoothing/translation
    -- commutation rule.
    simpa using
      map_sub_const_conv_standardGaussian_eq (μ := (gaussianReal 0 1 : Measure ℝ)) x
  -- Proof comment: after rewriting both translated once-smoothed laws as translated centered
  -- once-smoothed laws, the existing phase-absorption identity applies verbatim.
  rw [hμ, hν]
  simpa using
    translatedCharFunDifferenceWindow_eq_centeredWindow
      (μ := μ ∗ gaussianReal 0 1)
      (ν := ((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) x T

/-- Helper for Theorem 15.51: the shifted translated smoothed endpoint pair and Gaussian tails
should collapse directly to the exact translated truncated-window surface. -/
private lemma translatedGaussianShiftedEndpointPair_eq_originGapPair
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹)| +
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)| =
    |cdf (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1)) 0 -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
          gaussianReal 0 1)) 0| +
      |cdf (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1)) 0 -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
            gaussianReal 0 1)) 0| := by
  -- Proof comment: rewrite each shifted endpoint gap as the corresponding translated-origin gap,
  -- once at `x + T⁻¹` and once at `x - T⁻¹`.
  rw [translatedSmoothedCdfGapAt_eq_originGap_shifted
      (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x (T⁻¹)]
  rw [translatedSmoothedCdfGapAt_eq_originGap_shifted
      (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x (-T⁻¹)]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 15.51: after the endpoint rewrite, each translated-origin gap is bounded
by its own left-ray inverse-Fourier surface. -/
private lemma translatedGaussianOriginGapPair_le_originFourierWindowPair
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    |cdf (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1)) 0 -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
          gaussianReal 0 1)) 0| +
      |cdf (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1)) 0 -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
            gaussianReal 0 1)) 0| ≤
    (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) := by
  have hPlus := translatedGaussianOriginFourierWindowBridge (μ := μ) (x + T⁻¹)
  have hMinus := translatedGaussianOriginFourierWindowBridge (μ := μ) (x - T⁻¹)
  -- Proof comment: apply the already proved translated-origin Fourier bridge separately to the
  -- two endpoint translations and add the resulting inequalities.
  linarith

/-- Helper for Theorem 15.51: the translated compare-window norm is exactly the norm of the
centered phase-window spelling. -/
private lemma translatedSmoothedCompareWindow_norm_eq_centeredPhaseNorm
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    ‖∫ t in -T..T,
        (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
            charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
              gaussianReal 0 1)) t)‖ =
      ‖∫ t in -T..T,
          (charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
            Complex.exp (((-x) * t : ℝ) * Complex.I)‖ := by
  -- Proof comment: freeze the translated compare window in the centered phase normal form once,
  -- then transport that exact equality through `norm`.
  exact congrArg norm (translatedSmoothedCompareWindow_eq_centeredPhaseWindow (μ := μ) x T)

/-- Helper for Theorem 15.51: the translated origin cdf gap is already reduced to the pair of
translated origin Fourier surfaces, the translated Gaussian comparator window, and the explicit
Gaussian tails. -/
private lemma translatedGaussianOriginGap_le_shiftedFourierPairAndComparator
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  have hShift :=
    translatedCdfGapAtZero_le_shiftedSmoothedPair_addGaussianWindowAndTails
      (μ := μ) hT x
  have hFourierPair :=
    translatedGaussianOriginGapPair_le_originFourierWindowPair (μ := μ) x T
  have hAugment :
      |cdf (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1)) 0 -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
            gaussianReal 0 1)) 0| +
        |cdf (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1)) 0 -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
              gaussianReal 0 1)) 0| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) ≤
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
    -- Proof comment: the only monotone step here is replacing each translated-origin gap by its
    -- corresponding translated-origin Fourier surface, leaving the Gaussian terms untouched.
    linarith
  -- Proof comment: rewrite the stale shifted-endpoint pair into the translated-origin pair and
  -- then substitute the already proved translated Fourier majorants for the two endpoint terms.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹)| +
        |cdf (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := hShift
    _ =
      |cdf (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1)) 0 -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
            gaussianReal 0 1)) 0| +
        |cdf (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1)) 0 -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
              gaussianReal 0 1)) 0| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
          rw [translatedGaussianShiftedEndpointPair_eq_originGapPair (μ := μ) x T]
    _ ≤
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := hAugment

/-- Helper for Theorem 15.51: once the translated-origin sinc comparison is available, the exact
translated truncated-window theorem is just its normalization corollary. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_ofSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hSinc :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  -- Local instance justification (measure transport): the normalization lemma is stated for
  -- probability measures, and translation preserves `IsProbabilityMeasure`.
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  -- Local instance justification (measure transport): the translated Gaussian comparator is still
  -- a probability measure.
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  let D : ℝ :=
    ∫ y, Real.sinc (T * y) ∂(μShift ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * y) ∂(νShift ∗ gaussianReal 0 1)
  have hWindowNorm :
      ‖∫ t in -T..T,
          (charFun (μShift ∗ gaussianReal 0 1) t -
              charFun (νShift ∗ gaussianReal 0 1) t)‖ =
        (2 * T) * |D| := by
    -- Proof comment: on the translated compare surface at `x = 0`, the exact truncated-window
    -- norm is exactly `2 * T` times the translated sinc gap.
    simpa [D] using
      (smoothedTruncatedWindowNorm_eq_twoMul_absSincGap_compare
        (μ := μShift) (ν := νShift) (hT := hT) 0)
  -- Proof comment: after normalizing the translated sinc gap to the exact truncated-window norm,
  -- the theorem is purely scalar algebra.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) * |D| +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
          simpa [μShift, νShift, D] using hSinc
    _ = (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
          rw [← smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv
            (T := T) (D := D) hT]
    _ = (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μShift ∗ gaussianReal 0 1) t -
                  charFun (νShift ∗ gaussianReal 0 1) t)‖ +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
          rw [hWindowNorm]
    _ = (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
          simp [μShift, νShift]

/-- Helper for Theorem 15.51: an exact translated-origin sinc comparison immediately yields the
translated truncated-window bridge with the explicit Gaussian cutoff term. -/
private lemma translatedGaussianOriginGaussianCutoffCompare_ofSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hSinc :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hCompare :=
    translatedGaussianOriginTruncatedWindowCompare_ofSincCompare
      (μ := μ) hT x hSinc
  have hWindow := translatedStandardGaussianSmoothedCdfWindow_le_invCutoff x T hT
  -- Proof comment: first normalize the exact translated sinc surface to the translated
  -- truncated-window surface, then absorb the translated Gaussian comparator window into the
  -- explicit `O(T⁻¹)` cutoff bound.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := hCompare
    _ ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
          gcongr

/-- Helper for Theorem 15.51: the centered shifted-sinc average for a once-smoothed law is
exactly the translated-origin sinc average after translating the once-smoothed law by `-x`. -/
private lemma centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) =
      ∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) := by
  rw [map_sub_const_conv_standardGaussian_eq (μ := μ) x]
  -- Proof comment: commute translation through the once-smoothed law and then rewrite the mapped
  -- sinc average back in the original coordinates.
  symm
  simpa [sub_eq_add_neg, mul_add, mul_assoc, mul_left_comm, mul_comm] using
    (MeasureTheory.integral_map
      (μ := μ ∗ gaussianReal 0 1)
      (φ := fun y : ℝ ↦ y - x)
      (f := fun y : ℝ ↦ Real.sinc (T * y))
      (measurable_id.sub measurable_const).aemeasurable
      (by
        fun_prop :
          AEStronglyMeasurable (fun y : ℝ ↦ Real.sinc (T * y))
            (Measure.map (fun y ↦ y - x) (μ ∗ gaussianReal 0 1))))

/-- Helper for Theorem 15.51: the centered once-smoothed comparator window is exactly the
translated-origin comparator window after translating the once-smoothed comparison law by `-x`. -/
private lemma centeredSmoothedCdfWindow_eq_translatedWindow
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (x T : ℝ) :
    cdf (ν ∗ gaussianReal 0 1) (x + T⁻¹) - cdf (ν ∗ gaussianReal 0 1) (x - T⁻¹) =
      cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (T⁻¹) -
        cdf (((ν.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) (-T⁻¹) := by
  rw [map_sub_const_conv_standardGaussian_eq (μ := ν) x]
  -- Proof comment: rewrite the translated comparator window back to the centered once-smoothed
  -- comparator, where the interval endpoints are `x ± T⁻¹`.
  rw [cdf_map_sub_const_eq_cdf_add (μ := ν ∗ gaussianReal 0 1) x (T⁻¹)]
  rw [cdf_map_sub_const_eq_cdf_add (μ := ν ∗ gaussianReal 0 1) x (-T⁻¹)]
  ring_nf

/-- Helper for Theorem 15.51: the reverse translated-origin cdf gap is the negative of the
forward translated-origin cdf gap. -/
private lemma translatedCdfSubAtZero_reverse_eq_neg_forward
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
        cdf (μ.map (fun y : ℝ ↦ y - x)) 0 =
      -(cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0) := by
  -- Proof comment: the reverse directional gap is just the additive inverse of the forward gap.
  ring

/-- Helper for Theorem 15.51: any centered shifted-sinc comparison on the exact Gaussian
comparator window normalizes directly to the centered phase-window surface. -/
private lemma centeredGaussianCenteredPhaseCompare_ofSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hSinc :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  let D : ℝ :=
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
  have hNorm :
      ‖∫ t in -T..T,
          (charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
            Complex.exp (((-x) * t : ℝ) * Complex.I)‖ =
        (2 * T) * |D| := by
    -- Proof comment: rewrite the centered phase-window norm exactly as the shifted-sinc gap on
    -- the once-smoothed comparison surface.
    simpa [D] using smoothedTruncatedWindowNorm_eq_twoMul_absSincGap (μ := μ) hT x
  have hScale :
      (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) = (1 / Real.pi) * |D| := by
    -- Proof comment: cancel the `2 * T` normalization from the truncated-window prefactor.
    exact smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv (T := T) (D := D) hT
  -- Proof comment: normalize the centered shifted-sinc comparison to the exact truncated-window
  -- norm and then simplify the scalar prefactor.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / Real.pi) * |D| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          simpa [D] using hSinc
    _ = (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          rw [← hScale]
    _ =
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          rw [← hNorm]

/-- Helper for Theorem 15.51: any centered phase-window comparison immediately renormalizes back
to the centered shifted-sinc surface on the same Gaussian comparator window. -/
private lemma centeredGaussianSincCompare_ofCenteredPhaseCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hPhase :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  let D : ℝ :=
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
  have hNorm :
      ‖∫ t in -T..T,
          (charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
            Complex.exp (((-x) * t : ℝ) * Complex.I)‖ =
        (2 * T) * |D| := by
    -- Proof comment: this is the same exact truncated-window/sinc normalization used in the
    -- forward direction, but now we read it from the phase-window surface back to the sinc side.
    simpa [D] using smoothedTruncatedWindowNorm_eq_twoMul_absSincGap (μ := μ) hT x
  have hScale :
      (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) = (1 / Real.pi) * |D| := by
    -- Proof comment: cancel the common `2 * T` factor after substituting the truncated-window
    -- norm.
    exact smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv (T := T) (D := D) hT
  -- Proof comment: rewrite the exact phase-window norm to the shifted-sinc normal form and
  -- simplify the scalar prefactor.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := hPhase
    _ = (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          rw [hNorm]
    _ = (1 / Real.pi) * |D| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          rw [hScale]
    _ = (1 / Real.pi) *
          |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          simp [D]

/-- Helper for Theorem 15.51: the exact translated truncated-window comparison normalizes
directly to the translated-origin sinc/comparator surface. -/
private lemma translatedGaussianOriginSincCompareOfTruncatedWindowCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCompare :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  -- Local instance justification (measure transport): the normalization lemma is stated for
  -- probability measures, and translation preserves `IsProbabilityMeasure`.
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  -- Local instance justification (measure transport): the translated Gaussian comparator remains
  -- a probability measure on the same translated compare surface.
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  let D : ℝ :=
    ∫ y, Real.sinc (T * y) ∂(μShift ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * y) ∂(νShift ∗ gaussianReal 0 1)
  have hWindowNorm :
      ‖∫ t in -T..T,
          (charFun (μShift ∗ gaussianReal 0 1) t -
              charFun (νShift ∗ gaussianReal 0 1) t)‖ =
        (2 * T) * |D| := by
    -- Proof comment: on the translated compare surface at `x = 0`, the exact truncated-window
    -- norm is exactly `2 * T` times the translated sinc gap.
    simpa [D] using
      (smoothedTruncatedWindowNorm_eq_twoMul_absSincGap_compare
        (μ := μShift) (ν := νShift) (hT := hT) 0)
  -- Proof comment: substitute the exact truncated-window/sinc normalization and simplify the
  -- scalar prefactor `1 / (2 * π * T)` to recover the translated sinc surface.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := hCompare
    _ =
      (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
          rw [hWindowNorm]
    _ =
      (1 / Real.pi) * |D| +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
          rw [smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv
            (T := T) (D := D) hT]
    _ =
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
          simp [μShift, νShift, D]

/-- Helper for Theorem 15.51: the canonical translated-origin sinc comparison is now the unique
unresolved proof object beneath the exact translated truncated-window normalization. -/
private lemma translatedGaussianOriginSincCompare_ofCenteredShiftedSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hCentered :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hGap :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
        |cdf μ x - cdf (gaussianReal 0 1) x| := by
    -- Proof comment: recentering the two cdf evaluations at the origin is exactly reversible.
    simpa using
      (cdfGap_eq_translatedCdfGapAtZero
        (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x).symm
  have hSinc :
      |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
          ∫ y, Real.sinc (T * y) ∂
            ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))| =
        |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
            ∫ y, Real.sinc (T * (y - x)) ∂
              (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| := by
    -- Proof comment: each translated once-smoothed sinc average is the centered shifted-sinc
    -- average of the corresponding untranslated once-smoothed law.
    rw [← centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
      (μ := μ) x T]
    rw [← centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
      (μ := (gaussianReal 0 1 : Measure ℝ)) x T]
  have hWindow :
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹) =
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹) := by
    -- Proof comment: the translated comparator window is exactly the centered variance-two
    -- Gaussian window evaluated at the shifted center `x`.
    simpa using
      (centeredSmoothedCdfWindow_eq_translatedWindow
        (ν := (gaussianReal 0 1 : Measure ℝ)) x T).symm
  -- Proof comment: transport the centered shifted-sinc comparison to the translated-origin
  -- spelling consumed by the downstream compare package.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
      |cdf μ x - cdf (gaussianReal 0 1) x| := hGap
    _ ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := hCentered
    _ =
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
          rw [hSinc, hWindow]

/-- Helper for Theorem 15.51: the canonical translated-origin sinc comparison is now the unique
unresolved proof object beneath the exact translated truncated-window normalization. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_ofCenteredPhaseCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hCompare :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hGap :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
        |cdf μ x - cdf (gaussianReal 0 1) x| := by
    -- Proof comment: translating both laws by `-x` moves the cdf comparison from `x` to `0`.
    simpa using
      (cdfGap_eq_translatedCdfGapAtZero
        (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x).symm
  have hNorm :
      ‖∫ t in -T..T,
          (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t)‖ =
        ‖∫ t in -T..T,
            (charFun (μ ∗ gaussianReal 0 1) t -
                charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
              Complex.exp (((-x) * t : ℝ) * Complex.I)‖ := by
    -- Proof comment: rewrite the translated exact compare window once into the centered
    -- phase-window normal form.
    exact translatedSmoothedCompareWindow_norm_eq_centeredPhaseNorm (μ := μ) x T
  have hWindow :
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹) =
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹) := by
    -- Proof comment: the translated Gaussian comparator window is the centered variance-two
    -- Gaussian window at the same center `x`.
    simpa using
      centeredSmoothedCdfWindow_eq_translatedWindow
        (ν := (gaussianReal 0 1 : Measure ℝ)) x T
  -- Proof comment: this transports the centered phase-window estimate to the exact translated
  -- truncated-window compare surface without reopening the stale shifted-endpoint route.
  calc
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
      |cdf μ x - cdf (gaussianReal 0 1) x| := hGap
    _ ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := hCompare
    _ =
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
          rw [← hNorm, hWindow]

/-- Helper for Theorem 15.51: once the centered phase-window compare theorem is available, the
translated-origin sinc theorem follows by one transport step and one exact normalization step. -/
private lemma translatedGaussianOriginSincCompare_ofCenteredPhaseCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCompare :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hTranslatedCompare :=
    translatedGaussianOriginTruncatedWindowCompare_ofCenteredPhaseCompareLocal
      (μ := μ) (x := x) hCompare
  -- Proof comment: after transporting to the exact translated compare surface, apply the exact
  -- truncated-window/sinc normalization once to reach the canonical translated-origin sinc form.
  exact
    translatedGaussianOriginSincCompareOfTruncatedWindowCompareLocal
      (μ := μ) hT x hTranslatedCompare

/-- Helper for Theorem 15.51: a centered shifted-sinc comparison already determines the exact
translated truncated-window comparison after one transport step and one exact normalization step.
-/
private lemma translatedGaussianOriginTruncatedWindowCompare_ofCenteredShiftedSincCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCentered :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hTranslatedSinc :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
    -- Proof comment: first transport the centered shifted-sinc statement to the translated-origin
    -- sinc surface that matches the exact compare normalization lemma.
    exact
      translatedGaussianOriginSincCompare_ofCenteredShiftedSincCompare
        (μ := μ) (x := x) hCentered
  -- Proof comment: once the translated-origin sinc comparison is available, the exact
  -- translated truncated-window theorem is its canonical normalization corollary.
  exact
    translatedGaussianOriginTruncatedWindowCompare_ofSincCompare
      (μ := μ) hT x hTranslatedSinc

/-- Helper for Theorem 15.51: an absolute centered cdf-gap bound immediately yields the forward
one-sided centered cdf inequality on the same comparison surface. -/
private lemma centeredCdfSub_le_of_absBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x B : ℝ)
    (hAbs : |cdf μ x - cdf (gaussianReal 0 1) x| ≤ B) :
    cdf μ x - cdf (gaussianReal 0 1) x ≤ B := by
  -- Proof comment: the forward centered cdf difference is always dominated by its absolute value.
  exact le_trans (le_abs_self _) hAbs

/-- Helper for Theorem 15.51: an absolute centered cdf-gap bound also yields the reverse
one-sided centered cdf inequality on the same comparison surface. -/
private lemma centeredCdfSub_reverse_le_of_absBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x B : ℝ)
    (hAbs : |cdf μ x - cdf (gaussianReal 0 1) x| ≤ B) :
    cdf (gaussianReal 0 1) x - cdf μ x ≤ B := by
  have hNeg :
      cdf (gaussianReal 0 1) x - cdf μ x ≤
        |cdf μ x - cdf (gaussianReal 0 1) x| := by
    -- Proof comment: the reverse centered cdf difference is the negative of the forward one.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (neg_le_abs (cdf μ x - cdf (gaussianReal 0 1) x))
  exact le_trans hNeg hAbs

/-- Helper for Theorem 15.51: matching forward and reverse centered cdf-gap bounds on one common
right-hand side packages them into the corresponding absolute centered cdf-gap estimate. -/
private lemma centeredCdfGap_abs_le_of_twoSidedBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x B : ℝ)
    (hForward : cdf μ x - cdf (gaussianReal 0 1) x ≤ B)
    (hReverse : cdf (gaussianReal 0 1) x - cdf μ x ≤ B) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤ B := by
  -- Proof comment: `abs_le` is exactly the packaging of the two one-sided centered cdf-gap
  -- inequalities against the same comparison surface.
  refine abs_le.mpr ?_
  constructor
  · linarith
  · exact hForward

/-- Helper for Theorem 15.51: matching forward and reverse translated-origin cdf-gap bounds on
one common right-hand side packages them into the corresponding absolute translated cdf-gap
estimate. -/
private lemma translatedCdfGapAtZero_abs_le_ofTwoSidedLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x B : ℝ)
    (hForward :
      cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        B)
    (hReverse :
      cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        B) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      B := by
  -- Proof comment: `abs_le` packages the two translated one-sided cdf-gap inequalities against
  -- the same right-hand side.
  refine abs_le.mpr ?_
  constructor
  · linarith
  · exact hForward

/-- Helper for Theorem 15.51: undoing the translation identifies the translated-origin sinc
comparison surface with the centered shifted-sinc surface. -/
private lemma translatedGaussianOriginSincCompareSurface_eq_centeredShifted
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    (1 / Real.pi) *
        |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
            ∫ y, Real.sinc (T * y) ∂
              ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1))| +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) =
    (1 / Real.pi) *
        |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
            ∫ y, Real.sinc (T * (y - x)) ∂
              (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
      (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  -- Proof comment: rewrite each translated once-smoothed sinc average back to the centered
  -- shifted-sinc average, then transport the translated Gaussian comparator window back to the
  -- centered variance-two Gaussian window.
  rw [← centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
    (μ := μ) x T]
  rw [← centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
    (μ := (gaussianReal 0 1 : Measure ℝ)) x T]
  rw [(centeredSmoothedCdfWindow_eq_translatedWindow
    (ν := (gaussianReal 0 1 : Measure ℝ)) x T).symm]

/-- Helper for Theorem 15.51: after recentering by `-x`, the exact translated truncated-window
right-hand side is exactly the centered phase-window right-hand side. -/
private lemma translatedGaussianOriginTruncatedWindowCompareRhs_eq_centeredPhaseRhs
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x T : ℝ) :
    (1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1)) t)‖ +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) =
    (1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun (μ ∗ gaussianReal 0 1) t -
                charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
              Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
      (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  -- Proof comment: freeze the exact compare right-hand side in one canonical centered normal
  -- form so later transport lemmas do not have to rebuild the norm and comparator-window rewrites.
  rw [translatedSmoothedCompareWindow_norm_eq_centeredPhaseNorm (μ := μ) x T]
  rw [(centeredSmoothedCdfWindow_eq_translatedWindow
    (ν := (gaussianReal 0 1 : Measure ℝ)) x T).symm]

/-- Helper for Theorem 15.51: the exact translated truncated-window surface and the centered
phase-window surface are equivalent under the fixed translation transport. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_iff_centeredPhaseCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ) :
    (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) ↔
      (|cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) := by
  constructor
  · intro hTranslated
    have hGap :
        |cdf μ x - cdf (gaussianReal 0 1) x| =
          |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
              cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := by
      -- Proof comment: recenter the cdf comparison at the origin before transporting the compare
      -- surface back to the centered `x`-phase spelling.
      simpa using
        cdfGap_eq_translatedCdfGapAtZero
          (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x
    -- Proof comment: transport the translated exact truncated-window comparison all the way back
    -- to the centered phase-window surface.
    calc
      |cdf μ x - cdf (gaussianReal 0 1) x| =
        |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := hGap
      _ ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := hTranslated
      _ =
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) :=
          translatedGaussianOriginTruncatedWindowCompareRhs_eq_centeredPhaseRhs
            (μ := μ) x T
  · intro hCentered
    have hGap :
        |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
          |cdf μ x - cdf (gaussianReal 0 1) x| := by
      -- Proof comment: translating both laws by `-x` moves the cdf comparison from `x` to `0`.
      simpa using
        (cdfGap_eq_translatedCdfGapAtZero
          (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x).symm
    -- Proof comment: this is the reverse transport direction, moving the centered phase-window
    -- inequality onto the exact translated truncated-window surface.
    calc
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| =
        |cdf μ x - cdf (gaussianReal 0 1) x| := hGap
      _ ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := hCentered
      _ =
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
            symm
            exact
              translatedGaussianOriginTruncatedWindowCompareRhs_eq_centeredPhaseRhs
                (μ := μ) x T

/-- Helper for Theorem 15.51: any exact translated truncated-window comparison transports
immediately to the centered phase-window surface at the same `x`. -/
private lemma centeredGaussianCenteredPhaseCompare_ofTranslatedTruncatedWindowLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hCompare :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  -- Proof comment: the translated exact compare surface and the centered phase-window surface are
  -- already equivalent by the frozen transport theorem, so reuse that equivalence directly.
  exact
    (translatedGaussianOriginTruncatedWindowCompare_iff_centeredPhaseCompare
      (μ := μ) (x := x)).1 hCompare

/-- Helper for Theorem 15.51: the translated exact truncated-window surface is equivalent to the
centered shifted-sinc surface once the fixed transport and exact normalization are both frozen. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_iff_centeredShiftedSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) ↔
      (|cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) := by
  constructor
  · intro hTranslated
    have hPhase :=
      (translatedGaussianOriginTruncatedWindowCompare_iff_centeredPhaseCompare
        (μ := μ) (x := x)).1 hTranslated
    -- Proof comment: first undo the fixed translation on the exact compare surface, then
    -- renormalize the centered phase-window theorem back to the shifted-sinc statement.
    exact centeredGaussianSincCompare_ofCenteredPhaseCompare (μ := μ) hT x hPhase
  · intro hCentered
    have hPhase :=
      centeredGaussianCenteredPhaseCompare_ofSincCompare (μ := μ) hT x hCentered
    -- Proof comment: normalize the centered shifted-sinc theorem to the phase-window spelling,
    -- then transport that centered theorem back to the translated exact surface.
    exact
      (translatedGaussianOriginTruncatedWindowCompare_iff_centeredPhaseCompare
        (μ := μ) (x := x)).2 hPhase

/-- Helper for Theorem 15.51: the proof-owning comparison should live on the centered exact
phase-window surface before any translated exact or shifted-sinc transport wrappers are applied.
-/
private lemma centeredGaussianCenteredPhaseCompare_ofTranslatedOriginSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hTranslatedSinc :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  have hTranslatedExact :=
    translatedGaussianOriginTruncatedWindowCompare_ofSincCompare
      (μ := μ) hT x hTranslatedSinc
  -- Proof comment: first normalize the translated-origin sinc theorem to the exact translated
  -- compare surface, then transport that exact surface straight back to the centered phase-window
  -- spelling.
  exact
    (translatedGaussianOriginTruncatedWindowCompare_iff_centeredPhaseCompare
      (μ := μ) (x := x)).1 hTranslatedExact

/-- Helper for Theorem 15.51: a translated-origin sinc/comparator comparison can always be moved
back to the centered shifted-sinc surface by undoing the fixed translation in the cdf, sinc, and
Gaussian window terms. -/
private lemma centeredShiftedSincCompare_ofTranslatedOriginSincCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hTranslated :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
  have hGap :
      |cdf μ x - cdf (gaussianReal 0 1) x| =
        |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := by
    -- Proof comment: recenter the translated-origin cdf comparison back at the original point
    -- `x` before undoing the translation on the right-hand side.
    simpa using
      cdfGap_eq_translatedCdfGapAtZero
        (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x
  have hSinc :
      |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
          ∫ y, Real.sinc (T * y) ∂
            ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))| =
        |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
            ∫ y, Real.sinc (T * (y - x)) ∂
              (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| := by
    -- Proof comment: both translated once-smoothed sinc averages are exactly the centered
    -- shifted-sinc averages after undoing the fixed translation.
    rw [centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
      (μ := μ) x T]
    rw [centeredShiftedSmoothedSincAverage_eq_translatedSmoothedSincAverage
      (μ := (gaussianReal 0 1 : Measure ℝ)) x T]
  have hWindow :
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹) =
      cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
        cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹) := by
    -- Proof comment: rewrite the translated Gaussian comparator window back to the centered
    -- variance-two Gaussian window at the same center `x`.
    simpa using
      (centeredSmoothedCdfWindow_eq_translatedWindow
        (ν := (gaussianReal 0 1 : Measure ℝ)) x T).symm
  -- Proof comment: once the cdf, sinc, and Gaussian window terms are all rewritten, the
  -- translated-origin sinc estimate is exactly the centered shifted-sinc estimate.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| =
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := hGap
    _ ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := hTranslated
    _ =
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
              ∫ y, Real.sinc (T * (y - x)) ∂
                (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
        (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
          cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹)) := by
          rw [hSinc, hWindow]

/-- Helper for Theorem 15.51: the translated-origin sinc/comparator surface is equivalent to the
centered shifted-sinc surface once the translation identities are frozen. -/
private lemma translatedGaussianOriginSincCompare_iff_centeredShiftedSincCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ) :
    (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) ↔
      (|cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) := by
  constructor
  · intro hTranslated
    -- Proof comment: undo the fixed translation to move the translated-origin sinc estimate back
    -- to the centered shifted-sinc surface.
    exact
      centeredShiftedSincCompare_ofTranslatedOriginSincCompareLocal
        (μ := μ) (x := x) hTranslated
  · intro hCentered
    -- Proof comment: transport the centered shifted-sinc comparison to the translated-origin
    -- spelling consumed by the downstream truncated-window normalization.
    exact
      translatedGaussianOriginSincCompare_ofCenteredShiftedSincCompare
        (μ := μ) (x := x) hCentered

/-- Helper for Theorem 15.51: on the stale shifted/Fourier-plus-tail surface, specializing to the
standard Gaussian kills both inverse-Fourier terms and leaves exactly the Gaussian comparator
window plus the two explicit Gaussian tails. -/
private lemma translatedShiftedFourierPairAndComparator_standardGaussian_self
    {T : ℝ} (x : ℝ) :
    (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) =
    (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
        (T⁻¹) -
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
        (-T⁻¹)) +
    (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
    (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  have hFourierInvZero : ∀ y : ℝ, 𝓕⁻ (fun s : ℝ ↦ (0 : ℂ)) y = 0 := by
    intro y
    rw [Real.fourierInv_eq']
    simp
  -- Proof comment: on the Gaussian self-comparison surface, both characteristic-function
  -- differences are identically zero, so only the explicit Gaussian window and tails remain.
  simp [hFourierInvZero]

/-- Helper for Theorem 15.51: on the exact translated truncated-window surface, specializing to
the standard Gaussian leaves only the Gaussian comparator window. -/
private lemma translatedExactCompareWindow_standardGaussian_self
    {T : ℝ} (x : ℝ) :
    (1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t)‖ +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) =
    cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
        (T⁻¹) -
      cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
        (-T⁻¹) := by
  -- Proof comment: the exact translated compare-window norm vanishes identically on the Gaussian
  -- self-comparison surface.
  simp

/-- Helper for Theorem 15.51: on the standard Gaussian, the stale shifted/Fourier surface is the
exact translated compare window plus the two explicit Gaussian tails. -/
private lemma translatedShiftedFourierSurface_standardGaussian_eq_exactCompareWindow_addTails
    {T : ℝ} (x : ℝ) :
    (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) =
    ((1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t)‖ +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹))) +
    (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
    (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  -- Proof comment: combine the two Gaussian self-specializations so the stale owner surface is
  -- recorded explicitly as the exact compare window together with the two leftover tails.
  rw [translatedShiftedFourierPairAndComparator_standardGaussian_self (T := T) x]
  rw [translatedExactCompareWindow_standardGaussian_self (T := T) x]

/-- Helper for Theorem 15.51: once the forward and reverse translated-origin exact compare
inequalities land on one common truncated-window right-hand side, `abs_le` packages them into the
desired absolute translated compare estimate. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_ofTwoSided
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hForward :
      cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)))
    (hReverse :
      cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  -- Proof comment: package the two directional translated exact compare inequalities against the
  -- same exact truncated-window right-hand side.
  exact translatedCdfGapAtZero_abs_le_ofTwoSidedLocal (μ := μ) x _ hForward hReverse

/-- Helper for Theorem 15.51: one direct absolute translated-origin exact compare bound already
contains the forward and reverse one-sided inequalities on the same common right-hand side. -/
private lemma translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x B : ℝ)
    (hAbs :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        B) :
    (cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        B) ∧
      (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        B) := by
  constructor
  · -- Proof comment: the forward translated cdf difference is bounded by the same absolute exact
    -- compare theorem on the common right-hand side.
    exact le_trans (le_abs_self _) hAbs
  · -- Proof comment: the reverse translated cdf difference is the second one-sided corollary of
    -- the same absolute exact compare theorem.
    have hNeg :
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
            cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
          |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
              cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := by
      -- Proof comment: rewrite the reverse translated cdf difference as the negative of the
      -- forward difference before applying `neg_le_abs`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (neg_le_abs
          (cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0))
    exact le_trans hNeg hAbs

/-- Helper for Theorem 15.51: the absolute translated exact compare theorem is equivalent to the
paired forward and reverse exact compare inequalities on the same canonical truncated-window
right-hand side. -/
private lemma translatedGaussianOriginExactCompare_iff_directionalBoundsLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) ↔
      ((cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
          (1 / (2 * Real.pi * T)) *
              ‖∫ t in -T..T,
                  (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                      charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                        gaussianReal 0 1)) t)‖ +
            (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
                (T⁻¹) -
              cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) (-T⁻¹))) ∧
        (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
            cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
          (1 / (2 * Real.pi * T)) *
              ‖∫ t in -T..T,
                  (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                      charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                        gaussianReal 0 1)) t)‖ +
            (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
                (T⁻¹) -
              cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) (-T⁻¹)))) := by
  let B : ℝ :=
    (1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1)) t)‖ +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹))
  constructor
  · intro hAbs
    -- Proof comment: unpack the absolute translated compare theorem into the forward and reverse
    -- directional inequalities against the same frozen right-hand side `B`.
    simpa [B] using
      translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
        (μ := μ) (x := x) (B := B) hAbs
  · rintro ⟨hForward, hReverse⟩
    -- Proof comment: once both directional inequalities land on the same exact compare surface,
    -- repack them with the standard absolute-value constructor.
    simpa [B] using
      translatedGaussianOriginTruncatedWindowCompare_ofTwoSided
        (μ := μ) (x := x) hForward hReverse

/-- Helper for Theorem 15.51: once the exact translated truncated-window comparison is available,
the translated-origin sinc/comparator theorem is only its fixed normalization corollary. -/
private lemma translatedGaussianOriginSincCompareDirect_ofExactCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCompare :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  -- Route correction: the old shifted/Fourier collapse target is false in the Gaussian self-case,
  -- so the real owner has to live on the exact translated truncated-window surface first.
  -- Proof comment: normalize the exact translated compare theorem directly to the translated-origin
  -- sinc/comparator surface and stop routing through the stale shifted/Fourier wrapper.
  exact
    translatedGaussianOriginSincCompareOfTruncatedWindowCompareLocal
      (μ := μ) hT x hCompare

/-- Helper for Theorem 15.51: the already proved stale shifted/Fourier absolute surface yields the
forward and reverse translated-origin cdf-gap bounds on that same common right-hand side. -/
private lemma translatedGaussianOriginShiftedFourierDirectionalBoundsLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
          (∫ y in Set.Iic 0,
              ‖𝓕⁻ (fun s : ℝ ↦
                  charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                      (-2 * Real.pi * s) -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                      gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹))) ∧
      (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
          (∫ y in Set.Iic 0,
              ‖𝓕⁻ (fun s : ℝ ↦
                  charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                      (-2 * Real.pi * s) -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                      gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
          (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹))) := by
  let B : ℝ :=
    (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹))
  have hAbs :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        B := by
    -- Proof comment: freeze the stale shifted/Fourier surface under one name, then read the
    -- existing absolute translated-origin theorem on exactly that right-hand side.
    simpa [B] using translatedGaussianOriginGap_le_shiftedFourierPairAndComparator (μ := μ) hT x
  -- Proof comment: once the shifted/Fourier surface is available as an absolute estimate, the
  -- forward and reverse translated-origin inequalities are immediate one-sided corollaries.
  exact
    translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
      (μ := μ) (x := x) (B := B) hAbs

/-- Helper for Theorem 15.51: after the stale shifted/Fourier surface is collapsed to the exact
translated truncated-window right-hand side, the final exact compare theorem is only the standard
two-sided packaging step. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_ofShiftedFourierCollapseLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCollapse :
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  rcases
      translatedGaussianOriginShiftedFourierDirectionalBoundsLocal
        (μ := μ) hT x with ⟨hForwardShifted, hReverseShifted⟩
  have hForward :
      cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
    -- Proof comment: compose the solved forward stale-surface estimate with the single missing
    -- monotone collapse to the exact translated compare surface.
    exact le_trans hForwardShifted hCollapse
  have hReverse :
      cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
    -- Proof comment: the reverse stale-surface bound collapses to the same exact translated
    -- compare right-hand side by the identical monotone step.
    exact le_trans hReverseShifted hCollapse
  -- Proof comment: after both one-sided inequalities share the exact translated truncated-window
  -- right-hand side, the remaining proof is the standard `abs_le` package.
  exact
    translatedGaussianOriginTruncatedWindowCompare_ofTwoSided
      (μ := μ) (x := x) hForward hReverse

/-- Helper for Theorem 15.51: on the translated-origin comparison surface, the exact truncated-
window right-hand side is exactly the corresponding sinc/comparator right-hand side. -/
private lemma translatedGaussianOriginExactCompareRhs_eq_sincCompareRhsLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) =
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  let μShift : Measure ℝ := μ.map (fun y : ℝ ↦ y - x)
  let νShift : Measure ℝ := (gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)
  -- Local instance justification (measure transport): the normalization helper works on the
  -- translated probability laws, so we reinstall those transported instances once.
  letI : IsProbabilityMeasure μShift := by
    simpa [μShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable : AEMeasurable (fun y : ℝ ↦ y - x) μ)
  -- Local instance justification (measure transport): the translated Gaussian comparator remains
  -- a probability law under translation.
  letI : IsProbabilityMeasure νShift := by
    simpa [νShift] using
      Measure.isProbabilityMeasure_map
        ((measurable_id.sub measurable_const).aemeasurable :
          AEMeasurable (fun y : ℝ ↦ y - x) (gaussianReal 0 1 : Measure ℝ))
  let D : ℝ :=
    ∫ y, Real.sinc (T * y) ∂(μShift ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * y) ∂(νShift ∗ gaussianReal 0 1)
  have hWindowNorm :
      ‖∫ t in -T..T,
          (charFun (μShift ∗ gaussianReal 0 1) t -
              charFun (νShift ∗ gaussianReal 0 1) t)‖ =
        (2 * T) * |D| := by
    -- Proof comment: on the translated compare surface at the origin, the exact truncated-window
    -- norm is exactly `2 * T` times the translated sinc gap.
    simpa [D] using
      (smoothedTruncatedWindowNorm_eq_twoMul_absSincGap_compare
        (μ := μShift) (ν := νShift) (hT := hT) 0)
  -- Proof comment: freeze the common translated compare window and normalize only the Fourier
  -- prefactor, so later exact/sinc equivalence proofs become pure rewrites.
  calc
    (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) =
      (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
            rw [hWindowNorm]
    _ = (1 / Real.pi) * |D| +
        (cdf (νShift ∗ gaussianReal 0 1) (T⁻¹) -
          cdf (νShift ∗ gaussianReal 0 1) (-T⁻¹)) := by
            rw [smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv
              (T := T) (D := D) hT]
    _ =
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
              simp [μShift, νShift, D]

/-- Helper for Theorem 15.51: on the translated-origin comparison surface, the exact truncated-
window statement and the sinc/comparator statement are equivalent by the frozen normalization
lemmas. -/
private lemma translatedGaussianOriginTruncatedWindowCompare_iff_sincCompareLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) ↔
      (|cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) := by
  constructor
  · intro hExact
    -- Proof comment: normalize the exact translated truncated-window surface to the translated-
    -- origin sinc/comparator spelling using the fixed exact-to-sinc bridge.
    rw [translatedGaussianOriginExactCompareRhs_eq_sincCompareRhsLocal (μ := μ) hT x] at hExact
    exact hExact
  · intro hSinc
    -- Proof comment: the reverse direction is the canonical sinc-to-exact normalization on the
    -- same translated-origin comparison surface.
    rw [translatedGaussianOriginExactCompareRhs_eq_sincCompareRhsLocal (μ := μ) hT x]
    exact hSinc

/-- Helper for Theorem 15.51: once the forward and reverse translated-origin exact compare bounds
share the common truncated-window right-hand side, the final translated-origin sinc/comparator
estimate is only the standard two-sided package followed by the fixed exact-to-sinc rewrite. -/
private lemma translatedGaussianOriginSincCompare_ofExactDirectionalBoundsLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hForward :
      cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)))
    (hReverse :
      cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / Real.pi) *
          |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
              ∫ y, Real.sinc (T * y) ∂
                ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                  gaussianReal 0 1))| +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hExact :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
    -- Proof comment: first package the paired exact translated compare inequalities on the common
    -- truncated-window right-hand side into the corresponding absolute-value estimate.
    exact
      translatedGaussianOriginTruncatedWindowCompare_ofTwoSided
        (μ := μ) (x := x) hForward hReverse
  -- Proof comment: once the exact translated compare theorem is packaged, rewrite the common
  -- right-hand side once to the final translated-origin sinc/comparator surface.
  exact
    (translatedGaussianOriginTruncatedWindowCompare_iff_sincCompareLocal
      (μ := μ) hT x).1 hExact

/-- Helper for Theorem 15.51: once the forward and reverse translated-origin exact compare bounds
are isolated on the same canonical right-hand side, the absolute exact frontier is just the
standard two-sided package. -/
private lemma translatedGaussianOriginExactCompareAbs_ofCenteredPhaseCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (x : ℝ)
    (hCentered :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  -- Proof comment: the translated exact compare frontier is exactly the centered phase-window
  -- owner theorem transported through the frozen translated/centered equivalence.
  exact
    translatedGaussianOriginTruncatedWindowCompare_ofCenteredPhaseCompareLocal
      (μ := μ) (x := x) hCentered

/-- Helper for Theorem 15.51: transporting a centered exact phase-window comparison to the
translated origin and unpacking its absolute-value consequence yields the paired exact translated
directional bounds on the common truncated-window surface. -/
private lemma translatedGaussianOriginExactDirectionalBounds_ofCenteredPhaseCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (x : ℝ)
    (hCentered :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    (cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) ∧
      (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) := by
  have hAbs :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹)) := by
    -- Proof comment: first transport the centered exact phase-window theorem to the exact
    -- translated truncated-window surface at the origin.
    exact
      translatedGaussianOriginExactCompareAbs_ofCenteredPhaseCompare
        (μ := μ) (x := x) hCentered
  -- Proof comment: once the translated absolute bound lands on the common right-hand side, the
  -- forward and reverse inequalities are its standard `abs_le` consequences.
  exact
    translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
      (μ := μ) (x := x)
      ((1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)))
      hAbs

/-- Helper for Theorem 15.51: on the Gaussian self-comparison surface, the stale shifted/Fourier
bound still dominates the exact compare window because the two explicit Gaussian tails remain.
This records why the old tail-free collapse cannot be the proof owner. -/
private lemma translatedShiftedFourierSurface_standardGaussian_ge_exactCompareWindow
    {T : ℝ} (x : ℝ) :
    (1 / (2 * Real.pi * T)) *
        ‖∫ t in -T..T,
            (charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t)‖ +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) ≤
    (∫ y in Set.Iic 0,
        ‖𝓕⁻ (fun s : ℝ ↦
            charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s) -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
      (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) := by
  -- Proof comment: rewrite the stale shifted/Fourier self-surface as the exact compare window
  -- plus the two Gaussian tails, then keep only the nonnegative tail contribution.
  rw [translatedShiftedFourierSurface_standardGaussian_eq_exactCompareWindow_addTails (T := T) x]
  nlinarith [MeasureTheory.measureReal_nonneg
      (μ := (gaussianReal 0 1 : Measure ℝ)) (s := Set.Ioi (T⁻¹)),
    MeasureTheory.measureReal_nonneg
      (μ := (gaussianReal 0 1 : Measure ℝ)) (s := Set.Iic (-T⁻¹))]

/-- Helper for Theorem 15.51: once the translated exact compare right-hand side is frozen at a
single real bound `B`, the paired one-sided translated inequalities are equivalent to the
corresponding absolute translated cdf-gap estimate. -/
private lemma translatedGaussianOriginExactDirectionalBounds_iff_abs
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x B : ℝ) :
    ((cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤ B) ∧
      (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤ B)) ↔
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤ B := by
  constructor
  · intro hBounds
    rcases hBounds with ⟨hForward, hReverse⟩
    -- Proof comment: package the two one-sided translated exact compare bounds into the absolute
    -- translated cdf-gap estimate on the same frozen right-hand side.
    exact translatedCdfGapAtZero_abs_le_ofTwoSidedLocal (μ := μ) x B hForward hReverse
  · intro hAbs
    -- Proof comment: unpack the absolute translated exact compare theorem back into its forward
    -- and reverse one-sided corollaries on that common right-hand side.
    exact
      translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
        (μ := μ) (x := x) (B := B) hAbs

/-- Helper for Theorem 15.51: transporting a centered shifted-sinc comparison to the translated
origin and then unpacking the resulting absolute bound gives the paired translated-origin sinc
directional inequalities on their common right-hand side. -/
private lemma translatedGaussianOriginSincDirectionalBounds_ofCenteredShiftedSincCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hCentered :
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂
                  (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x + T⁻¹) -
            cdf (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) (x - T⁻¹))) :
    (cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) ∧
      (cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
          cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
        (1 / Real.pi) *
            |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
                ∫ y, Real.sinc (T * y) ∂
                  ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1))| +
          (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (T⁻¹) -
            cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
              (-T⁻¹))) := by
  let B : ℝ :=
    (1 / Real.pi) *
        |∫ y, Real.sinc (T * y) ∂(((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) -
            ∫ y, Real.sinc (T * y) ∂
              ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1))| +
      (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (T⁻¹) -
        cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
          (-T⁻¹))
  have hAbs :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        B := by
    -- Proof comment: transport the centered shifted-sinc bound to the translated-origin sinc
    -- spelling and freeze its right-hand side under one name before unpacking the one-sided
    -- inequalities.
    simpa [B] using
      translatedGaussianOriginSincCompare_ofCenteredShiftedSincCompare
        (μ := μ) (x := x) hCentered
  -- Proof comment: once the translated-origin sinc comparison is available as one absolute bound
  -- on the frozen right-hand side `B`, the forward and reverse inequalities are the standard
  -- `abs_le` corollaries.
  exact
    translatedGaussianOriginExactCompareDirectionalBounds_ofAbs
      (μ := μ) (x := x) (B := B) hAbs

/- The stale centered/translated frontier block that used to live here depended on a circular
shifted-sinc owner and contained the last unresolved placeholder. The active proof route later in the file now
reintroduces only the one downstream theorem that is still consumed by the live Gaussian-cutoff
chain, after the translated exact owner has been proved noncircularly. -/
/-- Helper for Theorem 15.51: once the stale shifted/Fourier surface is collapsed to the exact
translated compare right-hand side, the forward one-sided translated cdf gap follows by a single
monotone step from the already proved shifted/Fourier directional bound. -/
private lemma translatedCdfSubAtZero_le_exactCompareWindow_ofShiftedFourierCollapse
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCollapse :
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) :
    cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hForwardShifted :=
    (translatedGaussianOriginShiftedFourierDirectionalBoundsLocal
      (μ := μ) hT x).1
  -- Proof comment: compose the forward shifted/Fourier directional estimate with the single
  -- right-hand-side collapse to the canonical exact translated compare surface.
  exact le_trans hForwardShifted hCollapse

/-- Helper for Theorem 15.51: the same collapsed right-hand side also controls the reverse
one-sided translated cdf gap, so the absolute translated exact theorem can be packaged from one
common collapse statement. -/
private lemma translatedCdfSubAtZero_reverse_le_exactCompareWindow_ofShiftedFourierCollapse
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ)
    (hCollapse :
      (∫ y in Set.Iic 0,
          ‖𝓕⁻ (fun s : ℝ ↦
              charFun (((μ.map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗ gaussianReal 0 1))
                  (-2 * Real.pi * s) -
                charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x + T⁻¹))) ∗
                  gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (∫ y in Set.Iic 0,
            ‖𝓕⁻ (fun s : ℝ ↦
                charFun (((μ.map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗ gaussianReal 0 1))
                    (-2 * Real.pi * s) -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - (x - T⁻¹))) ∗
                    gaussianReal 0 1)) (-2 * Real.pi * s)) y‖ ∂volume) +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Ioi (T⁻¹)) +
        (gaussianReal 0 1 : Measure ℝ).real (Set.Iic (-T⁻¹)) ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹))) :
    cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0 -
        cdf (μ.map (fun y : ℝ ↦ y - x)) 0 ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (T⁻¹) -
          cdf ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1))
            (-T⁻¹)) := by
  have hReverseShifted :=
    (translatedGaussianOriginShiftedFourierDirectionalBoundsLocal
      (μ := μ) hT x).2
  -- Proof comment: the reverse shifted/Fourier directional estimate lands on the same collapsed
  -- exact compare right-hand side by the identical monotone step.
  exact le_trans hReverseShifted hCollapse

/-- Helper for Theorem 15.51: a translated-origin cutoff comparison transports directly to the
centered phase-window cutoff surface by the frozen cdf and window identities. -/
private lemma centeredGaussianPhaseCutoff_ofTranslatedCutoffCompare
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (x : ℝ)
    (hTranslated :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (2 / Real.sqrt (2 * Real.pi)) / T) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  have hGap :
      |cdf μ x - cdf (gaussianReal 0 1) x| =
        |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
            cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := by
    -- Proof comment: translating both laws by `-x` moves the cdf comparison from `x` to `0`.
    simpa using
      cdfGap_eq_translatedCdfGapAtZero
        (μ := μ) (ν := (gaussianReal 0 1 : Measure ℝ)) x
  have hNorm :
      ‖∫ t in -T..T,
          (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
              charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                gaussianReal 0 1)) t)‖ =
        ‖∫ t in -T..T,
            (charFun (μ ∗ gaussianReal 0 1) t -
                charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
              Complex.exp (((-x) * t : ℝ) * Complex.I)‖ := by
    -- Proof comment: the translated truncated-window norm is exactly the centered phase-window
    -- norm under the frozen phase-absorption identity.
    exact translatedSmoothedCompareWindow_norm_eq_centeredPhaseNorm (μ := μ) x T
  -- Proof comment: transport the translated-origin cutoff theorem back to the centered phase-
  -- window spelling used by the downstream damped-quotient owner.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| =
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| := hGap
    _ ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := hTranslated
    _ =
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
          rw [hNorm]

/-- Helper for Theorem 15.51: the only live owner theorem needed downstream is the translated-
origin cutoff comparison on the canonical compare-window surface. -/
private lemma translatedGaussianOriginGaussianCutoffDirectLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
        cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                  charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                    gaussianReal 0 1)) t)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  -- Route correction: the stale shifted/Fourier-to-exact theorem was false because its left-hand
  -- side retained standalone Gaussian tails. The live downstream theorem only needs this weaker
  -- translated cutoff inequality, so the proof owner is rerooted here.
  -- TODO: prove the translated cutoff theorem directly from the translated-origin smoothing/Fourier
  -- bridge and `translatedStandardGaussianSmoothedCdfWindow_le_invCutoff`, without routing through
  -- the dead exact/sinc wrapper chain.
  sorry

/-- Helper for Theorem 15.51: the proof graph is now rerooted at the centered phase-window plus
explicit Gaussian cutoff surface actually consumed by the damped-quotient theorem. -/
private lemma centeredGaussianPhaseCutoffFrontierLocal
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi * T)) *
          ‖∫ t in -T..T,
              (charFun (μ ∗ gaussianReal 0 1) t -
                  charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  -- Route correction: the old exact/sinc cluster was a dead branch. The live downstream consumer
  -- only needs the translated cutoff theorem and the fixed transport back to the centered
  -- phase-window spelling.
  have hTranslatedCutoff :
      |cdf (μ.map (fun y : ℝ ↦ y - x)) 0 -
          cdf ((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) 0| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (((μ.map (fun y : ℝ ↦ y - x)) ∗ gaussianReal 0 1)) t -
                    charFun ((((gaussianReal 0 1 : Measure ℝ).map (fun y : ℝ ↦ y - x)) ∗
                      gaussianReal 0 1)) t)‖ +
          (2 / Real.sqrt (2 * Real.pi)) / T := by
    -- Proof comment: consume the rerooted translated cutoff theorem directly, without reviving
    -- the stale exact/sinc wrappers.
    exact translatedGaussianOriginGaussianCutoffDirectLocal (μ := μ) hT x
  -- Proof comment: the final step is now just the fixed transport from translated-origin cutoff
  -- form back to the centered phase-window surface used below.
  exact
    centeredGaussianPhaseCutoff_ofTranslatedCutoffCompare
      (μ := μ) (x := x) hTranslatedCutoff

/-- Helper for Theorem 15.51: the final pointwise smoothing surface already lands directly on the
Gaussian-damped quotient integral plus the explicit Gaussian cutoff term. -/
private lemma cdfGap_le_dampedQuotientSurface_add_gaussianCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (x : ℝ)
    (hDampedInt :
      IntervalIntegrable
        (fun t ↦
          (((charFun μ t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
        volume (-T) T) :
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
      (1 / (2 * Real.pi)) *
          (∫ t in -T..T,
            ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
                Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  let D : ℝ :=
    ∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
      ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))
  have hWindow :=
    centeredGaussianPhaseCutoffFrontierLocal (μ := μ) hT x
  have hNorm :
      ‖∫ t in -T..T,
          (charFun (μ ∗ gaussianReal 0 1) t -
              charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
            Complex.exp (((-x) * t : ℝ) * Complex.I)‖ =
        (2 * T) * |D| := by
    -- Proof comment: rewrite the centered truncated-window norm on the shifted-sinc surface.
    simpa [D] using smoothedTruncatedWindowNorm_eq_twoMul_absSincGap (μ := μ) hT x
  have hScale :
      (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) = (1 / Real.pi) * |D| := by
    -- Proof comment: cancel the canonical `2 * T` normalization from the truncated-window
    -- prefactor.
    exact smoothedTruncatedWindowPrefactor_mul_twoMul_abs_eq_piInv hT
  have hDamped :=
    smoothedShiftedSincAverageDifference_le_dampedQuotientWindowIntegral
      (μ := μ) x T hT hDampedInt
  -- Proof comment: start from the rerooted centered phase-window cutoff owner theorem, normalize
  -- its truncated-window norm to the shifted-sinc surface, and then bound that shifted-sinc gap
  -- by the damped quotient integral.
  calc
    |cdf μ x - cdf (gaussianReal 0 1) x| ≤
        (1 / (2 * Real.pi * T)) *
            ‖∫ t in -T..T,
                (charFun (μ ∗ gaussianReal 0 1) t -
                    charFun (((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1)) t) *
                  Complex.exp (((-x) * t : ℝ) * Complex.I)‖ +
          (2 / Real.sqrt (2 * Real.pi)) / T := hWindow
    _ = (1 / (2 * Real.pi * T)) * ((2 * T) * |D|) + (2 / Real.sqrt (2 * Real.pi)) / T := by
          rw [hNorm]
    _ = (1 / Real.pi) * |D| + (2 / Real.sqrt (2 * Real.pi)) / T := by
          rw [hScale]
    _ = (1 / Real.pi) *
            |∫ y, Real.sinc (T * (y - x)) ∂(μ ∗ gaussianReal 0 1) -
                ∫ y, Real.sinc (T * (y - x)) ∂(((gaussianReal 0 1 : Measure ℝ) ∗ gaussianReal 0 1))| +
          (2 / Real.sqrt (2 * Real.pi)) / T := by
          simp [D]
    _ ≤
        (1 / Real.pi) *
            ((1 / 2) *
              ∫ t in -T..T,
                ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
                    Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
          (2 / Real.sqrt (2 * Real.pi)) / T := by
            gcongr
    _ =
        (1 / (2 * Real.pi)) *
            (∫ t in -T..T,
              ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
                  Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
          (2 / Real.sqrt (2 * Real.pi)) / T := by
            ring_nf

/-- Helper for Theorem 15.51: away from `t = 0`, the Gaussian-damped quotient kernel is bounded
by the trivial `2 * exp (-(t²) / 2) / |t|` majorant coming from the unit bounds on both
characteristic functions. -/
private lemma dampedQuotientKernel_norm_le_two_exp_div_abs
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht0 : t ≠ 0) :
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / |t| := by
  have hCharμ : ‖charFun μ t‖ ≤ 1 := by
    simpa [MeasureTheory.Measure.real_def] using
      (norm_charFun_le (μ := μ) t)
  have hCharGauss : ‖charFun (gaussianReal 0 1) t‖ ≤ 1 := by
    simpa [MeasureTheory.Measure.real_def] using
      (norm_charFun_le (μ := (gaussianReal 0 1 : Measure ℝ)) t)
  have hSub : ‖charFun μ t - charFun (gaussianReal 0 1) t‖ ≤ 2 := by
    calc
      ‖charFun μ t - charFun (gaussianReal 0 1) t‖ ≤
          ‖charFun μ t‖ + ‖charFun (gaussianReal 0 1) t‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  calc
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
        ‖(charFun μ t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2))‖ / |t| := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤
        (‖charFun μ t - charFun (gaussianReal 0 1) t‖ *
            ‖Complex.exp (-(t ^ (2 : ℕ) / 2))‖) / |t| := by
          gcongr
          exact norm_mul_le _ _
    _ = (‖charFun μ t - charFun (gaussianReal 0 1) t‖ *
          Real.exp (-(t ^ (2 : ℕ) / 2))) / |t| := by
          congr 2
          simpa using (Complex.norm_exp_ofReal (-(t ^ (2 : ℕ) / 2)))
    _ ≤ (2 * Real.exp (-(t ^ (2 : ℕ) / 2))) / |t| := by
          gcongr

/-- Helper for Theorem 15.51: on an annulus where `|t|` stays above a fixed radius `R`, the
Gaussian-damped quotient kernel is bounded by replacing the denominator `|t|` with the cheaper
uniform lower bound `R`. -/
private lemma dampedQuotientKernel_norm_le_two_exp_div_radius
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {R t : ℝ}
    (hR : 0 < R) (ht : R ≤ |t|) :
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / R := by
  have ht0 : t ≠ 0 := by
    intro ht0
    have : R ≤ 0 := by simpa [ht0] using ht
    linarith
  have hNumerator_nonneg : 0 ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) := by positivity
  -- Proof comment: first use the pointwise `1 / |t|` majorant, then freeze the denominator on
  -- the annulus by the lower bound `R ≤ |t|`.
  calc
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / |t| :=
        dampedQuotientKernel_norm_le_two_exp_div_abs (μ := μ) ht0
    _ ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / R := by
        exact div_le_div_of_nonneg_left hNumerator_nonneg hR ht

/-- Helper for Theorem 15.51: the scalar profile `u * exp (-(u²) / 2)` is globally maximized at
`u = 1`, so its value never exceeds `exp (-1 / 2)`. -/
private lemma abs_mul_exp_neg_sq_div_two_le_exp_neg_half
    (t : ℝ) :
    |t| * Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) := by
  have hAMGM : |t| ≤ (t ^ (2 : ℕ) + 1) / 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have hExpLower :
      (t ^ (2 : ℕ) + 1) / 2 ≤ Real.exp ((t ^ (2 : ℕ) - 1) / 2) := by
    have hExp := Real.add_one_le_exp ((t ^ (2 : ℕ) - 1) / 2)
    nlinarith
  calc
    |t| * Real.exp (-(t ^ (2 : ℕ) / 2)) ≤
        ((t ^ (2 : ℕ) + 1) / 2) * Real.exp (-(t ^ (2 : ℕ) / 2)) := by
          gcongr
    _ ≤ Real.exp ((t ^ (2 : ℕ) - 1) / 2) * Real.exp (-(t ^ (2 : ℕ) / 2)) := by
          gcongr
    _ = Real.exp (-(1 / 2 : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring

/-- Helper for Theorem 15.51: the reciprocal-square kernel has the exact scale-two annulus
primitive `1 / (2 * T0)` on the positive tail `[T0, 2 * T0]`. -/
private lemma integral_invSq_scaleTwoTail
    {T0 : ℝ} (hT0 : 0 < T0) :
    ∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ) = 1 / (2 * T0) := by
  have hZero :
      (0 : ℝ) ∉ Set.uIcc T0 (2 * T0) := by
    rw [Set.uIcc_of_le (by linarith [hT0])]
    intro hmem
    exact not_le_of_gt hT0 hmem.1
  have hIntegral :
      ∫ t in T0..(2 * T0), t ^ (-2 : ℤ) =
        ((2 * T0) ^ (-1 : ℤ) - T0 ^ (-1 : ℤ)) / (-1 : ℤ) := by
    -- Proof comment: evaluate the reciprocal-square primitive through the standard `zpow`
    -- antiderivative away from the singular point `0`.
    convert
      (integral_zpow (a := T0) (b := 2 * T0) (n := (-2 : ℤ))
        (Or.inr ⟨by norm_num, hZero⟩)) using 1
    norm_num
  have hRewrite :
      (∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ)) =
        ∫ t in T0..(2 * T0), t ^ (-2 : ℤ) := by
    -- Proof comment: on the positive annulus, the reciprocal-square profile is exactly the
    -- `zpow` integrand from the antiderivative formula.
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith [hT0])] at ht
    have ht0 : t ≠ 0 := by
      have htLower : T0 ≤ t := ht.1
      linarith
    calc
      (1 : ℝ) / t ^ (2 : ℕ) = (t ^ (2 : ℕ))⁻¹ := by rw [one_div]
      _ = t ^ (-2 : ℤ) := by
        rw [show (-2 : ℤ) = Int.negSucc 1 by decide, zpow_negSucc]
  calc
    ∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ) =
        ∫ t in T0..(2 * T0), t ^ (-2 : ℤ) := hRewrite
    _ = ((2 * T0) ^ (-1 : ℤ) - T0 ^ (-1 : ℤ)) / (-1 : ℤ) := hIntegral
    _ = 1 / (2 * T0) := by
        field_simp [ne_of_gt hT0, show 2 * T0 ≠ 0 by positivity]
        ring

/-- Helper for Theorem 15.51: once the direct damped-window remainder is isolated at the natural
cutoff, the remaining integral contribution fits inside the leftover coefficient
`0.8 - 2 / √(2π)`. -/
private lemma standardizedLawGaussianDampedIntegrand_eq_expDefect
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
    let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
    let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
    (((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) =
      ((Complex.exp (-(t ^ (2 : ℕ))) * (Complex.exp η - 1)) / t : ℂ) := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
  have hLaw :
      charFun μn t = Complex.exp ((n : ℂ) * Complex.log (charFun (P.map Y) u)) := by
    -- Proof comment: reuse the existing exp/log normalization of the standardized law.
    simpa [μn, Y, u] using
      standardizedLawCharFun_eq_exp_log P X hX_iid hX_mean hX_var hX_third n ht
  have hGauss :
      charFun (gaussianReal 0 1) t = Complex.exp (-(t ^ (2 : ℕ) / 2)) := by
    -- Proof comment: the standard Gaussian characteristic function is the quadratic exponential.
    simpa using
      (ProbabilityTheory.charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) t)
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hu_sq_real :
      (n : ℝ) * (u ^ (2 : ℕ) / 2) = t ^ (2 : ℕ) / 2 := by
    -- Proof comment: the natural-window scaling `u = t / √n` turns `n * u² / 2` into `t² / 2`.
    dsimp [u]
    field_simp [hsqrt_n_ne]
    rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  have hu_sq :
      (n : ℂ) * (((u : ℂ) ^ (2 : ℕ)) / 2) = ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
    exact_mod_cast hu_sq_real
  have hExpRewrite :
      Complex.exp ((n : ℂ) * Complex.log (charFun (P.map Y) u)) =
        Complex.exp (-(t ^ (2 : ℕ) / 2)) * Complex.exp η := by
    -- Proof comment: isolate the Gaussian quadratic phase from the logarithmic defect `η`.
    have hExponent :
        (n : ℂ) * Complex.log (charFun (P.map Y) u) =
          η - (t ^ (2 : ℕ) / 2 : ℝ) := by
      dsimp [η]
      rw [mul_add, hu_sq]
      ring
    calc
      Complex.exp ((n : ℂ) * Complex.log (charFun (P.map Y) u)) =
          Complex.exp (η - (t ^ (2 : ℕ) / 2 : ℝ)) := by
            rw [hExponent]
      _ = Complex.exp (-(t ^ (2 : ℕ) / 2)) * Complex.exp η := by
            rw [sub_eq_add_neg, add_comm, Complex.exp_add]
            congr 1
            norm_num
  have hDoubleExp :
      Complex.exp (-(t ^ (2 : ℕ) / 2)) * Complex.exp (-(t ^ (2 : ℕ) / 2)) =
        Complex.exp (-(t ^ (2 : ℕ))) := by
    -- Proof comment: the extra Gaussian damping doubles the quadratic exponent.
    rw [← Complex.exp_add]
    congr 1
    ring
  -- Proof comment: substitute the exp/log rewrite, factor out the common Gaussian term, and
  -- collapse the two damping factors into `exp (-t²)`.
  calc
    (((charFun μn t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) =
        (((Complex.exp (-(t ^ (2 : ℕ) / 2)) * Complex.exp η -
              Complex.exp (-(t ^ (2 : ℕ) / 2))) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) := by
          rw [hLaw, hExpRewrite, hGauss]
    _ = ((Complex.exp (-(t ^ (2 : ℕ) / 2)) * (Complex.exp η - 1) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) := by
          ring
    _ = (((Complex.exp (-(t ^ (2 : ℕ) / 2)) * Complex.exp (-(t ^ (2 : ℕ) / 2))) *
            (Complex.exp η - 1)) / t : ℂ) := by
          ring
    _ = ((Complex.exp (-(t ^ (2 : ℕ))) * (Complex.exp η - 1)) / t : ℂ) := by
          rw [hDoubleExp]

/-- Helper for Theorem 15.51: once the damped quotient integrand is rewritten through the
exp/log defect `η`, a small-defect hypothesis `‖η‖ ≤ 1` gives the uniform linear estimate
`‖exp η - 1‖ ≤ 2 ‖η‖`. -/
private lemma standardizedLawGaussianDampedIntegrand_norm_le_two_mul_expDefect
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)
    (ht0 : t ≠ 0)
    (hη :
      let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
      let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
      let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
      ‖η‖ ≤ 1) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
    let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
    let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ))) * ‖η‖ / |t| := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
  have hRewrite :
      (((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)) =
        ((Complex.exp (-(t ^ (2 : ℕ))) * (Complex.exp η - 1)) / t : ℂ) := by
    -- Proof comment: first rewrite the damped quotient integrand using the exact defect factor.
    simpa [μn, Y, u, η] using
      standardizedLawGaussianDampedIntegrand_eq_expDefect
        P X hX_iid hX_mean hX_var hX_third n ht
  have ht_abs_pos : 0 < |t| := abs_pos.mpr ht0
  have hη_unit :
      ‖η‖ ≤ 1 := by
    simpa [Y, u, η] using hη
  have hExpSub :
      ‖Complex.exp η - 1‖ ≤ 2 * ‖η‖ := Complex.norm_exp_sub_one_le hη_unit
  -- Proof comment: take norms, use `‖exp (-t²)‖ = exp (-t²)`, apply the small-defect estimate,
  -- and divide by the positive scalar `|t|`.
  calc
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
        ‖((Complex.exp (-(t ^ (2 : ℕ))) * (Complex.exp η - 1)) / t : ℂ)‖ := by
          rw [hRewrite]
    _ = ‖Complex.exp (-(t ^ (2 : ℕ))) * (Complex.exp η - 1)‖ / |t| := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (‖Complex.exp (-(t ^ (2 : ℕ)))‖ * ‖Complex.exp η - 1‖) / |t| := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ (Real.exp (-(t ^ (2 : ℕ))) * (2 * ‖η‖)) / |t| := by
          gcongr
          exact le_of_eq <| by
            simpa using (Complex.norm_exp_ofReal (-(t ^ (2 : ℕ))))
    _ = 2 * Real.exp (-(t ^ (2 : ℕ))) * ‖η‖ / |t| := by
          field_simp [abs_ne_zero.mpr ht0]

/-- Helper for Theorem 15.51: on the natural Berry--Esseen window, any additional cubic control
`|t|^3 ≤ Tn` forces the logarithmic exponent defect to lie in the unit ball. -/
private lemma standardizedLawGaussianExponentDefect_le_one_of_cubicBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)
    (hcubic : |t| ^ (3 : ℕ) ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
    let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
    ‖((n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))‖ ≤ 1 := by
  dsimp
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale is already known to dominate `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hDefect :
      ‖((n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))‖ ≤
        β * |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) := by
    -- Proof comment: first rewrite the existing cubic exponent-defect estimate in terms of `β`.
    simpa [β, Y, u, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      standardizedLawGaussianExponentDefectBound
        P X hX_iid hX_mean hX_var hX_third n ht
  have hScaled :
      β * |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) ≤
        β *
            (Real.sqrt (n : ℝ) *
              (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) /
          Real.sqrt (n : ℝ) := by
    -- Proof comment: replace `|t|^3` by the assumed cubic window size before clearing the
    -- positive denominator `√n`.
    exact
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcubic (le_of_lt hβ_pos))
        (by positivity)
  have hMoment_pos : 0 < absoluteMoment (X 1) 3 P := by
    have hσ_cube_pos : 0 < Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
      positivity
    have hProd : 0 < β * Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
      exact mul_pos hβ_pos hσ_cube_pos
    rw [show β * Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) = absoluteMoment (X 1) 3 P by
      dsimp [β]
      field_simp [hσ_cube_pos.ne']] at hProd
    exact hProd
  have hTarget :
      β *
          (Real.sqrt (n : ℝ) *
            (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) /
        Real.sqrt (n : ℝ) = 1 := by
    -- Proof comment: the natural Berry--Esseen scaling makes the cubic defect exactly unit size.
    dsimp [β]
    field_simp [hMoment_pos.ne', hsqrt_n_pos.ne']
  calc
    ‖((n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2))‖ ≤
        β * |t| ^ (3 : ℕ) / Real.sqrt (n : ℝ) := hDefect
    _ ≤
        β *
            (Real.sqrt (n : ℝ) *
              (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) /
          Real.sqrt (n : ℝ) := hScaled
    _ = 1 := hTarget

/-- Helper for Theorem 15.51: on the natural window, the damped quotient integrand is controlled
by the cubic exponent-defect majorant as soon as the cubic scale lies in the unit-logarithm
regime. -/
private lemma standardizedLawGaussianDampedIntegrand_smallCubicBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)
    (hcubic : |t| ^ (3 : ℕ) ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)
    (ht0 : t ≠ 0) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ))) *
        (absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let Y : Ω → ℝ := fun ω ↦ X 1 ω / Real.sqrt (Var[X 1; P])
  let u : ℝ := (Real.sqrt (n : ℝ))⁻¹ * t
  let η : ℂ := (n : ℂ) * (Complex.log (charFun (P.map Y) u) + ((u : ℂ) ^ (2 : ℕ)) / 2)
  have hη :
      ‖η‖ ≤ 1 := by
    -- Proof comment: the extra cubic window hypothesis is exactly the side condition needed to
    -- place the logarithmic defect inside the unit ball.
    simpa [Y, u, η] using
      standardizedLawGaussianExponentDefect_le_one_of_cubicBound
        P X hX_iid hX_mean hX_var hX_third n ht hcubic
  have hLinear :
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
        2 * Real.exp (-(t ^ (2 : ℕ))) * ‖η‖ / |t| := by
    -- Proof comment: rewrite the damped quotient integrand through `η`, then apply the uniform
    -- `‖exp η - 1‖ ≤ 2‖η‖` estimate inside the unit ball.
    simpa [μn, Y, u, η] using
      standardizedLawGaussianDampedIntegrand_norm_le_two_mul_expDefect
        P X hX_iid hX_mean hX_var hX_third n ht ht0 hη
  have hDefect :
      ‖η‖ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
    -- Proof comment: substitute the established cubic exponent-defect estimate on the natural
    -- Berry--Esseen window.
    simpa [Y, u, η] using
      standardizedLawGaussianExponentDefectBound
        P X hX_iid hX_mean hX_var hX_third n ht
  have hMain :
      2 * Real.exp (-(t ^ (2 : ℕ))) * ‖η‖ / |t| ≤
        2 * Real.exp (-(t ^ (2 : ℕ))) *
          (absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) / |t| := by
    -- Proof comment: transport the cubic defect bound through the nonnegative damped prefactor.
    gcongr
  have hσ_ne : Real.sqrt (Var[X 1; P]) ≠ 0 := ne_of_gt (berryEsseenSigmaPos P X hX_var)
  have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
  calc
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
        2 * Real.exp (-(t ^ (2 : ℕ))) * ‖η‖ / |t| := hLinear
    _ ≤
        2 * Real.exp (-(t ^ (2 : ℕ))) *
          (absoluteMoment (X 1) 3 P * |t| ^ (3 : ℕ) /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) / |t| := hMain
    _ =
        2 * Real.exp (-(t ^ (2 : ℕ))) *
          (absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
          field_simp [abs_ne_zero.mpr ht0, hσ_ne, hsqrt_n_ne]

/-- Helper for Theorem 15.51: the canonical inner radius `min Tn 1` is nonnegative, lies inside
the natural cutoff, and already satisfies the cubic side condition needed for the small-defect
window. -/
private lemma naturalInnerRadius_bounds
    {Tn : ℝ} (hTn_nonneg : 0 ≤ Tn) :
    0 ≤ min Tn 1 ∧ min Tn 1 ≤ Tn ∧ (min Tn 1) ^ (3 : ℕ) ≤ Tn := by
  have hRadius_nonneg : 0 ≤ min Tn 1 := by
    exact le_min hTn_nonneg zero_le_one
  have hRadius_le_one : min Tn 1 ≤ 1 := min_le_right _ _
  have hCube_le_radius : (min Tn 1) ^ (3 : ℕ) ≤ min Tn 1 := by
    -- Proof comment: on `[0, 1]`, cubing only decreases the radius.
    calc
      (min Tn 1) ^ (3 : ℕ) = (min Tn 1) ^ (2 : ℕ) * min Tn 1 := by ring
      _ ≤ 1 * min Tn 1 := by
            gcongr
            nlinarith
      _ = min Tn 1 := by ring
  exact ⟨hRadius_nonneg, min_le_left _ _, hCube_le_radius.trans (min_le_left _ _)⟩

/-- Helper for Theorem 15.51: any point with `|t| ≤ min Tn 1` automatically satisfies the cubic
window bound `|t|³ ≤ Tn`. -/
private lemma abs_cube_le_of_abs_le_naturalInnerRadius
    {Tn t : ℝ} (hTn_nonneg : 0 ≤ Tn) (ht : |t| ≤ min Tn 1) :
    |t| ^ (3 : ℕ) ≤ Tn := by
  have hRadius := naturalInnerRadius_bounds hTn_nonneg
  -- Proof comment: first bound `|t|³` by the cube of the inner radius, then use the canonical
  -- cubic-window property of `min Tn 1`.
  calc
    |t| ^ (3 : ℕ) ≤ (min Tn 1) ^ (3 : ℕ) := by
          gcongr
    _ ≤ Tn := hRadius.2.2

/-- Helper for Theorem 15.51: on the canonical inner window `|t| ≤ min Tn 1`, the damped
quotient integrand already satisfies the small-cubic majorant. -/
private lemma standardizedLawGaussianDampedIntegrand_onCanonicalInnerWindow_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      min
        (Real.sqrt (n : ℝ) *
          (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)
        1)
    (ht0 : t ≠ 0) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      2 * Real.exp (-(t ^ (2 : ℕ))) *
        (absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  let Tn : ℝ :=
    Real.sqrt (n : ℝ) *
      (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹
  have hβ_ge_one :
      1 ≤ absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
    -- Proof comment: the normalized third-moment scale is already known to dominate `1`.
    exact berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos :
      0 < absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) := by
    exact lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hTn_nonneg : 0 ≤ Tn := by
    -- Proof comment: the natural cutoff is nonnegative because both factors are nonnegative.
    dsimp [Tn]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hCutoff :
      |t| ≤
        Real.sqrt (n : ℝ) *
          (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹ := by
    exact ht.trans (min_le_left _ _)
  have hCubic :
      |t| ^ (3 : ℕ) ≤
        Real.sqrt (n : ℝ) *
          (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹ := by
    simpa [Tn] using abs_cube_le_of_abs_le_naturalInnerRadius hTn_nonneg ht
  -- Proof comment: specialize the general small-cubic estimate to the canonical inner radius
  -- `min Tn 1`.
  simpa using
    standardizedLawGaussianDampedIntegrand_smallCubicBound
      P X hX_iid hX_mean hX_var hX_third n hCutoff hCubic ht0

/-- Helper for Theorem 15.51: a symmetric scale-two interval integral can be split into the two
outer tails, the two middle bands, and the canonical inner window. -/
private lemma intervalIntegral_split_scaleTwo
    {f : ℝ → ℝ} {R T0 Tn : ℝ}
    (hLeftTail : IntervalIntegrable f volume (-Tn) (-T0))
    (hLeftMiddle : IntervalIntegrable f volume (-T0) (-R))
    (hInner : IntervalIntegrable f volume (-R) R)
    (hRightMiddle : IntervalIntegrable f volume R T0)
    (hRightTail : IntervalIntegrable f volume T0 Tn) :
    ∫ t in -Tn..Tn, f t =
      (∫ t in -Tn..-T0, f t) +
        (∫ t in -T0..-R, f t) +
          (∫ t in -R..R, f t) +
            (∫ t in R..T0, f t) +
              ∫ t in T0..Tn, f t := by
  have hLeftToInner : IntervalIntegrable f volume (-Tn) (-R) := hLeftTail.trans hLeftMiddle
  have hLeftToRightMiddle : IntervalIntegrable f volume (-Tn) T0 :=
    (hLeftToInner.trans hInner).trans hRightMiddle
  have hAll : IntervalIntegrable f volume (-Tn) Tn := hLeftToRightMiddle.trans hRightTail
  have hSplitTail :
      ∫ t in -Tn..-R, f t =
        (∫ t in -Tn..-T0, f t) + ∫ t in -T0..-R, f t := by
    -- Proof comment: first split the negative half of the scale-two window at `-T0`.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := f) hLeftTail hLeftMiddle).symm
  have hSplitCore :
      ∫ t in -R..T0, f t =
        (∫ t in -R..R, f t) + ∫ t in R..T0, f t := by
    -- Proof comment: then split the central block at the inner radius `R`.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := f) hInner hRightMiddle).symm
  have hSplitOuter :
      ∫ t in -Tn..T0, f t =
        (∫ t in -Tn..-R, f t) + ∫ t in -R..T0, f t := by
    -- Proof comment: glue the negative annulus to the center block.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := f) hLeftToInner (hInner.trans hRightMiddle)).symm
  have hSplitAll :
      ∫ t in -Tn..Tn, f t =
        (∫ t in -Tn..T0, f t) + ∫ t in T0..Tn, f t := by
    -- Proof comment: the final split isolates the positive outer tail.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := f) hLeftToRightMiddle hRightTail).symm
  -- Proof comment: substitute the adjacent-interval decompositions and reassociate the sum.
  rw [hSplitAll, hSplitOuter, hSplitTail, hSplitCore]
  ring

/-- Helper for Theorem 15.51: on the natural Berry--Esseen window `|t| ≤ T0`, the middle-band
surface is controlled by the existing split majorant for the undamped quotient kernel. -/
private lemma standardizedLawGaussianMiddleBandPointwise_le_splitMajorant
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  have hSplit :
      ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
    -- Proof comment: reuse the established law/proxy plus proxy/Gaussian quotient split on the
    -- full natural window `|t| ≤ T0`.
    simpa [μn] using
      standardizedLawGaussianQuotientWindowSplitBound
        P X hX_iid hX_mean hX_var hX_third n ht
  have hExp_le_one : Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ 1 := by
    -- Proof comment: the Gaussian damping factor is bounded by `1` everywhere on `ℝ`.
    have hExponent_nonpos : -(t ^ (2 : ℕ) / 2) ≤ 0 := by
      nlinarith
    exact Real.exp_le_one_iff.mpr hExponent_nonpos
  have hDamped_le :
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
        ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ := by
    -- Proof comment: discard the extra Gaussian damping by rewriting the quotient kernel as a
    -- product and using `‖exp (-t² / 2)‖ ≤ 1`.
    calc
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
          ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ) *
              Complex.exp (-(t ^ (2 : ℕ) / 2))‖ := by
            congr 1
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ *
            Real.exp (-(t ^ (2 : ℕ) / 2)) := by
            rw [norm_mul]
            congr 2
            simpa using (Complex.norm_exp_ofReal (-(t ^ (2 : ℕ) / 2)))
      _ ≤ ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ * 1 := by
            gcongr
      _ = ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ := by ring
  -- Proof comment: first drop the extra damping, then appeal to the already proved natural-window
  -- split majorant.
  exact hDamped_le.trans hSplit

/-- Helper for Theorem 15.51: on the natural Berry--Esseen window `|t| ≤ T0`, the Gaussian-damped
quotient surface splits into a damped law term and a twice-damped proxy term. -/
private lemma standardizedLawGaussianDampedSplitBoundOnCentralWindow
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) {t : ℝ}
    (ht : |t| ≤
      Real.sqrt (n : ℝ) *
        (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ ≤
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ)) := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  have hSplit :
      ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ ≤
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ)) := by
    -- Proof comment: start from the already proved undamped natural-window split on the same
    -- standardized partial-sum law.
    simpa [μn] using
      standardizedLawGaussianQuotientWindowSplitBound
        P X hX_iid hX_mean hX_var hX_third n ht
  have hRewrite :
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
        ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ *
          Real.exp (-(t ^ (2 : ℕ) / 2)) := by
    -- Proof comment: expose the extra Gaussian damping as a multiplicative real factor of norm
    -- `exp (-(t²) / 2)`.
    calc
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
            Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
          ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ) *
              Complex.exp (-(t ^ (2 : ℕ) / 2))‖ := by
            congr 1
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ *
            ‖Complex.exp (-(t ^ (2 : ℕ) / 2))‖ := by
            rw [norm_mul]
      _ = ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ *
            Real.exp (-(t ^ (2 : ℕ) / 2)) := by
            congr 1
            simpa using (Complex.norm_exp_ofReal (-(t ^ (2 : ℕ) / 2)))
  have hExp_nonneg : 0 ≤ Real.exp (-(t ^ (2 : ℕ) / 2)) := by positivity
  -- Proof comment: multiply the established undamped split by the common damping factor and then
  -- fold the proxy's two matching exponentials into `exp (-t²)`.
  calc
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖ =
      ‖((charFun μn t - charFun (gaussianReal 0 1) t) / t : ℂ)‖ *
        Real.exp (-(t ^ (2 : ℕ) / 2)) := hRewrite
    _ ≤
        (absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
          |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))) *
          Real.exp (-(t ^ (2 : ℕ) / 2)) := by
          exact mul_le_mul_of_nonneg_right hSplit hExp_nonneg
    _ =
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) *
            (Real.exp (-(t ^ (2 : ℕ) / 2)) * Real.exp (-(t ^ (2 : ℕ) / 2))) /
          (4 * (n : ℝ)) := by
          ring
    _ =
        absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) +
        |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ)) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring

/-- Helper for Theorem 15.51: after restricting to the two scale-two tails
`[-2 * T0, -T0] ∪ [T0, 2 * T0]`, the damped quotient surface is controlled by an explicit
`exp (-1 / 2) / T0` coefficient. -/
private lemma dampedQuotientScaleTwoTailIntegral_le_expHalfCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T0 : ℝ} (hT0 : 0 < T0) :
    let f : ℝ → ℝ := fun t ↦
      ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
    (1 / (2 * Real.pi)) *
        ((∫ t in -(2 * T0)..-T0, f t) + ∫ t in T0..(2 * T0), f t) ≤
      ((2 * Real.exp (-(1 / 2 : ℝ))) / Real.pi) / T0 := by
  dsimp
  let f : ℝ → ℝ := fun t ↦
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
  have hLeftInt : IntervalIntegrable f volume (-(2 * T0)) (-T0) := by
    -- Proof comment: the negative tail stays away from `0`, so the damped quotient kernel is
    -- continuous and hence interval-integrable there.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := -(2 * T0)) (b := -T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_le : t ≤ -T0 := ht.2
        exact_mod_cast (show t ≠ 0 by linarith [ht_le, hT0])
  have hRightInt : IntervalIntegrable f volume T0 (2 * T0) := by
    -- Proof comment: the same continuity argument applies on the positive scale-two tail.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := T0) (b := 2 * T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_ge : T0 ≤ t := ht.1
        exact_mod_cast (show t ≠ 0 by linarith [ht_ge, hT0])
  have hConstLeftInt :
      IntervalIntegrable (fun _ : ℝ ↦ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0)
        volume (-(2 * T0)) (-T0) := by
    refine Continuous.intervalIntegrable ?_ (-(2 * T0)) (-T0)
    continuity
  have hConstRightInt :
      IntervalIntegrable (fun _ : ℝ ↦ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0)
        volume T0 (2 * T0) := by
    refine Continuous.intervalIntegrable ?_ T0 (2 * T0)
    continuity
  have hLeftBound :
      ∫ t in -(2 * T0)..-T0, f t ≤ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
    have hmono :
        ∫ t in -(2 * T0)..-T0, f t ≤
          ∫ t in -(2 * T0)..-T0, 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := by
      refine
        intervalIntegral.integral_mono_on
          (μ := volume) (a := -(2 * T0)) (b := -T0)
          (f := f)
          (g := fun _ : ℝ ↦ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0)
          (by linarith) hLeftInt hConstLeftInt ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc (-(2 * T0)) (-T0) := by
        simpa [Set.uIcc_of_le (show -(2 * T0) ≤ -T0 by nlinarith [hT0])] using ht
      have ht_nonpos : t ≤ 0 := le_trans ht_mem.2 (by linarith)
      have ht_abs : T0 ≤ |t| := by
        rw [abs_of_nonpos ht_nonpos]
        nlinarith [ht_mem.2, hT0]
      have hsq : T0 ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by
        nlinarith [sq_abs t, ht_abs]
      have hexp :
          Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        f t ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / T0 := by
            exact dampedQuotientKernel_norm_le_two_exp_div_radius (μ := μ) hT0 ht_abs
        _ ≤ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := by
            gcongr
    calc
      ∫ t in -(2 * T0)..-T0, f t ≤
          ∫ t in -(2 * T0)..-T0, 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := hmono
      _ = ((-T0) - (-(2 * T0))) * (2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
            field_simp [ne_of_gt hT0]
            ring
  have hRightBound :
      ∫ t in T0..(2 * T0), f t ≤ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
    have hmono :
        ∫ t in T0..(2 * T0), f t ≤
          ∫ t in T0..(2 * T0), 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := by
      refine
        intervalIntegral.integral_mono_on
          (μ := volume) (a := T0) (b := 2 * T0)
          (f := f)
          (g := fun _ : ℝ ↦ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0)
          (by linarith) hRightInt hConstRightInt ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc T0 (2 * T0) := by
        simpa [Set.uIcc_of_le (show T0 ≤ 2 * T0 by nlinarith [hT0])] using ht
      have ht_nonneg : 0 ≤ t := by
        linarith [ht_mem.1, hT0]
      have ht_abs : T0 ≤ |t| := by
        rw [abs_of_nonneg ht_nonneg]
        exact ht_mem.1
      have hsq : T0 ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by
        nlinarith [sq_abs t, ht_abs]
      have hexp :
          Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        f t ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / T0 := by
            exact dampedQuotientKernel_norm_le_two_exp_div_radius (μ := μ) hT0 ht_abs
        _ ≤ 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := by
            gcongr
    calc
      ∫ t in T0..(2 * T0), f t ≤
          ∫ t in T0..(2 * T0), 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0 := hmono
      _ = ((2 * T0) - T0) * (2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) / T0) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
            field_simp [ne_of_gt hT0]
            ring
  have hPeakAtOne :
      T0 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have hAMGM : T0 ≤ (T0 ^ (2 : ℕ) + 1) / 2 := by
      nlinarith [sq_nonneg (T0 - 1)]
    have hExpLower :
        (T0 ^ (2 : ℕ) + 1) / 2 ≤ Real.exp ((T0 ^ (2 : ℕ) - 1) / 2) := by
      have hExp := Real.add_one_le_exp ((T0 ^ (2 : ℕ) - 1) / 2)
      nlinarith
    have hScale :
        T0 ≤ Real.exp ((T0 ^ (2 : ℕ) - 1) / 2) := hAMGM.trans hExpLower
    calc
      T0 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) ≤
          Real.exp ((T0 ^ (2 : ℕ) - 1) / 2) * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
            gcongr
      _ = Real.exp (-(1 / 2 : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hExpScale :
      Real.exp (-(T0 ^ (2 : ℕ) / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) / T0 := by
    have hPeakAtOne' :
        Real.exp (-(T0 ^ (2 : ℕ) / 2)) * T0 ≤ Real.exp (-(1 / 2 : ℝ)) := by
      simpa [mul_comm] using hPeakAtOne
    exact (le_div_iff₀ hT0).2 hPeakAtOne'
  -- Proof comment: bound both tails by the same frozen annulus majorant, then use the elementary
  -- estimate `T0 * exp (-(T0²) / 2) ≤ exp (-1 / 2)` to convert the remaining scale factor into
  -- the displayed `exp (-1 / 2) / T0` coefficient.
  calc
    (1 / (2 * Real.pi)) *
        ((∫ t in -(2 * T0)..-T0, f t) + ∫ t in T0..(2 * T0), f t) ≤
      (1 / (2 * Real.pi)) *
        (2 * Real.exp (-(T0 ^ (2 : ℕ) / 2)) + 2 * Real.exp (-(T0 ^ (2 : ℕ) / 2))) := by
          gcongr
    _ = (2 / Real.pi) * Real.exp (-(T0 ^ (2 : ℕ) / 2)) := by
          field_simp [Real.pi_ne_zero]
          ring
    _ ≤ (2 / Real.pi) * (Real.exp (-(1 / 2 : ℝ)) / T0) := by
          gcongr
    _ = ((2 * Real.exp (-(1 / 2 : ℝ))) / Real.pi) / T0 := by
          field_simp [Real.pi_ne_zero, ne_of_gt hT0]

/-- Helper for Theorem 15.51: the scale-two annulus estimate is sharper if the Gaussian damping
is converted into a reciprocal-square majorant before integrating. -/
private lemma dampedQuotientScaleTwoTailIntegral_le_sharpScaledCutoff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T0 : ℝ} (hT0 : 0 < T0) :
    let f : ℝ → ℝ := fun t ↦
      ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
    (1 / (2 * Real.pi)) *
        ((∫ t in -(2 * T0)..-T0, f t) + ∫ t in T0..(2 * T0), f t) ≤
      (Real.exp (-(1 / 2 : ℝ)) / Real.pi) / T0 := by
  dsimp
  let f : ℝ → ℝ := fun t ↦
    ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
  let g : ℝ → ℝ := fun t ↦ 2 * Real.exp (-(1 / 2 : ℝ)) / t ^ (2 : ℕ)
  have hLeftInt : IntervalIntegrable f volume (-(2 * T0)) (-T0) := by
    -- Proof comment: the negative tail stays away from `0`, so the damped quotient kernel is
    -- continuous and hence interval-integrable there.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := -(2 * T0)) (b := -T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_le : t ≤ -T0 := ht.2
        exact_mod_cast (show t ≠ 0 by linarith [ht_le, hT0])
  have hRightInt : IntervalIntegrable f volume T0 (2 * T0) := by
    -- Proof comment: the same continuity argument applies on the positive scale-two tail.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := T0) (b := 2 * T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_ge : T0 ≤ t := ht.1
        exact_mod_cast (show t ≠ 0 by linarith [ht_ge, hT0])
  have hLeftMajInt : IntervalIntegrable g volume (-(2 * T0)) (-T0) := by
    -- Proof comment: the reciprocal-square majorant is continuous on the negative annulus.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := -(2 * T0)) (b := -T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.div continuousAt_const ?_ ?_
      · exact ContinuousAt.pow continuousAt_id 2
      · have ht_le : t ≤ -T0 := ht.2
        exact_mod_cast (show t ^ (2 : ℕ) ≠ 0 by
          have ht0 : t ≠ 0 := by linarith [ht_le, hT0]
          exact pow_ne_zero 2 ht0)
  have hRightMajInt : IntervalIntegrable g volume T0 (2 * T0) := by
    -- Proof comment: the same reciprocal-square majorant is continuous on the positive annulus.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := T0) (b := 2 * T0) ?_ ?_
    · linarith
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.div continuousAt_const ?_ ?_
      · exact ContinuousAt.pow continuousAt_id 2
      · have ht_ge : T0 ≤ t := ht.1
        exact_mod_cast (show t ^ (2 : ℕ) ≠ 0 by
          have ht0 : t ≠ 0 := by linarith [ht_ge, hT0]
          exact pow_ne_zero 2 ht0)
  have hInvSqLeft :
      ∫ t in -(2 * T0)..-T0, (1 : ℝ) / t ^ (2 : ℕ) =
        1 / (2 * T0) := by
    calc
      ∫ t in -(2 * T0)..-T0, (1 : ℝ) / t ^ (2 : ℕ) =
          ∫ t in T0..(2 * T0), (1 : ℝ) / (-t) ^ (2 : ℕ) := by
            simpa using
              (intervalIntegral.integral_comp_neg
                (f := fun t : ℝ ↦ (1 : ℝ) / t ^ (2 : ℕ))
                (a := -(2 * T0)) (b := -T0))
      _ = ∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ) := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with t
            simp [pow_two]
      _ = 1 / (2 * T0) := integral_invSq_scaleTwoTail hT0
  have hLeftBound :
      ∫ t in -(2 * T0)..-T0, f t ≤ Real.exp (-(1 / 2 : ℝ)) / T0 := by
    have hmono :
        ∫ t in -(2 * T0)..-T0, f t ≤ ∫ t in -(2 * T0)..-T0, g t := by
      refine
        intervalIntegral.integral_mono_on
          (μ := volume) (a := -(2 * T0)) (b := -T0)
          (f := f) (g := g) (by linarith) hLeftInt hLeftMajInt ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc (-(2 * T0)) (-T0) := by
        simpa [Set.uIcc_of_le (show -(2 * T0) ≤ -T0 by nlinarith [hT0])] using ht
      have ht0 : t ≠ 0 := by
        have ht_le : t ≤ -T0 := ht_mem.2
        exact_mod_cast (show t ≠ 0 by linarith [ht_le, hT0])
      have hExpScale :
          Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) / |t| := by
        have hMul :
            Real.exp (-(t ^ (2 : ℕ) / 2)) * |t| ≤ Real.exp (-(1 / 2 : ℝ)) := by
          simpa [mul_comm] using abs_mul_exp_neg_sq_div_two_le_exp_neg_half t
        exact (le_div_iff₀ (abs_pos.mpr ht0)).2 hMul
      have hAbsSq : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by
        simpa [pow_two] using (sq_abs t)
      calc
        f t ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / |t| := by
            exact dampedQuotientKernel_norm_le_two_exp_div_abs (μ := μ) ht0
        _ ≤ 2 * (Real.exp (-(1 / 2 : ℝ)) / |t|) / |t| := by
            gcongr
        _ = 2 * Real.exp (-(1 / 2 : ℝ)) / t ^ (2 : ℕ) := by
            rw [← hAbsSq]
            field_simp [abs_ne_zero.mpr ht0]
    calc
      ∫ t in -(2 * T0)..-T0, f t ≤ ∫ t in -(2 * T0)..-T0, g t := hmono
      _ = (2 * Real.exp (-(1 / 2 : ℝ))) *
          (∫ t in -(2 * T0)..-T0, (1 : ℝ) / t ^ (2 : ℕ)) := by
            calc
              ∫ t in -(2 * T0)..-T0, g t =
                  ∫ t in -(2 * T0)..-T0,
                    (2 * Real.exp (-(1 / 2 : ℝ))) * ((1 : ℝ) / t ^ (2 : ℕ)) := by
                      refine intervalIntegral.integral_congr_ae ?_
                      filter_upwards with t
                      simp [g, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
              _ = (2 * Real.exp (-(1 / 2 : ℝ))) *
                    (∫ t in -(2 * T0)..-T0, (1 : ℝ) / t ^ (2 : ℕ)) := by
                      rw [intervalIntegral.integral_const_mul]
      _ = (2 * Real.exp (-(1 / 2 : ℝ))) * (1 / (2 * T0)) := by
            rw [hInvSqLeft]
      _ = Real.exp (-(1 / 2 : ℝ)) / T0 := by
            field_simp [ne_of_gt hT0]
  have hRightBound :
      ∫ t in T0..(2 * T0), f t ≤ Real.exp (-(1 / 2 : ℝ)) / T0 := by
    have hmono :
        ∫ t in T0..(2 * T0), f t ≤ ∫ t in T0..(2 * T0), g t := by
      refine
        intervalIntegral.integral_mono_on
          (μ := volume) (a := T0) (b := 2 * T0)
          (f := f) (g := g) (by linarith) hRightInt hRightMajInt ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc T0 (2 * T0) := by
        simpa [Set.uIcc_of_le (show T0 ≤ 2 * T0 by nlinarith [hT0])] using ht
      have ht0 : t ≠ 0 := by
        have ht_ge : T0 ≤ t := ht_mem.1
        exact_mod_cast (show t ≠ 0 by linarith [ht_ge, hT0])
      have hExpScale :
          Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ Real.exp (-(1 / 2 : ℝ)) / |t| := by
        have hMul :
            Real.exp (-(t ^ (2 : ℕ) / 2)) * |t| ≤ Real.exp (-(1 / 2 : ℝ)) := by
          simpa [mul_comm] using abs_mul_exp_neg_sq_div_two_le_exp_neg_half t
        exact (le_div_iff₀ (abs_pos.mpr ht0)).2 hMul
      have hAbsSq : |t| ^ (2 : ℕ) = t ^ (2 : ℕ) := by
        simpa [pow_two] using (sq_abs t)
      calc
        f t ≤ 2 * Real.exp (-(t ^ (2 : ℕ) / 2)) / |t| := by
            exact dampedQuotientKernel_norm_le_two_exp_div_abs (μ := μ) ht0
        _ ≤ 2 * (Real.exp (-(1 / 2 : ℝ)) / |t|) / |t| := by
            gcongr
        _ = 2 * Real.exp (-(1 / 2 : ℝ)) / t ^ (2 : ℕ) := by
            rw [← hAbsSq]
            field_simp [abs_ne_zero.mpr ht0]
    calc
      ∫ t in T0..(2 * T0), f t ≤ ∫ t in T0..(2 * T0), g t := hmono
      _ = (2 * Real.exp (-(1 / 2 : ℝ))) *
          (∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ)) := by
            calc
              ∫ t in T0..(2 * T0), g t =
                  ∫ t in T0..(2 * T0),
                    (2 * Real.exp (-(1 / 2 : ℝ))) * ((1 : ℝ) / t ^ (2 : ℕ)) := by
                      refine intervalIntegral.integral_congr_ae ?_
                      filter_upwards with t
                      simp [g, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
              _ = (2 * Real.exp (-(1 / 2 : ℝ))) *
                    (∫ t in T0..(2 * T0), (1 : ℝ) / t ^ (2 : ℕ)) := by
                      rw [intervalIntegral.integral_const_mul]
      _ = (2 * Real.exp (-(1 / 2 : ℝ))) * (1 / (2 * T0)) := by
            rw [integral_invSq_scaleTwoTail hT0]
      _ = Real.exp (-(1 / 2 : ℝ)) / T0 := by
            field_simp [ne_of_gt hT0]
  -- Proof comment: estimate both scale-two tails by the reciprocal-square majorant and evaluate
  -- the exact annulus primitive on each side.
  calc
    (1 / (2 * Real.pi)) *
        ((∫ t in -(2 * T0)..-T0, f t) + ∫ t in T0..(2 * T0), f t) ≤
      (1 / (2 * Real.pi)) *
        ((Real.exp (-(1 / 2 : ℝ)) / T0) + (Real.exp (-(1 / 2 : ℝ)) / T0)) := by
          gcongr
    _ = (Real.exp (-(1 / 2 : ℝ)) / Real.pi) / T0 := by
          field_simp [Real.pi_ne_zero, ne_of_gt hT0]
          ring

/-- Helper for Theorem 15.51: the elementary factor `1 / n` is dominated by the normalized
third-moment scale `β / √n`. -/
private lemma berryEsseenOneDivNat_le_scaledThirdMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    1 / (n : ℝ) ≤
      absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale is already known to dominate `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast n.2
  have hsqrt_ge_one : 1 ≤ Real.sqrt (n : ℝ) := by
    simpa using Real.sqrt_le_sqrt hn_ge_one
  have hInvSqrt_le_one : (Real.sqrt (n : ℝ))⁻¹ ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le zero_lt_one hsqrt_ge_one
  have hOneDivNat_le_invSqrt :
      1 / (n : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by
    -- Proof comment: write `1 / n` as the square of `1 / √n`, then use `1 / √n ≤ 1`.
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    calc
      1 / (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ := by
        field_simp [hsqrt_ne]
        rw [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      _ ≤ (Real.sqrt (n : ℝ))⁻¹ * 1 := by
            exact mul_le_mul_of_nonneg_left hInvSqrt_le_one
              (inv_nonneg.mpr (le_of_lt hsqrt_pos))
      _ = (Real.sqrt (n : ℝ))⁻¹ := by ring
  calc
    1 / (n : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := hOneDivNat_le_invSqrt
    _ ≤ β * (Real.sqrt (n : ℝ))⁻¹ := by
          simpa [one_mul] using
            (mul_le_mul_of_nonneg_right hβ_ge_one
              (inv_nonneg.mpr (le_of_lt hsqrt_pos)))
    _ = β / Real.sqrt (n : ℝ) := by
          rw [div_eq_mul_inv]
    _ =
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
          simp [β, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 15.51: the proxy/Gaussian part of the three central scale-two pieces is
already controlled by the standard `β / √n` scale. -/
private lemma standardizedLawGaussianProxyInnerMiddleIntegral_le_scaledThirdMoment
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let R : ℝ := min T0 1
    let proxy : ℝ → ℝ := fun t ↦
      |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
    (1 / (2 * Real.pi)) *
        ((∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t) ≤
      (1 / (2 * Real.pi)) *
        (absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let R : ℝ := min T0 1
  let proxy : ℝ → ℝ := fun t ↦
    |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ)) / 2) / (4 * (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale is still at least `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hT0_nonneg : 0 ≤ T0 := by
    -- Proof comment: the natural cutoff is nonnegative because both `√n` and `β⁻¹` are.
    dsimp [T0]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hProxyLeft : IntervalIntegrable proxy volume (-T0) (-R) := by
    -- Proof comment: the proxy majorant is continuous on each compact central subinterval.
    refine Continuous.intervalIntegrable ?_ (-T0) (-R)
    continuity
  have hProxyInner : IntervalIntegrable proxy volume (-R) R := by
    -- Proof comment: continuity gives integrability on the canonical inner block as well.
    refine Continuous.intervalIntegrable ?_ (-R) R
    continuity
  have hProxyRight : IntervalIntegrable proxy volume R T0 := by
    -- Proof comment: the same continuity argument applies on the positive middle band.
    refine Continuous.intervalIntegrable ?_ R T0
    continuity
  have hProxySplitLeft :
      ∫ t in -T0..R, proxy t =
        (∫ t in -T0..-R, proxy t) + ∫ t in -R..R, proxy t := by
    -- Proof comment: first split the central proxy integral at `-R`.
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (f := proxy) hProxyLeft hProxyInner).symm
  have hProxySplit :
      ∫ t in -T0..T0, proxy t =
        (∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
    -- Proof comment: then split the remaining block at `R` and reassociate the sum.
    calc
      ∫ t in -T0..T0, proxy t =
          (∫ t in -T0..R, proxy t) + ∫ t in R..T0, proxy t := by
            simpa using
              (intervalIntegral.integral_add_adjacent_intervals
                (f := proxy) (hProxyLeft.trans hProxyInner) hProxyRight).symm
      _ =
          ((∫ t in -T0..-R, proxy t) + ∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
            rw [hProxySplitLeft]
      _ =
          (∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t := by
            ring
  have hProxyFull :
      ∫ t in -T0..T0, proxy t ≤ 1 / (n : ℝ) := by
    -- Proof comment: the exact symmetric proxy integral is already bounded by `1 / n`.
    simpa [proxy, T0] using
      proxyGaussianWeightedMajorantIntegral_le_one_div (n := n) hT0_nonneg
  have hScaled :
      1 / (n : ℝ) ≤
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
    -- Proof comment: convert the residual `1 / n` factor to the global Berry--Esseen scale.
    exact
      berryEsseenOneDivNat_le_scaledThirdMoment
        P X hX_iid hX_mean hX_var hX_third n
  calc
    (1 / (2 * Real.pi)) *
        ((∫ t in -T0..-R, proxy t) + (∫ t in -R..R, proxy t) + ∫ t in R..T0, proxy t) =
      (1 / (2 * Real.pi)) * (∫ t in -T0..T0, proxy t) := by
        rw [hProxySplit]
    _ ≤ (1 / (2 * Real.pi)) * (1 / (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hProxyFull (by positivity)
    _ ≤
        (1 / (2 * Real.pi)) *
          (absoluteMoment (X 1) 3 P /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hScaled (by positivity)

/-- Helper for Theorem 15.51: the symmetric absolute-value integral on `[-T, T]` is `T²`. -/
private lemma integral_abs_symm
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, |t| = T ^ (2 : ℕ) := by
  have hHalf : ∫ t in 0..T, |t| = T ^ (2 : ℕ) / 2 := by
    -- Proof comment: on `[0, T]`, the absolute value drops and the standard power-integral
    -- formula gives the exact half-window mass.
    calc
      ∫ t in 0..T, |t| = ∫ t in 0..T, t := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        rw [Set.uIcc_of_le hT] at ht
        exact abs_of_nonneg ht.1
      _ = T ^ (2 : ℕ) / 2 := by
        simpa using (intervalIntegral.integral_id (a := (0 : ℝ)) (b := T))
  have hNegEq : ∫ t in -T..0, |t| = ∫ t in 0..T, |t| := by
    -- Proof comment: reflect the negative half-window through `t ↦ -t`; the integrand is even.
    calc
      ∫ t in -T..0, |t| = ∫ t in -T..0, |(-t)| := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t
        simp
      _ = ∫ t in 0..T, |t| := by
        simpa using
          (intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦ |t|) (a := -T) (b := 0))
  have hSplit :
      ∫ t in -T..T, |t| = (∫ t in -T..0, |t|) + ∫ t in 0..T, |t| := by
    have hLeft : IntervalIntegrable (fun t : ℝ ↦ |t|) volume (-T) 0 :=
      Continuous.intervalIntegrable continuous_abs (-T) 0
    have hRight : IntervalIntegrable (fun t : ℝ ↦ |t|) volume 0 T :=
      Continuous.intervalIntegrable continuous_abs 0 T
    -- Proof comment: split the symmetric interval at the origin.
    simpa using (intervalIntegral.integral_add_adjacent_intervals hLeft hRight).symm
  calc
    ∫ t in -T..T, |t| = (∫ t in 0..T, |t|) + ∫ t in 0..T, |t| := by
      rw [hSplit, hNegEq]
    _ = T ^ (2 : ℕ) := by
      rw [hHalf]
      ring

/-- Helper for Theorem 15.51: the whole-line Gaussian square moment at exponent `2 / 3` is the
exact normalization used in the large-`n` central-window branch. -/
private lemma integral_sq_mul_exp_neg_twoThird_mul_sq :
    ∫ t : ℝ, t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))) =
      (3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2) := by
  let v : NNReal := (3 / 4 : NNReal)
  have hv : v ≠ 0 := by
    norm_num [v]
  have hMean : ∫ x, x ∂(gaussianReal (0 : ℝ) v) = 0 := by
    -- Proof comment: the centered Gaussian `gaussianReal 0 (3 / 4)` has zero mean.
    simp [integral_id_gaussianReal, v]
  have hSecond : ∫ x, x ^ (2 : ℕ) ∂(gaussianReal (0 : ℝ) v) = (3 / 4 : ℝ) := by
    -- Proof comment: convert the second moment into the Gaussian variance and use the exact
    -- variance parameter `3 / 4`.
    calc
      ∫ x, x ^ (2 : ℕ) ∂(gaussianReal (0 : ℝ) v) = Var[id; gaussianReal (0 : ℝ) v] := by
        exact (variance_of_integral_eq_zero measurable_id.aemeasurable hMean).symm
      _ = v := by
        simp [variance_id_gaussianReal]
      _ = (3 / 4 : ℝ) := by
        norm_num [v]
  have hDensity :
      ∫ x, gaussianPDFReal (0 : ℝ) v x * x ^ (2 : ℕ) = (3 / 4 : ℝ) := by
    have hBase :=
      integral_gaussianReal_eq_integral_smul
        (μ := (0 : ℝ)) (v := v) (f := fun x : ℝ ↦ x ^ (2 : ℕ)) hv
    -- Proof comment: rewrite the Gaussian-measure moment as a Lebesgue integral against the
    -- explicit Gaussian density.
    rw [hSecond] at hBase
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hBase.symm
  have hCoeff :
      √3 * √Real.pi / √2 * (√4 / √3 * ((√Real.pi)⁻¹ * (√2)⁻¹)) = (1 : ℝ) := by
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      have hsq : (Real.sqrt (4 : ℝ)) ^ (2 : ℕ) = 4 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (4 : ℝ) by positivity)]
      have hnonneg : 0 ≤ Real.sqrt (4 : ℝ) := by
        positivity
      nlinarith
    have hsqrt2sq : (Real.sqrt (2 : ℝ)) ^ (2 : ℕ) = 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
    -- Proof comment: the Gaussian-density normalizing coefficient collapses to `1` after
    -- expanding `v = 3 / 4` and clearing the square-root denominators.
    rw [hsqrt4]
    field_simp [show Real.sqrt (3 : ℝ) ≠ 0 by positivity,
      show Real.sqrt Real.pi ≠ 0 by positivity,
      show Real.sqrt (2 : ℝ) ≠ 0 by positivity]
    rw [hsqrt2sq]
  have hPoint :
      ∀ x : ℝ,
        x ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) =
          Real.sqrt (3 * Real.pi / 2) * (gaussianPDFReal (0 : ℝ) v x * x ^ (2 : ℕ)) := by
    intro x
    rw [gaussianPDFReal_def]
    norm_num [v]
    have hExp :
        Real.exp (-x ^ (2 : ℕ) / (3 / 2 : ℝ)) =
          Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) := by
      congr 1
      ring
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
      have hsq : (Real.sqrt (4 : ℝ)) ^ (2 : ℕ) = 4 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (4 : ℝ) by positivity)]
      have hnonneg : 0 ≤ Real.sqrt (4 : ℝ) := by
        positivity
      nlinarith
    have hPointR :
        √3 * √Real.pi / √2 *
            (√4 / √3 * ((√Real.pi)⁻¹ * (√2)⁻¹) *
              Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) * x ^ (2 : ℕ)) =
          x ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) := by
      -- Proof comment: after normalizing the density coefficient and the exponent, the pointwise
      -- identity is just commutative reassociation of the remaining factors.
      calc
        √3 * √Real.pi / √2 *
            (√4 / √3 * ((√Real.pi)⁻¹ * (√2)⁻¹) *
              Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) * x ^ (2 : ℕ)) =
            (√3 * √Real.pi / √2 * (√4 / √3 * ((√Real.pi)⁻¹ * (√2)⁻¹))) *
              (Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) * x ^ (2 : ℕ)) := by
                ring
        _ = Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) * x ^ (2 : ℕ) := by
              rw [hCoeff]
              simp
        _ = x ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * x ^ (2 : ℕ))) := by
              ring_nf
    -- Proof comment: substitute the exact density exponent `-(2 / 3) * x²` and the normalized
    -- Gaussian prefactor.
    simpa [hExp, hsqrt4] using hPointR.symm
  -- Proof comment: identify the target integrand with the Gaussian-density integrand pointwise,
  -- then substitute the exact second moment of `gaussianReal 0 (3 / 4)`.
  calc
    ∫ t : ℝ, t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))) =
        ∫ t : ℝ, Real.sqrt (3 * Real.pi / 2) * (gaussianPDFReal (0 : ℝ) v t * t ^ (2 : ℕ)) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          exact hPoint t
    _ = Real.sqrt (3 * Real.pi / 2) * ∫ x, gaussianPDFReal (0 : ℝ) v x * x ^ (2 : ℕ) := by
          rw [integral_const_mul]
    _ = (3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2) := by
          rw [hDensity]
          ring

/-- Helper for Theorem 15.51: the exact whole-line Gaussian-square majorant already lies below the
residual coefficient `1 / 21`. -/
private lemma gaussianSquareIntegral_twoThird_le_one_div_twentyone :
    (1 / (12 * Real.pi : ℝ)) * ((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2)) ≤ 1 / 21 := by
  have hTarget :
      (3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2) ≤ 4 * Real.pi / 7 := by
    have hsqrt :
        (Real.sqrt (3 * Real.pi / 2)) ^ (2 : ℕ) = 3 * Real.pi / 2 := by
      simpa using Real.sq_sqrt (show 0 ≤ 3 * Real.pi / 2 by positivity)
    -- Proof comment: after squaring both sides, `π > 3` is already enough for the required
    -- numerical inequality.
    nlinarith [Real.pi_gt_three, hsqrt]
  calc
    (1 / (12 * Real.pi : ℝ)) * ((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2)) =
        (((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2)) / (12 * Real.pi)) := by
          ring
    _ ≤ (4 * Real.pi / 7) / (12 * Real.pi) := by
          gcongr
    _ = 1 / 21 := by
          field_simp [Real.pi_ne_zero]
          ring

/-- Helper for Theorem 15.51: any scale parameter `β ≥ 1` also dominates its reciprocal. -/
private lemma inv_le_self_of_one_le
    {β : ℝ} (hβ_ge_one : 1 ≤ β) :
    β⁻¹ ≤ β := by
  have hInv_le_one : β⁻¹ ≤ (1 : ℝ) := by
    -- Proof comment: reciprocals reverse the inequality `1 ≤ β` on the positive half-line.
    simpa using one_div_le_one_div_of_le zero_lt_one hβ_ge_one
  -- Proof comment: chain the reciprocal bound `β⁻¹ ≤ 1` with the hypothesis `1 ≤ β`.
  exact le_trans hInv_le_one hβ_ge_one

/-- Helper for Theorem 15.51: a nonnegative interval integral is bounded by the corresponding
whole-line integral of the same function. -/
private lemma intervalIntegral_le_integral_univ_of_nonneg
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_nonneg : 0 ≤ᵐ[volume] f) (hf_int : Integrable f) :
    ∫ t in a..b, f t ≤ ∫ t : ℝ, f t := by
  have hMeasure :=
    MeasureTheory.integral_mono_measure
      (μ := volume.restrict (Set.Ioc a b))
      (ν := volume)
      (f := f)
      (Measure.restrict_le_self) hf_nonneg hf_int
  -- Proof comment: rewrite the interval integral as an integral against the restricted measure,
  -- then apply measure monotonicity on the nonnegative integrand.
  simpa [intervalIntegral.integral_of_le hab] using hMeasure

/-- Helper for Theorem 15.51: the sharp scale-two tail coefficient together with the central
residual package stays below the target Berry--Esseen constant
`0.8 - 1 / √(2π)`. -/
private lemma scaleTwoTailAndCentralCoefficient_le_target :
    (Real.exp (-(1 / 2 : ℝ)) / Real.pi) + (1 / (2 * Real.pi) + (1 / 21 : ℝ)) ≤
      (0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi) := by
  have hExpHalfLower : (633 / 384 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := by
    have hSeries := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ)) 5
    -- Proof comment: keep the first five nonnegative terms of the exponential series at `1 / 2`.
    norm_num at hSeries ⊢
    exact hSeries
  have hExpHalfUpper : Real.exp (-(1 / 2 : ℝ)) ≤ (384 / 633 : ℝ) := by
    have hPos : 0 < (633 / 384 : ℝ) := by norm_num
    -- Proof comment: invert the lower bound on `exp (1 / 2)` to obtain an explicit rational
    -- upper bound on `exp (-1 / 2)`.
    simpa [Real.exp_neg] using one_div_le_one_div_of_le hPos hExpHalfLower
  have hPiLower : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hPiInvUpper : 1 / Real.pi ≤ 1 / (3.14 : ℝ) := by
    -- Proof comment: the rational lower bound on `π` gives a convenient reciprocal upper bound.
    exact one_div_le_one_div_of_le (by positivity : 0 < (3.14 : ℝ)) hPiLower.le
  have hHalfPiInvUpper : 1 / (2 * Real.pi) ≤ 1 / (2 * (3.14 : ℝ)) := by
    exact one_div_le_one_div_of_le (by positivity : 0 < (2 * (3.14 : ℝ))) (by nlinarith)
  have hSqrtLower : (501 / 200 : ℝ) ≤ Real.sqrt (2 * (3.14 : ℝ)) := by
    -- Proof comment: `2.505² ≤ 6.28`, so `2.505` is a usable rational lower bound for
    -- `√(2 * 3.14)`.
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (3.14 : ℝ)) := by positivity
    have hsq : ((501 / 200 : ℝ) ^ (2 : ℕ)) ≤ 2 * (3.14 : ℝ) := by norm_num
    nlinarith [hsqrt_nonneg, hsq, Real.sq_sqrt (show 0 ≤ 2 * (3.14 : ℝ) by positivity)]
  have hInvSqrtUpper : 1 / Real.sqrt (2 * (3.14 : ℝ)) ≤ (200 / 501 : ℝ) := by
    -- Proof comment: convert the square-root lower bound into the reciprocal upper bound that the
    -- target coefficient uses.
    simpa [one_div] using one_div_le_one_div_of_le (by positivity : 0 < (501 / 200 : ℝ))
      hSqrtLower
  have hNumeric :
      ((384 / 633 : ℝ) * (1 / (3.14 : ℝ))) + (1 / (2 * (3.14 : ℝ)) + (1 / 21 : ℝ)) ≤
        (0.8 : ℝ) - (200 / 501 : ℝ) := by
    norm_num
  -- Proof comment: bound the left side from above using the explicit `exp (-1 / 2)` and `π`
  -- estimates, bound the reciprocal square root on the right from above, then compare the two
  -- rational approximations.
  calc
    (Real.exp (-(1 / 2 : ℝ)) / Real.pi) + (1 / (2 * Real.pi) + (1 / 21 : ℝ)) ≤
        ((384 / 633 : ℝ) * (1 / (3.14 : ℝ))) + (1 / (2 * (3.14 : ℝ)) + (1 / 21 : ℝ)) := by
          gcongr
          · simpa [div_eq_mul_inv] using
              mul_le_mul hExpHalfUpper hPiInvUpper (by positivity) (by positivity)
    _ ≤ (0.8 : ℝ) - (200 / 501 : ℝ) := hNumeric
    _ ≤ (0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi) := by
          have hInvSqrtPi :
              1 / Real.sqrt (2 * Real.pi) ≤ (200 / 501 : ℝ) := by
            have hSqrtPi :
                Real.sqrt (2 * (3.14 : ℝ)) ≤ Real.sqrt (2 * Real.pi) := by
              gcongr
            exact (one_div_le_one_div_of_le (by positivity : 0 < Real.sqrt (2 * (3.14 : ℝ)))
              hSqrtPi).trans hInvSqrtUpper
          linarith

/-- Helper for Theorem 15.51: in the one-step case `n = 1`, the law-term contribution on the
natural window is dominated by the elementary majorant `|t| / 6`. -/
private lemma standardizedLawGaussianLawTermNaturalWindowIntegral_oneStep
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) (hn1 : (n : ℕ) = 1) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let law : ℝ → ℝ := fun t ↦
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤
      (1 / 21 : ℝ) *
        (absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let law : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
  let scale : ℝ :=
    absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale still dominates `1` on the natural
    -- Berry--Esseen window.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hT0_nonneg : 0 ≤ T0 := by
    -- Proof comment: the natural cutoff is nonnegative because both `√n` and `β⁻¹` are.
    dsimp [T0]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hLawInt : IntervalIntegrable law volume (-T0) T0 := by
    -- Proof comment: the law-term majorant is continuous on the compact natural window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  have hT0_eq : T0 = β⁻¹ := by
    -- Proof comment: in the one-step branch the natural window has radius exactly `β⁻¹`.
    dsimp [T0]
    simp [hn1]
  have hT0_le_one : T0 ≤ 1 := by
    -- Proof comment: `β ≥ 1` implies the one-step window radius `β⁻¹` is at most `1`.
    rw [hT0_eq]
    simpa using one_div_le_one_div_of_le zero_lt_one hβ_ge_one
  have hLawPointwise :
      ∀ t ∈ Set.Icc (-T0) T0, law t ≤ |t| / 6 := by
    intro t ht
    have ht_abs_le : |t| ≤ T0 := by
      rcases ht with ⟨ht_left, ht_right⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have ht_abs_le_one : |t| ≤ 1 := ht_abs_le.trans hT0_le_one
    have hExpProd_le_one :
        Real.exp (-(t ^ (2 : ℕ) / 2)) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) ≤ 1 := by
      have hExp_le_one : Real.exp (-(t ^ (2 : ℕ) / 2)) ≤ 1 := by
        have hExponent_nonpos : -(t ^ (2 : ℕ) / 2) ≤ 0 := by
          nlinarith
        exact Real.exp_le_one_iff.mpr hExponent_nonpos
      have hPow_le_one :
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) ≤ 1 := by
        simp [hn1]
      have hExp_nonneg : 0 ≤ Real.exp (-(t ^ (2 : ℕ) / 2)) := by positivity
      have hPow_nonneg :
          0 ≤
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) := by
        positivity
      nlinarith
    have hAbsSq_nonneg : 0 ≤ |t| ^ (2 : ℕ) := by positivity
    have hsq_le_mul : |t| ^ (2 : ℕ) ≤ |t| * T0 := by
      have hAbs_nonneg : 0 ≤ |t| := abs_nonneg t
      nlinarith [hAbs_nonneg, ht_abs_le]
    have hBetaScale :
        absoluteMoment (X 1) 3 P /
            (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ))) =
          β / 6 := by
      dsimp [β]
      simp [hn1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      law t =
          (absoluteMoment (X 1) 3 P /
              (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))) *
            (|t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
              Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1)) := by
            dsimp [law]
            ring
      _ =
          (β / 6) * (|t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1)) := by
            rw [hBetaScale]
      _ ≤ (β / 6) * (|t| ^ (2 : ℕ)) := by
            have hProd_le :
                |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
                    Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^
                      ((n : ℕ) - 1) ≤
                  |t| ^ (2 : ℕ) := by
              have hMul := mul_le_mul_of_nonneg_left hExpProd_le_one hAbsSq_nonneg
              simpa [mul_assoc] using hMul
            exact mul_le_mul_of_nonneg_left hProd_le (by positivity : 0 ≤ β / 6)
      _ ≤ (β / 6) * (|t| * T0) := by
            gcongr
      _ = |t| / 6 := by
            rw [hT0_eq]
            field_simp [hβ_pos.ne']
  have hAbsInt : IntervalIntegrable (fun t : ℝ ↦ |t| / 6) volume (-T0) T0 := by
    -- Proof comment: the comparison kernel `|t| / 6` is continuous on the compact window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  have hLawBound :
      ∫ t in -T0..T0, law t ≤ ∫ t in -T0..T0, |t| / 6 := by
    -- Proof comment: dominate the one-step law term by `|t| / 6` on the whole natural window.
    refine
      intervalIntegral.integral_mono_on
        (μ := volume) (a := -T0) (b := T0) (f := law) (g := fun t ↦ |t| / 6)
        (by linarith) hLawInt hAbsInt ?_
    intro t ht
    have ht_mem : t ∈ Set.Icc (-T0) T0 := by
      simpa [Set.uIcc_of_le hT0_nonneg] using ht
    exact hLawPointwise t ht_mem
  have hAbsIntegral :
      ∫ t in -T0..T0, |t| / 6 = T0 ^ (2 : ℕ) / 6 := by
    -- Proof comment: evaluate the symmetric absolute-value integral exactly and divide by `6`.
    calc
      ∫ t in -T0..T0, |t| / 6 = ∫ t in -T0..T0, (1 / 6 : ℝ) * |t| := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        ring
      _ = (1 / 6 : ℝ) * ∫ t in -T0..T0, |t| := by
        rw [intervalIntegral.integral_const_mul]
      _ = T0 ^ (2 : ℕ) / 6 := by
        rw [integral_abs_symm hT0_nonneg]
        ring
  have hSmall :
      (1 / (2 * Real.pi)) * (T0 ^ (2 : ℕ) / 6) ≤ (1 / 21 : ℝ) * scale := by
    -- Proof comment: in the one-step branch `T0 = β⁻¹`, so the left side is at most the
    -- explicit numerical constant `1 / (12π)`, which is below `1 / 21`.
    have hScale_eq : scale = β := by
      dsimp [scale, β]
      simp [hn1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hT0_sq_le_one : T0 ^ (2 : ℕ) ≤ 1 := by
      nlinarith [hT0_nonneg, hT0_le_one]
    have hPi :
        (1 / (2 * Real.pi)) * (1 / 6 : ℝ) ≤ (1 / 21 : ℝ) := by
      have hpiLower : (6 : ℝ) ≤ 2 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      have hInv : 1 / (2 * Real.pi) ≤ (1 / 6 : ℝ) := by
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hpiLower
      nlinarith
    calc
      (1 / (2 * Real.pi)) * (T0 ^ (2 : ℕ) / 6) ≤
          (1 / (2 * Real.pi)) * (1 / 6 : ℝ) := by
            gcongr
      _ ≤ (1 / 21 : ℝ) := hPi
      _ ≤ (1 / 21 : ℝ) * scale := by
            rw [hScale_eq]
            nlinarith
  calc
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤
        (1 / (2 * Real.pi)) * (∫ t in -T0..T0, |t| / 6) := by
          exact mul_le_mul_of_nonneg_left hLawBound (by positivity)
    _ = (1 / (2 * Real.pi)) * (T0 ^ (2 : ℕ) / 6) := by
          rw [hAbsIntegral]
    _ ≤ (1 / 21 : ℝ) * scale := hSmall

/-- Helper for Theorem 15.51: for `2 ≤ n`, the law-term contribution on the natural window is
dominated by the integrable Gaussian-square majorant with exponent `2 / 3`. -/
private lemma standardizedLawGaussianLawTermNaturalWindowIntegral_largeN
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) (hn2 : 2 ≤ (n : ℕ)) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let law : ℝ → ℝ := fun t ↦
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤
      (1 / 21 : ℝ) *
        (absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let law : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
  let scale : ℝ :=
    absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale still dominates `1` on the natural
    -- Berry--Esseen window.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hT0_nonneg : 0 ≤ T0 := by
    -- Proof comment: the natural cutoff is nonnegative because both `√n` and `β⁻¹` are.
    dsimp [T0]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hLawInt : IntervalIntegrable law volume (-T0) T0 := by
    -- Proof comment: the law-term majorant is continuous on the compact natural window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  have hLawMajorant :
      ∀ t ∈ Set.Icc (-T0) T0, law t ≤
        (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
    intro t ht
    have hSquare :
        (((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) = t ^ (2 : ℕ) / (n : ℝ) := by
      have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      calc
        (((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) =
            (Real.sqrt (n : ℝ))⁻¹ ^ (2 : ℕ) * t ^ (2 : ℕ) := by
              ring
        _ = t ^ (2 : ℕ) / (n : ℝ) := by
              rw [inv_pow, hsqrt_sq]
              field_simp [ne_of_gt hsqrt_n_pos]
    have hExpPow :
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) =
          Real.exp (-((((n : ℝ) - 1) / (3 * (n : ℝ))) * t ^ (2 : ℕ))) := by
      rw [hSquare, ← Real.exp_nat_mul]
      have hn_pred : (((n : ℕ) - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        simpa [Nat.pred_eq_sub_one] using (Nat.cast_pred (Nat.ne_of_gt n.2))
      congr 1
      rw [hn_pred]
      field_simp [show (n : ℝ) ≠ 0 by positivity]
    have hExpBound :
        Real.exp (-(t ^ (2 : ℕ) / 2)) *
            Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) ≤
          Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))) := by
      rw [hExpPow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hCoeff : (2 / 3 : ℝ) ≤ (1 / 2 : ℝ) + ((n : ℝ) - 1) / (3 * (n : ℝ)) := by
        have hDenom : (6 : ℝ) ≤ 3 * (n : ℝ) := by
          have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
          nlinarith
        have hRewrite :
            ((n : ℝ) - 1) / (3 * (n : ℝ)) = (1 / 3 : ℝ) - 1 / (3 * (n : ℝ)) := by
          field_simp [show (n : ℝ) ≠ 0 by positivity]
        rw [hRewrite]
        have hThirdInv : 1 / (3 * (n : ℝ)) ≤ (1 / 6 : ℝ) := by
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hDenom
        nlinarith
      have ht_sq_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
      nlinarith
    calc
      law t =
          (scale / 6) * (|t| ^ (2 : ℕ) *
            (Real.exp (-(t ^ (2 : ℕ) / 2)) *
              Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1))) := by
            dsimp [law, scale]
            ring
      _ ≤ (scale / 6) * (|t| ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
            have hScaleSix_nonneg : 0 ≤ scale / 6 := by
              dsimp [scale]
              rw [absoluteMoment_eq_expectation_abs_pow]
              positivity
            have hAbsSq_nonneg : 0 ≤ |t| ^ (2 : ℕ) := by positivity
            have hInner := mul_le_mul_of_nonneg_left hExpBound hAbsSq_nonneg
            exact mul_le_mul_of_nonneg_left hInner hScaleSix_nonneg
      _ = (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
            congr 1
            simpa [pow_two] using (sq_abs t)
  have hMajInt :
      Integrable (fun t : ℝ ↦ (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))))) := by
    -- Proof comment: the Gaussian-square majorant is integrable on the whole line.
    refine Integrable.const_mul ?_ (scale / 6)
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (2 / 3 : ℝ)) (s := (2 : ℝ))
        (by positivity) (by norm_num : (-1 : ℝ) < 2))
  have hMajBound :
      ∫ t in -T0..T0, law t ≤
        ∫ t : ℝ, (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
    have hScaleSix_nonneg : 0 ≤ scale / 6 := by
      dsimp [scale]
      rw [absoluteMoment_eq_expectation_abs_pow]
      positivity
    have hMajNonneg :
        0 ≤ᵐ[volume] fun t : ℝ ↦
          (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
      filter_upwards with t
      have hPow_nonneg : 0 ≤ t ^ (2 : ℕ) := by positivity
      have hExp_nonneg : 0 ≤ Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))) := by positivity
      exact mul_nonneg hScaleSix_nonneg (mul_nonneg hPow_nonneg hExp_nonneg)
    have hMajIntInterval :
        IntervalIntegrable
          (fun t : ℝ ↦ (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))))
          volume (-T0) T0 := hMajInt.intervalIntegrable
    have hMono :
        ∫ t in -T0..T0, law t ≤
          ∫ t in -T0..T0, (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) := by
      refine
        intervalIntegral.integral_mono_on
          (μ := volume) (a := -T0) (b := T0) (f := law)
          (g := fun t : ℝ ↦ (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))))
          (by linarith) hLawInt hMajIntInterval ?_
      intro t ht
      have ht_mem : t ∈ Set.Icc (-T0) T0 := by
        simpa [Set.uIcc_of_le hT0_nonneg] using ht
      exact hLawMajorant t ht_mem
    exact hMono.trans (intervalIntegral_le_integral_univ_of_nonneg (by linarith) hMajNonneg hMajInt)
  have hMajorantEval :
      ∫ t : ℝ, (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ)))) =
        (scale / 6) * ((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2)) := by
    rw [integral_const_mul, integral_sq_mul_exp_neg_twoThird_mul_sq]
  have hScale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    rw [absoluteMoment_eq_expectation_abs_pow]
    positivity
  calc
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤
        (1 / (2 * Real.pi)) *
          (∫ t : ℝ, (scale / 6) * (t ^ (2 : ℕ) * Real.exp (-((2 / 3 : ℝ) * t ^ (2 : ℕ))))) := by
          exact mul_le_mul_of_nonneg_left hMajBound (by positivity)
    _ = (1 / (2 * Real.pi)) * ((scale / 6) * ((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2))) := by
          rw [hMajorantEval]
    _ = scale * ((1 / (12 * Real.pi : ℝ)) * ((3 / 4 : ℝ) * Real.sqrt (3 * Real.pi / 2))) := by
          ring
    _ ≤ scale * (1 / 21 : ℝ) := by
          exact
            mul_le_mul_of_nonneg_left gaussianSquareIntegral_twoThird_le_one_div_twentyone
              hScale_nonneg
    _ = (1 / 21 : ℝ) * scale := by ring

/-- Helper for Theorem 15.51: the law-term part of the damped split already fits inside the
residual `1 / 21` coefficient on the full natural window `[-T0, T0]`. -/
private lemma standardizedLawGaussianLawTermNaturalWindowIntegral_le_oneDivTwentyOneScaled
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let law : ℝ → ℝ := fun t ↦
      absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
          Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤
      (1 / 21 : ℝ) *
        (absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let law : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
  let scale : ℝ :=
    absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale still dominates `1` on the natural
    -- Berry--Esseen window.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    positivity
  have hT0_nonneg : 0 ≤ T0 := by
    -- Proof comment: the natural cutoff is nonnegative because both `√n` and `β⁻¹` are.
    dsimp [T0]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hT0_pos : 0 < T0 := by
    -- Proof comment: the natural cutoff is strictly positive on positive `n`.
    dsimp [T0]
    exact mul_pos hsqrt_n_pos (inv_pos.mpr hβ_pos)
  have hLawInt : IntervalIntegrable law volume (-T0) T0 := by
    -- Proof comment: the law-term majorant is continuous on the compact natural window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  by_cases hn1 : (n : ℕ) = 1
  · simpa using
      standardizedLawGaussianLawTermNaturalWindowIntegral_oneStep
        P X hX_iid hX_mean hX_var hX_third n hn1
  · have hn2 : 2 ≤ (n : ℕ) := by
      have hn_one_le : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt n.2
      have hn_gt_one : 1 < (n : ℕ) := lt_of_le_of_ne hn_one_le (Ne.symm hn1)
      exact Nat.succ_le_iff.mpr hn_gt_one
    simpa using
      standardizedLawGaussianLawTermNaturalWindowIntegral_largeN
        P X hX_iid hX_mean hX_var hX_third n hn2

/-- Helper for Theorem 15.51: the full central natural window is already controlled by the
remaining coefficient `(1 / (2π)) + (1 / 21)`. -/
private lemma standardizedLawGaussianCentralWindowIntegral_le_remainingGap
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
    let f : ℝ → ℝ := fun t ↦
      ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
          Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, f t) ≤
      ((1 / (2 * Real.pi)) + (1 / 21 : ℝ)) *
        (absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  dsimp
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let f : ℝ → ℝ := fun t ↦
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
  let law : ℝ → ℝ := fun t ↦
    absoluteMoment (X 1) 3 P * |t| ^ (2 : ℕ) * Real.exp (-(t ^ (2 : ℕ) / 2)) *
        Real.exp (-((((Real.sqrt (n : ℝ))⁻¹ * t) ^ (2 : ℕ)) / 3)) ^ ((n : ℕ) - 1) /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * (6 * Real.sqrt (n : ℝ)))
  let proxy : ℝ → ℝ := fun t ↦
    |t| ^ (3 : ℕ) * Real.exp (-(t ^ (2 : ℕ))) / (4 * (n : ℝ))
  let scale : ℝ :=
    absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale again gives the sign and scale data for
    -- the natural window.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hT0_nonneg : 0 ≤ T0 := by
    dsimp [T0]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (le_of_lt hβ_pos))
  have hFInt :
      IntervalIntegrable f volume (-T0) T0 := by
    -- Proof comment: the damped quotient kernel is already known to be integrable on the full
    -- natural Berry--Esseen window.
    simpa [f, μn, β, T0] using
      (standardizedLawGaussianDampedQuotientIntervalIntegrable
        P X hX_iid hX_mean hX_var hX_third n).norm
  have hLawInt :
      IntervalIntegrable law volume (-T0) T0 := by
    -- Proof comment: the law-term majorant is continuous on the compact natural window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  have hProxyInt :
      IntervalIntegrable proxy volume (-T0) T0 := by
    -- Proof comment: the proxy majorant is also continuous on the compact natural window.
    refine Continuous.intervalIntegrable ?_ (-T0) T0
    continuity
  have hSplitPointwise :
      ∀ t ∈ Set.Icc (-T0) T0, f t ≤ law t + proxy t := by
    intro t ht
    have ht_abs : |t| ≤ T0 := by
      rcases ht with ⟨ht_left, ht_right⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    -- Proof comment: specialize the already proved damped split bound to points on the full
    -- natural window.
    simpa [f, law, proxy, μn] using
      standardizedLawGaussianDampedSplitBoundOnCentralWindow
        P X hX_iid hX_mean hX_var hX_third n ht_abs
  have hMono :
      ∫ t in -T0..T0, f t ≤ ∫ t in -T0..T0, (law t + proxy t) := by
    refine
      intervalIntegral.integral_mono_on
        (μ := volume) (a := -T0) (b := T0) (f := f) (g := fun t ↦ law t + proxy t)
        (by linarith) hFInt (hLawInt.add hProxyInt) ?_
    intro t ht
    have ht_mem : t ∈ Set.Icc (-T0) T0 := by
      simpa [Set.uIcc_of_le hT0_nonneg] using ht
    exact hSplitPointwise t ht_mem
  have hLaw :
      (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) ≤ (1 / 21 : ℝ) * scale := by
    simpa [β, T0, law] using
      standardizedLawGaussianLawTermNaturalWindowIntegral_le_oneDivTwentyOneScaled
        P X hX_iid hX_mean hX_var hX_third n
  have hProxyFull :
      ∫ t in -T0..T0, proxy t ≤ 1 / (n : ℝ) := by
    -- Proof comment: the proxy majorant has an exact symmetric antiderivative on the full
    -- natural window.
    rw [proxyGaussianDampedMajorantIntegral_eq (n := n) hT0_nonneg]
    have hTail_nonneg : 0 ≤ (T0 ^ (2 : ℕ) + 1) * Real.exp (-(T0 ^ (2 : ℕ))) := by
      positivity
    have hNumerator_le_one :
        1 - (T0 ^ (2 : ℕ) + 1) * Real.exp (-(T0 ^ (2 : ℕ))) ≤ (1 : ℝ) := by
      nlinarith
    calc
      (1 - (T0 ^ (2 : ℕ) + 1) * Real.exp (-(T0 ^ (2 : ℕ)))) / (4 * (n : ℝ)) ≤
          1 / (4 * (n : ℝ)) := by
            exact div_le_div_of_nonneg_right hNumerator_le_one (by positivity)
      _ ≤ 1 / (n : ℝ) := by
            have hn_inv_nonneg : 0 ≤ (1 / (n : ℝ)) := by positivity
            have hQuarter : (1 / (4 * (n : ℝ)) : ℝ) = (1 / 4 : ℝ) * (1 / (n : ℝ)) := by
              field_simp [show (n : ℝ) ≠ 0 by positivity]
            rw [hQuarter]
            nlinarith
  have hScaled :
      1 / (n : ℝ) ≤ scale := by
    -- Proof comment: convert the residual `1 / n` proxy coefficient to the global Berry--Esseen
    -- scale.
    simpa [scale] using
      berryEsseenOneDivNat_le_scaledThirdMoment
        P X hX_iid hX_mean hX_var hX_third n
  calc
    (1 / (2 * Real.pi)) * (∫ t in -T0..T0, f t) ≤
        (1 / (2 * Real.pi)) * (∫ t in -T0..T0, (law t + proxy t)) := by
          exact mul_le_mul_of_nonneg_left hMono (by positivity)
    _ =
        (1 / (2 * Real.pi)) * (∫ t in -T0..T0, law t) +
          (1 / (2 * Real.pi)) * (∫ t in -T0..T0, proxy t) := by
          rw [intervalIntegral.integral_add hLawInt hProxyInt]
          ring
    _ ≤ (1 / 21 : ℝ) * scale + (1 / (2 * Real.pi)) * (1 / (n : ℝ)) := by
          gcongr
    _ ≤ (1 / 21 : ℝ) * scale + (1 / (2 * Real.pi)) * scale := by
          gcongr
    _ = ((1 / (2 * Real.pi)) + (1 / 21 : ℝ)) * scale := by
          ring

/-- Helper for Theorem 15.51: on the scale-two Berry--Esseen window, the damped quotient integral
should fit inside the leftover coefficient `0.8 - 1 / √(2π)`. -/
private lemma standardizedLawGaussianDampedWindowIntegral_le_targetGap
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn,
          ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) ≤
      (((0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi)) *
        absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) := by
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let T0 : ℝ := Real.sqrt (n : ℝ) * β⁻¹
  let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
  let f : ℝ → ℝ := fun t ↦
    ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
        Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖
  let scale : ℝ :=
    absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))
  have hβ_ge_one : 1 ≤ β := by
    -- Proof comment: the normalized third-moment scale still dominates `1`, so both cutoffs are
    -- positive and the scale factor is nonnegative.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ_ge_one
  have hT0_pos : 0 < T0 := by
    -- Proof comment: the natural cutoff `T0 = √n / β` is positive on positive `n`.
    dsimp [T0]
    exact mul_pos (by positivity) (inv_pos.mpr hβ_pos)
  have hLeftTailInt :
      IntervalIntegrable f volume (-Tn) (-T0) := by
    -- Proof comment: the negative scale-two tail stays away from `0`, so the damped kernel is
    -- continuous and hence interval-integrable there.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := -Tn) (b := -T0) ?_ ?_
    · dsimp [Tn, T0]
      nlinarith [hT0_pos]
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_le : t ≤ -T0 := ht.2
        exact_mod_cast (show t ≠ 0 by linarith [ht_le, hT0_pos])
  have hCentralInt :
      IntervalIntegrable f volume (-T0) T0 := by
    -- Proof comment: the damped quotient kernel is already integrable on the full natural
    -- Berry--Esseen window.
    simpa [f, μn, β, T0] using
      (standardizedLawGaussianDampedQuotientIntervalIntegrable
        P X hX_iid hX_mean hX_var hX_third n).norm
  have hRightTailInt :
      IntervalIntegrable f volume T0 Tn := by
    -- Proof comment: the positive scale-two tail satisfies the same continuity argument.
    refine ContinuousOn.intervalIntegrable_of_Icc (a := T0) (b := Tn) ?_ ?_
    · dsimp [Tn, T0]
      nlinarith [hT0_pos]
    · refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      refine ContinuousAt.norm ?_
      refine ContinuousAt.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · have ht_ge : T0 ≤ t := ht.1
        exact_mod_cast (show t ≠ 0 by linarith [ht_ge, hT0_pos])
  have hSplit :
      ∫ t in -Tn..Tn, f t =
        (∫ t in -Tn..-T0, f t) + (∫ t in -T0..T0, f t) + ∫ t in T0..Tn, f t := by
    -- Proof comment: split the scale-two window into the two tails and the full natural window.
    calc
      ∫ t in -Tn..Tn, f t = (∫ t in -Tn..T0, f t) + ∫ t in T0..Tn, f t := by
        simpa using
          (intervalIntegral.integral_add_adjacent_intervals
            (f := f) (hLeftTailInt.trans hCentralInt) hRightTailInt).symm
      _ = ((∫ t in -Tn..-T0, f t) + ∫ t in -T0..T0, f t) + ∫ t in T0..Tn, f t := by
        rw [show ∫ t in -Tn..T0, f t =
            (∫ t in -Tn..-T0, f t) + ∫ t in -T0..T0, f t by
              simpa using
                (intervalIntegral.integral_add_adjacent_intervals
                  (f := f) hLeftTailInt hCentralInt).symm]
      _ = (∫ t in -Tn..-T0, f t) + (∫ t in -T0..T0, f t) + ∫ t in T0..Tn, f t := by
        ring
  have hTail :
      (1 / (2 * Real.pi)) * ((∫ t in -Tn..-T0, f t) + ∫ t in T0..Tn, f t) ≤
        (Real.exp (-(1 / 2 : ℝ)) / Real.pi) * scale := by
    have hTailBase :=
      dampedQuotientScaleTwoTailIntegral_le_sharpScaledCutoff (μ := μn) (T0 := T0) hT0_pos
    -- Proof comment: rewrite the tail cutoff `1 / T0` into the global Berry--Esseen scale.
    simpa [f, μn, β, T0, Tn, scale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using hTailBase
  have hCentral :
      (1 / (2 * Real.pi)) * (∫ t in -T0..T0, f t) ≤
        ((1 / (2 * Real.pi)) + (1 / 21 : ℝ)) * scale := by
    -- Proof comment: the full natural window is already packaged into the remaining central
    -- coefficient.
    simpa [f, μn, β, T0, scale] using
      standardizedLawGaussianCentralWindowIntegral_le_remainingGap
        P X hX_iid hX_mean hX_var hX_third n
  have hScale_nonneg : 0 ≤ scale := by
    -- Proof comment: the global Berry--Esseen scale is nonnegative.
    dsimp [scale]
    rw [absoluteMoment_eq_expectation_abs_pow]
    positivity
  have hMain :
      (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, f t) ≤
        (((0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi)) * scale) := by
    calc
      (1 / (2 * Real.pi)) * (∫ t in -Tn..Tn, f t) =
          (1 / (2 * Real.pi)) *
            ((∫ t in -Tn..-T0, f t) + (∫ t in -T0..T0, f t) + ∫ t in T0..Tn, f t) := by
              rw [hSplit]
      _ =
          (1 / (2 * Real.pi)) * ((∫ t in -Tn..-T0, f t) + ∫ t in T0..Tn, f t) +
            (1 / (2 * Real.pi)) * (∫ t in -T0..T0, f t) := by
              ring
      _ ≤
          (Real.exp (-(1 / 2 : ℝ)) / Real.pi) * scale +
            (((1 / (2 * Real.pi)) + (1 / 21 : ℝ)) * scale) := by
              exact add_le_add hTail hCentral
      _ =
          ((Real.exp (-(1 / 2 : ℝ)) / Real.pi) + (1 / (2 * Real.pi) + (1 / 21 : ℝ))) * scale := by
            ring
      _ ≤ (((0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi)) * scale) := by
            exact mul_le_mul_of_nonneg_right scaleTwoTailAndCentralCoefficient_le_target hScale_nonneg
  simpa [μn, β, Tn, f, scale, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMain

/-- Helper for Theorem 15.51: the repaired owner-level smoothing theorem should bound the cdf gap
by the Gaussian-damped quotient integral plus the explicit cutoff term, with no one-sided Gaussian
tails left in the statement. -/
private lemma gaussianEsseenCorrectedDirectSmoothingSupBound
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 < T)
    (hDampedInt :
      IntervalIntegrable
        (fun t ↦
          (((charFun μ t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
        volume (-T) T) :
    sSup (Set.range fun x : ℝ ↦ |cdf μ x - cdf (gaussianReal 0 1) x|) ≤
      (1 / (2 * Real.pi)) *
          (∫ t in -T..T,
            ‖(((charFun μ t - charFun (gaussianReal 0 1) t) *
                Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
        (2 / Real.sqrt (2 * Real.pi)) / T := by
  let S : Set ℝ := Set.range fun x : ℝ ↦ |cdf μ x - cdf (gaussianReal 0 1) x|
  have hSBdd : BddAbove S := by
    refine ⟨2, ?_⟩
    rintro y ⟨x, rfl⟩
    have hμ_nonneg : 0 ≤ cdf μ x := ProbabilityTheory.cdf_nonneg _ _
    have hGauss_nonneg : 0 ≤ cdf (gaussianReal 0 1) x := ProbabilityTheory.cdf_nonneg _ _
    have hμ_one : cdf μ x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
    have hGauss_one : cdf (gaussianReal 0 1) x ≤ 1 := ProbabilityTheory.cdf_le_one _ _
    calc
      |cdf μ x - cdf (gaussianReal 0 1) x| ≤
          |cdf μ x| + |cdf (gaussianReal 0 1) x| := by
            simpa using
              (abs_sub_le (cdf μ x) 0 (cdf (gaussianReal 0 1) x))
      _ = cdf μ x + cdf (gaussianReal 0 1) x := by
            rw [abs_of_nonneg hμ_nonneg, abs_of_nonneg hGauss_nonneg]
      _ ≤ 2 := by
            linarith
  -- Proof comment: lift the direct pointwise damped-quotient surface to `sSup`; the sinc
  -- normalization now stays hidden behind the owner theorem.
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨x, rfl⟩
  have hPoint :=
    cdfGap_le_dampedQuotientSurface_add_gaussianCutoff
      (μ := μ) hT x hDampedInt
  exact hPoint

/-- Helper for Theorem 15.51: the remaining quantitative theorem now lands on the corrected
Gaussian-damped quotient window at the scale-two Berry--Esseen cutoff. -/
private lemma standardizedLawGaussianQuotientDirectBoundAtScale
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn,
          ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
    (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  dsimp
  have hIntegral :=
    standardizedLawGaussianDampedWindowIntegral_le_targetGap
      P X hX_iid hX_mean hX_var hX_third n
  have hCutoff :=
    berryEsseenCutoffAtScale P X hX_iid hX_mean hX_var hX_third (c := 2) (by norm_num) n
  -- Proof comment: combine the scale-two damped-window estimate with the exact scale-two cutoff
  -- rewrite; the two coefficients add up to the target constant `0.8`.
  calc
    (1 / (2 * Real.pi)) *
        (∫ t in -(2 * Real.sqrt (n : ℝ) *
              (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹)..
            (2 * Real.sqrt (n : ℝ) *
              (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹),
          ‖(((charFun
                (ProbabilityMeasure.map ⟨P, inferInstance⟩
                  (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
                    (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)) t -
              charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
      (2 / Real.sqrt (2 * Real.pi)) /
          (2 * Real.sqrt (n : ℝ) *
            (absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ))⁻¹) ≤
        (((0.8 : ℝ) - 1 / Real.sqrt (2 * Real.pi)) *
            absoluteMoment (X 1) 3 P /
              (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ))) +
          ((2 / Real.sqrt (2 * Real.pi)) / 2) *
            absoluteMoment (X 1) 3 P /
              (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
          linarith [hIntegral, hCutoff]
    _ = (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
          (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
          ring

/-- Helper for Theorem 15.51: the scale-two wrapper is just the corrected damped-window estimate
at the canonical cutoff `Tn = 2 * √n * β⁻¹`. -/
private lemma standardizedLawGaussianQuotientNaturalWindowDirectBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    let μn : Measure ℝ :=
      ProbabilityMeasure.map ⟨P, inferInstance⟩
        (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
          (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
    let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
    let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
    (1 / (2 * Real.pi)) *
        (∫ t in -Tn..Tn,
          ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
      (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
    (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
      (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  -- Proof comment: the natural-window closing theorem is just the corrected damped-window bound
  -- with the standard cutoff notation expanded.
  simpa using
    standardizedLawGaussianQuotientDirectBoundAtScale
      P X hX_iid hX_mean hX_var hX_third n

/-- Helper for Theorem 15.51: once the direct smoothing inequality and the sharp natural-window
majorant are available, the Berry--Esseen bound follows by transitivity. -/
private lemma berryEsseenDirectSmoothingBound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    sSup
        (Set.range fun x : ℝ ↦
          |cdf
              (ProbabilityMeasure.map ⟨P, inferInstance⟩
                (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
                  (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)) x -
            cdf (gaussianReal 0 1) x|) ≤
      (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  let μn : Measure ℝ :=
    ProbabilityMeasure.map ⟨P, inferInstance⟩
      (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
        (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)
  let β : ℝ := absoluteMoment (X 1) 3 P / Real.sqrt (Var[X 1; P]) ^ (3 : ℕ)
  let Tn : ℝ := 2 * Real.sqrt (n : ℝ) * β⁻¹
  have hβ : 1 ≤ β := by
    -- Proof comment: the natural Berry--Esseen scale is already known to be at least `1`.
    simpa [β] using
      berryEsseenThirdMomentScale_ge_one P X hX_iid hX_mean hX_var hX_third
  have hβ_pos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hTn_pos : 0 < Tn := by
    -- Proof comment: the scale-two cutoff is positive because both `√n` and `β⁻¹` are positive.
    dsimp [Tn]
    positivity
  have hDampedInt :
      IntervalIntegrable
        (fun t ↦
          (((charFun μn t - charFun (gaussianReal 0 1) t) *
              Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ)))
        volume (-Tn) Tn := by
    -- Proof comment: the specialized damped quotient kernel is integrable on the scale-two
    -- window, so the owner smoothing theorem can consume it as an explicit side condition.
    simpa [μn, β, Tn] using
      standardizedLawGaussianDampedQuotientIntervalIntegrableScaleTwo
        P X hX_iid hX_mean hX_var hX_third n
  have hSmooth :
      sSup (Set.range fun x : ℝ ↦ |cdf μn x - cdf (gaussianReal 0 1) x|) ≤
        (1 / (2 * Real.pi)) *
            (∫ t in -Tn..Tn,
              ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
                  Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
          (2 / Real.sqrt (2 * Real.pi)) / Tn := by
    simpa [μn, β, Tn] using
      gaussianEsseenCorrectedDirectSmoothingSupBound (μ := μn) hTn_pos hDampedInt
  have hSharpWindow :
      (1 / (2 * Real.pi)) *
          (∫ t in -Tn..Tn,
            ‖(((charFun μn t - charFun (gaussianReal 0 1) t) *
                Complex.exp (-(t ^ (2 : ℕ) / 2)) / t : ℂ))‖) +
        (2 / Real.sqrt (2 * Real.pi)) / Tn ≤
      (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
    -- Proof comment: the repaired scale-two quantitative theorem now lands exactly on the same
    -- damped quotient surface as the corrected smoothing inequality.
    simpa [μn, β, Tn] using
      standardizedLawGaussianQuotientNaturalWindowDirectBound
        P X hX_iid hX_mean hX_var hX_third n
  -- Proof comment: chain the direct smoothing inequality with the sharp natural-window majorant.
  exact le_trans hSmooth hSharpWindow
-- Proof sketch: use the canonical owner hypothesis `IsIID (fun n ↦ X (n + 1)) P` to obtain the
-- measurability and common-law data needed for the pushforward law of
-- `standardizedPartialSum P (fun k ↦ X (k + 1)) n`, then apply the classical Berry--Esseen
-- inequality with the intrinsic variance and third absolute moment of `X 1`.
/-- Theorem 15.51: Berry--Esseen. If `X₁, X₂, …` are iid real random variables with mean `0`,
positive variance, and finite third absolute moment, then for every positive integer `n` the
Kolmogorov distance between the law of `S_n^*` and the standard normal cdf `cdf (gaussianReal 0
1)` is bounded by
`0.8 * absoluteMoment (X 1) 3 P / ((Real.sqrt (Var[X 1; P]))^3 * √n)`. -/
theorem berry_esseen_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX_mean : P[X 1] = 0)
    (hX_var : 0 < Var[X 1; P])
    (hX_third : Integrable (fun ω ↦ |X 1 ω| ^ (3 : ℕ)) P)
    (n : ℕ+) :
    sSup
        (Set.range fun x : ℝ ↦
          |cdf
              (ProbabilityMeasure.map ⟨P, inferInstance⟩
                (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
                  (fun k ↦ (hX_iid.identDistrib k 0).aemeasurable_fst) n)) x -
            cdf (gaussianReal 0 1) x|) ≤
      (0.8 : ℝ) * absoluteMoment (X 1) 3 P /
        (Real.sqrt (Var[X 1; P]) ^ (3 : ℕ) * Real.sqrt (n : ℝ)) := by
  -- Proof comment: the theorem is exactly the direct smoothing bound specialized to the
  -- standardized partial-sum law.
  exact berryEsseenDirectSmoothingBound P X hX_iid hX_mean hX_var hX_third n

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_45
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [A.IsIndependent μ] [A.IsCentered μ] [A.IsNormed μ]

/-- Helper for Lemma 15.46: under the independent centered normed hypotheses, each row sum has
variance `1`. -/
private lemma rowSumVarianceEqOne
    (n : ℕ) :
    Var[A.rowSum n; μ] = 1 := by
  have hPairwise : Pairwise fun i j : Fin (A.rowLength n) ↦ A n i ⟂ᵢ[μ] A n j := by
    intro i j hij
    exact (RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := μ) n).indepFun hij
  -- Proof comment: rowwise independence turns the variance of the row sum into the sum of the
  -- row variances, and the normed-array hypothesis normalizes that sum to `1`.
  calc
    Var[A.rowSum n; μ] = ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
      simpa [RealRandomVariableArray.rowSum] using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := μ) (X := fun i : Fin (A.rowLength n) ↦ A n i) (s := Finset.univ)
          (hs := fun i _ ↦ RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i)
          (by
            intro i _ j _ hij
            exact hPairwise hij)
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n

/-- Helper for Lemma 15.46: after normalizing `Var[A.rowSum n; μ] = 1`, the Lindeberg quantity is
exactly the rowwise truncated second-moment sum. -/
private lemma lindebergFunction_eq_rowTruncatedSecondMoment
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    A.lindebergFunction μ ε n =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  rw [RealRandomVariableArray.lindebergFunction_def]
  rw [rowSumVarianceEqOne (A := A) (μ := μ) n, inv_one, one_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs :
      {ω | ε ^ 2 * (1 : ℝ) < (A n i ω) ^ 2} = {ω | ε < |A n i ω|} := by
    ext ω
    simp [sq_lt_sq, abs_of_pos hε]
  rw [hs]

/-- Helper for Lemma 15.46: the rowwise truncated second moments forced by the Lindeberg condition
tend to `0` for every fixed threshold `ε > 0`. -/
private theorem rowTruncatedSecondMoment_tendstoZero
    (hLindeberg : A.SatisfiesLindebergCondition μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦
        ∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ)
      atTop
      (𝓝 0) := by
  -- Proof comment: rewrite the normalized Lindeberg quantity rowwise into the textbook truncated
  -- second-moment sum and then use the defining convergence field.
  simpa [lindebergFunction_eq_rowTruncatedSecondMoment (A := A) (μ := μ) hε] using
    hLindeberg.lindeberg_tendsto hε

/-- Helper for Lemma 15.46: each tail probability in a fixed row is controlled by the matching
truncated second moment via the elementary bound `1 ≤ x^2 / ε^2` on `{ω | ε < |A n i ω|}`. -/
private lemma tailProbRealLeScaledTruncatedSecondMoment
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (i : Fin (A.rowLength n)) :
    μ.real {ω | ε < |A n i ω|} ≤
      (ε ^ (2 : ℕ))⁻¹ *
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  let s : Set Ω := {ω | ε < |A n i ω|}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const (A.measurable_entry n i).norm
  have hpointwise :
      s.indicator (fun _ : Ω ↦ (1 : ℝ)) ≤
        s.indicator (fun ω ↦ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ 2) := by
    intro ω
    by_cases hω : ω ∈ s
    · have htail : ε < |A n i ω| := hω
      have hsq_abs : ε ^ 2 < |A n i ω| ^ 2 := by
        nlinarith [hε, abs_nonneg (A n i ω), htail]
      have hsq : ε ^ 2 < (A n i ω) ^ 2 := by
        simpa [sq_abs] using hsq_abs
      have hone : (1 : ℝ) ≤ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ 2 := by
        have hεsq : 0 < ε ^ 2 := by positivity
        have hdiv : (1 : ℝ) < (A n i ω) ^ 2 / (ε ^ 2) := by
          exact (one_lt_div hεsq).2 hsq
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv.le
      simp [s, hω, hone]
    · simp [s, hω]
  have hIntLeft : Integrable (Set.indicator s (fun _ : Ω ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hs
  have hIntRight :
      Integrable (Set.indicator s (fun ω ↦ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ 2)) μ := by
    exact
      (((RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq).const_mul
        ((ε ^ (2 : ℕ))⁻¹)).indicator hs
  have hindicator_mul :
      Set.indicator s (fun ω ↦ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ 2) =
        fun ω ↦ (ε ^ (2 : ℕ))⁻¹ * Set.indicator s (fun ω ↦ (A n i ω) ^ 2) ω := by
    funext ω
    by_cases hω : ω ∈ s
    · simp [Set.indicator, hω]
    · simp [Set.indicator, hω]
  calc
    μ.real s = ∫ ω, Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ∂μ := by
      simpa [s] using (integral_indicator_one (μ := μ) hs).symm
    _ ≤ ∫ ω, Set.indicator s (fun ω ↦ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ 2) ω ∂μ := by
      exact integral_mono_ae hIntLeft hIntRight (Filter.Eventually.of_forall hpointwise)
    _ = (ε ^ (2 : ℕ))⁻¹ * ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
      rw [hindicator_mul, integral_const_mul]

/-- Helper for Lemma 15.46: for a fixed frequency `t`, the entry characteristic functions become
uniformly close to `1` along each row under the Lindeberg condition. -/
private lemma eventually_entryCharFunSubOne_le
    (hLindeberg : A.SatisfiesLindebergCondition μ)
    (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      ∀ l : Fin (A.rowLength n), ‖charFun (μ.map (A n l)) t - 1‖ ≤ δ := by
  let η : ℝ := δ / (4 * (|t| + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  let F : ℕ → ℝ := fun n ↦
    ∑ i : Fin (A.rowLength n),
      ∫ ω, Set.indicator {ω | η < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ
  have hF : Tendsto F atTop (𝓝 0) :=
    rowTruncatedSecondMoment_tendstoZero (A := A) (μ := μ) hLindeberg hη
  have hFsmall :
      ∀ᶠ n in atTop, (η ^ (2 : ℕ))⁻¹ * F n ≤ δ / 4 := by
    have hScaled :
        Tendsto (fun n ↦ (η ^ (2 : ℕ))⁻¹ * F n) atTop (𝓝 ((η ^ (2 : ℕ))⁻¹ * 0)) :=
      tendsto_const_nhds.mul hF
    exact hScaled.eventually (Iic_mem_nhds <| by simpa using (show (0 : ℝ) < δ / 4 by positivity))
  filter_upwards [hFsmall] with n hnF l
  let s : Set Ω := {ω | η < |A n l ω|}
  let f : Ω → ℂ := fun ω ↦ Complex.exp (t * A n l ω * Complex.I) - 1
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const (A.measurable_entry n l).norm
  have htail_real :
      μ.real s ≤ δ / 4 := by
    have htail_base :=
      tailProbRealLeScaledTruncatedSecondMoment (A := A) (μ := μ) hη n l
    have hterm_nonneg :
        ∀ j : Fin (A.rowLength n),
          0 ≤ ∫ ω, Set.indicator {ω | η < |A n j ω|} (fun ω ↦ (A n j ω) ^ 2) ω ∂μ := by
      intro j
      refine integral_nonneg fun ω ↦ ?_
      by_cases hω : η < |A n j ω|
      · simp [Set.indicator, hω, sq_nonneg]
      · simp [Set.indicator, hω]
    have hterm_le :
        ∫ ω, Set.indicator {ω | η < |A n l ω|} (fun ω ↦ (A n l ω) ^ 2) ω ∂μ ≤ F n := by
      simpa [F] using
        (Finset.single_le_sum
          (fun j _ ↦ hterm_nonneg j)
          (Finset.mem_univ l))
    have hscaled_le :
        (η ^ (2 : ℕ))⁻¹ *
            ∫ ω, Set.indicator {ω | η < |A n l ω|} (fun ω ↦ (A n l ω) ^ 2) ω ∂μ ≤
          (η ^ (2 : ℕ))⁻¹ * F n := by
      exact mul_le_mul_of_nonneg_left hterm_le (by positivity)
    exact htail_base.trans (hscaled_le.trans hnF)
  have hgood_const : |t| * η ≤ δ / 4 := by
    have ht_le : |t| ≤ |t| + 1 := by linarith
    calc
      |t| * η ≤ (|t| + 1) * η := by gcongr
      _ = δ / 4 := by
            dsimp [η]
            field_simp
  have hpoint_two : ∀ ω, ‖f ω‖ ≤ 2 := by
    intro ω
    have hnorm_exp : ‖Complex.exp (t * A n l ω * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n l ω))
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n l ω * Complex.I) - 1‖ := by rfl
      _ ≤ ‖Complex.exp (t * A n l ω * Complex.I)‖ + ‖(1 : ℂ)‖ := by
            simpa using norm_sub_le (Complex.exp (t * A n l ω * Complex.I)) (1 : ℂ)
      _ = 2 := by
            rw [hnorm_exp]
            norm_num
  have hgood_point : ∀ ω ∈ sᶜ, ‖f ω‖ ≤ |t| * η := by
    intro ω hω
    have hω_le : |A n l ω| ≤ η := by
      exact le_of_not_gt <| by simpa [s] using hω
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n l ω * Complex.I) - 1‖ := by rfl
      _ ≤ |t * A n l ω| := by
            simpa [mul_assoc, mul_left_comm, mul_comm, Real.norm_eq_abs] using
              (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * A n l ω))
      _ = |t| * |A n l ω| := by rw [abs_mul]
      _ ≤ |t| * η := by gcongr
  have htail_int : ‖∫ ω in s, f ω ∂μ‖ ≤ δ / 2 := by
    calc
      ‖∫ ω in s, f ω ∂μ‖ ≤ 2 * μ.real s := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := μ) (s := s) (f := f) (by simp) fun ω _ ↦ hpoint_two ω
      _ ≤ 2 * (δ / 4) := by gcongr
      _ = δ / 2 := by ring
  have hgood_int : ‖∫ ω in sᶜ, f ω ∂μ‖ ≤ δ / 4 := by
    calc
      ‖∫ ω in sᶜ, f ω ∂μ‖ ≤ (|t| * η) * μ.real sᶜ := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := μ) (s := sᶜ) (f := f) (by simp) hgood_point
      _ ≤ (|t| * η) * 1 := by
        gcongr
        exact measureReal_le_one
      _ = |t| * η := by ring
      _ ≤ δ / 4 := hgood_const
  have hexp_int : Integrable (fun ω ↦ Complex.exp (t * A n l ω * Complex.I)) μ := by
    have hmeas :
        Measurable (fun ω ↦ Complex.exp (t * A n l ω * Complex.I)) := by
      refine Complex.measurable_exp.comp ?_
      simpa using
        (Complex.measurable_ofReal.comp ((A.measurable_entry n l).const_mul t)).mul_const Complex.I
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hnorm_exp : ‖Complex.exp (t * A n l ω * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n l ω))
    simpa [hnorm_exp]
  have hf_int : Integrable f μ := by
    exact hexp_int.sub (integrable_const 1)
  have hchar_split :
      charFun (μ.map (A n l)) t - 1 = ∫ ω in s, f ω ∂μ + ∫ ω in sᶜ, f ω ∂μ := by
    have hconst : (∫ ω, (1 : ℂ) ∂μ) = 1 := by simp
    have hkernel_meas :
        AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
          (Measure.map (A n l) μ) := by
      refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
      simpa using
        (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
    -- Proof comment: rewrite the pushforward characteristic function as an integral over `μ`
    -- and split it into the tail and small-entry pieces.
    rw [MeasureTheory.charFun_apply_real]
    rw [integral_map (A.measurable_entry n l).aemeasurable hkernel_meas]
    rw [← hconst, ← integral_sub hexp_int (integrable_const 1)]
    simpa [f] using (integral_add_compl hs hf_int).symm
  calc
    ‖charFun (μ.map (A n l)) t - 1‖
        = ‖∫ ω in s, f ω ∂μ + ∫ ω in sᶜ, f ω ∂μ‖ := by
            rw [hchar_split]
    _ ≤ ‖∫ ω in s, f ω ∂μ‖ + ‖∫ ω in sᶜ, f ω ∂μ‖ := by exact norm_add_le _ _
    _ ≤ δ / 2 + δ / 4 := by
          gcongr
    _ ≤ δ := by linarith

/-- Helper for Lemma 15.46: the centered quadratic kernel whose variance-weighted row-law
integrals are exactly the middle terms `φₙ,ᵢ(t) - 1`. -/
private def centeredQuadraticCharFunKernel (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if x = 0 then
      (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
    else
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
        (((x : ℂ) ^ (2 : ℕ)))

/-- Helper for Lemma 15.46: the centered quadratic kernel takes the Gaussian exponent value
`-t^2 / 2` at `0`. -/
private lemma centeredQuadraticCharFunKernel_apply_zero (t : ℝ) :
    centeredQuadraticCharFunKernel t 0 = (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  -- Proof comment: this is the zero branch of the defining `if`.
  simp [centeredQuadraticCharFunKernel]

/-- Helper for Lemma 15.46: away from `0`, the centered quadratic kernel is the explicit
quadratic remainder `(exp(itx) - 1 - itx) / x^2`. -/
private lemma centeredQuadraticCharFunKernel_apply_ne_zero
    (t x : ℝ) (hx : x ≠ 0) :
    centeredQuadraticCharFunKernel t x =
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
        (((x : ℂ) ^ (2 : ℕ))) := by
  -- Proof comment: away from the origin, the defining `if` collapses to the explicit formula.
  simp [centeredQuadraticCharFunKernel, hx]

/-- Helper for Lemma 15.46: multiplying the centered quadratic kernel by `x^2` recovers the
centered exponential increment exactly. -/
private lemma centeredQuadraticCharFunKernel_mul_sq
    (t x : ℝ) :
    centeredQuadraticCharFunKernel t x * (((x : ℂ) ^ (2 : ℕ))) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) := by
  by_cases hx : x = 0
  · -- Proof comment: at the origin both sides vanish because the quadratic factor kills the
    -- continuous extension value and the centered increment is zero.
    simp [centeredQuadraticCharFunKernel, hx]
  · -- Proof comment: away from `0`, cancel the explicit denominator.
    have hxC : ((x : ℂ)) ≠ 0 := by
      exact_mod_cast hx
    rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx]
    field_simp [pow_ne_zero 2 hxC]

/-- Helper for Lemma 15.46: the third-order Taylor remainder of
`Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))`. -/
private def centeredQuadraticCharFunKernelTaylorRemainder (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
    Finset.sum (Finset.range 3)
      (fun m ↦ ((((t * x : ℝ) : ℂ) * Complex.I) ^ m) / m.factorial)

/-- Helper for Lemma 15.46: the cubic Taylor polynomial of `exp ((((t * x : ℝ) : ℂ) * I))`
has the canonical textbook normal form `1 + i t x - t² x² / 2`. -/
private lemma centeredQuadraticCharFunKernelTaylorPolynomial_eval
    (t x : ℝ) :
    Finset.sum (Finset.range 3)
      (fun m ↦ ((((t * x : ℝ) : ℂ) * Complex.I) ^ m) / m.factorial) =
        1 + (((t * x : ℝ) : ℂ) * Complex.I) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  -- Proof comment: expand the three Taylor terms once and freeze the resulting normal form so
  -- the later kernel quotient rewrite only needs a single directed rewrite.
  have hI : Complex.I * Complex.I = -(1 : ℂ) := by
    calc
      Complex.I * Complex.I = Complex.I ^ (2 : ℕ) := by simp [pow_two]
      _ = -(1 : ℂ) := Complex.I_sq
  have hI2 (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
    calc
      Complex.I * (Complex.I * z) = (Complex.I * Complex.I) * z := by ring
      _ = -(1 : ℂ) * z := by rw [hI]
      _ = -z := by ring
  simp [Finset.sum_range_succ, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm, sub_eq_add_neg]
  rw [hI2]

/-- Helper for Lemma 15.46: away from `0`, subtracting the origin value rewrites the centered
quadratic kernel as the third-order Taylor remainder divided by `x^2`. -/
private lemma centeredQuadraticCharFunKernel_sub_apply_zero_eq_taylorRemainderDiv
    (t x : ℝ) (hx : x ≠ 0) :
    centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0 =
      centeredQuadraticCharFunKernelTaylorRemainder t x /
        (((x : ℂ) ^ (2 : ℕ))) := by
  have hxC : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hx)
  have hTaylor :
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
          (((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) =
        centeredQuadraticCharFunKernelTaylorRemainder t x := by
    -- Proof comment: rewrite the truncated Taylor sum into the fixed polynomial normal form and
    -- collect the numerator terms into the stored remainder expression.
    rw [centeredQuadraticCharFunKernelTaylorRemainder,
      centeredQuadraticCharFunKernelTaylorPolynomial_eval (t := t) (x := x)]
    ring
  calc
    centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0 =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
            (((x : ℂ) ^ (2 : ℕ))) +
          ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
            rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx,
              centeredQuadraticCharFunKernel_apply_zero]
            ring
    _ =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
            ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) * (((x : ℂ) ^ (2 : ℕ)))) /
          (((x : ℂ) ^ (2 : ℕ))) := by
            let a : ℂ :=
              Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)
            let b : ℂ := ((x : ℂ) ^ (2 : ℕ))
            let c : ℂ := ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
            change a / b + c = (a + c * b) / b
            rw [div_eq_mul_inv, div_eq_mul_inv, add_mul]
            congr 1
            calc
              c = c * (b * b⁻¹) := by simp [b, hxC]
              _ = c * b * b⁻¹ := by ring
    _ =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
            (((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ))) /
          (((x : ℂ) ^ (2 : ℕ))) := by
            simp [div_eq_mul_inv, pow_two, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    _ = centeredQuadraticCharFunKernelTaylorRemainder t x /
          (((x : ℂ) ^ (2 : ℕ))) := by
            rw [hTaylor]

/-- Helper for Lemma 15.46: near `0`, the centered quadratic kernel differs from its value at
`0` by at most a linear multiple of `|x|`. -/
private lemma norm_centeredQuadraticCharFunKernel_sub_apply_zero_le
    (t x : ℝ) (hx : x ≠ 0) :
    ‖centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0‖ ≤
      |t| ^ (3 : ℕ) * |x| / 6 := by
  have hxC : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hx)
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hRemainder :
      ‖centeredQuadraticCharFunKernelTaylorRemainder t x‖ ≤ |t * x| ^ (3 : ℕ) / 6 := by
    -- Proof comment: the Taylor remainder estimate supplies the cubic numerator bound once the
    -- kernel difference is normalized by the dedicated quotient lemma.
    simpa [centeredQuadraticCharFunKernelTaylorRemainder, mul_assoc] using
      norm_exp_mul_I_sub_taylor_sum_le (t := t * x) (n := 3)
  calc
    ‖centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0‖ =
        ‖centeredQuadraticCharFunKernelTaylorRemainder t x / (((x : ℂ) ^ (2 : ℕ)))‖ := by
          rw [centeredQuadraticCharFunKernel_sub_apply_zero_eq_taylorRemainderDiv
            (t := t) (x := x) hx]
    _ = ‖centeredQuadraticCharFunKernelTaylorRemainder t x‖ / ‖((x : ℂ) ^ (2 : ℕ))‖ := by
          rw [norm_div]
    _ ≤ (|t * x| ^ (3 : ℕ) / 6) / |x| ^ (2 : ℕ) := by
          have hNormDen : ‖((x : ℂ) ^ (2 : ℕ))‖ = |x| ^ (2 : ℕ) := by
            simp [Complex.norm_real, Real.norm_eq_abs]
          rw [hNormDen]
          gcongr
    _ = (|t| ^ (3 : ℕ) * |x| ^ (3 : ℕ) / 6) / |x| ^ (2 : ℕ) := by
          rw [abs_mul, mul_pow]
    _ = |t| ^ (3 : ℕ) * |x| / 6 := by
          field_simp [hxabs]

/-- Helper for Lemma 15.46: the centered quadratic kernel is continuous on `ℝ`. -/
private lemma continuous_centeredQuadraticCharFunKernel
    (t : ℝ) :
    Continuous (centeredQuadraticCharFunKernel t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x = 0
  · -- Proof comment: the Taylor remainder estimate makes the quadratic kernel converge to its
    -- prescribed continuous extension at the origin.
    subst hx
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    by_cases ht : t = 0
    · refine Filter.Eventually.of_forall fun y ↦ ?_
      simpa [centeredQuadraticCharFunKernel, ht, dist_eq_norm] using hε
    · have ht3pos : 0 < |t| ^ (3 : ℕ) / 6 := by
        have htnorm : 0 < |t| := abs_pos.mpr ht
        positivity
      have hδpos : 0 < ε / (|t| ^ (3 : ℕ) / 6) := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with y hy
      by_cases hy0 : y = 0
      · simpa [hy0, dist_eq_norm] using hε
      · have hbound :=
          norm_centeredQuadraticCharFunKernel_sub_apply_zero_le (t := t) (x := y) hy0
        have hyabs : |y| < ε / (|t| ^ (3 : ℕ) / 6) := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
        calc
          dist (centeredQuadraticCharFunKernel t y) (centeredQuadraticCharFunKernel t 0) =
              ‖centeredQuadraticCharFunKernel t y - centeredQuadraticCharFunKernel t 0‖ := by
                simp [dist_eq_norm]
          _ ≤ |t| ^ (3 : ℕ) * |y| / 6 := hbound
          _ < |t| ^ (3 : ℕ) * (ε / (|t| ^ (3 : ℕ) / 6)) / 6 := by
                gcongr
          _ = ε := by
                field_simp [ht3pos.ne']
  · -- Proof comment: away from the origin, the kernel is the quotient of continuous functions
    -- with a nonvanishing denominator.
    have hdenom_ne : (((x : ℂ) ^ (2 : ℕ))) ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast hx)
    have hEventually :
        centeredQuadraticCharFunKernel t =ᶠ[𝓝 x]
          fun y : ℝ ↦
            (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * y : ℝ)) /
              (((y : ℂ) ^ (2 : ℕ))) := by
      filter_upwards [Metric.ball_mem_nhds x (half_pos (abs_pos.mpr hx))] with y hy
      have hy0 : y ≠ 0 := by
        have hdist : |y - x| < |x| / 2 := by
          simpa [Metric.mem_ball, Real.dist_eq] using hy
        intro hy0
        subst hy0
        have hxlt : |x| < |x| / 2 := by simpa [abs_sub_comm] using hdist
        linarith [abs_nonneg x]
      simp [centeredQuadraticCharFunKernel, hy0]
    have hnum :
        Continuous fun y : ℝ ↦
          Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * y : ℝ) := by
      fun_prop
    have hden : Continuous fun y : ℝ ↦ ((y : ℂ) ^ (2 : ℕ)) := by
      fun_prop
    exact (hnum.continuousAt.div hden.continuousAt hdenom_ne).congr hEventually.symm

/-- Helper for Lemma 15.46: the range of the centered quadratic kernel is bounded. -/
private lemma isBounded_range_centeredQuadraticCharFunKernel
    (t : ℝ) :
    Bornology.IsBounded (Set.range (centeredQuadraticCharFunKernel t)) := by
  -- Proof comment: continuity bounds the kernel on the compact core `[-1,1]`, while outside that
  -- core the explicit denominator gives a uniform `O(1)` bound.
  obtain ⟨Ccore, hcore⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := centeredQuadraticCharFunKernel t)
      (continuous_centeredQuadraticCharFunKernel (t := t)).continuousOn
  refine (isBounded_iff_forall_norm_le).2 ?_
  refine ⟨max Ccore (2 + |t|), ?_⟩
  intro z hz
  rcases hz with ⟨x, rfl⟩
  by_cases hx : |x| ≤ 1
  · have hx_mem : x ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [abs_le] using hx
    exact (hcore x hx_mem).trans (le_max_left _ _)
  · have hx1 : 1 ≤ |x| := by linarith
    by_cases hx0 : x = 0
    · exfalso
      have hnot : ¬ (1 ≤ (0 : ℝ)) := by norm_num
      exact hnot (by simpa [hx0] using hx1)
    · rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx0]
      have hexp : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
        calc
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
              ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := by
                simpa using norm_sub_le (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) (1 : ℂ)
          _ = 2 := by
                rw [show ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ = 1 by
                  simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (t * x)]
                norm_num
      have hlin : ‖Complex.I * (t * x : ℝ)‖ ≤ |t| * |x| := by
        simpa [norm_mul, Complex.norm_I, Real.norm_eq_abs, abs_mul]
      have hxnorm : ‖((x : ℂ) ^ (2 : ℕ))‖ = |x| ^ (2 : ℕ) := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_pow]
      have hxabs0 : |x| ≠ 0 := abs_ne_zero.mpr hx0
      have hnum2 :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ ≤
            2 + |t| * |x| := by
        calc
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ ≤
              ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ + ‖Complex.I * (t * x : ℝ)‖ := by
                exact norm_sub_le _ _
          _ ≤ 2 + |t| * |x| := by nlinarith
      calc
        ‖(Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
            (((x : ℂ) ^ (2 : ℕ)))‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ /
                ‖((x : ℂ) ^ (2 : ℕ))‖ := by
                  rw [norm_div]
        _ ≤ (2 + |t| * |x|) / (|x| ^ (2 : ℕ)) := by
              rw [hxnorm]
              gcongr
        _ = 2 / (|x| ^ (2 : ℕ)) + |t| / |x| := by
              field_simp [hxabs0]
        _ ≤ 2 + |t| := by
              have hx_sq : 1 ≤ |x| ^ (2 : ℕ) := by nlinarith
              have htwo : 2 / (|x| ^ (2 : ℕ)) ≤ 2 := by
                have hpos : 0 < |x| ^ (2 : ℕ) := by positivity
                rw [div_le_iff₀ hpos]
                nlinarith
              have hdivt : |t| / |x| ≤ |t| := by
                have hpos1 : (0 : ℝ) < 1 := by positivity
                have hInv : 1 / |x| ≤ 1 := by
                  simpa using (one_div_le_one_div_of_le hpos1 hx1)
                calc
                  |t| / |x| = |t| * (1 / |x|) := by ring
                  _ ≤ |t| * 1 := by
                        gcongr
                  _ = |t| := by ring
              linarith
        _ ≤ max Ccore (2 + |t|) := le_max_right _ _

/-- Helper for Lemma 15.46: the centered quadratic kernel is canonically a bounded continuous
test function on `ℝ`. -/
private def centeredQuadraticCharFunKernelBCF (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  { toContinuousMap := ⟨centeredQuadraticCharFunKernel t,
      continuous_centeredQuadraticCharFunKernel (t := t)⟩
    map_bounded' := Metric.isBounded_range_iff.1
      (isBounded_range_centeredQuadraticCharFunKernel (t := t)) }

/-- Helper for Lemma 15.46: coercing the bundled centered quadratic kernel recovers the explicit
function. -/
@[simp] private lemma coe_centeredQuadraticCharFunKernelBCF (t : ℝ) :
    (centeredQuadraticCharFunKernelBCF t : ℝ → ℂ) = centeredQuadraticCharFunKernel t := rfl

/-- Helper for Lemma 15.46: the canonical owner measure on `ℝ` that records the `n`-th row by
weighting each entry law with the quadratic density `x ↦ x^2`. -/
private def varianceWeightedRowMeasure
    (n : ℕ) :
    Measure ℝ :=
  ∑ i : Fin (A.rowLength n),
    (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)

/-- Helper for Lemma 15.46: the threshold `-1` sees the whole real line because absolute values
are always nonnegative. -/
private lemma negOne_lt_abs_univ : {x : ℝ | (-1 : ℝ) < |x|} = Set.univ := by
  -- Proof comment: `|x|` is always at least `0`, so the inequality `-1 < |x|` is automatic.
  refine Set.eq_univ_of_forall ?_
  intro x
  have hneg : (-1 : ℝ) < 0 := by norm_num
  exact lt_of_lt_of_le hneg (abs_nonneg x)

/-- Helper for Lemma 15.46: the owner measure tail outside `(-ε, ε)` is exactly the textbook
truncated second-moment sum in row `n`. -/
private lemma varianceWeightedRowMeasure_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowMeasure μ n).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  classical
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by
    -- Proof comment: the tail set is measurable because `x ↦ |x|` is measurable.
    exact measurableSet_lt measurable_const measurable_abs
  -- Proof comment: expand the finite owner measure sum and rewrite each summand on the tail set
  -- back to the corresponding truncated second moment.
  rw [varianceWeightedRowMeasure, Measure.real_def]
  have hsum :
      ((∑ i : Fin (A.rowLength n),
          (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
        ∑ i : Fin (A.rowLength n),
          (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
    calc
      ((∑ i : Fin (A.rowLength n),
          (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
          (∑ i : Fin (A.rowLength n),
            ((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            simpa using
              congrArg ENNReal.toReal
                (Measure.sum_apply
                  (f := fun i : Fin (A.rowLength n) ↦
                    (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i))
                  hs)
      _ = ∑ i : Fin (A.rowLength n),
            (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            rw [ENNReal.toReal_sum]
            intro i hi
            have hSqInt : HasFiniteIntegral (fun ω ↦ (A n i ω) ^ 2) μ := by
              have hIntegrableSq : Integrable (fun ω ↦ (A n i ω) ^ 2) μ := by
                simpa using
                  (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
              exact hIntegrableSq.hasFiniteIntegral
            letI :
                IsFiniteMeasure (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) :=
              MeasureTheory.isFiniteMeasure_withDensity_ofReal hSqInt
            exact measure_ne_top _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs_pre : MeasurableSet ((A n i) ⁻¹' s) :=
    (A.measurable_entry n i) hs
  have hDensity_meas :
      AEMeasurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) (μ.restrict ((A n i) ⁻¹' s)) := by
    exact (((A.measurable_entry n i).pow_const 2).ennreal_ofReal.aemeasurable).restrict
  have hDensity_lt_top :
      ∀ᵐ ω ∂(μ.restrict ((A n i) ⁻¹' s)), ENNReal.ofReal ((A n i ω) ^ 2) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    ((((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal) =
        (∫⁻ ω in (A n i) ⁻¹' s, ENNReal.ofReal ((A n i ω) ^ 2) ∂μ).toReal := by
          rw [Measure.map_apply (A.measurable_entry n i) hs, withDensity_apply _ hs_pre]
    _ = ∫ ω in (A n i) ⁻¹' s, (A n i ω) ^ 2 ∂μ := by
          -- Proof comment: the density is finite everywhere, so `integral_toReal` converts the
          -- lower integral on the restricted measure into the corresponding set integral.
          simpa [ENNReal.toReal_ofReal, sq_nonneg] using
            (MeasureTheory.integral_toReal (μ := μ.restrict ((A n i) ⁻¹' s))
              hDensity_meas hDensity_lt_top).symm
    _ = ∫ ω, Set.indicator ((A n i) ⁻¹' s) (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          rw [MeasureTheory.integral_indicator hs_pre]
    _ = ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          simp [s]

/-- Helper for Lemma 15.46: the canonical owner measure has total mass `1`, so it can be viewed
as a probability law. -/
private lemma varianceWeightedRowMeasure_real_univ
    (n : ℕ) :
    (A.varianceWeightedRowMeasure μ n).real Set.univ = 1 := by
  have hTail :=
    varianceWeightedRowMeasure_tail_eq (A := A) (μ := μ) (-1) n
  rw [negOne_lt_abs_univ] at hTail
  -- Proof comment: at threshold `-1`, the tail set is all of `ℝ`, so the owner measure mass is
  -- the sum of the entry second moments; centeredness then identifies these with the entry
  -- variances, and the normed-array hypothesis normalizes the row sum to `1`.
  calc
    (A.varianceWeightedRowMeasure μ n).real Set.univ =
        ∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | (-1 : ℝ) < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          simpa [negOne_lt_abs_univ] using hTail
    _ =
        ∑ i : Fin (A.rowLength n), ∫ ω, (A n i ω) ^ 2 ∂μ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hAll : {ω : Ω | (-1 : ℝ) < |A n i ω|} = Set.univ := by
            refine Set.eq_univ_of_forall fun ω ↦ ?_
            have hneg : (-1 : ℝ) < 0 := by norm_num
            exact lt_of_lt_of_le hneg (abs_nonneg (A n i ω))
          simp [hAll]
    _ = ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact
            (ProbabilityTheory.variance_of_integral_eq_zero
              (A.measurable_entry n i).aemeasurable
              (RealRandomVariableArray.IsCentered.expectation_eq_zero
                (A := A) (μ := μ) n i)).symm
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n

/-- Helper for Lemma 15.46: each owner measure can be packaged as a probability measure because
its total mass is `1`. -/
private lemma varianceWeightedRowMeasure_isProbabilityMeasure
    (n : ℕ) :
    IsProbabilityMeasure (A.varianceWeightedRowMeasure μ n) := by
  rw [MeasureTheory.isProbabilityMeasure_iff_real]
  exact varianceWeightedRowMeasure_real_univ (A := A) (μ := μ) n

/-- Helper for Lemma 15.46: the canonical owner probability law attached to row `n`. -/
private def varianceWeightedRowLaw
    (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨A.varianceWeightedRowMeasure μ n,
    varianceWeightedRowMeasure_isProbabilityMeasure (A := A) (μ := μ) n⟩

/-- Helper for Lemma 15.46: coercing the owner probability law back to a measure recovers the
underlying weighted-row measure. -/
@[simp] private theorem varianceWeightedRowLaw_toMeasure
    (n : ℕ) :
    (A.varianceWeightedRowLaw μ n : Measure ℝ) = A.varianceWeightedRowMeasure μ n :=
  rfl

/-- Helper for Lemma 15.46: rewrite the weighted-entry kernel integral as a source-variable
integral against `μ`, with the quadratic weight moved into the integrand. -/
private lemma integral_centeredQuadraticCharFunKernel_weightedEntry_eq_sourceIntegral
    (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    ∫ x, centeredQuadraticCharFunKernelBCF t x
      ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        ∫ ω, centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ))) ∂μ := by
  have hKernelMap :
      AEStronglyMeasurable (centeredQuadraticCharFunKernelBCF t : ℝ → ℂ)
        (Measure.map (A n i) (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2))) := by
    exact
      (centeredQuadraticCharFunKernelBCF t).continuous.stronglyMeasurable.aestronglyMeasurable
  have hDensityMeas :
      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) := by
    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
  have hDensityFinite :
      ∀ᵐ ω ∂μ, ENNReal.ofReal ((A n i ω) ^ 2) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  -- Proof comment: first remove the pushforward, then turn the `withDensity` integral into a
  -- source integral where the quadratic weight appears directly in the integrand.
  rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]
  rw [integral_withDensity_eq_integral_toReal_smul hDensityMeas hDensityFinite]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
  change
    (((ENNReal.ofReal ((A n i ω) ^ 2)).toReal : ℝ) • centeredQuadraticCharFunKernel t (A n i ω)) =
      centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ)))
  rw [ENNReal.toReal_ofReal (sq_nonneg (A n i ω)), Complex.real_smul]
  simpa [pow_two, mul_comm]

/-- Helper for Lemma 15.46: one weighted entry law integrates the centered quadratic kernel to
the corresponding characteristic-function increment `φₙ,ᵢ(t) - 1`. -/
private lemma entryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_weightedEntry
    (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    ∫ x, centeredQuadraticCharFunKernelBCF t x
      ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        charFun (μ.map (A n i)) t - 1 := by
  have hTransport :=
    integral_centeredQuadraticCharFunKernel_weightedEntry_eq_sourceIntegral
      (A := A) (μ := μ) n i t
  have hEntryInt :
      Integrable (fun ω ↦ (A n i ω : ℂ)) μ :=
    (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := μ) n i).ofReal
  have hLinearInt :
      Integrable (fun ω ↦ Complex.I * (t * A n i ω : ℝ)) μ := by
    have hConst :
        Integrable (fun ω ↦ (Complex.I * (t : ℂ)) * (A n i ω : ℂ)) μ :=
      hEntryInt.const_mul (Complex.I * (t : ℂ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hConst
  have hExpKernelMeas :
      Measurable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) := by
    refine Complex.measurable_exp.comp ?_
    simpa using
      (Complex.measurable_ofReal.comp ((A.measurable_entry n i).const_mul t)).mul_const Complex.I
  have hExpKernelInt :
      Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) μ := by
    refine Integrable.of_bound hExpKernelMeas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n i ω)).le
  have hExpSubOneInt :
      Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I) - 1) μ :=
    hExpKernelInt.sub (integrable_const 1)
  have hMeanZero :
      ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ = 0 := by
    have hOfReal :
        ∫ ω, (A n i ω : ℂ) ∂μ = ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
      simpa using (integral_ofReal (μ := μ) (f := fun ω ↦ A n i ω))
    -- Proof comment: rewrite the complex linear term as a scalar multiple of the centered real
    -- expectation and then cancel it with the centeredness hypothesis.
    calc
      ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ =
          ∫ ω, (Complex.I * (t : ℂ)) * (A n i ω : ℂ) ∂μ := by
            congr with ω
            simp [mul_assoc]
      _ = (Complex.I * (t : ℂ)) * ∫ ω, (A n i ω : ℂ) ∂μ := by
            simpa using
              (integral_const_mul (μ := μ) (Complex.I * (t : ℂ))
                (fun ω ↦ (A n i ω : ℂ)))
      _ = (Complex.I * (t : ℂ)) * ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
            rw [hOfReal]
      _ = 0 := by
            simp [RealRandomVariableArray.IsCentered.expectation_eq_zero
              (A := A) (μ := μ) n i]
  have hKernelMap :
      AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        (Measure.map (A n i) μ) := by
    refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
    simpa using
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
  -- Route correction: after the transport lemma, cancel the quadratic denominator pointwise and
  -- only then identify the remaining source integral with `φₙ,ᵢ(t) - 1`.
  calc
    ∫ x, centeredQuadraticCharFunKernelBCF t x
        ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        ∫ ω, centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ))) ∂μ :=
          hTransport
    _ = ∫ ω,
          (Complex.exp (t * A n i ω * Complex.I) - 1 - Complex.I * (t * A n i ω : ℝ)) ∂μ := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
          simpa using centeredQuadraticCharFunKernel_mul_sq (t := t) (x := A n i ω)
    _ = ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ := by
          rw [integral_sub hExpSubOneInt hLinearInt, hMeanZero, sub_zero]
    _ = ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - 1 := by
          symm
          rw [integral_sub hExpKernelInt (integrable_const 1)]
          simp
    _ = charFun (μ.map (A n i)) t - 1 := by
          rw [MeasureTheory.charFun_apply_real]
          rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]

/-- Helper for Lemma 15.46: the full middle object `∑ (φₙ,ᵢ(t) - 1)` is exactly one integral
against the variance-weighted row law. -/
private lemma sumEntryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_varianceWeightedRowLaw
    (n : ℕ) (t : ℝ) :
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1) =
      ∫ x, centeredQuadraticCharFunKernelBCF t x ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
  calc
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1) =
        ∑ i : Fin (A.rowLength n),
          ∫ x, centeredQuadraticCharFunKernelBCF t x
            ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          symm
          exact
            entryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_weightedEntry
              (A := A) (μ := μ) n i t
    _ = ∫ x, centeredQuadraticCharFunKernelBCF t x ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
          rw [varianceWeightedRowLaw_toMeasure, varianceWeightedRowMeasure]
          symm
          refine integral_finset_sum_measure ?_
          intro i hi
          have hSqInt : HasFiniteIntegral (fun ω ↦ (A n i ω) ^ 2) μ := by
            have hIntegrableSq : Integrable (fun ω ↦ (A n i ω) ^ 2) μ := by
              simpa using
                (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
            exact hIntegrableSq.hasFiniteIntegral
          letI :
              IsFiniteMeasure (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) :=
            MeasureTheory.isFiniteMeasure_withDensity_ofReal hSqInt
          exact
            BoundedContinuousFunction.integrable
              (μ := (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) :
                Measure ℝ))
              (centeredQuadraticCharFunKernelBCF t)

/-- Helper for Lemma 15.46: convergence of the variance-weighted row laws to `δ₀` transports
directly to the middle-object limit `∑ (φₙ,ᵢ(t) - 1) → -t²/2`. -/
private lemma sumEntryCharFunSubOne_tendsto_gaussianExponent_of_varianceWeightedRowLaw
    (t : ℝ)
    (hWeighted :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ)))) :
    Tendsto
      (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  have hIntegral :
      Tendsto
        (fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝
          (∫ x, centeredQuadraticCharFunKernelBCF t x
            ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    exact
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hWeighted
        (centeredQuadraticCharFunKernelBCF t)
  have hDirac :
      (∫ x, centeredQuadraticCharFunKernelBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    -- Proof comment: the Dirac limit evaluates the bounded continuous kernel at the origin.
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    simp [centeredQuadraticCharFunKernel_apply_zero]
  have hIntegral' :
      Tendsto
        (fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    convert hIntegral using 1
    exact congrArg nhds hDirac.symm
  have hEq :
      (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)) =
        fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
    funext n
    exact
      sumEntryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_varianceWeightedRowLaw
        (A := A) (μ := μ) n t
  -- Proof comment: combine the rowwise integral identity with bounded-continuous transport of
  -- the weighted-row-law convergence to `δ₀`.
  rw [hEq]
  exact hIntegral'

/-- Helper for Lemma 15.46: the owner probability law has the same tail formula as the
underlying weighted-row measure. -/
private lemma varianceWeightedRowLaw_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  -- Proof comment: this is only the coercion rewrite from the owner law back to its measure.
  simpa [varianceWeightedRowLaw_toMeasure (A := A) (μ := μ) n] using
    varianceWeightedRowMeasure_tail_eq (A := A) (μ := μ) ε n

/-- Helper for Lemma 15.46: the Lindeberg condition already forces the canonical owner-law tails
to vanish outside every neighborhood of `0`. -/
private lemma varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|})
      atTop (𝓝 0) := by
  -- Proof comment: once the repaired tail formula is available, this reduces directly to the
  -- rowwise truncated-second-moment convergence already proved above.
  have hEq :
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|}) =
        (fun n ↦
          ∑ i : Fin (A.rowLength n),
            ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ) := by
    funext n
    exact varianceWeightedRowLaw_tail_eq (A := A) (μ := μ) ε n
  rw [hEq]
  exact rowTruncatedSecondMoment_tendstoZero (A := A) (μ := μ) hLindeberg hε

/-- Helper for Lemma 15.46: if a sequence of probability laws on `ℝ` puts asymptotically all of
its mass inside every neighborhood of `0`, then it integrates each bounded continuous test
function to its value at `0`. -/
private lemma tendsto_integral_boundedContinuous_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0))
    (f : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) atTop (𝓝 (f 0)) := by
  let g : BoundedContinuousFunction ℝ ℂ := f - BoundedContinuousFunction.const ℝ (f 0)
  have hg0 : g 0 = 0 := by
    -- Proof comment: after subtracting the constant value `f 0`, the centered test function
    -- vanishes at the limit point `0`.
    simp [g]
  have hIntegralEq :
      (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) =
        fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
    funext n
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hConstInt : Integrable (fun _ : ℝ ↦ (f 0 : ℂ)) (ν n : Measure ℝ) :=
      integrable_const _
    -- Proof comment: split `f` into its centered part `g` and the constant value `f 0`.
    calc
      ∫ x, f x ∂(ν n : Measure ℝ) = ∫ x, (g x + f 0) ∂(ν n : Measure ℝ) := by
        congr 1 with x
        simp [g]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + ∫ x, (f 0 : ℂ) ∂(ν n : Measure ℝ) := by
        rw [integral_add hgInt hConstInt]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
        simp
  rw [hIntegralEq]
  have hCentered :
      Tendsto (fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.1 g.continuous.continuousAt (ε / 4) (by positivity)
    let r : ℝ := δ / 2
    let s : Set ℝ := {x | r < |x|}
    have hrpos : 0 < r := by
      -- Proof comment: shrink the continuity neighborhood so that points outside `s` still lie in
      -- the continuity control ball around `0`.
      dsimp [r]
      exact half_pos hδpos
    have hs : MeasurableSet s := by
      exact measurableSet_lt measurable_const measurable_abs
    let C : ℝ := ‖g‖ + 1
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hTailSmall : ∀ᶠ n in atTop, (ν n : Measure ℝ).real s < ε / (4 * C) := by
      have hTail' : Tendsto (fun n ↦ (ν n : Measure ℝ).real s) atTop (𝓝 0) := by
        simpa [s, r] using hTail hrpos
      exact hTail' (Iio_mem_nhds (by positivity : 0 < ε / (4 * C)))
    filter_upwards [hTailSmall] with n hn
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hs_lt_top : (ν n : Measure ℝ) s < ⊤ := by
      simp [s]
    have hscompl_lt_top : (ν n : Measure ℝ) sᶜ < ⊤ := by
      simp [s]
    have hSmallOnCompl : ∀ x ∈ sᶜ, ‖g x‖ ≤ ε / 4 := by
      intro x hx
      have hxle : |x| ≤ r := by
        dsimp [s] at hx
        exact le_of_not_gt hx
      have hrlt : r < δ := by
        dsimp [r]
        linarith
      have hxdist : dist x 0 < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using lt_of_le_of_lt hxle hrlt
      have hxcont : dist (g x) (g 0) < ε / 4 := hδ hxdist
      -- Proof comment: points outside the tail set stay inside the continuity neighborhood where
      -- the centered test function is uniformly small.
      simpa [hg0, dist_eq_norm] using le_of_lt hxcont
    have hTailIntegral :
        ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ < ε / 4 := by
      have hBase :
          ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ ≤ ‖g‖ * (ν n : Measure ℝ).real s :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_lt_top
          (fun x _ ↦ BoundedContinuousFunction.norm_coe_le_norm g x)
      have hCmul :
          ‖g‖ * (ν n : Measure ℝ).real s ≤ C * (ν n : Measure ℝ).real s := by
        dsimp [C]
        gcongr
        linarith
      have hScaled :
          C * (ν n : Measure ℝ).real s < C * (ε / (4 * C)) := by
        gcongr
      have hRewrite : C * (ε / (4 * C)) = ε / 4 := by
        field_simp [hCpos.ne']
      exact lt_of_le_of_lt (hBase.trans hCmul) (hScaled.trans_eq hRewrite)
    have hComplIntegral :
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ ε / 4 := by
      have hBase :
          ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤
            (ε / 4) * (ν n : Measure ℝ).real sᶜ :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hscompl_lt_top hSmallOnCompl
      have hMassLeOne : (ν n : Measure ℝ).real sᶜ ≤ 1 := by
        calc
          (ν n : Measure ℝ).real sᶜ ≤ (ν n : Measure ℝ).real Set.univ := by
            exact MeasureTheory.measureReal_mono (by intro x _; simp)
          _ = 1 := by
            simp
      calc
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ (ε / 4) * (ν n : Measure ℝ).real sᶜ := hBase
        _ ≤ (ε / 4) * 1 := by
          gcongr
        _ = ε / 4 := by ring
    have hSplit := (integral_add_compl hs hgInt).symm
    -- Proof comment: split the centered integral into the tiny tail part and the uniformly small
    -- near-zero part, then add the two bounds.
    calc
      dist (∫ x, g x ∂(ν n : Measure ℝ)) 0 = ‖∫ x, g x ∂(ν n : Measure ℝ)‖ := by
        simp [dist_eq_norm]
      _ = ‖∫ x in s, g x ∂(ν n : Measure ℝ) + ∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        rw [← hSplit]
      _ ≤ ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ + ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        exact norm_add_le _ _
      _ ≤ ε / 4 + ε / 4 := by
        linarith [le_of_lt hTailIntegral, hComplIntegral]
      _ = ε / 2 := by ring
      _ < ε := by linarith
  simpa [zero_add] using hCentered.add tendsto_const_nhds

/-- Helper for Lemma 15.46: vanishing tails outside every neighborhood of `0` force weak
convergence to the Dirac probability measure at `0`. -/
private lemma tendsto_diracProba_zero_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0)) :
    Tendsto ν atTop (𝓝 (diracProba (0 : ℝ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hIntegral :=
    tendsto_integral_boundedContinuous_of_tail_tendsto_zero hTail f
  have hDirac :
      (∫ x, f x ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = f 0 := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
  convert hIntegral using 1
  exact congrArg nhds hDirac

/-- Helper for Lemma 15.46: the Lindeberg condition already implies weak convergence of the
canonical weighted-row laws to `diracProba 0`. -/
private lemma varianceWeightedRowLaw_tendsto_diracZero_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition μ) :
    Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ))) := by
  -- Proof comment: once the weighted-row tails vanish outside every neighborhood of `0`, the
  -- generic bounded-continuous test-function lemma identifies the weak limit as `δ₀`.
  refine tendsto_diracProba_zero_of_tail_tendsto_zero ?_
  intro ε hε
  exact
    varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
      (A := A) (μ := μ) hLindeberg hε

end

section

variable (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [A.IsIndependent μ] [A.IsNormed μ]

/-- Helper for Lemma 15.46: the characteristic function of a row sum factors into the product of
the entry characteristic functions in that row. -/
private lemma rowSumLaw_charFun_eq_prod_entryCharFun
    (n : ℕ) (t : ℝ) :
    charFun (A.rowSumLaw μ n : Measure ℝ) t =
      ∏ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t := by
  -- Proof comment: rewrite the row-sum law as the pushforward of the actual row sum, then apply
  -- the finite-family characteristic-function factorization from rowwise independence.
  rw [A.rowSumLaw_toMeasure μ n]
  have hrow : A.rowSum n = fun ω ↦ ∑ i : Fin (A.rowLength n), A n i ω := by
    funext ω
    simp [RealRandomVariableArray.rowSum, Finset.sum_apply]
  rw [hrow]
  simpa using congrFun
    ((RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := μ) n).charFun_map_fun_sum_eq_prod
      (fun i ↦ (A.measurable_entry n i).aemeasurable)) t

/-- Helper for Lemma 15.46: the first-order characteristic-function sum converges to the same
Gaussian exponent as the row logarithm. -/
private theorem sumEntryCharFunSubOne_tendstoGaussianExponent
    (hLindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  -- Proof comment: the weighted-row-law convergence reduces the whole first-order sum to one
  -- bounded continuous kernel integral against laws converging to `δ₀`.
  have hWeighted :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ))) :=
    varianceWeightedRowLaw_tendsto_diracZero_of_satisfiesLindebergCondition
      (A := A) (μ := μ) hLindeberg
  exact
    sumEntryCharFunSubOne_tendsto_gaussianExponent_of_varianceWeightedRowLaw
      (A := A) (μ := μ) t hWeighted

/-- Helper for Lemma 15.46: the summed logarithmic remainder
`Σ log φₙ,ᵢ(t) - Σ (φₙ,ᵢ(t) - 1)` tends to `0`. -/
private theorem sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero
    (hLindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦
        ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖)
      atTop
      (𝓝 0) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let B : ℝ := t ^ (2 : ℕ) / 2 + 1
  let δ : ℝ := min (1 / 2 : ℝ) (ε / (2 * B))
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδbound : δ ≤ ε / (2 * B) := by
    dsimp [δ]
    exact min_le_right _ _
  filter_upwards [eventually_entryCharFunSubOne_le (A := A) (μ := μ) hLindeberg t hδpos] with n hn
  let z : Fin (A.rowLength n) → ℂ := fun i ↦ charFun (μ.map (A n i)) t
  have hterm :
      ∀ i : Fin (A.rowLength n),
        ‖Complex.log (z i) - (z i - 1)‖ ≤ δ * ‖z i - 1‖ := by
    intro i
    have hz_lt_one : ‖z i - 1‖ < 1 := by
      have hquarter : (1 / 2 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt (hn i) (lt_of_le_of_lt hδhalf hquarter)
    have hhalf : ‖z i - 1‖ ≤ 1 / 2 := le_trans (hn i) hδhalf
    have hpos : 0 < 1 - ‖z i - 1‖ := by linarith
    have hInv : (1 - ‖z i - 1‖)⁻¹ ≤ 2 := by
      have hge : (1 / 2 : ℝ) ≤ 1 - ‖z i - 1‖ := by linarith
      have htmp : 1 / (1 - ‖z i - 1‖) ≤ (1 / (1 / 2 : ℝ)) := by
        exact one_div_le_one_div_of_le (by norm_num : 0 < (1 / 2 : ℝ)) hge
      simpa using htmp
    have hfactor : (1 - ‖z i - 1‖)⁻¹ / 2 ≤ 1 := by
      nlinarith
    have hsq_nonneg : 0 ≤ ‖z i - 1‖ ^ (2 : ℕ) := by positivity
    calc
      ‖Complex.log (z i) - (z i - 1)‖ =
          ‖Complex.log (1 + (z i - 1)) - (z i - 1)‖ := by
            congr 1
            ring
      _ ≤ ‖z i - 1‖ ^ (2 : ℕ) * (1 - ‖z i - 1‖)⁻¹ / 2 := by
            exact Complex.norm_log_one_add_sub_self_le hz_lt_one
      _ ≤ ‖z i - 1‖ ^ (2 : ℕ) := by
            nlinarith
      _ ≤ δ * ‖z i - 1‖ := by
            nlinarith [hn i, norm_nonneg (z i - 1)]
  have hsum :
      ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ ≤
        δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := by
    calc
      ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ ≤
          ∑ i : Fin (A.rowLength n), δ * ‖z i - 1‖ := by
            exact Finset.sum_le_sum fun i _ ↦ hterm i
      _ = δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := by
            rw [Finset.mul_sum]
  have hBudget :
      ∑ i : Fin (A.rowLength n), ‖z i - 1‖ ≤ t ^ (2 : ℕ) / 2 := by
    simpa [z] using sumNormEntryCharFunSubOne_le_halfSq (A := A) (μ := μ) n t
  have hCoreLeB : t ^ (2 : ℕ) / 2 ≤ B := by
    dsimp [B]
    linarith
  have hδB : δ * B ≤ ε / 2 := by
    calc
      δ * B ≤ (ε / (2 * B)) * B := by
            gcongr
      _ = ε / 2 := by
            field_simp [hBpos.ne']
  have hBound :
      ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
          ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖ < ε := by
    calc
      ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
          ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖
          = ‖∑ i : Fin (A.rowLength n),
              (Complex.log (z i) - (z i - 1))‖ := by
                rw [Finset.sum_sub_distrib]
                simp [z]
      _ ≤ ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ := by
            simpa using
              (norm_sum_le (s := Finset.univ)
                (f := fun i : Fin (A.rowLength n) ↦ Complex.log (z i) - (z i - 1)))
      _ ≤ δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := hsum
      _ ≤ δ * (t ^ (2 : ℕ) / 2) := by
            gcongr
      _ ≤ δ * B := by
            gcongr
      _ ≤ ε / 2 := hδB
      _ < ε := by linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hBound

/-- Helper for Lemma 15.46: the row characteristic functions converge to the Gaussian
characteristic exponent via the eventual exponential formula for the row-product of logs. -/
private theorem rowSumLawCharFun_tendstoGaussianExponent
    (hLindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) t)
      atTop
      (𝓝 (Complex.exp ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) := by
  letI : A.IsCentered μ := hLindeberg.toIsCentered
  have hSumEntry :
      Tendsto
        (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) :=
    sumEntryCharFunSubOne_tendstoGaussianExponent (A := A) (μ := μ) hLindeberg t
  have hLogRemainderNorm :
      Tendsto
        (fun n ↦
          ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
              ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖)
        atTop
        (𝓝 0) :=
    sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero
      (A := A) (μ := μ) hLindeberg t
  have hLogRemainder :
      Tendsto
        (fun n ↦
          (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
        atTop
        (𝓝 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.2 hLogRemainderNorm
  have hSumLog :
      Tendsto
        (fun n ↦ ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have hEq :
        (fun n ↦
          ((∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
              ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)) +
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)) =
          (fun n ↦ ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) := by
      funext n
      abel
    rw [← hEq]
    simpa using hLogRemainder.add hSumEntry
  have hExpSumLog :
      Tendsto
        (fun n ↦ Complex.exp (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)))
        atTop
        (𝓝 (Complex.exp ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) :=
    hSumLog.cexp
  have hQuarter :
      ∀ᶠ n in atTop,
        ∀ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ ≤ (1 / 4 : ℝ) :=
    eventually_entryCharFunSubOne_le (A := A) (μ := μ) hLindeberg t (by positivity)
  have hRowExp :
      ∀ᶠ n in atTop,
        charFun (A.rowSumLaw μ n : Measure ℝ) t =
          Complex.exp
            (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) := by
    filter_upwards [hQuarter] with n hn
    have hentry_ne :
        ∀ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t ≠ 0 := by
      intro i hzero
      have hone : ‖charFun (μ.map (A n i)) t - 1‖ = 1 := by
        simp [hzero]
      have hsmall : ‖charFun (μ.map (A n i)) t - 1‖ < 1 / 2 := by
        exact lt_of_le_of_lt (hn i) (by norm_num)
      linarith
    -- Route correction: with the rowwise defects eventually inside the principal branch ball, the
    -- row product is exactly `exp (∑ log ...)`, so the same-limit route closes locally.
    calc
      charFun (A.rowSumLaw μ n : Measure ℝ) t =
          ∏ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t := by
            exact rowSumLaw_charFun_eq_prod_entryCharFun (A := A) (μ := μ) n t
      _ = ∏ i : Fin (A.rowLength n), Complex.exp (Complex.log (charFun (μ.map (A n i)) t)) := by
            refine Finset.prod_congr rfl fun i _ ↦ ?_
            symm
            exact Complex.exp_log (hentry_ne i)
      _ = Complex.exp
            (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) := by
            symm
            exact Complex.exp_sum _ _
  have hRowExpSymm :
      (fun n ↦ Complex.exp
        (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t))) =ᶠ[atTop]
        fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) t := by
    filter_upwards [hRowExp] with n hn
    exact hn.symm
  exact Tendsto.congr' hRowExpSymm hExpSumLog

/-- Helper for Lemma 15.46: the logarithm of the row-sum characteristic function converges to the
Gaussian exponent `-t² / 2`. -/
private theorem rowSumLawLog_tendstoGaussianExponent
    (hLindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦ Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) t))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  have hChar :
      Tendsto
        (fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) t)
        atTop
        (𝓝 (Complex.exp ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) :=
    rowSumLawCharFun_tendstoGaussianExponent (A := A) (μ := μ) hLindeberg t
  have hMem :
      Complex.exp ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    simpa using
      (Complex.ofReal_mem_slitPlane.2
        (Real.exp_pos (-(t ^ (2 : ℕ) / 2 : ℝ))))
  have hLogEval :
      Complex.log (Complex.exp (-(↑t ^ (2 : ℕ) / 2))) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    have hCast :
        (-(↑t ^ (2 : ℕ) / 2 : ℂ)) = -↑(t ^ (2 : ℕ) / 2) := by
      simp
    rw [hCast]
    calc
      Complex.log (Complex.exp (-↑(t ^ (2 : ℕ) / 2))) =
          Complex.log (((Real.exp (-(t ^ (2 : ℕ) / 2 : ℝ))) : ℝ) : ℂ) := by
            simp
      _ = (((Real.exp (-(t ^ (2 : ℕ) / 2 : ℝ))).log : ℝ) : ℂ) := by
            symm
            exact Complex.ofReal_log (show 0 ≤ Real.exp (-(t ^ (2 : ℕ) / 2 : ℝ)) by positivity)
      _ = ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
            simp
  -- Route correction: after obtaining characteristic-function convergence from Theorem 15.43,
  -- apply `Complex.log` at the positive real Gaussian limit.
  have hLog := hChar.clog hMem
  simpa [hLogEval] using hLog

/-- Lemma 15.46: under the standing setup of Theorem 15.43 and its item (i) Lindeberg condition,
the logarithm of the row characteristic function is asymptotically equal to the sum of the
first-order terms `φₙ,ᵢ(t) - 1`. -/
theorem rowSumLaw_log_sub_sum_entryCharFun_tendsto_zero
    (hLindeberg : A.SatisfiesLindebergCondition μ) (t : ℝ) :
    Tendsto
      (fun n ↦
        ‖Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) t) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖)
      atTop
      (𝓝 0) := by
  letI : A.IsCentered μ := hLindeberg.toIsCentered
  have hRowLog :
      Tendsto
        (fun n ↦ Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) t))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) :=
    rowSumLawLog_tendstoGaussianExponent (A := A) (μ := μ) hLindeberg t
  have hSumEntry :
      Tendsto
        (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) :=
    sumEntryCharFunSubOne_tendstoGaussianExponent (A := A) (μ := μ) hLindeberg t
  have hDiff :
      Tendsto
        (fun n ↦
          Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) t) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
        atTop
        (𝓝 (0 : ℂ)) := by
    -- Proof comment: both terms have the same Gaussian limit, so their difference tends to `0`.
    simpa using hRowLog.sub hSumEntry
  -- Proof comment: convert convergence of the complex difference to convergence of its norm.
  exact tendsto_zero_iff_norm_tendsto_zero.1 hDiff

end

end RealRandomVariableArray

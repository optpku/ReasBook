module

public import ReasLib.Optimization.DFP.Polar.General.Recurrence
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.UniformRemainder

public section

noncomputable section

open Filter
open scoped Topology Matrix ContDiff

namespace DFP.Polar.General.Estimates

/-- Helper for eq:polar-slow-drift: the new canceled stage and the inherited
rational-family API use the same normalized slope. -/
theorem slope_eq_original (x : ℝ × ℝ × ℝ) :
    Normalized.slope x = DFP.Polar.Normalized.slope x := by
  rw [Normalized.slope_def, DFP.Polar.Normalized.slope_def]

/-- Helper for eq:polar-slow-drift: at zero scale the first diagonal entry is
the source DFP bracket's scalar expansion in its first secant component. -/
theorem stage_zero_first_formula (a : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    (Normalized.stage a 0 x ζ η).1 =
      x.1 + 2 * ((x.1 * Normalized.slope x - x.2.1) *
          (Normalized.stepW a 0 x ζ η 0 / Normalized.stageSigma a 0 x ζ η)) +
        (x.1 * Normalized.slope x ^ 2 - 2 * x.2.1 * Normalized.slope x + x.2.2) *
          (Normalized.stepW a 0 x ζ η 0 / Normalized.stageSigma a 0 x ζ η) ^ 2 +
        Normalized.stepW a 0 x ζ η 0 ^ 2 / Normalized.stageSigma a 0 x ζ η := by
  simp only [Normalized.stage_apply, Normalized.stageMatrix_def,
    Normalized.rotation_def, Normalized.stageAngle_def, Normalized.stepV_def,
    mul_zero, Real.cos_zero, one_mul, mul_one,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul, RealSymmetric2.matrix_eq, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    div_eq_mul_inv, one_mul]
  norm_num
  ring

/-- Helper for eq:polar-slow-drift: the differential of the source first-entry
bracket depends only on the linear secant perturbation at a unit secant scalar. -/
theorem hasDerivAt_firstBracket {γ A B w σ : ℝ → ℝ} {γ' w' : ℝ}
    (hγ : HasDerivAt γ γ' 0) (hA : DifferentiableAt ℝ A 0)
    (hB : DifferentiableAt ℝ B 0) (hw : HasDerivAt w w' 0)
    (hσ : DifferentiableAt ℝ σ 0) (hw0 : w 0 = 0) (hσ0 : σ 0 = 1) :
    HasDerivAt (fun v ↦ γ v + 2 * (A v * (w v / σ v)) +
      B v * (w v / σ v) ^ 2 + w v ^ 2 / σ v)
      (γ' + 2 * (A 0 * w')) 0 := by
  have hσne : σ 0 ≠ 0 := by
    rw [hσ0]
    exact one_ne_zero
  have hquotRaw := hw.fun_div hσ.hasDerivAt hσne
  have hquotCoefficient :
      (w' * σ 0 - w 0 * deriv σ 0) / σ 0 ^ 2 = w' := by
    rw [hw0, hσ0]
    ring
  have hquot := hquotRaw.congr_deriv hquotCoefficient
  have hlinear := (hA.hasDerivAt.fun_mul hquot).const_mul 2
  have hquadratic := hB.hasDerivAt.fun_mul (hquot.fun_pow 2)
  have hsecant := (hw.fun_pow 2).fun_div hσ.hasDerivAt hσne
  have htotal := ((hγ.fun_add hlinear).fun_add hquadratic).fun_add hsecant
  simpa only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, hw0, hσ0,
    zero_div, Nat.reduceSub, pow_one, pow_two, mul_zero, zero_mul,
    mul_one, add_zero, zero_add, sub_zero, div_one, one_pow] using htotal

/-- Helper for eq:polar-slow-drift: the first normalized secant component at zero
scale is exactly the gradient-factor difference divided by the angle coefficient. -/
theorem stepW_zero_first (a : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    Normalized.stepW a 0 x ζ η 0 = (η - ζ) / a := by
  simp only [Normalized.stepW_def, Normalized.cotFactor_def,
    Normalized.sinFactor_def, Normalized.stageAngle_def, mul_zero, Real.cos_zero,
    Real.sinc_zero, mul_one, Matrix.cons_val_zero, pow_two, zero_mul, sub_zero,
    div_eq_mul_inv, one_mul]

/-- Helper for eq:polar-slow-drift: the zero-scale secant scalar separates its
first-component perturbation from the final gradient factor. -/
theorem stageSigma_zero_formula (a : ℝ) (x : ℝ × ℝ × ℝ) (ζ η : ℝ) :
    Normalized.stageSigma a 0 x ζ η =
      -Normalized.slope x * ((η - ζ) / a) + η := by
  rw [Normalized.stageSigma_def]
  simp only [dotProduct, Fin.sum_univ_two, Normalized.stepV_def,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [stepW_zero_first]
  simp only [Normalized.stepW_def, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]

/-- Helper for eq:polar-slow-drift: differentiating one zero-scale stage retains
the input first-coordinate derivative and the linear gradient-factor correction. -/
theorem hasDerivAt_stage_zero_first {a ζ η : ℝ → ℝ} {X : ℝ → ℝ × ℝ × ℝ}
    {γ' ζ' η' : ℝ} (ha : DifferentiableAt ℝ a 0)
    (hX : DifferentiableAt ℝ X 0) (hγ : HasDerivAt (fun v ↦ (X v).1) γ' 0)
    (hζ : HasDerivAt ζ ζ' 0) (hη : HasDerivAt η η' 0)
    (ha0 : a 0 ≠ 0) (hC : (X 0).2.1 ≠ 0) (hζ0 : ζ 0 = 1) (hη0 : η 0 = 1) :
    HasDerivAt (fun v ↦ (Normalized.stage (a v) 0 (X v) (ζ v) (η v)).1)
      (γ' + 2 * (((X 0).1 * Normalized.slope (X 0) - (X 0).2.1) *
        ((η' - ζ') / a 0))) 0 := by
  have hSlope : DifferentiableAt ℝ (fun v ↦ Normalized.slope (X v)) 0 := by
    simpa only [Normalized.slope_def] using (hX.snd.snd.fun_div hX.snd.fst hC)
  have hA : DifferentiableAt ℝ
      (fun v ↦ (X v).1 * Normalized.slope (X v) - (X v).2.1) 0 :=
    (hX.fst.mul hSlope).sub hX.snd.fst
  have hB : DifferentiableAt ℝ
      (fun v ↦ (X v).1 * Normalized.slope (X v) ^ 2 -
        2 * (X v).2.1 * Normalized.slope (X v) + (X v).2.2) 0 :=
    ((hX.fst.mul (hSlope.pow 2)).sub
      ((hX.snd.fst.const_mul 2).mul hSlope)).add hX.snd.snd
  have hquotRaw := (hη.fun_sub hζ).fun_div ha.hasDerivAt ha0
  have hquotCoefficient :
      ((η' - ζ') * a 0 - (η 0 - ζ 0) * deriv a 0) / a 0 ^ 2 =
        (η' - ζ') / a 0 := by
    rw [hζ0, hη0]
    field_simp [ha0]
    ring
  have hquot := hquotRaw.congr_deriv hquotCoefficient
  have hw : HasDerivAt (fun v ↦ Normalized.stepW (a v) 0 (X v) (ζ v) (η v) 0)
      ((η' - ζ') / a 0) 0 := by
    simpa only [stepW_zero_first] using hquot
  have hσ : DifferentiableAt ℝ
      (fun v ↦ Normalized.stageSigma (a v) 0 (X v) (ζ v) (η v)) 0 := by
    simpa only [stageSigma_zero_formula] using
      (hSlope.fun_neg.fun_mul hquot.differentiableAt).fun_add hη.differentiableAt
  have hw0 : Normalized.stepW (a 0) 0 (X 0) (ζ 0) (η 0) 0 = 0 := by
    rw [stepW_zero_first, hζ0, hη0, sub_self, zero_div]
  have hσ0 : Normalized.stageSigma (a 0) 0 (X 0) (ζ 0) (η 0) = 1 := by
    rw [stageSigma_zero_formula, hζ0, hη0, sub_self, zero_div, mul_zero, zero_add]
  simpa only [stage_zero_first_formula] using
    hasDerivAt_firstBracket hγ hA hB hw hσ hw0 hσ0

/-- Helper for eq:polar-feedback: the source feedback has first inverse-index
derivative equal to minus its potential at the even boundary. -/
theorem hasDerivAt_feedback_zero (φ : ℝ → ℝ) (γ : ℝ) :
    HasDerivAt (fun v ↦ Normalized.feedback φ v γ) (-φ γ) 0 := by
  simpa only [Normalized.feedback_def, id_eq, mul_zero, Real.exp_zero, one_mul, mul_one] using
    ((hasDerivAt_id (0 : ℝ)).const_mul (-φ γ)).exp

/-- Helper for eq:polar-slow-drift: the source scale ratio has inverse-index
derivative `-1 / (1 + β)` at zero. -/
theorem hasDerivAt_scaleRatio_zero (β : ℝ) :
    HasDerivAt (Normalized.scaleRatio β) (-1 / (1 + β)) 0 := by
  have hbase : (1 : ℝ) + 0 ≠ 0 := by
    norm_num
  have hlog := (((hasDerivAt_id (0 : ℝ)).const_add 1).log hbase).neg
  have hratio := (hlog.div_const (1 + β)).exp
  rw [funext (Normalized.scaleRatio_def β)]
  simpa only [Pi.neg_apply, id_eq, add_zero, Real.log_one, neg_zero,
    zero_div, Real.exp_zero, one_mul, div_one, neg_div] using hratio

/-- Helper for eq:polar-slow-drift: the two zero-scale stages add their opposite
shared-feedback corrections to the first coordinate. -/
theorem hasDerivAt_twoStep_zeroScale_first (aE aO φ : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (Normalized.leadingStage (aE 0) x).2.1 ≠ 0) :
    HasDerivAt (fun v ↦ (Normalized.twoStep aE aO φ 0 v x).1)
      (2 * φ x.1 *
        (((Normalized.leadingStage (aE 0) x).1 *
              Normalized.slope (Normalized.leadingStage (aE 0) x) -
            (Normalized.leadingStage (aE 0) x).2.1) / aO 0 -
          (x.1 * Normalized.slope x - x.2.1) / aE 0)) 0 := by
  let y : ℝ → ℝ × ℝ × ℝ :=
    fun v ↦ Normalized.stage (aE v) 0 x 1 (Normalized.feedback φ v x.1)
  have hfeedback : AnalyticAt ℝ (fun v ↦ Normalized.feedback φ v x.1) 0 := by
    simp only [Normalized.feedback_def]
    fun_prop
  have hσ : Normalized.stageSigma (aE 0) 0 x 1
      (Normalized.feedback φ 0 x.1) ≠ 0 := by
    simp only [stageSigma_zero_formula, Normalized.feedback_zero, sub_self,
      zero_div, mul_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true]
  have hy : AnalyticAt ℝ y 0 :=
    Normalized.stageAlong_analyticAt haE analyticAt_const analyticAt_const
      analyticAt_const hfeedback ha0 rfl hC hσ
  have hy0 : y 0 = Normalized.leadingStage (aE 0) x := by
    simp only [y, Normalized.feedback_zero, Normalized.stage_zero]
  have hyC : (y 0).2.1 ≠ 0 := by
    rwa [hy0]
  have hEraw := hasDerivAt_stage_zero_first haE.differentiableAt
    (differentiableAt_const x) (hasDerivAt_const 0 x.1) (hasDerivAt_const 0 (1 : ℝ))
    (hasDerivAt_feedback_zero φ x.1) ha0 hC rfl (Normalized.feedback_zero φ x.1)
  have hEcoefficient : 0 + 2 * ((x.1 * Normalized.slope x - x.2.1) *
      ((-φ x.1 - 0) / aE 0)) =
      -(2 * (x.1 * Normalized.slope x - x.2.1) * φ x.1 / aE 0) := by
    ring
  have hE := hEraw.congr_deriv hEcoefficient
  have hOraw := hasDerivAt_stage_zero_first haO.differentiableAt hy.differentiableAt hE
    (hasDerivAt_feedback_zero φ x.1) (hasDerivAt_const 0 (1 : ℝ)) hb0 hyC
    (Normalized.feedback_zero φ x.1) rfl
  have hOcoefficient : -(2 * (x.1 * Normalized.slope x - x.2.1) * φ x.1 / aE 0) +
      2 * (((y 0).1 * Normalized.slope (y 0) - (y 0).2.1) *
        ((0 - -φ x.1) / aO 0)) =
      2 * φ x.1 *
        (((Normalized.leadingStage (aE 0) x).1 *
              Normalized.slope (Normalized.leadingStage (aE 0) x) -
            (Normalized.leadingStage (aE 0) x).2.1) / aO 0 -
          (x.1 * Normalized.slope x - x.2.1) / aE 0) := by
    rw [hy0]
    ring
  simpa only [Normalized.twoStep_apply, Normalized.cycleStage_even,
    Normalized.cycleStage_odd, y] using hOraw.congr_deriv hOcoefficient

/-- Helper for eq:polar-slow-drift: the first cycle coordinate separates the
scale-ratio square from the first coordinate of the two shared-feedback stages. -/
theorem map_first (β : ℝ) (aE aO φ : ℝ → ℝ) (t v : ℝ) (x : ℝ × ℝ × ℝ) :
    (Normalized.map β aE aO φ t v x).1 =
      Normalized.scaleRatio β v ^ 2 * (Normalized.twoStep aE aO φ t v x).1 := by
  rw [Normalized.map_apply, Normalized.rescale_apply]

/-- Helper for eq:polar-slow-drift: the inverse-index differential of the actual
cycle is the sum of both shared-feedback terms and the reciprocal-square scale term. -/
theorem hasDerivAt_map_zeroScale_first (β : ℝ) (aE aO φ : ℝ → ℝ)
    (x : ℝ × ℝ × ℝ) (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0) (hC : x.2.1 ≠ 0)
    (hCNext : (Normalized.leadingStage (aE 0) x).2.1 ≠ 0) :
    HasDerivAt (fun v ↦ (Normalized.map β aE aO φ 0 v x).1)
      (2 * φ x.1 *
        (((Normalized.leadingStage (aE 0) x).1 *
              Normalized.slope (Normalized.leadingStage (aE 0) x) -
            (Normalized.leadingStage (aE 0) x).2.1) / aO 0 -
          (x.1 * Normalized.slope x - x.2.1) / aE 0) -
        2 * x.1 / (1 + β)) 0 := by
  have htwo := hasDerivAt_twoStep_zeroScale_first aE aO φ x haE haO ha0 hb0 hC hCNext
  have hproduct := ((hasDerivAt_scaleRatio_zero β).fun_pow 2).fun_mul htwo
  have htwo0 : (Normalized.twoStep aE aO φ 0 0 x).1 = x.1 := by
    rw [Normalized.twoStep_zero, Normalized.leadingStage_apply,
      Normalized.leadingStage_apply]
  simp only [Normalized.scaleRatio_zero, htwo0, Nat.reduceSub, pow_one,
    one_pow, one_mul, mul_one, Nat.cast_ofNat] at hproduct
  have hcoefficient :
      2 * (-1 / (1 + β)) * x.1 +
        (2 * φ x.1 *
          (((Normalized.leadingStage (aE 0) x).1 *
                Normalized.slope (Normalized.leadingStage (aE 0) x) -
              (Normalized.leadingStage (aE 0) x).2.1) / aO 0 -
            (x.1 * Normalized.slope x - x.2.1) / aE 0)) =
      2 * φ x.1 *
        (((Normalized.leadingStage (aE 0) x).1 *
              Normalized.slope (Normalized.leadingStage (aE 0) x) -
            (Normalized.leadingStage (aE 0) x).2.1) / aO 0 -
          (x.1 * Normalized.slope x - x.2.1) / aE 0) -
        2 * x.1 / (1 + β) := by
    ring
  simpa only [map_first] using hproduct.congr_deriv hcoefficient

/-- Helper for eq:polar-slow-drift: the even feedback coefficient is the preserved
diagonal coordinate times the positive even angular gap. -/
theorem evenState_feedbackCoefficient {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    (evenState δE δO ν).1 * Normalized.slope (evenState δE δO ν) -
        (evenState δE δO ν).2.1 = cycleGamma δE δO ν * (δE - ν) := by
  have hmatching : cycleLambdaEven δE δO ν = cycleLambdaOdd δE δO ν + ν := by
    linarith [cycleLambdaEven_sub_odd h]
  rw [slope_eq_original, slope_evenState h, evenState_def, cycleState_apply]
  dsimp only
  rw [hmatching]
  ring

/-- Helper for eq:polar-slow-drift: the odd feedback coefficient is the preserved
diagonal coordinate times the positive odd angular gap. -/
theorem oddState_feedbackCoefficient {δE δO ν : ℝ} (h : CycleDomain δE δO ν) :
    (oddState δE δO ν).1 * Normalized.slope (oddState δE δO ν) -
        (oddState δE δO ν).2.1 = cycleGamma δE δO ν * (δO + ν) := by
  have hmatching : cycleLambdaEven δE δO ν = cycleLambdaOdd δE δO ν + ν := by
    linarith [cycleLambdaEven_sub_odd h]
  rw [slope_eq_original, slope_oddState h, oddState_def, cycleState_apply]
  dsimp only
  rw [hmatching]
  ring

/-- Helper for eq:polar-slow-drift: on the rational two-cycle family the actual
inverse-index derivative is the source feedback drift before its prescribed cancellation. -/
theorem hasDerivAt_map_evenState_first (β : ℝ) (aE aO φ : ℝ → ℝ) (ν : ℝ)
    (haE : AnalyticAt ℝ aE 0) (haO : AnalyticAt ℝ aO 0)
    (ha0 : aE 0 ≠ 0) (hb0 : aO 0 ≠ 0) (h : CycleDomain (aE 0) (aO 0) ν) :
    HasDerivAt (fun v ↦
      (Normalized.map β aE aO φ 0 v (evenState (aE 0) (aO 0) ν)).1)
      (2 * cycleGamma (aE 0) (aO 0) ν * ν * (1 / aE 0 + 1 / aO 0) *
          φ (cycleGamma (aE 0) (aO 0) ν) -
        2 * cycleGamma (aE 0) (aO 0) ν / (1 + β)) 0 := by
  have hC : (evenState (aE 0) (aO 0) ν).2.1 ≠ 0 := by
    rw [evenState_def, cycleState_apply]
    exact (mul_pos (cycleGamma_pos h) (cycleLambdaEven_pos h)).ne'
  have hCNext :
      (Normalized.leadingStage (aE 0) (evenState (aE 0) (aO 0) ν)).2.1 ≠ 0 := by
    rw [Parameters.leadingStage_eq_original, evenToOdd h, oddState_def, cycleState_apply]
    exact (mul_pos (cycleGamma_pos h) (cycleLambdaOdd_pos h)).ne'
  have hraw := hasDerivAt_map_zeroScale_first β aE aO φ
    (evenState (aE 0) (aO 0) ν) haE haO ha0 hb0 hC hCNext
  simp only [Parameters.leadingStage_eq_original, evenToOdd h,
    evenState_feedbackCoefficient h, oddState_feedbackCoefficient h] at hraw
  have hfirst : (evenState (aE 0) (aO 0) ν).1 = cycleGamma (aE 0) (aO 0) ν := by
    rw [evenState_def, cycleState_apply]
  rw [hfirst] at hraw
  have hcoefficient :
      2 * φ (cycleGamma (aE 0) (aO 0) ν) *
          ((cycleGamma (aE 0) (aO 0) ν * (aO 0 + ν)) / aO 0 -
            (cycleGamma (aE 0) (aO 0) ν * (aE 0 - ν)) / aE 0) -
          2 * cycleGamma (aE 0) (aO 0) ν / (1 + β) =
        2 * cycleGamma (aE 0) (aO 0) ν * ν * (1 / aE 0 + 1 / aO 0) *
            φ (cycleGamma (aE 0) (aO 0) ν) -
          2 * cycleGamma (aE 0) (aO 0) ν / (1 + β) := by
    field_simp [ha0, hb0]
    ring
  exact hraw.congr_deriv hcoefficient

/-- eq:polar-slow-drift (actual source differential). Throughout one fixed
neighborhood of the selected equilibrium, the inverse-index derivative of the
actual normalized cycle on its even reference curve is the exact linear restoring drift. -/
theorem hasDerivAt_sourceMap_first_eventually (p : Parameters) (hβ : 0 < p.beta) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      HasDerivAt (fun v ↦ (Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor
        p.feedbackPotential 0 v (p.evenReference γ)).1)
        (-2 * (γ - p.gammaStar) / (1 + p.beta)) 0 := by
  filter_upwards [p.referenceFamily_eventually] with γ hfamily
  have ha0 : p.evenAngleFactor 0 ≠ 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  have hb0 : p.oddAngleFactor 0 ≠ 0 := by
    rw [p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos.ne'
  have hdomain : CycleDomain (p.evenAngleFactor 0) (p.oddAngleFactor 0)
      (p.inverseParameter γ) := by
    simpa only [p.evenAngleFactor_zero hβ, p.oddAngleFactor_zero hβ] using hfamily.1
  have hraw := hasDerivAt_map_evenState_first p.beta p.evenAngleFactor p.oddAngleFactor
    p.feedbackPotential (p.inverseParameter γ) p.evenAngleFactor_analyticAt
    p.oddAngleFactor_analyticAt ha0 hb0 hdomain
  simp only [p.evenAngleFactor_zero hβ, p.oddAngleFactor_zero hβ] at hraw
  have hgamma : cycleGamma p.deltaEven p.deltaOdd (p.inverseParameter γ) = γ := by
    have hfirst := congrArg Prod.fst hfamily.2.1
    simpa only [p.evenReference_fst, evenState_def, cycleState_apply] using hfirst.symm
  have hγ : 0 < γ := by
    rw [← hgamma]
    exact cycleGamma_pos hfamily.1
  rw [hgamma, ← hfamily.2.1] at hraw
  exact hraw.congr_deriv (p.restoringDrift_eq hβ hγ.ne' hfamily.1.nu_pos.ne')

/-- Helper for eq:polar-fast-bound: jointly twice differentiable families have
uniform first-derivative bounds and quadratic Taylor remainders on a compact fiber. -/
theorem uniformSecondOrderTaylorBound {Θ F : Type*}
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Θ → (ℝ × ℝ) → F} {K : Set Θ} (hK : IsCompact K)
    (hjoint : ∀ θ ∈ K, ContDiffAt ℝ 2 (Function.uncurry f) (θ, 0)) :
    ∃ B ≥ 0, ∃ C > 0, ∃ ε > 0, ∀ θ ∈ K,
      ‖fderiv ℝ (f θ) 0‖ ≤ B ∧ ∀ h : ℝ × ℝ, ‖h‖ < ε →
        ‖f θ h - f θ 0 - fderiv ℝ (f θ) 0 h‖ ≤ C * ‖h‖ ^ 2 := by
  let J : Θ → FiniteTaylorJet ℝ (ℝ × ℝ) F 2 :=
    fun θ ↦ FiniteTaylorJet.ofFunction ℝ 2 (f θ) 0
  have hJ : FiniteTaylorJet.IsUniformOn f J 0 K :=
    FiniteTaylorJet.isUniformOn_of_contDiffAt 2 f 0 K hK hjoint
  obtain ⟨B, hB, hfirst⟩ := hJ.boundedCoeff (1 : Fin 3)
  obtain ⟨D, hD, hsecond⟩ := hJ.boundedCoeff (2 : Fin 3)
  obtain ⟨ε, hε, hrem⟩ := FiniteTaylorJet.IsUniformRemainderOn.bound
    (hJ.remainder 1 zero_lt_one)
  refine ⟨B, hB, D + 1, add_pos_of_nonneg_of_pos hD zero_lt_one, ε, hε, ?_⟩
  intro θ hθ
  have hdegreeZero : ((0 : Fin 3) : ℕ) = 0 := rfl
  have hdegreeOne : ((1 : Fin 3) : ℕ) = 1 := rfl
  constructor
  · have hbound := hfirst θ hθ
    dsimp only [J] at hbound
    rw [FiniteTaylorJet.coeff_ofFunction, hdegreeOne] at hbound
    norm_num [norm_smul] at hbound
    exact hbound
  · intro h hh
    have hconstant : (J θ).coeff (0 : Fin 3) (fun _ ↦ h) = f θ 0 := by
      dsimp only [J]
      rw [FiniteTaylorJet.coeff_ofFunction_apply, hdegreeZero]
      norm_num [iteratedFDeriv_zero_apply]
    have hlinear : (J θ).coeff (1 : Fin 3) (fun _ ↦ h) = fderiv ℝ (f θ) 0 h := by
      dsimp only [J]
      rw [FiniteTaylorJet.coeff_ofFunction_apply, hdegreeOne]
      norm_num [iteratedFDeriv_one_apply]
    have heval : (J θ).eval h =
        f θ 0 + fderiv ℝ (f θ) 0 h + (J θ).coeff (2 : Fin 3) (fun _ ↦ h) := by
      rw [FiniteTaylorJet.eval_eq_sum, Fin.sum_univ_three, hconstant, hlinear]
    have htop : ‖(J θ).coeff (2 : Fin 3) (fun _ ↦ h)‖ ≤ D * ‖h‖ ^ 2 := by
      calc
        ‖(J θ).coeff (2 : Fin 3) (fun _ ↦ h)‖ ≤
            ‖(J θ).coeff (2 : Fin 3)‖ * ∏ _ : Fin 2, ‖h‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ D * ∏ _ : Fin 2, ‖h‖ :=
          mul_le_mul_of_nonneg_right (hsecond θ hθ)
            (Finset.prod_nonneg fun _ _ ↦ norm_nonneg h)
        _ = D * ‖h‖ ^ 2 := by
          simp only [Finset.prod_const, Finset.card_fin]
    have hremainder : ‖(J θ).remainder (f θ) 0 h‖ ≤ ‖h‖ ^ 2 := by
      simpa only [Real.rpow_natCast, one_mul] using hrem θ hθ h hh
    have hvalue : f θ h - f θ 0 - fderiv ℝ (f θ) 0 h =
        (J θ).remainder (f θ) 0 h + (J θ).coeff (2 : Fin 3) (fun _ ↦ h) := by
      rw [FiniteTaylorJet.remainder_def, zero_add, heval]
      abel
    rw [hvalue]
    calc
      ‖(J θ).remainder (f θ) 0 h + (J θ).coeff (2 : Fin 3) (fun _ ↦ h)‖ ≤
          ‖(J θ).remainder (f θ) 0 h‖ + ‖(J θ).coeff (2 : Fin 3) (fun _ ↦ h)‖ :=
        norm_add_le _ _
      _ ≤ ‖h‖ ^ 2 + D * ‖h‖ ^ 2 := add_le_add hremainder htop
      _ = (D + 1) * ‖h‖ ^ 2 := by
        ring

/-- Helper for eq:polar-fast-bound: a linear map on the two independent small
parameters is determined by its scale and inverse-index directions. -/
theorem linearMap_pair_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ℝ × ℝ) →L[ℝ] F) (t v : ℝ) :
    L (t, v) = t • L (1, 0) + v • L (0, 1) := by
  have hpair : (t, v) = t • ((1, 0) : ℝ × ℝ) + v • ((0, 1) : ℝ × ℝ) := by
    apply Prod.ext
    · simp
    · simp
  rw [hpair, map_add, map_smul, map_smul]

/-- Helper for eq:polar-fast-bound: evenness removes the scale direction of
the Fréchet derivative at the origin of the independent parameter plane. -/
theorem fderiv_scale_eq_zero_of_even {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (ℝ × ℝ) → F}
    (hf : DifferentiableAt ℝ f 0) (heven : ∀ t : ℝ, f (-t, 0) = f (t, 0)) :
    fderiv ℝ f 0 (1, 0) = 0 := by
  have hpath := (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 (0 : ℝ))
  have hderiv := hf.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ (t, 0)) 0 hpath
  have hzero : deriv (fun t : ℝ ↦ f (t, 0)) 0 = 0 :=
    Normalized.deriv_zero_of_even heven
  exact hderiv.deriv.symm.trans hzero

/-- Helper for eq:polar-fast-bound: the parameter-plane norm squared is bounded
by the sum of the squares of its two coordinates. -/
theorem pair_norm_sq_le (t v : ℝ) : ‖((t, v) : ℝ × ℝ)‖ ^ 2 ≤ t ^ 2 + v ^ 2 := by
  rw [Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases htv : |t| ≤ |v|
  · rw [max_eq_right htv, sq_abs]
    linarith [sq_nonneg t]
  · rw [max_eq_left (le_of_not_ge htv), sq_abs]
    linarith [sq_nonneg v]

/-- Helper for eq:polar-fast-bound: a compact family with vanishing scale
differential has parameter variation bounded by `|v| + t²`. -/
theorem uniformParameterPerturbation {Θ F : Type*}
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Θ → (ℝ × ℝ) → F} {K : Set Θ} (hK : IsCompact K)
    (hjoint : ∀ θ ∈ K, ContDiffAt ℝ 2 (Function.uncurry f) (θ, 0))
    (hscale : ∀ θ ∈ K, fderiv ℝ (f θ) 0 (1, 0) = 0) :
    ∃ C > 0, ∃ ε > 0, ∀ θ ∈ K, ∀ t v : ℝ, ‖(t, v)‖ < ε →
      ‖f θ (t, v) - f θ 0‖ ≤ C * (|v| + t ^ 2) := by
  obtain ⟨B, hB, D, hD, ε, hε, hbound⟩ := uniformSecondOrderTaylorBound hK hjoint
  refine ⟨B + D, add_pos_of_nonneg_of_pos hB hD,
    min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro θ hθ t v htv
  have hsmall : ‖(t, v)‖ < ε := htv.trans_le (min_le_left ε 1)
  have hvOne : |v| ≤ 1 := by
    have hnorm : |v| ≤ ‖((t, v) : ℝ × ℝ)‖ := by
      simpa only [Prod.norm_mk, Real.norm_eq_abs] using le_max_right |t| |v|
    exact hnorm.trans (htv.le.trans (min_le_right ε 1))
  have hvSquare : v ^ 2 ≤ |v| := by
    nlinarith [abs_nonneg v, sq_abs v]
  have hlinear : ‖fderiv ℝ (f θ) 0 (t, v)‖ ≤ B * |v| := by
    rw [linearMap_pair_apply, hscale θ hθ, smul_zero, zero_add, norm_smul,
      Real.norm_eq_abs]
    have hunit := (fderiv ℝ (f θ) 0).le_opNorm ((0, 1) : ℝ × ℝ)
    have hunitNorm : ‖((0, 1) : ℝ × ℝ)‖ = 1 := by
      simp
    rw [hunitNorm, mul_one] at hunit
    have hproduct := mul_le_mul_of_nonneg_left (hunit.trans (hbound θ hθ).1)
      (abs_nonneg v)
    nlinarith
  have hrem := (hbound θ hθ).2 (t, v) hsmall
  have hnormSquare : ‖((t, v) : ℝ × ℝ)‖ ^ 2 ≤ t ^ 2 + |v| := by
    linarith [pair_norm_sq_le t v]
  have hremBound :
      ‖f θ (t, v) - f θ 0 - fderiv ℝ (f θ) 0 (t, v)‖ ≤ D * (t ^ 2 + |v|) :=
    hrem.trans (mul_le_mul_of_nonneg_left hnormSquare hD.le)
  have htriangle : ‖f θ (t, v) - f θ 0‖ ≤
      ‖f θ (t, v) - f θ 0 - fderiv ℝ (f θ) 0 (t, v)‖ +
        ‖fderiv ℝ (f θ) 0 (t, v)‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (f θ (t, v) - f θ 0 - fderiv ℝ (f θ) 0 (t, v))
        (fderiv ℝ (f θ) 0 (t, v))
  nlinarith [mul_nonneg hB (sq_nonneg t)]

/-- Helper for eq:polar-slow-drift: prescribed first differentials in the two
independent parameter directions give a compact uniform quadratic residual. -/
theorem uniformScalarTaylorBound {Θ : Type*}
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    {f : Θ → (ℝ × ℝ) → ℝ} {g : Θ → ℝ} {K : Set Θ} (hK : IsCompact K)
    (hjoint : ∀ θ ∈ K, ContDiffAt ℝ 2 (Function.uncurry f) (θ, 0))
    (hscale : ∀ θ ∈ K, fderiv ℝ (f θ) 0 (1, 0) = 0)
    (hindex : ∀ θ ∈ K, fderiv ℝ (f θ) 0 (0, 1) = g θ) :
    ∃ C > 0, ∃ ε > 0, ∀ θ ∈ K, ∀ t v : ℝ, ‖(t, v)‖ < ε →
      |f θ (t, v) - f θ 0 - v * g θ| ≤ C * (t ^ 2 + v ^ 2) := by
  obtain ⟨B, hB, C, hC, ε, hε, hbound⟩ := uniformSecondOrderTaylorBound hK hjoint
  refine ⟨C, hC, ε, hε, ?_⟩
  intro θ hθ t v htv
  have hlinear : fderiv ℝ (f θ) 0 (t, v) = v * g θ := by
    rw [linearMap_pair_apply, hscale θ hθ, hindex θ hθ, smul_zero, zero_add, smul_eq_mul]
  have hrem := (hbound θ hθ).2 (t, v) htv
  rw [hlinear, Real.norm_eq_abs] at hrem
  exact hrem.trans (mul_le_mul_of_nonneg_left (pair_norm_sq_le t v) hC.le)

/-- Helper for lem:polar-continuation: the actual source cycle viewed as a family
in its independent scale and inverse-index parameters. -/
def parameterMap (p : Parameters) (x : ℝ × ℝ × ℝ) (h : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential h.1 h.2 x

/-- Helper for lem:polar-continuation: the independent-parameter map is exactly
the actual normalized source cycle, with no trajectory assumptions. -/
theorem parameterMap_apply (p : Parameters) (x : ℝ × ℝ × ℝ) (h : ℝ × ℝ) :
    parameterMap p x h =
      Normalized.map p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
        h.1 h.2 x := by
  rfl

/-- Helper for eq:polar-fast-bound: the actual independent-parameter map is even
in its scale coordinate at every state and inverse index. -/
theorem parameterMap_neg_scale (p : Parameters) (x : ℝ × ℝ × ℝ) (t v : ℝ) :
    parameterMap p x (-t, v) = parameterMap p x (t, v) := by
  exact Normalized.map_neg p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential t v x

/-- Helper for eq:polar-slow-drift: the limiting source map preserves the first
diagonal coordinate at every state, including states off the reference family. -/
theorem parameterMap_zero_first (p : Parameters) (x : ℝ × ℝ × ℝ) :
    (parameterMap p x 0).1 = x.1 := by
  exact Normalized.map_zero_first p.beta p.evenAngleFactor p.oddAngleFactor p.feedbackPotential x

/-- Helper for eq:polar-fast-bound: the actual source cycle is jointly analytic
at its initial reference state and zero independent parameters. -/
theorem parameterMap_joint_analyticAt (p : Parameters) (hβ : 0 < p.beta) :
    AnalyticAt ℝ (Function.uncurry (parameterMap p)) (p.initialState, 0) := by
  have ha0 : p.evenAngleFactor 0 ≠ 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  have hb0 : p.oddAngleFactor 0 ≠ 0 := by
    rw [p.oddAngleFactor_zero hβ]
    exact p.deltaOdd_pos.ne'
  have hfirst : p.initialState.1 = p.gammaStar := by
    rw [p.initialState_def, cycleState_apply]
  have hφ : AnalyticAt ℝ p.feedbackPotential p.initialState.1 := by
    rw [hfirst]
    exact p.feedbackPotential_analyticAt hβ
  have hnext : Normalized.leadingStage (p.evenAngleFactor 0) p.initialState =
      p.oddReference p.gammaStar := by
    rw [p.evenAngleFactor_zero hβ, ← p.evenReference_gammaStar]
    exact p.referenceCycle_eventually.self_of_nhds.1
  have hCNext : (Normalized.leadingStage (p.evenAngleFactor 0) p.initialState).2.1 ≠ 0 := by
    rw [hnext]
    exact p.initial_reference_positive.2.ne'
  have hmap := Normalized.map_analyticAt p.beta p.evenAngleFactor p.oddAngleFactor
    p.feedbackPotential p.initialState p.evenAngleFactor_analyticAt p.oddAngleFactor_analyticAt
    hφ ha0 hb0 p.initial_reference_positive.1.ne' hCNext
  have hswap : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (z.2, z.1)) (p.initialState, 0) :=
    analyticAt_snd.prod analyticAt_fst
  exact hmap.comp_of_eq hswap rfl

/-- Helper for eq:polar-fast-bound: on one fixed closed
state neighborhood of the selected initial reference, the actual source cycle
differs from its limiting cycle by at most `C * (|v| + t²)`. -/
theorem exists_sourceMap_parameter_bound (p : Parameters) (hβ : 0 < p.beta) :
    ∃ r > 0, ∃ C > 0, ∃ ε > 0, ∀ x : ℝ × ℝ × ℝ,
      ‖x - p.initialState‖ ≤ r → ∀ t v : ℝ, ‖(t, v)‖ < ε →
        ‖parameterMap p x (t, v) - parameterMap p x 0‖ ≤ C * (|v| + t ^ 2) := by
  have hfinite : (2 : ℕ∞ω) ≠ ∞ := by
    norm_num
  have hnonzero : (2 : ℕ∞ω) ≠ 0 := by
    norm_num
  have hbase : ContDiffAt ℝ 2 (Function.uncurry (parameterMap p)) (p.initialState, 0) :=
    (parameterMap_joint_analyticAt p hβ).contDiffAt
  have hinput : Tendsto (fun x : ℝ × ℝ × ℝ ↦ (x, (0 : ℝ × ℝ)))
      (𝓝 p.initialState) (𝓝 (p.initialState, 0)) :=
    continuousAt_id.prodMk continuousAt_const
  have hnear := hinput.eventually (hbase.eventually hfinite)
  obtain ⟨δ, hδ, hregular⟩ := Metric.eventually_nhds_iff.mp hnear
  have hK : IsCompact (Metric.closedBall p.initialState (δ / 2)) :=
    isCompact_closedBall p.initialState (δ / 2)
  have hjoint : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      ContDiffAt ℝ 2 (Function.uncurry (parameterMap p)) (x, 0) := by
    intro x hx
    exact hregular ((Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hδ))
  have hscale : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      fderiv ℝ (parameterMap p x) 0 (1, 0) = 0 := by
    intro x hx
    have hpath : ContDiffAt ℝ 2 (fun h : ℝ × ℝ ↦ (x, h)) 0 :=
      contDiffAt_const.prodMk contDiffAt_id
    have hslice : DifferentiableAt ℝ (parameterMap p x) 0 :=
      ((hjoint x hx).comp 0 hpath).differentiableAt hnonzero
    exact fderiv_scale_eq_zero_of_even hslice (fun t ↦ parameterMap_neg_scale p x t 0)
  obtain ⟨C, hC, ε, hε, hbound⟩ := uniformParameterPerturbation hK hjoint hscale
  refine ⟨δ / 2, half_pos hδ, C, hC, ε, hε, ?_⟩
  intro x hx t v htv
  have hxK : x ∈ Metric.closedBall p.initialState (δ / 2) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  exact hbound x hxK t v htv

/-- Helper for eq:polar-slow-drift: the inverse-index coefficient of the first
coordinate, defined using the joint source derivative. -/
def inverseIndexCoefficient (p : Parameters) (x : ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1)
    (x, 0) (0, (0, 1))

/-- Helper for eq:polar-slow-drift: the joint inverse-index coefficient equals
the derivative of the fixed-state independent-parameter map. -/
theorem inverseIndexCoefficient_eq_slice (p : Parameters) (x : ℝ × ℝ × ℝ)
    (hreg : DifferentiableAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1) (x, 0)) :
    inverseIndexCoefficient p x =
      fderiv ℝ (fun h : ℝ × ℝ ↦ (parameterMap p x h).1) 0 (0, 1) := by
  have hpath : HasFDerivAt (fun h : ℝ × ℝ ↦ (x, h))
      (ContinuousLinearMap.inr ℝ (ℝ × ℝ × ℝ) (ℝ × ℝ)) 0 :=
    hasFDerivAt_prodMk_right x 0
  have hderiv := hreg.hasFDerivAt.comp 0 hpath
  have hfderiv := hderiv.fderiv
  simp only [Function.comp_def] at hfderiv
  rw [hfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rfl

/-- Helper for eq:polar-slow-drift: the inverse-index coefficient is analytic
as a function of state near the selected initial reference. -/
theorem inverseIndexCoefficient_analyticAt (p : Parameters) (hβ : 0 < p.beta) :
    AnalyticAt ℝ (inverseIndexCoefficient p) p.initialState := by
  have hscalar : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1)
      (p.initialState, 0) :=
    analyticAt_fst.comp (parameterMap_joint_analyticAt p hβ)
  have hpath : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ (x, (0 : ℝ × ℝ)))
      p.initialState := analyticAt_id.prod analyticAt_const
  have hderiv := hscalar.fderiv.comp_of_eq hpath rfl
  exact ((ContinuousLinearMap.apply ℝ ℝ
    ((0, ((0, 1) : ℝ × ℝ)) : (ℝ × ℝ × ℝ) × (ℝ × ℝ))).analyticAt _).comp hderiv

/-- Helper for eq:polar-slow-drift: any derivative calculation on the zero-scale
inverse-index slice identifies the joint coefficient. -/
theorem inverseIndexCoefficient_eq_of_hasDerivAt (p : Parameters)
    (x : ℝ × ℝ × ℝ) {d : ℝ}
    (hreg : DifferentiableAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1) (x, 0))
    (hindex : HasDerivAt (fun v : ℝ ↦ (parameterMap p x (0, v)).1) d 0) :
    inverseIndexCoefficient p x = d := by
  have hpath := (hasDerivAt_const 0 x).prodMk
    ((hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have hderiv := hreg.hasFDerivAt.comp_hasDerivAt
    (f := fun v : ℝ ↦ (x, ((0, v) : ℝ × ℝ))) 0 hpath
  exact hderiv.unique hindex

/-- Helper for eq:polar-slow-drift: the inverse-index coefficient on the actual
reference curve is exactly the source restoring drift on a fixed neighborhood. -/
theorem inverseIndexCoefficient_reference_eventually (p : Parameters) (hβ : 0 < p.beta) :
    ∀ᶠ γ in 𝓝 p.gammaStar,
      inverseIndexCoefficient p (p.evenReference γ) =
        -2 * (γ - p.gammaStar) / (1 + p.beta) := by
  have hscalar : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1)
      (p.initialState, 0) :=
    analyticAt_fst.comp (parameterMap_joint_analyticAt p hβ)
  have hfinite : (1 : ℕ∞ω) ≠ ∞ := by
    norm_num
  have hnonzero : (1 : ℕ∞ω) ≠ 0 := by
    norm_num
  have hbase : ContDiffAt ℝ 1
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (parameterMap p z.1 z.2).1)
      (p.initialState, 0) := hscalar.contDiffAt
  have hinput : Tendsto (fun γ : ℝ ↦ (p.evenReference γ, (0 : ℝ × ℝ)))
      (𝓝 p.gammaStar) (𝓝 (p.initialState, 0)) := by
    have hconstant : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ × ℝ)) p.gammaStar :=
      continuousAt_const
    simpa only [p.evenReference_gammaStar] using
      (p.evenReference_analyticAt.continuousAt.prodMk hconstant).tendsto
  have hregular := hinput.eventually (hbase.eventually hfinite)
  filter_upwards [hregular, hasDerivAt_sourceMap_first_eventually p hβ] with γ hreg hderiv
  exact inverseIndexCoefficient_eq_of_hasDerivAt p (p.evenReference γ)
    (hreg.differentiableAt hnonzero) hderiv

/-- Helper for eq:polar-fast-bound: throughout one fixed closed state neighborhood,
the first cycle coordinate has a quadratic residual after its inverse-index term. -/
theorem exists_sourceMap_scalarTaylor_bound (p : Parameters) (hβ : 0 < p.beta) :
    ∃ r > 0, ∃ C > 0, ∃ ε > 0, ∀ x : ℝ × ℝ × ℝ,
      ‖x - p.initialState‖ ≤ r → ∀ t v : ℝ, ‖(t, v)‖ < ε →
        |(parameterMap p x (t, v)).1 - x.1 - v * inverseIndexCoefficient p x| ≤
          C * (t ^ 2 + v ^ 2) := by
  let f : (ℝ × ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun x h ↦ (parameterMap p x h).1
  have hfinite : (2 : ℕ∞ω) ≠ ∞ := by
    norm_num
  have hnonzero : (2 : ℕ∞ω) ≠ 0 := by
    norm_num
  have hscalar : AnalyticAt ℝ (Function.uncurry f) (p.initialState, 0) :=
    analyticAt_fst.comp (parameterMap_joint_analyticAt p hβ)
  have hbase : ContDiffAt ℝ 2 (Function.uncurry f) (p.initialState, 0) := hscalar.contDiffAt
  have hinput : Tendsto (fun x : ℝ × ℝ × ℝ ↦ (x, (0 : ℝ × ℝ)))
      (𝓝 p.initialState) (𝓝 (p.initialState, 0)) :=
    continuousAt_id.prodMk continuousAt_const
  obtain ⟨δ, hδ, hregular⟩ :=
    Metric.eventually_nhds_iff.mp (hinput.eventually (hbase.eventually hfinite))
  have hK : IsCompact (Metric.closedBall p.initialState (δ / 2)) :=
    isCompact_closedBall p.initialState (δ / 2)
  have hjoint : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      ContDiffAt ℝ 2 (Function.uncurry f) (x, 0) := by
    intro x hx
    exact hregular ((Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hδ))
  have hscale : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      fderiv ℝ (f x) 0 (1, 0) = 0 := by
    intro x hx
    have hpath : ContDiffAt ℝ 2 (fun h : ℝ × ℝ ↦ (x, h)) 0 :=
      contDiffAt_const.prodMk contDiffAt_id
    have hslice : DifferentiableAt ℝ (f x) 0 :=
      ((hjoint x hx).comp 0 hpath).differentiableAt hnonzero
    exact fderiv_scale_eq_zero_of_even hslice
      (fun t ↦ congrArg Prod.fst (parameterMap_neg_scale p x t 0))
  have hindex : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      fderiv ℝ (f x) 0 (0, 1) = inverseIndexCoefficient p x := by
    intro x hx
    exact (inverseIndexCoefficient_eq_slice p x
      ((hjoint x hx).differentiableAt hnonzero)).symm
  obtain ⟨C, hC, ε, hε, hbound⟩ := uniformScalarTaylorBound hK hjoint hscale hindex
  refine ⟨δ / 2, half_pos hδ, C, hC, ε, hε, ?_⟩
  intro x hx t v htv
  have hxK : x ∈ Metric.closedBall p.initialState (δ / 2) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  simpa only [f, parameterMap_zero_first] using hbound x hxK t v htv

/-- Helper for eq:polar-fast-bound: the inverse-index coefficient is uniformly
Lipschitz on one fixed closed state neighborhood of the selected reference. -/
theorem exists_inverseIndexCoefficient_lipschitz (p : Parameters) (hβ : 0 < p.beta) :
    ∃ r > 0, ∃ C > 0, ∀ x y : ℝ × ℝ × ℝ,
      ‖x - p.initialState‖ ≤ r → ‖y - p.initialState‖ ≤ r →
        |inverseIndexCoefficient p x - inverseIndexCoefficient p y| ≤ C * ‖x - y‖ := by
  obtain ⟨L, S, hS, hLip⟩ :=
    (inverseIndexCoefficient_analyticAt p hβ).hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.mp hS
  refine ⟨δ / 2, half_pos hδ, (L : ℝ) + 1, ?_, ?_⟩
  · positivity
  · intro x y hx hy
    have hxS : x ∈ S := by
      apply hmem
      rw [dist_eq_norm]
      exact hx.trans_lt (half_lt_self hδ)
    have hyS : y ∈ S := by
      apply hmem
      rw [dist_eq_norm]
      exact hy.trans_lt (half_lt_self hδ)
    have hbound := hLip.norm_sub_le hxS hyS
    rw [Real.norm_eq_abs] at hbound
    nlinarith [norm_nonneg (x - y)]

/-- Helper for eq:polar-fast-bound: near the selected reference
curve, the first coordinate has the exact restoring drift plus a remainder
bounded by `C * (|v| * ‖x - evenReference γ‖ + v² + t²)`. The absence of an
unmultiplied fast-state error follows from exact zero-parameter preservation. -/
theorem exists_sourceMap_scalar_bound (p : Parameters) (hβ : 0 < p.beta) :
    ∃ rγ > 0, ∃ ru > 0, ∃ C > 0, ∃ ε > 0, ∀ γ : ℝ,
      |γ - p.gammaStar| ≤ rγ → ∀ x : ℝ × ℝ × ℝ, x.1 = γ →
        ‖x - p.evenReference γ‖ ≤ ru → ∀ t v : ℝ, ‖(t, v)‖ < ε →
          |(parameterMap p x (t, v)).1 - γ -
              v * (-2 * (γ - p.gammaStar) / (1 + p.beta))| ≤
            C * (|v| * ‖x - p.evenReference γ‖ + v ^ 2 + t ^ 2) := by
  obtain ⟨rT, hrT, CT, hCT, ε, hε, hTaylor⟩ := exists_sourceMap_scalarTaylor_bound p hβ
  obtain ⟨rL, hrL, L, hL, hLip⟩ := exists_inverseIndexCoefficient_lipschitz p hβ
  let R := min rT rL
  have hR : 0 < R := lt_min hrT hrL
  have hrefNorm : Tendsto (fun γ : ℝ ↦ ‖p.evenReference γ - p.initialState‖)
      (𝓝 p.gammaStar) (𝓝 0) := by
    simpa only [p.evenReference_gammaStar, sub_self, norm_zero] using
      (p.evenReference_analyticAt.continuousAt.sub_const p.initialState).norm
  have hnear : ∀ᶠ γ in 𝓝 p.gammaStar,
      inverseIndexCoefficient p (p.evenReference γ) =
          -2 * (γ - p.gammaStar) / (1 + p.beta) ∧
        ‖p.evenReference γ - p.initialState‖ < R / 2 := by
    filter_upwards [inverseIndexCoefficient_reference_eventually p hβ,
      hrefNorm.eventually (Iio_mem_nhds (half_pos hR))] with γ hcoefficient href
    exact ⟨hcoefficient, href⟩
  obtain ⟨δ, hδ, hnearBound⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨δ / 2, half_pos hδ, R / 2, half_pos hR,
    CT + L, add_pos hCT hL, ε, hε, ?_⟩
  intro γ hγ x hxFirst hxRef t v htv
  have hγnear : dist γ p.gammaStar < δ := by
    rw [Real.dist_eq]
    exact hγ.trans_lt (half_lt_self hδ)
  obtain ⟨hcoefficient, href⟩ := hnearBound hγnear
  have hxInitial : ‖x - p.initialState‖ ≤ R := by
    calc
      ‖x - p.initialState‖ ≤ ‖x - p.evenReference γ‖ +
          ‖p.evenReference γ - p.initialState‖ :=
        norm_sub_le_norm_sub_add_norm_sub x (p.evenReference γ) p.initialState
      _ ≤ R / 2 + R / 2 := add_le_add hxRef href.le
      _ = R := by
        ring
  have hRT : R ≤ rT := min_le_left rT rL
  have hRL : R ≤ rL := min_le_right rT rL
  have hrefL : ‖p.evenReference γ - p.initialState‖ ≤ rL := by
    linarith
  have herror := hTaylor x (hxInitial.trans hRT) t v htv
  have hvariation := hLip x (p.evenReference γ) (hxInitial.trans hRL) hrefL
  have hidentity : (parameterMap p x (t, v)).1 - γ -
        v * (-2 * (γ - p.gammaStar) / (1 + p.beta)) =
      ((parameterMap p x (t, v)).1 - x.1 - v * inverseIndexCoefficient p x) +
        v * (inverseIndexCoefficient p x - inverseIndexCoefficient p (p.evenReference γ)) := by
    rw [hxFirst, hcoefficient]
    ring
  have hproduct :
      |v * (inverseIndexCoefficient p x - inverseIndexCoefficient p (p.evenReference γ))| ≤
        |v| * (L * ‖x - p.evenReference γ‖) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hvariation (abs_nonneg v)
  rw [hidentity]
  calc
    |((parameterMap p x (t, v)).1 - x.1 - v * inverseIndexCoefficient p x) +
        v * (inverseIndexCoefficient p x - inverseIndexCoefficient p (p.evenReference γ))| ≤
        |(parameterMap p x (t, v)).1 - x.1 - v * inverseIndexCoefficient p x| +
          |v * (inverseIndexCoefficient p x - inverseIndexCoefficient p (p.evenReference γ))| :=
      abs_add_le _ _
    _ ≤ CT * (t ^ 2 + v ^ 2) + |v| * (L * ‖x - p.evenReference γ‖) :=
      add_le_add herror hproduct
    _ ≤ (CT + L) * (|v| * ‖x - p.evenReference γ‖ + v ^ 2 + t ^ 2) := by
      have hcrossT := mul_nonneg hCT.le
        (mul_nonneg (abs_nonneg v) (norm_nonneg (x - p.evenReference γ)))
      have hcrossL := mul_nonneg hL.le (add_nonneg (sq_nonneg t) (sq_nonneg v))
      nlinarith

/-- Helper for lem:polar-continuation: the actual first source stage has
uniform `|v| + t²` parameter variation on one fixed closed state neighborhood.
Its shared feedback remains evaluated at the original even boundary state. -/
theorem exists_evenStage_parameter_bound (p : Parameters) (hβ : 0 < p.beta) :
    ∃ r > 0, ∃ C > 0, ∃ ε > 0, ∀ x : ℝ × ℝ × ℝ,
      ‖x - p.initialState‖ ≤ r → ∀ t v : ℝ, ‖(t, v)‖ < ε →
        ‖Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
            0 t v x x -
          Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
            0 0 0 x x‖ ≤ C * (|v| + t ^ 2) := by
  let f : (ℝ × ℝ × ℝ) → (ℝ × ℝ) → ℝ × ℝ × ℝ := fun x h ↦
    Normalized.cycleStage p.evenAngleFactor p.oddAngleFactor p.feedbackPotential
      0 h.1 h.2 x x
  have hfinite : (2 : ℕ∞ω) ≠ ∞ := by
    norm_num
  have hnonzero : (2 : ℕ∞ω) ≠ 0 := by
    norm_num
  have ha0 : p.evenAngleFactor 0 ≠ 0 := by
    rw [p.evenAngleFactor_zero hβ]
    exact p.deltaEven_pos.ne'
  have hfirst : p.initialState.1 = p.gammaStar := by
    rw [p.initialState_def, cycleState_apply]
  have hφ : AnalyticAt ℝ p.feedbackPotential p.initialState.1 := by
    rw [hfirst]
    exact p.feedbackPotential_analyticAt hβ
  have hmap := Normalized.evenStage_analyticAt p.evenAngleFactor p.oddAngleFactor
    p.feedbackPotential p.initialState p.evenAngleFactor_analyticAt hφ ha0
    p.initial_reference_positive.1.ne'
  have hswap : AnalyticAt ℝ
      (fun z : (ℝ × ℝ × ℝ) × (ℝ × ℝ) ↦ (z.2, z.1)) (p.initialState, 0) :=
    analyticAt_snd.prod analyticAt_fst
  have hbase : ContDiffAt ℝ 2 (Function.uncurry f) (p.initialState, 0) :=
    (hmap.comp_of_eq hswap rfl).contDiffAt
  have hinput : Tendsto (fun x : ℝ × ℝ × ℝ ↦ (x, (0 : ℝ × ℝ)))
      (𝓝 p.initialState) (𝓝 (p.initialState, 0)) :=
    continuousAt_id.prodMk continuousAt_const
  obtain ⟨δ, hδ, hregular⟩ :=
    Metric.eventually_nhds_iff.mp (hinput.eventually (hbase.eventually hfinite))
  have hK : IsCompact (Metric.closedBall p.initialState (δ / 2)) :=
    isCompact_closedBall p.initialState (δ / 2)
  have hjoint : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      ContDiffAt ℝ 2 (Function.uncurry f) (x, 0) := by
    intro x hx
    exact hregular ((Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hδ))
  have hscale : ∀ x ∈ Metric.closedBall p.initialState (δ / 2),
      fderiv ℝ (f x) 0 (1, 0) = 0 := by
    intro x hx
    have hpath : ContDiffAt ℝ 2 (fun h : ℝ × ℝ ↦ (x, h)) 0 :=
      contDiffAt_const.prodMk contDiffAt_id
    have hslice : DifferentiableAt ℝ (f x) 0 :=
      ((hjoint x hx).comp 0 hpath).differentiableAt hnonzero
    have heven : ∀ t : ℝ, f x (-t, 0) = f x (t, 0) := by
      intro t
      simp only [f, Normalized.cycleStage_even, Normalized.stage_neg]
    exact fderiv_scale_eq_zero_of_even hslice heven
  obtain ⟨C, hC, ε, hε, hbound⟩ := uniformParameterPerturbation hK hjoint hscale
  refine ⟨δ / 2, half_pos hδ, C, hC, ε, hε, ?_⟩
  intro x hx t v htv
  have hxK : x ∈ Metric.closedBall p.initialState (δ / 2) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  exact hbound x hxK t v htv

end DFP.Polar.General.Estimates

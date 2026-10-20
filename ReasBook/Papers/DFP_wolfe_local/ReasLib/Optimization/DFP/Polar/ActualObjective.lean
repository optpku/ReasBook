module

public import ReasLib.Optimization.DFP.Polar.InterpolationSum
public import ReasLib.Optimization.DFP.Polar.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.PointGeometry
public import ReasLib.Analysis.Convex.HessianPerturbation.Bounds

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators Asymptotics

namespace DFP.Polar.ActualObjective

/-- Helper for eq:polar-corrections: the prescribed real polar direction has unit norm. -/
theorem norm_polarUnit (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  have hnorm := EuclideanSpace.real_norm_sq_eq (polarUnit θ)
  simp only [Fin.sum_univ_two, polarUnit_apply_zero, polarUnit_apply_one] at hnorm
  nlinarith [Real.sin_sq_add_cos_sq θ, norm_nonneg (polarUnit θ)]

/-- Helper for eq:polar-corrections: a nonnegative original radius is exactly the point norm. -/
theorem norm_point (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.point k‖ = p.radius k := by
  rw [Parameters.point_def, norm_smul, norm_polarUnit, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_one]

/-- Helper for eq:polar-corrections: the actual coefficient is the radial multiplier
defect times the original point, with no change to the interpolation data. -/
theorem polarCoefficient_eq_smul (p : Parameters) (k : ℕ) :
    InterpolationSum.polarCoefficient p k = (p.zeta k - 1) • p.point k := by
  rw [InterpolationSum.polarCoefficient_apply, Parameters.gradient_def, sub_smul, one_smul]

/-- Helper for eq:polar-corrections: every actual even affine correction is zero. -/
theorem polarCoefficient_even (p : Parameters) (j : ℕ) :
    InterpolationSum.polarCoefficient p (2 * j) = 0 := by
  rw [polarCoefficient_eq_smul, Parameters.zeta_even, sub_self, zero_smul]

/-- Helper for eq:polar-corrections: the actual odd correction has exactly the source formula. -/
theorem polarCoefficient_odd (p : Parameters) (j : ℕ) :
    InterpolationSum.polarCoefficient p (2 * j + 1) =
      (p.zeta (2 * j + 1) - 1) • p.point (2 * j + 1) := by
  exact polarCoefficient_eq_smul p _

/-- Helper for eq:polar-corrections: the true cycle amplitude is the first normalized
state coordinate, as used in the cubic feedback. -/
theorem amplitude_eq_normalized (p : Parameters) (j : ℕ) :
    p.amplitude j = (p.normalizedEvenState j).1 := by
  rw [Parameters.amplitude_def, Parameters.amplitudeOf_def, Parameters.normalizedEvenState_apply]

/-- Helper for eq:polar-corrections: the exact odd multiplier uses the original
cubic exponential feedback at the actual amplitude. -/
theorem zeta_odd_eq_exp (p : Parameters) (j : ℕ) :
    p.zeta (2 * j + 1) =
      Real.exp (-(p.feedbackRate * (p.kStar / p.amplitude j) ^ 2) * p.scale j ^ 3) := by
  rw [Parameters.zeta_odd, Parameters.oddMultiplierOf_def, Parameters.amplitude_def]
  congr 1
  ring

/-- Helper for eq:polar-corrections: a nonnegative cubic feedback exponent produces
a multiplier defect between zero and the exponent. -/
theorem exp_neg_defect_bounds {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1 - Real.exp (-u) ∧ 1 - Real.exp (-u) ≤ u := by
  have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hlower := Real.add_one_le_exp (-u)
  constructor
  · linarith
  · linarith

/-- Helper for eq:polar-corrections: the rational cubic feedback coefficient is
locally Lipschitz at its nonzero limiting amplitude. -/
theorem feedbackCoefficient_local_bound (L K : ℝ) (hK : K ≠ 0) :
    ∃ B > 0, ∃ δ > 0, ∀ A : ℝ, |A - K| < δ →
      |L * (K / A) ^ 2 - L| ≤ B * |A - K| := by
  have hdiff : DifferentiableAt ℝ (fun A : ℝ ↦ L * (K / A) ^ 2) K := by
    fun_prop
  have hbig : (fun A : ℝ ↦ L * (K / A) ^ 2 - L) =O[𝓝 K] (fun A ↦ A - K) := by
    simpa only [div_self hK, one_pow, mul_one] using hdiff.isBigO_sub
  obtain ⟨B, hB, hbound⟩ := hbig.exists_pos
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨B, hB, δ, hδ, ?_⟩
  intro A hA
  have hdist : dist A K < δ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hA
  simpa only [Real.norm_eq_abs] using hδbound hdist

/-- Helper for eq:polar-corrections: Taylor's formula for the exact exponential
feedback preserves its cubic coefficient with a controlled fourth-order remainder. -/
theorem feedbackDefect_error {t q L B Q : ℝ} (ht : 0 ≤ t) (htone : t ≤ 1)
    (hq : 0 ≤ q) (hQ : q ≤ Q) (hsmall : Q * t ^ 3 ≤ 1)
    (herror : |q - L| ≤ B * t) :
    |(1 - Real.exp (-q * t ^ 3)) - L * t ^ 3| ≤ (Q ^ 2 + B) * t ^ 4 := by
  have hQt : 0 ≤ Q := hq.trans hQ
  have hpow : 0 ≤ t ^ 3 := pow_nonneg ht 3
  have hqu : 0 ≤ q * t ^ 3 := mul_nonneg hq hpow
  have hqupper : q * t ^ 3 ≤ 1 := (mul_le_mul_of_nonneg_right hQ hpow).trans hsmall
  have habs : |-q * t ^ 3| ≤ 1 := by
    rw [neg_mul, abs_neg, abs_of_nonneg hqu]
    exact hqupper
  have hexp := Real.abs_exp_sub_one_sub_id_le habs
  have hlinear : |(q - L) * t ^ 3| ≤ B * t ^ 4 := by
    rw [abs_mul, abs_of_nonneg hpow]
    calc
      |q - L| * t ^ 3 ≤ (B * t) * t ^ 3 := mul_le_mul_of_nonneg_right herror hpow
      _ = B * t ^ 4 := by ring
  have hsquare : (-q * t ^ 3) ^ 2 ≤ Q ^ 2 * t ^ 6 := by
    have hsq := pow_le_pow_left₀ hq hQ 2
    nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg ht 6)]
  have hexponents : (4 : ℕ) ≤ 6 := by norm_num
  have hpowers : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht htone hexponents
  have hquad : |1 - Real.exp (-q * t ^ 3) - q * t ^ 3| ≤ Q ^ 2 * t ^ 4 := by
    have hsign : 1 - Real.exp (-q * t ^ 3) - q * t ^ 3 =
        -(Real.exp (-q * t ^ 3) - 1 - (-q * t ^ 3)) := by ring
    rw [hsign, abs_neg]
    exact hexp.trans (hsquare.trans (mul_le_mul_of_nonneg_left hpowers (sq_nonneg Q)))
  calc
    |(1 - Real.exp (-q * t ^ 3)) - L * t ^ 3| =
        |(1 - Real.exp (-q * t ^ 3) - q * t ^ 3) + (q - L) * t ^ 3| := by ring_nf
    _ ≤ |1 - Real.exp (-q * t ^ 3) - q * t ^ 3| + |(q - L) * t ^ 3| := abs_add_le _ _
    _ ≤ (Q ^ 2 + B) * t ^ 4 := by linarith

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: cubic coefficient
control gives a linear coefficient-to-radius bound for the exact prescribed supports. -/
theorem coefficientRatio_le (p : Parameters) (hstart : 0 < p.startIndex)
    {κ A : ℝ} (hκ : 0 < κ)
    (hbound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ ≤ A * p.scale (k / 2) ^ 3)
    (k : ℕ) :
    ‖InterpolationSum.polarCoefficient p k‖ / InterpolationSum.polarSupportRadius p κ k ≤
      (A / κ) * p.scale (k / 2) := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have hρ : 0 < κ * p.scale (k / 2) ^ 2 := by positivity
  rw [InterpolationSum.polarSupportRadius_apply]
  calc
    ‖InterpolationSum.polarCoefficient p k‖ / (κ * p.scale (k / 2) ^ 2) ≤
        (A * p.scale (k / 2) ^ 3) / (κ * p.scale (k / 2) ^ 2) :=
      div_le_div_of_nonneg_right (hbound k) hρ.le
    _ = (A / κ) * p.scale (k / 2) := by
      field_simp

/-- Helper for lem:polar-interpolation: the exact coefficient-to-radius ratios tend
to zero as required by the accepted gluing theorem. -/
theorem coefficientRatio_tendsto_zero (p : Parameters) (hstart : 0 < p.startIndex)
    {κ A : ℝ} (hκ : 0 < κ)
    (hbound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ ≤ A * p.scale (k / 2) ^ 3) :
    Tendsto (fun k ↦ ‖InterpolationSum.polarCoefficient p k‖ /
      InterpolationSum.polarSupportRadius p κ k) atTop (𝓝 0) := by
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  have hscale := (ScaleTails.scale_tendsto_zero p).comp (Nat.tendsto_div_const_atTop htwo)
  have hlimit : Tendsto (fun k ↦ (A / κ) * p.scale (k / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using hscale.const_mul (A / κ)
  apply squeeze_zero _ (coefficientRatio_le p hstart hκ hbound) hlimit
  intro k
  rw [InterpolationSum.polarSupportRadius_apply]
  exact div_nonneg (norm_nonneg _) (mul_nonneg hκ.le (sq_nonneg _))

/-- Helper for lem:polar-interpolation: the coefficient-to-radius envelope is uniform
over every index and bounded by a constant times the original starting scale. -/
theorem coefficientRatio_le_start (p : Parameters) (hstart : 0 < p.startIndex)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hbound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ ≤ A * p.scale (k / 2) ^ 3)
    (k : ℕ) :
    ‖InterpolationSum.polarCoefficient p k‖ / InterpolationSum.polarSupportRadius p κ k ≤
      (A / κ) * p.scale 0 := by
  exact (coefficientRatio_le p hstart hκ hbound k).trans
    (mul_le_mul_of_nonneg_left (ScaleTails.scale_antitone p hstart (Nat.zero_le _))
      (div_nonneg hA hκ.le))

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: the exact cubic
scale cancels the support radius power `ρ^(-3/2)`. -/
theorem supportRadius_rpow (p : Parameters) (hstart : 0 < p.startIndex)
    {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) =
      κ ^ (-3 / 2 : ℝ) * (p.scale (k / 2) ^ 3)⁻¹ := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have hexponent : (2 : ℝ) * (-3 / 2) = -3 := by norm_num
  rw [InterpolationSum.polarSupportRadius_apply, Real.mul_rpow hκ.le (sq_nonneg _),
    ← Real.rpow_natCast_mul ht.le]
  simp only [Nat.cast_ofNat]
  rw [hexponent, Real.rpow_neg ht.le, Real.rpow_ofNat]

/-- Helper for lem:polar-interpolation: cubic coefficients give a global half-Hölder
envelope independent of every subsequent starting index. -/
theorem coefficientHolder_le (p : Parameters) (hstart : 0 < p.startIndex)
    {κ A : ℝ} (hκ : 0 < κ)
    (hbound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ ≤ A * p.scale (k / 2) ^ 3)
    (k : ℕ) :
    ‖InterpolationSum.polarCoefficient p k‖ *
        (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) ≤
      A * κ ^ (-3 / 2 : ℝ) := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have hpower := Real.rpow_nonneg hκ.le (-3 / 2 : ℝ)
  rw [supportRadius_rpow p hstart hκ]
  calc
    ‖InterpolationSum.polarCoefficient p k‖ *
        (κ ^ (-3 / 2 : ℝ) * (p.scale (k / 2) ^ 3)⁻¹) ≤
        (A * p.scale (k / 2) ^ 3) *
          (κ ^ (-3 / 2 : ℝ) * (p.scale (k / 2) ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_right (hbound k)
        (mul_nonneg hpower (inv_nonneg.mpr (pow_nonneg ht.le 3)))
    _ = A * κ ^ (-3 / 2 : ℝ) := by
      field_simp

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: the actual source
radial expansion places every unchanged closed support ball outside the unit disk. -/
theorem radialMargin_of_radius_error {p : Parameters} {D : Fin 2 → ℝ} {K c B κ : ℝ}
    (h : RadiusProducts.RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hsmall : (K + 2 * κ) * p.scale 0 ≤ 3 * (D 0 + D 1)) (k : ℕ) :
    1 + 2 * InterpolationSum.polarSupportRadius p κ k ≤ ‖p.point k‖ := by
  have ht := ScaleTails.scale_nonneg p (k / 2)
  have hconstant : 0 ≤ K + 2 * κ := by positivity
  have hscale := ScaleTails.scale_antitone p hstart (Nat.zero_le (k / 2))
  have hsmallj := (mul_le_mul_of_nonneg_left hscale hconstant).trans hsmall
  have hsmallPower := mul_le_mul_of_nonneg_right hsmallj ht
  have herror := (abs_le.mp (h.expansion k)).1
  rw [InterpolationSum.polarSupportRadius_apply,
    norm_point p k (zero_lt_one.trans (h.above_one k)).le]
  nlinarith

/-- Helper for eq:polar-corrections: the exact odd affine coefficient norm is the
positive feedback defect times the actual odd radius. -/
theorem norm_polarCoefficient_odd (p : Parameters) (j : ℕ)
    (hL : 0 ≤ p.feedbackRate) (hr : 0 ≤ p.radius (2 * j + 1)) :
    ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ =
      (1 - Real.exp (-(p.feedbackRate * (p.kStar / p.amplitude j) ^ 2) * p.scale j ^ 3)) *
        p.radius (2 * j + 1) := by
  have hu : 0 ≤ (p.feedbackRate * (p.kStar / p.amplitude j) ^ 2) * p.scale j ^ 3 :=
    mul_nonneg (mul_nonneg hL (sq_nonneg _)) (pow_nonneg (ScaleTails.scale_nonneg p j) 3)
  have hdefect := exp_neg_defect_bounds hu
  rw [polarCoefficient_odd, norm_smul, Real.norm_eq_abs, norm_point p _ hr, zeta_odd_eq_exp]
  rw [← neg_mul] at hdefect
  have hsign : Real.exp (-(p.feedbackRate * (p.kStar / p.amplitude j) ^ 2) *
      p.scale j ^ 3) - 1 ≤ 0 := by linarith [hdefect.1]
  rw [abs_of_nonpos hsign]
  ring

/-- Helper for eq:polar-corrections: a small interface for the cubic source
coefficients and their uniform fourth-order error, independent of objective regularity. -/
structure CoefficientEstimates (p : Parameters) (A E : ℝ) : Prop where
  /-- Helper for eq:polar-corrections: all actual coefficients satisfy the cubic envelope. -/
  norm_le : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ ≤ A * p.scale (k / 2) ^ 3
  /-- Helper for eq:polar-corrections: the odd norm has exactly the source cubic coefficient. -/
  odd_error : ∀ j, |‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ -
    p.feedbackRate * p.scale j ^ 3| ≤ E * p.scale j ^ 4

/-- Helper for eq:polar-corrections: the actual amplitude tube and the actual radius
products hold together on one source parameter neighborhood and one uniform threshold. -/
theorem actualAmplitudeRadiusBounds :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ M > 0, ∃ K > 0, ∃ c > 0, ∃ B > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          let p := Parameters.of j₀ νStar
          RadiusProducts.RadiusEstimates p (RadiusExpansions.radiusCoefficient νStar) K c B ∧
            ∀ j, |p.amplitude j - p.kStar| ≤ M * p.scale j := by
  obtain ⟨η₀, hη₀, htube⟩ := Continuation.actualTube
  obtain ⟨η₁, hη₁, hradii⟩ := RadiusProducts.polarRadiusProducts
  refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨hparameter, _, _, _, M, hM, J₀, hJ₀, htubeAll⟩ := htube νStar hnear₀
  obtain ⟨_, K, hK, c, hc, B, hB, J₁, hJ₁, hradiusAll⟩ := hradii νStar hnear₁
  refine ⟨hparameter, M, hM, K, hK, c, hc, B, hB,
    max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  refine ⟨hradiusAll j₀ ((le_max_right J₀ J₁).trans hj₀), ?_⟩
  intro j
  rw [amplitude_eq_normalized]
  exact (htubeAll j₀ ((le_max_left J₀ J₁).trans hj₀) j).1

/-- Helper for eq:polar-corrections: exact cubic feedback and the accepted radius
expansion imply the cubic correction envelope and its fourth-order norm remainder. -/
theorem coefficientEstimates_of_feedback {p : Parameters} {D : Fin 2 → ℝ}
    {K c B S Q : ℝ} (hr : RadiusProducts.RadiusEstimates p D K c B)
    (hstart : 0 < p.startIndex) (hK : 0 ≤ K) (hL : 0 ≤ p.feedbackRate)
    (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hfeedback : ∀ j,
      |p.feedbackRate * (p.kStar / p.amplitude j) ^ 2 - p.feedbackRate| ≤ S * p.scale j ∧
        p.feedbackRate * (p.kStar / p.amplitude j) ^ 2 ≤ Q ∧ Q * p.scale j ^ 3 ≤ 1) :
    CoefficientEstimates p (Real.exp 1 * Q)
      (Real.exp 1 * (Q ^ 2 + S) + p.feedbackRate * (3 * (D 0 + D 1) + K)) := by
  have hodd : ∀ j,
      ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ ≤
          (Real.exp 1 * Q) * p.scale j ^ 3 ∧
        |‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ - p.feedbackRate * p.scale j ^ 3| ≤
          (Real.exp 1 * (Q ^ 2 + S) + p.feedbackRate * (3 * (D 0 + D 1) + K)) *
            p.scale j ^ 4 := by
    intro j
    let q := p.feedbackRate * (p.kStar / p.amplitude j) ^ 2
    have hq : 0 ≤ q := mul_nonneg hL (sq_nonneg _)
    have ht := ScaleTails.scale_nonneg p j
    have htone := ScaleTails.scale_le_one p hstart j
    have hpow := pow_nonneg ht 3
    have hdefect := exp_neg_defect_bounds (mul_nonneg hq hpow)
    have hdefectUpper : 1 - Real.exp (-q * p.scale j ^ 3) ≤ Q * p.scale j ^ 3 := by
      rw [← neg_mul] at hdefect
      exact hdefect.2.trans (mul_le_mul_of_nonneg_right (hfeedback j).2.1 hpow)
    have hrnonneg := (zero_lt_one.trans (hr.above_one (2 * j + 1))).le
    have hrUpper := hr.upper (2 * j + 1)
    have hnorm := norm_polarCoefficient_odd p j hL hrnonneg
    have herror := feedbackDefect_error ht htone hq (hfeedback j).2.1
      (hfeedback j).2.2 (hfeedback j).1
    have hquot : (2 * j + 1) / 2 = j := by omega
    have hRadError := (abs_le.mp (hr.expansion (2 * j + 1))).2
    rw [hquot] at hRadError
    have hexponents : (1 : ℕ) ≤ 2 := by norm_num
    have hpowers : p.scale j ^ 2 ≤ p.scale j := by
      simpa only [pow_one] using pow_le_pow_of_le_one ht htone hexponents
    have hRad : p.radius (2 * j + 1) - 1 ≤ (3 * (D 0 + D 1) + K) * p.scale j := by
      have hmul := mul_le_mul_of_nonneg_left hpowers hK
      linarith
    have hRadNonneg : 0 ≤ p.radius (2 * j + 1) - 1 := sub_nonneg.mpr (hr.above_one _).le
    constructor
    · rw [hnorm]
      calc
        (1 - Real.exp (-q * p.scale j ^ 3)) * p.radius (2 * j + 1) ≤
            (Q * p.scale j ^ 3) * Real.exp 1 :=
          mul_le_mul hdefectUpper hrUpper hrnonneg (mul_nonneg hQ hpow)
        _ = (Real.exp 1 * Q) * p.scale j ^ 3 := by ring
    · rw [hnorm]
      calc
        |(1 - Real.exp (-q * p.scale j ^ 3)) * p.radius (2 * j + 1) -
            p.feedbackRate * p.scale j ^ 3| =
            |((1 - Real.exp (-q * p.scale j ^ 3)) - p.feedbackRate * p.scale j ^ 3) *
              p.radius (2 * j + 1) +
                (p.feedbackRate * p.scale j ^ 3) * (p.radius (2 * j + 1) - 1)| := by ring_nf
        _ ≤ |((1 - Real.exp (-q * p.scale j ^ 3)) - p.feedbackRate * p.scale j ^ 3) *
              p.radius (2 * j + 1)| +
            |(p.feedbackRate * p.scale j ^ 3) * (p.radius (2 * j + 1) - 1)| := abs_add_le _ _
        _ ≤ ((Q ^ 2 + S) * p.scale j ^ 4) * Real.exp 1 +
            (p.feedbackRate * p.scale j ^ 3) * ((3 * (D 0 + D 1) + K) * p.scale j) := by
          rw [abs_mul, abs_of_nonneg hrnonneg,
            abs_of_nonneg (mul_nonneg (mul_nonneg hL hpow) hRadNonneg)]
          exact add_le_add
            (mul_le_mul herror hrUpper hrnonneg (mul_nonneg (add_nonneg (sq_nonneg Q) hS)
              (pow_nonneg ht 4)))
            (mul_le_mul_of_nonneg_left hRad (mul_nonneg hL hpow))
        _ = (Real.exp 1 * (Q ^ 2 + S) +
            p.feedbackRate * (3 * (D 0 + D 1) + K)) * p.scale j ^ 4 := by ring
  constructor
  · intro k
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [polarCoefficient_even, norm_zero]
      have ht := ScaleTails.scale_nonneg p (2 * j / 2)
      positivity
    · have hquot : (2 * j + 1) / 2 = j := by omega
      rw [hquot]
      exact (hodd j).1
  · intro j
    exact (hodd j).2

/-- Helper for eq:polar-corrections: the fixed source angle is positive. -/
theorem baseAngle_pos : 0 < baseAngle := by
  rw [baseAngle_def]
  positivity

/-- eq:polar-corrections (uniform actual estimates). The original feedback and
radius products prove the cubic correction law with a uniform fourth-order error.
All constants precede every subsequent choice of the starting index. -/
theorem actualCoefficientEstimates :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ A > 0, ∃ E > 0, ∃ K > 0, ∃ c > 0, ∃ B > 0,
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          let p := Parameters.of j₀ νStar
          RadiusProducts.RadiusEstimates p (RadiusExpansions.radiusCoefficient νStar) K c B ∧
            CoefficientEstimates p A E ∧ 0 < p.feedbackRate := by
  obtain ⟨η, hη, hdata⟩ := actualAmplitudeRadiusBounds
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, M, hM, K, hK, c, hc, B, hB, J₀, hJ₀, hall⟩ := hdata νStar hnear
  let L := 4 * baseAngle / (9 * νStar)
  have ha := baseAngle_pos
  have hν : 0 < νStar := ha.trans hnear.1
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hKstar : 0 < cycleK νStar := (TwoCycle.cycleFamily_mapsTo_positive hparameter).1
  obtain ⟨S, hS, δ, hδ, hlocal⟩ := feedbackCoefficient_local_bound L (cycleK νStar) hKstar.ne'
  let Q := L + S * M
  have hQ : 0 < Q := by positivity
  let R := 3 * (RadiusExpansions.radiusCoefficient νStar 0 +
    RadiusExpansions.radiusCoefficient νStar 1) + K
  have hD := RadiusExpansions.radiusCoefficients_pos νStar hparameter
  have hD₀ := hD.1
  have hD₁ := hD.2
  have hR : 0 < R := by positivity
  have hE : 0 < Real.exp 1 * (Q ^ 2 + S * M) + L * R := by positivity
  have hcutoff : 0 < min (δ / (M + 1)) (1 / (Q + 1)) := by positivity
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨hparameter, Real.exp 1 * Q, mul_pos (Real.exp_pos 1) hQ,
    Real.exp 1 * (Q ^ 2 + S * M) + L * R, hE, K, hK, c, hc, B, hB,
      max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hj₀old : J₀ ≤ j₀ := (le_max_left J₀ J₁).trans hj₀
  have hj₀scale : J₁ ≤ j₀ := (le_max_right J₀ J₁).trans hj₀
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  have hpL : p.feedbackRate = L := by
    rw [Parameters.feedbackRate_def, Parameters.of_cycleParameter]
  have hpK : p.kStar = cycleK νStar := by
    rw [Parameters.kStar_def, Parameters.of_cycleParameter]
  have hzero : p.scale 0 < min (δ / (M + 1)) (1 / (Q + 1)) := hscale νStar j₀ hj₀scale
  have hzeroδ := hzero.trans_le (min_le_left _ _)
  have hzeroQ := hzero.trans_le (min_le_right _ _)
  have hMone : 0 < M + 1 := by positivity
  have hQone : 0 < Q + 1 := by positivity
  have hfeedback : ∀ j,
      |p.feedbackRate * (p.kStar / p.amplitude j) ^ 2 - p.feedbackRate| ≤
          (S * M) * p.scale j ∧
        p.feedbackRate * (p.kStar / p.amplitude j) ^ 2 ≤ Q ∧ Q * p.scale j ^ 3 ≤ 1 := by
    intro j
    have ht := ScaleTails.scale_nonneg p j
    have htone := ScaleTails.scale_le_one p hstart j
    have hscalej := ScaleTails.scale_antitone p hstart (Nat.zero_le j)
    have hamp := (hall j₀ hj₀old).2 j
    rw [hpK] at hamp
    have hampδ : |p.amplitude j - cycleK νStar| < δ := by
      nlinarith [(lt_div_iff₀ hMone).mp hzeroδ]
    have hqError : |L * (cycleK νStar / p.amplitude j) ^ 2 - L| ≤ S * M * p.scale j := by
      have hbound := (hlocal (p.amplitude j) hampδ).trans
        (mul_le_mul_of_nonneg_left hamp hS.le)
      simpa only [hpK, mul_assoc] using hbound
    have hqUpper : L * (cycleK νStar / p.amplitude j) ^ 2 ≤ Q := by
      have hsmall := mul_le_mul_of_nonneg_left htone (mul_nonneg hS.le hM.le)
      have hbound := (abs_le.mp hqError).2
      dsimp only [Q]
      linarith
    have hexponents : (1 : ℕ) ≤ 3 := by norm_num
    have hpow : p.scale j ^ 3 ≤ p.scale j := by
      simpa only [pow_one] using pow_le_pow_of_le_one ht htone hexponents
    have hQsmall : Q * p.scale j ^ 3 ≤ 1 := by
      have hpower := mul_le_mul_of_nonneg_left (hpow.trans hscalej) hQ.le
      nlinarith [(lt_div_iff₀ hQone).mp hzeroQ, ScaleTails.scale_nonneg p 0]
    rw [hpL, hpK]
    exact ⟨hqError, hqUpper, hQsmall⟩
  have hLp : 0 < p.feedbackRate := by
    rw [hpL]
    exact hL
  have hcoeff := coefficientEstimates_of_feedback (hall j₀ hj₀old).1 hstart hK.le
    hLp.le (mul_nonneg hS.le hM.le) hQ.le hfeedback
  rw [hpL] at hcoeff
  exact ⟨(hall j₀ hj₀old).1, hcoeff, hLp⟩

/-- Helper for eq:polar-corrections: the cubic source envelope makes the actual
correction norms tend to zero. -/
theorem CoefficientEstimates.norm_tendsto_zero {p : Parameters} {A E : ℝ}
    (h : CoefficientEstimates p A E) :
    Tendsto (fun k ↦ ‖InterpolationSum.polarCoefficient p k‖) atTop (𝓝 0) := by
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  have hthree : (3 : ℕ) ≠ 0 := by norm_num
  have hscale := (ScaleTails.scale_tendsto_zero p).comp (Nat.tendsto_div_const_atTop htwo)
  have hlimit : Tendsto (fun k ↦ A * p.scale (k / 2) ^ 3) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow hthree, mul_zero] using
      (hscale.pow 3).const_mul A
  exact squeeze_zero (fun _ ↦ norm_nonneg _) h.norm_le hlimit

/-- Helper for lem:polar-interpolation: the actual original point norms tend to one
as a direct consequence of the accepted radius products. -/
theorem point_norm_tendsto_one {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (h : RadiusProducts.RadiusEstimates p D K c B) :
    Tendsto (fun k ↦ ‖p.point k‖) atTop (𝓝 1) := by
  have hnorm (k : ℕ) : ‖p.point k‖ = p.radius k :=
    norm_point p k (zero_lt_one.trans (h.above_one k)).le
  simpa only [hnorm] using h.tendsto_one

/-- Helper for eq:polar-corrections and eq:polar-endpoint-data: the prescribed gradient
norm tends to exactly one, using the source correction decay and original radii. -/
theorem gradient_norm_tendsto_one {p : Parameters} {D : Fin 2 → ℝ} {K c B A E : ℝ}
    (hr : RadiusProducts.RadiusEstimates p D K c B) (ha : CoefficientEstimates p A E) :
    Tendsto (fun k ↦ ‖p.gradient k‖) atTop (𝓝 1) := by
  have hbound : ∀ k, ‖‖p.gradient k‖ - ‖p.point k‖‖ ≤
      ‖InterpolationSum.polarCoefficient p k‖ := by
    intro k
    rw [Real.norm_eq_abs, InterpolationSum.polarCoefficient_apply]
    exact abs_norm_sub_norm_le _ _
  have hzero := squeeze_zero_norm hbound ha.norm_tendsto_zero
  simpa only [sub_add_cancel, zero_add] using hzero.add (point_norm_tendsto_one hr)

/-- Helper for eq:polar-corrections: the uniform fourth-order error proves the exact
source equivalence `‖a_(2j+1)‖ / (L t_j³) ⟶ 1`. -/
theorem CoefficientEstimates.odd_ratio_tendsto_one {p : Parameters} {A E : ℝ}
    (h : CoefficientEstimates p A E) (hstart : 0 < p.startIndex) (hL : 0 < p.feedbackRate) :
    Tendsto (fun j ↦ ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ /
      (p.feedbackRate * p.scale j ^ 3)) atTop (𝓝 1) := by
  have hbound : ∀ j, ‖‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ /
      (p.feedbackRate * p.scale j ^ 3) - 1‖ ≤ (E / p.feedbackRate) * p.scale j := by
    intro j
    have ht := ScaleTails.scale_pos p hstart j
    have hden : 0 < p.feedbackRate * p.scale j ^ 3 := by positivity
    have hid : ‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ /
        (p.feedbackRate * p.scale j ^ 3) - 1 =
        (‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ -
          p.feedbackRate * p.scale j ^ 3) / (p.feedbackRate * p.scale j ^ 3) := by
      field_simp
    rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos hden]
    calc
      |‖InterpolationSum.polarCoefficient p (2 * j + 1)‖ -
          p.feedbackRate * p.scale j ^ 3| / (p.feedbackRate * p.scale j ^ 3) ≤
          (E * p.scale j ^ 4) / (p.feedbackRate * p.scale j ^ 3) :=
        div_le_div_of_nonneg_right (h.odd_error j) hden.le
      _ = (E / p.feedbackRate) * p.scale j := by field_simp
  have hlimit : Tendsto (fun j ↦ (E / p.feedbackRate) * p.scale j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (ScaleTails.scale_tendsto_zero p).const_mul (E / p.feedbackRate)
  have hzero := squeeze_zero_norm hbound hlimit
  simpa only [sub_add_cancel, zero_add] using hzero.add_const 1

/-- Helper for eq:polar-support-radii: genuine all-pairs source separation gives
disjoint OPEN balls at the unchanged radii `κ t_(k/2)²`. -/
theorem supportBalls_disjoint_of_separation (p : Parameters) {κ s : ℝ}
    (hκ : 0 ≤ κ) (hsmall : 2 * κ ≤ s)
    (hsep : ∀ k m, k ≠ m → s * max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) ≤
      ‖p.point m - p.point k‖) :
    Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball (p.point k) (InterpolationSum.polarSupportRadius p κ k)) := by
  intro k _ m _ hkm
  apply Metric.ball_disjoint_ball
  rw [InterpolationSum.polarSupportRadius_apply, InterpolationSum.polarSupportRadius_apply,
    dist_eq_norm, norm_sub_rev]
  have hmax : 0 ≤ max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) :=
    (sq_nonneg _).trans (le_max_left _ _)
  calc
    κ * p.scale (k / 2) ^ 2 + κ * p.scale (m / 2) ^ 2 ≤
        κ * max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) +
          κ * max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hκ)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hκ)
    _ = (2 * κ) * max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) := by ring
    _ ≤ s * max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmall hmax
    _ ≤ ‖p.point m - p.point k‖ := hsep k m hkm

/-- Helper for lem:polar-interpolation: the Riesz map transports the ordinary second
Fréchet derivative to the gradient Hessian without changing the source function. -/
theorem hessian_eq_riesz_comp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (f : F → ℝ) (x : F) :
    fderiv ℝ (gradient f) x =
      ((InnerProductSpace.toDual ℝ F).symm : StrongDual ℝ F →L[ℝ] F) ∘L
        fderiv ℝ (fderiv ℝ f) x := by
  have hfun : gradient f = (InnerProductSpace.toDual ℝ F).symm ∘ fderiv ℝ f := by
    rfl
  rw [hfun]
  exact LinearIsometryEquiv.comp_fderiv (InnerProductSpace.toDual ℝ F).symm

/-- Helper for lem:polar-interpolation: differences of the Hessian operators and
ordinary second Fréchet derivatives have exactly the same norm. -/
theorem norm_hessian_sub_eq_secondFDeriv_sub {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (f : F → ℝ) (x y : F) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  rw [hessian_eq_riesz_comp, hessian_eq_riesz_comp, ← ContinuousLinearMap.comp_sub]
  exact LinearIsometry.norm_toContinuousLinearMap_comp
    (InnerProductSpace.toDual ℝ F).symm.toLinearIsometry

/-- Helper for lem:polar-interpolation: a small universal interface for the fixed
cutoff's second-derivative and half-Hölder estimates on the exact infinite sum. -/
structure CutoffBounds (Cχ : ℝ) : Prop where
  /-- Helper for lem:polar-interpolation: both source estimates hold before all data. -/
  estimates : ∀ (c : ℕ → EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ)
      (a : ℕ → EuclideanSpace ℝ (Fin 2)),
      InterpolationSum.Geometry c ρ a → ∀ B M : ℝ, 0 ≤ B → 0 ≤ M →
      (∀ k, ‖a k‖ / ρ k ≤ B) → (∀ k, ‖a k‖ * (ρ k) ^ (-3 / 2 : ℝ) ≤ M) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x‖ ≤ Cχ * B) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) x -
        fderiv ℝ (fderiv ℝ (InterpolationSum.perturbation c ρ a)) y‖ ≤
          2 * Cχ * M * ‖x - y‖ ^ (1 / 2 : ℝ))

/-- Helper for lem:polar-interpolation: a single strictly positive cutoff constant
controls both global estimates before all interpolation data. -/
theorem exists_positive_cutoff_bounds : ∃ Cχ > 0, CutoffBounds Cχ := by
  obtain ⟨C, hC, hbounds⟩ :=
    InterpolationSum.exists_global_hessian_bounds (E := EuclideanSpace ℝ (Fin 2))
  refine ⟨C + 1, add_pos_of_nonneg_of_pos hC zero_lt_one, ⟨?_⟩⟩
  intro c ρ a h B M hB hM hsize hholder
  obtain ⟨hsizeBound, hholderBound⟩ := hbounds c ρ a h B M hB hM hsize hholder
  constructor
  · intro x
    have hconstant : C ≤ C + 1 := by linarith
    exact (hsizeBound x).trans (mul_le_mul_of_nonneg_right hconstant hB)
  · intro x y
    have hconstant : 2 * C * M ≤ 2 * (C + 1) * M := by nlinarith
    exact (hholderBound x y).trans
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (norm_nonneg _) _))

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: actual source data
prepared independently of all-pairs separation. Regularity is not a field. -/
structure PreparedData (p : Parameters) (κ A E : ℝ) : Prop where
  /-- Helper for lem:polar-interpolation: the original starting index is positive. -/
  start_pos : 0 < p.startIndex
  /-- Helper for eq:polar-support-radii: the fixed support coefficient is positive. -/
  support_pos : 0 < κ
  /-- Helper for eq:polar-corrections: the actual cubic source coefficient estimates. -/
  coefficients : CoefficientEstimates p A E
  /-- Helper for eq:polar-corrections: the source cubic feedback rate is positive. -/
  feedback_pos : 0 < p.feedbackRate
  /-- Helper for lem:polar-interpolation: the actual radius is the center norm. -/
  center_norm : ∀ k, ‖p.point k‖ = p.radius k
  /-- Helper for lem:polar-interpolation: actual centers approach the unit circle radially. -/
  centers_limit : Tendsto (fun k ↦ ‖p.point k‖) atTop (𝓝 1)
  /-- Helper for lem:polar-interpolation: the original closed supports have a radial margin. -/
  margin : ∀ k, 1 + 2 * InterpolationSum.polarSupportRadius p κ k ≤ ‖p.point k‖
  /-- Helper for lem:polar-interpolation: the actual coefficient-to-radius ratio decays. -/
  ratio_decay : Tendsto (fun k ↦ ‖InterpolationSum.polarCoefficient p k‖ /
    InterpolationSum.polarSupportRadius p κ k) atTop (𝓝 0)
  /-- Helper for lem:polar-interpolation: the global ratio envelope is a fixed multiple of t₀. -/
  ratio_bound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ /
    InterpolationSum.polarSupportRadius p κ k ≤ (A / κ) * p.scale 0
  /-- Helper for lem:polar-interpolation: the actual half-Hölder coefficient is uniform. -/
  holder_bound : ∀ k, ‖InterpolationSum.polarCoefficient p k‖ *
    (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) ≤ A * κ ^ (-3 / 2 : ℝ)
  /-- Helper for eq:polar-endpoint-data: the actual prescribed gradient norm tends to one. -/
  gradient_limit : Tendsto (fun k ↦ ‖p.gradient k‖) atTop (𝓝 1)

/-- Helper for lem:polar-interpolation: disjoint OPEN balls complete exactly the
geometric certificate required by the accepted C² gluing proof. -/
theorem PreparedData.geometry {p : Parameters} {κ A E : ℝ} (h : PreparedData p κ A E)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball (p.point k) (InterpolationSum.polarSupportRadius p κ k))) :
    InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p) := by
  constructor
  · intro k
    rw [InterpolationSum.polarSupportRadius_apply]
    exact mul_pos h.support_pos (sq_pos_of_pos (ScaleTails.scale_pos p h.start_pos _))
  · exact hballs
  · exact h.centers_limit
  · exact h.margin
  · exact h.ratio_decay

/-- Helper for lem:polar-interpolation and eq:polar-support-radii: all actual margin,
decay and coefficient estimates hold after choosing the fixed support parameter and
then one natural starting-index threshold. Separation is proved independently. -/
theorem actualPreparedData :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ A > 0, ∃ E > 0, ∀ κ : ℝ, 0 < κ → ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        PreparedData (Parameters.of j₀ νStar) κ A E := by
  obtain ⟨η, hη, hdata⟩ := actualCoefficientEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, A, hA, E, hE, K, hK, c, _, B, _, J₀, hJ₀, hall⟩ := hdata νStar hnear
  refine ⟨A, hA, E, hE, ?_⟩
  intro κ hκ
  let D := RadiusExpansions.radiusCoefficient νStar
  have hD := RadiusExpansions.radiusCoefficients_pos νStar hparameter
  have hDsum : 0 < D 0 + D 1 := add_pos hD.1 hD.2
  have hcutoff : 0 < 3 * (D 0 + D 1) / (K + 2 * κ + 1) := by positivity
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  let p := Parameters.of j₀ νStar
  have hj₀old : J₀ ≤ j₀ := (le_max_left J₀ J₁).trans hj₀
  have hj₀scale : J₁ ≤ j₀ := (le_max_right J₀ J₁).trans hj₀
  obtain ⟨hr, ha, hL⟩ := hall j₀ hj₀old
  have hstart : 0 < p.startIndex := by
    simpa only [p, Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  have hzero : p.scale 0 < 3 * (D 0 + D 1) / (K + 2 * κ + 1) :=
    hscale νStar j₀ hj₀scale
  have hden : 0 < K + 2 * κ + 1 := by positivity
  have hsmall : (K + 2 * κ) * p.scale 0 ≤ 3 * (D 0 + D 1) := by
    nlinarith [(lt_div_iff₀ hden).mp hzero, ScaleTails.scale_nonneg p 0]
  exact ⟨hstart, hκ, ha, hL,
    fun k ↦ norm_point p k (zero_lt_one.trans (hr.above_one k)).le,
    point_norm_tendsto_one hr, radialMargin_of_radius_error hr hstart hK.le hκ.le hsmall,
    coefficientRatio_tendsto_zero p hstart hκ ha.norm_le,
    coefficientRatio_le_start p hstart hκ hA.le ha.norm_le,
    coefficientHolder_le p hstart hκ ha.norm_le, gradient_norm_tendsto_one hr ha⟩

/-- Helper for eq:polar-endpoint-data: the exact source objective realizes each
prescribed value, original gradient and identity Hessian once Geometry is proved. -/
theorem objective_endpoint {p : Parameters} {κ A E : ℝ} (h : PreparedData p κ A E)
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p)) (k : ℕ) :
    InterpolationSum.polarObjective p κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 ∧
      gradient (InterpolationSum.polarObjective p κ) (p.point k) = p.gradient k ∧
      fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) (p.point k) = 1 := by
  rw [InterpolationSum.polarObjective_def]
  refine ⟨?_, ?_, InterpolationSum.hessian_objective_center hg k⟩
  · rw [InterpolationSum.objective_center hg, h.center_norm]
  · rw [InterpolationSum.gradient_objective_center hg, InterpolationSum.polarCoefficient_apply]
    abel

/-- Helper for lem:polar-interpolation: the exact perturbation and both jets vanish
on the entire closed unit disk, including its true support-boundary contacts. -/
theorem perturbation_jets_on_disk {p : Parameters} {κ : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p)) {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ 1) :
    InterpolationSum.polarPerturbation p κ x = 0 ∧
      gradient (InterpolationSum.polarPerturbation p κ) x = 0 ∧
      fderiv ℝ (gradient (InterpolationSum.polarPerturbation p κ)) x = 0 := by
  rw [InterpolationSum.polarPerturbation_def]
  refine ⟨InterpolationSum.perturbation_eq_zero_of_norm_le_one hg hx,
    InterpolationSum.gradient_perturbation_eq_zero_of_norm_le_one hg hx, ?_⟩
  apply norm_eq_zero.mp
  rw [norm_fderiv_gradient_eq_norm_fderiv_fderiv,
    InterpolationSum.secondFDeriv_perturbation_eq_zero_of_norm_le_one hg hx, norm_zero]

/-- Helper for lem:polar-interpolation: the actual objective Hessian perturbation
has the same norm bound as the ordinary second derivative of the exact source sum. -/
theorem objective_hessian_bound {p : Parameters} {κ D : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p))
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x‖ ≤ D)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x - 1‖ ≤ D := by
  rw [InterpolationSum.polarObjective_def, InterpolationSum.hessian_objective hg,
    add_sub_cancel_left, norm_fderiv_gradient_eq_norm_fderiv_fderiv,
    ← InterpolationSum.polarPerturbation_def]
  exact hbound x

/-- Helper for lem:polar-interpolation: the objective inherits the exact source sum's
global half-Hölder Hessian modulus through the fixed Riesz isometry. -/
theorem objective_hessian_holder {p : Parameters} {κ H : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p))
    (hholder : ∀ x y, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x -
        fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ)) (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x -
        fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  rw [InterpolationSum.polarObjective_def, InterpolationSum.hessian_objective hg,
    InterpolationSum.hessian_objective hg, add_sub_add_left_eq_sub,
    norm_hessian_sub_eq_secondFDeriv_sub, ← InterpolationSum.polarPerturbation_def]
  exact hholder x y

/-- Helper for lem:polar-interpolation and eq:polar-objective: the source small
Hessian bound yields the uniform Loewner bounds, strong convexity and quadratic growth. -/
theorem objective_convexity_of_small_bound {p : Parameters} {κ ε : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p))
    (hε : ε < 1)
    (hbound : ∀ x, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x‖ ≤ ε) :
    HasHessianBounds (1 - ε) (1 + ε) (InterpolationSum.polarObjective p κ) ∧
      StrongConvexOn Set.univ (1 - ε) (InterpolationSum.polarObjective p κ) ∧
      ∀ x, ((1 - ε) / 2) * ‖x‖ ^ 2 ≤ InterpolationSum.polarObjective p κ x := by
  have hcont : ContDiff ℝ 2 (InterpolationSum.polarPerturbation p κ) := by
    rw [InterpolationSum.polarPerturbation_def]
    exact InterpolationSum.contDiff_perturbation hg
  have hfun : InterpolationSum.polarObjective p κ =
      fun x ↦ (1 / 2 : ℝ) * ‖x - 0‖ ^ 2 + InterpolationSum.polarPerturbation p κ x := by
    funext x
    rw [InterpolationSum.polarObjective_apply, sub_zero]
  have hpositive : 0 < 1 - ε := sub_pos.mpr hε
  have hHessian := HessianPerturbation.hasHessianBounds_halfNormSq_sub_add_of_secondFDeriv_norm_le
    (0 : EuclideanSpace ℝ (Fin 2)) (InterpolationSum.polarPerturbation p κ) ε
    hcont hbound
  have hconvex := HessianPerturbation.strongConvexOn_halfNormSq_add_of_secondFDeriv_norm_le
    (0 : EuclideanSpace ℝ (Fin 2)) (InterpolationSum.polarPerturbation p κ) ε
    hcont hε hbound
  rw [← hfun] at hHessian hconvex
  have hregular : ContDiff ℝ 2 (InterpolationSum.polarObjective p κ) := by
    rw [InterpolationSum.polarObjective_def]
    exact InterpolationSum.contDiff_objective hg
  have hlower : ∀ x v, (1 - ε) * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x v) v := by
    intro x v
    simpa only [hessian_def] using ((hHessian.at x).quadraticForm v).1
  have hzeroNorm : ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by simp
  have hjet := perturbation_jets_on_disk hg hzeroNorm
  have hgradientZero : gradient (InterpolationSum.polarObjective p κ) 0 = 0 := by
    rw [hfun, HessianPerturbation.gradient_halfNormSq_sub_add]
    · simpa only [sub_self, zero_add] using hjet.2.1
    · exact (hcont.differentiable two_ne_zero).differentiableAt
  have hzero : InterpolationSum.polarObjective p κ 0 = 0 := by
    rw [InterpolationSum.polarObjective_def]
    exact InterpolationSum.objective_zero hg
  refine ⟨hHessian, hconvex, ?_⟩
  intro x
  have hgrowth := ContDiff.firstOrderOfHessianLowerBound _ (1 - ε)
    hregular hpositive hlower 0 x
  simpa only [hzero, hgradientZero, inner_zero_left, sub_zero, zero_add] using hgrowth

/-- Helper for lem:polar-interpolation: the actual source bump is exactly the accepted
generic correction at the unchanged point, support radius and affine coefficient. -/
theorem polarBump_eq_correction (p : Parameters) (κ : ℝ) (k : ℕ) :
    InterpolationSum.polarBump p κ k = ExplicitCutoff.correction (p.point k)
      (InterpolationSum.polarSupportRadius p κ k) (InterpolationSum.polarCoefficient p k) := by
  funext x
  rw [InterpolationSum.polarBump_apply, ExplicitCutoff.correction_apply,
    InterpolationSum.polarSupportRadius_apply, InterpolationSum.polarCoefficient_apply]

/-- Helper for lem:polar-interpolation: each actual source correction is smooth. -/
theorem contDiff_polarBump (p : Parameters) (κ : ℝ) (k : ℕ) :
    ContDiff ℝ ∞ (InterpolationSum.polarBump p κ k) := by
  rw [polarBump_eq_correction]
  exact ExplicitCutoff.contDiff_correction _ _ _

/-- Helper for lem:polar-interpolation: each actual source bump has its global
half-Hölder Hessian bound with the fixed cutoff constant chosen before all data. -/
theorem exists_polarBump_holder :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (p : Parameters) (κ : ℝ), 0 < p.startIndex → 0 < κ →
      ∀ k x y, ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarBump p κ k)) x -
        fderiv ℝ (fderiv ℝ (InterpolationSum.polarBump p κ k)) y‖ ≤
          Cχ * ‖InterpolationSum.polarCoefficient p k‖ *
            (InterpolationSum.polarSupportRadius p κ k) ^ (-3 / 2 : ℝ) *
              ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨Cχ, hCχ, hholder⟩ :=
    InterpolationBounds.exists_norm_hessian_correction_sub_le (E := EuclideanSpace ℝ (Fin 2))
  refine ⟨Cχ, hCχ, ?_⟩
  intro p κ hstart hκ k x y
  have hρ : 0 < InterpolationSum.polarSupportRadius p κ k := by
    rw [InterpolationSum.polarSupportRadius_apply]
    exact mul_pos hκ (sq_pos_of_pos (ScaleTails.scale_pos p hstart _))
  rw [polarBump_eq_correction]
  exact hholder _ _ _ x y hρ

/-- Helper for eq:polar-objective: positive quadratic growth and origin normalization
give exactly one global minimizer, at the origin. -/
theorem unique_minimizer_of_quadratic_growth {F : Type*} [NormedAddCommGroup F]
    {f : F → ℝ} {m : ℝ} (hm : 0 < m) (hzero : f 0 = 0)
    (hgrowth : ∀ x, m * ‖x‖ ^ 2 ≤ f x) (x : F) :
    (∀ y, f x ≤ f y) ↔ x = 0 := by
  constructor
  · intro hmin
    have hupper := hmin 0
    rw [hzero] at hupper
    have hnorm : ‖x‖ = 0 := by
      by_contra hn
      have hnpos := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hn)
      have hpositive := mul_pos hm (sq_pos_of_pos hnpos)
      exact (not_lt_of_ge ((hgrowth x).trans hupper)) hpositive
    exact norm_eq_zero.mp hnorm
  · intro hx
    subst x
    intro y
    rw [hzero]
    exact (mul_nonneg hm.le (sq_nonneg _)).trans (hgrowth y)

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the complete actual
objective conclusions, including arbitrary near-identity accuracy, with no geometric
or regularity assumptions hidden in the certificate. -/
structure ObjectiveEstimates (p : Parameters) (κ ε C H : ℝ) : Prop where
  /-- Helper for lem:polar-interpolation: the actual source Geometry has been proved. -/
  geometry : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
    (InterpolationSum.polarCoefficient p)
  /-- Helper for lem:polar-interpolation: each unchanged actual bump is smooth. -/
  bump_smooth : ∀ k, ContDiff ℝ ∞ (InterpolationSum.polarBump p κ k)
  /-- Helper for lem:polar-interpolation: actual topological supports are CLOSED balls. -/
  closed_support : ∀ k, tsupport (InterpolationSum.polarBump p κ k) ⊆
    Metric.closedBall (p.point k) (InterpolationSum.polarSupportRadius p κ k)
  /-- Helper for eq:polar-objective: the pointwise finsum equals the exact source infinite sum. -/
  sum_formula : ∀ x, InterpolationSum.polarPerturbation p κ x =
    ∑' k, InterpolationSum.polarBump p κ k x
  /-- Helper for lem:polar-interpolation: C² regularity of the exact sum across the sphere. -/
  perturbation_contDiff : ContDiff ℝ 2 (InterpolationSum.polarPerturbation p κ)
  /-- Helper for lem:polar-interpolation: C² regularity of the actual source objective. -/
  objective_contDiff : ContDiff ℝ 2 (InterpolationSum.polarObjective p κ)
  /-- Helper for lem:polar-interpolation: the source perturbation jets vanish on the circle. -/
  sphere_jets : ∀ x, ‖x‖ = 1 → InterpolationSum.polarPerturbation p κ x = 0 ∧
    gradient (InterpolationSum.polarPerturbation p κ) x = 0 ∧
      fderiv ℝ (gradient (InterpolationSum.polarPerturbation p κ)) x = 0
  /-- Helper for eq:polar-interpolation-jets: the exact interpolation at each center. -/
  center_jets : ∀ k, InterpolationSum.polarPerturbation p κ (p.point k) = 0 ∧
    gradient (InterpolationSum.polarPerturbation p κ) (p.point k) =
      InterpolationSum.polarCoefficient p k ∧
      fderiv ℝ (gradient (InterpolationSum.polarPerturbation p κ)) (p.point k) = 0
  /-- Helper for eq:polar-endpoint-data: the exact original values, gradients and Hessians. -/
  endpoints : ∀ k,
    InterpolationSum.polarObjective p κ (p.point k) = (1 / 2 : ℝ) * p.radius k ^ 2 ∧
      gradient (InterpolationSum.polarObjective p κ) (p.point k) = p.gradient k ∧
      fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) (p.point k) = 1
  /-- Helper for eq:polar-objective: the actual objective is quadratic on the closed disk. -/
  disk : ∀ x, ‖x‖ ≤ 1 → InterpolationSum.polarObjective p κ x = (1 / 2 : ℝ) * ‖x‖ ^ 2
  /-- Helper for eq:polar-endpoint-data: the objective has exactly the source normalization. -/
  origin : InterpolationSum.polarObjective p κ 0 = 0
  /-- Helper for eq:polar-interpolation-bound: the global Hessian correction is at most Ct₀. -/
  perturbation_bound : ∀ x,
    ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x‖ ≤ C * p.scale 0
  /-- Helper for lem:polar-interpolation: the objective has the same global Hessian envelope. -/
  hessian_bound : ∀ x,
    ‖fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x - 1‖ ≤ C * p.scale 0
  /-- Helper for lem:polar-interpolation: arbitrary source accuracy follows by increasing j₀. -/
  near_identity : ∀ x,
    ‖fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x - 1‖ ≤ ε
  /-- Helper for lem:polar-interpolation: the exact sum has a global half-Hölder Hessian. -/
  perturbation_holder : ∀ x y,
    ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x -
      fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) y‖ ≤
        H * ‖x - y‖ ^ (1 / 2 : ℝ)
  /-- Helper for lem:polar-interpolation: the objective Hessian has the same global modulus. -/
  hessian_holder : ∀ x y,
    ‖fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) x -
      fderiv ℝ (gradient (InterpolationSum.polarObjective p κ)) y‖ ≤
        H * ‖x - y‖ ^ (1 / 2 : ℝ)
  /-- Helper for eq:polar-objective: the source uniform two-sided Loewner Hessian bounds. -/
  hessian_bounds : HasHessianBounds (1 - ε) (1 + ε) (InterpolationSum.polarObjective p κ)
  /-- Helper for eq:polar-objective: the source objective is uniformly strongly convex. -/
  strongConvex : StrongConvexOn Set.univ (1 - ε) (InterpolationSum.polarObjective p κ)
  /-- Helper for eq:polar-objective: positive quadratic growth at the origin. -/
  quadratic_growth : ∀ x, ((1 - ε) / 2) * ‖x‖ ^ 2 ≤ InterpolationSum.polarObjective p κ x
  /-- Helper for eq:polar-objective: the origin is the unique global minimizer. -/
  unique_minimizer : ∀ x,
    (∀ y, InterpolationSum.polarObjective p κ x ≤ InterpolationSum.polarObjective p κ y) ↔ x = 0
  /-- Helper for eq:polar-endpoint-data: the prescribed endpoint gradients have norm limit one. -/
  gradient_limit : Tendsto (fun k ↦ ‖p.gradient k‖) atTop (𝓝 1)

/-- Helper for eq:polar-objective: the accepted generic bump at the actual data is
exactly the previously defined polar bump. -/
theorem polarBump_eq_bump (p : Parameters) (κ : ℝ) (k : ℕ) :
    InterpolationSum.polarBump p κ k = InterpolationSum.bump p.point
      (InterpolationSum.polarSupportRadius p κ) (InterpolationSum.polarCoefficient p) k := by
  funext x
  rw [InterpolationSum.polarBump_apply, InterpolationSum.bump_apply,
    InterpolationSum.polarSupportRadius_apply, InterpolationSum.polarCoefficient_apply]

/-- Helper for eq:polar-objective: the exact actual pointwise sum equals the source tsum. -/
theorem polarPerturbation_eq_tsum {p : Parameters} {κ : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p)) (x : EuclideanSpace ℝ (Fin 2)) :
    InterpolationSum.polarPerturbation p κ x = ∑' k, InterpolationSum.polarBump p κ k x := by
  rw [InterpolationSum.polarPerturbation_def, InterpolationSum.perturbation_eq_tsum hg]
  apply tsum_congr
  intro k
  rw [polarBump_eq_bump]

/-- Helper for lem:polar-interpolation: each actual source bump has its true closed
support boundary, even though function and jet supports lie in disjoint open balls. -/
theorem tsupport_polarBump_subset_closedBall {p : Parameters} {κ : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p)) (k : ℕ) :
    tsupport (InterpolationSum.polarBump p κ k) ⊆
      Metric.closedBall (p.point k) (InterpolationSum.polarSupportRadius p κ k) := by
  rw [polarBump_eq_correction]
  exact ExplicitCutoff.tsupport_correction_subset_closedBall _ _ _ (hg.radius_pos k)

/-- Helper for eq:polar-interpolation-jets: the exact perturbation has zero value,
the prescribed correction gradient and zero Hessian at each actual center. -/
theorem perturbation_jets_at_center {p : Parameters} {κ : ℝ}
    (hg : InterpolationSum.Geometry p.point (InterpolationSum.polarSupportRadius p κ)
      (InterpolationSum.polarCoefficient p)) (k : ℕ) :
    InterpolationSum.polarPerturbation p κ (p.point k) = 0 ∧
      gradient (InterpolationSum.polarPerturbation p κ) (p.point k) =
        InterpolationSum.polarCoefficient p k ∧
      fderiv ℝ (gradient (InterpolationSum.polarPerturbation p κ)) (p.point k) = 0 := by
  rw [InterpolationSum.polarPerturbation_def]
  refine ⟨InterpolationSum.perturbation_center hg k,
    InterpolationSum.gradient_perturbation_center hg k, ?_⟩
  apply norm_eq_zero.mp
  rw [norm_fderiv_gradient_eq_norm_fderiv_fderiv,
    InterpolationSum.secondFDeriv_perturbation_center hg k, norm_zero]

/-- Helper for lem:polar-interpolation and eq:polar-endpoint-data: the accepted exact
C² gluing theorem and cutoff bounds prove the objective conclusions from prepared
actual data and disjoint OPEN balls. No regularity is an assumption. -/
theorem objectiveEstimatesOfPreparedData {p : Parameters} {κ A E ε Cχ : ℝ}
    (hp : PreparedData p κ A E) (hA : 0 ≤ A) (hχ : CutoffBounds Cχ)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball (p.point k) (InterpolationSum.polarSupportRadius p κ k)))
    (hε : ε < 1) (hsmall : (Cχ * (A / κ)) * p.scale 0 ≤ ε) :
    ObjectiveEstimates p κ ε (Cχ * (A / κ)) (2 * Cχ * (A * κ ^ (-3 / 2 : ℝ))) := by
  have hg := hp.geometry hballs
  have hB : 0 ≤ (A / κ) * p.scale 0 :=
    mul_nonneg (div_nonneg hA hp.support_pos.le) (ScaleTails.scale_nonneg p 0)
  have hM : 0 ≤ A * κ ^ (-3 / 2 : ℝ) := mul_nonneg hA (Real.rpow_nonneg hp.support_pos.le _)
  obtain ⟨hsize, hholder⟩ := hχ.estimates p.point (InterpolationSum.polarSupportRadius p κ)
    (InterpolationSum.polarCoefficient p) hg ((A / κ) * p.scale 0)
      (A * κ ^ (-3 / 2 : ℝ)) hB hM hp.ratio_bound hp.holder_bound
  have hsizeActual : ∀ x,
      ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x‖ ≤
        (Cχ * (A / κ)) * p.scale 0 := by
    intro x
    rw [InterpolationSum.polarPerturbation_def]
    simpa only [mul_assoc] using hsize x
  have hholderActual : ∀ x y,
      ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x -
        fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) y‖ ≤
          (2 * Cχ * (A * κ ^ (-3 / 2 : ℝ))) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    rw [InterpolationSum.polarPerturbation_def]
    exact hholder
  have hsmallActual : ∀ x,
      ‖fderiv ℝ (fderiv ℝ (InterpolationSum.polarPerturbation p κ)) x‖ ≤ ε :=
    fun x ↦ (hsizeActual x).trans hsmall
  obtain ⟨hHessian, hconvex, hgrowth⟩ := objective_convexity_of_small_bound hg hε hsmallActual
  have hzero : InterpolationSum.polarObjective p κ 0 = 0 := by
    rw [InterpolationSum.polarObjective_def]
    exact InterpolationSum.objective_zero hg
  have hregularPerturbation : ContDiff ℝ 2 (InterpolationSum.polarPerturbation p κ) := by
    rw [InterpolationSum.polarPerturbation_def]
    exact InterpolationSum.contDiff_perturbation hg
  have hregularObjective : ContDiff ℝ 2 (InterpolationSum.polarObjective p κ) := by
    rw [InterpolationSum.polarObjective_def]
    exact InterpolationSum.contDiff_objective hg
  have hdisk : ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ≤ 1 →
      InterpolationSum.polarObjective p κ x = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    intro x hx
    rw [InterpolationSum.polarObjective_def]
    exact InterpolationSum.objective_eq_quadratic_of_norm_le_one hg hx
  have hpositive : 0 < (1 - ε) / 2 := half_pos (sub_pos.mpr hε)
  exact ⟨hg, contDiff_polarBump p κ, tsupport_polarBump_subset_closedBall hg,
    polarPerturbation_eq_tsum hg, hregularPerturbation, hregularObjective,
    fun x hx ↦ perturbation_jets_on_disk hg hx.le, perturbation_jets_at_center hg,
    objective_endpoint hp hg, hdisk, hzero, hsizeActual,
    objective_hessian_bound hg hsizeActual,
    fun x ↦ (objective_hessian_bound hg hsizeActual x).trans hsmall,
    hholderActual, objective_hessian_holder hg hholderActual, hHessian, hconvex, hgrowth,
    unique_minimizer_of_quadratic_growth hpositive hzero hgrowth, hp.gradient_limit⟩

/-- Helper for eq:polar-support-radii and lem:polar-interpolation: actual source
separation fixes a positive support coefficient, and all remaining actual data estimates
hold uniformly after the final natural starting-index threshold. -/
theorem actualInterpolationData :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ κ > 0, ∃ A > 0, ∃ E > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        PreparedData p κ A E ∧ Set.univ.PairwiseDisjoint
          (fun k ↦ Metric.ball (p.point k) (InterpolationSum.polarSupportRadius p κ k)) := by
  obtain ⟨η₀, hη₀, hprepared⟩ := actualPreparedData
  obtain ⟨η₁, hη₁, hgeometry⟩ := PointGeometry.polarPointGeometry
  refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨A, hA, E, hE, hprepareκ⟩ := hprepared νStar hnear₀
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, separation, hseparation, J₁, hJ₁, hpoints⟩ :=
    hgeometry νStar hnear₁
  let κ := separation / 4
  have hκ : 0 < κ := by positivity
  have hsmall : 2 * κ ≤ separation := by
    dsimp only [κ]
    linarith
  obtain ⟨J₀, hJ₀, hprepare⟩ := hprepareκ κ hκ
  refine ⟨κ, hκ, A, hA, E, hE, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hprep := hprepare j₀ ((le_max_left J₀ J₁).trans hj₀)
  have hpoint := (hpoints j₀ ((le_max_right J₀ J₁).trans hj₀)).2
  exact ⟨hprep, supportBalls_disjoint_of_separation _ hκ.le hsmall hpoint.separate⟩

/-- lem:polar-interpolation and eq:polar-objective and eq:polar-endpoint-data:
the manuscript's exact actual correction sum is C² across the unit circle, has globally
half-Hölder Hessian, and realizes the original values, gradients and identity Hessians.
For the fixed support parameter chosen after νStar, every accuracy `0 < ε < 1` is attained
by one later natural threshold, uniformly over all larger starting indices. The resulting
objective is uniformly convex with unique origin minimizer and `f(0) = 0`. -/
theorem polarObjectiveEstimates :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ κ > 0, ∃ C > 0, ∃ H > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
          ObjectiveEstimates (Parameters.of j₀ νStar) κ ε C H := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_positive_cutoff_bounds
  obtain ⟨η, hη, hactual⟩ := actualInterpolationData
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨κ, hκ, A, hA, E, _, J₀, hJ₀, hdata⟩ := hactual νStar hnear
  let C := Cχ * (A / κ)
  let H := 2 * Cχ * (A * κ ^ (-3 / 2 : ℝ))
  have hC : 0 < C := mul_pos hCχ (div_pos hA hκ)
  have hH : 0 < H := by
    have hpower := Real.rpow_pos_of_pos hκ (-3 / 2 : ℝ)
    positivity
  refine ⟨κ, hκ, C, hC, H, hH, ?_⟩
  intro ε hε hεone
  have hcutoff : 0 < ε / C := div_pos hε hC
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold _ hcutoff
  refine ⟨max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  obtain ⟨hprepared, hballs⟩ := hdata j₀ ((le_max_left J₀ J₁).trans hj₀)
  have hzero : (Parameters.of j₀ νStar).scale 0 < ε / C :=
    hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀)
  have hsmall : C * (Parameters.of j₀ νStar).scale 0 ≤ ε := by
    nlinarith [(lt_div_iff₀ hC).mp hzero]
  exact objectiveEstimatesOfPreparedData hprepared hA.le hχ hballs hεone hsmall

/-- Helper for eq:polar-objective: the source accuracy ε = 1/2 gives the stated
uniformly convex actual objective, with all endpoint and Hölder conclusions. -/
theorem polarHalfObjective :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ κ > 0, ∃ C > 0, ∃ H > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ObjectiveEstimates (Parameters.of j₀ νStar) κ (1 / 2) C H := by
  obtain ⟨η, hη, hobjective⟩ := polarObjectiveEstimates
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨κ, hκ, C, hC, H, hH, haccuracy⟩ := hobjective νStar hnear
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  exact ⟨κ, hκ, C, hC, H, hH, haccuracy (1 / 2) hhalf hhalfOne⟩

end DFP.Polar.ActualObjective

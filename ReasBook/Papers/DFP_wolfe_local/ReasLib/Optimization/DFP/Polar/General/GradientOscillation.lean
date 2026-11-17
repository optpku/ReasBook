module

public import ReasLib.Optimization.DFP.Polar.General.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.SequenceAsymptotics

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.General.GradientOscillation

/-- Helper for sec:known-results: exponential Taylor error and a first-order
coefficient error retain one quadratic source-scale bound. -/
theorem exp_linear_error {q L v t Q E : ℝ} (hv : 0 ≤ v)
    (hq : |q| ≤ Q) (hsmall : |q * v| ≤ 1) (hscale : v ^ 2 ≤ t ^ 2)
    (hlinear : |q - L| * v ≤ E * t ^ 2) :
    |Real.exp (q * v) - 1 - L * v| ≤ (Q ^ 2 + E) * t ^ 2 := by
  have htaylor := Real.abs_exp_sub_one_sub_id_le hsmall
  have hqSquare : q ^ 2 ≤ Q ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg q) hq 2
    simpa only [sq_abs] using h
  have hquadratic : (q * v) ^ 2 ≤ Q ^ 2 * t ^ 2 := by
    calc
      (q * v) ^ 2 = q ^ 2 * v ^ 2 := mul_pow q v 2
      _ ≤ Q ^ 2 * v ^ 2 := mul_le_mul_of_nonneg_right hqSquare (sq_nonneg _)
      _ ≤ Q ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
  have hidentity : Real.exp (q * v) - 1 - L * v =
      (Real.exp (q * v) - 1 - q * v) + (q - L) * v := by ring
  rw [hidentity]
  calc
    |(Real.exp (q * v) - 1 - q * v) + (q - L) * v| ≤
        |Real.exp (q * v) - 1 - q * v| + |(q - L) * v| := abs_add_le _ _
    _ ≤ (q * v) ^ 2 + E * t ^ 2 := by
      rw [abs_mul, abs_of_nonneg hv]
      exact add_le_add htaylor hlinear
    _ ≤ (Q ^ 2 + E) * t ^ 2 := by nlinarith

/-- Helper for sec:known-results: division by a radius factor close to one
preserves a source-scale error when the numerator stays bounded. -/
theorem quotient_error {z R target t C U : ℝ} (hR : 1 ≤ R) (hz : |z| ≤ 2)
    (hdefect : R - 1 ≤ U * t ^ 2) (herror : |z - target| ≤ C * t ^ 2) :
    |z / R - target| ≤ (C + 2 * U) * t ^ 2 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hdiff : z / R - z = -z * ((R - 1) / R) := by
    field_simp
    ring
  have hdefectNonneg : 0 ≤ (R - 1) / R := div_nonneg (sub_nonneg.mpr hR) hRpos.le
  have hdefectSmall : (R - 1) / R ≤ R - 1 := div_le_self (sub_nonneg.mpr hR) hR
  have hquotient : |z / R - z| ≤ 2 * U * t ^ 2 := by
    rw [hdiff, abs_mul, abs_neg, abs_of_nonneg hdefectNonneg]
    calc
      |z| * ((R - 1) / R) ≤ 2 * ((R - 1) / R) :=
        mul_le_mul_of_nonneg_right hz hdefectNonneg
      _ ≤ 2 * (U * t ^ 2) :=
        mul_le_mul_of_nonneg_left (hdefectSmall.trans hdefect) zero_le_two
      _ = _ := by ring
  have hsum := abs_sub_le (z / R) z target
  nlinarith

/-- Helper for sec:known-results: the actual cycle radial decrement upper
bound controls each radius-factor defect without an extra asymptotic premise. -/
theorem radiusFactor_defect_le {R r next U t : ℝ}
    (hR : 1 ≤ R) (hnext : 1 ≤ next) (hbalance : r = R * next)
    (hdrop : r - next ≤ U * t ^ 2) : R - 1 ≤ U * t ^ 2 := by
  have hproduct := mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hnext)
  rw [hbalance] at hdrop
  nlinarith

/-- Helper for sec:known-results: the selected feedback coefficient at the
equilibrium is positive for every allowed exponent and Wolfe base. -/
theorem feedbackPotential_base_pos (p : Parameters) (hβ : 0 < p.beta) :
    0 < p.feedbackPotential p.gammaStar := by
  have hν : 0 < p.inverseParameter p.gammaStar := by
    rw [p.inverseParameter_gammaStar]
    exact sub_pos.mpr p.base.one_lt_ell
  exact p.feedbackPotential_pos hβ p.gammaStar_pos hν

/-- Helper for sec:known-results: the same actual odd multiplier and its
reciprocal have opposite linear source terms and uniform quadratic errors.
The error constant is chosen before the initial index. -/
theorem existsMultiplierErrors (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ j0 : ℕ, 0 < j0 → ∀ N : ℝ,
      Continuation.TrajectoryBounds p j0 N M → ∀ᶠ j in atTop,
        |(p.withStartIndex j0).oddMultiplier j - 1 +
            p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta)| ≤
          C * scale p.beta j0 j ^ 2 ∧
        |((p.withStartIndex j0).oddMultiplier j)⁻¹ - 1 -
            p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta)| ≤
          C * scale p.beta j0 j ^ 2 := by
  let L := p.feedbackPotential p.gammaStar
  let Q := |L| + 1
  have hQ : 0 < Q := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  have hbig := (p.feedbackPotential_analyticAt hβ).differentiableAt.isBigO_sub
  obtain ⟨D, hD, hDbound⟩ := hbig.exists_pos
  let C := Q ^ 2 + D * M
  have hC : 0 < C := add_pos_of_pos_of_nonneg (sq_pos_of_pos hQ) (mul_nonneg hD.le hM)
  refine ⟨C, hC, ?_⟩
  intro j0 hstart N htrajectory
  let q := p.withStartIndex j0
  let gamma : ℕ → ℝ := fun j ↦ (Continuation.stateAt p j0 j).1
  let v : ℕ → ℝ := fun j ↦ scale p.beta j0 j ^ (1 + p.beta)
  have hgamma : Tendsto gamma atTop (𝓝 p.gammaStar) := htrajectory.gamma_tendsto hβ hβone
  have hphi := (p.feedbackPotential_analyticAt hβ).continuousAt.tendsto.comp hgamma
  have hcoeff := hgamma.eventually hDbound.bound
  have habs := hphi.norm.eventually (Iio_mem_nhds (lt_add_one ‖L‖))
  have hv : Tendsto v atTop (𝓝 0) := by
    simpa only [v, scale_rpow_one_add hβ, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (Continuation.index_tendsto_atTop j0)
  have hproduct : Tendsto (fun j ↦ p.feedbackPotential (gamma j) * v j) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using hphi.mul hv
  have hproductNorm : Tendsto (fun j ↦ |p.feedbackPotential (gamma j) * v j|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, norm_zero] using hproduct.norm
  have hsmall := hproductNorm.eventually (Iio_mem_nhds zero_lt_one)
  have hfeedback (j : ℕ) :
      q.oddMultiplier j = Real.exp (-(p.feedbackPotential (gamma j) * v j)) := by
    rw [Parameters.oddMultiplier_def, Normalized.feedback_def]
    simp only [q, Parameters.inverseIndex_def, p.withStartIndex_startIndex,
      (p.withStartIndex_analyticData j0).2.2, gamma, Continuation.stateAt_def,
      v, scale_rpow_one_add hβ, neg_mul]
  filter_upwards [hcoeff, habs, hsmall] with j hDj hQj hsmallj
  have ht : 0 < scale p.beta j0 j := scale_pos p.beta hstart j
  have htone := scale_le_one hβ hstart j
  have hvpos : 0 < v j := Real.rpow_pos_of_pos ht _
  have hvt : v j ≤ scale p.beta j0 j := by
    have hexponent : (1 : ℝ) ≤ 1 + p.beta := by linarith
    simpa only [v, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge ht htone hexponent
  have hvSquare : v j ^ 2 ≤ scale p.beta j0 j ^ 2 := by nlinarith
  have hscaleBalance : scale p.beta j0 j ^ (1 - p.beta) * v j = scale p.beta j0 j ^ 2 := by
    have hexponent : (1 - p.beta) + (1 + p.beta) = (2 : ℝ) := by ring
    dsimp only [v]
    rw [← Real.rpow_add ht, hexponent, Real.rpow_two]
  have hslow : |gamma j - p.gammaStar| ≤ M * scale p.beta j0 j ^ (1 - p.beta) := by
    simpa only [gamma, Continuation.slowError_def] using htrajectory.slow_bound j
  have hlinear : |p.feedbackPotential (gamma j) - L| * v j ≤
      (D * M) * scale p.beta j0 j ^ 2 := by
    have hlocal : |p.feedbackPotential (gamma j) - L| ≤ D * |gamma j - p.gammaStar| := by
      simpa only [Real.norm_eq_abs] using hDj
    calc
      |p.feedbackPotential (gamma j) - L| * v j ≤
          (D * (M * scale p.beta j0 j ^ (1 - p.beta))) * v j :=
        mul_le_mul_of_nonneg_right
          (hlocal.trans (mul_le_mul_of_nonneg_left hslow hD.le)) hvpos.le
      _ = (D * M) * (scale p.beta j0 j ^ (1 - p.beta) * v j) := by ring
      _ = _ := by rw [hscaleBalance]
  have hbound : |p.feedbackPotential (gamma j)| ≤ Q := by
    simpa only [Real.norm_eq_abs, Function.comp_def, Q] using hQj.le
  have hsmall' : |p.feedbackPotential (gamma j) * v j| ≤ 1 := by
    simpa only [Real.norm_eq_abs, mul_zero, norm_zero] using hsmallj.le
  have hpositive := exp_linear_error hvpos.le hbound hsmall' hvSquare hlinear
  have hnegativeBound : |-p.feedbackPotential (gamma j)| ≤ Q := by rwa [abs_neg]
  have hnegativeSmall : |(-p.feedbackPotential (gamma j)) * v j| ≤ 1 := by
    simpa only [neg_mul, abs_neg] using hsmall'
  have hnegativeLinear : |-p.feedbackPotential (gamma j) - -L| * v j ≤
      (D * M) * scale p.beta j0 j ^ 2 := by
    simpa only [neg_sub_neg, abs_sub_comm] using hlinear
  have hnegative := exp_linear_error hvpos.le hnegativeBound hnegativeSmall
    hvSquare hnegativeLinear
  constructor
  · rw [hfeedback]
    simpa only [neg_mul, sub_neg_eq_add] using hnegative
  · rw [hfeedback, Real.exp_neg, inv_inv]
    exact hpositive


/-- Helper for sec:known-results: both actual gradient-norm quotients are
exactly the shared feedback or its reciprocal divided by the corresponding
source radius factor. -/
theorem gradientRatios_eq {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (h : RadiusProducts.SourceRadialData p j0 N M B K c U) (j : ℕ) :
    let q := p.withStartIndex j0
    ‖q.gradients (2 * j + 1)‖ / ‖q.gradients (2 * j)‖ =
        q.oddMultiplier j / q.radiusRatio (2 * j) ∧
      ‖q.gradients (2 * j + 2)‖ / ‖q.gradients (2 * j + 1)‖ =
        (q.oddMultiplier j)⁻¹ / q.radiusRatio (2 * j + 1) := by
  let q := p.withStartIndex j0
  have hr (k : ℕ) : 0 < q.radius k := zero_lt_one.trans (h.radii.above_one k)
  have hFactor (k : ℕ) : 0 < q.radiusRatio k := zero_lt_one.trans (h.factors k)
  have hbalance := q.radius_recurrence hFactor h.logarithms
  have hzNext : q.zeta (2 * j + 2) = 1 := by
    have hindex : 2 * j + 2 = 2 * (j + 1) := by omega
    rw [hindex, q.zeta_even]
  constructor
  · rw [q.gradients_norm _ (hr _).le, q.gradients_norm _ (hr _).le,
      q.zeta_odd, q.zeta_even, one_mul, hbalance (2 * j)]
    exact mul_div_mul_right _ _ (hr (2 * j + 1)).ne'
  · have hbalanceOdd : q.radius (2 * j + 1) =
        q.radiusRatio (2 * j + 1) * q.radius (2 * j + 2) := hbalance (2 * j + 1)
    rw [q.gradients_norm _ (hr _).le, q.gradients_norm _ (hr _).le,
      hzNext, q.zeta_odd, one_mul, hbalanceOdd]
    calc
      q.radius (2 * j + 2) /
          (q.oddMultiplier j * (q.radiusRatio (2 * j + 1) * q.radius (2 * j + 2))) =
          (1 * q.radius (2 * j + 2)) /
            ((q.oddMultiplier j * q.radiusRatio (2 * j + 1)) * q.radius (2 * j + 2)) := by
        rw [one_mul, mul_assoc]
      _ = 1 / (q.oddMultiplier j * q.radiusRatio (2 * j + 1)) :=
        mul_div_mul_right _ _ (hr (2 * j + 2)).ne'
      _ = (q.oddMultiplier j)⁻¹ / q.radiusRatio (2 * j + 1) := by
        simp only [mul_inv_rev, div_eq_mul_inv]
        ring

/-- Helper for sec:known-results: the two actual gradient quotients have the
source opposite linear terms and one common uniform quadratic error constant.
The constant precedes the starting index and concerns the same radial data. -/
theorem existsGradientRatioErrors (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {M U : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U) :
    ∃ C > 0, ∀ j0 : ℕ, 0 < j0 → ∀ N B K c : ℝ,
      RadiusProducts.SourceRadialData p j0 N M B K c U → ∀ᶠ j in atTop,
        let q := p.withStartIndex j0
        |‖q.gradients (2 * j + 1)‖ / ‖q.gradients (2 * j)‖ - 1 +
            p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta)| ≤
          C * scale p.beta j0 j ^ 2 ∧
        |‖q.gradients (2 * j + 2)‖ / ‖q.gradients (2 * j + 1)‖ - 1 -
            p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta)| ≤
          C * scale p.beta j0 j ^ 2 := by
  obtain ⟨Cexp, hCexp, hExp⟩ := existsMultiplierErrors p hβ hβone hM
  refine ⟨Cexp + 2 * U, add_pos_of_pos_of_nonneg hCexp (mul_nonneg zero_le_two hU), ?_⟩
  intro j0 hstart N B K c hdata
  let q := p.withStartIndex j0
  let L := p.feedbackPotential p.gammaStar
  let v : ℕ → ℝ := fun j ↦ scale p.beta j0 j ^ (1 + p.beta)
  have hz := hdata.trajectory.oddMultiplier_tendsto_one hβ hβone
  have hzInv : Tendsto (fun j ↦ (q.oddMultiplier j)⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hz.inv₀ one_ne_zero
  have hbound : ‖(1 : ℝ)‖ < 2 := by norm_num
  have hzBound := hz.norm.eventually (Iio_mem_nhds hbound)
  have hzInvBound := hzInv.norm.eventually (Iio_mem_nhds hbound)
  have hFactor (k : ℕ) : 0 < q.radiusRatio k := zero_lt_one.trans (hdata.factors k)
  have hbalance := q.radius_recurrence hFactor hdata.logarithms
  have hDefect (k : ℕ) : q.radiusRatio k - 1 ≤ U * scale p.beta j0 (k / 2) ^ 2 :=
    radiusFactor_defect_le (hdata.factors k).le (hdata.radii.above_one (k + 1)).le
      (hbalance k) (hdata.radii.drop_upper k)
  filter_upwards [hExp j0 hstart N hdata.trajectory, hzBound, hzInvBound] with j herrors hzb hizb
  have hEvenDefect : q.radiusRatio (2 * j) - 1 ≤ U * scale p.beta j0 j ^ 2 := by
    have hhalf : 2 * j / 2 = j := by omega
    simpa only [hhalf] using hDefect (2 * j)
  have hOddDefect : q.radiusRatio (2 * j + 1) - 1 ≤ U * scale p.beta j0 j ^ 2 := by
    have hhalf : (2 * j + 1) / 2 = j := by omega
    simpa only [hhalf] using hDefect (2 * j + 1)
  have hEvenShape (x : ℝ) : x - (1 - L * v j) = x - 1 + L * v j := by ring
  have hOddShape (x : ℝ) : x - (1 + L * v j) = x - 1 - L * v j := by ring
  have hEvenError : |q.oddMultiplier j - (1 - L * v j)| ≤ Cexp * scale p.beta j0 j ^ 2 := by
    simpa only [hEvenShape] using herrors.1
  have hOddError : |(q.oddMultiplier j)⁻¹ - (1 + L * v j)| ≤ Cexp * scale p.beta j0 j ^ 2 := by
    simpa only [hOddShape] using herrors.2
  have hEven := quotient_error (hdata.factors (2 * j)).le
    (le_of_lt hzb) hEvenDefect hEvenError
  have hOdd := quotient_error (hdata.factors (2 * j + 1)).le
    (le_of_lt hizb) hOddDefect hOddError
  have hquotients := gradientRatios_eq hdata j
  constructor
  · simpa only [hquotients.1, hEvenShape] using hEven
  · simpa only [hquotients.2, hOddShape] using hOdd

/-- Helper for sec:known-results: the two gradient quotient remainders are
quadratic in the source scale with the same constant, chosen before the
starting index. -/
theorem existsGradientRatioBigOWith (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) {M U : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U) :
    ∃ C > 0, ∀ j0 : ℕ, 0 < j0 → ∀ N B K c : ℝ,
      RadiusProducts.SourceRadialData p j0 N M B K c U →
        let q := p.withStartIndex j0
        Asymptotics.IsBigOWith C atTop
            (fun j ↦ ‖q.gradients (2 * j + 1)‖ / ‖q.gradients (2 * j)‖ - 1 +
              p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta))
            (fun j ↦ scale p.beta j0 j ^ 2) ∧
          Asymptotics.IsBigOWith C atTop
            (fun j ↦ ‖q.gradients (2 * j + 2)‖ / ‖q.gradients (2 * j + 1)‖ - 1 -
              p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta))
            (fun j ↦ scale p.beta j0 j ^ 2) := by
  obtain ⟨C, hC, herrors⟩ := existsGradientRatioErrors p hβ hβone hM hU
  refine ⟨C, hC, ?_⟩
  intro j0 hstart N B K c hdata
  constructor
  · apply Asymptotics.IsBigOWith.of_bound
    filter_upwards [herrors j0 hstart N B K c hdata] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scale p.beta j0 j))] using
      hj.1
  · apply Asymptotics.IsBigOWith.of_bound
    filter_upwards [herrors j0 hstart N B K c hdata] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scale p.beta j0 j))] using
      hj.2

/-- Helper for sec:known-results: both actual gradient quotients have their
opposite feedback leading terms up to a quadratic source-scale remainder. -/
theorem gradientRatioErrors_isBigO (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) {j0 : ℕ} (hstart : 0 < j0) {N M B K c U : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hdata : RadiusProducts.SourceRadialData p j0 N M B K c U) :
    let q := p.withStartIndex j0
    Asymptotics.IsBigO atTop
        (fun j ↦ ‖q.gradients (2 * j + 1)‖ / ‖q.gradients (2 * j)‖ - 1 +
          p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta))
        (fun j ↦ scale p.beta j0 j ^ 2) ∧
      Asymptotics.IsBigO atTop
        (fun j ↦ ‖q.gradients (2 * j + 2)‖ / ‖q.gradients (2 * j + 1)‖ - 1 -
          p.feedbackPotential p.gammaStar * scale p.beta j0 j ^ (1 + p.beta))
        (fun j ↦ scale p.beta j0 j ^ 2) := by
  obtain ⟨C, _, hbounds⟩ := existsGradientRatioBigOWith p hβ hβone hM hU
  exact ⟨(hbounds j0 hstart N B K c hdata).1.isBigO,
    (hbounds j0 hstart N B K c hdata).2.isBigO⟩

/-- Helper for sec:known-results: a quadratic source-scale error is eventually
smaller than any positive multiple of `τ^(1 + β)` when `0 < β < 1`. -/
private theorem quadraticScale_lt_leading {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    (C : ℝ) {L : ℝ} (hL : 0 < L) {j0 : ℕ} (hstart : 0 < j0) :
    ∀ᶠ j in atTop,
      C * scale β j0 j ^ 2 < L * scale β j0 j ^ (1 + β) := by
  have hdecay : Tendsto (fun j ↦ C * scale β j0 j ^ (1 - β)) atTop (𝓝 0) := by
    simpa only [scale_rpow_one_sub, Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (slowExponent_pos hβ hβone)).comp
        (Continuation.index_tendsto_atTop j0)).const_mul C
  filter_upwards [hdecay.eventually (Iio_mem_nhds hL)] with j hj
  have ht := scale_pos β hstart j
  have hpower : scale β j0 j ^ (1 - β) * scale β j0 j ^ (1 + β) =
      scale β j0 j ^ 2 := by
    have hexponent : (1 - β) + (1 + β) = (2 : ℝ) := by ring
    rw [← Real.rpow_add ht, hexponent, Real.rpow_two]
  have h := mul_lt_mul_of_pos_right hj (Real.rpow_pos_of_pos ht (1 + β))
  simpa only [mul_assoc, hpower] using h

/-- Helper for sec:known-results: the prescribed gradient norms are positive
on the same actual radial trajectory. -/
private theorem gradientNorm_pos {p : Parameters} {j0 : ℕ} {N M B K c U : ℝ}
    (hdata : RadiusProducts.SourceRadialData p j0 N M B K c U) (k : ℕ) :
    0 < ‖(p.withStartIndex j0).gradients k‖ := by
  have hr : 0 < (p.withStartIndex j0).radius k :=
    zero_lt_one.trans (hdata.radii.above_one k)
  rw [(p.withStartIndex j0).gradients_norm k hr.le]
  exact mul_pos ((p.withStartIndex j0).zeta_pos k) hr

/-- Helper for sec:known-results: the actual gradient norms eventually decrease
on every even-to-odd step and increase on every odd-to-even step. -/
theorem gradientPhaseSigns (p : Parameters) (hβ : 0 < p.beta) (hβone : p.beta < 1)
    {j0 : ℕ} (hstart : 0 < j0) {N M B K c U : ℝ} (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hdata : RadiusProducts.SourceRadialData p j0 N M B K c U) :
    ∀ᶠ j in atTop,
      ‖(p.withStartIndex j0).gradients (2 * j + 1)‖ <
          ‖(p.withStartIndex j0).gradients (2 * j)‖ ∧
        ‖(p.withStartIndex j0).gradients (2 * j + 1)‖ <
          ‖(p.withStartIndex j0).gradients (2 * j + 2)‖ := by
  obtain ⟨C, _, herrors⟩ := existsGradientRatioErrors p hβ hβone hM hU
  have hdominance := quadraticScale_lt_leading hβ hβone C
    (feedbackPotential_base_pos p hβ) hstart
  filter_upwards [herrors j0 hstart N B K c hdata, hdominance] with j hj hsmall
  have heven : ‖(p.withStartIndex j0).gradients (2 * j + 1)‖ /
      ‖(p.withStartIndex j0).gradients (2 * j)‖ < 1 := by
    have hupper := (abs_le.mp hj.1).2
    linarith
  have hodd : 1 < ‖(p.withStartIndex j0).gradients (2 * j + 2)‖ /
      ‖(p.withStartIndex j0).gradients (2 * j + 1)‖ := by
    have hlower := (abs_le.mp hj.2).1
    linarith
  exact ⟨(div_lt_one (gradientNorm_pos hdata (2 * j))).mp heven,
    (one_lt_div (gradientNorm_pos hdata (2 * j + 1))).mp hodd⟩

/-- Helper for sec:known-results: the gradient norms of the actual trajectory
are neither eventually nonincreasing nor eventually nondecreasing. -/
theorem gradientNorm_not_eventually_monotone (p : Parameters) (hβ : 0 < p.beta)
    (hβone : p.beta < 1) {j0 : ℕ} (hstart : 0 < j0) {N M B K c U : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U)
    (hdata : RadiusProducts.SourceRadialData p j0 N M B K c U) :
    (¬ ∀ᶠ k in atTop, ‖(p.withStartIndex j0).gradients (k + 1)‖ ≤
      ‖(p.withStartIndex j0).gradients k‖) ∧
    (¬ ∀ᶠ k in atTop, ‖(p.withStartIndex j0).gradients k‖ ≤
      ‖(p.withStartIndex j0).gradients (k + 1)‖) := by
  have hphase := gradientPhaseSigns p hβ hβone hstart hM hU hdata
  exact ⟨DFP.Polar.SequenceAsymptotics.not_eventually_nonincreasing_of_odd_increases
      (fun k ↦ ‖(p.withStartIndex j0).gradients k‖) (hphase.mono fun _ hj ↦ hj.2),
    DFP.Polar.SequenceAsymptotics.not_eventually_nondecreasing_of_even_decreases
      (fun k ↦ ‖(p.withStartIndex j0).gradients k‖) (hphase.mono fun _ hj ↦ hj.1)⟩

end DFP.Polar.General.GradientOscillation

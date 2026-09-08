module

public import Mathlib.Analysis.Complex.Angle

public section

namespace Complex

/-- The squared distance between scaled unit complex numbers splits into radial and angular
contributions. -/
private lemma normRealMulSubRealMulSq (r s : ℝ) (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(r : ℂ) * u - (s : ℂ) * v‖ ^ 2 = (r - s) ^ 2 + r * s * ‖u - v‖ ^ 2 := by
  -- Express both squared norms through `normSq`, where the radial algebra is polynomial.
  have huSq : normSq u = 1 := by
    simp only [normSq_eq_norm_sq, hu, one_pow]
  have hvSq : normSq v = 1 := by
    simp only [normSq_eq_norm_sq, hv, one_pow]
  have hcross :
      ((r : ℂ) * u) * (starRingEnd ℂ) ((s : ℂ) * v) =
        ((r * s : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) := by
    rw [map_mul, conj_ofReal, ofReal_mul]
    ring
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_sub, normSq_sub,
    normSq_mul, normSq_mul, normSq_ofReal, normSq_ofReal, huSq, hvSq, hcross]
  simp only [mul_one, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  ring

/-- Scaling two unit complex numbers by radii at least `rMin` cannot reduce their chord below
`rMin` times the unit chord. -/
private lemma minRadiusMulNormSubLe {rMin r s : ℝ} {u v : ℂ} (hrMin : 0 ≤ rMin)
    (hr : rMin ≤ r) (hs : rMin ≤ s) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    rMin * ‖u - v‖ ≤ ‖(r : ℂ) * u - (s : ℂ) * v‖ := by
  -- Compare nonnegative squares, using the exact radial-angular decomposition.
  rw [← sq_le_sq₀ (mul_nonneg hrMin (norm_nonneg _)) (norm_nonneg _),
    normRealMulSubRealMulSq r s u v hu hv, mul_pow]
  have hrs : rMin ^ 2 ≤ r * s := by
    nlinarith
  have hang : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
  nlinarith

/-- A real angle of absolute value at most `Real.pi` has principal representative with the same
absolute value. -/
private lemma absAngleToRealCoeEqAbsOfLePi (t : ℝ) (ht : |t| ≤ Real.pi) :
    |((t : Real.Angle).toReal)| = |t| := by
  -- Split by the sign of `t` so that the endpoint-aware angle lemmas apply directly.
  rcases le_total 0 t with htNonneg | htNonpos
  · rw [abs_of_nonneg htNonneg]
    have htLe : t ≤ Real.pi := by
      simpa only [abs_of_nonneg htNonneg] using ht
    exact Real.Angle.abs_toReal_coe_eq_self_iff.2 ⟨htNonneg, htLe⟩
  · rw [abs_of_nonpos htNonpos]
    have hnegNonneg : 0 ≤ -t := neg_nonneg.2 htNonpos
    have hnegLe : -t ≤ Real.pi := by
      simpa only [abs_of_nonpos htNonpos] using ht
    simpa only [Real.Angle.coe_neg, neg_neg] using
      (Real.Angle.abs_toReal_neg_coe_eq_self_iff.2 ⟨hnegNonneg, hnegLe⟩)

/-- Points whose radii lie in a common positive annulus are separated by their principal
circular angular distance, with coefficient `2 * rMin / Real.pi`. -/
theorem polarChordLowerBound {rMin rMax r₁ r₂ θ₁ θ₂ : ℝ} (hrMin : 0 < rMin)
    (hr₁ : r₁ ∈ Set.Icc rMin rMax) (hr₂ : r₂ ∈ Set.Icc rMin rMax) :
    2 * rMin / Real.pi * |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)| ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
  -- First obtain the unit-circle chord estimate for the principal angular separation.
  have hu : ‖Complex.exp (θ₁ * Complex.I)‖ = 1 := norm_exp_ofReal_mul_I θ₁
  have hv : ‖Complex.exp (θ₂ * Complex.I)‖ = 1 := norm_exp_ofReal_mul_I θ₂
  have hangle :
      2 / Real.pi * |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)| ≤
        ‖Complex.exp (θ₁ * Complex.I) - Complex.exp (θ₂ * Complex.I)‖ := by
    rw [Real.Angle.toReal_coe, ← angle_exp_exp]
    exact mul_angle_le_norm_sub hu hv
  -- Multiplication by the positive lower radius preserves that estimate, and the radial
  -- comparison transports it from the unit circle to the annulus.
  calc
    2 * rMin / Real.pi * |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)| =
        rMin * (2 / Real.pi * |(((θ₁ - θ₂ : ℝ) : Real.Angle).toReal)|) := by
          ring
    _ ≤ rMin * ‖Complex.exp (θ₁ * Complex.I) - Complex.exp (θ₂ * Complex.I)‖ :=
      mul_le_mul_of_nonneg_left hangle hrMin.le
    _ ≤ _ := minRadiusMulNormSubLe hrMin.le hr₁.1 hr₂.1 hu hv

/-- When the absolute angular difference is at most `Real.pi`, the annular chord bound
is expressed directly in terms of that unwrapped difference. -/
theorem polarChordLowerBoundOfAbsSubLePi {rMin rMax r₁ r₂ θ₁ θ₂ : ℝ}
    (hrMin : 0 < rMin) (hr₁ : r₁ ∈ Set.Icc rMin rMax) (hr₂ : r₂ ∈ Set.Icc rMin rMax)
    (hθ : |θ₁ - θ₂| ≤ Real.pi) :
    2 * rMin / Real.pi * |θ₁ - θ₂| ≤
      ‖(r₁ : ℂ) * Complex.exp (θ₁ * Complex.I) -
        (r₂ : ℂ) * Complex.exp (θ₂ * Complex.I)‖ := by
  -- Normalize the raw small angular difference to its principal representative.
  rw [← absAngleToRealCoeEqAbsOfLePi (θ₁ - θ₂) hθ]
  exact polarChordLowerBound hrMin hr₁ hr₂

end Complex

module

public import ReasLib.Optimization.DFP.Polar.ScaleTails
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.IsolatedZeros

public section

noncomputable section

open Filter
open scoped Topology BigOperators

namespace DFP.Polar.General

/-- Helper for eq:polar-angles: the power-law scale for a prescribed Hessian exponent `β`. -/
def scale (β : ℝ) (j0 j : ℕ) : ℝ :=
  ((j0 + j : ℕ) : ℝ) ^ (-1 / (1 + β))

/-- Helper for eq:polar-angles: the analytic extension of the normalized angular increment. -/
def angleFactor (β v : ℝ) : ℝ :=
  ((1 + β) / β) * dslope (fun u : ℝ ↦ (1 + u) ^ (β / (1 + β))) 0 v

/-- Helper for lem:polar-continuation: the normalized angular increment is analytic at zero. -/
theorem analyticAt_angleFactor_zero (β : ℝ) : AnalyticAt ℝ (angleFactor β) 0 := by
  exact (analyticAt_const.mul
    Real.one_add_rpow_hasFPowerSeriesAt_zero.has_fpower_series_dslope_fslope.analyticAt)

/-- Helper for eq:polar-angles: away from zero the angular factor has the source
quotient formula. -/
theorem angleFactor_of_ne_zero (β : ℝ) {v : ℝ} (hv : v ≠ 0) :
    angleFactor β v = (1 + β) / (β * v) * ((1 + v) ^ (β / (1 + β)) - 1) := by
  rw [angleFactor, dslope_of_ne _ hv, slope_def_field]
  simp only [add_zero, Real.one_rpow, sub_zero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Helper for eq:polar-angles: the analytic angular factor is normalized to one at zero. -/
theorem angleFactor_zero {β : ℝ} (hβ : 0 < β) : angleFactor β 0 = 1 := by
  have hden : 1 + β ≠ 0 := by
    positivity
  have hbase : (1 : ℝ) + 0 ≠ 0 ∨ 1 ≤ β / (1 + β) := by
    left
    norm_num
  have hderiv : HasDerivAt (fun u : ℝ ↦ (1 + u) ^ (β / (1 + β)))
      (β / (1 + β)) 0 := by
    simpa only [id_eq, one_mul, add_zero, Real.one_rpow, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const hbase
  rw [angleFactor, dslope_same, hderiv.deriv]
  field_simp [hβ.ne', hden]

/-- Helper for lem:polar-continuation: the angular factor has the source linear
Taylor coefficient at the removable singularity. -/
theorem hasDerivAt_angleFactor_zero {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (angleFactor β) (-1 / (2 * (1 + β))) 0 := by
  have hden : 1 + β ≠ 0 := by
    positivity
  have hseries := HasFPowerSeriesAt.has_fpower_series_dslope_fslope
    (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := β / (1 + β)))
  have hderiv : HasDerivAt
      (dslope (fun u : ℝ ↦ (1 + u) ^ (β / (1 + β))) 0)
      ((binomialSeries ℝ (β / (1 + β))).fslope.coeff 1) 0 :=
    hseries.hasDerivAt
  rw [FormalMultilinearSeries.coeff_fslope] at hderiv
  simp only [binomialSeries, FormalMultilinearSeries.coeff_ofScalars] at hderiv
  have hcoefficient : ((1 + β) / β) * Ring.choose (β / (1 + β)) (1 + 1) =
      -1 / (2 * (1 + β)) := by
    rw [Ring.choose_eq_smul]
    norm_num [descPochhammer_succ_right, Polynomial.smeval_mul,
      Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_one]
    field_simp [hβ.ne', hden]
    ring
  have hfactor := hderiv.const_mul ((1 + β) / β)
  rw [hcoefficient] at hfactor
  exact hfactor

/-- Helper for eq:polar-angles: the normalized angular increment differs from one
by at most first order in the reciprocal index. -/
theorem angleFactor_sub_one_isBigO {β : ℝ} (hβ : 0 < β) :
    (fun v ↦ angleFactor β v - 1) =O[𝓝 (0 : ℝ)] (fun v : ℝ ↦ v) := by
  simpa only [angleFactor_zero hβ, sub_zero] using
    (hasDerivAt_angleFactor_zero hβ).isBigO_sub

/-- Helper for eq:polar-angles: a positive real index has the exact normalized angular
power increment from the source construction. -/
theorem powerIncrement_eq_angleFactor {β n : ℝ} (hβ : 0 < β) (hn : 0 < n) :
    ((1 + β) / β) * ((n + 1) ^ (β / (1 + β)) - n ^ (β / (1 + β))) =
      n ^ (-1 / (1 + β)) * angleFactor β n⁻¹ := by
  have hden : 1 + β ≠ 0 := by
    positivity
  have hnext : n + 1 = n * (1 + n⁻¹) := by
    rw [mul_add, mul_one, mul_inv_cancel₀ hn.ne']
  have hfactor : 0 ≤ 1 + n⁻¹ := by
    positivity
  have hexponent : β / (1 + β) = -1 / (1 + β) + 1 := by
    field_simp [hden]
    ring
  have hpower : n ^ (β / (1 + β)) = n ^ (-1 / (1 + β)) * n := by
    rw [hexponent, Real.rpow_add_one hn.ne']
  rw [hnext, Real.mul_rpow hn.le hfactor, angleFactor_of_ne_zero β (inv_ne_zero hn.ne'),
    hpower]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Helper for eq:polar-angles: the total real-power formula for the prescribed scale. -/
theorem scale_def (β : ℝ) (j0 j : ℕ) :
    scale β j0 j = ((j0 + j : ℕ) : ℝ) ^ (-1 / (1 + β)) := by
  rfl

/-- Helper for eq:polar-angles: the exact source angular power increment at a cycle index. -/
theorem powerIncrement_eq_scale_angleFactor {β : ℝ} (hβ : 0 < β)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    ((1 + β) / β) *
        ((((j0 + (j + 1) : ℕ) : ℝ)) ^ (β / (1 + β)) -
          (((j0 + j : ℕ) : ℝ)) ^ (β / (1 + β))) =
      scale β j0 j * angleFactor β (((j0 + j : ℕ) : ℝ))⁻¹ := by
  have hn : (0 : ℝ) < ((j0 + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  simpa only [scale_def, Nat.cast_add, Nat.cast_one, add_assoc] using
    powerIncrement_eq_angleFactor hβ hn

/-- Helper for eq:polar-angles: the prescribed scale is nonnegative at every index. -/
theorem scale_nonneg (β : ℝ) (j0 j : ℕ) : 0 ≤ scale β j0 j := by
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Helper for eq:polar-angles: positive starting indices give strictly positive scales. -/
theorem scale_pos (β : ℝ) {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    0 < scale β j0 j := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.add_pos_left hstart j)) _

/-- Helper for eq:polar-angles: every real power of the scale retains an exact power law. -/
theorem scale_rpow (β : ℝ) (j0 j : ℕ) (q : ℝ) :
    scale β j0 j ^ q = ((j0 + j : ℕ) : ℝ) ^ (-q / (1 + β)) := by
  rw [scale_def, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- Helper for eq:polar-angles: natural powers are special cases of the exact real-power law. -/
theorem scale_pow (β : ℝ) (j0 j m : ℕ) :
    scale β j0 j ^ m = ((j0 + j : ℕ) : ℝ) ^ (-(m : ℝ) / (1 + β)) := by
  rw [← Real.rpow_natCast, scale_rpow]

/-- Helper for eq:polar-angles: the Hessian correction scale is exactly the reciprocal index. -/
theorem scale_rpow_one_add {β : ℝ} (hβ : 0 < β) (j0 j : ℕ) :
    scale β j0 j ^ (1 + β) = (((j0 + j : ℕ) : ℝ))⁻¹ := by
  have hden : 1 + β ≠ 0 := by
    positivity
  rw [scale_rpow, neg_div, div_self hden, Real.rpow_neg_one]

/-- Helper for eq:polar-angles: scales decrease as the cycle index increases. -/
theorem scale_antitone {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) :
    Antitone (scale β j0) := by
  intro i j hij
  have hpositive : (0 : ℝ) < ((j0 + i : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart i)
  have hindices : ((j0 + i : ℕ) : ℝ) ≤ ((j0 + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hij j0
  have hexponent : -1 / (1 + β) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zero_le_one)
      (add_pos zero_lt_one hβ).le
  exact Real.rpow_le_rpow_of_nonpos hpositive hindices hexponent

/-- Helper for eq:polar-angles: every positive-index scale is at most one. -/
theorem scale_le_one {β : ℝ} (hβ : 0 < β) {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scale β j0 j ≤ 1 := by
  have hindex : (1 : ℝ) ≤ ((j0 + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  have hexponent : -1 / (1 + β) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr zero_le_one)
      (add_pos zero_lt_one hβ).le
  rw [scale_def]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_of_nonpos zero_lt_one hindex hexponent

/-- Helper for eq:polar-angles: the prescribed positive powers decay to zero. -/
theorem scale_tendsto_zero {β : ℝ} (hβ : 0 < β) (j0 : ℕ) :
    Tendsto (scale β j0) atTop (𝓝 0) := by
  have hindex : Tendsto (fun j : ℕ ↦ ((j0 + j : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, add_comm] using
      tendsto_atTop_add_const_right atTop (j0 : ℝ) tendsto_natCast_atTop_atTop
  have hexponent : (0 : ℝ) < 1 / (1 + β) := by
    positivity
  rw [funext (scale_def β j0)]
  simpa only [neg_div, Function.comp_def] using
    (tendsto_rpow_neg_atTop hexponent).comp hindex

/-- Helper for lem:polar-continuation: a successor index changes scale by the exact source ratio. -/
theorem scale_succ (β : ℝ) {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scale β j0 (j + 1) =
      scale β j0 j * (1 + (((j0 + j : ℕ) : ℝ))⁻¹) ^ (-1 / (1 + β)) := by
  have hn : (0 : ℝ) < ((j0 + j : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.add_pos_left hstart j)
  have hnext : ((j0 + (j + 1) : ℕ) : ℝ) =
      ((j0 + j : ℕ) : ℝ) * (1 + (((j0 + j : ℕ) : ℝ))⁻¹) := by
    rw [← Nat.add_assoc, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
      mul_inv_cancel₀ hn.ne']
  have hfactor : 0 ≤ 1 + (((j0 + j : ℕ) : ℝ))⁻¹ := by
    positivity
  rw [scale_def, scale_def, hnext]
  exact Real.mul_rpow hn.le hfactor

/-- Helper for lem:polar-continuation: the scalar barrier exponent. -/
def slowExponent (β : ℝ) : ℝ := (1 - β) / (1 + β)

/-- Helper for lem:polar-continuation: the restoring rate exceeds the scalar barrier
exponent by one. -/
theorem restoringRate_sub_slowExponent {β : ℝ} (hβ : 0 < β) :
    2 / (1 + β) - slowExponent β = 1 := by
  have hden : 1 + β ≠ 0 := by
    positivity
  rw [slowExponent]
  field_simp [hden]
  ring

/-- Helper for lem:polar-continuation: the scalar barrier has a positive decay exponent. -/
theorem slowExponent_pos {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    0 < slowExponent β := by
  have hden : 0 < 1 + β := by
    positivity
  exact div_pos (sub_pos.mpr hβone) hden

/-- Helper for lem:polar-continuation: the squared scale is bounded above by the
reciprocal index. -/
theorem scale_sq_le_inv {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scale β j0 j ^ 2 ≤ (((j0 + j : ℕ) : ℝ))⁻¹ := by
  have hindex : (1 : ℝ) ≤ ((j0 + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  have hden : 0 < 1 + β := by
    positivity
  have hexponent : -(2 : ℝ) / (1 + β) ≤ -1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  rw [scale_pow]
  simpa only [Nat.cast_ofNat, Real.rpow_neg_one] using
    Real.rpow_le_rpow_of_exponent_le hindex hexponent

/-- Helper for lem:polar-continuation: the reciprocal index squared is bounded by
the squared scale. -/
theorem inv_sq_le_scale_sq {β : ℝ} (hβ : 0 < β)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    (((j0 + j : ℕ) : ℝ))⁻¹ ^ 2 ≤ scale β j0 j ^ 2 := by
  have hindex : (1 : ℝ) ≤ ((j0 + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  have hden : 0 < 1 + β := by
    positivity
  have hexponent : -(2 : ℝ) ≤ -(2 : ℝ) / (1 + β) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  rw [scale_pow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg _)]
  simpa only [Nat.cast_ofNat] using
    Real.rpow_le_rpow_of_exponent_le hindex hexponent

/-- Helper for eq:polar-angles: every scale power with exponent above `1 + β` is summable. -/
theorem summable_scale_rpow {β q : ℝ} (hβ : 0 < β) (hq : 1 + β < q) (j0 : ℕ) :
    Summable (fun j ↦ scale β j0 j ^ q) := by
  have hden : 0 < 1 + β := by
    positivity
  have hexponent : -q / (1 + β) < -1 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hsum : Summable (fun j : ℕ ↦ ((j + j0 : ℕ) : ℝ) ^ (-q / (1 + β))) :=
    (summable_nat_add_iff j0).mpr (Real.summable_nat_rpow.mpr hexponent)
  apply hsum.congr
  intro j
  rw [scale_rpow]
  simp only [Nat.add_comm]

/-- Helper for eq:polar-angles: radial increments of order `τ²` have a finite total sum. -/
theorem summable_scale_sq {β : ℝ} (hβ : 0 < β) (hβone : β < 1) (j0 : ℕ) :
    Summable (fun j ↦ scale β j0 j ^ 2) := by
  have hexponent : 1 + β < (2 : ℝ) := by
    linarith
  simpa only [Real.rpow_two] using summable_scale_rpow hβ hexponent j0

/-- Helper for eq:polar-angles: the total angular scale is divergent. -/
theorem not_summable_scale {β : ℝ} (hβ : 0 < β) (j0 : ℕ) :
    ¬ Summable (scale β j0) := by
  intro hsum
  have hshift : Summable (fun j : ℕ ↦ ((j + j0 : ℕ) : ℝ) ^ (-1 / (1 + β))) := by
    apply hsum.congr
    intro j
    rw [scale_def]
    simp only [Nat.add_comm]
  have hexponent := Real.summable_nat_rpow.mp ((summable_nat_add_iff j0).mp hshift)
  have hden : 0 < 1 + β := by
    positivity
  have hcontradiction := (div_lt_iff₀ hden).mp hexponent
  linarith

/-- Helper for eq:polar-angles: accumulated positive scales tend to infinity. -/
theorem tendsto_sum_scale_atTop {β : ℝ} (hβ : 0 < β) (j0 : ℕ) :
    Tendsto (fun n ↦ ∑ j ∈ Finset.range n, scale β j0 j) atTop atTop := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg (scale_nonneg β j0)).mp
    (not_summable_scale hβ j0)

/-- Helper for lem:polar-geometry: the tail of any real power of the prescribed scale. -/
def scaleTail (β q : ℝ) (j0 j : ℕ) : ℝ :=
  ∑' l : ℕ, scale β j0 (j + l) ^ q

/-- Helper for lem:polar-geometry: the scale tail is the corresponding shifted real-power series. -/
theorem scaleTail_eq_rpowSum (β q : ℝ) (j0 j : ℕ) :
    scaleTail β q j0 j =
      ∑' l : ℕ, ((l + (j0 + j) : ℕ) : ℝ) ^ (-q / (1 + β)) := by
  apply tsum_congr
  intro l
  rw [scale_rpow]
  simp only [Nat.add_left_comm, Nat.add_comm]

/-- Helper for lem:polar-geometry: every convergent power tail has its exact integral
principal term and an error between zero and its first summand. -/
theorem scaleTail_error {β q : ℝ} (hβ : 0 < β) (hq : 1 + β < q)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    0 ≤ scaleTail β q j0 j -
        ((1 + β) / (q - 1 - β)) * scale β j0 j ^ (q - 1 - β) ∧
      scaleTail β q j0 j -
        ((1 + β) / (q - 1 - β)) * scale β j0 j ^ (q - 1 - β) ≤
          scale β j0 j ^ q := by
  have hden : 0 < 1 + β := by
    positivity
  have hgap : 0 < q - 1 - β := by
    linarith
  have hexponent : -q / (1 + β) < -1 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have herror := ScaleTails.rpowTail_error hexponent (j0 + j)
    (Nat.add_pos_left hstart j)
  have hprimitiveExponent : -q / (1 + β) + 1 = -(q - 1 - β) / (1 + β) := by
    field_simp [hden.ne']
    ring
  have hprimitive : -(((j0 + j : ℕ) : ℝ)) ^ (-q / (1 + β) + 1) /
      (-q / (1 + β) + 1) =
      ((1 + β) / (q - 1 - β)) * scale β j0 j ^ (q - 1 - β) := by
    rw [hprimitiveExponent, scale_rpow]
    field_simp [hden.ne', hgap.ne']
  rw [hprimitive, ← scaleTail_eq_rpowSum, ← scale_rpow] at herror
  exact herror

/-- Helper for lem:polar-geometry: the radial quadratic tail has the source principal
coefficient `(1 + β) / (1 - β)` and an error at most `τ²`. -/
theorem scaleSqTail_error {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    0 ≤ scaleTail β 2 j0 j -
        ((1 + β) / (1 - β)) * scale β j0 j ^ (1 - β) ∧
      scaleTail β 2 j0 j -
        ((1 + β) / (1 - β)) * scale β j0 j ^ (1 - β) ≤ scale β j0 j ^ 2 := by
  have hq : 1 + β < (2 : ℝ) := by
    linarith
  have hexponent : (2 : ℝ) - 1 - β = 1 - β := by
    ring
  simpa only [hexponent, Real.rpow_two] using scaleTail_error hβ hq hstart j

/-- Helper for lem:polar-geometry: each convergent scale tail is bounded by its
integral principal coefficient plus one, uniformly in the starting index. -/
theorem scaleTail_le {β q : ℝ} (hβ : 0 < β) (hq : 1 + β < q)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scaleTail β q j0 j ≤
      (((1 + β) / (q - 1 - β)) + 1) * scale β j0 j ^ (q - 1 - β) := by
  have hexponents : q - 1 - β ≤ q := by
    linarith
  have hpowers := Real.rpow_le_rpow_of_exponent_ge
    (scale_pos β hstart j) (scale_le_one hβ hstart j) hexponents
  linarith [(scaleTail_error hβ hq hstart j).2]

/-- Helper for lem:polar-geometry: the source radial remainder tail has order
`τ^(2 * (1 - β))`, uniformly in the positive starting index. -/
theorem radialRemainderTail_le {β : ℝ} (hβ : 0 < β) (hβone : β < 1)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    scaleTail β (3 - β) j0 j ≤
      (((1 + β) / (2 * (1 - β))) + 1) * scale β j0 j ^ (2 * (1 - β)) := by
  have hq : 1 + β < 3 - β := by
    linarith
  have hexponent : (3 - β) - 1 - β = 2 * (1 - β) := by
    ring
  simpa only [hexponent] using scaleTail_le hβ hq hstart j

/-- Helper for lem:polar-continuation: the source slow tube radius equals the
negative power with exponent `(1 - β) / (1 + β)`. -/
theorem scale_rpow_one_sub (β : ℝ) (j0 j : ℕ) :
    scale β j0 j ^ (1 - β) = ((j0 + j : ℕ) : ℝ) ^ (-slowExponent β) := by
  rw [scale_rpow, slowExponent, neg_div]

/-- Helper for lem:polar-continuation: multiplying the slow tube radius by the
reciprocal index gives exactly the quadratic scale. -/
theorem inv_mul_scale_rpow_one_sub {β : ℝ} (hβ : 0 < β)
    {j0 : ℕ} (hstart : 0 < j0) (j : ℕ) :
    (((j0 + j : ℕ) : ℝ))⁻¹ * scale β j0 j ^ (1 - β) = scale β j0 j ^ 2 := by
  have hscale : 0 < scale β j0 j := scale_pos β hstart j
  have hexponent : (1 + β) + (1 - β) = (2 : ℝ) := by
    ring
  rw [← scale_rpow_one_add hβ j0 j, ← Real.rpow_add hscale, hexponent,
    Real.rpow_two]

end DFP.Polar.General

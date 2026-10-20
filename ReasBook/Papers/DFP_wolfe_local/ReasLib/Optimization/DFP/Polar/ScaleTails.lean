module

public import ReasLib.Optimization.DFP.Polar.Recurrence
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Asymptotics

namespace DFP.Polar.ScaleTails

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: for a decreasing
integrable real power, the discrete tail exceeds its integral by at most its
first term. -/
theorem rpowTail_error {q : ℝ} (hq : q < -1) (N : ℕ) (hN : 0 < N) :
    0 ≤ (∑' n : ℕ, ((n + N : ℕ) : ℝ) ^ q) -
        (-(N : ℝ) ^ (q + 1) / (q + 1)) ∧
      (∑' n : ℕ, ((n + N : ℕ) : ℝ) ^ q) -
        (-(N : ℝ) ^ (q + 1) / (q + 1)) ≤ (N : ℝ) ^ q := by
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hqnonpos : q ≤ 0 := by
    linarith
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ q) (Ici (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hNreal.trans_le hx) hxy hqnonpos
  have hnonneg : ∀ x ∈ Ioi (N : ℝ), 0 ≤ x ^ q := by
    intro x hx
    exact Real.rpow_nonneg (hNreal.trans hx).le q
  have hintegrable : IntegrableOn (fun x : ℝ ↦ x ^ q) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hq hNreal
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ q) := Real.summable_nat_rpow.mpr hq
  have hshift : Summable (fun n : ℕ ↦ ((n + N : ℕ) : ℝ) ^ q) :=
    (summable_nat_add_iff N).mpr hsum
  have hsplit : (∑' n : ℕ, ((n + N : ℕ) : ℝ) ^ q) =
      (N : ℝ) ^ q + ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ q := by
    simpa only [Nat.zero_add, Nat.add_right_comm] using hshift.tsum_eq_zero_add
  have hlower := hanti.integral_le_tsum_comp_add N hsum hnonneg
  have hupper := hanti.tsum_comp_add_le_integral N hintegrable hnonneg
  rw [integral_Ioi_rpow_of_lt hq hNreal] at hlower hupper
  constructor
  · linarith
  · linarith

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: all natural
powers of the prescribed scale retain their exact real-power formula. -/
theorem scale_pow (p : Parameters) (j m : ℕ) :
    p.scale j ^ m = ((p.startIndex + j : ℕ) : ℝ) ^ (-(m : ℝ) / 3) := by
  rw [Parameters.scale_def, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the prescribed
scale is nonnegative, including at the total real-power junk value at index zero. -/
theorem scale_nonneg (p : Parameters) (j : ℕ) : 0 ≤ p.scale j := by
  rw [Parameters.scale_def]
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: a positive
starting index makes every prescribed scale strictly positive. -/
theorem scale_pos (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    0 < p.scale j := by
  rw [Parameters.scale_def]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.add_pos_left hstart j)) _

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the prescribed
scales decrease with the cycle index whenever the starting index is positive. -/
theorem scale_antitone (p : Parameters) (hstart : 0 < p.startIndex) : Antitone p.scale := by
  intro i j hij
  rw [Parameters.scale_def, Parameters.scale_def]
  have hpositive : (0 : ℝ) < ((p.startIndex + i : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left hstart i
  have hindices : ((p.startIndex + i : ℕ) : ℝ) ≤ ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hij p.startIndex
  have hexponent : (-(1 : ℝ) / 3) ≤ 0 := by
    norm_num
  exact Real.rpow_le_rpow_of_nonpos hpositive hindices hexponent

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: every scale is
at most one after the fixed threshold `startIndex ≥ 1`. -/
theorem scale_le_one (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    p.scale j ≤ 1 := by
  have hindex : (1 : ℝ) ≤ ((p.startIndex + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.add_pos_left hstart j)
  have hexponent : (-(1 : ℝ) / 3) ≤ 0 := by
    norm_num
  rw [Parameters.scale_def]
  simpa only [Real.one_rpow] using
    Real.rpow_le_rpow_of_nonpos zero_lt_one hindex hexponent

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the explicit
prescribed scales tend to zero without any orbit-dynamics assumption. -/
theorem scale_tendsto_zero (p : Parameters) : Tendsto p.scale atTop (𝓝 0) := by
  have hindex : Tendsto (fun j : ℕ ↦ ((p.startIndex + j : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, add_comm] using
      tendsto_atTop_add_const_right atTop (p.startIndex : ℝ) tendsto_natCast_atTop_atTop
  have hexponent : (0 : ℝ) < 1 / 3 := by
    norm_num
  rw [funext (Parameters.scale_def p)]
  simpa only [neg_div, Function.comp_def] using
    (tendsto_rpow_neg_atTop hexponent).comp hindex

/-- eq:polar-W-expansion (scale summability component). Every scale power
strictly larger than three is summable for the actual prescribed scales. -/
theorem summable_scale_pow (p : Parameters) (m : ℕ) (hm : 3 < m) :
    Summable (fun j ↦ p.scale j ^ m) := by
  have hmreal : (3 : ℝ) < m := by
    exact_mod_cast hm
  have hexponent : -(m : ℝ) / 3 < -1 := by
    linarith
  have hsum : Summable (fun j : ℕ ↦ ((j + p.startIndex : ℕ) : ℝ) ^ (-(m : ℝ) / 3)) :=
    (summable_nat_add_iff p.startIndex).mpr (Real.summable_nat_rpow.mpr hexponent)
  apply hsum.congr
  intro j
  rw [scale_pow]
  simp only [Nat.add_comm]

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the fourth
powers of the actual prescribed scale are summable. -/
theorem summable_scale_four (p : Parameters) : Summable (fun j ↦ p.scale j ^ 4) := by
  apply summable_scale_pow
  norm_num

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the fifth
powers of the actual prescribed scale are summable. -/
theorem summable_scale_five (p : Parameters) : Summable (fun j ↦ p.scale j ^ 5) := by
  apply summable_scale_pow
  norm_num

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the power tail
of the prescribed scales, starting at cycle `j`. -/
def powerTail (p : Parameters) (m j : ℕ) : ℝ := ∑' l : ℕ, p.scale (j + l) ^ m

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the defining
sum of the prescribed scale-power tail. -/
theorem powerTail_def (p : Parameters) (m j : ℕ) :
    powerTail p m j = ∑' l : ℕ, p.scale (j + l) ^ m := by
  rfl

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the scale tail
is exactly the real-power series with lower endpoint `startIndex + j`. -/
theorem powerTail_eq_rpow_sum (p : Parameters) (m j : ℕ) :
    powerTail p m j =
      ∑' l : ℕ, ((l + (p.startIndex + j) : ℕ) : ℝ) ^ (-(m : ℝ) / 3) := by
  rw [powerTail_def]
  apply tsum_congr
  intro l
  rw [scale_pow]
  simp only [Nat.add_left_comm, Nat.add_comm]

/-- lem:polar-geometry (explicit quartic scale tail). Uniformly for every
positive starting index and every cycle, the quartic tail is `3 t_j` plus a
nonnegative error at most `t_j⁴`. The error constant is exactly one. -/
theorem quarticTail_error (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    0 ≤ powerTail p 4 j - 3 * p.scale j ∧
      powerTail p 4 j - 3 * p.scale j ≤ p.scale j ^ 4 := by
  have hq : (-4 / 3 : ℝ) < -1 := by
    norm_num
  have herror := rpowTail_error hq (p.startIndex + j) (Nat.add_pos_left hstart j)
  have hexponent : (-4 / 3 : ℝ) + 1 = -(1 : ℝ) / 3 := by
    norm_num
  have hprimitive : -((p.startIndex + j : ℕ) : ℝ) ^ ((-4 / 3 : ℝ) + 1) /
      ((-4 / 3 : ℝ) + 1) = 3 * p.scale j := by
    rw [hexponent, Parameters.scale_def]
    ring
  have htail : (∑' l : ℕ, ((l + (p.startIndex + j) : ℕ) : ℝ) ^ (-4 / 3 : ℝ)) =
      powerTail p 4 j := (powerTail_eq_rpow_sum p 4 j).symm
  have hterm : ((p.startIndex + j : ℕ) : ℝ) ^ (-4 / 3 : ℝ) = p.scale j ^ 4 :=
    (scale_pow p j 4).symm
  rwa [htail, hprimitive, hterm] at herror

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: uniformly in the
positive starting index, the quintic tail is `(3/2) t_j²` plus a nonnegative
error at most `t_j⁵`. -/
theorem quinticTail_error (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    0 ≤ powerTail p 5 j - (3 / 2) * p.scale j ^ 2 ∧
      powerTail p 5 j - (3 / 2) * p.scale j ^ 2 ≤ p.scale j ^ 5 := by
  have hq : (-5 / 3 : ℝ) < -1 := by
    norm_num
  have herror := rpowTail_error hq (p.startIndex + j) (Nat.add_pos_left hstart j)
  have hexponent : (-5 / 3 : ℝ) + 1 = -(2 : ℝ) / 3 := by
    norm_num
  have hprimitive : -((p.startIndex + j : ℕ) : ℝ) ^ ((-5 / 3 : ℝ) + 1) /
      ((-5 / 3 : ℝ) + 1) = (3 / 2) * p.scale j ^ 2 := by
    rw [hexponent, scale_pow]
    simp only [Nat.cast_ofNat]
    ring
  have htail : (∑' l : ℕ, ((l + (p.startIndex + j) : ℕ) : ℝ) ^ (-5 / 3 : ℝ)) =
      powerTail p 5 j := (powerTail_eq_rpow_sum p 5 j).symm
  have hterm : ((p.startIndex + j : ℕ) : ℝ) ^ (-5 / 3 : ℝ) = p.scale j ^ 5 :=
    (scale_pow p j 5).symm
  rwa [htail, hprimitive, hterm] at herror

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the quintic tail
is at most `(5/2) t_j²`, with a constant independent of the starting index. -/
theorem quinticTail_le (p : Parameters) (hstart : 0 < p.startIndex) (j : ℕ) :
    powerTail p 5 j ≤ (5 / 2) * p.scale j ^ 2 := by
  have hexponents : (2 : ℕ) ≤ 5 := by
    norm_num
  have hpowers : p.scale j ^ 5 ≤ p.scale j ^ 2 :=
    pow_le_pow_of_le_one (scale_nonneg p j) (scale_le_one p hstart j) hexponents
  linarith [(quinticTail_error p hstart j).2]

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the quartic-tail
error has big-O constant exactly one, uniformly in the positive starting index. -/
theorem quarticTail_isBigOWith (p : Parameters) (hstart : 0 < p.startIndex) :
    Asymptotics.IsBigOWith 1 atTop (fun j ↦ powerTail p 4 j - 3 * p.scale j)
      (fun j ↦ p.scale j ^ 4) := by
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards with j
  have herror := quarticTail_error p hstart j
  simpa only [Real.norm_eq_abs, abs_of_nonneg herror.1,
    abs_of_nonneg (pow_nonneg (scale_nonneg p j) 4), one_mul] using herror.2

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the quintic tail
has big-O constant exactly `5/2` relative to `t_j²`, uniformly in the starting index. -/
theorem quinticTail_isBigOWith (p : Parameters) (hstart : 0 < p.startIndex) :
    Asymptotics.IsBigOWith (5 / 2) atTop (fun j ↦ powerTail p 5 j)
      (fun j ↦ p.scale j ^ 2) := by
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards with j
  have hnonneg : 0 ≤ powerTail p 5 j := by
    rw [powerTail_def]
    exact tsum_nonneg (fun l ↦ pow_nonneg (scale_nonneg p _) 5)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (sq_nonneg (p.scale j))] using quinticTail_le p hstart j

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: a finite power
sum differs from the integral between its endpoints by at most the first
summand. This follows by subtracting the two controlled infinite tails. -/
theorem rpowSegment_abs_error {q : ℝ} (hq : q < -1) (A B : ℕ)
    (hA : 0 < A) (hAB : A ≤ B) :
    |(∑ n ∈ Finset.Ico A B, (n : ℝ) ^ q) -
      (-(A : ℝ) ^ (q + 1) / (q + 1) - -(B : ℝ) ^ (q + 1) / (q + 1))| ≤
      (A : ℝ) ^ q := by
  have hB : 0 < B := hA.trans_le hAB
  have htailA := rpowTail_error hq A hA
  have htailB := rpowTail_error hq B hB
  have hqnonpos : q ≤ 0 := by
    linarith
  have hterm : (B : ℝ) ^ q ≤ (A : ℝ) ^ q :=
    Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hA) (Nat.cast_le.mpr hAB) hqnonpos
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ q) := Real.summable_nat_rpow.mpr hq
  have hdecompose : (∑ n ∈ Finset.Ico A B, (n : ℝ) ^ q) +
      (∑' n : ℕ, ((n + B : ℕ) : ℝ) ^ q) =
      ∑' n : ℕ, ((n + A : ℕ) : ℝ) ^ q := by
    rw [Finset.sum_Ico_eq_sub _ hAB]
    linarith [hsum.sum_add_tsum_nat_add A, hsum.sum_add_tsum_nat_add B]
  apply abs_le.mpr
  constructor
  · linarith [htailA.1, htailB.2]
  · linarith [htailA.2, htailB.1]

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: a negative
third-power exponent at a cubic integer endpoint is the corresponding negative
integer power, with no change to the prescribed cubic scale. -/
theorem cubic_rpow_neg_nat (N m : ℕ) :
    ((N ^ 3 : ℕ) : ℝ) ^ (-(m : ℝ) / 3) = (N : ℝ) ^ (-(m : ℤ)) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  simp only [Nat.cast_ofNat]
  have hexponent : (3 : ℝ) * (-(m : ℝ) / 3) = -(m : ℝ) := by
    ring
  rw [hexponent, Real.rpow_neg_natCast]

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the explicit
scale at a cubic endpoint is exactly the inverse integer endpoint. -/
theorem cubic_rpow_neg_third (N : ℕ) :
    ((N ^ 3 : ℕ) : ℝ) ^ (-(1 : ℝ) / 3) = (N : ℝ)⁻¹ := by
  simpa only [Nat.cast_one, Int.natCast_one, zpow_neg_one] using cubic_rpow_neg_nat N 1

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the quartic
power sum over the cubic endpoints of one full turn has principal term
`3 / (N(N+1))` and error at most `N⁻⁴`, uniformly for `N ≥ 1`. -/
theorem quarticCubicBlock_abs_error (N : ℕ) (hN : 0 < N) :
    |(∑ n ∈ Finset.Ico (N ^ 3) ((N + 1) ^ 3), (n : ℝ) ^ (-4 / 3 : ℝ)) -
      3 / ((N : ℝ) * (N + 1))| ≤ (N : ℝ) ^ (-4 : ℤ) := by
  have hq : (-4 / 3 : ℝ) < -1 := by
    norm_num
  have hAB : N ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ N) 3
  have herror := rpowSegment_abs_error hq (N ^ 3) ((N + 1) ^ 3) (pow_pos hN 3) hAB
  have hexponent : (-4 / 3 : ℝ) + 1 = -(1 : ℝ) / 3 := by
    norm_num
  have hprimitive : -((N ^ 3 : ℕ) : ℝ) ^ ((-4 / 3 : ℝ) + 1) / ((-4 / 3 : ℝ) + 1) -
      -(((N + 1) ^ 3 : ℕ) : ℝ) ^ ((-4 / 3 : ℝ) + 1) / ((-4 / 3 : ℝ) + 1) =
      3 / ((N : ℝ) * (N + 1)) := by
    rw [hexponent, cubic_rpow_neg_third N, cubic_rpow_neg_third (N + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    have hNreal : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    have hnext : (N : ℝ) + 1 ≠ 0 := by
      positivity
    field_simp
    ring
  have hterm : ((N ^ 3 : ℕ) : ℝ) ^ (-4 / 3 : ℝ) = (N : ℝ) ^ (-4 : ℤ) :=
    cubic_rpow_neg_nat N 4
  rwa [hprimitive, hterm] at herror

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: reindexing the
actual prescribed scale between the cycle indices `N³-startIndex` and
`(N+1)³-startIndex` gives precisely the power sum between those cubic endpoints. -/
theorem fullTurn_sum_eq (p : Parameters) (N m : ℕ) (hstart : p.startIndex ≤ N ^ 3) :
    (∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex), p.scale j ^ m) =
      ∑ n ∈ Finset.Ico (N ^ 3) ((N + 1) ^ 3), (n : ℝ) ^ (-(m : ℝ) / 3) := by
  have hAB : N ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ N) 3
  have hnext : p.startIndex ≤ (N + 1) ^ 3 := hstart.trans hAB
  have hsum := Finset.sum_Ico_add
    (fun n : ℕ ↦ (n : ℝ) ^ (-(m : ℝ) / 3))
    (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex) p.startIndex
  rw [Nat.sub_add_cancel hstart, Nat.sub_add_cancel hnext] at hsum
  simpa only [scale_pow] using hsum

/-- Helper for eq:polar-W-expansion and lem:polar-geometry: the actual
prescribed quartic scale sum over one full turn equals `3 / (N(N+1))` with
absolute error at most `N⁻⁴`, independently of the starting index. -/
theorem quarticFullTurn_abs_error (p : Parameters) (N : ℕ)
    (hN : 0 < N) (hstart : p.startIndex ≤ N ^ 3) :
    |(∑ j ∈ Finset.Ico (N ^ 3 - p.startIndex) ((N + 1) ^ 3 - p.startIndex),
      p.scale j ^ 4) - 3 / ((N : ℝ) * (N + 1))| ≤ (N : ℝ) ^ (-4 : ℤ) := by
  rw [fullTurn_sum_eq p N 4 hstart]
  exact quarticCubicBlock_abs_error N hN

end DFP.Polar.ScaleTails

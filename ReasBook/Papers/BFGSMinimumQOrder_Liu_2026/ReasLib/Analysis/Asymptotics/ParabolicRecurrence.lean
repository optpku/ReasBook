module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

open Filter
open scoped Asymptotics Topology

namespace ParabolicRecurrence

/-- If the forward differences of a real sequence tend to `c`, then the sequence divided by
the natural-number index tends to `c`. This is the telescoping form of Cesàro convergence. -/
theorem tendsto_div_natCast_of_tendsto_forwardDiff {u : ℕ → ℝ} {c : ℝ}
    (h_diff : Tendsto (fun j ↦ u (j + 1) - u j) atTop (𝓝 c)) :
    Tendsto (fun j ↦ u j / (j : ℝ)) atTop (𝓝 c) := by
  have h_average :
      Tendsto (fun n : ℕ ↦ (n⁻¹ : ℝ) * (u n - u 0)) atTop (𝓝 c) := by
    simpa only [Finset.sum_range_sub] using h_diff.cesaro
  convert h_average.add (tendsto_const_div_atTop_nhds_zero_nat (u 0)) using 1
  · funext n
    simp only [div_eq_mul_inv]
    ring
  · ring_nf

/-- The parabolic recurrence residual of order `p + 2` makes the decrement, normalized by
`ε j ^ (p + 1)`, tend to its leading coefficient `a`. -/
theorem tendsto_scaledDecrement_of_isBigO {ε : ℕ → ℝ} {a : ℝ} {p : ℕ}
    (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ (p + 1)) =O[atTop]
      (fun j ↦ ε j ^ (p + 2))) :
    Tendsto (fun j ↦ (ε j - ε (j + 1)) / ε j ^ (p + 1)) atTop (𝓝 a) := by
  have hpow : (fun j ↦ ε j ^ (p + 2)) =o[atTop] (fun j ↦ ε j ^ (p + 1)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.add_assoc] using
      (Asymptotics.isLittleO_pow_pow (Nat.lt_succ_self (p + 1))).comp_tendsto hε_zero
  have hres : Tendsto
      (fun j ↦ (ε (j + 1) - ε j + a * ε j ^ (p + 1)) / ε j ^ (p + 1))
      atTop (𝓝 0) := (h_rec.trans_isLittleO hpow).tendsto_div_nhds_zero
  have hfun : (fun j ↦ (ε j - ε (j + 1)) / ε j ^ (p + 1)) =
      fun j ↦ a -
        (ε (j + 1) - ε j + a * ε j ^ (p + 1)) / ε j ^ (p + 1) := by
    funext j
    have hne : ε j ^ (p + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt (hε_pos j))
    field_simp [hne]
    ring
  rw [hfun]
  simpa using tendsto_const_nhds.sub hres

/-- A positive sequence tending to zero and satisfying a parabolic recurrence has successive
ratio tending to one. -/
theorem tendsto_ratio_one_of_isBigO {ε : ℕ → ℝ} {a : ℝ} {p : ℕ} (hp : 0 < p)
    (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ (p + 1)) =O[atTop]
      (fun j ↦ ε j ^ (p + 2))) :
    Tendsto (fun j ↦ ε (j + 1) / ε j) atTop (𝓝 1) := by
  have hscaled := tendsto_scaledDecrement_of_isBigO hε_pos hε_zero h_rec
  have hpow : Tendsto (fun j ↦ ε j ^ p) atTop (𝓝 0) := by
    simpa [zero_pow (ne_of_gt hp)] using hε_zero.pow p
  have hprod : Tendsto
      (fun j ↦ (ε j - ε (j + 1)) / ε j ^ (p + 1) * ε j ^ p)
      atTop (𝓝 0) := by
    simpa using hscaled.mul hpow
  have hfun : (fun j ↦ ε (j + 1) / ε j) = fun j ↦
      1 - (ε j - ε (j + 1)) / ε j ^ (p + 1) * ε j ^ p := by
    funext j
    have hne : ε j ≠ 0 := ne_of_gt (hε_pos j)
    field_simp [pow_succ, hne]
    ring
  rw [hfun]
  simpa using tendsto_const_nhds.sub hprod

/-- A normalized decrement limit and a successive-ratio limit determine the forward difference
of the reciprocal `p`-th powers. -/
theorem tendsto_invPow_forwardDiff_of_ratio_and_scaledDecrement {ε : ℕ → ℝ} {a : ℝ}
    {p : ℕ} (hp : 0 < p) (hε_pos : ∀ j, 0 < ε j)
    (h_ratio : Tendsto (fun j ↦ ε (j + 1) / ε j) atTop (𝓝 1))
    (h_decrement : Tendsto (fun j ↦ (ε j - ε (j + 1)) / ε j ^ (p + 1))
      atTop (𝓝 a)) :
    Tendsto (fun j ↦ (ε (j + 1) ^ p)⁻¹ - (ε j ^ p)⁻¹) atTop
      (𝓝 (a * (p : ℝ))) := by
  have _hp_ne : p ≠ 0 := ne_of_gt hp
  let φ : ℝ → ℝ := fun r ↦ (r ^ p)⁻¹
  have hφ : HasDerivAt φ (-(p : ℝ)) 1 := by
    simpa [φ, zpow_neg, zpow_natCast] using
      (hasDerivAt_zpow (-(p : ℤ)) (1 : ℝ) (Or.inl one_ne_zero))
  have hfactor : Tendsto
      (fun j ↦ -dslope φ 1 (ε (j + 1) / ε j)) atTop (𝓝 (p : ℝ)) := by
    simpa [Function.comp_def, hφ.deriv] using
      ((continuousAt_dslope_same.mpr hφ.differentiableAt).tendsto.comp h_ratio).neg
  have hidentity : ∀ j,
      (ε (j + 1) ^ p)⁻¹ - (ε j ^ p)⁻¹ =
        (ε j - ε (j + 1)) / ε j ^ (p + 1) *
          (-dslope φ 1 (ε (j + 1) / ε j)) := by
    intro j
    let x := ε j
    let y := ε (j + 1)
    have hx : x ≠ 0 := ne_of_gt (hε_pos j)
    have hy : y ≠ 0 := ne_of_gt (hε_pos (j + 1))
    calc
      (y ^ p)⁻¹ - (x ^ p)⁻¹ =
          (x ^ p)⁻¹ * (φ (y / x) - φ 1) := by
        dsimp [φ]
        rw [one_pow, inv_one, div_pow, inv_div]
        field_simp [hx, hy]
      _ = (x ^ p)⁻¹ * ((y / x - 1) * dslope φ 1 (y / x)) := by
        apply congrArg ((x ^ p)⁻¹ * ·)
        simpa [smul_eq_mul] using (sub_smul_dslope φ 1 (y / x)).symm
      _ = (x - y) / x ^ (p + 1) * (-dslope φ 1 (y / x)) := by
        field_simp [pow_succ, hx]
        ring
  have hfun : (fun j ↦ (ε (j + 1) ^ p)⁻¹ - (ε j ^ p)⁻¹) = fun j ↦
      (ε j - ε (j + 1)) / ε j ^ (p + 1) *
        (-dslope φ 1 (ε (j + 1) / ε j)) := funext hidentity
  rw [hfun]
  exact h_decrement.mul hfactor

/-- For a positive parabolic recurrence, the forward differences of the reciprocal `p`-th
powers tend to `a * p`. -/
theorem tendsto_invPow_forwardDiff_of_isBigO {ε : ℕ → ℝ} {a : ℝ} {p : ℕ}
    (hp : 0 < p) (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ (p + 1)) =O[atTop]
      (fun j ↦ ε j ^ (p + 2))) :
    Tendsto (fun j ↦ (ε (j + 1) ^ p)⁻¹ - (ε j ^ p)⁻¹) atTop
      (𝓝 (a * (p : ℝ))) := by
  exact tendsto_invPow_forwardDiff_of_ratio_and_scaledDecrement hp hε_pos
    (tendsto_ratio_one_of_isBigO hp hε_pos hε_zero h_rec)
    (tendsto_scaledDecrement_of_isBigO hε_pos hε_zero h_rec)

end ParabolicRecurrence

namespace Asymptotics.IsEquivalent

/-- A positive real sequence tending to zero and satisfying
`ε (j + 1) = ε j - a * ε j ^ (p + 1) + O(ε j ^ (p + 2))` is asymptotic to
`(a * (p : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ))` when `a > 0` and
`p` is a positive natural number. -/
theorem ofParabolicRecurrence {ε : ℕ → ℝ} {a : ℝ} {p : ℕ} (ha : 0 < a) (hp : 0 < p)
    (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ (p + 1)) =O[atTop]
      (fun j ↦ ε j ^ (p + 2))) :
    ε ~[atTop] (fun j ↦ (a * (p : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ))) := by
  let c : ℝ := a * (p : ℝ)
  have hc : 0 < c := mul_pos ha (Nat.cast_pos.mpr hp)
  have hdiff := ParabolicRecurrence.tendsto_invPow_forwardDiff_of_isBigO
    hp hε_pos hε_zero h_rec
  have hdiv : Tendsto (fun j ↦ (ε j ^ p)⁻¹ / (j : ℝ)) atTop (𝓝 c) := by
    simpa [c] using ParabolicRecurrence.tendsto_div_natCast_of_tendsto_forwardDiff hdiff
  have hratio : Tendsto (fun j ↦ ((ε j ^ p)⁻¹ / (j : ℝ)) / c) atTop (𝓝 1) := by
    simpa [hc.ne'] using hdiv.div_const c
  have hratio' : Tendsto (fun j ↦ (ε j ^ p)⁻¹ / (c * (j : ℝ))) atTop (𝓝 1) := by
    apply hratio.congr'
    filter_upwards [eventually_gt_atTop 0] with j hj
    have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hj)
    field_simp [hc.ne', hj0]
  have hlin : (fun j ↦ (ε j ^ p)⁻¹) ~[atTop] (fun j ↦ c * (j : ℝ)) :=
    isEquivalent_of_tendsto_one hratio'
  have hrpow := hlin.rpow (fun j ↦ mul_nonneg hc.le (Nat.cast_nonneg j))
    (r := -(1 : ℝ) / (p : ℝ))
  refine hrpow.congr_left ?_ |>.congr_right ?_
  · exact Filter.Eventually.of_forall fun j ↦ by
      change ((ε j ^ p)⁻¹) ^ (-(1 : ℝ) / (p : ℝ)) = ε j
      rw [← Real.rpow_neg_eq_inv_rpow]
      convert Real.pow_rpow_inv_natCast (le_of_lt (hε_pos j)) (ne_of_gt hp) using 1; field_simp
  · exact Filter.Eventually.of_forall fun j ↦ by
      change (c * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ)) =
        (a * (p : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / (p : ℝ))
      simp [c, mul_assoc]

/-- A positive sequence tending to zero whose quadratic-recurrence residual
`ε (j + 1) - ε j + a * ε j ^ 2` is `O(ε j ^ 3)` is asymptotic to
the explicit reciprocal scale `(a * (j : ℝ))⁻¹`. -/
theorem ofQuadraticRecurrence {ε : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ 2) =O[atTop]
      (fun j ↦ ε j ^ 3)) :
    ε ~[atTop] (fun j ↦ (a * (j : ℝ))⁻¹) := by
  have h := ofParabolicRecurrence (p := 1) ha (by norm_num) hε_pos hε_zero
    (by simpa using h_rec)
  refine h.congr_right (Filter.Eventually.of_forall fun j ↦ ?_)
  simp [Real.rpow_neg_one]

/-- A positive sequence tending to zero whose quartic-recurrence residual
`ε (j + 1) - ε j + a * ε j ^ 4` is `O(ε j ^ 5)` is asymptotic to
the parabolic scale `(3 * a * (j : ℝ)) ^ (-(1 : ℝ) / 3)`. -/
theorem ofQuarticRecurrence {ε : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hε_pos : ∀ j, 0 < ε j) (hε_zero : Tendsto ε atTop (𝓝 0))
    (h_rec : (fun j ↦ ε (j + 1) - ε j + a * ε j ^ 4) =O[atTop]
      (fun j ↦ ε j ^ 5)) :
    ε ~[atTop] (fun j ↦ (3 * a * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
  have h := ofParabolicRecurrence (p := 3) ha (by norm_num) hε_pos hε_zero
    (by simpa using h_rec)
  refine h.congr_right (Filter.Eventually.of_forall fun j ↦ ?_)
  simpa using congrArg (fun x : ℝ ↦ x ^ (-(1 : ℝ) / 3))
    (by ring : a * (3 : ℝ) * (j : ℝ) = 3 * a * (j : ℝ))

end Asymptotics.IsEquivalent

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

open Filter
open scoped Asymptotics

namespace Asymptotics.IsEquivalent

/-- Shifted tail summation preserves little-o estimates whose summable comparison sequence is
eventually nonnegative. -/
private lemma natTail_isLittleO {f g : ℕ → ℝ} (hfg : f =o[atTop] g) (hg : Summable g)
    (hg_nonneg : ∀ᶠ n in atTop, 0 ≤ g n) :
    (fun j : ℕ ↦ ∑' k : ℕ, f (j + k)) =o[atTop] (fun j : ℕ ↦ ∑' k : ℕ, g (j + k)) := by
  -- Choose one threshold supporting both the little-o bound and nonnegativity.
  refine IsLittleO.of_bound fun c hc ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hfg.bound hc).and hg_nonneg)
  filter_upwards [eventually_ge_atTop N] with j hj
  -- Every term in the tail lies beyond the common threshold.
  have hgj_nonneg (k : ℕ) : 0 ≤ g (j + k) := by
    exact (hN (j + k) (hj.trans (Nat.le_add_right j k))).2
  have hfg_bound (k : ℕ) : ‖f (j + k)‖ ≤ c * g (j + k) := by
    calc
      ‖f (j + k)‖ ≤ c * ‖g (j + k)‖ :=
        (hN (j + k) (hj.trans (Nat.le_add_right j k))).1
      _ = c * g (j + k) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hgj_nonneg k)]
  have hgj : Summable (fun k : ℕ ↦ g (j + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hg
  -- Sum the pointwise majorization and identify the norm of the nonnegative tail.
  calc
    ‖∑' k : ℕ, f (j + k)‖ ≤ c * ∑' k : ℕ, g (j + k) :=
      tsum_of_norm_bounded (hgj.hasSum.mul_left c) hfg_bound
    _ = c * ‖∑' k : ℕ, g (j + k)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg hgj_nonneg)]

/-- Asymptotically equivalent real sequences have asymptotically equivalent shifted tails
when the comparison sequence is summable and eventually positive. -/
theorem tsum_nat_add {u v : ℕ → ℝ} (h : u ~[atTop] v) (hv : Summable v)
    (hv_pos : ∀ᶠ j in atTop, 0 < v j) :
    (fun j : ℕ ↦ ∑' k : ℕ, u (j + k)) ~[atTop]
      (fun j : ℕ ↦ ∑' k : ℕ, v (j + k)) := by
  -- Transfer the original little-o error estimate through shifted tail summation.
  have huv : Summable (u - v) := summable_of_isBigO_nat hv h.isLittleO.isBigO
  have hu : Summable u := by
    simpa only [Pi.add_apply, Pi.sub_apply, sub_add_cancel] using huv.add hv
  have hv_nonneg : ∀ᶠ j in atTop, 0 ≤ v j := hv_pos.mono fun _ hj ↦ hj.le
  have htail := natTail_isLittleO h hv hv_nonneg
  -- Linearity of `tsum` identifies the summed error with the difference of the tails.
  have tailSub :
      (fun j : ℕ ↦ ∑' k : ℕ, (u - v) (j + k)) =
        (fun j : ℕ ↦ ∑' k : ℕ, u (j + k)) - (fun j : ℕ ↦ ∑' k : ℕ, v (j + k)) := by
    funext j
    have huj : Summable (fun k : ℕ ↦ u (j + k)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hu
    have hvj : Summable (fun k : ℕ ↦ v (j + k)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff j).2 hv
    simpa only [Pi.sub_apply] using huj.tsum_sub hvj
  rw [Asymptotics.IsEquivalent, ← tailSub]
  exact htail

end Asymptotics.IsEquivalent

namespace Real

/-- The tail of the real `p`-series with exponent `s > 1` is asymptotic to
`(s - 1)⁻¹ * j ^ (1 - s)`. -/
theorem tsum_nat_add_rpow_isEquivalent {s : ℝ} (hs : 1 < s) :
    (fun j : ℕ ↦ ∑' k : ℕ, (j + k : ℝ) ^ (-s)) ~[atTop]
      (fun j : ℕ ↦ (s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) := by
  have hsummableExponent : -s < -1 := by
    linarith
  have hnegativeExponent : -s ≤ 0 := by
    linarith
  have hshiftedExponent : -s + 1 = -(s - 1) := by
    ring_nf
  have herrorExponent : -s - (1 - s) = -1 := by
    ring_nf
  have hsummable : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr hsummableExponent
  have hIntegral (j : ℕ) (hj : 0 < j) :
      ∫ x : ℝ in Set.Ioi (j : ℝ), x ^ (-s) =
        (s - 1)⁻¹ * (j : ℝ) ^ (1 - s) := by
    rw [integral_Ioi_rpow_of_lt hsummableExponent (Nat.cast_pos.mpr hj)]
    rw [hshiftedExponent, neg_div_neg_eq]
    ring_nf
  have hAntitone (j : ℕ) (hj : 0 < j) :
      AntitoneOn (fun x : ℝ ↦ x ^ (-s)) (Set.Ici (j : ℝ)) := by
    refine (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hnegativeExponent).mono ?_
    intro x hx
    exact (Nat.cast_pos.mpr hj).trans_le (Set.mem_Ici.mp hx)
  have hLower : ∀ᶠ j : ℕ in atTop,
      (s - 1)⁻¹ * (j : ℝ) ^ (1 - s) ≤ ∑' k : ℕ, (j + k : ℝ) ^ (-s) := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    rw [← hIntegral j hj]
    simpa only [Nat.cast_add, Nat.add_comm] using
      (hAntitone j hj).integral_le_tsum_comp_add j hsummable
        (fun x hx ↦ Real.rpow_nonneg (le_of_lt ((Nat.cast_pos.mpr hj).trans hx)) _)
  have hUpper : ∀ᶠ j : ℕ in atTop,
      (∑' k : ℕ, (j + k : ℝ) ^ (-s)) ≤
        (j : ℝ) ^ (-s) + (s - 1)⁻¹ * (j : ℝ) ^ (1 - s) := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    have hshift : Summable (fun k : ℕ ↦ (j + k : ℝ) ^ (-s)) := by
      simpa only [Nat.cast_add, Nat.add_comm] using (summable_nat_add_iff j).mpr hsummable
    have htail := (hAntitone j hj).tsum_comp_add_le_integral j
      (integrableOn_Ioi_rpow_of_lt hsummableExponent (Nat.cast_pos.mpr hj))
      (fun x hx ↦ Real.rpow_nonneg (le_of_lt ((Nat.cast_pos.mpr hj).trans hx)) _)
    have htail' : (∑' k : ℕ, (k + j + 1 : ℝ) ^ (-s)) ≤
        ∫ x : ℝ in Set.Ioi (j : ℝ), x ^ (-s) := by
      simpa only [Nat.cast_add, Nat.cast_one] using htail
    calc
      (∑' k : ℕ, (j + k : ℝ) ^ (-s)) =
          (j : ℝ) ^ (-s) + ∑' k : ℕ, (k + j + 1 : ℝ) ^ (-s) := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.add_zero, Nat.zero_add,
              add_zero, zero_add, add_assoc, add_comm, add_left_comm] using hshift.tsum_eq_zero_add
      _ ≤ (j : ℝ) ^ (-s) + ∫ x : ℝ in Set.Ioi (j : ℝ), x ^ (-s) :=
        add_le_add_right htail' _
      _ = (j : ℝ) ^ (-s) + (s - 1)⁻¹ * (j : ℝ) ^ (1 - s) := by
        rw [hIntegral j hj]
  have hdenPos : ∀ᶠ j : ℕ in atTop,
      0 < (s - 1)⁻¹ * (j : ℝ) ^ (1 - s) := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one (hdenPos.mono fun _ hj ↦ hj.ne')]
  have hErrorEq : ∀ᶠ j : ℕ in atTop,
      (j : ℝ) ^ (-s) / ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) =
        (s - 1) * (j : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    calc
      (j : ℝ) ^ (-s) / ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) =
          (s - 1) * ((j : ℝ) ^ (-s) / (j : ℝ) ^ (1 - s)) := by
            field_simp [ne_of_gt (sub_pos.mpr hs),
              (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hj) _).ne']
      _ = (s - 1) * (j : ℝ) ^ (-s - (1 - s)) := by
        exact congrArg ((s - 1) * ·) (Real.rpow_sub (Nat.cast_pos.mpr hj) _ _).symm
      _ = (s - 1) * (j : ℝ)⁻¹ := by
        rw [herrorExponent, Real.rpow_neg_one]
  have hErrorTendsto : Tendsto
      (fun j : ℕ ↦ (j : ℝ) ^ (-s) / ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)))
      atTop (nhds 0) := by
    apply Tendsto.congr' (hErrorEq.mono fun _ hj ↦ hj.symm)
    have hconst : Tendsto (fun _ : ℕ ↦ s - 1) atTop (nhds (s - 1)) :=
      tendsto_const_nhds
    simpa only [Function.comp_apply, mul_zero] using hconst.mul
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hUpperTendsto : Tendsto
      (fun j : ℕ ↦ 1 + (j : ℝ) ^ (-s) / ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)))
      atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hErrorTendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    hUpperTendsto ?_ ?_
  · filter_upwards [hLower, hdenPos] with j hj hpos
    exact (one_le_div hpos).mpr hj
  · filter_upwards [hUpper, hdenPos] with j hj hpos
    calc
      (∑' k : ℕ, (j + k : ℝ) ^ (-s)) /
          ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) ≤
          ((j : ℝ) ^ (-s) + (s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) /
            ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) :=
        (div_le_div_iff_of_pos_right hpos).mpr hj
      _ = 1 + (j : ℝ) ^ (-s) /
          ((s - 1)⁻¹ * (j : ℝ) ^ (1 - s)) := by
        rw [add_div, div_self hpos.ne']
        ring_nf

end Real

namespace Asymptotics.IsEquivalent

/-- If `ε j` is asymptotic to `C * j ^ (-1 / p)` for positive `C` and `p`,
then the sequence `ε j ^ q` is summable exactly when `p < q`. -/
theorem summable_rpow_iff {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C) (hp : 0 < p) :
    Summable (fun j ↦ ε j ^ q) ↔ p < q := by
  have hpow := Asymptotics.IsEquivalent.rpow (r := q)
    (fun j ↦ mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hε
  refine hpow.summable_iff_nat.trans ?_
  have hcomparison :
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-1 / p)) ^ q =
        (fun j : ℕ ↦ C ^ q * (j : ℝ) ^ (-q / p)) := by
    funext j
    rw [Pi.pow_apply, Real.mul_rpow hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _),
      ← Real.rpow_mul (Nat.cast_nonneg j)]
    congr 2
    field_simp [hp.ne']
  rw [hcomparison, summable_mul_left_iff (Real.rpow_pos_of_pos hC q).ne',
    Real.summable_nat_rpow]
  constructor
  · intro h
    have h' := (div_lt_iff₀ hp).mp h
    linarith
  · intro h
    apply (div_lt_iff₀ hp).mpr
    linarith

/-- If `ε j` is asymptotic to `C * j ^ (-1 / p)` for positive `C` and `p`, then
for `p < q` its shifted `q`-power tail has sharp asymptotic coefficient
`C ^ q * (p / (q - p))`. -/
theorem tail_rpow_isEquivalent {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C)
    (hp : 0 < p) (hq : p < q) :
    (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) ~[atTop]
      (fun j : ℕ ↦ C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p)) := by
  have hpow := Asymptotics.IsEquivalent.rpow (r := q)
    (fun j ↦ mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hε
  have hcomparison :
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-1 / p)) ^ q =
        (fun j : ℕ ↦ C ^ q * (j : ℝ) ^ (-q / p)) := by
    funext j
    rw [Pi.pow_apply, Real.mul_rpow hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _),
      ← Real.rpow_mul (Nat.cast_nonneg j)]
    congr 2
    field_simp [hp.ne']
  rw [hcomparison] at hpow
  have hexponent : -q / p < -1 := by
    apply (div_lt_iff₀ hp).mpr
    linarith
  have hcomparisonSummable : Summable (fun j : ℕ ↦ C ^ q * (j : ℝ) ^ (-q / p)) :=
    (Real.summable_nat_rpow.mpr hexponent).mul_left (C ^ q)
  have hcomparisonPos : ∀ᶠ j : ℕ in atTop, 0 < C ^ q * (j : ℝ) ^ (-q / p) := by
    filter_upwards [eventually_gt_atTop 0] with j hj
    exact mul_pos (Real.rpow_pos_of_pos hC q) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hj) _)
  -- First pass the asymptotic equivalence through shifted summation.
  have htail := tsum_nat_add hpow hcomparisonSummable hcomparisonPos
  have hratio : 1 < q / p := by
    apply (lt_div_iff₀ hp).mpr
    linarith
  have hbase := Real.tsum_nat_add_rpow_isEquivalent hratio
  have hscaled := (IsEquivalent.refl : (fun _ : ℕ ↦ C ^ q) ~[atTop] fun _ ↦ C ^ q).mul hbase
  have htailComparison : ∀ j : ℕ,
      (∑' k : ℕ, C ^ q * ((j + k : ℕ) : ℝ) ^ (-q / p)) =
        C ^ q * ∑' k : ℕ, (j + k : ℝ) ^ (-(q / p)) := by
    intro j
    have hshift : Summable (fun k : ℕ ↦ (j + k : ℝ) ^ (-q / p)) := by
      simpa only [Nat.cast_add, Nat.add_comm] using
        (summable_nat_add_iff j).mpr (Real.summable_nat_rpow.mpr hexponent)
    simpa only [Nat.cast_add, neg_div] using hshift.tsum_mul_left (C ^ q)
  have hcoefficient : (q / p - 1)⁻¹ = p / (q - p) := by
    field_simp [hp.ne', sub_ne_zero.mpr hq.ne]
  have hscaled' :
      (fun j : ℕ ↦ ∑' k : ℕ, C ^ q * ((j + k : ℕ) : ℝ) ^ (-q / p)) ~[atTop]
        (fun j : ℕ ↦ C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p)) := by
    refine hscaled.congr_left (Eventually.of_forall fun j ↦ ?_) |>.congr_right
      (Eventually.of_forall fun j ↦ ?_)
    · simpa only [Pi.mul_apply] using (htailComparison j).symm
    · simp only [Pi.mul_apply]
      rw [hcoefficient]
      ring_nf
  simpa only [Pi.pow_apply] using htail.trans hscaled'

/-- If `ε j` is asymptotic to `C * j ^ (-1 / p)` for positive `C` and `p`, then
for `p < q` its shifted `q`-power tail is asymptotic to
`C ^ p * (p / (q - p)) * ε j ^ (q - p)`. -/
theorem tail_rpow_isEquivalent_self {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C)
    (hp : 0 < p) (hq : p < q) :
    (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) ~[atTop]
      (fun j : ℕ ↦ C ^ p * (p / (q - p)) * ε j ^ (q - p)) := by
  have hpow := Asymptotics.IsEquivalent.rpow (r := q - p)
    (fun j ↦ mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hε
  have hcomparison :
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-1 / p)) ^ (q - p) =
        (fun j : ℕ ↦ C ^ (q - p) * (j : ℝ) ^ (1 - q / p)) := by
    funext j
    rw [Pi.pow_apply, Real.mul_rpow hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _),
      ← Real.rpow_mul (Nat.cast_nonneg j)]
    congr 2
    field_simp [hp.ne']
    ring_nf
  rw [hcomparison] at hpow
  have htail := tail_rpow_isEquivalent hε hC hp hq
  have hscaled :
      (fun j : ℕ ↦ C ^ p * (p / (q - p)) * ε j ^ (q - p)) ~[atTop]
        (fun j : ℕ ↦ C ^ p * (p / (q - p)) *
          (C ^ (q - p) * (j : ℝ) ^ (1 - q / p))) := by
    have hconst :
        (fun _ : ℕ ↦ C ^ p * (p / (q - p))) ~[atTop]
          (fun _ : ℕ ↦ C ^ p * (p / (q - p))) := IsEquivalent.refl
    have hmul := hconst.mul hpow
    convert hmul using 1 <;> (try funext j) <;>
      simp only [Pi.mul_apply, Pi.pow_apply]
  have hcoeff : ∀ j : ℕ,
      C ^ q * (p / (q - p)) * (j : ℝ) ^ (1 - q / p) =
        C ^ p * (p / (q - p)) *
          (C ^ (q - p) * (j : ℝ) ^ (1 - q / p)) := by
    intro j
    have hCpow : C ^ q = C ^ p * C ^ (q - p) := by
      calc
        C ^ q = C ^ (p + (q - p)) := by
          congr 1
          ring
        _ = C ^ p * C ^ (q - p) := Real.rpow_add hC _ _
    rw [hCpow]
    ring
  have htail' := htail.congr_right (Eventually.of_forall hcoeff)
  exact htail'.trans hscaled.symm

/-- Under the same power-scale asymptotic hypotheses, the shifted `q`-power tail is
`O(j ^ (1 - q / p))` whenever `p < q`. -/
theorem tail_rpow_isBigO {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C)
    (hp : 0 < p) (hq : p < q) :
    (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) =O[atTop]
      (fun j : ℕ ↦ (j : ℝ) ^ (1 - q / p)) := by
  exact (tail_rpow_isEquivalent hε hC hp hq).isBigO.trans
    (isBigO_const_mul_self (C ^ q * (p / (q - p)))
      (fun j : ℕ ↦ (j : ℝ) ^ (1 - q / p)) atTop)

/-- Under the same power-scale asymptotic hypotheses, the shifted `q`-power tail is
`O(ε j ^ (q - p))` whenever `p < q`. -/
theorem tail_rpow_isBigO_self {ε : ℕ → ℝ} {C p q : ℝ}
    (hε : ε ~[atTop] (fun j ↦ C * (j : ℝ) ^ (-1 / p))) (hC : 0 < C)
    (hp : 0 < p) (hq : p < q) :
    (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ q) =O[atTop]
      (fun j : ℕ ↦ ε j ^ (q - p)) := by
  have hpow := Asymptotics.IsEquivalent.rpow (r := q - p)
    (fun j ↦ mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _)) hε
  have hcomparison :
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-1 / p)) ^ (q - p) =
        (fun j : ℕ ↦ C ^ (q - p) * (j : ℝ) ^ (1 - q / p)) := by
    funext j
    rw [Pi.pow_apply, Real.mul_rpow hC.le (Real.rpow_nonneg (Nat.cast_nonneg j) _),
      ← Real.rpow_mul (Nat.cast_nonneg j)]
    congr 2
    field_simp [hp.ne']
    ring_nf
  rw [hcomparison] at hpow
  have hindex : (fun j : ℕ ↦ (j : ℝ) ^ (1 - q / p)) =O[atTop]
      (fun j : ℕ ↦ ε j ^ (q - p)) := by
    have hconstant : C ^ (q - p) ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
    exact (isBigO_self_const_mul hconstant
      (fun j : ℕ ↦ (j : ℝ) ^ (1 - q / p)) atTop).trans hpow.isBigO_symm
  exact (tail_rpow_isBigO hε hC hp hq).trans hindex

end Asymptotics.IsEquivalent

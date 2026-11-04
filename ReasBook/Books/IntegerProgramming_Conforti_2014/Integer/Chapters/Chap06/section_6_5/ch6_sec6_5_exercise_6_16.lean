/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_example_3_45

open scoped BigOperators Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section Exercise616

variable {p k : ℕ}

/-- The center `f` of Exercise 6.16, with all coordinates equal to `1 / 2`. -/
def exercise_6_16_center (p : ℕ) : Fin p → ℝ :=
  fun _ ↦ (1 / 2 : ℝ)

/-- The octahedron `Ω_f` from Exercise 6.16, written in the displayed `ℓ¹`-ball form around the
center `f = (1 / 2, …, 1 / 2)`. -/
def exercise_6_16_octahedron (p : ℕ) : Set (Fin p → ℝ) :=
  {x | ∑ i : Fin p, |x i - exercise_6_16_center p i| ≤ (p : ℝ) / 2}

/-- Helper for Exercise 6.16: a point lies in a nonnegative scalar multiple of the canonical
octahedron exactly when its `ℓ¹` norm is bounded by that scalar. -/
lemma mem_smul_octahedron_iff_sum_abs_le
    {a : ℝ} (ha : 0 ≤ a) (r : Fin p → ℝ) :
    r ∈ a • octahedron p ↔ ∑ i : Fin p, |r i| ≤ a := by
  by_cases ha_zero : a = 0
  · have hzero_mem : (0 : Fin p → ℝ) ∈ octahedron p := by
      -- The origin is the center of the canonical octahedron.
      rw [mem_octahedron_iff]
      simp
    have hocta_nonempty : (octahedron p : Set (Fin p → ℝ)).Nonempty := ⟨0, hzero_mem⟩
    rw [ha_zero, Set.zero_smul_set hocta_nonempty]
    change r = 0 ↔ ∑ i : Fin p, |r i| ≤ 0
    constructor
    · intro hr_zero
      -- If the point is forced to be the origin, its `ℓ¹` norm vanishes.
      simp [hr_zero]
    · intro hsum_le
      -- A nonnegative finite sum can be at most `0` only if every summand vanishes.
      have hsum_eq : ∑ i : Fin p, |r i| = 0 := by
        refine le_antisymm hsum_le ?_
        exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (r i)
      rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ abs_nonneg (r i)] at hsum_eq
      ext i
      have hi_mem : i ∈ Finset.univ := by
        simp
      exact abs_eq_zero.mp (hsum_eq i hi_mem)
  · have ha_pos : 0 < a := by
      exact lt_of_le_of_ne ha fun hzero => ha_zero hzero.symm
    -- For a positive scalar, rewrite set membership by pulling the scalar onto the point.
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha_zero, mem_octahedron_iff]
    have hsum :
        ∑ i : Fin p, |(a⁻¹ • r) i| = a⁻¹ * ∑ i : Fin p, |r i| := by
      calc
        ∑ i : Fin p, |(a⁻¹ • r) i|
            = ∑ i : Fin p, a⁻¹ * |r i| := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [Pi.smul_apply, abs_mul, abs_of_nonneg (inv_nonneg.mpr ha)]
        _ = a⁻¹ * ∑ i : Fin p, |r i| := by
              rw [Finset.mul_sum]
    rw [hsum]
    simpa using
      (inv_mul_le_iff₀ ha_pos :
        a⁻¹ * ∑ i : Fin p, |r i| ≤ (1 : ℝ) ↔ ∑ i : Fin p, |r i| ≤ a * 1)

/-- Translating `Ω_f` by `-f` identifies it with the scaled canonical octahedron
`(p / 2) • octahedron p`. -/
theorem exercise_6_16_translated_octahedron_eq
    (p : ℕ) :
    {r : Fin p → ℝ | exercise_6_16_center p + r ∈ exercise_6_16_octahedron p} =
      ((p : ℝ) / 2) • octahedron p := by
  ext r
  have hhalf_nonneg : 0 ≤ ((p : ℝ) / 2) := by
    positivity
  -- Translating by the center removes the offset and leaves the `ℓ¹` ball of radius `p / 2`.
  rw [mem_smul_octahedron_iff_sum_abs_le (p := p) (a := (p : ℝ) / 2) hhalf_nonneg r]
  simp [exercise_6_16_octahedron, exercise_6_16_center]

/-- Helper for Exercise 6.16: the gauge of the canonical octahedron is the `ℓ¹` norm. -/
lemma gauge_octahedron_eq_sum_abs
    (r : Fin p → ℝ) :
    gauge (octahedron p) r = ∑ i : Fin p, |r i| := by
  let s : ℝ := ∑ i : Fin p, |r i|
  have hs_nonneg : 0 ≤ s := by
    -- The `ℓ¹` norm is a sum of nonnegative terms.
    dsimp [s]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (r i)
  rw [gauge_def']
  have hset :
      {t : ℝ | t ∈ Set.Ioi (0 : ℝ) ∧ t⁻¹ • r ∈ octahedron p} =
        {t : ℝ | 0 < t ∧ s ≤ t} := by
    ext t
    constructor
    · intro ht
      rcases ht with ⟨ht_pos, ht_mem⟩
      have hr_mem : r ∈ t • octahedron p := by
        exact (Set.mem_smul_set_iff_inv_smul_mem₀ ht_pos.ne' (octahedron p) r).2 ht_mem
      -- Membership in a positive dilate is exactly the upper-ray condition `s ≤ t`.
      exact ⟨ht_pos,
        (mem_smul_octahedron_iff_sum_abs_le (p := p) (a := t) ht_pos.le r).1 hr_mem⟩
    · intro ht
      rcases ht with ⟨ht_pos, hs_le_t⟩
      have hr_mem : r ∈ t • octahedron p := by
        exact (mem_smul_octahedron_iff_sum_abs_le (p := p) (a := t) ht_pos.le r).2 hs_le_t
      exact ⟨ht_pos,
        (Set.mem_smul_set_iff_inv_smul_mem₀ ht_pos.ne' (octahedron p) r).1 hr_mem⟩
  rw [hset]
  by_cases hs_zero : s = 0
  · have hupper_ray : {t : ℝ | 0 < t ∧ s ≤ t} = Set.Ioi 0 := by
      -- When the `ℓ¹` norm is zero, the only remaining condition is positivity.
      ext t
      constructor
      · intro ht
        exact ht.1
      · intro ht
        have hle : s ≤ t := by
          simpa [hs_zero] using ht.le
        exact ⟨ht, hle⟩
    rw [hupper_ray, csInf_Ioi]
    exact hs_zero.symm
  · have hs_ne_zero : 0 ≠ s := by
      exact fun hzero => hs_zero hzero.symm
    have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg hs_ne_zero
    have hupper_ray : {t : ℝ | 0 < t ∧ s ≤ t} = Set.Ici s := by
      -- For a positive `ℓ¹` norm, the upper ray starts at `s`.
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro ht
        exact ⟨hs_pos.trans_le ht, ht⟩
    rw [hupper_ray, csInf_Ici]

/-- Exercise 6.16 (1). For the translated octahedron `K = Ω_f - f`, the gauge is
`γ_K(r) = (2 / p) ∑ i |r_i|`; this also covers the degenerate case `p = 0`, where both sides are
`0`. -/
theorem exercise_6_16_gauge_eq_sum_abs
    (r : Fin p → ℝ) :
    gauge {rho : Fin p → ℝ | exercise_6_16_center p + rho ∈ exercise_6_16_octahedron p} r =
      (2 / (p : ℝ)) * ∑ i : Fin p, |r i| := by
  have hhalf_nonneg : 0 ≤ ((p : ℝ) / 2) := by
    positivity
  -- Rewrite the translated set as a scaled canonical octahedron.
  rw [exercise_6_16_translated_octahedron_eq]
  have hscale :
      gauge (((p : ℝ) / 2) • octahedron p) r =
        (((p : ℝ) / 2 : ℝ)⁻¹) * gauge (octahedron p) r := by
    -- Gauge rescales contravariantly under dilation of the underlying set.
    simpa [Pi.smul_apply] using
      congrArg (fun g : (Fin p → ℝ) → ℝ => g r)
        (gauge_smul_left_of_nonneg (s := octahedron p) (a := (p : ℝ) / 2) hhalf_nonneg)
  rw [hscale, gauge_octahedron_eq_sum_abs]
  by_cases hp_zero : p = 0
  · -- In the degenerate zero-dimensional case, both coefficients vanish.
    subst hp_zero
    simp
  · have hp_pos_nat : 0 < p := Nat.pos_of_ne_zero hp_zero
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp_pos_nat
    have hcoeff : (((p : ℝ) / 2 : ℝ)⁻¹) = 2 / (p : ℝ) := by
      -- Simplify the inverse of the scaling factor to the textbook coefficient.
      field_simp [div_eq_mul_inv, hp_pos.ne']
    rw [hcoeff]

/-- Helper for Exercise 6.16: summing the coordinate split inequalities gives the global lower
bound with coefficient `2 * ∑ i |r_i|` on each ray. -/
lemma coordinate_splits_total_lower_bound
    (rays : Fin k → Fin p → ℝ)
    (y : Fin k → ℝ)
    (hsplit :
      ∀ i : Fin p, 1 ≤ ∑ j : Fin k, ((2 : ℝ) * |rays j i|) * y j) :
    (p : ℝ) ≤ ∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j := by
  -- Add the `p` split inequalities and commute the two finite sums.
  calc
    (p : ℝ) = ∑ i : Fin p, (1 : ℝ) := by
      simp
    _ ≤ ∑ i : Fin p, ∑ j : Fin k, ((2 : ℝ) * |rays j i|) * y j := by
      exact Finset.sum_le_sum fun i _ ↦ hsplit i
    _ = ∑ j : Fin k, ∑ i : Fin p, ((2 : ℝ) * |rays j i|) * y j := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      calc
        ∑ i : Fin p, ((2 : ℝ) * |rays j i|) * y j
            = (∑ i : Fin p, (2 : ℝ) * |rays j i|) * y j := by
                rw [Finset.sum_mul]
        _ = ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j := by
              rw [Finset.mul_sum]

/-- Exercise 6.16 (2). If the `p` coordinate split inequalities
`∑ j, 2 * |(r^j)_i| * y_j ≥ 1` hold for every coordinate `i`, then the octahedral intersection cut
`∑ j, ((2 / p) * ∑ i, |(r^j)_i|) * y_j ≥ 1` follows. -/
theorem exercise_6_16_cut_implied_by_coordinate_splits
    (hp : 0 < p)
    (rays : Fin k → Fin p → ℝ)
    (y : Fin k → ℝ)
    (hsplit :
      ∀ i : Fin p, 1 ≤ ∑ j : Fin k, ((2 : ℝ) * |rays j i|) * y j) :
    1 ≤ ∑ j : Fin k, ((2 / (p : ℝ)) * ∑ i : Fin p, |rays j i|) * y j := by
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have htotal : (p : ℝ) ≤ ∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j := by
    exact coordinate_splits_total_lower_bound rays y hsplit
  have hnormalized :
      1 ≤ (∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j) * (p : ℝ)⁻¹ := by
    -- Divide the summed inequality by the positive scalar `p`.
    rw [le_mul_inv_iff₀ hp_pos]
    simpa using htotal
  calc
    1 ≤ (∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j) * (p : ℝ)⁻¹ := hnormalized
    _ = ∑ j : Fin k, ((2 / (p : ℝ)) * ∑ i : Fin p, |rays j i|) * y j := by
      -- Push the scalar `(p : ℝ)⁻¹` through the sum and rewrite each coefficient.
      calc
        (∑ j : Fin k, ((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j) * (p : ℝ)⁻¹
            = ∑ j : Fin k, (((2 : ℝ) * ∑ i : Fin p, |rays j i|) * y j) * (p : ℝ)⁻¹ := by
                rw [Finset.sum_mul]
        _ = ∑ j : Fin k, ((2 / (p : ℝ)) * ∑ i : Fin p, |rays j i|) * y j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [div_eq_mul_inv]
              ring

end Exercise616

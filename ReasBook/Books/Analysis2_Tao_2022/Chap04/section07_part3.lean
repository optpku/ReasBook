/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section07_part2

section Chap04
section Section07

/-- Helper for Proposition 4.7.14: floor-bracketing `x₀` between consecutive
`32^{-m}`-mesh points. -/
lemma helperForProposition_4_7_14_gridBracket_by_floor
    (x₀ : ℝ) (m : ℕ) :
    let j : ℤ := Int.floor (x₀ * (32 : ℝ) ^ m)
    let a : ℝ := (j : ℝ) / ((32 : ℝ) ^ m)
    let b : ℝ := ((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)
    a ≤ x₀ ∧ x₀ < b ∧ b - a = 1 / ((32 : ℝ) ^ m) := by
  dsimp
  set p : ℝ := (32 : ℝ) ^ m
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hfloor_le : ((Int.floor (x₀ * p) : ℤ) : ℝ) ≤ x₀ * p := by
    exact Int.floor_le (x₀ * p)
  have hlt_floor_add : x₀ * p < ((Int.floor (x₀ * p) : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one (x₀ * p)
  have ha_le : ((Int.floor (x₀ * p) : ℤ) : ℝ) / p ≤ x₀ := by
    exact (div_le_iff₀ hp_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor_le)
  have hx_lt_b : x₀ < (((Int.floor (x₀ * p) + 1 : ℤ) : ℝ) / p) := by
    have hlt' : x₀ * p < (((Int.floor (x₀ * p) + 1 : ℤ) : ℝ)) := by
      simpa [Int.cast_add, Int.cast_one, add_assoc, add_comm, add_left_comm] using hlt_floor_add
    exact (lt_div_iff₀ hp_pos).2 hlt'
  have hsub : (((Int.floor (x₀ * p) + 1 : ℤ) : ℝ) / p) - (((Int.floor (x₀ * p) : ℤ) : ℝ) / p) =
      1 / p := by
    have hcast_add :
        (((Int.floor (x₀ * p) + 1 : ℤ) : ℝ)) = ((Int.floor (x₀ * p) : ℤ) : ℝ) + 1 := by
      simp
    rw [hcast_add]
    ring
  exact ⟨ha_le, hx_lt_b, by simpa [p] using hsub⟩

/-- Helper for Proposition 4.7.14: ratio identity `(8^m)/(32^m) = 1/(4^m)`. -/
lemma helperForProposition_4_7_14_powRatio_eight_div_thirtyTwo
    (m : ℕ) :
    ((8 : ℝ) ^ m) / ((32 : ℝ) ^ m) = 1 / ((4 : ℝ) ^ m) := by
  have hdecomp : (32 : ℝ) ^ m = (8 : ℝ) ^ m * (4 : ℝ) ^ m := by
    calc
      (32 : ℝ) ^ m = ((8 : ℝ) * (4 : ℝ)) ^ m := by norm_num
      _ = (8 : ℝ) ^ m * (4 : ℝ) ^ m := by rw [mul_pow]
  have h8pow_ne : (8 : ℝ) ^ m ≠ 0 := by positivity
  have h4pow_ne : (4 : ℝ) ^ m ≠ 0 := by positivity
  calc
    ((8 : ℝ) ^ m) / ((32 : ℝ) ^ m)
        = ((8 : ℝ) ^ m) / ((8 : ℝ) ^ m * (4 : ℝ) ^ m) := by rw [hdecomp]
    _ = 1 / ((4 : ℝ) ^ m) := by field_simp [h8pow_ne, h4pow_ne]

/-- Helper for Proposition 4.7.14: a lower bound on numerator and an upper bound
on distance imply a large secant quotient. -/
lemma helperForProposition_4_7_14_secantLower_from_numerator_and_distance
    (x₀ y : ℝ) (m : ℕ)
    (hnum : 1 / (2 * (4 : ℝ) ^ m) ≤
      |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀|)
    (hdist_pos : 0 < |y - x₀|)
    (hdist_le : |y - x₀| ≤ 1 / ((32 : ℝ) ^ m)) :
    (8 : ℝ) ^ m / 2 ≤
      |(scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀)| := by
  have hcoeff_nonneg : 0 ≤ (8 : ℝ) ^ m / 2 := by positivity
  have hmul_dist :
      ((8 : ℝ) ^ m / 2) * |y - x₀| ≤ ((8 : ℝ) ^ m / 2) * (1 / ((32 : ℝ) ^ m)) :=
    mul_le_mul_of_nonneg_left hdist_le hcoeff_nonneg
  have hmul_target :
      ((8 : ℝ) ^ m / 2) * (1 / ((32 : ℝ) ^ m)) = 1 / (2 * (4 : ℝ) ^ m) := by
    calc
      ((8 : ℝ) ^ m / 2) * (1 / ((32 : ℝ) ^ m))
          = (((8 : ℝ) ^ m) / ((32 : ℝ) ^ m)) / 2 := by ring
      _ = (1 / ((4 : ℝ) ^ m)) / 2 := by
            rw [helperForProposition_4_7_14_powRatio_eight_div_thirtyTwo m]
      _ = 1 / (2 * (4 : ℝ) ^ m) := by ring
  have hmul_num :
      ((8 : ℝ) ^ m / 2) * |y - x₀| ≤ |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀| :=
    by
      calc
        ((8 : ℝ) ^ m / 2) * |y - x₀| ≤ ((8 : ℝ) ^ m / 2) * (1 / ((32 : ℝ) ^ m)) := hmul_dist
        _ = 1 / (2 * (4 : ℝ) ^ m) := hmul_target
        _ ≤ |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀| := hnum
  have hquo :
      (8 : ℝ) ^ m / 2 ≤
        |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀| / |y - x₀| :=
    (le_div_iff₀ hdist_pos).2 hmul_num
  have habs_div :
      |(scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀)| =
        |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀| / |y - x₀| := by
    rw [abs_div]
  calc
    (8 : ℝ) ^ m / 2 ≤
        |scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀| / |y - x₀| := hquo
    _ = |(scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀)| := by
          symm
          exact habs_div

/-- Helper for Proposition 4.7.14: for every mesh scale, one can find a nearby
point with secant slope at least `(8^m)/2`. -/
lemma helperForProposition_4_7_14_exists_large_local_secant
    (x₀ : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ∃ y : ℝ,
      0 < |y - x₀| ∧
      |y - x₀| ≤ 1 / ((32 : ℝ) ^ m) ∧
      (8 : ℝ) ^ m / 2 ≤
        |((scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀))| := by
  let j : ℤ := Int.floor (x₀ * (32 : ℝ) ^ m)
  let a : ℝ := (j : ℝ) / ((32 : ℝ) ^ m)
  let b : ℝ := ((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)
  have hgrid := helperForProposition_4_7_14_gridBracket_by_floor x₀ m
  dsimp [j, a, b] at hgrid
  rcases hgrid with ⟨ha_le, hx_lt_b, hgap⟩
  have hinc :
      |scaledCosineSeriesFunction b - scaledCosineSeriesFunction a| ≥ 1 / ((4 : ℝ) ^ m) := by
    simpa [a, b, j] using scaledCosineSeries_increment_lower_bound j m hm
  have htri :
      |scaledCosineSeriesFunction b - scaledCosineSeriesFunction a| ≤
        |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀| +
          |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| := by
    have hdecomp :
        scaledCosineSeriesFunction b - scaledCosineSeriesFunction a =
          (scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀) +
            (scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a) := by ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hsum :
      1 / ((4 : ℝ) ^ m) ≤
        |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀| +
          |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| :=
    le_trans hinc htri
  by_cases hb_large :
      1 / (2 * (4 : ℝ) ^ m) ≤ |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀|
  · have hdist_pos : 0 < |b - x₀| := by
      have hbx_pos : 0 < b - x₀ := sub_pos.mpr hx_lt_b
      simpa [abs_of_pos hbx_pos] using hbx_pos
    have hdist_le : |b - x₀| ≤ 1 / ((32 : ℝ) ^ m) := by
      have hb_ge : x₀ ≤ b := le_of_lt hx_lt_b
      have hbxa_le : b - x₀ ≤ b - a := by linarith [ha_le]
      have hbx_nonneg : 0 ≤ b - x₀ := sub_nonneg.mpr hb_ge
      calc
        |b - x₀| = b - x₀ := abs_of_nonneg hbx_nonneg
        _ ≤ b - a := hbxa_le
        _ = 1 / ((32 : ℝ) ^ m) := hgap
    have hslope :
        (8 : ℝ) ^ m / 2 ≤
          |((scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀) / (b - x₀))| :=
      helperForProposition_4_7_14_secantLower_from_numerator_and_distance
        x₀ b m hb_large hdist_pos hdist_le
    exact ⟨b, hdist_pos, hdist_le, hslope⟩
  · have hb_lt :
      |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀| < 1 / (2 * (4 : ℝ) ^ m) :=
      lt_of_not_ge hb_large
    have ha_large :
        1 / (2 * (4 : ℝ) ^ m) ≤ |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| := by
      set q : ℝ := 1 / ((4 : ℝ) ^ m)
      set t : ℝ := |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀|
      have hsum' : q ≤ t + |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| := by
        simpa [q, t] using hsum
      have hq_eq : 1 / (2 * (4 : ℝ) ^ m) = q / 2 := by
        dsimp [q]
        ring
      have ht_lt : t < q / 2 := by
        simpa [q, t] using (show
          |scaledCosineSeriesFunction b - scaledCosineSeriesFunction x₀| < 1 / (2 * (4 : ℝ) ^ m)
            from hb_lt)
      have hqhalf_le : q / 2 ≤ |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| := by
        linarith [hsum', ht_lt]
      simpa [hq_eq] using hqhalf_le
    have hhalf_pos : 0 < 1 / (2 * (4 : ℝ) ^ m) := by positivity
    have ha_pos_val : 0 < |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| :=
      lt_of_lt_of_le hhalf_pos ha_large
    have hxa_ne : x₀ ≠ a := by
      intro hxa
      have hzero : |scaledCosineSeriesFunction x₀ - scaledCosineSeriesFunction a| = 0 := by
        simp [hxa]
      linarith [ha_pos_val, hzero]
    have hax_ne : a ≠ x₀ := by
      intro hax
      exact hxa_ne hax.symm
    have ha_lt_x : a < x₀ := lt_of_le_of_ne ha_le hax_ne
    have hdist_pos : 0 < |a - x₀| := by
      have hneg : a - x₀ < 0 := sub_neg.mpr ha_lt_x
      have habs : |a - x₀| = x₀ - a := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using abs_of_neg hneg
      have hpos : 0 < x₀ - a := sub_pos.mpr ha_lt_x
      simpa [habs] using hpos
    have hdist_le : |a - x₀| ≤ 1 / ((32 : ℝ) ^ m) := by
      have hxb_ge : x₀ ≤ b := le_of_lt hx_lt_b
      have hxa_le : x₀ - a ≤ b - a := by linarith
      have hneg : a - x₀ < 0 := sub_neg.mpr ha_lt_x
      have habs : |a - x₀| = x₀ - a := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using abs_of_neg hneg
      calc
        |a - x₀| = x₀ - a := habs
        _ ≤ b - a := hxa_le
        _ = 1 / ((32 : ℝ) ^ m) := hgap
    have ha_large' :
        1 / (2 * (4 : ℝ) ^ m) ≤ |scaledCosineSeriesFunction a - scaledCosineSeriesFunction x₀| := by
      simpa [abs_sub_comm] using ha_large
    have hslope :
        (8 : ℝ) ^ m / 2 ≤
          |((scaledCosineSeriesFunction a - scaledCosineSeriesFunction x₀) / (a - x₀))| :=
      helperForProposition_4_7_14_secantLower_from_numerator_and_distance
        x₀ a m ha_large' hdist_pos hdist_le
    exact ⟨a, hdist_pos, hdist_le, hslope⟩

/-- Helper for Proposition 4.7.14: differentiability at `x₀` forces eventual
boundedness of punctured-neighborhood secant quotients. -/
lemma helperForProposition_4_7_14_eventual_secant_bound_of_differentiableAt
    (x₀ : ℝ) (hf : DifferentiableAt ℝ scaledCosineSeriesFunction x₀) :
    ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ),
      |((scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀))| ≤
        |deriv scaledCosineSeriesFunction x₀| + 1 := by
  have hslope :
      Filter.Tendsto
        (slope scaledCosineSeriesFunction x₀)
        (nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ))
        (nhds (deriv scaledCosineSeriesFunction x₀)) := by
    simpa [nhdsWithin, Set.compl_singleton_eq] using hf.hasDerivAt.tendsto_slope
  have hnear :
      ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ),
        |(slope scaledCosineSeriesFunction x₀ y) -
            deriv scaledCosineSeriesFunction x₀| < 1 := by
    have hball : Metric.ball (deriv scaledCosineSeriesFunction x₀) 1 ∈
        nhds (deriv scaledCosineSeriesFunction x₀) :=
      Metric.ball_mem_nhds _ (by norm_num)
    have hdist := hslope hball
    filter_upwards [hdist] with y hy
    simpa [Metric.mem_ball, Real.dist_eq] using hy
  filter_upwards [hnear] with y hy
  set q : ℝ := slope scaledCosineSeriesFunction x₀ y
  have htri : |q| ≤ |q - deriv scaledCosineSeriesFunction x₀| +
      |deriv scaledCosineSeriesFunction x₀| := by
    set d : ℝ := deriv scaledCosineSeriesFunction x₀
    have hdecomp : q = (q - deriv scaledCosineSeriesFunction x₀) +
        deriv scaledCosineSeriesFunction x₀ := by ring
    have htri' :
        |(q - deriv scaledCosineSeriesFunction x₀) + deriv scaledCosineSeriesFunction x₀| ≤
          |q - deriv scaledCosineSeriesFunction x₀| + |deriv scaledCosineSeriesFunction x₀| :=
      abs_add_le _ _
    have habs : |q| = |(q - deriv scaledCosineSeriesFunction x₀) + deriv scaledCosineSeriesFunction x₀| :=
      congrArg abs hdecomp
    exact habs.trans_le htri'
  have hlt : |q| < |deriv scaledCosineSeriesFunction x₀| + 1 := by
    linarith [htri, hy]
  have hslope_def :
      slope scaledCosineSeriesFunction x₀ y =
        (scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀) := by
    simpa using (slope_def_field scaledCosineSeriesFunction x₀ y)
  simpa [q, hslope_def] using le_of_lt hlt

/-- Helper for Proposition 4.7.14: choose a scale `m` making `32^{-m}` tiny and
`(8^m)/2` larger than a prescribed bound. -/
lemma helperForProposition_4_7_14_choose_m_against_delta_and_C
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ 1 / ((32 : ℝ) ^ m) < δ ∧ C < (8 : ℝ) ^ m / 2 := by
  have htoZero : Filter.Tendsto (fun m : ℕ => 1 / ((32 : ℝ) ^ m)) Filter.atTop (nhds (0 : ℝ)) := by
    have hbase : |(1 / (32 : ℝ))| < 1 := by norm_num
    have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
    simpa [one_div_pow] using hpow
  have hsmall : ∀ᶠ m in Filter.atTop, 1 / ((32 : ℝ) ^ m) < δ :=
    htoZero (Iio_mem_nhds hδ)
  have htoTop : Filter.Tendsto (fun m : ℕ => (8 : ℝ) ^ m) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 8)
  have hlargePow : ∀ᶠ m in Filter.atTop, 2 * C < (8 : ℝ) ^ m :=
    htoTop (Filter.eventually_gt_atTop (2 * C))
  have hlarge : ∀ᶠ m in Filter.atTop, C < (8 : ℝ) ^ m / 2 := by
    filter_upwards [hlargePow] with m hm
    linarith
  have hall : ∀ᶠ m in Filter.atTop,
      1 ≤ m ∧ 1 / ((32 : ℝ) ^ m) < δ ∧ C < (8 : ℝ) ^ m / 2 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hsmall, hlarge] with m hm1 hm2 hm3
    exact ⟨hm1, hm2, hm3⟩
  rcases (Filter.eventually_atTop.1 hall) with ⟨m, hm⟩
  exact ⟨m, (hm m le_rfl).1, (hm m le_rfl).2.1, (hm m le_rfl).2.2⟩

/-- Proposition 4.7.14: for `f(x) = ∑_{n=1}^∞ 4^{-n} cos(32^n π x)`
(encoded here as `scaledCosineSeriesFunction` from Definition 4.7.4),
`f` is nowhere differentiable on `ℝ`; i.e., for every `x₀ : ℝ`,
`f` is not differentiable at `x₀`. -/
theorem scaledCosineSeries_nowhere_differentiable
    (x₀ : ℝ) :
    ¬ DifferentiableAt ℝ scaledCosineSeriesFunction x₀ := by
  intro hf
  have hBoundedSecants :
      ∀ᶠ y in nhdsWithin x₀ (({x₀} : Set ℝ)ᶜ),
        |((scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀))| ≤
          |deriv scaledCosineSeriesFunction x₀| + 1 :=
    helperForProposition_4_7_14_eventual_secant_bound_of_differentiableAt x₀ hf
  rcases helperForProposition_4_7_2_radius_from_eventually_punctured x₀ hBoundedSecants with
    ⟨δ, hδ_pos, hδ_local⟩
  let C : ℝ := |deriv scaledCosineSeriesFunction x₀| + 1
  rcases helperForProposition_4_7_14_choose_m_against_delta_and_C δ hδ_pos C with
    ⟨m, hm_one, hm_small, hm_large⟩
  rcases helperForProposition_4_7_14_exists_large_local_secant x₀ m hm_one with
    ⟨y, hy_pos, hy_dist_le, hy_slope_large⟩
  have hy_dist_lt : |y - x₀| < δ := lt_of_le_of_lt hy_dist_le hm_small
  have hy_slope_bounded :
      |((scaledCosineSeriesFunction y - scaledCosineSeriesFunction x₀) / (y - x₀))| ≤ C := by
    simpa [C] using hδ_local y ⟨hy_pos, hy_dist_lt⟩
  linarith [hm_large, hy_slope_large, hy_slope_bounded]


end Section07
end Chap04

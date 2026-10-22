/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section07_part1

section Chap04
section Section07

/-- Helper for Theorem 4.7.9: shifting by `firstPositiveSineZero / 2` converts
`Real.sin` to `Real.cos`. -/
lemma helperForTheorem_4_7_9_sin_shift_half_firstPositiveSineZero_eq_cos (x : ℝ) :
    Real.sin (x + firstPositiveSineZero / 2) = Real.cos x := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  calc
    Real.sin (x + firstPositiveSineZero / 2)
        = Real.sin (x + Real.pi / 2) := by rw [hpi]
    _ = Real.cos x := Real.sin_add_pi_div_two x

/-- Helper for Theorem 4.7.9: division by `firstPositiveSineZero` after the
half-period shift simplifies to adding `1/2`. -/
lemma helperForTheorem_4_7_9_shifted_division_formula (x : ℝ) :
    (x + firstPositiveSineZero / 2) / firstPositiveSineZero =
      x / firstPositiveSineZero + (1 / 2 : ℝ) := by
  have hne : firstPositiveSineZero ≠ 0 :=
    helperForTheorem_4_7_8_firstPositiveSineZero_ne_zero
  have hhalf : (firstPositiveSineZero / 2) / firstPositiveSineZero = (1 / 2 : ℝ) := by
    field_simp [hne]
  calc
    (x + firstPositiveSineZero / 2) / firstPositiveSineZero
        = x / firstPositiveSineZero + (firstPositiveSineZero / 2) / firstPositiveSineZero := by
          rw [add_div]
    _ = x / firstPositiveSineZero + (1 / 2 : ℝ) := by rw [hhalf]

/-- Helper for Theorem 4.7.9: integer-valuedness of the shifted quotient is
equivalent to half-integer-valuedness of the original quotient. -/
lemma helperForTheorem_4_7_9_exists_integer_shifted_iff_half_integer (x : ℝ) :
    (∃ n : ℤ, (x + firstPositiveSineZero / 2) / firstPositiveSineZero = (n : ℝ)) ↔
      (∃ n : ℤ, x / firstPositiveSineZero = (n : ℝ) + (1 / 2 : ℝ)) := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    have hshift : x / firstPositiveSineZero + (1 / 2 : ℝ) = (n : ℝ) := by
      calc
        x / firstPositiveSineZero + (1 / 2 : ℝ)
            = (x + firstPositiveSineZero / 2) / firstPositiveSineZero := by
              symm
              exact helperForTheorem_4_7_9_shifted_division_formula x
        _ = (n : ℝ) := hn
    have hx : x / firstPositiveSineZero = (n : ℝ) - (1 / 2 : ℝ) := by linarith
    have hcast_sub : ((n - 1 : ℤ) : ℝ) = (n : ℝ) - (1 : ℝ) := by
      simpa using (Int.cast_sub n 1 : ((n - 1 : ℤ) : ℝ) = (n : ℝ) - (1 : ℝ))
    refine ⟨n - 1, ?_⟩
    calc
      x / firstPositiveSineZero = (n : ℝ) - (1 / 2 : ℝ) := hx
      _ = ((n : ℝ) - (1 : ℝ)) + (1 / 2 : ℝ) := by ring
      _ = ((n - 1 : ℤ) : ℝ) + (1 / 2 : ℝ) := by rw [← hcast_sub]
  · intro h
    rcases h with ⟨n, hn⟩
    have hcast_add : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + (1 : ℝ) := by
      simpa using (Int.cast_add n 1 : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + (1 : ℝ))
    refine ⟨n + 1, ?_⟩
    calc
      (x + firstPositiveSineZero / 2) / firstPositiveSineZero
          = x / firstPositiveSineZero + (1 / 2 : ℝ) :=
            helperForTheorem_4_7_9_shifted_division_formula x
      _ = ((n : ℝ) + (1 / 2 : ℝ)) + (1 / 2 : ℝ) := by rw [hn]
      _ = (n : ℝ) + (1 : ℝ) := by ring
      _ = ((n + 1 : ℤ) : ℝ) := by rw [← hcast_add]

/-- Helper for Theorem 4.7.9: `Real.cos x = 0` is equivalent to vanishing of the
shifted sine value. -/
lemma helperForTheorem_4_7_9_cos_zero_iff_shifted_sin_zero (x : ℝ) :
    Real.cos x = 0 ↔ Real.sin (x + firstPositiveSineZero / 2) = 0 := by
  constructor
  · intro hcos
    rw [helperForTheorem_4_7_9_sin_shift_half_firstPositiveSineZero_eq_cos x]
    exact hcos
  · intro hsin
    rw [← helperForTheorem_4_7_9_sin_shift_half_firstPositiveSineZero_eq_cos x]
    exact hsin

/-- Theorem 4.7.9: For every real number `x` (with `π` given by Definition 4.7.2),
`Real.cos x = 0` if and only if `x / π` is an integer plus `(1/2)`. -/
theorem real_cos_eq_zero_iff_div_firstPositiveSineZero_half_integer (x : ℝ) :
    Real.cos x = 0 ↔ ∃ n : ℤ, x / firstPositiveSineZero = (n : ℝ) + (1 / 2 : ℝ) := by
  constructor
  · intro hcos
    have hsin : Real.sin (x + firstPositiveSineZero / 2) = 0 :=
      (helperForTheorem_4_7_9_cos_zero_iff_shifted_sin_zero x).mp hcos
    have hInt : ∃ n : ℤ, (x + firstPositiveSineZero / 2) / firstPositiveSineZero = (n : ℝ) :=
      (real_sine_eq_zero_iff_div_firstPositiveSineZero_integer
        (x + firstPositiveSineZero / 2)).mp hsin
    exact (helperForTheorem_4_7_9_exists_integer_shifted_iff_half_integer x).mp hInt
  · intro hHalf
    have hInt : ∃ n : ℤ, (x + firstPositiveSineZero / 2) / firstPositiveSineZero = (n : ℝ) :=
      (helperForTheorem_4_7_9_exists_integer_shifted_iff_half_integer x).mpr hHalf
    have hsin : Real.sin (x + firstPositiveSineZero / 2) = 0 :=
      (real_sine_eq_zero_iff_div_firstPositiveSineZero_integer
        (x + firstPositiveSineZero / 2)).mpr hInt
    exact (helperForTheorem_4_7_9_cos_zero_iff_shifted_sin_zero x).mpr hsin

/-- Helper for Proposition 4.7.11: the Leibniz series gives `π / 4` for
the conditional summation filter on `ℕ`. -/
lemma helperForProposition_4_7_11_hasSum_alternating_inv_odd_pi_div_four_conditional :
    HasSum (fun n : ℕ => (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))) (Real.pi / 4)
      (SummationFilter.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
  simpa using Real.tendsto_sum_pi_div_four

/-- Helper for Proposition 4.7.11: the conditionally summed Leibniz identity
for `firstPositiveSineZero` (hence for `π`). -/
lemma helperForProposition_4_7_11_firstPositiveSineZero_eq_four_mul_conditional_tsum :
    firstPositiveSineZero =
      4 * ∑'[SummationFilter.conditional ℕ] n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) := by
  have htsum :
      (∑'[SummationFilter.conditional ℕ] n : ℕ,
        (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))) = Real.pi / 4 :=
    helperForProposition_4_7_11_hasSum_alternating_inv_odd_pi_div_four_conditional.tsum_eq
  calc
    firstPositiveSineZero = Real.pi := helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
    _ = 4 * (Real.pi / 4) := by ring
    _ = 4 * ∑'[SummationFilter.conditional ℕ] n : ℕ,
      (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) := by rw [htsum]

/-- Helper for Proposition 4.7.11: the odd reciprocal series is not
unconditionally summable. -/
lemma helperForProposition_4_7_11_not_summable_inv_odd :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (2 * n + 1 : ℝ)) := by
  intro hodd
  have htwoodd : Summable (fun n : ℕ => (2 : ℝ) * ((1 : ℝ) / (2 * n + 1 : ℝ))) :=
    hodd.mul_left 2
  have hharmShift : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ htwoodd
    · intro n
      positivity
    · intro n
      have hleDen : (2 * n + 1 : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
        have hstep : (2 * n + 1 : ℝ) ≤ 2 * n + 2 := by linarith
        calc
          (2 * n + 1 : ℝ) ≤ 2 * n + 2 := hstep
          _ = 2 * ((n + 1 : ℕ) : ℝ) := by
            rw [Nat.cast_add, Nat.cast_one]
            ring
      have hA : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
      have hB : (0 : ℝ) < (2 * n + 1 : ℝ) := by positivity
      have hdiv : (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) ≤ (1 : ℝ) / (2 * n + 1 : ℝ) :=
        (one_div_le_one_div hA hB).2 hleDen
      have hmul :
          (2 : ℝ) * ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) ≤
            (2 : ℝ) * ((1 : ℝ) / (2 * n + 1 : ℝ)) := by
        gcongr
      have hrewrite :
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ) =
            (2 : ℝ) * ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) := by
        have h1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp [h1]
      calc
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
            = (2 : ℝ) * ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) := hrewrite
        _ ≤ (2 : ℝ) * ((1 : ℝ) / (2 * n + 1 : ℝ)) := hmul
  have hharm : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 1).1 hharmShift
  exact Real.not_summable_one_div_natCast hharm

/-- Helper for Proposition 4.7.11: the alternating odd-reciprocal series is
not unconditionally summable. -/
lemma helperForProposition_4_7_11_not_summable_alternating_inv_odd :
    ¬ Summable (fun n : ℕ => (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))) := by
  intro hsum
  have habs : Summable (fun n : ℕ => |(((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))|) :=
    hsum.abs
  have hodd : Summable (fun n : ℕ => (1 : ℝ) / (2 * n + 1 : ℝ)) := by
    refine habs.congr ?_
    intro n
    have hden : (0 : ℝ) < (2 * n + 1 : ℝ) := by positivity
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hden]
  exact helperForProposition_4_7_11_not_summable_inv_odd hodd

/-- Helper for Proposition 4.7.11: under Lean's default unconditional `tsum`,
the alternating odd-reciprocal series has value `0`. -/
lemma helperForProposition_4_7_11_tsum_alternating_inv_odd_eq_zero :
    (∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))) = 0 := by
  exact tsum_eq_zero_of_not_summable
    helperForProposition_4_7_11_not_summable_alternating_inv_odd

/-- Helper for Proposition 4.7.11: consequently,
`4 * ∑' n, (-1)^n / (2n+1)` is `0` under unconditional `tsum`. -/
lemma helperForProposition_4_7_11_four_mul_tsum_alternating_inv_odd_eq_zero :
    4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) = 0 := by
  rw [helperForProposition_4_7_11_tsum_alternating_inv_odd_eq_zero]
  ring

/-- Helper for Proposition 4.7.11: the unconditional-series equality would
force `firstPositiveSineZero = 0`. -/
lemma helperForProposition_4_7_11_eq_four_mul_tsum_implies_firstPositiveSineZero_eq_zero
    (hmain : firstPositiveSineZero =
      4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ))) :
    firstPositiveSineZero = 0 := by
  calc
    firstPositiveSineZero = 4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) := hmain
    _ = 0 := helperForProposition_4_7_11_four_mul_tsum_alternating_inv_odd_eq_zero

/-- Helper for Proposition 4.7.11: lower bound `4 - 4/3 < firstPositiveSineZero`. -/
lemma helperForProposition_4_7_11_lower_bound :
    4 - 4 / 3 < firstPositiveSineZero := by
  have hleft : (4 - 4 / 3 : ℝ) < 3 := by norm_num
  have hright : (3 : ℝ) < firstPositiveSineZero := by
    calc
      (3 : ℝ) < Real.pi := Real.pi_gt_three
      _ = firstPositiveSineZero := by
        symm
        exact helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  exact lt_trans hleft hright

/-- Helper for Proposition 4.7.11: upper bound `firstPositiveSineZero < 4`. -/
lemma helperForProposition_4_7_11_upper_bound :
    firstPositiveSineZero < 4 := by
  calc
    firstPositiveSineZero = Real.pi := helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
    _ < 4 := Real.pi_lt_four

/-- Helper for Proposition 4.7.11: package the two stated numerical bounds
into a single conjunction. -/
lemma helperForProposition_4_7_11_bounds_conjunction :
    4 - 4 / 3 < firstPositiveSineZero ∧ firstPositiveSineZero < 4 := by
  exact ⟨helperForProposition_4_7_11_lower_bound,
    helperForProposition_4_7_11_upper_bound⟩

/-- Helper for Proposition 4.7.11: under unconditional `tsum`, the asserted
Leibniz equality would force `firstPositiveSineZero = 0`, contradicting
`firstPositiveSineZero = Real.pi`. -/
lemma helperForProposition_4_7_11_not_firstPositiveSineZero_eq_four_mul_tsum_alternating_inv_odd :
    ¬ firstPositiveSineZero = 4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) := by
  intro hmain
  have hzero : firstPositiveSineZero = 0 :=
    helperForProposition_4_7_11_eq_four_mul_tsum_implies_firstPositiveSineZero_eq_zero hmain
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  have hpi_zero : Real.pi = 0 := by
    calc
      Real.pi = firstPositiveSineZero := by symm; exact hpi
      _ = 0 := hzero
  exact Real.pi_ne_zero hpi_zero

/-- Helper for Proposition 4.7.11: the full conjunction in the target statement
is inconsistent with unconditional `tsum` for this series. -/
lemma helperForProposition_4_7_11_not_target_conjunction :
    ¬ (firstPositiveSineZero = 4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) ∧
      4 - 4 / 3 < firstPositiveSineZero ∧ firstPositiveSineZero < 4) := by
  intro h
  exact
    helperForProposition_4_7_11_not_firstPositiveSineZero_eq_four_mul_tsum_alternating_inv_odd h.1

/-- Helper for Proposition 4.7.11: combining any witness of the main Leibniz
equality with the proven numerical bounds yields a contradiction under
unconditional `tsum`. -/
lemma helperForProposition_4_7_11_false_of_main_conjunct_and_bounds
    (hmain : firstPositiveSineZero =
      4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)))
    (hbounds : 4 - 4 / 3 < firstPositiveSineZero ∧ firstPositiveSineZero < 4) : False := by
  have htarget :
      firstPositiveSineZero = 4 * ∑' n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) ∧
        4 - 4 / 3 < firstPositiveSineZero ∧ firstPositiveSineZero < 4 :=
    ⟨hmain, hbounds⟩
  exact helperForProposition_4_7_11_not_target_conjunction htarget

/-- Proposition 4.7.11: the Leibniz series identity
`π = 4 * (1 - 1/3 + 1/5 - 1/7 + ⋯)` holds in Lean via the conditional
summation filter on `ℕ`; in particular, `4 - 4/3 < π < 4`. -/
theorem firstPositiveSineZero_eq_four_mul_tsum_alternating_inv_odd_and_bounds :
    firstPositiveSineZero =
      4 * ∑'[SummationFilter.conditional ℕ] n : ℕ, (((-1 : ℝ) ^ n) / (2 * n + 1 : ℝ)) ∧
    4 - 4 / 3 < firstPositiveSineZero ∧ firstPositiveSineZero < 4 := by
  exact ⟨helperForProposition_4_7_11_firstPositiveSineZero_eq_four_mul_conditional_tsum,
    helperForProposition_4_7_11_bounds_conjunction⟩

/-- Helper for Proposition 4.7.12: each summand in the scaled cosine series is continuous. -/
lemma helperForProposition_4_7_12_termContinuous (n : ℕ) :
    Continuous (fun x : ℝ =>
      (1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)) := by
  have hmulx :
      Continuous (fun x : ℝ => ((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x) := by
    exact continuous_const.mul continuous_id
  exact continuous_const.mul (Real.continuous_cos.comp hmulx)

/-- Helper for Proposition 4.7.12: the geometric majorant `4^{-(n+1)}` is summable. -/
lemma helperForProposition_4_7_12_majorantSummable :
    Summable (fun n : ℕ => 1 / (4 : ℝ) ^ (n + 1)) := by
  have hgeomShift : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ (n + 1)) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => (1 / 4 : ℝ) ^ n) 1).2
      (summable_geometric_of_lt_one (by positivity) (by norm_num))
  simpa [one_div_pow] using hgeomShift

/-- Helper for Proposition 4.7.12: each summand is bounded in norm by `4^{-(n+1)}`. -/
lemma helperForProposition_4_7_12_termNormBound (n : ℕ) (x : ℝ) :
    ‖(1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)‖ ≤
      1 / (4 : ℝ) ^ (n + 1) := by
  have hcoeff_nonneg : 0 ≤ (1 / (4 : ℝ) ^ (n + 1)) := by positivity
  have hcos :
      ‖Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)‖ ≤ (1 : ℝ) := by
    simpa [Real.norm_eq_abs] using
      (Real.abs_cos_le_one (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x))
  calc
    ‖(1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)‖ =
        ‖1 / (4 : ℝ) ^ (n + 1)‖ *
          ‖Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)‖ := by
          rw [norm_mul]
    _ ≤ ‖1 / (4 : ℝ) ^ (n + 1)‖ * 1 := by gcongr
    _ = (1 / (4 : ℝ) ^ (n + 1)) * 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
    _ = 1 / (4 : ℝ) ^ (n + 1) := by ring


/-- Helper for Proposition 4.7.12: partial sums converge uniformly to the infinite series. -/
lemma helperForProposition_4_7_12_uniformLimit_raw :
    TendstoUniformly
      (fun N => fun x =>
        Finset.sum (Finset.range N) (fun n =>
          (1 / (4 : ℝ) ^ (n + 1)) *
            Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)))
      scaledCosineSeriesFunction
      Filter.atTop := by
  change TendstoUniformly
    (fun N => fun x =>
      Finset.sum (Finset.range N) (fun n =>
        (1 / (4 : ℝ) ^ (n + 1)) *
          Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)))
    (fun x =>
      ∑' n : ℕ,
        (1 / (4 : ℝ) ^ (n + 1)) *
          Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x))
    Filter.atTop
  refine tendstoUniformly_tsum_nat helperForProposition_4_7_12_majorantSummable ?_
  intro n x
  exact helperForProposition_4_7_12_termNormBound n x

/-- Helper for Proposition 4.7.12: each partial sum in the scaled cosine series is continuous. -/
lemma helperForProposition_4_7_12_partialSumsContinuous (N : ℕ) :
    Continuous (fun x : ℝ =>
      Finset.sum (Finset.range N) (fun n =>
        (1 / (4 : ℝ) ^ (n + 1)) *
          Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x))) := by
  exact continuous_finset_sum (Finset.range N)
    (fun n _ => helperForProposition_4_7_12_termContinuous n)

/-- Proposition 4.7.12: for `f(x) = ∑_{n=1}^∞ 4^{-n} cos(32^n π x)` (with
`π = firstPositiveSineZero` from Definition 4.7.2), the series converges uniformly
on `ℝ`; in particular, `f` is continuous on `ℝ`. -/
theorem scaledCosineSeries_uniformly_convergent_and_continuous :
    TendstoUniformly
      (fun N => fun x =>
        Finset.sum (Finset.range N) (fun n =>
          (1 / (4 : ℝ) ^ (n + 1)) *
            Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)))
      scaledCosineSeriesFunction Filter.atTop ∧
    Continuous scaledCosineSeriesFunction := by
  refine ⟨helperForProposition_4_7_12_uniformLimit_raw, ?_⟩
  refine helperForProposition_4_7_12_uniformLimit_raw.continuous ?_
  exact Filter.Frequently.of_forall helperForProposition_4_7_12_partialSumsContinuous

/-- Helper for Proposition 4.7.13: the `n`-th increment term of
`scaledCosineSeriesFunction` across mesh size `32^{-m}`. -/
noncomputable def helperForProposition_4_7_13_diffTerm (j : ℤ) (m n : ℕ) : ℝ :=
  ((1 / (4 : ℝ) ^ (n + 1)) *
      Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero *
        (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)))) -
    ((1 / (4 : ℝ) ^ (n + 1)) *
      Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero *
        ((j : ℝ) / ((32 : ℝ) ^ m))) )

/-- Helper for Proposition 4.7.13: pointwise summability of the cosine series. -/
lemma helperForProposition_4_7_13_seriesSummableAtPoint (x : ℝ) :
    Summable (fun n : ℕ =>
      (1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x)) := by
  refine Summable.of_norm_bounded helperForProposition_4_7_12_majorantSummable ?_
  intro n
  simpa using helperForProposition_4_7_12_termNormBound n x

/-- Helper for Proposition 4.7.13: for `n ≥ m`, the phase shift
`32^(n+1-m) * π` is an integer multiple of `2π`. -/
lemma helperForProposition_4_7_13_phaseShift_asTwoPiMultiple
    (m n : ℕ) (hmn : m ≤ n) :
    ∃ k : ℕ,
      ((32 : ℝ) ^ (n + 1 - m)) * firstPositiveSineZero = (k : ℝ) * (2 * Real.pi) := by
  refine ⟨16 * 32 ^ (n - m), ?_⟩
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  have hsub : n + 1 - m = (n - m) + 1 := by
    omega
  calc
    ((32 : ℝ) ^ (n + 1 - m)) * firstPositiveSineZero
        = ((32 : ℝ) ^ ((n - m) + 1)) * Real.pi := by rw [hsub, hpi]
    _ = ((32 : ℝ) * (32 : ℝ) ^ (n - m)) * Real.pi := by rw [pow_succ']
    _ = ((16 : ℝ) * (32 : ℝ) ^ (n - m)) * (2 * Real.pi) := by ring
    _ = (((16 * 32 ^ (n - m) : ℕ) : ℝ) * (2 * Real.pi)) := by
          norm_num [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 4.7.13: all modes `n ≥ m` vanish in the increment. -/
lemma helperForProposition_4_7_13_highModesVanish
    (j : ℤ) (m n : ℕ) (hnm : m ≤ n) :
    helperForProposition_4_7_13_diffTerm j m n = 0 := by
  have hd_ne : ((32 : ℝ) ^ m) ≠ 0 := by positivity
  have hpow : ((32 : ℝ) ^ (n + 1)) = ((32 : ℝ) ^ m) * ((32 : ℝ) ^ (n + 1 - m)) := by
    have hsplit : n + 1 = m + (n + 1 - m) := by
      omega
    have hpow' := congrArg (fun t : ℕ => ((32 : ℝ) ^ t)) hsplit
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hpow'
  rcases helperForProposition_4_7_13_phaseShift_asTwoPiMultiple m n hnm with ⟨k, hk⟩
  let d : ℝ := ((32 : ℝ) ^ m)
  let c : ℝ := ((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero
  let a1 : ℝ := c * (((j + 1 : ℤ) : ℝ) / d)
  let a0 : ℝ := c * ((j : ℝ) / d)
  have hfrac : (((j + 1 : ℤ) : ℝ) / d) = (j : ℝ) / d + 1 / d := by
    dsimp [d]
    field_simp [hd_ne]
    norm_num
  have hc_div : c * (1 / d) = ((32 : ℝ) ^ (n + 1 - m)) * firstPositiveSineZero := by
    dsimp [c, d]
    rw [hpow]
    field_simp [hd_ne]
  have ha1 : a1 = a0 + ((32 : ℝ) ^ (n + 1 - m)) * firstPositiveSineZero := by
    dsimp [a1, a0]
    rw [hfrac, mul_add, hc_div]
  have hcos : Real.cos a1 = Real.cos a0 := by
    rw [ha1, hk]
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      (Real.cos_add_nat_mul_two_pi a0 k)
  unfold helperForProposition_4_7_13_diffTerm
  dsimp [a1, a0, c, d] at hcos
  rw [hcos]
  ring

/-- Helper for Proposition 4.7.13: the increment equals a finite sum over modes `< m`. -/
lemma helperForProposition_4_7_13_increment_asFiniteSum
    (j : ℤ) (m : ℕ) :
    scaledCosineSeriesFunction (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) -
        scaledCosineSeriesFunction ((j : ℝ) / ((32 : ℝ) ^ m)) =
      ∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n := by
  let x1 : ℝ := (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m))
  let x0 : ℝ := ((j : ℝ) / ((32 : ℝ) ^ m))
  let f1 : ℕ → ℝ :=
    fun n =>
      (1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x1)
  let f0 : ℕ → ℝ :=
    fun n =>
      (1 / (4 : ℝ) ^ (n + 1)) *
        Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x0)
  have hs1 :
      Summable (fun n : ℕ =>
        (1 / (4 : ℝ) ^ (n + 1)) *
          Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x1)) :=
    helperForProposition_4_7_13_seriesSummableAtPoint x1
  have hs0 :
      Summable (fun n : ℕ =>
        (1 / (4 : ℝ) ^ (n + 1)) *
          Real.cos (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero * x0)) :=
    helperForProposition_4_7_13_seriesSummableAtPoint x0
  have hs1' : Summable f1 := by
    simpa [f1] using hs1
  have hs0' : Summable f0 := by
    simpa [f0] using hs0
  have htailZero :
      ∀ n ∉ Finset.range m, helperForProposition_4_7_13_diffTerm j m n = 0 := by
    intro n hn
    have hmn : m ≤ n := by
      simpa [Finset.mem_range] using hn
    exact helperForProposition_4_7_13_highModesVanish j m n hmn
  have htsumSub : (∑' n : ℕ, f1 n) - (∑' n : ℕ, f0 n) = ∑' n : ℕ, (f1 n - f0 n) := by
    exact (Summable.tsum_sub hs1' hs0').symm
  have hdiffTerm : ∀ n : ℕ, (f1 n - f0 n) = helperForProposition_4_7_13_diffTerm j m n := by
    intro n
    simp [f1, f0, helperForProposition_4_7_13_diffTerm, x1, x0]
  calc
    scaledCosineSeriesFunction x1 - scaledCosineSeriesFunction x0
        = (∑' n : ℕ, f1 n) - (∑' n : ℕ, f0 n) := by
            simp [scaledCosineSeriesFunction, f1, f0]
    _ = ∑' n : ℕ, (f1 n - f0 n) := htsumSub
    _ = ∑' n : ℕ, helperForProposition_4_7_13_diffTerm j m n := by
          simp [hdiffTerm]
    _ = ∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n := by
          exact tsum_eq_sum htailZero

/-- Helper for Proposition 4.7.13: the main mode `n = m-1` contributes exactly
`2 / 4^m` in absolute value. -/
lemma helperForProposition_4_7_13_mainMode_exact
    (j : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    |helperForProposition_4_7_13_diffTerm j m (m - 1)| = 2 / (4 : ℝ) ^ m := by
  have hpi : firstPositiveSineZero = Real.pi :=
    helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi
  have h32m_ne : ((32 : ℝ) ^ m) ≠ 0 := by positivity
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have harg1 :
      ((32 : ℝ) ^ m) * firstPositiveSineZero * (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) =
        (((j + 1 : ℤ) : ℝ) * Real.pi) := by
    calc
      ((32 : ℝ) ^ m) * firstPositiveSineZero * (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m))
          = (((j + 1 : ℤ) : ℝ) * firstPositiveSineZero) := by
              field_simp [h32m_ne]
      _ = (((j + 1 : ℤ) : ℝ) * Real.pi) := by rw [hpi]
  have harg0 :
      ((32 : ℝ) ^ m) * firstPositiveSineZero * ((j : ℝ) / ((32 : ℝ) ^ m))
        = (j : ℝ) * Real.pi := by
    calc
      ((32 : ℝ) ^ m) * firstPositiveSineZero * ((j : ℝ) / ((32 : ℝ) ^ m))
          = (j : ℝ) * firstPositiveSineZero := by
              field_simp [h32m_ne]
      _ = (j : ℝ) * Real.pi := by rw [hpi]
  unfold helperForProposition_4_7_13_diffTerm
  rw [hm_sub, harg1, harg0]
  have hcos_shift :
      Real.cos ((((j + 1 : ℤ) : ℝ) * Real.pi)) = -Real.cos ((j : ℝ) * Real.pi) := by
    have hcast : (((j + 1 : ℤ) : ℝ) * Real.pi) = (j : ℝ) * Real.pi + Real.pi := by
      calc
        (((j + 1 : ℤ) : ℝ) * Real.pi) = (((j : ℤ) : ℝ) + 1) * Real.pi := by norm_num
        _ = (j : ℝ) * Real.pi + Real.pi := by ring
    rw [hcast, Real.cos_add_pi]
  rw [hcos_shift]
  have habsInt : |Real.cos ((j : ℝ) * Real.pi)| = 1 := by
    simpa [mul_comm] using (Real.abs_cos_int_mul_pi j)
  calc
    |(1 / (4 : ℝ) ^ m) * (-Real.cos ((j : ℝ) * Real.pi)) -
        (1 / (4 : ℝ) ^ m) * Real.cos ((j : ℝ) * Real.pi)|
        = |(1 / (4 : ℝ) ^ m) * (-2 * Real.cos ((j : ℝ) * Real.pi))| := by ring_nf
    _ = |1 / (4 : ℝ) ^ m| * |-2 * Real.cos ((j : ℝ) * Real.pi)| := by rw [abs_mul]
    _ = (1 / (4 : ℝ) ^ m) * (|(-2 : ℝ)| * |Real.cos ((j : ℝ) * Real.pi)|) := by
          rw [abs_of_nonneg (by positivity), abs_mul]
    _ = (1 / (4 : ℝ) ^ m) * 2 := by
          rw [habsInt]
          norm_num
    _ = 2 / (4 : ℝ) ^ m := by ring

/-- Helper for Proposition 4.7.13: finite geometric bound for
`∑_{n < m-1} 8^{n+1}`. -/
lemma helperForProposition_4_7_13_sumPowEight_bound
    (m : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) ≤ ((8 : ℝ) ^ m) / 7 := by
  let S : ℝ := ∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ n
  have hgeom : S * ((8 : ℝ) - 1) = (8 : ℝ) ^ (m - 1) - 1 := by
    simpa [S] using (geom_sum_mul (8 : ℝ) (m - 1))
  have hgeom7 : S * 7 = (8 : ℝ) ^ (m - 1) - 1 := by
    nlinarith [hgeom]
  have hshift :
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) = (8 : ℝ) * S := by
    simp [S, pow_succ', Finset.mul_sum]
  have hmul :
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) * 7 = (8 : ℝ) ^ m - 8 := by
    calc
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) * 7
          = ((8 : ℝ) * S) * 7 := by rw [hshift]
      _ = (8 : ℝ) * (S * 7) := by ring
      _ = (8 : ℝ) * ((8 : ℝ) ^ (m - 1) - 1) := by rw [hgeom7]
      _ = (8 : ℝ) ^ m - 8 := by
            have hpow : (8 : ℝ) * (8 : ℝ) ^ (m - 1) = (8 : ℝ) ^ m := by
              rw [← pow_succ']
              simp [Nat.sub_add_cancel hm]
            linarith
  have hle_mul :
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) * 7 ≤ (8 : ℝ) ^ m := by
    calc
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) * 7 = (8 : ℝ) ^ m - 8 := hmul
      _ ≤ (8 : ℝ) ^ m := by nlinarith
  nlinarith [hle_mul]

/-- Helper for Proposition 4.7.13: each increment mode is bounded by a
Lipschitz estimate for cosine. -/
lemma helperForProposition_4_7_13_singleLowMode_absBound
    (j : ℤ) (m n : ℕ) :
    |helperForProposition_4_7_13_diffTerm j m n| ≤
      (Real.pi / (32 : ℝ) ^ m) * (8 : ℝ) ^ (n + 1) := by
  let a : ℝ := 1 / (4 : ℝ) ^ (n + 1)
  let u : ℝ :=
    ((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero *
      (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m))
  let v : ℝ :=
    ((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero *
      ((j : ℝ) / ((32 : ℝ) ^ m)
      )
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hcos : |Real.cos u - Real.cos v| ≤ |u - v| :=
    Real.abs_cos_sub_cos_le u v
  have hmul : a * |Real.cos u - Real.cos v| ≤ a * |u - v| :=
    mul_le_mul_of_nonneg_left hcos ha_nonneg
  have hleft :
      |a * Real.cos u - a * Real.cos v| = a * |Real.cos u - Real.cos v| := by
    calc
      |a * Real.cos u - a * Real.cos v| = |a * (Real.cos u - Real.cos v)| := by ring_nf
      _ = |a| * |Real.cos u - Real.cos v| := by rw [abs_mul]
      _ = a * |Real.cos u - Real.cos v| := by rw [abs_of_nonneg ha_nonneg]
  have h32m_ne : ((32 : ℝ) ^ m) ≠ 0 := by positivity
  have hgap :
      (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) - ((j : ℝ) / ((32 : ℝ) ^ m)) =
        1 / ((32 : ℝ) ^ m) := by
    have hcast : (((j + 1 : ℤ) : ℝ) - (j : ℝ)) = 1 := by
      norm_num
    calc
      (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) - ((j : ℝ) / ((32 : ℝ) ^ m))
          = ((((j + 1 : ℤ) : ℝ) - (j : ℝ)) / ((32 : ℝ) ^ m)) := by ring
      _ = 1 / ((32 : ℝ) ^ m) := by rw [hcast]
  have huv : u - v =
      (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero) * (1 / ((32 : ℝ) ^ m)) := by
    calc
      u - v =
          (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero) *
            ((((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) - ((j : ℝ) / ((32 : ℝ) ^ m))) := by
            dsimp [u, v]
            ring
      _ = (((32 : ℝ) ^ (n + 1)) * firstPositiveSineZero) * (1 / ((32 : ℝ) ^ m)) := by
            rw [hgap]
  have huv_abs :
      |u - v| = (((32 : ℝ) ^ (n + 1)) * Real.pi) * (1 / ((32 : ℝ) ^ m)) := by
    rw [huv, helperForTheorem_4_7_7_firstPositiveSineZero_eq_pi]
    have hnonnegA : 0 ≤ ((32 : ℝ) ^ (n + 1)) * Real.pi := by positivity
    have hnonnegB : 0 ≤ 1 / ((32 : ℝ) ^ m) := by positivity
    rw [abs_of_nonneg (mul_nonneg hnonnegA hnonnegB)]
  have hpow_cancel :
      ((32 : ℝ) ^ (n + 1)) * (1 / (4 : ℝ) ^ (n + 1)) = (8 : ℝ) ^ (n + 1) := by
    have hdecomp :
        (32 : ℝ) ^ (n + 1) = (4 : ℝ) ^ (n + 1) * (8 : ℝ) ^ (n + 1) := by
      calc
        (32 : ℝ) ^ (n + 1) = ((4 : ℝ) * 8) ^ (n + 1) := by norm_num
        _ = (4 : ℝ) ^ (n + 1) * (8 : ℝ) ^ (n + 1) := by rw [mul_pow]
    have h4pow_ne : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    calc
      ((32 : ℝ) ^ (n + 1)) * (1 / (4 : ℝ) ^ (n + 1))
          = ((4 : ℝ) ^ (n + 1) * (8 : ℝ) ^ (n + 1)) * (1 / (4 : ℝ) ^ (n + 1)) := by
              rw [hdecomp]
      _ = (8 : ℝ) ^ (n + 1) * ((4 : ℝ) ^ (n + 1) * (1 / (4 : ℝ) ^ (n + 1))) := by ring
      _ = (8 : ℝ) ^ (n + 1) * 1 := by
            congr 1
            field_simp [h4pow_ne]
      _ = (8 : ℝ) ^ (n + 1) := by ring
  have hbound :
      |a * Real.cos u - a * Real.cos v| ≤
        (Real.pi / (32 : ℝ) ^ m) * (8 : ℝ) ^ (n + 1) := by
    calc
      |a * Real.cos u - a * Real.cos v|
          = a * |Real.cos u - Real.cos v| := hleft
      _ ≤ a * |u - v| := hmul
      _ = (1 / (4 : ℝ) ^ (n + 1)) *
            ((((32 : ℝ) ^ (n + 1)) * Real.pi) * (1 / ((32 : ℝ) ^ m)) ) := by
            rw [huv_abs]
      _ = (Real.pi / (32 : ℝ) ^ m) *
            (((32 : ℝ) ^ (n + 1)) * (1 / (4 : ℝ) ^ (n + 1))) := by ring
      _ = (Real.pi / (32 : ℝ) ^ m) * (8 : ℝ) ^ (n + 1) := by rw [hpow_cancel]
  simpa [helperForProposition_4_7_13_diffTerm, a, u, v] using hbound

/-- Helper for Proposition 4.7.13: the finite sum of absolute low-mode terms is
bounded by the corresponding geometric series. -/
lemma helperForProposition_4_7_13_lowMode_sumAbs_bound
    (j : ℤ) (m : ℕ) :
    (∑ n ∈ Finset.range (m - 1), |helperForProposition_4_7_13_diffTerm j m n|) ≤
      (Real.pi / (32 : ℝ) ^ m) *
        (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) := by
  calc
    (∑ n ∈ Finset.range (m - 1), |helperForProposition_4_7_13_diffTerm j m n|)
        ≤ ∑ n ∈ Finset.range (m - 1),
            ((Real.pi / (32 : ℝ) ^ m) * (8 : ℝ) ^ (n + 1)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          exact helperForProposition_4_7_13_singleLowMode_absBound j m n
    _ = (Real.pi / (32 : ℝ) ^ m) *
          (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) := by
          rw [Finset.mul_sum]

/-- Helper for Proposition 4.7.13: the geometric-factor estimate implies the
final `1 / 4^m` bound. -/
lemma helperForProposition_4_7_13_lowMode_series_to_quarterPow
    (m : ℕ) (hm : 1 ≤ m) :
    (Real.pi / (32 : ℝ) ^ m) * (((8 : ℝ) ^ m) / 7) ≤ 1 / (4 : ℝ) ^ m := by
  have hratio : ((8 : ℝ) ^ m) / ((32 : ℝ) ^ m) = 1 / (4 : ℝ) ^ m := by
    have hdecomp : (32 : ℝ) ^ m = (8 : ℝ) ^ m * (4 : ℝ) ^ m := by
      calc
        (32 : ℝ) ^ m = ((8 : ℝ) * 4) ^ m := by norm_num
        _ = (8 : ℝ) ^ m * (4 : ℝ) ^ m := by rw [mul_pow]
    have h8pow_ne : (8 : ℝ) ^ m ≠ 0 := by positivity
    have h4pow_ne : (4 : ℝ) ^ m ≠ 0 := by positivity
    rw [hdecomp]
    field_simp [h8pow_ne, h4pow_ne]
  have hpi_div7_le_one : Real.pi / 7 ≤ (1 : ℝ) := by
    have hpi_div7_le_four_div7 : Real.pi / 7 ≤ (4 : ℝ) / 7 := by
      nlinarith [Real.pi_lt_four]
    have hfour_div7_le_one : (4 : ℝ) / 7 ≤ (1 : ℝ) := by norm_num
    exact le_trans hpi_div7_le_four_div7 hfour_div7_le_one
  have hpow_nonneg : 0 ≤ 1 / (4 : ℝ) ^ m := by positivity
  have hmul :
      (Real.pi / 7) * (1 / (4 : ℝ) ^ m) ≤ (1 : ℝ) * (1 / (4 : ℝ) ^ m) :=
    mul_le_mul_of_nonneg_right hpi_div7_le_one hpow_nonneg
  calc
    (Real.pi / (32 : ℝ) ^ m) * (((8 : ℝ) ^ m) / 7)
        = (Real.pi / 7) * (((8 : ℝ) ^ m) / ((32 : ℝ) ^ m)) := by ring
    _ = (Real.pi / 7) * (1 / (4 : ℝ) ^ m) := by rw [hratio]
    _ ≤ (1 : ℝ) * (1 / (4 : ℝ) ^ m) := hmul
    _ = 1 / (4 : ℝ) ^ m := by ring

/-- Helper for Proposition 4.7.13: the sum of low modes `n < m-1` is bounded by
`1 / 4^m` in absolute value. -/
lemma helperForProposition_4_7_13_lowModes_bound
    (j : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    |∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n| ≤
      1 / (4 : ℝ) ^ m := by
  have hsumAbs :
      (∑ n ∈ Finset.range (m - 1), |helperForProposition_4_7_13_diffTerm j m n|) ≤
        (Real.pi / (32 : ℝ) ^ m) *
          (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) :=
    helperForProposition_4_7_13_lowMode_sumAbs_bound j m
  have hgeom :
      (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) ≤ ((8 : ℝ) ^ m) / 7 :=
    helperForProposition_4_7_13_sumPowEight_bound m hm
  have hcoeff_nonneg : 0 ≤ Real.pi / (32 : ℝ) ^ m := by positivity
  have hscaled :
      (Real.pi / (32 : ℝ) ^ m) *
          (∑ n ∈ Finset.range (m - 1), (8 : ℝ) ^ (n + 1)) ≤
        (Real.pi / (32 : ℝ) ^ m) * (((8 : ℝ) ^ m) / 7) :=
    mul_le_mul_of_nonneg_left hgeom hcoeff_nonneg
  have hquarter :
      (Real.pi / (32 : ℝ) ^ m) * (((8 : ℝ) ^ m) / 7) ≤ 1 / (4 : ℝ) ^ m :=
    helperForProposition_4_7_13_lowMode_series_to_quarterPow m hm
  have habs :
      |∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n| ≤
        ∑ n ∈ Finset.range (m - 1), |helperForProposition_4_7_13_diffTerm j m n| := by
    simpa using (Finset.abs_sum_le_sum_abs
      (f := fun n => helperForProposition_4_7_13_diffTerm j m n)
      (s := Finset.range (m - 1)))
  exact le_trans habs (le_trans hsumAbs (le_trans hscaled hquarter))

/-- Helper for Proposition 4.7.13: if the main term has size `2/4^m` and the
error is bounded by `1/4^m`, then the total has size at least `1/4^m`. -/
lemma helperForProposition_4_7_13_absLowerBound_from_main_plus_error
    (m : ℕ) {main error : ℝ}
    (hmain : |main| = 2 / (4 : ℝ) ^ m)
    (herror : |error| ≤ 1 / (4 : ℝ) ^ m) :
    |main + error| ≥ 1 / (4 : ℝ) ^ m := by
  have htri : |main| ≤ |main + error| + |error| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      abs_add_le (main + error) (-error)
  have hmainLe : 2 / (4 : ℝ) ^ m ≤ |main + error| + 1 / (4 : ℝ) ^ m := by
    linarith [hmain, herror, htri]
  have hsub : 2 / (4 : ℝ) ^ m - 1 / (4 : ℝ) ^ m ≤ |main + error| := by
    linarith [hmainLe]
  have hleft : 2 / (4 : ℝ) ^ m - 1 / (4 : ℝ) ^ m = 1 / (4 : ℝ) ^ m := by ring
  linarith [hsub, hleft]

/-- Proposition 4.7.13: for every `j : ℤ` and every integer `m ≥ 1`,
for `f(x) = ∑_{n=1}^∞ 4^{-n} cos(32^n π x)` (with `π = firstPositiveSineZero`),
the increment across consecutive points of mesh size `32^{-m}` satisfies
`|f((j+1)/32^m) - f(j/32^m)| ≥ 4^{-m}`. -/
theorem scaledCosineSeries_increment_lower_bound
    (j : ℤ) (m : ℕ) (hm : 1 ≤ m) :
    |scaledCosineSeriesFunction (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) -
        scaledCosineSeriesFunction ((j : ℝ) / ((32 : ℝ) ^ m))| ≥
      (1 / ((4 : ℝ) ^ m)) := by
  have hfinite :
      scaledCosineSeriesFunction (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) -
          scaledCosineSeriesFunction ((j : ℝ) / ((32 : ℝ) ^ m)) =
        ∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n :=
    helperForProposition_4_7_13_increment_asFiniteSum j m
  have hsplit :
      (∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n) =
        (∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n) +
          helperForProposition_4_7_13_diffTerm j m (m - 1) := by
    calc
      (∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n)
          = (∑ n ∈ Finset.range ((m - 1) + 1), helperForProposition_4_7_13_diffTerm j m n) := by
              rw [Nat.sub_add_cancel hm]
      _ = (∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n) +
            helperForProposition_4_7_13_diffTerm j m (m - 1) :=
            Finset.sum_range_succ (fun n => helperForProposition_4_7_13_diffTerm j m n) (m - 1)
  have hmain :
      |helperForProposition_4_7_13_diffTerm j m (m - 1)| = 2 / (4 : ℝ) ^ m :=
    helperForProposition_4_7_13_mainMode_exact j m hm
  have hlow :
      |∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n| ≤
        1 / (4 : ℝ) ^ m :=
    helperForProposition_4_7_13_lowModes_bound j m hm
  have habs :
      |(∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n) +
          helperForProposition_4_7_13_diffTerm j m (m - 1)| ≥
        1 / (4 : ℝ) ^ m :=
    by
      have habs' :
          |helperForProposition_4_7_13_diffTerm j m (m - 1) +
              (∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n)| ≥
            1 / (4 : ℝ) ^ m :=
        helperForProposition_4_7_13_absLowerBound_from_main_plus_error
          (m := m)
          (main := helperForProposition_4_7_13_diffTerm j m (m - 1))
          (error := ∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n)
          hmain hlow
      simpa [add_comm] using habs'
  calc
    |scaledCosineSeriesFunction (((j + 1 : ℤ) : ℝ) / ((32 : ℝ) ^ m)) -
        scaledCosineSeriesFunction ((j : ℝ) / ((32 : ℝ) ^ m))|
        = |∑ n ∈ Finset.range m, helperForProposition_4_7_13_diffTerm j m n| := by
            rw [hfinite]
    _ = |(∑ n ∈ Finset.range (m - 1), helperForProposition_4_7_13_diffTerm j m n) +
          helperForProposition_4_7_13_diffTerm j m (m - 1)| := by rw [hsplit]
    _ ≥ 1 / (4 : ℝ) ^ m := habs


end Section07
end Chap04

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Example_6_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Lemma_11_18
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_44

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology ENNReal

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The textbook Laplace transform of the generation-size variable `Z_n` in the critical geometric
branching process started from `i`. -/
noncomputable def criticalGeometricBranchingLaplaceTransform (n i : ℕ) : ℝ → ℝ :=
  fun t ↦
    ((((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (Real.exp (-t))) ^ i)

/-- Evaluating `criticalGeometricBranchingLaplaceTransform` expands to the explicit iterate of the
critical geometric offspring pgf. -/
theorem criticalGeometricBranchingLaplaceTransform_apply (n i : ℕ) (t : ℝ) :
    criticalGeometricBranchingLaplaceTransform n i t =
      ((((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n])
        (Real.exp (-t))) ^ i) :=
  rfl

/-- The generation-size variable `Z_n` has the textbook Laplace transform of the critical
geometric branching process started from `i` under the probability law `P`. -/
def HasCriticalGeometricBranchingLaplaceTransform
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (i n : ℕ) : Prop :=
  ∀ t : ℝ,
    0 ≤ t →
      ∫ ω, Real.exp (-(t * (Z n ω : ℝ))) ∂(P : Measure Ω) =
        criticalGeometricBranchingLaplaceTransform n i t

/-- Unfolding `HasCriticalGeometricBranchingLaplaceTransform` gives the explicit Laplace-transform
identity. -/
theorem hasCriticalGeometricBranchingLaplaceTransform_iff
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (i n : ℕ) :
    HasCriticalGeometricBranchingLaplaceTransform P Z i n ↔
      ∀ t : ℝ,
        0 ≤ t →
          ∫ ω, Real.exp (-(t * (Z n ω : ℝ))) ∂(P : Measure Ω) =
            criticalGeometricBranchingLaplaceTransform n i t :=
  Iff.rfl

/-- Helper for Lemma 21.45: on `|s| < 2`, the critical geometric offspring pgf is the fractional
linear map `s ↦ 1 / (2 - s)`. -/
lemma criticalGeometricOffspringPgf_eq_fractionalLinear_of_abs_lt_two {s : ℝ} (hs : |s| < 2) :
    probabilityGeneratingFunctionReal criticalGeometricOffspringPMF s = 1 / (2 - s) := by
  -- Proof comment: rewrite the pgf as a geometric series with ratio `s / 2`, then sum it
  -- explicitly using the standard geometric-series identity.
  rw [probabilityGeneratingFunctionReal_apply]
  have hratio : |s / 2| < 1 := by
    have habs : |s| / 2 < 1 := by nlinarith [hs]
    simpa [abs_div] using habs
  calc
    ∑' n : ℕ, (criticalGeometricOffspringPMF n).toReal * s ^ n
        = ∑' n : ℕ, (1 / 2 : ℝ) * (s / 2) ^ n := by
            refine tsum_congr fun n ↦ ?_
            have hmass :
                (criticalGeometricOffspringPMF n).toReal = ((1 / 2 : ℝ) ^ n) * (1 / 2) := by
              rw [criticalGeometricOffspringPMF, geometricPMF]
              change (ENNReal.ofReal (geometricPMFReal (1 / 2 : ℝ) n)).toReal =
                ((1 / 2 : ℝ) ^ n) * (1 / 2)
              rw [ENNReal.toReal_ofReal]
              · have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
                rw [geometricPMFReal, hhalf]
              · exact geometricPMFReal_nonneg (show 0 < (1 / 2 : ℝ) by norm_num)
                  (show (1 / 2 : ℝ) ≤ 1 by norm_num)
            rw [hmass]
            have hpow : ((1 / 2 : ℝ) ^ n) * s ^ n = (s / 2) ^ n := by
              rw [← mul_pow]
              ring_nf
            calc
              ((1 / 2 : ℝ) ^ n * (1 / 2)) * s ^ n = (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ n) * s ^ n) := by
                ring
              _ = (1 / 2 : ℝ) * (s / 2) ^ n := by rw [hpow]
    _ = (1 / 2 : ℝ) * ∑' n : ℕ, (s / 2) ^ n := by rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) * (1 - s / 2)⁻¹ := by
          rw [(hasSum_geometric_of_abs_lt_one hratio).tsum_eq]
    _ = 1 / (2 - s) := by
          have hs_ne : s ≠ 2 := by
            intro hs_eq
            rw [hs_eq, abs_of_pos (by norm_num)] at hs
            linarith
          field_simp [hs_ne]

/-- Helper for Lemma 21.45: if `s` stays within `1 / (n + 1)` of `1`, then the Möbius
denominator `n + 1 - n * s` is positive. -/
lemma criticalGeometricFractionalLinear_denominator_pos_of_abs_sub_one_lt {n : ℕ} {s : ℝ}
    (hs : |s - 1| < 1 / (n + 1 : ℝ)) :
    0 < (n + 1 : ℝ) - n * s := by
  -- Proof comment: write the denominator as `1 - n * (s - 1)` and use the upper half of the
  -- radius bound around `1`.
  cases n with
  | zero =>
      norm_num
  | succ n =>
      have hs_upper := (abs_lt.mp hs).2
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hs_upper ⊢
      have hmul : (n.succ : ℝ) * (s - 1) < 1 := by
        have hs_mul : (n.succ : ℝ) * (s - 1) < (n.succ : ℝ) * (1 / (n + 2 : ℝ)) := by
          simpa [one_div] using mul_lt_mul_of_pos_left hs_upper (by positivity)
        have hfrac : (n.succ : ℝ) * (1 / (n + 2 : ℝ)) < 1 := by
          field_simp [show (n + 2 : ℝ) ≠ 0 by positivity]
          norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
        linarith
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hmul ⊢
      nlinarith

/-- Helper for Lemma 21.45: if `s` stays within `1 / (n + 1)` of `1`, then the Möbius numerator
`n - (n - 1) * s` is positive. -/
lemma criticalGeometricFractionalLinear_numerator_pos_of_abs_sub_one_lt {n : ℕ} (hn : 1 ≤ n)
    {s : ℝ}
    (hs : |s - 1| < 1 / (n + 1 : ℝ)) :
    0 < (n : ℝ) - (n - 1 : ℕ) * s := by
  -- Proof comment: rewrite the numerator as `1 - (n - 1) * (s - 1)` and again use the radius
  -- bound around `1`.
  cases n with
  | zero =>
      cases hn
  | succ n =>
      cases n with
      | zero =>
          norm_num
      | succ m =>
          have hs_upper := (abs_lt.mp hs).2
          norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hs_upper ⊢
          have hmul : ((m + 1 : ℕ) : ℝ) * (s - 1) < 1 := by
            have hs_mul :
                ((m + 1 : ℕ) : ℝ) * (s - 1) < ((m + 1 : ℕ) : ℝ) * (1 / (m + 3 : ℝ)) := by
              simpa [one_div] using mul_lt_mul_of_pos_left hs_upper (by positivity)
            have hfrac : (((m + 1 : ℕ) : ℝ) * (1 / (m + 3 : ℝ))) < 1 := by
              field_simp [show (m + 3 : ℝ) ≠ 0 by positivity]
              norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
            linarith
          norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hmul ⊢
          nlinarith

/-- Helper for Lemma 21.45: under the local radius condition around `1`, the fractional-linear
iterate value stays in `(0, 2)`. -/
private lemma criticalGeometricFractionalLinear_value_pos_lt_two_of_abs_sub_one_lt {n : ℕ}
    (hn : 1 ≤ n) {s : ℝ} (hs : |s - 1| < 1 / (n + 1 : ℝ)) :
    0 < (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) ∧
      (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) < 2 := by
  have hnum :
      0 < (n : ℝ) - (n - 1) * s :=
    by
      simpa [Nat.cast_sub hn] using
        criticalGeometricFractionalLinear_numerator_pos_of_abs_sub_one_lt hn hs
  have hden : 0 < (n + 1 : ℝ) - n * s :=
    criticalGeometricFractionalLinear_denominator_pos_of_abs_sub_one_lt hs
  have hs_upper := (abs_lt.mp hs).2
  have hlt :
      (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) < 2 := by
    rw [div_lt_iff₀ hden]
    have hs_mul : (n + 1 : ℝ) * (s - 1) < 1 := by
      have hs_mul' :
          (n + 1 : ℝ) * (s - 1) < (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) := by
        simpa [one_div] using mul_lt_mul_of_pos_left hs_upper (by positivity)
      have h_cancel : (n + 1 : ℝ) * (1 / (n + 1 : ℝ)) = 1 := by
        field_simp
      rw [h_cancel] at hs_mul'
      exact hs_mul'
    nlinarith
  exact ⟨div_pos hnum hden, hlt⟩

/-- Helper for Lemma 21.45: the positive iterates satisfy the Möbius formula on a small
neighborhood of the fixed point `1`. -/
private lemma criticalGeometricOffspringPgf_iterate_succ_eq_fractionalLinear_of_abs_sub_one_lt
    (m : ℕ) {s : ℝ} (hs : |s - 1| < 1 / (m + 2 : ℝ)) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[m + 1]) s =
      ((((m + 1 : ℕ) : ℝ) - m * s) / (m + 2 - (m + 1) * s)) := by
  induction m generalizing s with
  | zero =>
      have hs_lower := (abs_lt.mp hs).1
      have hs_upper := (abs_lt.mp hs).2
      have hs_pos : 0 < s := by
        linarith
      have hs_lt_two : s < 2 := by
        linarith
      have hs_abs_lt_two : |s| < 2 := by
        simpa [abs_of_pos hs_pos] using hs_lt_two
      -- Proof comment: the first positive iterate is just the pgf itself, so the local
      -- geometric-series formula closes the base step.
      simpa [Function.iterate_one] using
        criticalGeometricOffspringPgf_eq_fractionalLinear_of_abs_lt_two hs_abs_lt_two
  | succ m ih =>
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hs
      have hbound :
          (m + 3 : ℝ)⁻¹ < (m + 2 : ℝ)⁻¹ := by
        field_simp
        nlinarith
      have hs' : |s - 1| < (m + 2 : ℝ)⁻¹ := lt_trans hs hbound
      have hih := ih (by simpa [one_div] using hs')
      have hm_pos : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have hs_for_m1 : |s - 1| < (↑m + 1 + 1 : ℝ)⁻¹ := by
        simpa [show (2 : ℝ) = 1 + 1 by norm_num, add_assoc] using hs'
      have hz_pos_lt_two :=
        by
          simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm, one_div,
            show (2 : ℝ) = 1 + 1 by norm_num] using
            criticalGeometricFractionalLinear_value_pos_lt_two_of_abs_sub_one_lt (n := m + 1)
              (s := s) hm_pos (by simpa [one_div] using hs_for_m1)
      have hz_abs_lt_two :
          |((((m + 1 : ℕ) : ℝ) - m * s) / (m + 2 - (m + 1) * s))| < 2 := by
        simpa [abs_of_pos hz_pos_lt_two.1, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm,
          add_comm, show (2 : ℝ) = 1 + 1 by norm_num] using hz_pos_lt_two.2
      have hden :
          0 < (m + 2 : ℝ) - (m + 1) * s :=
        by
          simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm, one_div,
            show (2 : ℝ) = 1 + 1 by norm_num] using
            criticalGeometricFractionalLinear_denominator_pos_of_abs_sub_one_lt (n := m + 1)
              (s := s) (by simpa [one_div] using hs_for_m1)
      have hnextDen :
          0 < (m + 3 : ℝ) - (m + 2) * s :=
        by
          have hs_for_m2 : |s - 1| < (↑m + 2 + 1 : ℝ)⁻¹ := by
            simpa [show (3 : ℝ) = 2 + 1 by norm_num, add_assoc] using hs
          simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm, one_div,
            show (3 : ℝ) = 2 + 1 by norm_num] using
            criticalGeometricFractionalLinear_denominator_pos_of_abs_sub_one_lt (n := m + 2)
              (s := s) (by simpa [one_div] using hs_for_m2)
      -- Proof comment: rewrite the next iterate through the local pgf formula and simplify the
      -- resulting rational identity once both denominators are known to be nonzero.
      rw [Nat.add_assoc, Function.iterate_succ_apply', hih]
      rw [criticalGeometricOffspringPgf_eq_fractionalLinear_of_abs_lt_two hz_abs_lt_two]
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
      field_simp [ne_of_gt hden, ne_of_gt hnextDen]
      ring

/-- Helper for Lemma 21.45: close to `1`, the `n`th iterate of the critical geometric offspring
pgf is the textbook fractional-linear expression. -/
lemma criticalGeometricOffspringPgf_iterate_eq_fractionalLinear_of_abs_sub_one_lt
    {n : ℕ} (hn : 1 ≤ n) {s : ℝ}
    (hs : |s - 1| < 1 / (n + 1 : ℝ)) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) s =
      (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)) with
    ⟨m, rfl⟩
  have hs' : |s - 1| < 1 / (m + 2 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
      show (2 : ℝ) = 1 + 1 by norm_num] using hs
  -- Proof comment: after writing the positive iterate index as `m + 1`, the general wrapper is
  -- exactly the already-proved successor-step formula.
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
    show (2 : ℝ) = 1 + 1 by norm_num] using
    criticalGeometricOffspringPgf_iterate_succ_eq_fractionalLinear_of_abs_sub_one_lt (m := m)
      (s := s) hs'

/-- Helper for Lemma 21.45: on the nonnegative half-line, the branching Laplace transform is the
explicit fractional-linear model from Lemma 21.44. -/
lemma criticalGeometricBranchingLaplaceTransform_eq_explicit_of_nonneg
    {n i : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    criticalGeometricBranchingLaplaceTransform n i t =
      ((((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t))) ^ i) := by
  -- Proof comment: for `t ≥ 0`, the Laplace argument `exp (-t)` lies in `[0, 1]`, so the exact
  -- iterate formula from Lemma 21.44 applies directly.
  have hs : Real.exp (-t) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Real.exp_pos _).le, ?_⟩
    simpa using Real.exp_le_one_iff.mpr (by linarith : -t ≤ 0)
  rw [criticalGeometricBranchingLaplaceTransform_apply,
    critical_geometric_offspring_pgf_iterate_eq n hn (Real.exp (-t)) hs]

/-- Helper for Lemma 21.45: for positive generations, the textbook Laplace transform agrees near
`0` with the explicit fractional-linear model. -/
lemma criticalGeometricBranchingLaplaceTransform_eq_explicit_nhds_zero
    {n i : ℕ} (hn : 1 ≤ n) :
    criticalGeometricBranchingLaplaceTransform n i =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦
        ((((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t))) ^ i) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)) with
    ⟨m, rfl⟩
  have h_near_one :
      ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |Real.exp (-t) - 1| < 1 / (m + 2 : ℝ) := by
    have h_radius : 0 < (1 / (m + 2 : ℝ)) := by positivity
    have h_tendsto : Tendsto (fun t : ℝ ↦ Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa using (show ContinuousAt (fun t : ℝ ↦ Real.exp (-t)) 0 by fun_prop).tendsto
    -- Proof comment: continuity of `t ↦ exp (-t)` at `0` moves the local iterate formula from a
    -- neighborhood of `1` back to a neighborhood of the Laplace origin `0`.
    simpa [Metric.ball, Real.dist_eq] using h_tendsto (Metric.ball_mem_nhds (1 : ℝ) h_radius)
  filter_upwards [h_near_one] with t ht
  have h_iter :=
    criticalGeometricOffspringPgf_iterate_succ_eq_fractionalLinear_of_abs_sub_one_lt (m := m)
      (s := Real.exp (-t)) ht
  have h_iter_pow := congrArg (fun x : ℝ ↦ x ^ i) h_iter
  rw [criticalGeometricBranchingLaplaceTransform_apply]
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
    show (2 : ℝ) = 1 + 1 by norm_num] using h_iter_pow

/-- Helper for Lemma 21.45: every positive iterate of the critical geometric offspring pgf agrees
near `1` with its explicit fractional-linear model. -/
lemma criticalGeometricOffspringPgf_iterate_eq_fractionalLinear_nhds_one
    {n : ℕ} (hn : 1 ≤ n) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) =ᶠ[𝓝 (1 : ℝ)]
      fun s ↦ (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)) with
    ⟨m, rfl⟩
  have h_ball :
      ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), |s - 1| < 1 / (m + 2 : ℝ) := by
    have h_radius : 0 < (1 / (m + 2 : ℝ)) := by positivity
    simpa [Metric.ball, Real.dist_eq] using
      Metric.ball_mem_nhds (1 : ℝ) h_radius
  -- Proof comment: the local Möbius formula is already proved on the textbook radius around `1`,
  -- so the neighborhood statement is just the corresponding filter lift.
  filter_upwards [h_ball] with s hs
  simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
    show (2 : ℝ) = 1 + 1 by norm_num] using
    criticalGeometricOffspringPgf_iterate_succ_eq_fractionalLinear_of_abs_sub_one_lt (m := m)
      (s := s) hs

/-- Helper for Lemma 21.45: near `1`, the critical geometric offspring pgf agrees with the
fractional-linear model `s ↦ 1 / (2 - s)`. -/
lemma criticalGeometricOffspringPgf_eq_fractionalLinear_nhds_one :
    probabilityGeneratingFunctionReal criticalGeometricOffspringPMF =ᶠ[𝓝 (1 : ℝ)]
      fun s ↦ 1 / (2 - s) := by
  -- Proof comment: a radius-`1` neighborhood of `1` stays inside `(-2, 2)`, where the explicit
  -- pgf formula already holds.
  have h_ball : ∀ᶠ s : ℝ in 𝓝 (1 : ℝ), |s - 1| < 1 := by
    simpa [Metric.ball, Real.dist_eq] using Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h_ball] with s hs
  have hs_pos : 0 < s := by
    have hs_lower := (abs_lt.mp hs).1
    linarith
  have hs_lt_two : s < 2 := by
    have hs_upper := (abs_lt.mp hs).2
    linarith
  have hs_abs_lt_two : |s| < 2 := by
    simpa [abs_of_pos hs_pos] using hs_lt_two
  exact criticalGeometricOffspringPgf_eq_fractionalLinear_of_abs_lt_two hs_abs_lt_two

/-- Helper for Lemma 21.45: the critical geometric offspring pgf fixes `1`. -/
lemma criticalGeometricOffspringPgf_eval_one :
    probabilityGeneratingFunctionReal criticalGeometricOffspringPMF 1 = 1 := by
  -- Proof comment: the local fractional-linear model is defined at `1` and evaluates to `1`.
  rw [criticalGeometricOffspringPgf_eq_fractionalLinear_of_abs_lt_two
    (s := (1 : ℝ)) (by norm_num)]
  norm_num

/-- Helper for Lemma 21.45: the critical geometric offspring pgf is analytic at the fixed point
`1`. -/
lemma criticalGeometricOffspringPgf_analyticAt_one :
    AnalyticAt ℝ (probabilityGeneratingFunctionReal criticalGeometricOffspringPMF) 1 := by
  -- Proof comment: transfer analyticity from the rational model `s ↦ 1 / (2 - s)` using the
  -- neighborhood equality around `1`.
  have h_frac : AnalyticAt ℝ (fun s : ℝ ↦ 1 / (2 - s)) 1 := by
    have h_sub : AnalyticAt ℝ (fun s : ℝ ↦ 2 - s) 1 := by
      fun_prop
    simpa [one_div] using h_sub.inv (by norm_num : (2 : ℝ) - 1 ≠ 0)
  exact h_frac.congr criticalGeometricOffspringPgf_eq_fractionalLinear_nhds_one.symm

/-- Helper for Lemma 21.45: every iterate of the critical geometric offspring pgf still fixes `1`.
-/
lemma criticalGeometricOffspringPgf_iterate_eval_one (n : ℕ) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) 1 = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- Proof comment: once the previous iterate lands at the fixed point `1`, the next pgf
      -- application also returns `1`.
      simp [Function.iterate_succ_apply', ih, criticalGeometricOffspringPgf_eval_one]

/-- Helper for Lemma 21.45: every iterate of the critical geometric offspring pgf is analytic at
the fixed point `1`. -/
lemma criticalGeometricOffspringPgf_iterate_analyticAt_one (n : ℕ) :
    AnalyticAt ℝ (((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n])) 1 := by
  induction n with
  | zero =>
      simpa using (analyticAt_id : AnalyticAt ℝ (fun s : ℝ ↦ s) 1)
  | succ n ih =>
      -- Proof comment: compose the analytic pgf with the previous analytic iterate, using that
      -- the iterate value at `1` is still the fixed point.
      simpa [Function.iterate_succ_apply'] using
        ih.comp_of_eq criticalGeometricOffspringPgf_analyticAt_one
          criticalGeometricOffspringPgf_eval_one

/-- Helper for Lemma 21.45: every iterate of the critical geometric offspring pgf has derivative
`1` at the fixed point `1`. -/
lemma criticalGeometricOffspringPgf_iterate_hasDerivAt_one (n : ℕ) :
    HasDerivAt (((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n])) 1 1 := by
  induction n with
  | zero =>
      simpa using (hasDerivAt_id (1 : ℝ))
  | succ n ih =>
      -- Proof comment: the pgf derivative at `1` is `1`, so composing with the previous iterate
      -- preserves the unit derivative.
      have hpgf :
          HasDerivAt (probabilityGeneratingFunctionReal criticalGeometricOffspringPMF) 1 1 := by
        have h_frac :
            HasDerivAt (fun s : ℝ ↦ 1 / (2 - s)) 1 1 := by
          have hsub : HasDerivAt (fun s : ℝ ↦ 2 - s) (-1) 1 := by
            simpa using (hasDerivAt_const (1 : ℝ) (2 : ℝ)).sub (hasDerivAt_id (1 : ℝ))
          have h_inv :
              HasDerivAt (fun s : ℝ ↦ (2 - s)⁻¹)
                (-(-1 : ℝ) / ((2 : ℝ) - 1) ^ 2) 1 := by
            exact hsub.inv (by norm_num : (2 : ℝ) - 1 ≠ 0)
          norm_num at h_inv
          simpa [one_div] using h_inv
        exact h_frac.congr_of_eventuallyEq criticalGeometricOffspringPgf_eq_fractionalLinear_nhds_one
      simpa [Function.iterate_succ_apply'] using
        ih.comp_of_eq (x := (1 : ℝ)) hpgf criticalGeometricOffspringPgf_eval_one.symm

/-- Helper for Lemma 21.45: the critical-geometric branching Laplace transform is analytic at the
origin. -/
lemma criticalGeometricBranchingLaplaceTransform_analyticAt_zero (n i : ℕ) :
    AnalyticAt ℝ (criticalGeometricBranchingLaplaceTransform n i) 0 := by
  -- Route correction: compose the iterate-analyticity at the fixed point `1` with
  -- `t ↦ exp (-t)` instead of proving the stronger neighborhood explicit formula first.
  have h_exp :
      AnalyticAt ℝ (fun t : ℝ ↦ Real.exp (-t)) 0 := by
    fun_prop
  have h_inner :
      AnalyticAt ℝ
        (fun t : ℝ ↦
          ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (Real.exp (-t)))
        0 := by
    exact (criticalGeometricOffspringPgf_iterate_analyticAt_one n).comp_of_eq h_exp (by simp)
  simpa [criticalGeometricBranchingLaplaceTransform] using h_inner.pow i

/-- Helper for Lemma 21.45: the critical-geometric branching Laplace transform has first
derivative `-i` at the origin. -/
lemma criticalGeometricBranchingLaplaceTransform_hasDerivAt_zero (n i : ℕ) :
    HasDerivAt (criticalGeometricBranchingLaplaceTransform n i) (-(i : ℝ)) 0 := by
  -- Proof comment: the iterate contributes derivative `1` at the fixed point `1`, while
  -- `t ↦ exp (-t)` contributes the sign `-1`; the outer power then multiplies by `i`.
  have h_exp :
      HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-1) 0 := by
    simpa using (show HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (Real.exp (-0) * (-1)) 0 by
      simpa using ((hasDerivAt_id (0 : ℝ)).neg).exp)
  have h_inner :
      HasDerivAt
        (fun t : ℝ ↦
          ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (Real.exp (-t)))
        (-1) 0 := by
    simpa using
      (criticalGeometricOffspringPgf_iterate_hasDerivAt_one n).comp_of_eq (x := (0 : ℝ)) h_exp
        (by simp)
  simpa [criticalGeometricBranchingLaplaceTransform, criticalGeometricOffspringPgf_iterate_eval_one n]
    using h_inner.pow i

/-- Helper for Lemma 21.45: for `t > 0`, the moment-generating function of `-(Z n)` is the
branching Laplace transform. -/
lemma criticalGeometricBranchingLaplaceTransform_eq_mgf_neg
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) {t : ℝ} (ht : 0 < t) :
    mgf (fun ω ↦ -((Z n ω : ℝ))) (P : Measure Ω) t =
      criticalGeometricBranchingLaplaceTransform n i t := by
  -- Proof comment: this is just the source Laplace-transform identity rewritten in `mgf` form.
  simpa [ProbabilityTheory.mgf, neg_mul, mul_comm, mul_left_comm, mul_assoc]
    using h_laplace t ht.le

/-- Helper for Lemma 21.45: the zeroth iterate case is the elementary exponential model
`t ↦ exp (-(t i))`. -/
theorem criticalGeometricBranchingLaplaceTransform_zero (i : ℕ) :
    criticalGeometricBranchingLaplaceTransform 0 i = fun t ↦ Real.exp (-(t * i)) := by
  ext t
  -- Proof comment: with zero iterations, only the initial-state power `exp (-t)^i` remains.
  simp [criticalGeometricBranchingLaplaceTransform]
  simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.exp_nat_mul (-t) i).symm

/-- Helper for Lemma 21.45: the explicit branching Laplace transform is strictly positive for
every positive Laplace parameter. -/
lemma criticalGeometricBranchingLaplaceTransform_pos_of_pos {n i : ℕ} {t : ℝ} (ht : 0 < t) :
    0 < criticalGeometricBranchingLaplaceTransform n i t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · rw [criticalGeometricBranchingLaplaceTransform_zero]
    exact Real.exp_pos _
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranchingLaplaceTransform_eq_explicit_of_nonneg hn ht.le]
    have hexp_lt_one : Real.exp (-t) < 1 := by
      simpa using Real.exp_lt_one_iff.mpr (by linarith : -t < 0)
    have hden : 0 < (n + 1 : ℝ) - n * Real.exp (-t) := by
      have hn_nonneg : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      nlinarith
    have hnum : 0 < (n : ℝ) - ((n : ℝ) - 1) * Real.exp (-t) := by
      have hn_cast : (1 : ℝ) ≤ n := by
        exact_mod_cast hn
      nlinarith
    simpa [Nat.cast_sub hn] using pow_pos (div_pos hnum hden) i

/-- Helper for Lemma 21.45: the Laplace-transform identity forces
`ω ↦ (Z n ω : ℝ)` to be almost-everywhere measurable. -/
lemma criticalGeometricBranching_aemeasurable
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    AEMeasurable (fun ω ↦ (Z n ω : ℝ)) (P : Measure Ω) := by
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  let μ : Measure Ω := (P : Measure Ω)
  have hExp_int : Integrable (fun ω ↦ Real.exp (-(X ω))) μ := by
    -- Proof comment: the Laplace-transform identity at `t = 1` gives a nonzero integral, hence an
    -- integrable exponential representative.
    apply Integrable.of_integral_ne_zero
    have hmgf :
        mgf (-X) μ 1 = criticalGeometricBranchingLaplaceTransform n i 1 := by
      simpa [X, μ] using
        criticalGeometricBranchingLaplaceTransform_eq_mgf_neg P Z h_laplace zero_lt_one
    have hnonzero : mgf (-X) μ 1 ≠ 0 := by
      rw [hmgf]
      exact ne_of_gt (criticalGeometricBranchingLaplaceTransform_pos_of_pos (n := n) (i := i)
        zero_lt_one)
    simpa [ProbabilityTheory.mgf, X, μ] using hnonzero
  have hExp_ae : AEMeasurable (fun ω ↦ Real.exp (-(X ω))) μ :=
    hExp_int.aestronglyMeasurable.aemeasurable
  have hlog_ae : AEMeasurable (fun ω ↦ -Real.log (Real.exp (-(X ω)))) μ :=
    (hExp_ae.log).neg
  have h_eq :
      (fun ω ↦ -Real.log (Real.exp (-(X ω)))) =ᵐ[μ] X := by
    exact Eventually.of_forall fun ω ↦ by
      simp [X]
  exact hlog_ae.congr h_eq

/-- Helper for Lemma 21.45: the signed derivatives of the branching Laplace transform converge
from the right to the `ENNReal` moments of `Z_n`. -/
lemma criticalGeometricBranchingSignedIteratedDeriv_tendsto_right_zero
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) (k : ℕ) :
    Tendsto
      (fun t : ℝ ↦
        ENNReal.ofReal
          (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ ω, ENNReal.ofReal (((Z n ω : ℝ)) ^ k) ∂(P : Measure Ω))) := by
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  let μ : Measure Ω := (P : Measure Ω)
  have hX_ae : AEMeasurable X μ := criticalGeometricBranching_aemeasurable P Z h_laplace
  have hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω := Eventually.of_forall fun ω ↦ by
    positivity
  let Xm : Ω → ℝ := hX_ae.mk X
  have hXm_meas : Measurable Xm := hX_ae.measurable_mk
  have hX_eq_Xm : X =ᵐ[μ] Xm := hX_ae.ae_eq_mk
  have hXm_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Xm ω := by
    filter_upwards [hX_nonneg, hX_eq_Xm] with ω hω hω_eq
    simpa [hω_eq] using hω
  have h_eqOn :
      Set.EqOn (mgf (-Xm) μ) (criticalGeometricBranchingLaplaceTransform n i) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    calc
      mgf (-Xm) μ r = mgf (-X) μ r := by
        rw [ProbabilityTheory.mgf, ProbabilityTheory.mgf]
        refine integral_congr_ae ?_
        filter_upwards [hX_eq_Xm] with ω hω_eq
        simp [X, Xm, hω_eq]
      _ = criticalGeometricBranchingLaplaceTransform n i r := by
        simpa [X, μ] using
          criticalGeometricBranchingLaplaceTransform_eq_mgf_neg P Z h_laplace hr
  have h_iterEq :
      Set.EqOn (iteratedDeriv k (mgf (-Xm) μ))
        (iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i)) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    have h_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have h_within := iteratedDerivWithin_congr (n := k) (s := Set.Ioi (0 : ℝ)) h_eqOn
    calc
      iteratedDeriv k (mgf (-Xm) μ) r =
          iteratedDerivWithin k (mgf (-Xm) μ) (Set.Ioi (0 : ℝ)) r := by
            symm
            exact iteratedDerivWithin_of_isOpen (n := k) (f := mgf (-Xm) μ) h_open hr
      _ =
          iteratedDerivWithin k (criticalGeometricBranchingLaplaceTransform n i) (Set.Ioi (0 : ℝ))
            r :=
        h_within hr
      _ = iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r := by
            exact iteratedDerivWithin_of_isOpen
              (n := k) (f := criticalGeometricBranchingLaplaceTransform n i) h_open hr
  have h_limit_mgf :
      Tendsto
        (fun t : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ k) * iteratedDeriv k (mgf (-Xm) μ) t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ)) :=
    tendsto_ofReal_signed_iteratedDeriv_laplaceTransform_right_zero hXm_meas hXm_nonneg k
  have h_eventually_eq :
      (fun t : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ k) * iteratedDeriv k (mgf (-Xm) μ) t)) =ᶠ[𝓝[>] 0]
        (fun t : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) t)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [h_iterEq ht.1]
  have h_limit_transform :
      Tendsto
        (fun t : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ)) := by
    exact Filter.Tendsto.congr' h_eventually_eq h_limit_mgf
  have h_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ =
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ k) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX_eq_Xm] with ω hω_eq
    simp [hω_eq]
  rw [h_lintegral_eq] at h_limit_transform
  simpa [X, μ] using h_limit_transform

-- Proof sketch: differentiate the Laplace-transform identity from the branching-process setup
-- `k` times at `λ = 0`, move the factor `(-1)^k` through the derivatives of
-- `exp (-(λ Z_n))`, and then evaluate at `0`.
/-- Auxiliary consequence of Lemma 21.45: the `k`th moment of `Z_n` is obtained from the signed `k`th derivative at
`0` of the explicit Laplace transform
`λ ↦ ((((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) (e^{-λ}))^i)`. -/
theorem criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) (k : ℕ) :
    moment (fun ω ↦ (Z n ω : ℝ)) k (P : Measure Ω) =
      (-1 : ℝ) ^ k * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0 := by
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  let μ : Measure Ω := (P : Measure Ω)
  have hX_ae : AEMeasurable X μ := criticalGeometricBranching_aemeasurable P Z h_laplace
  have hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω := Eventually.of_forall fun ω ↦ by
    positivity
  let Xm : Ω → ℝ := hX_ae.mk X
  have hXm_meas : Measurable Xm := hX_ae.measurable_mk
  have hX_eq_Xm : X =ᵐ[μ] Xm := hX_ae.ae_eq_mk
  have hXm_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Xm ω := by
    filter_upwards [hX_nonneg, hX_eq_Xm] with ω hω hω_eq
    simpa [hω_eq] using hω
  have h_eqOn :
      Set.EqOn (mgf (-Xm) μ) (criticalGeometricBranchingLaplaceTransform n i) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    calc
      mgf (-Xm) μ r = mgf (-X) μ r := by
        rw [ProbabilityTheory.mgf, ProbabilityTheory.mgf]
        refine integral_congr_ae ?_
        filter_upwards [hX_eq_Xm] with ω hω_eq
        simp [X, Xm, hω_eq]
      _ = criticalGeometricBranchingLaplaceTransform n i r := by
        simpa [X, μ] using
          criticalGeometricBranchingLaplaceTransform_eq_mgf_neg P Z h_laplace hr
  have h_iterEq :
      Set.EqOn (iteratedDeriv k (mgf (-Xm) μ))
        (iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i)) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    have h_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have h_within :=
      iteratedDerivWithin_congr (n := k) (s := Set.Ioi (0 : ℝ)) h_eqOn
    -- Proof comment: on the open right half-line, the iterated derivatives agree because the
    -- transform agrees there with the measurable-representative mgf.
    calc
      iteratedDeriv k (mgf (-Xm) μ) r =
          iteratedDerivWithin k (mgf (-Xm) μ) (Set.Ioi (0 : ℝ)) r := by
            symm
            exact iteratedDerivWithin_of_isOpen (n := k) (f := mgf (-Xm) μ) h_open hr
      _ =
          iteratedDerivWithin k (criticalGeometricBranchingLaplaceTransform n i) (Set.Ioi (0 : ℝ))
            r :=
        h_within hr
      _ = iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r := by
            exact iteratedDerivWithin_of_isOpen
              (n := k) (f := criticalGeometricBranchingLaplaceTransform n i) h_open hr
  have h_limit_transform :
      Tendsto
        (fun t : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((X ω) ^ k) ∂μ)) := by
    simpa [X, μ] using
      criticalGeometricBranchingSignedIteratedDeriv_tendsto_right_zero P Z h_laplace k
  have h_analytic :
      AnalyticAt ℝ (criticalGeometricBranchingLaplaceTransform n i) 0 :=
    criticalGeometricBranchingLaplaceTransform_analyticAt_zero n i
  have h_iterCont :
      ContinuousAt
        (fun r : ℝ ↦ iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r) 0 := by
    simpa [iteratedDeriv_eq_iterate] using (h_analytic.iterated_deriv k).continuousAt
  have h_signedCont :
      ContinuousAt
        (fun r : ℝ ↦
          ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r)
        0 :=
    h_iterCont.const_mul ((-1 : ℝ) ^ k)
  have h_limit_value :
      Tendsto
        (fun r : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (h_signedCont.tendsto.mono_left nhdsWithin_le_nhds)
  have h_lintegral :
      ∫⁻ ω, ENNReal.ofReal ((X ω) ^ k) ∂μ =
        ENNReal.ofReal
          (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0) :=
    tendsto_nhds_unique h_limit_transform h_limit_value
  have h_signed_nonneg_pos :
      ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have h_sign :
        ∀ ω,
          ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) =
            (Xm ω) ^ k * Real.exp (-(r * Xm ω)) := by
      intro ω
      have hpow :
          ((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k = (Xm ω) ^ k := by
        calc
          ((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k =
              ((-1 : ℝ) ^ k) * (((-1 : ℝ) * Xm ω) ^ k) := by
                congr 1
                ring
          _ = ((-1 : ℝ) ^ k) * (((-1 : ℝ) ^ k) * (Xm ω) ^ k) := by
                rw [mul_pow]
          _ = ((((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k) * (Xm ω) ^ k) := by ring
          _ = (Xm ω) ^ k := by
                rw [← pow_add]
                simp
      calc
        ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) =
            (((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k) * Real.exp (-(r * Xm ω)) := by ring
        _ = (Xm ω) ^ k * Real.exp (-(r * Xm ω)) := by rw [hpow]
    rw [← h_iterEq hr.1, iteratedDeriv_laplaceTransform_eq hXm_meas hXm_nonneg k hr.1]
    calc
      ((-1 : ℝ) ^ k) * ∫ ω, (-(Xm ω)) ^ k * Real.exp (-(r * Xm ω)) ∂μ =
          ∫ ω, ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) ∂μ := by
            rw [← integral_const_mul]
      _ = ∫ ω, (Xm ω) ^ k * Real.exp (-(r * Xm ω)) ∂μ := by
            refine integral_congr_ae (Eventually.of_forall h_sign)
      _ ≥ 0 := by
            refine integral_nonneg_of_ae ?_
            filter_upwards [hXm_nonneg] with ω hω
            exact mul_nonneg (pow_nonneg hω _) (Real.exp_pos _).le
  have h_signed_nonneg :
      0 ≤ ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0 := by
    have h_tendsto_signed :
        Tendsto
          (fun r : ℝ ↦
            ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r)
          (𝓝[>] (0 : ℝ))
          (𝓝 (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0)) :=
      h_signedCont.tendsto.mono_left nhdsWithin_le_nhds
    have h_nonneg_mem :
        ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) r ∈
            Set.Ici (0 : ℝ) := h_signed_nonneg_pos
    exact IsClosed.mem_of_tendsto isClosed_Ici h_tendsto_signed h_nonneg_mem
  have h_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ =
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ k) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX_eq_Xm] with ω hω_eq
    simp [hω_eq]
  have h_pow_nonneg_Xm : 0 ≤ᵐ[μ] fun ω ↦ (Xm ω) ^ k := by
    filter_upwards [hXm_nonneg] with ω hω
    exact pow_nonneg hω _
  have h_pow_int_Xm :
      Integrable (fun ω ↦ (Xm ω) ^ k) μ := by
    have h_meas_enn :
        AEMeasurable (fun ω ↦ ENNReal.ofReal ((Xm ω) ^ k)) μ := by
      fun_prop
    have h_lintegral_ne_top :
        ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ ≠ ∞ := by
      rw [h_lintegral_eq, h_lintegral]
      exact ENNReal.ofReal_ne_top
    refine (integrable_toReal_of_lintegral_ne_top h_meas_enn h_lintegral_ne_top).congr ?_
    filter_upwards [hXm_nonneg] with ω hω
    simp [ENNReal.toReal_ofReal, pow_nonneg hω]
  have h_moment_eq :
      moment X k μ = moment Xm k μ := by
    rw [moment_def, moment_def]
    refine integral_congr_ae ?_
    filter_upwards [hX_eq_Xm] with ω hω_eq
    simp [X, Xm, hω_eq]
  have h_moment_nonneg_Xm :
      0 ≤ moment Xm k μ := by
    rw [moment_def]
    exact integral_nonneg_of_ae h_pow_nonneg_Xm
  have h_ofReal_moment_Xm :
      ENNReal.ofReal (moment Xm k μ) = ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ := by
    simpa [moment_def] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_pow_int_Xm h_pow_nonneg_Xm)
  have h_moment_Xm :
      moment Xm k μ =
        ((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0 := by
    rw [← ENNReal.ofReal_eq_ofReal_iff h_moment_nonneg_Xm h_signed_nonneg]
    rw [h_ofReal_moment_Xm, h_lintegral_eq, h_lintegral]
  -- Proof comment: the measurable representative has the same moments as `X`, so the real
  -- moment identity follows from the ENNReal right-limit identity.
  exact h_moment_eq.trans h_moment_Xm

-- Proof sketch: specialize
-- `criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero` to `k = 1`, rewrite the
-- iterate of `probabilityGeneratingFunctionReal criticalGeometricOffspringPMF` with
-- Lemma 21.44, and evaluate the resulting first derivative at `0`.
/-- Auxiliary consequence of Lemma 21.45: the first moment of `Z_n` is `i`. -/
theorem criticalGeometricBranching_first_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = i := by
  -- Proof comment: specialize the signed-derivative identity to `k = 1` and evaluate the first
  -- derivative of the explicit Laplace transform at `0`.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 1]
  have hderiv := criticalGeometricBranchingLaplaceTransform_hasDerivAt_zero n i
  simpa [iteratedDeriv_one] using congrArg Neg.neg hderiv.deriv

/-- Helper for Lemma 21.45: the positive-generation explicit Laplace model obtained from the local
fractional-linear formula. -/
private noncomputable def criticalGeometricBranchingExplicitModel (n i : ℕ) : ℝ → ℝ :=
  fun t ↦
    ((((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t))) ^ i)

/-- Helper for Lemma 21.45: the branching Laplace transform and the explicit positive-generation
model have the same iterated derivatives at the origin. -/
private lemma criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
    {n i k : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv k (criticalGeometricBranchingLaplaceTransform n i) 0 =
      iteratedDeriv k (criticalGeometricBranchingExplicitModel n i) 0 := by
  -- Proof comment: equality on a neighborhood of `0` forces equality of all iterated derivatives
  -- there, hence also at the center.
  simpa [criticalGeometricBranchingExplicitModel] using
    Filter.EventuallyEq.iteratedDeriv_eq k
      (criticalGeometricBranchingLaplaceTransform_eq_explicit_nhds_zero (n := n) (i := i) hn)

/-- Helper for Lemma 21.45: the explicit positive-generation model is analytic at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_analyticAt_zero
    {n i : ℕ} (hn : 1 ≤ n) :
    AnalyticAt ℝ (criticalGeometricBranchingExplicitModel n i) 0 := by
  -- Proof comment: transfer analyticity from the actual branching Laplace transform through the
  -- already-proved neighborhood identity at `0`.
  simpa [criticalGeometricBranchingExplicitModel] using
    (criticalGeometricBranchingLaplaceTransform_analyticAt_zero n i).congr
      (criticalGeometricBranchingLaplaceTransform_eq_explicit_nhds_zero (n := n) (i := i) hn)

/-- Helper for Lemma 21.45: near `0`, the Möbius denominator of the explicit positive-generation
model stays nonzero. -/
private lemma criticalGeometricBranchingExplicitModel_denominator_ne_zero_nhds_zero
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (n + 1 : ℝ) - n * Real.exp (-t) ≠ 0 := by
  have hcont : ContinuousAt (fun t : ℝ ↦ (n + 1 : ℝ) - n * Real.exp (-t)) 0 := by
    fun_prop
  have hzero : (n + 1 : ℝ) - n * Real.exp (-(0 : ℝ)) ≠ 0 := by
    norm_num
  exact hcont.eventually_ne hzero

/-- Helper for Lemma 21.45: the base Möbius factor of the explicit positive-generation model
satisfies a quadratic differential equation. -/
private lemma criticalGeometricBranchingExplicitBase_hasDerivAt
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (hden : (n + 1 : ℝ) - n * Real.exp (-t) ≠ 0) :
    HasDerivAt
      (fun u : ℝ ↦ ((n : ℝ) - (n - 1) * Real.exp (-u)) / (n + 1 - n * Real.exp (-u)))
      (-(n : ℝ) * (n + 1) *
          (((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t))) ^ 2 +
        (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
            (((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t))) -
          (n : ℝ) * (n - 1 : ℕ))) t := by
  -- Proof comment: differentiate the Möbius numerator and denominator separately and apply the
  -- quotient rule at the fixed denominator value `hden`.
  have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-t)) t := by
    simpa using ((hasDerivAt_id t).neg).exp
  have hnum :
      HasDerivAt
        (fun u : ℝ ↦ (n : ℝ) - ((n - 1 : ℕ) : ℝ) * Real.exp (-u))
        (((n - 1 : ℕ) : ℝ) * Real.exp (-t)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const t (n : ℝ)).sub
        ((hasDerivAt_const t (((n - 1 : ℕ) : ℝ))).mul hexp))
  have hden' :
      HasDerivAt
        (fun u : ℝ ↦ (n + 1 : ℝ) - (n : ℝ) * Real.exp (-u))
        ((n : ℝ) * Real.exp (-t)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const t ((n + 1 : ℝ))).sub
        ((hasDerivAt_const t ((n : ℝ))).mul hexp))
  have hdiv := hnum.div hden' hden
  -- Proof comment: once the quotient derivative is available, a single algebraic normalization
  -- turns it into the quadratic ODE form used later.
  convert hdiv using 1
  · ext u
    simp [Nat.cast_sub hn]
  · rw [Nat.cast_sub hn]
    field_simp [hden]
    ring

/-- Helper for Lemma 21.45: positive powers of the explicit model differentiate to the linear
combination of neighboring powers that drives the moment recursion. -/
private lemma criticalGeometricBranchingExplicitModel_hasDerivAt_succ
    {n m : ℕ} (hn : 1 ≤ n) {t : ℝ} (hden : (n + 1 : ℝ) - n * Real.exp (-t) ≠ 0) :
    HasDerivAt (criticalGeometricBranchingExplicitModel n (m + 1))
      (-(((m + 1 : ℕ) : ℝ) *
          (((n : ℝ) * (n + 1) * criticalGeometricBranchingExplicitModel n (m + 2) t) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingExplicitModel n (m + 1) t) +
            ((n : ℝ) * (n - 1 : ℕ) * criticalGeometricBranchingExplicitModel n m t)))) t := by
  -- Proof comment: differentiate the `(m + 1)`st power of the Möbius base and then factor the
  -- resulting powers into the neighboring explicit models `m`, `m + 1`, and `m + 2`.
  convert (criticalGeometricBranchingExplicitBase_hasDerivAt (n := n) hn hden).pow (m + 1)
    using 1
  set x : ℝ :=
    (((n : ℝ) - (n - 1) * Real.exp (-t)) / (n + 1 - n * Real.exp (-t)))
  -- Proof comment: after naming the common Möbius factor `x`, the target is a polynomial
  -- identity in `x`.
  change
    -(((m + 1 : ℕ) : ℝ) *
        (((n : ℝ) * (n + 1) * x ^ (m + 2)) -
          (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * x ^ (m + 1)) +
          ((n : ℝ) * (n - 1 : ℕ) * x ^ m))) =
      (((m + 1 : ℕ) : ℝ) * x ^ m) *
        (-(n : ℝ) * (n + 1) * x ^ 2 + (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * x - (n : ℝ) * (n - 1 : ℕ)))
  ring

/-- Helper for Lemma 21.45: near `0`, the derivative of the explicit positive-generation model is
the normalized linear combination of the neighboring explicit models. -/
private lemma criticalGeometricBranchingExplicitModel_deriv_eq_nhds_zero
    {n m : ℕ} (hn : 1 ≤ n) :
    deriv (criticalGeometricBranchingExplicitModel n (m + 1)) =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦
        -(((m + 1 : ℕ) : ℝ) *
          (((n : ℝ) * (n + 1) * criticalGeometricBranchingExplicitModel n (m + 2) t) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingExplicitModel n (m + 1) t) +
            ((n : ℝ) * (n - 1 : ℕ) * criticalGeometricBranchingExplicitModel n m t))) := by
  -- Proof comment: discharge the Möbius denominator side condition once on a neighborhood of `0`,
  -- then read off the derivative from the pointwise `HasDerivAt` identity.
  filter_upwards [criticalGeometricBranchingExplicitModel_denominator_ne_zero_nhds_zero (n := n) hn]
    with t hden
  exact
    (criticalGeometricBranchingExplicitModel_hasDerivAt_succ (n := n) (m := m) hn hden).deriv

/-- Helper for Lemma 21.45: every explicit positive-generation model takes the value `1` at the
origin. -/
private lemma criticalGeometricBranchingExplicitModel_eval_zero (n i : ℕ) :
    criticalGeometricBranchingExplicitModel n i 0 = 1 := by
  -- Proof comment: both Möbius numerator and denominator evaluate to `1` at `0`, so every power
  -- of the base equals `1`.
  simp [criticalGeometricBranchingExplicitModel]

/-- Helper for Lemma 21.45: exponent `0` makes the explicit positive-generation model the constant
function `1`. -/
private lemma criticalGeometricBranchingExplicitModel_zero (n : ℕ) :
    criticalGeometricBranchingExplicitModel n 0 = fun _ : ℝ ↦ (1 : ℝ) := by
  -- Proof comment: raising any real-valued base to the zeroth power turns the explicit model
  -- into the constant function `1`.
  ext t
  simp [criticalGeometricBranchingExplicitModel]

/-- Helper for Lemma 21.45: every positive iterated derivative of the exponent-zero explicit
model vanishes at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_zero_iteratedDeriv
    {n k : ℕ} (hk : 0 < k) :
    iteratedDeriv k (criticalGeometricBranchingExplicitModel n 0) 0 = 0 := by
  -- Proof comment: after rewriting the exponent-zero model to the constant function `1`, the
  -- general constant-function iterated-derivative formula gives the required vanishing.
  rw [criticalGeometricBranchingExplicitModel_zero]
  simpa [hk.ne'] using
    (iteratedDeriv_const (n := k) (c := (1 : ℝ)) (x := (0 : ℝ)))

/-- Helper for Lemma 21.45: rewrite the predecessor coefficient `↑(n - 1)` as `(n : ℝ) - 1` in
the explicit-model recursion. -/
private lemma criticalGeometricBranchingSuccCoefficient_realPred
    {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    (n : ℝ) * (n - 1 : ℕ) * x = (n : ℝ) * ((n : ℝ) - (1 : ℝ)) * x := by
  -- Proof comment: the only nontrivial step is the cast normalization `↑(n - 1) = (n : ℝ) - 1`.
  rw [Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the zeroth-generation Laplace transform has signed derivatives
`i^k` at the origin. -/
private lemma criticalGeometricBranching_zero_signedIteratedDerivAtZero (i k : ℕ) :
    (-1 : ℝ) ^ k * iteratedDeriv k (criticalGeometricBranchingLaplaceTransform 0 i) 0 =
      (i : ℝ) ^ k := by
  -- Proof comment: the zero-generation transform is a pure exponential, so its iterated
  -- derivatives are given by the closed formula `iteratedDeriv_exp_const_mul`.
  rw [criticalGeometricBranchingLaplaceTransform_zero]
  have hfun :
      (fun t : ℝ ↦ Real.exp (-(t * i))) = fun t : ℝ ↦ Real.exp ((-(i : ℝ)) * t) := by
    ext t
    ring_nf
  rw [hfun, iteratedDeriv_exp_const_mul]
  -- Proof comment: the remaining sign is exactly `(-1)^k * (-(i : ℝ))^k = (i : ℝ)^k`.
  simp [mul_comm, ← mul_pow]

/-- Helper for Lemma 21.45: the explicit positive-generation model has signed first derivative `i`
at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_one
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) * iteratedDeriv 1 (criticalGeometricBranchingExplicitModel n i) 0 = i := by
  -- Proof comment: transport the already-computed first derivative of the actual Laplace
  -- transform through the neighborhood equality with the explicit model.
  have hderiv := criticalGeometricBranchingLaplaceTransform_hasDerivAt_zero n i
  rw [iteratedDeriv_one]
  rw [← iteratedDeriv_one (f := criticalGeometricBranchingExplicitModel n i)]
  rw [← criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel (n := n) (i := i) (k := 1)
    hn]
  rw [iteratedDeriv_one]
  simpa using congrArg Neg.neg hderiv.deriv

/-- Helper for Lemma 21.45: the signed iterated derivatives of the explicit positive-generation
model satisfy the neighboring-power recursion coming from its first-derivative identity. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
    {n m k : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv (k + 1) (criticalGeometricBranchingExplicitModel n (m + 1))
      0 =
      ((m + 1 : ℝ) *
        (((n : ℝ) * (n + 1) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 2))
              0)) -
          (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 1))
              0)) +
          ((n : ℝ) * (n - 1 : ℕ) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n m) 0)))) := by
  -- Route correction: the pointwise derivative of the explicit model is now closed, so the
  -- remaining work is to package it into a neighborhood derivative identity at `0` and then push
  -- `iteratedDeriv` across that normalized linear combination once.
  have hcont0 : ContDiffAt ℝ k (criticalGeometricBranchingExplicitModel n m) 0 := by
    simpa using
      (criticalGeometricBranchingExplicitModel_analyticAt_zero (n := n) (i := m) hn).contDiffAt
  have hcont1 : ContDiffAt ℝ k (criticalGeometricBranchingExplicitModel n (m + 1)) 0 := by
    simpa using
      (criticalGeometricBranchingExplicitModel_analyticAt_zero (n := n) (i := m + 1) hn).contDiffAt
  have hcont2 : ContDiffAt ℝ k (criticalGeometricBranchingExplicitModel n (m + 2)) 0 := by
    simpa using
      (criticalGeometricBranchingExplicitModel_analyticAt_zero (n := n) (i := m + 2) hn).contDiffAt
  have hcont0' :
      ContDiffAt ℝ k
        (fun t ↦ (n : ℝ) * (n - 1 : ℕ) * criticalGeometricBranchingExplicitModel n m t) 0 := by
    simpa [smul_eq_mul, mul_assoc] using hcont0.const_smul ((n : ℝ) * (n - 1 : ℕ))
  have hcont1' :
      ContDiffAt ℝ k
        (fun t ↦
          (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
            criticalGeometricBranchingExplicitModel n (m + 1) t)) 0 := by
    simpa [smul_eq_mul, mul_assoc] using hcont1.const_smul (((2 : ℝ) * (n : ℝ) ^ 2 - 1))
  have hcont2' :
      ContDiffAt ℝ k
        (fun t ↦ (n : ℝ) * (n + 1) * criticalGeometricBranchingExplicitModel n (m + 2) t) 0 := by
    simpa [smul_eq_mul, mul_assoc] using hcont2.const_smul ((n : ℝ) * (n + 1))
  have hsplit :
      iteratedDeriv k
          (fun t ↦
            -(((m + 1 : ℕ) : ℝ) *
              (((n : ℝ) * (n + 1) * criticalGeometricBranchingExplicitModel n (m + 2) t) -
                (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
                  criticalGeometricBranchingExplicitModel n (m + 1) t) +
                ((n : ℝ) * (n - 1 : ℕ) * criticalGeometricBranchingExplicitModel n m t)))) 0 =
        -(((m + 1 : ℕ) : ℝ) *
          ((((n : ℝ) * (n + 1) *
                iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 2)) 0) -
              (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
                iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 1)) 0)) +
            ((n : ℝ) * (n - 1 : ℕ) *
              iteratedDeriv k (criticalGeometricBranchingExplicitModel n m) 0))) := by
    -- Proof comment: once the derivative is in normalized linear-combination form, `iteratedDeriv`
    -- distributes across the sum and the constant weights.
    rw [iteratedDeriv_fun_neg, iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_fun_add (hcont2'.sub hcont1') hcont0']
    rw [iteratedDeriv_fun_sub hcont2' hcont1']
    simp
  calc
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv (k + 1) (criticalGeometricBranchingExplicitModel n (m + 1))
        0 =
      (-1 : ℝ) ^ (k + 1) *
        iteratedDeriv k (deriv (criticalGeometricBranchingExplicitModel n (m + 1))) 0 := by
          rw [iteratedDeriv_succ']
    _ =
      (-1 : ℝ) ^ (k + 1) *
        iteratedDeriv k
          (fun t ↦
            -(((m + 1 : ℕ) : ℝ) *
              (((n : ℝ) * (n + 1) * criticalGeometricBranchingExplicitModel n (m + 2) t) -
                (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
                  criticalGeometricBranchingExplicitModel n (m + 1) t) +
                ((n : ℝ) * (n - 1 : ℕ) * criticalGeometricBranchingExplicitModel n m t)))) 0 := by
          rw [Filter.EventuallyEq.iteratedDeriv_eq k
            (criticalGeometricBranchingExplicitModel_deriv_eq_nhds_zero (n := n) (m := m) hn)]
    _ =
      (-1 : ℝ) ^ (k + 1) *
        (-(((m + 1 : ℕ) : ℝ) *
          ((((n : ℝ) * (n + 1) *
                iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 2)) 0) -
              (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
                iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 1)) 0)) +
            ((n : ℝ) * (n - 1 : ℕ) *
              iteratedDeriv k (criticalGeometricBranchingExplicitModel n m) 0)))) := by
          rw [hsplit]
    _ =
      ((m + 1 : ℝ) *
        (((n : ℝ) * (n + 1) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 2))
              0)) -
          (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n (m + 1))
              0)) +
          ((n : ℝ) * (n - 1 : ℕ) *
            (((-1 : ℝ) ^ k) * iteratedDeriv k (criticalGeometricBranchingExplicitModel n m)
              0)))) := by
          rw [pow_succ]
          norm_num [Nat.cast_add, Nat.cast_one]
          ring

/-- Helper for Lemma 21.45: the quadratic raw-moment polynomial in the initial population `i` and
generation `n`. -/
private abbrev criticalGeometricBranchingRawMomentPolyTwo (i n : ℝ) : ℝ :=
  2 * i * n + i ^ 2

/-- Helper for Lemma 21.45: the cubic raw-moment polynomial in the initial population `i` and
generation `n`. -/
private abbrev criticalGeometricBranchingRawMomentPolyThree (i n : ℝ) : ℝ :=
  6 * i * n ^ 2 + 6 * i ^ 2 * n + i ^ 3

/-- Helper for Lemma 21.45: the quartic raw-moment polynomial in the initial population `i` and
generation `n`. -/
private abbrev criticalGeometricBranchingRawMomentPolyFour (i n : ℝ) : ℝ :=
  24 * i * n ^ 3 + 36 * i ^ 2 * n ^ 2 + (12 * i ^ 3 + 2 * i) * n + i ^ 4

/-- Helper for Lemma 21.45: the quintic raw-moment polynomial in the initial population `i` and
generation `n`. -/
private abbrev criticalGeometricBranchingRawMomentPolyFive (i n : ℝ) : ℝ :=
  120 * i * n ^ 4 + 240 * i ^ 2 * n ^ 3 + (120 * i ^ 3 + 30 * i) * n ^ 2 +
    (20 * i ^ 4 + 10 * i ^ 2) * n + i ^ 5

/-- Helper for Lemma 21.45: the sextic raw-moment polynomial in the initial population `i` and
generation `n`. -/
private abbrev criticalGeometricBranchingRawMomentPolySix (i n : ℝ) : ℝ :=
  720 * i * n ^ 5 + 1800 * i ^ 2 * n ^ 4 + (1200 * i ^ 3 + 360 * i) * n ^ 3 +
    (300 * i ^ 4 + 240 * i ^ 2) * n ^ 2 + (30 * i ^ 5 + 30 * i ^ 3 + 2 * i) * n + i ^ 6

/-- Helper for Lemma 21.45: the successor step for the quadratic raw-moment polynomial matches
the explicit-model derivative recursion. -/
private lemma criticalGeometricBranchingSecondMomentPolySucc
    {n m : ℕ} (hn : 1 ≤ n) :
    (m + 1 : ℝ) *
        ((((n : ℝ) * (n + 1) * (m + 2 : ℝ)) -
              (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * (m + 1 : ℝ))) +
          ((n : ℝ) * (n - 1 : ℕ) * (m : ℝ))) =
      criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ) := by
  -- Proof comment: after rewriting the cast of `n - 1`, the recursion side is a pure polynomial
  -- identity in `m` and `n`.
  simp [criticalGeometricBranchingRawMomentPolyTwo, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the successor step for the cubic raw-moment polynomial matches the
explicit-model derivative recursion. -/
private lemma criticalGeometricBranchingThirdMomentPolySucc
    {n m : ℕ} (hn : 1 ≤ n) :
    (m + 1 : ℝ) *
        ((((n : ℝ) * (n + 1) *
              criticalGeometricBranchingRawMomentPolyTwo (m + 2 : ℝ) (n : ℝ)) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ))) +
          ((n : ℝ) * (n - 1 : ℕ) *
            criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ))) =
      criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ) := by
  -- Proof comment: once the lower-order formulas are substituted, only a cubic polynomial
  -- normalization remains.
  simp [criticalGeometricBranchingRawMomentPolyTwo, criticalGeometricBranchingRawMomentPolyThree,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the successor step for the fourth raw-moment polynomial matches the
explicit-model derivative recursion. -/
private lemma criticalGeometricBranchingFourthMomentPolySucc
    {n m : ℕ} (hn : 1 ≤ n) :
    (m + 1 : ℝ) *
        ((((n : ℝ) * (n + 1) *
              criticalGeometricBranchingRawMomentPolyThree (m + 2 : ℝ) (n : ℝ)) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ))) +
          ((n : ℝ) * (n - 1 : ℕ) *
            criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ))) =
      criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ) := by
  -- Proof comment: the quartic successor identity is a pure polynomial normalization once the
  -- cubic raw moments are substituted.
  simp [criticalGeometricBranchingRawMomentPolyThree, criticalGeometricBranchingRawMomentPolyFour,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the successor step for the fifth raw-moment polynomial matches the
explicit-model derivative recursion. -/
private lemma criticalGeometricBranchingFifthMomentPolySucc
    {n m : ℕ} (hn : 1 ≤ n) :
    (m + 1 : ℝ) *
        ((((n : ℝ) * (n + 1) *
              criticalGeometricBranchingRawMomentPolyFour (m + 2 : ℝ) (n : ℝ)) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ))) +
          ((n : ℝ) * (n - 1 : ℕ) *
            criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ))) =
      criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ) := by
  -- Proof comment: once the quartic raw-moment formulas are substituted, the fifth-order target
  -- is again just a ring identity.
  simp [criticalGeometricBranchingRawMomentPolyFour, criticalGeometricBranchingRawMomentPolyFive,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the successor step for the sixth raw-moment polynomial matches
the explicit-model derivative recursion. -/
private lemma criticalGeometricBranchingSixthMomentPolySucc
    {n m : ℕ} (hn : 1 ≤ n) :
    (m + 1 : ℝ) *
        ((((n : ℝ) * (n + 1) *
              criticalGeometricBranchingRawMomentPolyFive (m + 2 : ℝ) (n : ℝ)) -
            (((2 : ℝ) * (n : ℝ) ^ 2 - 1) *
              criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ))) +
          ((n : ℝ) * (n - 1 : ℕ) *
            criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ))) =
      criticalGeometricBranchingRawMomentPolySix (m + 1 : ℝ) (n : ℝ) := by
  -- Proof comment: the last raw-moment recursion closes after substituting the quintic formulas
  -- and normalizing one polynomial identity.
  simp [criticalGeometricBranchingRawMomentPolyFive, criticalGeometricBranchingRawMomentPolySix,
    Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
  ring

/-- Helper for Lemma 21.45: the signed second derivative of the explicit positive-generation model
evaluates to `2in + i²` at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_two
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ 2 * iteratedDeriv 2 (criticalGeometricBranchingExplicitModel n i) 0 =
      2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
  cases i with
  | zero =>
      -- Proof comment: exponent zero makes the explicit model constant, so every positive
      -- iterated derivative vanishes.
      rw [criticalGeometricBranchingExplicitModel_zero]
      simpa using
        criticalGeometricBranchingExplicitModel_zero_iteratedDeriv (n := n) (k := 2)
          (by norm_num : 0 < 2)
  | succ m =>
      -- Proof comment: the `k = 1` recursion reduces the second derivative to the already known
      -- first-derivative values of the neighboring powers.
      have hrec :=
        criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
          (n := n) (m := m) (k := 1) hn
      have hm2 :
          (-1 : ℝ) ^ 1 * iteratedDeriv 1 (criticalGeometricBranchingExplicitModel n (m + 2)) 0 =
            (m + 2 : ℝ) := by
        simpa using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_one
            (n := n) (i := m + 2) hn
      have hm1 :
          (-1 : ℝ) ^ 1 * iteratedDeriv 1 (criticalGeometricBranchingExplicitModel n (m + 1)) 0 =
            (m + 1 : ℝ) := by
        simpa using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_one
            (n := n) (i := m + 1) hn
      have hm0 :
          (-1 : ℝ) ^ 1 * iteratedDeriv 1 (criticalGeometricBranchingExplicitModel n m) 0 =
            (m : ℝ) := by
        simpa using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_one
            (n := n) (i := m) hn
      rw [hm2, hm1, hm0,
        Nat.cast_sub hn] at hrec
      rw [Nat.cast_one] at hrec
      -- Proof comment: the remaining goal is the standalone quadratic polynomial recursion.
      have hpoly :
          (m + 1 : ℝ) *
              ((((n : ℝ) * (n + 1) * (m + 2 : ℝ)) -
                    (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * (m + 1 : ℝ))) +
                ((n : ℝ) * ((n : ℝ) - 1) * (m : ℝ))) =
            criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ) := by
        -- Proof comment: rewrite the polynomial recursion into the same predecessor-coefficient
        -- normal form as `hrec` before composing the equalities.
        calc
          (m + 1 : ℝ) *
              ((((n : ℝ) * (n + 1) * (m + 2 : ℝ)) -
                    (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * (m + 1 : ℝ))) +
                ((n : ℝ) * ((n : ℝ) - 1) * (m : ℝ))) =
              (m + 1 : ℝ) *
                ((((n : ℝ) * (n + 1) * (m + 2 : ℝ)) -
                      (((2 : ℝ) * (n : ℝ) ^ 2 - 1) * (m + 1 : ℝ))) +
                  ((n : ℝ) * (n - 1 : ℕ) * (m : ℝ))) := by
                    congr 1
                    rw [← criticalGeometricBranchingSuccCoefficient_realPred (n := n) hn (m : ℝ)]
          _ = criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ) :=
            criticalGeometricBranchingSecondMomentPolySucc (n := n) (m := m) hn
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hrec.trans hpoly

/-- Helper for Lemma 21.45: the signed third derivative of the explicit positive-generation model
evaluates to `6in² + 6i²n + i³` at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_three
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ 3 * iteratedDeriv 3 (criticalGeometricBranchingExplicitModel n i) 0 =
      6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
  cases i with
  | zero =>
      -- Proof comment: exponent zero again gives the constant function `1`, so the third
      -- derivative vanishes.
      rw [criticalGeometricBranchingExplicitModel_zero]
      simpa using
        criticalGeometricBranchingExplicitModel_zero_iteratedDeriv (n := n) (k := 3)
          (by norm_num : 0 < 3)
  | succ m =>
      -- Proof comment: substitute the second-derivative polynomial for the neighboring powers
      -- into the `k = 2` recursion and normalize the result.
      have hrec :=
        criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
          (n := n) (m := m) (k := 2) hn
      have hm2 :
          (-1 : ℝ) ^ 2 * iteratedDeriv 2 (criticalGeometricBranchingExplicitModel n (m + 2)) 0 =
            criticalGeometricBranchingRawMomentPolyTwo (m + 2 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyTwo] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_two
            (n := n) (i := m + 2) hn
      have hm1 :
          (-1 : ℝ) ^ 2 * iteratedDeriv 2 (criticalGeometricBranchingExplicitModel n (m + 1)) 0 =
            criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyTwo] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_two
            (n := n) (i := m + 1) hn
      have hm0 :
          (-1 : ℝ) ^ 2 * iteratedDeriv 2 (criticalGeometricBranchingExplicitModel n m) 0 =
            criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyTwo] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_two
            (n := n) (i := m) hn
      rw [hm2, hm1, hm0,
        Nat.cast_sub hn] at hrec
      rw [Nat.cast_one] at hrec
      -- Proof comment: the cubic successor identity is now isolated as a pure algebra lemma.
      have hpoly :
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyTwo (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ)) =
            criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ) := by
        -- Proof comment: normalize the predecessor coefficient on the polynomial side before
        -- chaining it with the derivative recursion.
        calc
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyTwo (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ)) =
              (m + 1 : ℝ) *
                (((n : ℝ) * (n + 1) *
                      criticalGeometricBranchingRawMomentPolyTwo (m + 2 : ℝ) (n : ℝ) -
                    (2 * (n : ℝ) ^ 2 - 1) *
                      criticalGeometricBranchingRawMomentPolyTwo (m + 1 : ℝ) (n : ℝ)) +
                  (n : ℝ) * (n - 1 : ℕ) *
                    criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ)) := by
                      congr 1
                      rw [← criticalGeometricBranchingSuccCoefficient_realPred (n := n) hn
                        (criticalGeometricBranchingRawMomentPolyTwo (m : ℝ) (n : ℝ))]
          _ = criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ) :=
            criticalGeometricBranchingThirdMomentPolySucc (n := n) (m := m) hn
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hrec.trans hpoly

/-- Helper for Lemma 21.45: the signed fourth derivative of the explicit positive-generation model
evaluates to the textbook fourth raw-moment polynomial at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_four
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ 4 * iteratedDeriv 4 (criticalGeometricBranchingExplicitModel n i) 0 =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
  cases i with
  | zero =>
      -- Proof comment: the exponent-zero branch stays constant, so the fourth signed derivative
      -- is still zero.
      rw [criticalGeometricBranchingExplicitModel_zero]
      simpa using
        criticalGeometricBranchingExplicitModel_zero_iteratedDeriv (n := n) (k := 4)
          (by norm_num : 0 < 4)
  | succ m =>
      -- Proof comment: substitute the cubic signed-derivative formulas into the `k = 3`
      -- recursion and collect coefficients.
      have hrec :=
        criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
          (n := n) (m := m) (k := 3) hn
      have hm2 :
          (-1 : ℝ) ^ 3 * iteratedDeriv 3 (criticalGeometricBranchingExplicitModel n (m + 2)) 0 =
            criticalGeometricBranchingRawMomentPolyThree (m + 2 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyThree] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_three
            (n := n) (i := m + 2) hn
      have hm1 :
          (-1 : ℝ) ^ 3 * iteratedDeriv 3 (criticalGeometricBranchingExplicitModel n (m + 1)) 0 =
            criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyThree] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_three
            (n := n) (i := m + 1) hn
      have hm0 :
          (-1 : ℝ) ^ 3 * iteratedDeriv 3 (criticalGeometricBranchingExplicitModel n m) 0 =
            criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyThree] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_three
            (n := n) (i := m) hn
      rw [hm2, hm1, hm0,
        Nat.cast_sub hn] at hrec
      rw [Nat.cast_one] at hrec
      -- Proof comment: the quartic successor identity reduces to the dedicated polynomial bridge.
      have hpoly :
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyThree (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ)) =
            criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ) := by
        -- Proof comment: as in the cubic case, align the recursion coefficient with the normal
        -- form already produced by `hrec`.
        calc
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyThree (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ)) =
              (m + 1 : ℝ) *
                (((n : ℝ) * (n + 1) *
                      criticalGeometricBranchingRawMomentPolyThree (m + 2 : ℝ) (n : ℝ) -
                    (2 * (n : ℝ) ^ 2 - 1) *
                      criticalGeometricBranchingRawMomentPolyThree (m + 1 : ℝ) (n : ℝ)) +
                  (n : ℝ) * (n - 1 : ℕ) *
                    criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ)) := by
                      congr 1
                      rw [← criticalGeometricBranchingSuccCoefficient_realPred (n := n) hn
                        (criticalGeometricBranchingRawMomentPolyThree (m : ℝ) (n : ℝ))]
          _ = criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ) :=
            criticalGeometricBranchingFourthMomentPolySucc (n := n) (m := m) hn
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hrec.trans hpoly

/-- Helper for Lemma 21.45: the signed fifth derivative of the explicit positive-generation model
evaluates to the textbook fifth raw-moment polynomial at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_five
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ 5 * iteratedDeriv 5 (criticalGeometricBranchingExplicitModel n i) 0 =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
        (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
  cases i with
  | zero =>
      -- Proof comment: the constant explicit model has vanishing fifth derivative.
      rw [criticalGeometricBranchingExplicitModel_zero]
      simpa using
        criticalGeometricBranchingExplicitModel_zero_iteratedDeriv (n := n) (k := 5)
          (by norm_num : 0 < 5)
  | succ m =>
      -- Proof comment: the `k = 4` recursion closes after replacing the neighboring fourth
      -- derivatives by their explicit polynomials.
      have hrec :=
        criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
          (n := n) (m := m) (k := 4) hn
      have hm2 :
          (-1 : ℝ) ^ 4 * iteratedDeriv 4 (criticalGeometricBranchingExplicitModel n (m + 2)) 0 =
            criticalGeometricBranchingRawMomentPolyFour (m + 2 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFour] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_four
            (n := n) (i := m + 2) hn
      have hm1 :
          (-1 : ℝ) ^ 4 * iteratedDeriv 4 (criticalGeometricBranchingExplicitModel n (m + 1)) 0 =
            criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFour] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_four
            (n := n) (i := m + 1) hn
      have hm0 :
          (-1 : ℝ) ^ 4 * iteratedDeriv 4 (criticalGeometricBranchingExplicitModel n m) 0 =
            criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFour] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_four
            (n := n) (i := m) hn
      rw [hm2, hm1, hm0,
        Nat.cast_sub hn] at hrec
      rw [Nat.cast_one] at hrec
      -- Proof comment: the quintic successor identity is delegated to the pure ring lemma.
      have hpoly :
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyFour (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ)) =
            criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ) := by
        -- Proof comment: rewrite the predecessor factor once so the recursive and polynomial
        -- sides are syntactically aligned.
        calc
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyFour (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ)) =
              (m + 1 : ℝ) *
                (((n : ℝ) * (n + 1) *
                      criticalGeometricBranchingRawMomentPolyFour (m + 2 : ℝ) (n : ℝ) -
                    (2 * (n : ℝ) ^ 2 - 1) *
                      criticalGeometricBranchingRawMomentPolyFour (m + 1 : ℝ) (n : ℝ)) +
                  (n : ℝ) * (n - 1 : ℕ) *
                    criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ)) := by
                      congr 1
                      rw [← criticalGeometricBranchingSuccCoefficient_realPred (n := n) hn
                        (criticalGeometricBranchingRawMomentPolyFour (m : ℝ) (n : ℝ))]
          _ = criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ) :=
            criticalGeometricBranchingFifthMomentPolySucc (n := n) (m := m) hn
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hrec.trans hpoly

/-- Helper for Lemma 21.45: the signed sixth derivative of the explicit positive-generation model
evaluates to the textbook sixth raw-moment polynomial at the origin. -/
private lemma criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_six
    {n i : ℕ} (hn : 1 ≤ n) :
    (-1 : ℝ) ^ 6 * iteratedDeriv 6 (criticalGeometricBranchingExplicitModel n i) 0 =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
        (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
        (i : ℝ) ^ 6 := by
  cases i with
  | zero =>
      -- Proof comment: the exponent-zero explicit model is constant, so the sixth derivative
      -- also vanishes.
      rw [criticalGeometricBranchingExplicitModel_zero]
      simpa using
        criticalGeometricBranchingExplicitModel_zero_iteratedDeriv (n := n) (k := 6)
          (by norm_num : 0 < 6)
  | succ m =>
      -- Proof comment: the last step substitutes the fifth-derivative formulas into the `k = 5`
      -- recursion and closes by polynomial normalization.
      have hrec :=
        criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_succ
          (n := n) (m := m) (k := 5) hn
      have hm2 :
          (-1 : ℝ) ^ 5 * iteratedDeriv 5 (criticalGeometricBranchingExplicitModel n (m + 2)) 0 =
            criticalGeometricBranchingRawMomentPolyFive (m + 2 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFive] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_five
            (n := n) (i := m + 2) hn
      have hm1 :
          (-1 : ℝ) ^ 5 * iteratedDeriv 5 (criticalGeometricBranchingExplicitModel n (m + 1)) 0 =
            criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFive] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_five
            (n := n) (i := m + 1) hn
      have hm0 :
          (-1 : ℝ) ^ 5 * iteratedDeriv 5 (criticalGeometricBranchingExplicitModel n m) 0 =
            criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ) := by
        simpa [criticalGeometricBranchingRawMomentPolyFive] using
          criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_five
            (n := n) (i := m) hn
      rw [hm2, hm1, hm0,
        Nat.cast_sub hn] at hrec
      rw [Nat.cast_one] at hrec
      -- Proof comment: the sextic recursion now closes through the dedicated polynomial bridge.
      have hpoly :
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyFive (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ)) =
            criticalGeometricBranchingRawMomentPolySix (m + 1 : ℝ) (n : ℝ) := by
        -- Proof comment: the final polynomial bridge needs the same predecessor-cast
        -- normalization and no further analytic input.
        calc
          (m + 1 : ℝ) *
              (((n : ℝ) * (n + 1) *
                    criticalGeometricBranchingRawMomentPolyFive (m + 2 : ℝ) (n : ℝ) -
                  (2 * (n : ℝ) ^ 2 - 1) *
                    criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ)) +
                (n : ℝ) * ((n : ℝ) - 1) *
                  criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ)) =
              (m + 1 : ℝ) *
                (((n : ℝ) * (n + 1) *
                      criticalGeometricBranchingRawMomentPolyFive (m + 2 : ℝ) (n : ℝ) -
                    (2 * (n : ℝ) ^ 2 - 1) *
                      criticalGeometricBranchingRawMomentPolyFive (m + 1 : ℝ) (n : ℝ)) +
                  (n : ℝ) * (n - 1 : ℕ) *
                    criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ)) := by
                      congr 1
                      rw [← criticalGeometricBranchingSuccCoefficient_realPred (n := n) hn
                        (criticalGeometricBranchingRawMomentPolyFive (m : ℝ) (n : ℝ))]
          _ = criticalGeometricBranchingRawMomentPolySix (m + 1 : ℝ) (n : ℝ) :=
            criticalGeometricBranchingSixthMomentPolySucc (n := n) (m := m) hn
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hrec.trans hpoly

-- Proof sketch: apply the derivative identity from clause (1) with `k = 2`, rewrite the pgf
-- iterate using Lemma 21.44, and simplify the resulting quadratic polynomial.
/-- Lemma 21.45: the second moment of `Z_n` is `2in + i²`. -/
theorem criticalGeometricBranching_second_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 2 (P : Measure Ω) =
      2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
  -- Proof comment: rewrite the second moment as a signed second derivative at `0`, then split
  -- into the zeroth-generation exponential case and the positive-generation explicit model.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 2]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simpa using criticalGeometricBranching_zero_signedIteratedDerivAtZero i 2
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
      (n := n) (i := i) (k := 2) hn]
    simpa using
      criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_two
        (n := n) (i := i) hn

-- Proof sketch: apply clause (1) with `k = 3` and evaluate the third derivative of the explicit
-- rational form obtained from Lemma 21.44.
/-- The third moment of `Z_n` is `6in² + 6i²n + i³`. -/
theorem criticalGeometricBranching_third_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 3 (P : Measure Ω) =
      6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
  -- Proof comment: the third moment follows from the same derivative transport, now with the
  -- cubic explicit signed-derivative polynomial.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 3]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simpa using criticalGeometricBranching_zero_signedIteratedDerivAtZero i 3
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
      (n := n) (i := i) (k := 3) hn]
    simpa using
      criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_three
        (n := n) (i := i) hn

-- Proof sketch: evaluate clause (1) at `k = 4` after rewriting the pgf iterate by
-- Lemma 21.44, then collect coefficients.
/-- The fourth moment of `Z_n` is `24in³ + 36i²n² + (12i³ + 2i)n + i⁴`. -/
theorem criticalGeometricBranching_fourth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 4 (P : Measure Ω) =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
  -- Proof comment: transport the fourth signed derivative from the actual Laplace transform to
  -- the explicit model and read off the polynomial closed form.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 4]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simpa using criticalGeometricBranching_zero_signedIteratedDerivAtZero i 4
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
      (n := n) (i := i) (k := 4) hn]
    simpa using
      criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_four
        (n := n) (i := i) hn

-- Proof sketch: evaluate clause (1) at `k = 5` and simplify the resulting polynomial after the
-- Lemma 21.44 rewrite.
/-- The fifth moment of `Z_n` is
`120in⁴ + 240i²n³ + (120i³ + 30i)n² + (20i⁴ + 10i²)n + i⁵`. -/
theorem criticalGeometricBranching_fifth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 5 (P : Measure Ω) =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
        (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
  -- Proof comment: the fifth raw moment is the signed fifth derivative at `0`, evaluated either
  -- on the elementary zeroth-generation exponential or on the explicit positive-generation model.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 5]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simpa using criticalGeometricBranching_zero_signedIteratedDerivAtZero i 5
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
      (n := n) (i := i) (k := 5) hn]
    simpa using
      criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_five
        (n := n) (i := i) hn

-- Proof sketch: evaluate clause (1) at `k = 6`, use Lemma 21.44 to rewrite the Laplace
-- transform, and collect the coefficients of the resulting sixth-degree polynomial.
/-- The sixth moment of `Z_n` is
`720in⁵ + 1800i²n⁴ + (1200i³ + 360i)n³ + (300i⁴ + 240i²)n² +
(30i⁵ + 30i³ + 2i)n + i⁶`. -/
theorem criticalGeometricBranching_sixth_moment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    moment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
        (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
        (i : ℝ) ^ 6 := by
  -- Proof comment: this is the final raw-moment transport from the Laplace derivative identity
  -- to the explicit sixth-derivative polynomial of the Möbius model.
  rw [criticalGeometricBranching_moment_eq_signed_iteratedDeriv_at_zero P Z h_laplace 6]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simpa using criticalGeometricBranching_zero_signedIteratedDerivAtZero i 6
  · have hn : 1 ≤ n := Nat.succ_le_of_lt hn_pos
    rw [criticalGeometricBranching_iteratedDerivAtZero_eq_explicitModel
      (n := n) (i := i) (k := 6) hn]
    simpa using
      criticalGeometricBranchingExplicitModel_signedIteratedDerivAtZero_six
        (n := n) (i := i) hn

/-- Helper for Lemma 21.45: if the branching process starts from `0`, then every later
generation is almost surely `0`. -/
private lemma criticalGeometricBranching_ae_eq_zero_of_zero_start
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) (h_zero : i = 0) :
    (fun ω ↦ (Z n ω : ℝ)) =ᵐ[(P : Measure Ω)] fun _ ↦ 0 := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hExp_eq_one : ∫ ω, Real.exp (-(X ω)) ∂μ = 1 := by
    have hLaplace := h_laplace 1 zero_le_one
    rw [h_zero] at hLaplace
    simpa [X, μ, criticalGeometricBranchingLaplaceTransform] using hLaplace
  have hExp_int : Integrable (fun ω ↦ Real.exp (-(X ω))) μ := by
    apply Integrable.of_integral_ne_zero
    rw [hExp_eq_one]
    norm_num
  have h_nonneg :
      0 ≤ᵐ[μ] fun ω ↦ 1 - Real.exp (-(X ω)) := by
    filter_upwards with ω
    have hX_nonneg : 0 ≤ X ω := by positivity
    have hExp_le_one : Real.exp (-(X ω)) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (by linarith : -(X ω) ≤ 0)
    exact sub_nonneg.mpr hExp_le_one
  have h_zero_int : ∫ ω, (1 - Real.exp (-(X ω))) ∂μ = 0 := by
    rw [integral_sub (integrable_const _) hExp_int, integral_const, hExp_eq_one]
    simp [μ]
  have h_zero_ae :
      (fun ω ↦ 1 - Real.exp (-(X ω))) =ᵐ[μ] fun _ ↦ 0 :=
    (integral_eq_zero_iff_of_nonneg_ae h_nonneg
      ((integrable_const _).sub hExp_int)).1 h_zero_int
  -- Proof comment: `1 - exp (-X) = 0` forces `exp (-X) = 1`, hence `X = 0` almost everywhere.
  refine h_zero_ae.mono ?_
  intro ω hω
  have hExp_eq : Real.exp (-(X ω)) = 1 := by
    linarith
  have hArg_zero : -(X ω) = 0 := (Real.exp_eq_one_iff (x := -(X ω))).1 hExp_eq
  have hX_zero : X ω = 0 := by linarith
  simpa [X] using hX_zero

/-- Helper for Lemma 21.45: the sixth power of the generation-size variable is integrable. -/
private lemma criticalGeometricBranching_integrable_pow_six
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    Integrable (fun ω ↦ (Z n ω : ℝ) ^ 6) (P : Measure Ω) := by
  by_cases hi : i = 0
  · have hzero :
        (fun ω ↦ (Z n ω : ℝ) ^ 6) =ᵐ[(P : Measure Ω)] fun _ ↦ 0 := by
          simpa using
            (criticalGeometricBranching_ae_eq_zero_of_zero_start P Z h_laplace hi).mono
              fun ω hω ↦ by simp [hω]
    exact (integrable_zero Ω ℝ (P : Measure Ω)).congr hzero.symm
  · by_contra h_int
    have h_formula :
        moment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) =
          720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
            (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
            (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
            (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
            (i : ℝ) ^ 6 :=
      criticalGeometricBranching_sixth_moment P Z h_laplace
    have hi_pos_nat : 0 < i := Nat.pos_iff_ne_zero.mpr hi
    have hi_pos : 0 < (i : ℝ) := by exact_mod_cast hi_pos_nat
    have hi6_pos : 0 < (i : ℝ) ^ 6 := by positivity
    have h_rhs_pos :
        0 <
          720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
            (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
            (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
            (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
            (i : ℝ) ^ 6 := by
      have h1 : 0 ≤ 720 * (i : ℝ) * (n : ℝ) ^ 5 := by positivity
      have h2 : 0 ≤ 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 := by positivity
      have h3 : 0 ≤ (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 := by
        positivity
      have h4 : 0 ≤ (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
        positivity
      have h5 :
          0 ≤ (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) := by
        positivity
      nlinarith
    have h_zero :
        moment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) = 0 := by
      simpa [ProbabilityTheory.moment_def] using
        (integral_undef h_int :
          ∫ ω, ((fun ω ↦ (Z n ω : ℝ)) ^ 6) ω ∂(P : Measure Ω) = 0)
    linarith

/-- Helper for Lemma 21.45: every power of the generation-size variable up to degree `6` is
integrable. -/
private lemma criticalGeometricBranching_integrable_pow_le_six
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) {p : ℕ} (hp : p ≤ 6) :
    Integrable (fun ω ↦ (Z n ω : ℝ) ^ p) (P : Measure Ω) := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hX_ae : AEMeasurable X μ := criticalGeometricBranching_aemeasurable P Z h_laplace
  have h6 : Integrable (fun ω ↦ X ω ^ 6) μ := by
    simpa [X, μ] using criticalGeometricBranching_integrable_pow_six P Z h_laplace
  have h6norm : Integrable (fun ω ↦ ‖X ω‖ ^ 6) μ := by
    have hX_nonneg : ∀ ω, 0 ≤ X ω := fun ω ↦ by positivity
    refine h6.congr ?_
    filter_upwards [Eventually.of_forall hX_nonneg] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hpnorm :
      Integrable (fun ω ↦ ‖X ω‖ ^ p) μ :=
    integrable_norm_pow_of_le hX_ae.aestronglyMeasurable hp h6norm
  -- Proof comment: the population size is nonnegative, so absolute values disappear after the
  -- finite-measure power estimate is descended from degree `6`.
  have hX_nonneg : ∀ ω, 0 ≤ X ω := fun ω ↦ by positivity
  refine hpnorm.congr ?_
  filter_upwards [Eventually.of_forall hX_nonneg] with ω hω
  simp [X, Real.norm_eq_abs, abs_of_nonneg hω]

section PopulationMartingale

variable {P : ProbabilityMeasure Ω} {Z : ℕ → Ω → ℕ}

local notation "Zℝ" => fun n ω ↦ (Z n ω : ℝ)
local notation "Pμ" => (P : Measure Ω)
variable (hZ_sm : ∀ n, StronglyMeasurable (Zℝ n))
local notation "ℱZ" => Filtration.natural Zℝ hZ_sm

-- Proof sketch: verify integrability and strong measurability of the real-valued population
-- process, then use the critical branching conditional-expectation identity
-- `E[Z_{n+1} | 𝓕_n] = Z_n` with respect to the natural filtration and apply the canonical
-- discrete-time martingale constructor `martingale_nat`.
/-- Auxiliary consequence of Lemma 21.45: under the one-step critical branching conditional-expectation identity, the
population process `Z` is a martingale with respect to its natural filtration. -/
theorem criticalGeometricBranching_population_martingale
    (hZ_int : ∀ n, Integrable (Zℝ n) Pμ)
    (h_step : ∀ n, Pμ[Zℝ (n + 1) | ℱZ n] =ᵐ[Pμ] Zℝ n) :
    Martingale Zℝ ℱZ Pμ :=
  let h_step' : ∀ n, Pμ[Zℝ (n + 1) | ℱZ n] =ᵐ[Pμ] fun ω ↦ (1 : ℝ) * Zℝ n ω :=
    fun n ↦ by simpa using h_step n
  by
    simpa [branchingNormalizedProcess] using
      branchingNormalizedProcess_martingale (μ := Pμ) (Z := Zℝ) (m := 1) zero_lt_one hZ_sm
        hZ_int h_step'

end PopulationMartingale

-- Proof sketch: every probability measure has vanishing first central moment.
/-- The first central moment of `Z_n` is `0`. -/
theorem criticalGeometricBranching_first_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) (n : ℕ) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = 0 := by
  simpa using
    (centralMoment_one :
      centralMoment (fun ω ↦ (Z n ω : ℝ)) 1 (P : Measure Ω) = 0)

-- Proof sketch: use the first-moment identity to identify the mean with `i`, expand
-- `centralMoment`, and substitute the explicit second raw moment formula.
/-- Auxiliary consequence of Lemma 21.45: the second central moment of `Z_n` is `2in`. -/
theorem criticalGeometricBranching_second_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 2 (P : Measure Ω) =
      2 * (i : ℝ) * (n : ℝ) := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = (i : ℝ) := by
    -- Proof comment: the center in the second central moment is the first raw moment `i`.
    simpa [X, μ, moment_one] using
      (criticalGeometricBranching_first_moment P Z (i := i) (n := n) h_laplace)
  have hX : Integrable X μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 1) (by norm_num)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 2) (by norm_num)
  have h2 : moment X 2 μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [X, μ] using
      (criticalGeometricBranching_second_moment P Z (i := i) (n := n) h_laplace)
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  rw [ProbabilityTheory.centralMoment, hmean]
  change ∫ ω, (X ω - (i : ℝ)) ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ)
  rw [show (fun ω ↦ (X ω - (i : ℝ)) ^ 2) =
      fun ω ↦ X ω ^ 2 - (2 * (i : ℝ)) * X ω + (i : ℝ) ^ 2 by
    funext ω
    ring]
  -- Proof comment: expand the square, integrate termwise, and insert the first two raw moments.
  have hA : Integrable (fun ω ↦ X ω ^ 2 - (2 * (i : ℝ)) * X ω) μ := by
    exact hX2.sub (hX.const_mul _)
  rw [integral_add hA (integrable_const _)]
  rw [integral_sub hX2 (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the third central moment in terms of raw moments, use the first-moment
-- identity to rewrite the mean as `i`, and simplify.
/-- The third central moment of `Z_n` is `6in²`. -/
theorem criticalGeometricBranching_third_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 3 (P : Measure Ω) =
      6 * (i : ℝ) * (n : ℝ) ^ 2 := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = (i : ℝ) := by
    -- Proof comment: rewrite the center by the already-proved first raw moment.
    simpa [X, μ, moment_one] using
      (criticalGeometricBranching_first_moment P Z (i := i) (n := n) h_laplace)
  have hX : Integrable X μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 1) (by norm_num)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 3) (by norm_num)
  have h2 : moment X 2 μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [X, μ] using
      (criticalGeometricBranching_second_moment P Z (i := i) (n := n) h_laplace)
  have h3 :
      moment X 3 μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [X, μ] using
      (criticalGeometricBranching_third_moment P Z (i := i) (n := n) h_laplace)
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  rw [ProbabilityTheory.centralMoment, hmean]
  change ∫ ω, (X ω - (i : ℝ)) ^ 3 ∂μ = 6 * (i : ℝ) * (n : ℝ) ^ 2
  rw [show (fun ω ↦ (X ω - (i : ℝ)) ^ 3) =
      fun ω ↦
        (X ω ^ 3 - (3 * (i : ℝ)) * X ω ^ 2) +
          ((3 * (i : ℝ) ^ 2) * X ω - (i : ℝ) ^ 3) by
    funext ω
    ring]
  -- Proof comment: the cubic expansion leaves only the first three raw moments.
  have hA : Integrable (fun ω ↦ X ω ^ 3 - (3 * (i : ℝ)) * X ω ^ 2) μ := by
    exact hX3.sub (hX2.const_mul _)
  have hB : Integrable (fun ω ↦ (3 * (i : ℝ) ^ 2) * X ω - (i : ℝ) ^ 3) μ := by
    exact (hX.const_mul _).sub (integrable_const _)
  rw [integral_add hA hB]
  rw [integral_sub hX3 (hX2.const_mul _)]
  rw [integral_sub (hX.const_mul _) (integrable_const _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the fourth central moment via the binomial formula and substitute the raw
-- moment identities from clause (2).
/-- The fourth central moment of `Z_n` is `24in³ + 12i²n² + 2in`. -/
theorem criticalGeometricBranching_fourth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 4 (P : Measure Ω) =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 12 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        2 * (i : ℝ) * (n : ℝ) := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = (i : ℝ) := by
    -- Proof comment: identify the center in the quartic central moment with the first raw moment.
    simpa [X, μ, moment_one] using
      (criticalGeometricBranching_first_moment P Z (i := i) (n := n) h_laplace)
  have hX : Integrable X μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 1) (by norm_num)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 4) (by norm_num)
  have h2 : moment X 2 μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [X, μ] using
      (criticalGeometricBranching_second_moment P Z (i := i) (n := n) h_laplace)
  have h3 :
      moment X 3 μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [X, μ] using
      (criticalGeometricBranching_third_moment P Z (i := i) (n := n) h_laplace)
  have h4 :
      moment X 4 μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [X, μ] using
      (criticalGeometricBranching_fourth_moment P Z (i := i) (n := n) h_laplace)
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - (i : ℝ)) ^ 4 ∂μ =
      24 * (i : ℝ) * (n : ℝ) ^ 3 + 12 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
        2 * (i : ℝ) * (n : ℝ)
  rw [show (fun ω ↦ (X ω - (i : ℝ)) ^ 4) =
      fun ω ↦
        ((X ω ^ 4 - (4 * (i : ℝ)) * X ω ^ 3) +
            ((6 * (i : ℝ) ^ 2) * X ω ^ 2 - (4 * (i : ℝ) ^ 3) * X ω)) +
          (i : ℝ) ^ 4 by
    funext ω
    ring]
  -- Proof comment: integrate the quartic binomial expansion and substitute the raw moments.
  have hA : Integrable (fun ω ↦ X ω ^ 4 - (4 * (i : ℝ)) * X ω ^ 3) μ := by
    exact hX4.sub (hX3.const_mul _)
  have hB : Integrable (fun ω ↦ (6 * (i : ℝ) ^ 2) * X ω ^ 2 - (4 * (i : ℝ) ^ 3) * X ω) μ := by
    exact (hX2.const_mul _).sub (hX.const_mul _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 4 - (4 * (i : ℝ)) * X ω ^ 3) +
            ((6 * (i : ℝ) ^ 2) * X ω ^ 2 - (4 * (i : ℝ) ^ 3) * X ω)) μ := by
    exact hA.add hB
  rw [integral_add hAB (integrable_const _)]
  rw [integral_add hA hB]
  rw [integral_sub hX4 (hX3.const_mul _)]
  rw [integral_sub (hX2.const_mul _) (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: express the fifth central moment in terms of raw moments and simplify using the
-- formulas from clause (2).
/-- The fifth central moment of `Z_n` is `120in⁴ + 120i²n³ + 30in²`. -/
theorem criticalGeometricBranching_fifth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 5 (P : Measure Ω) =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 120 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        30 * (i : ℝ) * (n : ℝ) ^ 2 := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = (i : ℝ) := by
    -- Proof comment: replace the centering constant by the first raw moment `i`.
    simpa [X, μ, moment_one] using
      (criticalGeometricBranching_first_moment P Z (i := i) (n := n) h_laplace)
  have hX : Integrable X μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 1) (by norm_num)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 4) (by norm_num)
  have hX5 : Integrable (fun ω ↦ X ω ^ 5) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 5) (by norm_num)
  have h2 : moment X 2 μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [X, μ] using
      (criticalGeometricBranching_second_moment P Z (i := i) (n := n) h_laplace)
  have h3 :
      moment X 3 μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [X, μ] using
      (criticalGeometricBranching_third_moment P Z (i := i) (n := n) h_laplace)
  have h4 :
      moment X 4 μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [X, μ] using
      (criticalGeometricBranching_fourth_moment P Z (i := i) (n := n) h_laplace)
  have h5 :
      moment X 5 μ =
        120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
          (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
          (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
    simpa [X, μ] using
      (criticalGeometricBranching_fifth_moment P Z (i := i) (n := n) h_laplace)
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  have hInt5 :
      ∫ ω, X ω ^ 5 ∂μ =
        120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
          (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
          (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
    simpa [moment_def] using h5
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - (i : ℝ)) ^ 5 ∂μ =
      120 * (i : ℝ) * (n : ℝ) ^ 4 + 120 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
        30 * (i : ℝ) * (n : ℝ) ^ 2
  rw [show (fun ω ↦ (X ω - (i : ℝ)) ^ 5) =
      fun ω ↦
        ((X ω ^ 5 - (5 * (i : ℝ)) * X ω ^ 4) +
            ((10 * (i : ℝ) ^ 2) * X ω ^ 3 - (10 * (i : ℝ) ^ 3) * X ω ^ 2)) +
          ((5 * (i : ℝ) ^ 4) * X ω - (i : ℝ) ^ 5) by
    funext ω
    ring]
  -- Proof comment: the quintic expansion integrates termwise against the first five raw moments.
  have hA : Integrable (fun ω ↦ X ω ^ 5 - (5 * (i : ℝ)) * X ω ^ 4) μ := by
    exact hX5.sub (hX4.const_mul _)
  have hB :
      Integrable (fun ω ↦ (10 * (i : ℝ) ^ 2) * X ω ^ 3 - (10 * (i : ℝ) ^ 3) * X ω ^ 2) μ := by
    exact (hX3.const_mul _).sub (hX2.const_mul _)
  have hC : Integrable (fun ω ↦ (5 * (i : ℝ) ^ 4) * X ω - (i : ℝ) ^ 5) μ := by
    exact (hX.const_mul _).sub (integrable_const _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 5 - (5 * (i : ℝ)) * X ω ^ 4) +
            ((10 * (i : ℝ) ^ 2) * X ω ^ 3 - (10 * (i : ℝ) ^ 3) * X ω ^ 2)) μ := by
    exact hA.add hB
  rw [integral_add hAB hC]
  rw [integral_add hA hB]
  rw [integral_sub hX5 (hX4.const_mul _)]
  rw [integral_sub (hX3.const_mul _) (hX2.const_mul _)]
  rw [integral_sub (hX.const_mul _) (integrable_const _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt5, hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the sixth central moment in terms of raw moments and collect the
-- remaining polynomial terms after substitution.
/-- The sixth central moment of `Z_n` is
`720in⁵ + 1080i²n⁴ + (120i³ + 360i)n³ + 60i²n² + 2in`. -/
theorem criticalGeometricBranching_sixth_centralMoment
    (P : ProbabilityMeasure Ω) (Z : ℕ → Ω → ℕ) {i n : ℕ}
    (h_laplace : HasCriticalGeometricBranchingLaplaceTransform P Z i n) :
    centralMoment (fun ω ↦ (Z n ω : ℝ)) 6 (P : Measure Ω) =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1080 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (120 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        60 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 + 2 * (i : ℝ) * (n : ℝ) := by
  let μ : Measure Ω := (P : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Z n ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = (i : ℝ) := by
    -- Proof comment: rewrite the centering constant in `centralMoment` as the first raw moment.
    simpa [X, μ, moment_one] using
      (criticalGeometricBranching_first_moment P Z (i := i) (n := n) h_laplace)
  have hX : Integrable X μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 1) (by norm_num)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 4) (by norm_num)
  have hX5 : Integrable (fun ω ↦ X ω ^ 5) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 5) (by norm_num)
  have hX6 : Integrable (fun ω ↦ X ω ^ 6) μ := by
    simpa [X, μ] using
      criticalGeometricBranching_integrable_pow_le_six P Z h_laplace (p := 6) (by norm_num)
  have h2 : moment X 2 μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [X, μ] using
      (criticalGeometricBranching_second_moment P Z (i := i) (n := n) h_laplace)
  have h3 :
      moment X 3 μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [X, μ] using
      (criticalGeometricBranching_third_moment P Z (i := i) (n := n) h_laplace)
  have h4 :
      moment X 4 μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [X, μ] using
      (criticalGeometricBranching_fourth_moment P Z (i := i) (n := n) h_laplace)
  have h5 :
      moment X 5 μ =
        120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
          (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
          (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
    simpa [X, μ] using
      (criticalGeometricBranching_fifth_moment P Z (i := i) (n := n) h_laplace)
  have h6 :
      moment X 6 μ =
        720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
          (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
          (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
          (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
          (i : ℝ) ^ 6 := by
    simpa [X, μ] using
      (criticalGeometricBranching_sixth_moment P Z (i := i) (n := n) h_laplace)
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (i : ℝ) * (n : ℝ) + (i : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (i : ℝ) * (n : ℝ) ^ 2 + 6 * (i : ℝ) ^ 2 * (n : ℝ) + (i : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (i : ℝ) * (n : ℝ) ^ 3 + 36 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 +
          (12 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) + (i : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  have hInt5 :
      ∫ ω, X ω ^ 5 ∂μ =
        120 * (i : ℝ) * (n : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2 * (n : ℝ) ^ 3 +
          (120 * (i : ℝ) ^ 3 + 30 * (i : ℝ)) * (n : ℝ) ^ 2 +
          (20 * (i : ℝ) ^ 4 + 10 * (i : ℝ) ^ 2) * (n : ℝ) + (i : ℝ) ^ 5 := by
    simpa [moment_def] using h5
  have hInt6 :
      ∫ ω, X ω ^ 6 ∂μ =
        720 * (i : ℝ) * (n : ℝ) ^ 5 + 1800 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
          (1200 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
          (300 * (i : ℝ) ^ 4 + 240 * (i : ℝ) ^ 2) * (n : ℝ) ^ 2 +
          (30 * (i : ℝ) ^ 5 + 30 * (i : ℝ) ^ 3 + 2 * (i : ℝ)) * (n : ℝ) +
          (i : ℝ) ^ 6 := by
    simpa [moment_def] using h6
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - (i : ℝ)) ^ 6 ∂μ =
      720 * (i : ℝ) * (n : ℝ) ^ 5 + 1080 * (i : ℝ) ^ 2 * (n : ℝ) ^ 4 +
        (120 * (i : ℝ) ^ 3 + 360 * (i : ℝ)) * (n : ℝ) ^ 3 +
        60 * (i : ℝ) ^ 2 * (n : ℝ) ^ 2 + 2 * (i : ℝ) * (n : ℝ)
  rw [show (fun ω ↦ (X ω - (i : ℝ)) ^ 6) =
      fun ω ↦
        ((X ω ^ 6 - (6 * (i : ℝ)) * X ω ^ 5) +
            ((15 * (i : ℝ) ^ 2) * X ω ^ 4 - (20 * (i : ℝ) ^ 3) * X ω ^ 3)) +
          (((15 * (i : ℝ) ^ 4) * X ω ^ 2 - (6 * (i : ℝ) ^ 5) * X ω) + (i : ℝ) ^ 6) by
    funext ω
    ring]
  -- Proof comment: the sextic expansion reduces the centered moment to a fixed linear
  -- combination of the first six raw moments.
  have hA : Integrable (fun ω ↦ X ω ^ 6 - (6 * (i : ℝ)) * X ω ^ 5) μ := by
    exact hX6.sub (hX5.const_mul _)
  have hB :
      Integrable (fun ω ↦ (15 * (i : ℝ) ^ 2) * X ω ^ 4 - (20 * (i : ℝ) ^ 3) * X ω ^ 3) μ := by
    exact (hX4.const_mul _).sub (hX3.const_mul _)
  have hC : Integrable (fun ω ↦ (15 * (i : ℝ) ^ 4) * X ω ^ 2 - (6 * (i : ℝ) ^ 5) * X ω) μ := by
    exact (hX2.const_mul _).sub (hX.const_mul _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 6 - (6 * (i : ℝ)) * X ω ^ 5) +
            ((15 * (i : ℝ) ^ 2) * X ω ^ 4 - (20 * (i : ℝ) ^ 3) * X ω ^ 3)) μ := by
    exact hA.add hB
  have hCD :
      Integrable
        (fun ω ↦
          ((15 * (i : ℝ) ^ 4) * X ω ^ 2 - (6 * (i : ℝ) ^ 5) * X ω) + (i : ℝ) ^ 6) μ := by
    exact hC.add (integrable_const _)
  rw [integral_add hAB hCD]
  rw [integral_add hA hB]
  rw [integral_add hC (integrable_const _)]
  rw [integral_sub hX6 (hX5.const_mul _)]
  rw [integral_sub (hX4.const_mul _) (hX3.const_mul _)]
  rw [integral_sub (hX2.const_mul _) (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt6, hInt5, hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

end ProbabilityTheory

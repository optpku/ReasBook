/-
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap05.section02_part1

section Chap05
section Section02

/-- Lemma 5.2.5c (Properties of the inner product (c), linearity in the first
variable): for `f, g, h ∈ C(ℝ/ℤ; ℂ)` and `c ∈ ℂ`,
`⟪f + g, h⟫ = ⟪f, h⟫ + ⟪g, h⟫` and `⟪cf, g⟫ = c ⟪f, g⟫`. -/
lemma periodicInnerProduct_linearity_first
    (f g h : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (c : ℂ) :
    periodicInnerProduct (addPeriodicFunction f g) h =
      periodicInnerProduct f h + periodicInnerProduct g h ∧
      periodicInnerProduct (smulPeriodicFunction c f) g = c * periodicInnerProduct f g := by
  constructor
  · have hIntF :
        MeasureTheory.IntegrableOn (fun x : ℝ => f.1 x * star (h.1 x)) (Set.Icc (0 : ℝ) 1) :=
      helperForLemma_5_2_5c_integrableOn_mul_star f h
    have hIntG :
        MeasureTheory.IntegrableOn (fun x : ℝ => g.1 x * star (h.1 x)) (Set.Icc (0 : ℝ) 1) :=
      helperForLemma_5_2_5c_integrableOn_mul_star g h
    calc
      periodicInnerProduct (addPeriodicFunction f g) h
          = ∫ x in Set.Icc (0 : ℝ) 1, (f.1 + g.1) x * star (h.1 x) := rfl
      _ = ∫ x in Set.Icc (0 : ℝ) 1, (f.1 x * star (h.1 x) + g.1 x * star (h.1 x)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            exact helperForLemma_5_2_5c_addIntegrand_expand f g h x
      _ = (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (h.1 x)) +
            (∫ x in Set.Icc (0 : ℝ) 1, g.1 x * star (h.1 x)) := by
            simpa using
              (MeasureTheory.integral_add
                (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) hIntF hIntG)
      _ = periodicInnerProduct f h + periodicInnerProduct g h := rfl
  · calc
      periodicInnerProduct (smulPeriodicFunction c f) g
          = ∫ x in Set.Icc (0 : ℝ) 1, (c • f.1) x * star (g.1 x) := rfl
      _ = ∫ x in Set.Icc (0 : ℝ) 1, c * (f.1 x * star (g.1 x)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            exact helperForLemma_5_2_5c_smulIntegrand_factor c f g x
      _ = c * (∫ x in Set.Icc (0 : ℝ) 1, f.1 x * star (g.1 x)) := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) c
                (fun x : ℝ => f.1 x * star (g.1 x)))
      _ = c * periodicInnerProduct f g := by rfl

/-- Helper for Lemma 5.2.5d: taking the star of `periodicInnerProduct u v`
swaps the arguments. -/
lemma helperForLemma_5_2_5d_star_swap
    (u v : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    star (periodicInnerProduct u v) = periodicInnerProduct v u := by
  simpa using congrArg star (periodicInnerProduct_hermitian v u)

/-- Lemma 5.2.5d (Properties of the inner product (d), antilinearity in the
second variable): for `f, g, h ∈ C(ℝ/ℤ; ℂ)` and `c ∈ ℂ`,
`⟪f, g + h⟫ = ⟪f, g⟫ + ⟪f, h⟫` and `⟪f, cg⟫ = \overline{c} ⟪f, g⟫`. -/
lemma periodicInnerProduct_antilinearity_second
    (f g h : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) (c : ℂ) :
    periodicInnerProduct f (addPeriodicFunction g h) =
      periodicInnerProduct f g + periodicInnerProduct f h ∧
      periodicInnerProduct f (smulPeriodicFunction c g) = star c * periodicInnerProduct f g := by
  constructor
  · calc
      periodicInnerProduct f (addPeriodicFunction g h)
          = star (periodicInnerProduct (addPeriodicFunction g h) f) := by
              simpa using (periodicInnerProduct_hermitian (addPeriodicFunction g h) f)
      _ = star (periodicInnerProduct g f + periodicInnerProduct h f) := by
            rw [(periodicInnerProduct_linearity_first g h f c).1]
      _ = star (periodicInnerProduct g f) + star (periodicInnerProduct h f) := by
            simp
      _ = periodicInnerProduct f g + periodicInnerProduct f h := by
            rw [helperForLemma_5_2_5d_star_swap g f, helperForLemma_5_2_5d_star_swap h f]
  · calc
      periodicInnerProduct f (smulPeriodicFunction c g)
          = star (periodicInnerProduct (smulPeriodicFunction c g) f) := by
              simpa using (periodicInnerProduct_hermitian (smulPeriodicFunction c g) f)
      _ = star (c * periodicInnerProduct g f) := by
            rw [(periodicInnerProduct_linearity_first g f h c).2]
      _ = star c * star (periodicInnerProduct g f) := by
            simp
      _ = star c * periodicInnerProduct f g := by
            rw [helperForLemma_5_2_5d_star_swap g f]

/-- The `L^∞` norm on continuous, `1`-periodic complex-valued functions,
taken as the supremum of `‖f(x)‖` on `[0,1]`. -/
noncomputable def periodicLInftyNorm
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) : ℝ :=
  sSup (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖))

/-- Helper for Exercise 5.2.3: `0` belongs to the fundamental interval `[0,1]`. -/
lemma helperForExercise_5_2_3_zero_mem_Icc :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num

/-- Helper for Exercise 5.2.3: the `L^∞`-range set is bounded above. -/
lemma helperForExercise_5_2_3_lInftyRange_bddAbove
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) := by
  have hCompactImage :
      IsCompact ((fun x : ℝ => ‖f.1 x‖) '' Set.Icc (0 : ℝ) 1) := by
    refine (isCompact_Icc.image_of_continuousOn ?_)
    exact (f.2.1.norm).continuousOn
  have hRangeEq :
      Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖) =
        (fun x : ℝ => ‖f.1 x‖) '' Set.Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hRangeEq]
  exact hCompactImage.bddAbove

/-- Helper for Exercise 5.2.3: the `L^∞`-range set is nonempty. -/
lemma helperForExercise_5_2_3_lInftyRange_nonempty
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    Set.Nonempty (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) := by
  refine ⟨‖f.1 0‖, ?_⟩
  exact ⟨⟨0, helperForExercise_5_2_3_zero_mem_Icc⟩, rfl⟩

/-- Helper for Exercise 5.2.3: the periodic `L^∞` norm is nonnegative. -/
lemma helperForExercise_5_2_3_lInfty_nonneg
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    0 ≤ periodicLInftyNorm f := by
  unfold periodicLInftyNorm
  have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
    helperForExercise_5_2_3_lInftyRange_bddAbove f
  have hNonempty : Set.Nonempty (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
    helperForExercise_5_2_3_lInftyRange_nonempty f
  rcases hNonempty with ⟨m, hm⟩
  have hmNonneg : 0 ≤ m := by
    rcases hm with ⟨x, rfl⟩
    exact norm_nonneg (f.1 x)
  have hmLeSup : m ≤ sSup (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
    le_csSup hBdd hm
  exact le_trans hmNonneg hmLeSup

/-- Helper for Exercise 5.2.3: pointwise `normSq` is bounded by `‖f‖^2_{L^∞}` on `[0,1]`. -/
lemma helperForExercise_5_2_3_normSq_le_lInftySq
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Complex.normSq (f.1 x) ≤ periodicLInftyNorm f ^ (2 : ℕ) := by
  have hBdd : BddAbove (Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖f.1 y‖)) :=
    helperForExercise_5_2_3_lInftyRange_bddAbove f
  have hxInRange : ‖f.1 x‖ ∈ Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖f.1 y‖) := by
    exact ⟨⟨x, hx⟩, rfl⟩
  have hNormLeSup : ‖f.1 x‖ ≤ periodicLInftyNorm f := by
    unfold periodicLInftyNorm
    exact le_csSup hBdd hxInRange
  have hNormNonneg : 0 ≤ ‖f.1 x‖ := norm_nonneg (f.1 x)
  have hSupNonneg : 0 ≤ periodicLInftyNorm f := helperForExercise_5_2_3_lInfty_nonneg f
  have hMulLe :
      ‖f.1 x‖ * ‖f.1 x‖ ≤ periodicLInftyNorm f * periodicLInftyNorm f := by
    exact mul_le_mul hNormLeSup hNormLeSup hNormNonneg hSupNonneg
  have hNormSqEq : Complex.normSq (f.1 x) = ‖f.1 x‖ * ‖f.1 x‖ := by
    calc
      Complex.normSq (f.1 x) = ‖f.1 x‖ ^ (2 : ℕ) := by
        simpa using (Complex.sq_norm (f.1 x)).symm
      _ = ‖f.1 x‖ * ‖f.1 x‖ := by ring
  calc
    Complex.normSq (f.1 x) = ‖f.1 x‖ * ‖f.1 x‖ := hNormSqEq
    _ ≤ periodicLInftyNorm f * periodicLInftyNorm f := hMulLe
    _ = periodicLInftyNorm f ^ (2 : ℕ) := by ring

/-- Helper for Exercise 5.2.3: a nonzero periodic continuous function has strictly
positive `L^2` norm. -/
lemma helperForExercise_5_2_3_nonzero_implies_l2_pos
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1})
    (hne : f.1 ≠ 0) :
    0 < periodicL2Norm f := by
  have hL2NeZero : periodicL2Norm f ≠ 0 := by
    intro hZero
    exact hne ((periodicL2Norm_eq_zero_iff f).1 hZero)
  have hL2Nonneg : 0 ≤ periodicL2Norm f := by
    unfold periodicL2Norm
    exact Real.sqrt_nonneg _
  exact lt_of_le_of_ne hL2Nonneg (Ne.symm hL2NeZero)

/-- Helper for Exercise 5.2.3: always `‖f‖_2 ≤ ‖f‖_{L^∞}`. -/
lemma helperForExercise_5_2_3_l2_le_lInfty
    (f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}) :
    periodicL2Norm f ≤ periodicLInftyNorm f := by
  have hIntNormSq :
      IntervalIntegrable (fun x : ℝ => Complex.normSq (f.1 x)) MeasureTheory.volume 0 1 := by
    exact (Complex.continuous_normSq.comp f.2.1).intervalIntegrable 0 1
  have hIntConst :
      IntervalIntegrable (fun _ : ℝ => periodicLInftyNorm f ^ (2 : ℕ))
        MeasureTheory.volume 0 1 := by
    simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => periodicLInftyNorm f ^ (2 : ℕ))
        MeasureTheory.volume 0 1)
  have hIntegralLe :
      ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x) ≤
        ∫ x in (0 : ℝ)..1, periodicLInftyNorm f ^ (2 : ℕ) := by
    refine intervalIntegral.integral_mono_on
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (by norm_num) hIntNormSq hIntConst ?_
    intro x hx
    exact helperForExercise_5_2_3_normSq_le_lInftySq f x hx
  have hIntegralConst :
      ∫ x in (0 : ℝ)..1, periodicLInftyNorm f ^ (2 : ℕ) = periodicLInftyNorm f ^ (2 : ℕ) := by
    simpa using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := 1)
      (c := periodicLInftyNorm f ^ (2 : ℕ)))
  have hReLe :
      (periodicInnerProduct f f).re ≤ periodicLInftyNorm f ^ (2 : ℕ) := by
    rw [helperForLemma_5_2_5b_re_eq_intervalIntegral_normSq f]
    calc
      ∫ x in (0 : ℝ)..1, Complex.normSq (f.1 x)
          ≤ ∫ x in (0 : ℝ)..1, periodicLInftyNorm f ^ (2 : ℕ) := hIntegralLe
      _ = periodicLInftyNorm f ^ (2 : ℕ) := hIntegralConst
  have hSqrtLe :
      Real.sqrt (periodicInnerProduct f f).re ≤ periodicLInftyNorm f := by
    exact (Real.sqrt_le_iff).2
      ⟨helperForExercise_5_2_3_lInfty_nonneg f, hReLe⟩
  simpa [periodicL2Norm] using hSqrtLe

/-- Helper for Exercise 5.2.3: for real scalars, `‖A‖` as a complex norm is `|A|`. -/
lemma helperForExercise_5_2_3_complexNorm_ofReal
    (A : ℝ) :
    ‖(A : ℂ)‖ = |A| := by
  simpa [Real.norm_eq_abs] using (Complex.norm_real A)

/-- Helper for Exercise 5.2.3: scaling `exp(2πix)` by `c` gives `L^∞` norm `‖c‖`. -/
lemma helperForExercise_5_2_3_lInfty_smul_exp
    (c : ℂ) :
    periodicLInftyNorm (smulPeriodicFunction c expTwoPiIPeriodicFunction) = ‖c‖ := by
  unfold periodicLInftyNorm
  have hRangeEq :
      Set.range (fun x : Set.Icc (0 : ℝ) 1 =>
        ‖(smulPeriodicFunction c expTwoPiIPeriodicFunction).1 x‖) = {‖c‖} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hExpNorm : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℝ))‖ = 1 := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (x : ℝ)))
      have hPointwise :
          ‖(smulPeriodicFunction c expTwoPiIPeriodicFunction).1 x‖ = ‖c‖ := by
        calc
          ‖(smulPeriodicFunction c expTwoPiIPeriodicFunction).1 x‖
              = ‖c * expTwoPiIPeriodicFunction.1 x‖ := by
                  simp [smulPeriodicFunction]
          _ = ‖c‖ * ‖expTwoPiIPeriodicFunction.1 x‖ := by
                simpa using norm_mul c (expTwoPiIPeriodicFunction.1 x)
          _ = ‖c‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℝ))‖ := by
                simp [expTwoPiIPeriodicFunction]
          _ = ‖c‖ * 1 := by rw [hExpNorm]
          _ = ‖c‖ := by ring
      simp [hPointwise]
    · intro hy
      have hy' : y = ‖c‖ := by simpa using hy
      rw [hy']
      refine ⟨⟨0, helperForExercise_5_2_3_zero_mem_Icc⟩, ?_⟩
      have hPoint0 : ‖(smulPeriodicFunction c expTwoPiIPeriodicFunction).1 (0 : ℝ)‖ = ‖c‖ := by
        have hExpNorm0 : ‖Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ))‖ = 1 := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (0 : ℝ)))
        calc
          ‖(smulPeriodicFunction c expTwoPiIPeriodicFunction).1 (0 : ℝ)‖
              = ‖c * expTwoPiIPeriodicFunction.1 (0 : ℝ)‖ := by
                  simp [smulPeriodicFunction]
          _ = ‖c‖ * ‖expTwoPiIPeriodicFunction.1 (0 : ℝ)‖ := by
                simpa using norm_mul c (expTwoPiIPeriodicFunction.1 (0 : ℝ))
          _ = ‖c‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (0 : ℝ))‖ := by
                simp [expTwoPiIPeriodicFunction]
          _ = ‖c‖ * 1 := by rw [hExpNorm0]
          _ = ‖c‖ := by ring
      simpa using hPoint0
  rw [hRangeEq, csSup_singleton]

/-- Helper for Exercise 5.2.3: diagonal converse case `A = B`. -/
lemma helperForExercise_5_2_3_exists_exact_norms_on_diagonal
    (A : ℝ) (hA : 0 < A) :
    ∃ f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
      f.1 ≠ 0 ∧ periodicL2Norm f = A ∧ periodicLInftyNorm f = A := by
  let f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
    smulPeriodicFunction (A : ℂ) expTwoPiIPeriodicFunction
  have hL2EqA : periodicL2Norm f = A := by
    change periodicL2Norm (smulPeriodicFunction (A : ℂ) expTwoPiIPeriodicFunction) = A
    rw [periodicL2Norm_smul, expTwoPiIPeriodicFunction_l2Norm_eq_one]
    rw [helperForExercise_5_2_3_complexNorm_ofReal]
    simp [abs_of_pos hA]
  have hInftyEqA : periodicLInftyNorm f = A := by
    change periodicLInftyNorm (smulPeriodicFunction (A : ℂ) expTwoPiIPeriodicFunction) = A
    rw [helperForExercise_5_2_3_lInfty_smul_exp]
    rw [helperForExercise_5_2_3_complexNorm_ofReal]
    simp [abs_of_pos hA]
  have hNonzero : f.1 ≠ 0 := by
    intro hZero
    have hL2Zero : periodicL2Norm f = 0 := (periodicL2Norm_eq_zero_iff f).2 hZero
    have hAZero : A = 0 := by
      rw [← hL2EqA]
      exact hL2Zero
    exact (ne_of_gt hA) hAZero
  refine ⟨f, hNonzero, hL2EqA, hInftyEqA⟩

/-- Helper for Exercise 5.2.3: choose `N,t` with
`t^2 + (1 - t)^2 / N = r` for any `0 < r < 1`. -/
lemma helperForExercise_5_2_3_choose_parameters_for_ratio
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N = r := by
  rcases exists_nat_one_div_lt hr0 with ⟨N0, hN0⟩
  let N : ℕ := N0 + 1
  have hNge1 : 1 ≤ N := by
    dsimp [N]
    omega
  have hNpos_nat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hNge1
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast hNpos_nat
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hInvNlt : (1 : ℝ) / N < r := by
    simpa [N, one_div, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hN0
  have hNrGtOne : (1 : ℝ) < (N : ℝ) * r := by
    have hmul : (N : ℝ) * ((1 : ℝ) / N) < (N : ℝ) * r :=
      mul_lt_mul_of_pos_left hInvNlt hNpos
    simpa [div_eq_mul_inv, hNne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hRadicandPos : 0 < (N : ℝ) * (((N : ℝ) + 1) * r - 1) := by
    have hInnerPos : 0 < ((N : ℝ) + 1) * r - 1 := by
      calc
        0 < (N : ℝ) * r - 1 := sub_pos.mpr hNrGtOne
        _ < ((N : ℝ) + 1) * r - 1 := by
          nlinarith [hr0]
    exact mul_pos hNpos hInnerPos
  have hRadicandNonneg : 0 ≤ (N : ℝ) * (((N : ℝ) + 1) * r - 1) := le_of_lt hRadicandPos
  let s : ℝ := Real.sqrt ((N : ℝ) * (((N : ℝ) + 1) * r - 1))
  let t : ℝ := (1 + s) / ((N : ℝ) + 1)
  have hN1pos : (0 : ℝ) < (N : ℝ) + 1 := by
    linarith
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (by linarith [Real.sqrt_nonneg ((N : ℝ) * (((N : ℝ) + 1) * r - 1))])
      (le_of_lt hN1pos)
  have hInnerLt : (((N : ℝ) + 1) * r - 1) < (N : ℝ) := by
    nlinarith [hr1]
  have hRadicandLt : (N : ℝ) * (((N : ℝ) + 1) * r - 1) < (N : ℝ) * (N : ℝ) := by
    exact mul_lt_mul_of_pos_left hInnerLt hNpos
  have hs_sq : s ^ (2 : ℕ) = (N : ℝ) * (((N : ℝ) + 1) * r - 1) := by
    dsimp [s]
    simpa using (Real.sq_sqrt hRadicandNonneg)
  have hs_le_N : s ≤ (N : ℝ) := by
    have hN_nonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
    have hs_sq_le : s ^ (2 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) := by
      nlinarith [hs_sq, hRadicandLt]
    have hs_abs_le : |s| ≤ (N : ℝ) := abs_le_of_sq_le_sq hs_sq_le hN_nonneg
    exact le_trans (le_abs_self s) hs_abs_le
  have ht_le_one : t ≤ 1 := by
    dsimp [t]
    have hnum_le : 1 + s ≤ (N : ℝ) + 1 := by
      linarith
    exact (div_le_iff₀ hN1pos).2 (by simpa using hnum_le)
  have hEq : t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N = r := by
    have hN1ne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hN1pos
    have hEqNum :
        (N : ℝ) * (t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N) = (N : ℝ) * r := by
      rw [show t = (1 + s) / ((N : ℝ) + 1) by rfl]
      field_simp [hNne, hN1ne]
      nlinarith [hs_sq]
    exact mul_left_cancel₀ hNne hEqNum
  exact ⟨N, hNge1, t, ht_nonneg, ht_le_one, hEq⟩

/-- Helper for Exercise 5.2.3: the Fourier mode `x ↦ exp(2πinx)` is continuous and
`1`-periodic for every integer frequency `n`. -/
lemma continuous_periodic_expMode
    (n : ℤ) :
    Continuous (fun x : ℝ => Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) ∧
      Function.Periodic (fun x : ℝ => Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) 1 := by
  constructor
  · have hPhase :
      Continuous (fun x : ℝ => ((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) :=
      continuous_const.mul Complex.continuous_ofReal
    simpa using Complex.continuous_exp.comp hPhase
  · intro x
    have hArg :
        ((n : ℂ) * (2 * Real.pi * Complex.I)) * (((x + 1 : ℝ) : ℂ))
          = (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) + ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
      simp [mul_add, add_mul, mul_comm, mul_left_comm]
    calc
      Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (((x + 1 : ℝ) : ℂ)))
          = Complex.exp ((((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) +
              ((n : ℂ) * (2 * Real.pi * Complex.I))) := by rw [hArg]
      _ = Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) *
            Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) := by
              simpa using Complex.exp_add (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))
                ((n : ℂ) * (2 * Real.pi * Complex.I))
      _ = Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) := by
            have hExp : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using (Complex.exp_int_mul_two_pi_mul_I n)
            simp [hExp]

/-- Helper for Exercise 5.2.3: integer Fourier modes as periodic continuous functions. -/
noncomputable def expModePeriodicFunction
    (n : ℤ) :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  ⟨fun x : ℝ => Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)),
    continuous_periodic_expMode n⟩

/-- Helper for Exercise 5.2.3: every Fourier mode has unit pointwise magnitude. -/
lemma helperForExercise_5_2_3_expMode_norm_eq_one
    (n : ℤ) (x : ℝ) :
    ‖(expModePeriodicFunction n).1 x‖ = 1 := by
  change ‖Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))‖ = 1
  have hRewrite :
      (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))
        = (((2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
    simp [mul_comm, mul_left_comm]
  rw [hRewrite]
  simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (n : ℝ) * x)

/-- Helper for Exercise 5.2.3: Fourier modes have orthonormal inner products on `[0,1]`. -/
lemma helperForExercise_5_2_3_expMode_inner
    (m n : ℤ) :
    periodicInnerProduct (expModePeriodicFunction m) (expModePeriodicFunction n) =
      if m = n then (1 : ℂ) else 0 := by
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl]
    unfold periodicInnerProduct
    have hInt :
        (∫ x in Set.Icc (0 : ℝ) 1,
          (expModePeriodicFunction m).1 x * star ((expModePeriodicFunction m).1 x))
          = ∫ x in Set.Icc (0 : ℝ) 1, (1 : ℂ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      have hNorm : ‖Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))‖ = 1 :=
        helperForExercise_5_2_3_expMode_norm_eq_one m x
      have hMulConj :
          Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) *
              star (Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) = (1 : ℂ) := by
        calc
          Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) *
              star (Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)))
              = (((Complex.normSq
                    (Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) : ℝ)) : ℂ) := by
                  simpa using
                    (Complex.mul_conj (Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))))
          _ = ((‖Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
                simp [Complex.normSq_eq_norm_sq]
          _ = (1 : ℂ) := by simp [hNorm]
      simpa [expModePeriodicFunction] using hMulConj
    rw [hInt]
    simp
  · have hDiff : (m - n : ℤ) ≠ 0 := sub_ne_zero.mpr hmn
    have hIntRewrite :
        (∫ x in Set.Icc (0 : ℝ) 1,
          (expModePeriodicFunction m).1 x * star ((expModePeriodicFunction n).1 x))
          = ∫ x in Set.Icc (0 : ℝ) 1,
              Complex.exp (((((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      change
        Complex.exp (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) *
            star (Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) =
          Complex.exp (((((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)))
      set z : ℂ := (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))
      have hStarExp : star (Complex.exp z) = Complex.exp (star z) := by
        simpa using (Complex.exp_conj z).symm
      have hz : star z = (-((n : ℂ) * (2 * Real.pi * Complex.I))) * (x : ℂ) := by
        simp [z, mul_comm]
      rw [show star (Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) =
            star (Complex.exp z) by simp [z]]
      rw [hStarExp, hz]
      rw [← Complex.exp_add]
      have hArg :
          (((m : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ)) +
              ((-((n : ℂ) * (2 * Real.pi * Complex.I))) * (x : ℂ))
            = (((((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))) := by
        simp [sub_eq_add_neg, mul_add, add_mul, mul_comm, mul_left_comm]
      rw [hArg]
    unfold periodicInnerProduct
    rw [hIntRewrite]
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have hCoeffNe : ((((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.two_pi_I_ne_zero
      exact_mod_cast hDiff
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le
      (f := fun x : ℝ => Complex.exp (((((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) * (x : ℂ))))
      h01]
    rw [integral_exp_mul_complex (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := (((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) hCoeffNe]
    simp
    have hExpCoeff : Complex.exp (((m - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using Complex.exp_int_mul_two_pi_mul_I (m - n)
    rw [if_neg hmn]
    have hExpCoeffSub : Complex.exp (((m : ℂ) - (n : ℂ)) * (2 * Real.pi * Complex.I)) = 1 := by
      simpa [Int.cast_sub] using hExpCoeff
    rw [hExpCoeffSub]
    simp

/-- Helper for Exercise 5.2.3: every Fourier mode has `L^2` norm squared equal to `1`. -/
lemma helperForExercise_5_2_3_expMode_l2Sq_eq_one
    (n : ℤ) :
    periodicL2Norm (expModePeriodicFunction n) ^ (2 : ℕ) = (1 : ℝ) := by
  calc
    periodicL2Norm (expModePeriodicFunction n) ^ (2 : ℕ)
        = (periodicInnerProduct (expModePeriodicFunction n) (expModePeriodicFunction n)).re :=
          (helperForLemma_5_2_7c_re_self_eq_sq_l2Norm (expModePeriodicFunction n)).symm
    _ = (if n = n then (1 : ℂ) else 0).re := by
          rw [helperForExercise_5_2_3_expMode_inner]
    _ = (1 : ℝ) := by simp

/-- Helper for Exercise 5.2.3: partial sums of positive Fourier modes. -/
noncomputable def sumExpModes : ℕ → {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1}
  | 0 => smulPeriodicFunction (0 : ℂ) (expModePeriodicFunction 0)
  | N + 1 => addPeriodicFunction (sumExpModes N) (expModePeriodicFunction (N + 1))

/-- Helper for Exercise 5.2.3: `sumExpModes N` is orthogonal to any higher mode. -/
lemma helperForExercise_5_2_3_sumExpModes_inner_of_lt
    (N k : ℕ) (hk : N < k) :
    periodicInnerProduct (sumExpModes N) (expModePeriodicFunction k) = 0 := by
  induction N generalizing k with
  | zero =>
      calc
        periodicInnerProduct (sumExpModes 0) (expModePeriodicFunction k)
            = periodicInnerProduct
                (smulPeriodicFunction (0 : ℂ) (expModePeriodicFunction 0))
                (expModePeriodicFunction k) := rfl
        _ = (0 : ℂ) * periodicInnerProduct (expModePeriodicFunction 0) (expModePeriodicFunction k) := by
              simpa using
                (periodicInnerProduct_linearity_first
                  (expModePeriodicFunction 0) (expModePeriodicFunction k)
                  (expModePeriodicFunction 0) (0 : ℂ)).2
        _ = 0 := by simp
  | succ n ih =>
      have hnk : n < k := lt_trans (Nat.lt_succ_self n) hk
      have hNe : ((n + 1 : ℤ) ≠ (k : ℤ)) := by
        exact_mod_cast (Nat.ne_of_lt hk)
      have hMode :
          periodicInnerProduct (expModePeriodicFunction (n + 1))
            (expModePeriodicFunction k) = 0 := by
        rw [helperForExercise_5_2_3_expMode_inner, if_neg hNe]
      calc
        periodicInnerProduct (sumExpModes (n + 1)) (expModePeriodicFunction k)
            = periodicInnerProduct
                (addPeriodicFunction (sumExpModes n) (expModePeriodicFunction (n + 1)))
                (expModePeriodicFunction k) := rfl
        _ = periodicInnerProduct (sumExpModes n) (expModePeriodicFunction k) +
              periodicInnerProduct (expModePeriodicFunction (n + 1))
                (expModePeriodicFunction k) := by
              simpa using
                (periodicInnerProduct_linearity_first
                  (sumExpModes n) (expModePeriodicFunction (n + 1))
                  (expModePeriodicFunction k) (1 : ℂ)).1
        _ = 0 := by simpa [ih k hnk, hMode]

/-- Helper for Exercise 5.2.3: `sumExpModes N` is orthogonal to the next mode. -/
lemma helperForExercise_5_2_3_sumExpModes_inner_next
    (N : ℕ) :
    periodicInnerProduct (sumExpModes N) (expModePeriodicFunction (N + 1)) = 0 := by
  exact helperForExercise_5_2_3_sumExpModes_inner_of_lt N (N + 1) (Nat.lt_succ_self N)

/-- Helper for Exercise 5.2.3: constant mode is orthogonal to `sumExpModes N`. -/
lemma helperForExercise_5_2_3_constMode_inner_sumExpModes
    (N : ℕ) :
    periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes N) = 0 := by
  induction N with
  | zero =>
      calc
        periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes 0)
            = periodicInnerProduct (expModePeriodicFunction 0)
                (smulPeriodicFunction (0 : ℂ) (expModePeriodicFunction 0)) := rfl
        _ = star (0 : ℂ) * periodicInnerProduct (expModePeriodicFunction 0) (expModePeriodicFunction 0) := by
              simpa using
                (periodicInnerProduct_antilinearity_second
                  (expModePeriodicFunction 0) (expModePeriodicFunction 0)
                  (expModePeriodicFunction 0) (0 : ℂ)).2
        _ = 0 := by simp
  | succ n ih =>
      have hNe : (0 : ℤ) ≠ (n + 1 : ℤ) := by
        exact_mod_cast (Nat.succ_ne_zero n)
      have hMode :
          periodicInnerProduct (expModePeriodicFunction 0)
            (expModePeriodicFunction (n + 1)) = 0 := by
        rw [helperForExercise_5_2_3_expMode_inner, if_neg hNe]
      calc
        periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes (n + 1))
            = periodicInnerProduct (expModePeriodicFunction 0)
                (addPeriodicFunction (sumExpModes n) (expModePeriodicFunction (n + 1))) := rfl
        _ = periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes n) +
              periodicInnerProduct (expModePeriodicFunction 0)
                (expModePeriodicFunction (n + 1)) := by
              simpa using
                (periodicInnerProduct_antilinearity_second
                  (expModePeriodicFunction 0) (sumExpModes n)
                  (expModePeriodicFunction (n + 1)) (1 : ℂ)).1
        _ = 0 := by simpa [ih, hMode]

/-- Helper for Exercise 5.2.3: `sumExpModes N` has exact `L^2` norm square `N`. -/
lemma helperForExercise_5_2_3_sumExpModes_l2Sq
    (N : ℕ) :
    periodicL2Norm (sumExpModes N) ^ (2 : ℕ) = (N : ℝ) := by
  induction N with
  | zero =>
      calc
        periodicL2Norm (sumExpModes 0) ^ (2 : ℕ)
            = periodicL2Norm (smulPeriodicFunction (0 : ℂ) (expModePeriodicFunction 0)) ^ (2 : ℕ) := rfl
        _ = ((‖(0 : ℂ)‖ * periodicL2Norm (expModePeriodicFunction 0)) : ℝ) ^ (2 : ℕ) := by
              rw [periodicL2Norm_smul]
        _ = ((0 : ℕ) : ℝ) := by norm_num
  | succ n ih =>
      have hOrth :
          periodicInnerProduct (sumExpModes n) (expModePeriodicFunction (n + 1)) = 0 :=
        helperForExercise_5_2_3_sumExpModes_inner_next n
      have hPyth :=
        periodicL2Norm_pythagoras (sumExpModes n) (expModePeriodicFunction (n + 1)) hOrth
      calc
        periodicL2Norm (sumExpModes (n + 1)) ^ (2 : ℕ)
            = periodicL2Norm
                (addPeriodicFunction (sumExpModes n) (expModePeriodicFunction (n + 1))) ^ (2 : ℕ) := rfl
        _ = periodicL2Norm (sumExpModes n) ^ (2 : ℕ) +
              periodicL2Norm (expModePeriodicFunction (n + 1)) ^ (2 : ℕ) := hPyth
        _ = (n : ℝ) + 1 := by
              rw [ih, helperForExercise_5_2_3_expMode_l2Sq_eq_one]
        _ = ((n + 1 : ℕ) : ℝ) := by norm_num

/-- Helper for Exercise 5.2.3: value of `sumExpModes N` at `0` is exactly `N`. -/
lemma helperForExercise_5_2_3_sumExpModes_value_zero
    (N : ℕ) :
    (sumExpModes N).1 (0 : ℝ) = (N : ℂ) := by
  induction N with
  | zero =>
      simp [sumExpModes, smulPeriodicFunction]
  | succ n ih =>
      calc
        (sumExpModes (n + 1)).1 (0 : ℝ)
            = (sumExpModes n).1 0 + (expModePeriodicFunction (n + 1)).1 0 := by
              simp [sumExpModes, addPeriodicFunction]
        _ = (n : ℂ) + 1 := by
              rw [ih]
              simp [expModePeriodicFunction]
        _ = ((n + 1 : ℕ) : ℂ) := by norm_num

/-- Helper for Exercise 5.2.3: pointwise bound for partial Fourier sums. -/
lemma helperForExercise_5_2_3_sumExpModes_norm_le
    (N : ℕ) (x : ℝ) :
    ‖(sumExpModes N).1 x‖ ≤ (N : ℝ) := by
  induction N with
  | zero =>
      simp [sumExpModes, smulPeriodicFunction]
  | succ n ih =>
      calc
        ‖(sumExpModes (n + 1)).1 x‖
            = ‖(sumExpModes n).1 x + (expModePeriodicFunction (n + 1)).1 x‖ := by
                simp [sumExpModes, addPeriodicFunction]
        _ ≤ ‖(sumExpModes n).1 x‖ + ‖(expModePeriodicFunction (n + 1)).1 x‖ := norm_add_le _ _
        _ = ‖(sumExpModes n).1 x‖ + 1 := by
              rw [helperForExercise_5_2_3_expMode_norm_eq_one]
        _ ≤ (n : ℝ) + 1 := by linarith [ih]
        _ = ((n + 1 : ℕ) : ℝ) := by norm_num

/-- Helper for Exercise 5.2.3: normalized average of the first `N` positive Fourier modes. -/
noncomputable def averageExpModesPeriodicFunction
    (N : ℕ) :
    {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
  smulPeriodicFunction ((1 / (N : ℝ)) : ℂ) (sumExpModes N)

/-- Helper for Exercise 5.2.3: exact profile of the normalized mode average, including
orthogonality to the constant mode, exact `L^2` square, exact `L^∞`, and value at `0`. -/
lemma helperForExercise_5_2_3_average_modes_profile
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
      periodicInnerProduct (expModePeriodicFunction 0) g = 0 ∧
      periodicL2Norm g ^ (2 : ℕ) = (1 : ℝ) / N ∧
      periodicLInftyNorm g = 1 ∧ g.1 0 = 1 := by
  let g : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
    averageExpModesPeriodicFunction N
  have hNpos_nat : 0 < N := Nat.succ_le_iff.mp hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNpos_nat
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hInnerSum : periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes N) = 0 := by
    simpa using helperForExercise_5_2_3_constMode_inner_sumExpModes N
  have hInner : periodicInnerProduct (expModePeriodicFunction 0) g = 0 := by
    have hSmul :
        periodicInnerProduct (expModePeriodicFunction 0)
            (smulPeriodicFunction ((1 / (N : ℝ)) : ℂ) (sumExpModes N)) =
          star (((1 / (N : ℝ)) : ℂ)) * periodicInnerProduct (expModePeriodicFunction 0) (sumExpModes N) := by
      simpa using
        (periodicInnerProduct_antilinearity_second
          (expModePeriodicFunction 0) (sumExpModes N) (sumExpModes N)
          ((1 / (N : ℝ)) : ℂ)).2
    simpa [g, averageExpModesPeriodicFunction, hInnerSum] using hSmul
  have hL2Sq : periodicL2Norm g ^ (2 : ℕ) = (1 : ℝ) / N := by
    calc
      periodicL2Norm g ^ (2 : ℕ)
          = periodicL2Norm
              (smulPeriodicFunction ((1 / (N : ℝ)) : ℂ) (sumExpModes N)) ^ (2 : ℕ) := by
                rfl
      _ = (‖((1 / (N : ℝ)) : ℂ)‖ * periodicL2Norm (sumExpModes N)) ^ (2 : ℕ) := by
            rw [periodicL2Norm_smul]
      _ = ‖((1 / (N : ℝ)) : ℂ)‖ ^ (2 : ℕ) * (periodicL2Norm (sumExpModes N)) ^ (2 : ℕ) := by ring
      _ = ((1 / (N : ℝ)) ^ (2 : ℕ)) * (N : ℝ) := by
            have hNormInv : ‖((1 / (N : ℝ)) : ℂ)‖ = (1 / (N : ℝ)) := by
              norm_num [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hNpos_nat)]
            rw [hNormInv]
            rw [helperForExercise_5_2_3_sumExpModes_l2Sq]
      _ = (1 : ℝ) / N := by
            field_simp [hNne]
  have hValue0 : g.1 (0 : ℝ) = 1 := by
    calc
      g.1 (0 : ℝ)
          = (((1 / (N : ℝ)) : ℂ) * (sumExpModes N).1 0) := by
              simp [g, averageExpModesPeriodicFunction, smulPeriodicFunction]
      _ = (((1 / (N : ℝ)) : ℂ) * (N : ℂ)) := by
            rw [helperForExercise_5_2_3_sumExpModes_value_zero]
      _ = 1 := by
            norm_num [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hNpos_nat)]
  have hUpper : periodicLInftyNorm g ≤ 1 := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖g.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove g
    have hNonempty : Set.Nonempty (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖g.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_nonempty g
    unfold periodicLInftyNorm
    refine csSup_le hNonempty ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    have hPoint : ‖(sumExpModes N).1 x‖ ≤ (N : ℝ) :=
      helperForExercise_5_2_3_sumExpModes_norm_le N x
    have hInvNonneg : 0 ≤ (1 / (N : ℝ)) := by positivity
    calc
      ‖g.1 x‖
          = ‖(((1 / (N : ℝ)) : ℂ) * (sumExpModes N).1 x)‖ := by
              simp [g, averageExpModesPeriodicFunction, smulPeriodicFunction]
      _ = ‖((1 / (N : ℝ)) : ℂ)‖ * ‖(sumExpModes N).1 x‖ := by
            simpa using norm_mul (((1 / (N : ℝ)) : ℂ)) ((sumExpModes N).1 x)
      _ = (1 / (N : ℝ)) * ‖(sumExpModes N).1 x‖ := by
            have hNormInv : ‖((1 / (N : ℝ)) : ℂ)‖ = (1 / (N : ℝ)) := by
              norm_num [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hNpos_nat)]
            rw [hNormInv]
      _ ≤ (1 / (N : ℝ)) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hPoint hInvNonneg
      _ = 1 := by field_simp [hNne]
  have hLower : (1 : ℝ) ≤ periodicLInftyNorm g := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖g.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove g
    have hMem :
        (1 : ℝ) ∈ Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖g.1 x‖) := by
      refine ⟨⟨0, helperForExercise_5_2_3_zero_mem_Icc⟩, ?_⟩
      simpa [hValue0]
    unfold periodicLInftyNorm
    exact le_csSup hBdd hMem
  have hInfty : periodicLInftyNorm g = 1 := le_antisymm hUpper hLower
  exact ⟨g, hInner, hL2Sq, hInfty, hValue0⟩

/-- Helper for Exercise 5.2.3: exact blended profile with prescribed
`t^2 + (1 - t)^2 / N`, unit `L^∞`, and value `1` at zero. -/
lemma helperForExercise_5_2_3_blend_profile
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ u : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
      periodicLInftyNorm u = 1 ∧
      periodicL2Norm u ^ (2 : ℕ) = t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N ∧
      u.1 0 = 1 := by
  rcases helperForExercise_5_2_3_average_modes_profile N hN with
    ⟨g, hgOrth, hgL2Sq, hgInfty, hgZero⟩
  let u : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
    addPeriodicFunction
      (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0))
      (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)
  have hOneMinusNonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hInnerScaled :
      periodicInnerProduct
          (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0))
          (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g) = 0 := by
    have hFirst :
        periodicInnerProduct
            (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0))
            (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)
          = (t : ℂ) *
              periodicInnerProduct (expModePeriodicFunction 0)
                (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g) := by
      simpa using
        (periodicInnerProduct_linearity_first
          (expModePeriodicFunction 0) (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)
          (expModePeriodicFunction 0) (t : ℂ)).2
    have hSecond :
        periodicInnerProduct (expModePeriodicFunction 0)
            (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)
          = star (((1 - t : ℝ) : ℂ)) * periodicInnerProduct (expModePeriodicFunction 0) g := by
      simpa using
        (periodicInnerProduct_antilinearity_second
          (expModePeriodicFunction 0) g g ((1 - t : ℝ) : ℂ)).2
    rw [hFirst, hSecond, hgOrth]
    simp
  have hL2Sq :
      periodicL2Norm u ^ (2 : ℕ) = t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N := by
    have hPyth := periodicL2Norm_pythagoras
      (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0))
      (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)
      hInnerScaled
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (Nat.succ_le_iff.mp hN)
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hFirstSq :
        periodicL2Norm (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0)) ^ (2 : ℕ)
          = t ^ (2 : ℕ) := by
      rw [periodicL2Norm_smul]
      have hModeL2 : periodicL2Norm (expModePeriodicFunction (0 : ℤ)) ^ (2 : ℕ) = (1 : ℝ) :=
        helperForExercise_5_2_3_expMode_l2Sq_eq_one (0 : ℤ)
      rw [helperForExercise_5_2_3_complexNorm_ofReal]
      rw [abs_of_nonneg ht0]
      nlinarith [hModeL2]
    have hSecondSq :
        periodicL2Norm (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g) ^ (2 : ℕ)
          = (1 - t) ^ (2 : ℕ) / N := by
      rw [periodicL2Norm_smul]
      rw [helperForExercise_5_2_3_complexNorm_ofReal]
      rw [abs_of_nonneg hOneMinusNonneg]
      calc
        ((1 - t) * periodicL2Norm g) ^ (2 : ℕ)
            = (1 - t) ^ (2 : ℕ) * (periodicL2Norm g) ^ (2 : ℕ) := by ring
        _ = (1 - t) ^ (2 : ℕ) * ((1 : ℝ) / N) := by rw [hgL2Sq]
        _ = (1 - t) ^ (2 : ℕ) / N := by field_simp [hNne]
    calc
      periodicL2Norm u ^ (2 : ℕ)
          = periodicL2Norm
              (addPeriodicFunction
                (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0))
                (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g)) ^ (2 : ℕ) := by rfl
      _ = periodicL2Norm (smulPeriodicFunction (t : ℂ) (expModePeriodicFunction 0)) ^ (2 : ℕ) +
            periodicL2Norm (smulPeriodicFunction ((1 - t : ℝ) : ℂ) g) ^ (2 : ℕ) := hPyth
      _ = t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N := by rw [hFirstSq, hSecondSq]
  have hUZero : u.1 0 = 1 := by
    have hModeZero : (expModePeriodicFunction 0).1 (0 : ℝ) = 1 := by
      simp [expModePeriodicFunction]
    simp [u, addPeriodicFunction, smulPeriodicFunction, hgZero, hModeZero]
  have hPointG :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → ‖g.1 x‖ ≤ 1 := by
    intro x hx
    have hBdd : BddAbove (Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖g.1 y‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove g
    have hxIn : ‖g.1 x‖ ∈ Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖g.1 y‖) :=
      ⟨⟨x, hx⟩, rfl⟩
    have hLeSup : ‖g.1 x‖ ≤ periodicLInftyNorm g := by
      unfold periodicLInftyNorm
      exact le_csSup hBdd hxIn
    simpa [hgInfty] using hLeSup
  have hUpper : periodicLInftyNorm u ≤ 1 := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖u.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove u
    have hNonempty : Set.Nonempty (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖u.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_nonempty u
    unfold periodicLInftyNorm
    refine csSup_le hNonempty ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    calc
      ‖u.1 x‖
          = ‖(t : ℂ) * (expModePeriodicFunction 0).1 x + ((1 - t : ℝ) : ℂ) * g.1 x‖ := by
              simp [u, addPeriodicFunction, smulPeriodicFunction]
      _ ≤ ‖(t : ℂ) * (expModePeriodicFunction 0).1 x‖ + ‖((1 - t : ℝ) : ℂ) * g.1 x‖ :=
            norm_add_le _ _
      _ = ‖(t : ℂ)‖ * ‖(expModePeriodicFunction 0).1 x‖ +
            ‖((1 - t : ℝ) : ℂ)‖ * ‖g.1 x‖ := by
              simp [norm_mul]
      _ = t * 1 + (1 - t) * ‖g.1 x‖ := by
            rw [helperForExercise_5_2_3_complexNorm_ofReal]
            rw [helperForExercise_5_2_3_complexNorm_ofReal]
            rw [abs_of_nonneg ht0]
            rw [abs_of_nonneg hOneMinusNonneg]
            rw [helperForExercise_5_2_3_expMode_norm_eq_one]
      _ ≤ t * 1 + (1 - t) * 1 := by
            have hMul : (1 - t) * ‖g.1 x‖ ≤ (1 - t) * 1 :=
              mul_le_mul_of_nonneg_left (hPointG x.1 x.2) hOneMinusNonneg
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hMul (t * 1)
      _ = 1 := by ring
  have hLower : (1 : ℝ) ≤ periodicLInftyNorm u := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖u.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove u
    have hMem : (1 : ℝ) ∈ Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖u.1 x‖) := by
      refine ⟨⟨0, helperForExercise_5_2_3_zero_mem_Icc⟩, ?_⟩
      simpa [hUZero]
    unfold periodicLInftyNorm
    exact le_csSup hBdd hMem
  have hInfty : periodicLInftyNorm u = 1 := le_antisymm hUpper hLower
  exact ⟨u, hInfty, hL2Sq, hUZero⟩

/-- Helper for Exercise 5.2.3: strict converse case `A < B`. -/
lemma helperForExercise_5_2_3_exists_exact_norms_strict
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) :
    ∃ f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
      f.1 ≠ 0 ∧ periodicL2Norm f = A ∧ periodicLInftyNorm f = B := by
  have hB : 0 < B := lt_trans hA hAB
  let r : ℝ := (A / B) ^ (2 : ℕ)
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    have hAB_div : A / B < 1 := (div_lt_iff₀ hB).2 (by simpa using hAB)
    have hAB_div_nonneg : 0 ≤ A / B := by positivity
    dsimp [r]
    nlinarith [hAB_div, hAB_div_nonneg]
  rcases helperForExercise_5_2_3_choose_parameters_for_ratio r hr0 hr1 with
    ⟨N, hNge1, t, ht0, ht1, htEq⟩
  rcases helperForExercise_5_2_3_blend_profile N hNge1 t ht0 ht1 with
    ⟨u, huInfty, huL2Sq, huZero⟩
  let f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1} :=
    smulPeriodicFunction (B : ℂ) u
  have hUSq : periodicL2Norm u ^ (2 : ℕ) = (A / B) ^ (2 : ℕ) := by
    calc
      periodicL2Norm u ^ (2 : ℕ) = t ^ (2 : ℕ) + (1 - t) ^ (2 : ℕ) / N := huL2Sq
      _ = r := htEq
      _ = (A / B) ^ (2 : ℕ) := rfl
  have hUNonneg : 0 ≤ periodicL2Norm u := by
    unfold periodicL2Norm
    exact Real.sqrt_nonneg _
  have hRatioPos : 0 < A / B := div_pos hA hB
  have hUEq : periodicL2Norm u = A / B := by
    have hSqEq : (periodicL2Norm u) ^ (2 : ℕ) = (A / B) ^ (2 : ℕ) := by
      simpa [pow_two] using hUSq
    have hSubMul : (periodicL2Norm u - A / B) * (periodicL2Norm u + A / B) = 0 := by
      nlinarith [hSqEq]
    have hSumNe : periodicL2Norm u + A / B ≠ 0 := by
      linarith [hUNonneg, hRatioPos]
    have hSubZero : periodicL2Norm u - A / B = 0 :=
      (mul_eq_zero.mp hSubMul).resolve_right hSumNe
    linarith
  have hL2EqA : periodicL2Norm f = A := by
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt hB
    calc
      periodicL2Norm f
          = periodicL2Norm (smulPeriodicFunction (B : ℂ) u) := rfl
      _ = ‖(B : ℂ)‖ * periodicL2Norm u := by rw [periodicL2Norm_smul]
      _ = B * (A / B) := by
            rw [helperForExercise_5_2_3_complexNorm_ofReal]
            rw [abs_of_pos hB]
            rw [hUEq]
      _ = A := by field_simp [hBne]
  have hPointU :
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → ‖u.1 x‖ ≤ 1 := by
    intro x hx
    have hBdd : BddAbove (Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖u.1 y‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove u
    have hxIn : ‖u.1 x‖ ∈ Set.range (fun y : Set.Icc (0 : ℝ) 1 => ‖u.1 y‖) :=
      ⟨⟨x, hx⟩, rfl⟩
    have hLeSup : ‖u.1 x‖ ≤ periodicLInftyNorm u := by
      unfold periodicLInftyNorm
      exact le_csSup hBdd hxIn
    simpa [huInfty] using hLeSup
  have hInftyUpper : periodicLInftyNorm f ≤ B := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove f
    have hNonempty : Set.Nonempty (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_nonempty f
    unfold periodicLInftyNorm
    refine csSup_le hNonempty ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    calc
      ‖f.1 x‖
          = ‖(B : ℂ) * u.1 x‖ := by
              simp [f, smulPeriodicFunction]
      _ = ‖(B : ℂ)‖ * ‖u.1 x‖ := by
            simpa using norm_mul (B : ℂ) (u.1 x)
      _ = B * ‖u.1 x‖ := by
            rw [helperForExercise_5_2_3_complexNorm_ofReal]
            rw [abs_of_pos hB]
      _ ≤ B * 1 := by
            exact mul_le_mul_of_nonneg_left (hPointU x.1 x.2) (le_of_lt hB)
      _ = B := by ring
  have hFNormZero : ‖f.1 (0 : ℝ)‖ = B := by
    calc
      ‖f.1 (0 : ℝ)‖
          = ‖(B : ℂ) * u.1 (0 : ℝ)‖ := by
              simp [f, smulPeriodicFunction]
      _ = ‖(B : ℂ)‖ * ‖u.1 (0 : ℝ)‖ := by
            simpa using norm_mul (B : ℂ) (u.1 (0 : ℝ))
      _ = B * ‖u.1 (0 : ℝ)‖ := by
            rw [helperForExercise_5_2_3_complexNorm_ofReal]
            rw [abs_of_pos hB]
      _ = B := by simpa [huZero]
  have hInftyLower : B ≤ periodicLInftyNorm f := by
    have hBdd : BddAbove (Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖)) :=
      helperForExercise_5_2_3_lInftyRange_bddAbove f
    have hMem : B ∈ Set.range (fun x : Set.Icc (0 : ℝ) 1 => ‖f.1 x‖) := by
      refine ⟨⟨0, helperForExercise_5_2_3_zero_mem_Icc⟩, ?_⟩
      simpa using hFNormZero
    unfold periodicLInftyNorm
    exact le_csSup hBdd hMem
  have hInftyEqB : periodicLInftyNorm f = B :=
    le_antisymm hInftyUpper hInftyLower
  have hNonzero : f.1 ≠ 0 := by
    intro hZero
    have hL2Zero : periodicL2Norm f = 0 := (periodicL2Norm_eq_zero_iff f).2 hZero
    linarith [hL2EqA, hA]
  exact ⟨f, hNonzero, hL2EqA, hInftyEqB⟩

/-- Exercise 5.2.3: if `f ∈ C(ℝ/ℤ; ℂ)` is non-zero, then
`0 < ‖f‖_2 ≤ ‖f‖_{L^∞}`; conversely, for real numbers `0 < A ≤ B`, there
exists a non-zero `f ∈ C(ℝ/ℤ; ℂ)` with `‖f‖_2 = A` and `‖f‖_{L^∞} = B`. -/
theorem exercise_5_2_3 :
    (∀ f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
      f.1 ≠ 0 →
        0 < periodicL2Norm f ∧ periodicL2Norm f ≤ periodicLInftyNorm f) ∧
      (∀ A B : ℝ, 0 < A → A ≤ B →
        ∃ f : {h : ℝ → ℂ // Continuous h ∧ Function.Periodic h 1},
          f.1 ≠ 0 ∧ periodicL2Norm f = A ∧ periodicLInftyNorm f = B) := by
  constructor
  · intro f hne
    refine ⟨helperForExercise_5_2_3_nonzero_implies_l2_pos f hne,
      helperForExercise_5_2_3_l2_le_lInfty f⟩
  · intro A B hA hAB
    by_cases hEq : A = B
    · subst hEq
      exact helperForExercise_5_2_3_exists_exact_norms_on_diagonal A hA
    · have hLt : A < B := lt_of_le_of_ne hAB hEq
      exact helperForExercise_5_2_3_exists_exact_norms_strict A B hA hLt


end Section02
end Chap05

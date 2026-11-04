/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_22.Cutoff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped Matrix

noncomputable section

namespace UniformEllipsoidAlgorithm

/-- Helper for Theorem 7.22: the polynomial witness combines the encoding bounds for the lower
and upper volume parameters into one uniform cutoff bound. -/
private def cutoffPolynomial (πLower πUpper : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 1 + Polynomial.C 2 * (Polynomial.X + 1) * (πLower + πUpper)

/-- Helper for Theorem 7.22: a positive rational contributes at least one binary digit from its
positive numerator, one from its positive denominator, and one sign bit to
`EncodingSize.rational`. -/
private lemma three_le_encodingSize_rational_of_pos
    {q : ℚ} (hq : 0 < q) :
    3 ≤ EncodingSize.rational q := by
  -- A positive rational has positive numerator and denominator, so each size term contributes.
  rw [EncodingSize.rational_eq]
  have hnum : 0 < q.num.natAbs := by
    exact Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'
  have hsnum : 1 ≤ Nat.size q.num.natAbs := Nat.succ_le_of_lt (Nat.size_pos.mpr hnum)
  have hsden : 1 ≤ Nat.size q.den := Nat.succ_le_of_lt (Nat.size_pos.mpr q.pos)
  omega

/-- Helper for Theorem 7.22: every positive binary power is strictly smaller than the matching
exponential bound `exp L`. -/
private lemma twoPowLtExpOfPos {L : ℕ} (hL : 0 < L) :
    (2 : ℝ) ^ L < Real.exp L := by
  -- Compare powers using the strict base inequality `2 < exp 1`.
  have htwo_lt_exp_one : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  calc
    (2 : ℝ) ^ L < (Real.exp 1) ^ L := by
      exact pow_lt_pow_left₀ htwo_lt_exp_one (by positivity) hL.ne'
    _ = Real.exp L := by
      rw [← Real.exp_nat_mul 1 L, mul_one]

/-- Helper for Theorem 7.22: a positive rational with encoding size at most `L` has positive
cutoff length, and each of its numerator and denominator bit lengths is bounded by `L`. -/
private lemma positiveRat_sizeBounds_of_encodingSize_le
    {q : ℚ} {L : ℕ}
    (hq : 0 < q)
    (hL : EncodingSize.rational q ≤ L) :
    0 < L ∧ Nat.size q.num.natAbs ≤ L ∧ Nat.size q.den ≤ L := by
  -- The total encoding budget bounds each size term separately and is itself positive.
  have hthree : 3 ≤ EncodingSize.rational q := three_le_encodingSize_rational_of_pos hq
  rw [EncodingSize.rational_eq] at hL
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Helper for Theorem 7.22: a positive rational with encoding size at most `L` is bounded above
by `exp L`. -/
private lemma positiveRat_upperExpBound_of_encodingSize_le
    {q : ℚ} {L : ℕ}
    (hq : 0 < q)
    (hL : EncodingSize.rational q ≤ L) :
    (q : ℝ) < Real.exp L := by
  -- Rewrite `q` as numerator over denominator and bound the numerator by `2 ^ L`.
  rcases positiveRat_sizeBounds_of_encodingSize_le hq hL with ⟨hLpos, hnum_size, hden_size⟩
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hnum_natAbs_lt : q.num.natAbs < 2 ^ L := (Nat.size_le.mp hnum_size)
  have hnum_eq : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum_pos.le
  have hq_eq : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  have hnum_nonneg : 0 ≤ (q.num : ℝ) := by
    exact_mod_cast hnum_pos.le
  have hdiv_le_num : (q.num : ℝ) / q.den ≤ q.num := by
    have hden_pos : (0 : ℝ) < q.den := by
      exact_mod_cast q.pos
    have hden_ge_one : (1 : ℝ) ≤ q.den := by
      exact_mod_cast q.pos
    simpa using div_le_self hnum_nonneg hden_ge_one
  have hnum_lt_pow : (q.num : ℝ) < (2 : ℝ) ^ L := by
    have : (q.num : ℝ) = q.num.natAbs := by
      exact congrArg (fun z : ℤ ↦ (z : ℝ)) hnum_eq.symm
    rw [this]
    exact_mod_cast hnum_natAbs_lt
  calc
    (q : ℝ) = (q.num : ℝ) / q.den := hq_eq
    _ ≤ q.num := hdiv_le_num
    _ < (2 : ℝ) ^ L := hnum_lt_pow
    _ < Real.exp L := twoPowLtExpOfPos hLpos

/-- Helper for Theorem 7.22: the reciprocal of `2 ^ L` still dominates `exp (-L)`. -/
private lemma expNegLtInvTwoPowOfPos {L : ℕ} (hL : 0 < L) :
    Real.exp (-(L : ℝ)) < ((2 : ℝ) ^ L)⁻¹ := by
  -- Inversion reverses the upper exponential bound on `2 ^ L`.
  have hpow : (2 : ℝ) ^ L < Real.exp L := twoPowLtExpOfPos hL
  have hpow_pos : 0 < (2 : ℝ) ^ L := by positivity
  have hinv : (Real.exp L)⁻¹ < ((2 : ℝ) ^ L)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hpow_pos hpow
  simpa [Real.exp_neg, one_div] using hinv

/-- Helper for Theorem 7.22: a positive rational with encoding size at most `L` is bounded below
by `exp (-L)`. -/
private lemma positiveRat_lowerExpBound_of_encodingSize_le
    {q : ℚ} {L : ℕ}
    (hq : 0 < q)
    (hL : EncodingSize.rational q ≤ L) :
    Real.exp (-(L : ℝ)) < (q : ℝ) := by
  -- A positive rational is at least the reciprocal of its denominator.
  rcases positiveRat_sizeBounds_of_encodingSize_le hq hL with ⟨hLpos, _hnum_size, hden_size⟩
  have hq_eq : (q : ℝ) = (q.num : ℝ) / q.den := by
    exact_mod_cast (Rat.num_div_den q).symm
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hnum_ge_one : (1 : ℝ) ≤ q.num := by
    exact_mod_cast hnum_pos
  have hden_pos : (0 : ℝ) < q.den := by
    exact_mod_cast q.pos
  have hden_lt_pow : (q.den : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast (Nat.size_le.mp hden_size)
  have hinv_lt : ((2 : ℝ) ^ L)⁻¹ < (q.den : ℝ)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hden_pos hden_lt_pow
  have hden_inv_le : (q.den : ℝ)⁻¹ ≤ (q.num : ℝ) / q.den := by
    have hden_inv_nonneg : 0 ≤ (q.den : ℝ)⁻¹ := by positivity
    simpa [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hnum_ge_one hden_inv_nonneg
  calc
    Real.exp (-(L : ℝ)) < ((2 : ℝ) ^ L)⁻¹ := expNegLtInvTwoPowOfPos hLpos
    _ < (q.den : ℝ)⁻¹ := hinv_lt
    _ ≤ (q.num : ℝ) / q.den := hden_inv_le
    _ = (q : ℝ) := hq_eq.symm

/-- Helper for Theorem 7.22: a positive rational whose encoding size is bounded by `L` lies
between the two exponential barriers `exp (-L)` and `exp L`. -/
private lemma positiveRat_expBounds_of_encodingSize_le
    {q : ℚ} {L : ℕ}
    (hq : 0 < q)
    (hL : EncodingSize.rational q ≤ L) :
    Real.exp (-(L : ℝ)) < (q : ℝ) ∧ (q : ℝ) < Real.exp L := by
  -- Combine the separate lower and upper exponential barriers.
  exact ⟨positiveRat_lowerExpBound_of_encodingSize_le hq hL,
    positiveRat_upperExpBound_of_encodingSize_le hq hL⟩

/-- Helper for Theorem 7.22: the explicit iteration budget forces the contraction factor
below `exp (-Lsum)`. -/
private lemma budgetContraction_le_expNeg
    {n Lsys Lsum remaining : ℕ}
    (h_sys_ge_n : n ≤ Lsys)
    (h_remaining : remaining = 2 * (Lsys + 1) * Lsum) :
    (Real.exp (-(1 / (2 * (n : ℝ) + 2)))) ^ remaining ≤
      Real.exp (-(Lsum : ℝ)) := by
  -- The explicit budget makes the repeated shrink factor at most `exp (-Lsum)`.
  have hden_pos : 0 < (2 * (n : ℝ) + 2) := by positivity
  have hmain :
      (remaining : ℝ) * (1 / (2 * (n : ℝ) + 2)) ≥ Lsum := by
    rw [h_remaining]
    have hsuc_le : (n : ℝ) + 1 ≤ (Lsys : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ h_sys_ge_n
    have hLsum_nonneg : 0 ≤ (Lsum : ℝ) := by positivity
    have hratio_ge_one : (1 : ℝ) ≤ ((Lsys : ℝ) + 1) / ((n : ℝ) + 1) := by
      refine (one_le_div (by positivity)).2 hsuc_le
    have hscaled :
        (Lsum : ℝ) ≤ (((Lsys : ℝ) + 1) / ((n : ℝ) + 1)) * Lsum := by
      nlinarith
    have hfactor :
        (((2 * (Lsys + 1) * Lsum : ℕ) : ℝ) * (1 / (2 * (n : ℝ) + 2))) =
          (((Lsys : ℝ) + 1) / ((n : ℝ) + 1)) * Lsum := by
      norm_num [Nat.cast_mul, Nat.cast_add]
      field_simp
    rw [hfactor]
    exact hscaled
  calc
    (Real.exp (-(1 / (2 * (n : ℝ) + 2)))) ^ remaining =
        Real.exp ((remaining : ℝ) * (-(1 / (2 * (n : ℝ) + 2)))) := by
      simpa [mul_comm] using (Real.exp_nat_mul (-(1 / (2 * (n : ℝ) + 2))) remaining).symm
    _ ≤ Real.exp (-(Lsum : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith

/-- Helper for Theorem 7.22: once the shrink factor is bounded by `exp (-(Lε + LΔ))`, the upper
volume bound `δ < exp LΔ` falls below the lower threshold `ε`. -/
private lemma realShrinkGap_of_expBounds
    {Lε LΔ : ℕ} {u δ ε : ℝ}
    (hu : u ≤ Real.exp (-(Lε + LΔ : ℝ)))
    (hδ_pos : 0 < δ)
    (hδ_lt : δ < Real.exp LΔ)
    (hε_lower : Real.exp (-(Lε : ℝ)) < ε) :
    u * δ < ε := by
  -- Either `u` is already negative, or the exponential upper bound propagates through
  -- multiplication by the positive `δ`.
  by_cases hu_nonneg : 0 ≤ u
  · have hexp_pos : 0 < Real.exp (-(Lε + LΔ : ℝ)) := Real.exp_pos _
    have hmul_le : u * δ ≤ Real.exp (-(Lε + LΔ : ℝ)) * δ := by
      exact mul_le_mul_of_nonneg_right hu hδ_pos.le
    have hmul_lt :
        Real.exp (-(Lε + LΔ : ℝ)) * δ <
          Real.exp (-(Lε + LΔ : ℝ)) * Real.exp LΔ := by
      exact mul_lt_mul_of_pos_left hδ_lt hexp_pos
    calc
      u * δ ≤ Real.exp (-(Lε + LΔ : ℝ)) * δ := hmul_le
      _ < Real.exp (-(Lε + LΔ : ℝ)) * Real.exp LΔ := hmul_lt
      _ = Real.exp (-(Lε : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < ε := hε_lower
  · have hu_lt : u < 0 := lt_of_not_ge hu_nonneg
    have hmul_lt_zero : u * δ < 0 := mul_neg_of_neg_of_pos hu_lt hδ_pos
    have hε_pos : 0 < ε := lt_trans (Real.exp_pos _) hε_lower
    exact lt_trans hmul_lt_zero hε_pos

/-- Helper for Theorem 7.22: the encoding-size bounds on `ε` and `Δ` imply the explicit strict
shrink inequality needed by the correctness recursion. -/
private lemma shrinkGap_of_encodingBounds
    (ρ : ℕ → ENNReal)
    (ε Δ : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℚ → (Fin m → ℚ) → ℚ)
    (πLower πUpper : Polynomial ℕ)
    (hρ : ∀ n : ℕ,
      ρ n ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * (n : ℝ) + 2)))))
    (hε_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < ε A b)
    (hΔ_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < Δ A b)
    (hε_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (ε A b) ≤
          πLower.eval (n + rational_linear_system_encoding_size A b))
    (hΔ_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (Δ A b) ≤
          πUpper.eval (n + rational_linear_system_encoding_size A b))
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b))
    (remaining : ℕ)
    (h_remaining :
      remaining = 2 * (n + rational_linear_system_encoding_size A b + 1) *
        (πLower.eval (n + rational_linear_system_encoding_size A b) +
          πUpper.eval (n + rational_linear_system_encoding_size A b))) :
    (ρ n) ^ remaining * ENNReal.ofReal (Δ A b : ℝ) <
      ENNReal.ofReal (ε A b : ℝ) := by
  let Lsys := n + rational_linear_system_encoding_size A b
  let Lε := πLower.eval Lsys
  let LΔ := πUpper.eval Lsys
  let expBase := Real.exp (-(1 / (2 * (n : ℝ) + 2)))
  have hε_pos' : 0 < ε A b := hε_pos A b h_bounded
  have hΔ_pos' : 0 < Δ A b := hΔ_pos A b h_bounded
  have hε_pos_real : 0 < (ε A b : ℝ) := by
    exact_mod_cast hε_pos'
  have hΔ_pos_real : 0 < (Δ A b : ℝ) := by
    exact_mod_cast hΔ_pos'
  have hε_bounds :
      Real.exp (-(Lε : ℝ)) < (ε A b : ℝ) ∧ (ε A b : ℝ) < Real.exp Lε := by
    -- The lower threshold `ε` inherits exponential upper and lower bounds from its encoding size.
    refine positiveRat_expBounds_of_encodingSize_le hε_pos' ?_
    simpa [Lsys, Lε] using hε_encoding A b h_bounded
  have hΔ_bounds :
      Real.exp (-(LΔ : ℝ)) < (Δ A b : ℝ) ∧ (Δ A b : ℝ) < Real.exp LΔ := by
    -- The initial-volume bound `Δ` obeys the same encoding-controlled exponential barrier.
    refine positiveRat_expBounds_of_encodingSize_le hΔ_pos' ?_
    simpa [Lsys, LΔ] using hΔ_encoding A b h_bounded
  have h_contract_real :
      expBase ^ remaining ≤ Real.exp (-(Lε + LΔ : ℝ)) := by
    -- The explicit budget turns the repeated shrink factor into the target exponential gap.
    have h_sys_ge_n : n ≤ Lsys := by
      simp [Lsys]
    have h_remaining' : remaining = 2 * (Lsys + 1) * (Lε + LΔ) := by
      simpa [Lsys, Lε, LΔ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_remaining
    simpa [expBase] using
      (budgetContraction_le_expNeg (n := n) (Lsys := Lsys) (Lsum := Lε + LΔ)
        (remaining := remaining) h_sys_ge_n h_remaining')
  have h_shrink_real : expBase ^ remaining * (Δ A b : ℝ) < (ε A b : ℝ) := by
    -- Multiply the contraction bound by the upper bound on `Δ`, then compare with the lower
    -- barrier for `ε`.
    exact realShrinkGap_of_expBounds h_contract_real hΔ_pos_real hΔ_bounds.2 hε_bounds.1
  have hρ_pow :
      (ρ n) ^ remaining ≤ ENNReal.ofReal (expBase ^ remaining) := by
    -- The pointwise shrink bound propagates through the remaining number of iterations.
    calc
      (ρ n) ^ remaining ≤ (ENNReal.ofReal expBase) ^ remaining := by
        exact pow_le_pow_left' (hρ n) remaining
      _ = ENNReal.ofReal (expBase ^ remaining) := by
        rw [← ENNReal.ofReal_pow]
        positivity
  have h_real_to_enn :
      ENNReal.ofReal (expBase ^ remaining * (Δ A b : ℝ)) <
        ENNReal.ofReal (ε A b : ℝ) := by
    -- Convert the real strict inequality into the `ENNReal` comparison used by the volume bound.
    exact (ENNReal.ofReal_lt_ofReal_iff hε_pos_real).2 h_shrink_real
  calc
    (ρ n) ^ remaining * ENNReal.ofReal (Δ A b : ℝ) ≤
        ENNReal.ofReal (expBase ^ remaining) * ENNReal.ofReal (Δ A b : ℝ) := by
      exact mul_le_mul_of_nonneg_right hρ_pow (by positivity)
    _ = ENNReal.ofReal (expBase ^ remaining * (Δ A b : ℝ)) := by
      rw [← ENNReal.ofReal_mul]
      positivity
    _ < ENNReal.ofReal (ε A b : ℝ) := h_real_to_enn

/-- Helper for Theorem 7.22: a valid `.next` step preserves the invariant that the current
ellipsoid contains the rational polyhedron. -/
private lemma nextStepPreservesInitialization
    (algorithm : UniformEllipsoidAlgorithm)
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℚ} {b : Fin m → ℚ}
    {E₀ E E' : RealEllipsoid n} {i : Fin m}
    (h_init : IsValidEllipsoidInitialization A b E)
    (h_step : (algorithm.run A b E₀).step E = .next i E') :
    IsValidEllipsoidInitialization A b E' := by
  -- Read the `.next` branch of `step_valid` as the cut-update certificate for the chosen row.
  have h_valid := (algorithm.run A b E₀).step_valid E h_init
  rw [h_step] at h_valid
  rcases (show
      (b i : ℝ) < ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ E.center ∧
        IsMinimumVolumeCutUpdate A b i E E' by
      simpa [EllipsoidAlgorithmStep.IsValidAt] using h_valid) with
    ⟨_, h_cutUpdate⟩
  have h_cutSubset :
      E.carrier ∩
          {x : Fin n → ℝ | ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ)} ⊆
        E'.carrier := by
    simpa [IsMinimumVolumeCutUpdate] using h_cutUpdate
  -- Every point in the polyhedron lies in the current carrier and satisfies the chosen cut.
  intro x hx
  have hx_carrier : x ∈ E.carrier := h_init hx
  have hx_system :
      (A.map (Rat.castHom ℝ)) *ᵥ x ≤ fun j ↦ (b j : ℝ) := by
    simpa [mem_rational_matrix_polyhedron] using hx
  have hx_cut : ((A.map (Rat.castHom ℝ)) i) ⬝ᵥ x ≤ (b i : ℝ) := hx_system i
  exact h_cutSubset ⟨hx_carrier, hx_cut⟩

/-- Helper for Theorem 7.22: a valid `.emptyInterior` step is globally correct once the current
ellipsoid still contains the whole rational polyhedron. -/
private lemma emptyInteriorStepIsCorrect
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (E : RealEllipsoid n)
    (h_step :
      (EllipsoidAlgorithmStep.emptyInterior : EllipsoidAlgorithmStep m n).IsValidAt A b E)
    (h_init : IsValidEllipsoidInitialization A b E) :
    (EllipsoidFeasibilityOutput.emptyInterior : EllipsoidFeasibilityOutput n).IsCorrect A b := by
  -- The owner module already proves that a local empty-cut certificate is globally correct.
  exact EllipsoidAlgorithmStep.emptyInterior_isCorrect A b E h_step h_init

/-- Helper for Theorem 7.22: once the remaining shrink budget drives the current valid ellipsoid
below the positive lower-volume threshold, the fuelled run is already correct. -/
private lemma correctOutputFromShrinkBudget
    (algorithm : UniformEllipsoidAlgorithm)
    (ρ : ℕ → ENNReal)
    (ε Δ : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℚ → (Fin m → ℚ) → ℚ)
    (h_shrink : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        ∀ (E₀ E : RealEllipsoid n) (i : Fin m) (E' : RealEllipsoid n),
          (algorithm.run A b E₀).step E = .next i E' →
            volume E'.carrier ≤ ρ n * volume E.carrier)
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b))
    (h_lower : ENNReal.ofReal (ε A b : ℝ) ≤ volume (rational_matrix_polyhedron A b))
    {E₀ E : RealEllipsoid n} {spent remaining : ℕ}
    (h_init : IsValidEllipsoidInitialization A b E)
    (h_vol : volume E.carrier ≤ (ρ n) ^ spent * ENNReal.ofReal (Δ A b : ℝ))
    (h_gap : (ρ n) ^ (spent + remaining) * ENNReal.ofReal (Δ A b : ℝ) <
      ENNReal.ofReal (ε A b : ℝ)) :
    ((algorithm.run A b E₀).runFor (remaining + 1) E).IsCorrect A b := by
  induction remaining generalizing E spent with
  | zero =>
      -- In the zero-remaining case, the current volume bound already contradicts the lower
      -- threshold for `volume P`, so the branch is impossible.
      have h_poly_vol :
          volume (rational_matrix_polyhedron A b) ≤ volume E.carrier := measure_mono h_init
      have h_current_gap : volume E.carrier < ENNReal.ofReal (ε A b : ℝ) := by
        exact lt_of_le_of_lt h_vol (by simpa using h_gap)
      have h_poly_gap : volume (rational_matrix_polyhedron A b) < ENNReal.ofReal (ε A b : ℝ) :=
        lt_of_le_of_lt h_poly_vol h_current_gap
      exact False.elim ((not_lt_of_ge h_lower) h_poly_gap)
  | succ remaining ih =>
      -- Inspect the operational step and discharge each branch with the corresponding API lemma.
      cases h_step : (algorithm.run A b E₀).step E with
      | feasiblePoint x =>
          have h_valid := (algorithm.run A b E₀).step_valid E h_init
          rw [h_step] at h_valid
          rcases (show x = E.center ∧ x ∈ rational_matrix_polyhedron A b by
              simpa [EllipsoidAlgorithmStep.IsValidAt] using h_valid) with
            ⟨_, hx_mem⟩
          simpa [EllipsoidAlgorithm.runFor, h_step,
            EllipsoidFeasibilityOutput.IsCorrect] using hx_mem
      | emptyInterior =>
          have h_valid := (algorithm.run A b E₀).step_valid E h_init
          rw [h_step] at h_valid
          have h_correct :
              (EllipsoidFeasibilityOutput.emptyInterior :
                EllipsoidFeasibilityOutput n).IsCorrect A b :=
            emptyInteriorStepIsCorrect A b E
              (by simpa [EllipsoidAlgorithmStep.IsValidAt] using h_valid) h_init
          simpa [EllipsoidAlgorithm.runFor, h_step] using h_correct
      | next i E' =>
          have h_init' : IsValidEllipsoidInitialization A b E' :=
            nextStepPreservesInitialization algorithm h_init h_step
          have h_next_vol :
              volume E'.carrier ≤
                (ρ n) ^ (spent + 1) * ENNReal.ofReal (Δ A b : ℝ) := by
            -- One more `.next` step multiplies the current upper volume bound by the shrink factor.
            calc
              volume E'.carrier ≤ ρ n * volume E.carrier := by
                exact h_shrink A b h_bounded E₀ E i E' h_step
              _ ≤ ρ n * ((ρ n) ^ spent * ENNReal.ofReal (Δ A b : ℝ)) := by
                exact mul_le_mul_of_nonneg_left h_vol (by positivity)
              _ = (ρ n) ^ (spent + 1) * ENNReal.ofReal (Δ A b : ℝ) := by
                simp [pow_succ, mul_assoc, mul_comm]
          have h_gap' :
              (ρ n) ^ ((spent + 1) + remaining) * ENNReal.ofReal (Δ A b : ℝ) <
                ENNReal.ofReal (ε A b : ℝ) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h_gap
          have h_recursive :=
            ih (spent := spent + 1) (E := E') h_init' h_next_vol h_gap'
          simpa [EllipsoidAlgorithm.runFor, h_step] using h_recursive

/-- Helper for Theorem 7.22: the encoding-size bounds on `ε` and `Δ` produce a polynomially
bounded shrink budget that drives the initial volume upper bound below the positive lower-volume
threshold. -/
private lemma existsEncodedShrinkBudget
    (ρ : ℕ → ENNReal)
    (ε Δ : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℚ → (Fin m → ℚ) → ℚ)
    (πLower πUpper : Polynomial ℕ)
    (hρ : ∀ n : ℕ,
      ρ n ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * (n : ℝ) + 2)))))
    (hε_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < ε A b)
    (hΔ_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < Δ A b)
    (hε_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (ε A b) ≤
          πLower.eval (n + rational_linear_system_encoding_size A b))
    (hΔ_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (Δ A b) ≤
          πUpper.eval (n + rational_linear_system_encoding_size A b))
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h_bounded : Bornology.IsBounded (rational_matrix_polyhedron A b)) :
    ∃ remaining : ℕ,
      (ρ n) ^ remaining * ENNReal.ofReal (Δ A b : ℝ) <
        ENNReal.ofReal (ε A b : ℝ) ∧
      remaining + 1 ≤ (cutoffPolynomial πLower πUpper).eval
        (n + rational_linear_system_encoding_size A b) := by
  let Lsys := n + rational_linear_system_encoding_size A b
  let remaining :=
    2 * (Lsys + 1) * (πLower.eval Lsys + πUpper.eval Lsys)
  refine ⟨remaining, ?_, ?_⟩
  · -- The explicit budget is exactly the shrink-gap budget proved in the numeric helper.
    refine shrinkGap_of_encodingBounds ρ ε Δ πLower πUpper hρ hε_pos hΔ_pos
      hε_encoding hΔ_encoding A b h_bounded remaining ?_
    simp [remaining, Lsys, Nat.add_left_comm, Nat.add_comm]
  · -- Evaluating the witness polynomial reproduces `remaining + 1`.
    simp [cutoffPolynomial, remaining, Lsys, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc]

/-- Theorem 7.22. For the ellipsoid algorithm, initial ellipsoids and
cutoffs can be chosen so that every bounded rational polyhedron receives a correct output after
polynomially many iterations. The polynomial bound follows from the standard contraction rate
and polynomially encoded positive lower and upper volume bounds. -/
theorem existsCorrectOutputByPolynomialBound
    (algorithm : UniformEllipsoidAlgorithm)
    (ρ : ℕ → ENNReal)
    (ε Δ : ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) ℚ → (Fin m → ℚ) → ℚ)
    (πLower πUpper : Polynomial ℕ)
    (hρ : ∀ n : ℕ,
      ρ n ≤ ENNReal.ofReal (Real.exp (-(1 / (2 * (n : ℝ) + 2)))))
    (h_initial : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        ∃ E₀ : RealEllipsoid n,
          IsValidEllipsoidInitialization A b E₀ ∧
            volume E₀.carrier ≤ ENNReal.ofReal (Δ A b : ℝ))
    (h_shrink : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        ∀ (E₀ E : RealEllipsoid n) (i : Fin m) (E' : RealEllipsoid n),
          (algorithm.run A b E₀).step E = .next i E' →
            volume E'.carrier ≤ ρ n * volume E.carrier)
    (hε_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < ε A b)
    (hΔ_pos : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) → 0 < Δ A b)
    (h_volumeLower : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        interior (rational_matrix_polyhedron A b) = ∅ ∨
          ENNReal.ofReal (ε A b : ℝ) ≤ volume (rational_matrix_polyhedron A b))
    (hε_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (ε A b) ≤
          πLower.eval (n + rational_linear_system_encoding_size A b))
    (hΔ_encoding : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      Bornology.IsBounded (rational_matrix_polyhedron A b) →
        EncodingSize.rational (Δ A b) ≤
          πUpper.eval (n + rational_linear_system_encoding_size A b)) :
    ∃ π : Polynomial ℕ, algorithm.PolynomialCutoffBound π := by
  refine ⟨cutoffPolynomial πLower πUpper, ?_⟩
  intro m n A b h_bounded
  rcases h_initial A b h_bounded with ⟨E₀, h_init₀, h_vol₀⟩
  rcases h_volumeLower A b h_bounded with h_emptyInterior | h_lower
  · -- If the polyhedron already has empty interior, cutoff `0` is immediately correct.
    refine ⟨CutoffCertificate.ofData E₀ 0 h_init₀ ?_, ?_⟩
    · simp [EllipsoidAlgorithm.correctOutputBy, EllipsoidAlgorithm.runFor,
        EllipsoidFeasibilityOutput.IsCorrect, h_emptyInterior]
    · simp [CutoffCertificate.ofData, cutoffPolynomial]
  · rcases existsEncodedShrinkBudget ρ ε Δ πLower πUpper hρ hε_pos hΔ_pos
        hε_encoding hΔ_encoding A b h_bounded with ⟨remaining, h_gap, h_bound⟩
    refine ⟨CutoffCertificate.ofData E₀ (remaining + 1) h_init₀ ?_, h_bound⟩
    -- Starting from the initial ellipsoid, the shrink-budget lemma gives correctness by the
    -- packaged polynomial cutoff.
    have h_start_vol :
        volume E₀.carrier ≤ (ρ n) ^ 0 * ENNReal.ofReal (Δ A b : ℝ) := by
      simpa using h_vol₀
    have h_gap0 :
        (ρ n) ^ (0 + remaining) * ENNReal.ofReal (Δ A b : ℝ) <
          ENNReal.ofReal (ε A b : ℝ) := by
      simpa using h_gap
    simpa [EllipsoidAlgorithm.correctOutputBy] using
      correctOutputFromShrinkBudget algorithm ρ ε Δ h_shrink A b h_bounded h_lower
        (E₀ := E₀) (E := E₀) (spent := 0) (remaining := remaining)
        h_init₀ h_start_vol h_gap0

end UniformEllipsoidAlgorithm

/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section01

section Chap02
section Section02

/-- Lemma 2.2.1 (Squeeze lemma): If real sequences `a`, `x`, `b` satisfy
`a n ≤ x n ≤ b n` for every `n`, and both `a` and `b` converge to the same
limit `l`, then `x` also converges to `l`, so
`lim_{n → ∞} x_n = lim_{n → ∞} a_n = lim_{n → ∞} b_n`. -/
lemma squeeze_converges {a b x : RealSequence} {l : ℝ}
    (hax : ∀ n : ℕ, a n ≤ x n) (hxb : ∀ n : ℕ, x n ≤ b n)
    (ha : ConvergesTo a l) (hb : ConvergesTo b l) :
    ConvergesTo x l := by
  intro ε hε
  rcases ha ε hε with ⟨M₁, hM₁⟩
  rcases hb ε hε with ⟨M₂, hM₂⟩
  refine ⟨max M₁ M₂, ?_⟩
  intro n hn
  have hge₁ : n ≥ M₁ := le_trans (Nat.le_max_left _ _) hn
  have hge₂ : n ≥ M₂ := le_trans (Nat.le_max_right _ _) hn
  have hha := hM₁ n hge₁
  have hhb := hM₂ n hge₂
  have hha_bounds : -ε < a n - l ∧ a n - l < ε := abs_lt.mp hha
  have hhb_bounds : -ε < b n - l ∧ b n - l < ε := abs_lt.mp hhb
  have h_lower_x : l - ε < x n := by
    have h_lower_a : l - ε < a n := by linarith [hha_bounds.1]
    exact lt_of_lt_of_le h_lower_a (hax n)
  have h_upper_x : x n < l + ε := by
    have h_upper_b : b n < l + ε := by linarith [hhb_bounds.2]
    exact lt_of_le_of_lt (hxb n) h_upper_b
  have h_lower : -ε < x n - l := by linarith
  have h_upper : x n - l < ε := by linarith
  exact abs_lt.mpr ⟨h_lower, h_upper⟩

/-- A sequence squeezed between two convergent sequences with common limit is
itself convergent with that limit. -/
lemma squeeze_convergentSequence {a b x : RealSequence} {l : ℝ}
    (hax : ∀ n : ℕ, a n ≤ x n) (hxb : ∀ n : ℕ, x n ≤ b n)
    (ha : ConvergesTo a l) (hb : ConvergesTo b l) :
    ConvergentSequence x :=
  ⟨l, squeeze_converges (a := a) (b := b) (x := x) (l := l) hax hxb ha hb⟩

/-- Example 2.2.2: By bounding `1 / (n √n)` (starting at `n = 1`) between the
constant `0` sequence and `1 / n`, and using the squeeze lemma together with
`lim_{n → ∞} 1 / n = 0`, we conclude `lim_{n → ∞} 1 / (n √n) = 0`. -/
lemma inv_mul_sqrt_bounds :
    ∀ n : ℕ,
      0 ≤ (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1)) ∧
        (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1)) ≤ (1 : ℝ) / (n + 1) := by
  intro n
  have hpos_nat : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hden_pos :
      0 < (n + 1 : ℝ) * Real.sqrt (n + 1) :=
    mul_pos hpos_nat (Real.sqrt_pos.mpr hpos_nat)
  have h_nonneg :
      0 ≤ (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1)) :=
    le_of_lt (one_div_pos.mpr hden_pos)
  have h_one_le_nat : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have h_one_le : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast h_one_le_nat
  have h_sqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
    have hmono : Real.sqrt (1 : ℝ) ≤ Real.sqrt (n + 1) :=
      Real.sqrt_le_sqrt h_one_le
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (n + 1) := hmono
  have hle : (n + 1 : ℝ) ≤ (n + 1 : ℝ) * Real.sqrt (n + 1) := by
    nlinarith
  have h_upper :
      (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1)) ≤ (1 : ℝ) / (n + 1) :=
    one_div_le_one_div_of_le hpos_nat hle
  exact ⟨h_nonneg, h_upper⟩

lemma inv_mul_sqrt_converges_to_zero :
    ConvergesTo
      (fun n : ℕ =>
        (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1))) 0 := by
  refine
    squeeze_converges
      (a := fun _ : ℕ => (0 : ℝ))
      (b := fun n : ℕ => (1 : ℝ) / (n + 1))
      (x :=
        fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) * Real.sqrt (n + 1))) (l := 0)
      ?hax ?hxb ?ha ?hb
  · intro n
    exact (inv_mul_sqrt_bounds n).1
  · intro n
    exact (inv_mul_sqrt_bounds n).2
  · simpa using (constant_seq_converges (0 : ℝ))
  · simpa using inv_nat_converges_to_zero

/-- Lemma 2.2.3: If convergent real sequences `x` and `y` satisfy
`x n ≤ y n` for every `n`, then their limits obey
`lim_{n → ∞} x_n ≤ lim_{n → ∞} y_n`. -/
lemma limit_le_of_pointwise_le {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m)
    (hxy : ∀ n : ℕ, x n ≤ y n) :
    l ≤ m := by
  classical
  by_contra hle
  have hlt : m < l := lt_of_not_ge hle
  have hpos : 0 < l - m := sub_pos.mpr hlt
  -- work with `ε = (l - m) / 2` and use `ε / 2` in the convergence bounds
  set ε : ℝ := (l - m) / 2 with hεdef
  have hεpos : 0 < ε := by linarith
  have hε2pos : 0 < ε / 2 := by linarith
  rcases hx (ε / 2) hε2pos with ⟨M₁, hM₁⟩
  rcases hy (ε / 2) hε2pos with ⟨M₂, hM₂⟩
  let M := max M₁ M₂
  have hxM : |x M - l| < ε / 2 := hM₁ M (Nat.le_max_left _ _)
  have hyM : |y M - m| < ε / 2 := hM₂ M (Nat.le_max_right _ _)
  have hx_lower : l - ε / 2 < x M := by
    have hx_bounds := abs_lt.mp hxM
    linarith
  have hy_upper : y M < m + ε / 2 := by
    have hy_bounds := abs_lt.mp hyM
    linarith
  have hxyM : x M ≤ y M := hxy M
  have hlt' : l - m < ε := by
    have hmid : l - ε / 2 < y M := lt_of_lt_of_le hx_lower hxyM
    have hfin : l - ε / 2 < m + ε / 2 := lt_trans hmid hy_upper
    linarith
  have hge : ε ≤ l - m := by linarith [hpos, hεdef]
  have hcontra : ¬ l - m < ε := not_lt_of_ge hge
  exact hcontra hlt'

/-- A convergent sequence with pointwise nonnegative terms has a nonnegative limit. -/
lemma limit_nonneg_of_pointwise_nonneg {x : RealSequence} {l : ℝ}
    (hx : ConvergesTo x l) (h_nonneg : ∀ n : ℕ, 0 ≤ x n) : 0 ≤ l := by
  have h :=
    limit_le_of_pointwise_le
      (x := fun _ : ℕ => (0 : ℝ))
      (y := x)
      (l := 0)
      (m := l)
      (constant_seq_converges (0 : ℝ))
      hx
      (by
        intro n
        simpa using h_nonneg n)
  simpa using h

/-- A pointwise lower bound for a convergent sequence bounds its limit below. -/
lemma limit_lower_bound_of_pointwise {x : RealSequence} {a l : ℝ}
    (hx : ConvergesTo x l) (hax : ∀ n : ℕ, a ≤ x n) : a ≤ l := by
  have h :=
    limit_le_of_pointwise_le
      (x := fun _ : ℕ => a)
      (y := x)
      (l := a)
      (m := l)
      (constant_seq_converges a)
      hx
      (by
        intro n
        simpa using hax n)
  simpa using h

/-- A pointwise upper bound for a convergent sequence bounds its limit above. -/
lemma limit_upper_bound_of_pointwise {x : RealSequence} {b l : ℝ}
    (hx : ConvergesTo x l) (hxb : ∀ n : ℕ, x n ≤ b) : l ≤ b := by
  have h :=
    limit_le_of_pointwise_le
      (x := x)
      (y := fun _ : ℕ => b)
      (l := l)
      (m := b)
      hx
      (constant_seq_converges b)
      (by
        intro n
        simpa using hxb n)
  simpa using h

/-- Corollary 2.2.4: (i) If a convergent real sequence has nonnegative terms,
then its limit is nonnegative. (ii) If a convergent real sequence is bounded
between real numbers `a` and `b`, then its limit also lies between `a` and
`b`. -/
lemma limit_nonneg_and_between_bounds :
    (∀ {x : RealSequence} {l : ℝ},
        ConvergesTo x l → (∀ n : ℕ, 0 ≤ x n) → 0 ≤ l) ∧
      (∀ {x : RealSequence} {a b l : ℝ},
        ConvergesTo x l → (∀ n : ℕ, a ≤ x n) → (∀ n : ℕ, x n ≤ b) →
          a ≤ l ∧ l ≤ b) := by
  constructor
  · intro x l hx h_nonneg
    exact limit_nonneg_of_pointwise_nonneg hx h_nonneg
  · intro x a b l hx hax hxb
    refine ⟨?_, ?_⟩
    · exact limit_lower_bound_of_pointwise hx hax
    · exact limit_upper_bound_of_pointwise hx hxb

/-- Proposition 2.2.5: For convergent real sequences `x` and `y`, the usual
algebraic operations preserve convergence. (i) The sum sequence converges to
the sum of the limits. (ii) The difference sequence converges to the
difference of the limits. (iii) The termwise product converges to the product
of the limits. (iv) If `lim_{n → ∞} y_n ≠ 0` and every `y n ≠ 0`, then the
quotient sequence converges to the quotient of the limits. -/
lemma limit_add_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n + y n) (l + m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.add hy'
  exact (convergesTo_iff_tendsto (fun n : ℕ => x n + y n) (l + m)).2 h

/-- The limit of the difference of two convergent real sequences is the
difference of their limits. -/
lemma limit_sub_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n - y n) (l - m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.sub hy'
  simpa [sub_eq_add_neg] using
    (convergesTo_iff_tendsto (fun n : ℕ => x n - y n) (l - m)).2 h

/-- The limit of the termwise product of two convergent real sequences is the
product of their limits. -/
lemma limit_mul_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) :
    ConvergesTo (fun n : ℕ => x n * y n) (l * m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have h := hx'.mul hy'
  exact (convergesTo_iff_tendsto (fun n : ℕ => x n * y n) (l * m)).2 h

/-- If a convergent real sequence `y` has nonzero limit and no zero terms,
then the termwise quotient of convergent sequences `x` and `y` converges to
the quotient of their limits. -/
lemma limit_div_of_convergent {x y : RealSequence} {l m : ℝ}
    (hx : ConvergesTo x l) (hy : ConvergesTo y m) (hm : m ≠ 0)
    (hy_ne_zero : ∀ n : ℕ, y n ≠ 0) :
    ConvergesTo (fun n : ℕ => x n / y n) (l / m) := by
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have hy' := (convergesTo_iff_tendsto y m).1 hy
  have hy_ne_zero_eventually :
      ∀ᶠ n in Filter.atTop, y n ≠ 0 :=
    Filter.Eventually.of_forall hy_ne_zero
  have h_inv :
      Filter.Tendsto (fun n : ℕ => (y n)⁻¹) Filter.atTop (nhds (m⁻¹)) :=
    hy'.inv₀ hm
  have h := hx'.mul h_inv
  have h_div :
      Filter.Tendsto (fun n : ℕ => x n / y n) Filter.atTop (nhds (l / m)) :=
    by
      simpa [div_eq_mul_inv] using h
  exact (convergesTo_iff_tendsto (fun n : ℕ => x n / y n) (l / m)).2 h_div

/-- Proposition 2.2.6: If a convergent real sequence satisfies `x n ≥ 0` for
every `n`, then its termwise square roots converge to the square root of its
limit, i.e. `lim_{n → ∞} √(x_n) = √(lim_{n → ∞} x_n)`. -/
lemma limit_sqrt_of_nonneg {x : RealSequence} {l : ℝ}
    (hx : ConvergesTo x l) (h_nonneg : ∀ n : ℕ, 0 ≤ x n) :
    ConvergesTo (fun n : ℕ => Real.sqrt (x n)) (Real.sqrt l) := by
  have hx_nonneg : ∀ n : ℕ, 0 ≤ x n := h_nonneg
  -- use continuity of `Real.sqrt`
  have hx' := (convergesTo_iff_tendsto x l).1 hx
  have h := (Real.continuous_sqrt.tendsto l).comp hx'
  exact
    (convergesTo_iff_tendsto
        (fun n : ℕ => Real.sqrt (x n)) (Real.sqrt l)).2 h

/-- Proposition 2.2.7: If a real sequence `x` converges, then its termwise
absolute values also converge, and the limit is the absolute value of the
original limit, so `lim_{n → ∞} |x_n| = |lim_{n → ∞} x_n|`. -/
lemma limit_abs_of_convergent {x : RealSequence} {l : ℝ}
    (hx : ConvergesTo x l) :
    ConvergesTo (fun n : ℕ => |x n|) |l| := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hineq : abs (abs (x n) - abs l) ≤ abs (x n - l) :=
    abs_abs_sub_abs_le_abs_sub (x n) l
  exact lt_of_le_of_lt hineq (hN n hn)

/-- The absolute value of a convergent real sequence is also convergent. -/
lemma abs_convergentSequence {x : RealSequence}
    (hx : ConvergentSequence x) :
    ConvergentSequence (fun n : ℕ => |x n|) := by
  rcases hx with ⟨l, hl⟩
  exact ⟨|l|, limit_abs_of_convergent hl⟩

/-- Example 2.2.8: Starting from `x₁ = 2` and defining
`x_{n+1} = x_n - (x_n^2 - 2) / (2 x_n)`, the recursion is well-defined because
each term stays positive. The sequence is monotone decreasing and bounded
below, so it converges; taking limits in the recurrence gives `x = √2`, so
the limit equals `√2`. -/
noncomputable def sqrtTwoNewtonSequence : RealSequence :=
  fun n =>
    Nat.recOn n (2 : ℝ)
      (fun _ x_n => x_n - (x_n ^ 2 - 2) / (2 * x_n))

/-- Every term of the Newton sequence for `√2` is positive, so the recurrence
is well-defined. -/
lemma sqrtTwoNewtonSequence_pos : ∀ n : ℕ, 0 < sqrtTwoNewtonSequence n := by
  intro n
  induction' n with n ih
  · norm_num [sqrtTwoNewtonSequence]
  · have hrec :
        sqrtTwoNewtonSequence (n + 1) =
          sqrtTwoNewtonSequence n -
            ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
              (2 * sqrtTwoNewtonSequence n) := by
        simp [sqrtTwoNewtonSequence]
    have hden_pos : 0 < 2 * sqrtTwoNewtonSequence n := by
      have hpos := ih
      nlinarith
    have hnum_pos :
        0 < (sqrtTwoNewtonSequence n) ^ 2 + 2 := by nlinarith
    have hrewrite :
        sqrtTwoNewtonSequence (n + 1) =
          ((sqrtTwoNewtonSequence n) ^ 2 + 2) /
            (2 * sqrtTwoNewtonSequence n) := by
      have hne : (2 * sqrtTwoNewtonSequence n) ≠ 0 := by nlinarith
      calc
        sqrtTwoNewtonSequence (n + 1)
            = sqrtTwoNewtonSequence n -
                ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                  (2 * sqrtTwoNewtonSequence n) := hrec
        _ = ((sqrtTwoNewtonSequence n) ^ 2 + 2) /
              (2 * sqrtTwoNewtonSequence n) := by
              field_simp [hne]
              ring
    have hpos :
        0 <
          ((sqrtTwoNewtonSequence n) ^ 2 + 2) /
            (2 * sqrtTwoNewtonSequence n) :=
      div_pos hnum_pos hden_pos
    simpa [hrewrite]
      using hpos

/-- For every `n`, `(x_n)^2 - 2` is nonnegative along the Newton sequence. -/
lemma sqrtTwoNewtonSequence_sq_sub_two_nonneg :
    ∀ n : ℕ, 0 ≤ (sqrtTwoNewtonSequence n) ^ 2 - 2 := by
  intro n
  induction' n with n ih
  · norm_num [sqrtTwoNewtonSequence]
  · have hpos : 0 < sqrtTwoNewtonSequence n :=
      sqrtTwoNewtonSequence_pos n
    have hden_pos : 0 < 4 * (sqrtTwoNewtonSequence n) ^ 2 := by nlinarith
    have hrewrite :
        sqrtTwoNewtonSequence (n + 1) =
          ((sqrtTwoNewtonSequence n) ^ 2 + 2) /
            (2 * sqrtTwoNewtonSequence n) := by
      have hne : (2 * sqrtTwoNewtonSequence n) ≠ 0 := by nlinarith
      calc
        sqrtTwoNewtonSequence (n + 1)
            = sqrtTwoNewtonSequence n -
                ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                  (2 * sqrtTwoNewtonSequence n) := by
                  simp [sqrtTwoNewtonSequence]
        _ = ((sqrtTwoNewtonSequence n) ^ 2 + 2) /
              (2 * sqrtTwoNewtonSequence n) := by
              field_simp [hne]
              ring
    have hsq :
        (sqrtTwoNewtonSequence (n + 1)) ^ 2 - 2 =
          ((sqrtTwoNewtonSequence n) ^ 2 - 2) ^ 2 /
            (4 * (sqrtTwoNewtonSequence n) ^ 2) := by
      have hne : (4 * (sqrtTwoNewtonSequence n) ^ 2) ≠ 0 := by nlinarith
      calc
        (sqrtTwoNewtonSequence (n + 1)) ^ 2 - 2
            = (((sqrtTwoNewtonSequence n) ^ 2 + 2) /
                (2 * sqrtTwoNewtonSequence n)) ^ 2 - 2 := by
                simp [hrewrite]
        _ = (((sqrtTwoNewtonSequence n) ^ 2 + 2) ^ 2) /
              (4 * (sqrtTwoNewtonSequence n) ^ 2) - 2 := by ring
        _ =
            ((sqrtTwoNewtonSequence n) ^ 2 - 2) ^ 2 /
              (4 * (sqrtTwoNewtonSequence n) ^ 2) := by
              field_simp [hne]
              ring
    have hnum_nonneg :
        0 ≤ ((sqrtTwoNewtonSequence n) ^ 2 - 2) ^ 2 := by nlinarith
    have hfrac_nonneg :
        0 ≤
          ((sqrtTwoNewtonSequence n) ^ 2 - 2) ^ 2 /
            (4 * (sqrtTwoNewtonSequence n) ^ 2) :=
      div_nonneg hnum_nonneg hden_pos.le
    simpa [hsq]
      using hfrac_nonneg

/-- The Newton sequence for `√2` is monotone decreasing. -/
lemma sqrtTwoNewtonSequence_monotone :
    MonotoneDecreasingSequence sqrtTwoNewtonSequence := by
  intro n
  have hpos : 0 < sqrtTwoNewtonSequence n := sqrtTwoNewtonSequence_pos n
  have hnonneg :
      0 ≤ (sqrtTwoNewtonSequence n) ^ 2 - 2 :=
    sqrtTwoNewtonSequence_sq_sub_two_nonneg n
  have hrec :
      sqrtTwoNewtonSequence (n + 1) =
        sqrtTwoNewtonSequence n -
          ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
            (2 * sqrtTwoNewtonSequence n) := by
    simp [sqrtTwoNewtonSequence]
  have hden_pos : 0 < 2 * sqrtTwoNewtonSequence n := by nlinarith
  have hfrac_nonneg :
      0 ≤
        ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
          (2 * sqrtTwoNewtonSequence n) :=
    div_nonneg hnonneg hden_pos.le
  have hle :
      sqrtTwoNewtonSequence (n + 1) ≤ sqrtTwoNewtonSequence n := by
    have := hrec
    linarith
  simpa [Nat.add_comm] using hle

/-- The Newton sequence for `√2` converges to `√2`. -/
lemma sqrtTwoNewtonSequence_tendsto :
    ConvergesTo sqrtTwoNewtonSequence (Real.sqrt 2) := by
  classical
  have hmono : MonotoneDecreasingSequence sqrtTwoNewtonSequence :=
    sqrtTwoNewtonSequence_monotone
  have hnonneg : ∀ n, 0 ≤ sqrtTwoNewtonSequence n :=
    fun n => (sqrtTwoNewtonSequence_pos n).le
  have hanti :
      Antitone sqrtTwoNewtonSequence :=
    (monotoneDecreasingSequence_iff_antitone
        sqrtTwoNewtonSequence).1 hmono
  have hbound : BoundedSequence sqrtTwoNewtonSequence := by
    refine ⟨2, ?_⟩
    intro n
    have hle :
        sqrtTwoNewtonSequence n ≤ sqrtTwoNewtonSequence 0 :=
      hanti (Nat.zero_le n)
    have hzero : sqrtTwoNewtonSequence 0 = 2 := by
      simp [sqrtTwoNewtonSequence]
    have hle' : sqrtTwoNewtonSequence n ≤ 2 := by simpa [hzero] using hle
    have hpos' : |sqrtTwoNewtonSequence n| = sqrtTwoNewtonSequence n :=
      abs_of_nonneg (hnonneg n)
    simpa [hpos'] using hle'
  have hmono_seq : MonotoneSequence sqrtTwoNewtonSequence :=
    Or.inr hmono
  have hconv_seq : ConvergentSequence sqrtTwoNewtonSequence :=
    (monotone_sequence_bounded_iff_convergent
        (x := sqrtTwoNewtonSequence) hmono_seq).1 hbound
  rcases hconv_seq with ⟨l, hl⟩
  have htail :
      ConvergesTo (fun n => sqrtTwoNewtonSequence (n + 1)) l := by
    simpa [sequenceTail] using
      (convergesTo_tail_of_converges (x := sqrtTwoNewtonSequence) (K := 0) hl)
  have hmul :
      ConvergesTo
        (fun n =>
          sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1))
        (l * l) :=
    limit_mul_of_convergent hl htail
  have hconst2 : ConvergesTo (fun _ : ℕ => (2 : ℝ)) 2 :=
    constant_seq_converges 2
  have hmul2 :
      ConvergesTo
        (fun n =>
          2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1))
        (2 * (l * l)) := by
    have :=
      limit_mul_of_convergent (x := fun _ : ℕ => (2 : ℝ))
        (y := fun n =>
          sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1))
        (l := 2) (m := l * l) hconst2 hmul
    simpa [mul_left_comm, mul_comm, mul_assoc] using this
  have hsq_conv :
      ConvergesTo
        (fun n =>
          sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence n)
        (l * l) :=
    limit_mul_of_convergent hl hl
  have hsq_add :
      ConvergesTo
        (fun n =>
          sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence n + 2)
        (l * l + 2) :=
    limit_add_of_convergent hsq_conv hconst2
  have hrec :
      ∀ n : ℕ,
        2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1) =
          (sqrtTwoNewtonSequence n) ^ 2 + 2 := by
    intro n
    have hne : (2 * sqrtTwoNewtonSequence n) ≠ 0 := by
      have hpos := sqrtTwoNewtonSequence_pos n
      nlinarith
    have hrec' :
        sqrtTwoNewtonSequence (n + 1) =
          sqrtTwoNewtonSequence n -
            ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
              (2 * sqrtTwoNewtonSequence n) := by
      simp [sqrtTwoNewtonSequence]
    calc
      2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1)
          = 2 * sqrtTwoNewtonSequence n *
              (sqrtTwoNewtonSequence n -
                ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                  (2 * sqrtTwoNewtonSequence n)) := by
                simp [hrec']
      _ = (sqrtTwoNewtonSequence n) ^ 2 + 2 := by
        have hxne : sqrtTwoNewtonSequence n ≠ 0 := by
          intro hx
          apply hne
          nlinarith [hx]
        have hmul_div :
            2 * sqrtTwoNewtonSequence n *
                (((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                  (2 * sqrtTwoNewtonSequence n)) =
              (sqrtTwoNewtonSequence n) ^ 2 - 2 := by
          field_simp [hxne]
        have hcalc :
            2 * sqrtTwoNewtonSequence n *
                (sqrtTwoNewtonSequence n -
                  ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                    (2 * sqrtTwoNewtonSequence n)) =
              (sqrtTwoNewtonSequence n) ^ 2 + 2 := by
          calc
            2 * sqrtTwoNewtonSequence n *
                (sqrtTwoNewtonSequence n -
                  ((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                    (2 * sqrtTwoNewtonSequence n)) =
                2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence n -
                  2 * sqrtTwoNewtonSequence n *
                    (((sqrtTwoNewtonSequence n) ^ 2 - 2) /
                      (2 * sqrtTwoNewtonSequence n)) := by ring
            _ =
                2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence n -
                  ((sqrtTwoNewtonSequence n) ^ 2 - 2) := by
                simpa using hmul_div
            _ = (sqrtTwoNewtonSequence n) ^ 2 + 2 := by ring
        simpa using hcalc
  have hsq_add' :
      ConvergesTo
        (fun n => (sqrtTwoNewtonSequence n) ^ 2 + 2)
        (l * l + 2) := by
    simpa [pow_two] using hsq_add
  have hfun_eq :
      (fun n =>
        2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1)) =
        fun n => (sqrtTwoNewtonSequence n) ^ 2 + 2 := by
    funext n
    simpa [pow_two] using hrec n
  have hright :
      ConvergesTo
        (fun n =>
          2 * sqrtTwoNewtonSequence n * sqrtTwoNewtonSequence (n + 1))
        (l * l + 2) := by
    simpa [hfun_eq] using hsq_add'
  have hlimit_eq : 2 * (l * l) = l * l + 2 :=
    convergesTo_unique hmul2 hright
  have hsq : l ^ 2 = 2 := by
    have hsq' : l * l = 2 := by nlinarith
    simpa [pow_two] using hsq'
  have hl_nonneg : 0 ≤ l :=
    limit_le_of_pointwise_le (x := fun _ => (0 : ℝ))
      (y := sqrtTwoNewtonSequence) (l := 0) (m := l)
      (by simpa using (constant_seq_converges (0 : ℝ))) hl
      (by intro n; exact hnonneg n)
  have habs : |l| = Real.sqrt 2 := by
    have := congrArg Real.sqrt hsq
    simpa [Real.sqrt_sq_eq_abs] using this
  have hpos_abs : |l| = l := abs_of_nonneg hl_nonneg
  have hfinal : l = Real.sqrt 2 := by
    linarith
  simpa [hfinal] using hl

/-- The Newton sequence for `√2` stays positive, decreases monotonically, and
converges to `√2`. -/
lemma sqrtTwoNewtonSequence_converges :
    (∀ n : ℕ, 0 < sqrtTwoNewtonSequence n) ∧
      MonotoneDecreasingSequence sqrtTwoNewtonSequence ∧
        ConvergesTo sqrtTwoNewtonSequence (Real.sqrt 2) := by
  exact
    ⟨sqrtTwoNewtonSequence_pos, sqrtTwoNewtonSequence_monotone,
      sqrtTwoNewtonSequence_tendsto⟩

/-- Example 2.2.9: For the recursion `x_{n+1} = x_n^2 + x_n`, starting at
`x₁ = 1` yields an unbounded sequence and hence no limit, while starting at
`x₁ = 0` gives the constant zero sequence whose limit is `0`. The long-term
behavior therefore depends on the initial value. -/
def quadraticRecursiveSequence (x₁ : ℝ) : RealSequence :=
  fun n => Nat.recOn n x₁ (fun _ x_n => x_n ^ 2 + x_n)

/-- Lower bound for the quadratic recursion started at `1`. -/
lemma quadraticRecursiveSequence_one_lower_bound :
    ∀ n : ℕ, quadraticRecursiveSequence 1 n ≥ (n : ℝ) + 1 := by
  intro n
  induction' n with n ih
  · norm_num [quadraticRecursiveSequence]
  · have hrec :
        quadraticRecursiveSequence 1 (n + 1) =
          quadraticRecursiveSequence 1 n ^ 2 +
            quadraticRecursiveSequence 1 n := by
        simp [quadraticRecursiveSequence]
    have hge_one : (1 : ℝ) ≤ quadraticRecursiveSequence 1 n := by
      linarith [ih]
    have hstep :
        quadraticRecursiveSequence 1 (n + 1) ≥
          quadraticRecursiveSequence 1 n + 1 := by
      have hcalc :
          quadraticRecursiveSequence 1 n ^ 2 +
              quadraticRecursiveSequence 1 n ≥
            quadraticRecursiveSequence 1 n + 1 := by
        nlinarith [hge_one]
      simpa [hrec] using hcalc
    have hbound :
        quadraticRecursiveSequence 1 (n + 1) ≥ (n : ℝ) + 1 + 1 := by
      linarith [hstep, ih]
    simpa [Nat.cast_succ, add_assoc] using hbound

/-- With initial value `1`, the quadratic recursion grows without bound. -/
lemma quadraticRecursiveSequence_unbounded :
    ¬ BoundedSequence (quadraticRecursiveSequence 1) := by
  intro hB
  rcases hB with ⟨B, hB⟩
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have hlower := quadraticRecursiveSequence_one_lower_bound N
  have hnonneg : 0 ≤ quadraticRecursiveSequence 1 N := by linarith [hlower]
  have habsle : |quadraticRecursiveSequence 1 N| ≤ B := hB N
  have hle : quadraticRecursiveSequence 1 N ≤ B := by
    have hrewrite :
        |quadraticRecursiveSequence 1 N| =
          quadraticRecursiveSequence 1 N :=
      abs_of_nonneg hnonneg
    simpa [hrewrite] using habsle
  have hB_lt : (B : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlt : B < quadraticRecursiveSequence 1 N := by
    linarith [hlower, hB_lt]
  linarith

/-- The quadratic recursion started at `1` does not converge. -/
lemma quadraticRecursiveSequence_diverges :
    ¬ ConvergentSequence (quadraticRecursiveSequence 1) := by
  intro hconv
  have hbounded : BoundedSequence (quadraticRecursiveSequence 1) :=
    convergentSequence_bounded hconv
  exact quadraticRecursiveSequence_unbounded hbounded

/-- The quadratic recursion started at `0` is identically zero. -/
lemma quadraticRecursiveSequence_zero_eq_zero :
    ∀ n : ℕ, quadraticRecursiveSequence 0 n = 0 := by
  intro n
  induction' n with n ih
  · simp [quadraticRecursiveSequence]
  · calc
      quadraticRecursiveSequence 0 (n + 1)
          = quadraticRecursiveSequence 0 n ^ 2 +
              quadraticRecursiveSequence 0 n := by
              simp [quadraticRecursiveSequence]
      _ = 0 := by simp [ih]

/-- Starting the quadratic recursion at `0` yields a sequence converging to
`0`. -/
lemma quadraticRecursiveSequence_zero_converges :
    ConvergesTo (quadraticRecursiveSequence 0) 0 := by
  -- rewrite the recursion as the constant zero sequence and apply the constant limit
  have hconst : ConvergesTo (fun _ : ℕ => (0 : ℝ)) 0 :=
    constant_seq_converges (0 : ℝ)
  have hseq : quadraticRecursiveSequence 0 = fun _ : ℕ => (0 : ℝ) := by
    funext n
    exact quadraticRecursiveSequence_zero_eq_zero n
  exact hseq ▸ hconst

/-- Proposition 2.2.10: If `x` is a real sequence and there exists `x₀ : ℝ`
and a convergent sequence `a` with `lim_{n → ∞} a_n = 0` such that
`|x_n - x₀| ≤ a_n` for every `n`, then `x` converges to `x₀`. -/
lemma converges_of_abs_sub_le_converging_to_zero {x a : RealSequence} {x₀ : ℝ}
    (ha : ConvergesTo a 0) (hbound : ∀ n : ℕ, |x n - x₀| ≤ a n) :
    ConvergesTo x x₀ := by
  intro ε hε
  rcases ha ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have h_nonneg : 0 ≤ a n := by
    have h_abs_nonneg : 0 ≤ |x n - x₀| := abs_nonneg _
    exact le_trans h_abs_nonneg (hbound n)
  have hlt : a n < ε := by
    have habs := hM n hn
    have habs' : |a n| = a n := abs_of_nonneg h_nonneg
    simpa [habs'] using habs
  exact lt_of_le_of_lt (hbound n) hlt

/-- A sequence controlled by a convergent error term with vanishing limit is
convergent. -/
lemma convergentSequence_of_abs_sub_le_converging_to_zero {x a : RealSequence}
    {x₀ : ℝ} (ha : ConvergesTo a 0) (hbound : ∀ n : ℕ, |x n - x₀| ≤ a n) :
    ConvergentSequence x :=
  ⟨x₀, converges_of_abs_sub_le_converging_to_zero (x := x) (a := a) (x₀ := x₀)
      ha hbound⟩

/-- Proposition 2.2.11: Let `c > 0`. (i) If `c < 1`, then `lim_{n → ∞} c^n = 0`.
(ii) If `c > 1`, then the sequence `(c^n)` is unbounded. -/
lemma pow_sequence_converges_or_unbounded {c : ℝ} (hc_pos : 0 < c) :
    (c < 1 → ConvergesTo (fun n : ℕ => c ^ n) 0) ∧
      (1 < c → ¬ BoundedSequence (fun n : ℕ => c ^ n)) := by
  constructor
  · intro hc_lt
    have h_abs : |c| < 1 := by
      simpa [abs_of_pos hc_pos] using hc_lt
    have h_lim :
        Filter.Tendsto (fun n : ℕ => c ^ n) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one h_abs
    exact (convergesTo_iff_tendsto (fun n : ℕ => c ^ n) 0).2 h_lim
  · intro hc_gt hbounded
    rcases hbounded with ⟨B, hB⟩
    have h_tendsto :
        Filter.Tendsto (fun n : ℕ => c ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hc_gt
    have h_eventually := (Filter.tendsto_atTop.1 h_tendsto) (B + 1)
    rcases (Filter.eventually_atTop.1 h_eventually) with ⟨N, hN⟩
    have h_ge : B + 1 ≤ c ^ N := hN N (le_rfl)
    have h_abs_eq :
        |c ^ N| = c ^ N := by
      have h_nonneg : 0 ≤ c ^ N := pow_nonneg (le_of_lt hc_pos) _
      exact abs_of_nonneg h_nonneg
    have h_bound := hB N
    have h_contra : False := by
      have h_le : c ^ N ≤ B := by
        simpa [h_abs_eq] using h_bound
      linarith
    exact h_contra.elim

/-- Lemma 2.2.12 (Ratio test for sequences): For a real sequence `x` with
no zero terms, suppose the limit `L = lim_{n → ∞} |x_{n+1}| / |x_n|` exists.
(i) If `L < 1`, then `x` converges to `0`. (ii) If `L > 1`, then `x` is
unbounded and therefore diverges. -/
lemma ratio_test_for_sequences {x : RealSequence} {L : ℝ}
    (hx_ne : ∀ n : ℕ, x n ≠ 0)
    (hL : ConvergesTo (fun n : ℕ => |x (n + 1)| / |x n|) L) :
    (L < 1 → ConvergesTo x 0) ∧ (1 < L → ¬ BoundedSequence x) := by
  have hx_abs_pos : ∀ n : ℕ, 0 < |x n| := fun n => abs_pos.mpr (hx_ne n)
  have hL_nonneg : 0 ≤ L := by
    by_contra hneg
    have hpos : 0 < -L / 2 := by linarith
    rcases hL (-L / 2) hpos with ⟨N, hN⟩
    have h_nonneg : 0 ≤ |x (N + 1)| / |x N| := by
      have hden_pos : 0 < |x N| := hx_abs_pos N
      have hnum_nonneg : 0 ≤ |x (N + 1)| := abs_nonneg _
      exact div_nonneg hnum_nonneg hden_pos.le
    have hbound := hN N (le_rfl)
    have hlt : |x (N + 1)| / |x N| < L / 2 := by
      have hlt' := (abs_lt.mp hbound).2
      linarith
    have hpos' : 0 < L / 2 := lt_of_le_of_lt h_nonneg hlt
    linarith
  constructor
  · intro hLt
    -- choose `r` with `L < r < 1`
    set r : ℝ := (L + 1) / 2
    have hL_lt_r : L < r := by
      have hrdef : r = (L + 1) / 2 := rfl
      nlinarith [hLt, hrdef]
    have hr_lt_one : r < 1 := by
      have hrdef : r = (L + 1) / 2 := rfl
      nlinarith [hLt, hrdef]
    have hr_pos : 0 < r := by
      have hrdef : r = (L + 1) / 2 := rfl
      nlinarith [hL_nonneg, hrdef]
    -- eventual bound on the ratio by `r`
    rcases hL (r - L) (sub_pos.mpr hL_lt_r) with ⟨M, hM⟩
    have hratio_le : ∀ n ≥ M, |x (n + 1)| ≤ r * |x n| := by
      intro n hn
      have hbound := hM n hn
      have hlt : |x (n + 1)| / |x n| < r := by
        have hlt' := (abs_lt.mp hbound).2
        linarith
      have hden_pos : 0 < |x n| := hx_abs_pos n
      have hlt_mul : |x (n + 1)| < r * |x n| := by
        have hmul := (mul_lt_mul_of_pos_right hlt hden_pos)
        have hrewrite :
            |x (n + 1)| / |x n| * |x n| = |x (n + 1)| := by
          have hne : |x n| ≠ 0 := ne_of_gt hden_pos
          field_simp [hne]
        simpa [hrewrite, mul_comm, mul_left_comm, mul_assoc] using hmul
      exact le_of_lt hlt_mul
    -- compare the tail with a geometric sequence
    have hbound_tail :
        ∀ k : ℕ, |x (M + 1 + k)| ≤ |x (M + 1)| * r ^ k := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hge : M ≤ M + 1 + k := by linarith
          have hstep := hratio_le (M + 1 + k) hge
          have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
          have hmul_le :
              r * |x (M + 1 + k)| ≤ r * (|x (M + 1)| * r ^ k) :=
            mul_le_mul_of_nonneg_left ih hr_nonneg
          calc
            |x (M + 1 + k.succ)| = |x (M + 1 + k + 1)| := by
              simp [Nat.succ_eq_add_one, add_comm, add_left_comm]
            _ ≤ r * |x (M + 1 + k)| := by
              simpa [Nat.add_assoc] using hstep
            _ ≤ r * (|x (M + 1)| * r ^ k) := hmul_le
            _ = |x (M + 1)| * r ^ k * r := by ring_nf
            _ = |x (M + 1)| * r ^ k.succ := by
              simp [pow_succ, mul_comm, mul_left_comm]
    -- convergence of the geometric upper bound
    have hpow_conv :
        ConvergesTo (fun k : ℕ => r ^ k) 0 :=
      (pow_sequence_converges_or_unbounded (c := r) hr_pos).1 hr_lt_one
    have hconst := constant_seq_converges (|x (M + 1)|)
    have hupper :
        ConvergesTo (fun k : ℕ => |x (M + 1)| * r ^ k) 0 := by
      have hmul := limit_mul_of_convergent hconst hpow_conv
      simpa [mul_zero] using hmul
    -- squeeze the absolute values of the tail
    have htail_abs :
        ConvergesTo (fun k : ℕ => |x (M + 1 + k)|) 0 := by
      refine
        squeeze_converges (a := fun _ => 0)
          (b := fun k => |x (M + 1)| * r ^ k)
          (x := fun k => |x (M + 1 + k)|) (l := 0) ?_ ?_ ?_ ?_
      · intro k
        exact abs_nonneg _
      · intro k
        exact hbound_tail k
      · simpa using (constant_seq_converges (0 : ℝ))
      · simpa using hupper
    -- translate back to the original sequence
    have htail : ConvergesTo (sequenceTail x M) 0 := by
      intro ε hε
      rcases htail_abs ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have h := hN n hn
      have h' : |x (n + (M + 1))| < ε := by
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using h
      simpa [sequenceTail, sub_eq_add_neg] using h'
    exact convergesTo_of_tail_converges M htail
  · intro hgt
    -- choose `r` with `1 < r < L`
    set r : ℝ := (L + 1) / 2
    have hr_gt_one : 1 < r := by
      have hrdef : r = (L + 1) / 2 := rfl
      nlinarith [hgt, hrdef]
    have hr_lt_L : r < L := by
      have hrdef : r = (L + 1) / 2 := rfl
      nlinarith [hgt, hrdef]
    have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
    rcases hL (L - r) (sub_pos.mpr hr_lt_L) with ⟨M, hM⟩
    have hratio_ge : ∀ n ≥ M, |x (n + 1)| ≥ r * |x n| := by
      intro n hn
      have hbound := hM n hn
      have hgt_ratio : r < |x (n + 1)| / |x n| := by
        have hlt' := (abs_lt.mp hbound).1
        linarith
      have hden_pos : 0 < |x n| := hx_abs_pos n
      have hgt_mul : r * |x n| < |x (n + 1)| := by
        have hmul := (mul_lt_mul_of_pos_right hgt_ratio hden_pos)
        have hrewrite :
            |x (n + 1)| / |x n| * |x n| = |x (n + 1)| := by
          have hne : |x n| ≠ 0 := ne_of_gt hden_pos
          field_simp [hne]
        have hcomm :
            r * |x n| = |x n| * r := by ring
        -- reorder to match the `simpa` below
        have hmul' :
            |x n| * r < |x (n + 1)| := by
          have := hmul
          simpa [hrewrite, hcomm, mul_comm, mul_left_comm, mul_assoc] using this
        simpa [hcomm, mul_comm] using hmul'
      exact le_of_lt hgt_mul
    -- geometric lower bound on the tail
    have hbound_tail :
        ∀ k : ℕ, |x (M + 1 + k)| ≥ |x (M + 1)| * r ^ k := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          have hge : M ≤ M + 1 + k := by linarith
          have hstep : r * |x (M + 1 + k)| ≤ |x (M + 1 + k.succ)| := by
            have h := hratio_ge (M + 1 + k) hge
            simpa [Nat.add_assoc] using h
          have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
          have hmul :
              r * (|x (M + 1)| * r ^ k) ≤ r * |x (M + 1 + k)| :=
            mul_le_mul_of_nonneg_left ih hr_nonneg
          calc
            |x (M + 1)| * r ^ k.succ =
                r * (|x (M + 1)| * r ^ k) := by
                  simp [pow_succ, mul_comm, mul_left_comm]
            _ ≤ r * |x (M + 1 + k)| := hmul
            _ ≤ |x (M + 1 + k.succ)| := hstep
    -- derive a contradiction with the unbounded geometric sequence
    have hpow_unbounded :
        ¬ BoundedSequence (fun k : ℕ => r ^ k) :=
      (pow_sequence_converges_or_unbounded (c := r) hr_pos).2 hr_gt_one
    intro hbounded
    rcases hbounded with ⟨B, hB⟩
    have hpow_bounded : BoundedSequence (fun k : ℕ => r ^ k) := by
      refine ⟨B / |x (M + 1)|, ?_⟩
      intro k
      have h_upper : |x (M + 1 + k)| ≤ B := hB (M + 1 + k)
      have h_lower : |x (M + 1)| * r ^ k ≤ |x (M + 1 + k)| :=
        hbound_tail k
      have hCpos : 0 < |x (M + 1)| := hx_abs_pos (M + 1)
      have hcomp : |x (M + 1)| * r ^ k ≤ B := le_trans h_lower h_upper
      have hpow_le : r ^ k ≤ B / |x (M + 1)| := by
        have hmul : |x (M + 1)| * r ^ k ≤ B := hcomp
        have hmul' :
            |x (M + 1)| * r ^ k * (|x (M + 1)|)⁻¹ ≤ B * (|x (M + 1)|)⁻¹ :=
          mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hCpos.le)
        have hne : |x (M + 1)| ≠ 0 := ne_of_gt hCpos
        have hleft :
            |x (M + 1)| * r ^ k * (|x (M + 1)|)⁻¹ = r ^ k := by
          field_simp [mul_comm, mul_left_comm, mul_assoc, hne]
        have hright :
            B * (|x (M + 1)|)⁻¹ = B / |x (M + 1)| := by
          simp [div_eq_mul_inv]
        have : r ^ k ≤ B / |x (M + 1)| := by
          simpa [hleft, hright, mul_comm, mul_left_comm, mul_assoc] using hmul'
        exact this
      have hpow_nonneg : 0 ≤ r ^ k := pow_nonneg (le_of_lt hr_pos) _
      have hpow_abs : |r ^ k| ≤ B / |x (M + 1)| := by
        have habs : |r ^ k| = r ^ k := abs_of_nonneg hpow_nonneg
        simpa [habs] using hpow_le
      simpa using hpow_abs
    exact hpow_unbounded hpow_bounded

/-- Example 2.2.13: Applying the ratio test with
`|x_{n+1}| / |x_n| = 2 / (n + 1)`, we obtain
`lim_{n → ∞} (2^n / n!) = 0`. -/
lemma pow_two_over_factorial_nonzero :
    ∀ n : ℕ, (2 : ℝ) ^ n / (Nat.factorial n) ≠ 0 := by
  intro n
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  exact div_ne_zero hpow hfact

lemma pow_two_over_factorial_ratio_limit :
    ConvergesTo
      (fun n : ℕ =>
        |(2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))| /
          |(2 : ℝ) ^ n / (Nat.factorial n)|) 0 := by
  have hpos : ∀ n : ℕ, 0 < (2 : ℝ) ^ n / (Nat.factorial n) := by
    intro n
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hfact : 0 < (Nat.factorial n : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    exact div_pos hpow hfact
  have hratio :
      (fun n : ℕ =>
        |(2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))| /
          |(2 : ℝ) ^ n / (Nat.factorial n)|) =
        fun n : ℕ => (2 : ℝ) / (n + 1) := by
    funext n
    have hposn : 0 < (2 : ℝ) ^ n / (Nat.factorial n) := hpos n
    have hposn1 : 0 < (2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1)) :=
      hpos (n + 1)
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hfact_ne : (Nat.factorial n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hfact_succ_ne : (Nat.factorial (n + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n + 1)
    have hsucc_ne : (n + 1 : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hpos_abs :
        |(2 : ℝ) ^ n / (Nat.factorial n)| =
          (2 : ℝ) ^ n / (Nat.factorial n) := abs_of_pos hposn
    have hpos_abs1 :
        |(2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))| =
          (2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1)) :=
      abs_of_pos hposn1
    calc
      |(2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))| /
          |(2 : ℝ) ^ n / (Nat.factorial n)|
          =
            ((2 : ℝ) ^ (n + 1) / (Nat.factorial (n + 1))) /
              ((2 : ℝ) ^ n / (Nat.factorial n)) := by
                simp [hpos_abs, hpos_abs1]
      _ = (2 : ℝ) / (n + 1) := by
        field_simp [pow_succ, Nat.factorial_succ, hpow_ne, hfact_ne,
          hfact_succ_ne, hsucc_ne]
        simp [Nat.factorial_succ]
        ring
  have hlim_inv : ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0 :=
    inv_nat_converges_to_zero
  have hconst : ConvergesTo (fun _ : ℕ => (2 : ℝ)) 2 :=
    constant_seq_converges 2
  have hlim :
      ConvergesTo (fun n : ℕ => (2 : ℝ) / (n + 1)) 0 := by
    have hmul := limit_mul_of_convergent hconst hlim_inv
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hratio ▸ hlim

lemma pow_two_over_factorial_converges_to_zero :
    ConvergesTo (fun n : ℕ => (2 : ℝ) ^ n / (Nat.factorial n)) 0 := by
  have hx_ne := pow_two_over_factorial_nonzero
  have hratio := pow_two_over_factorial_ratio_limit
  have htest :=
      (ratio_test_for_sequences
          (x := fun n : ℕ => (2 : ℝ) ^ n / (Nat.factorial n))
          (L := 0) hx_ne hratio).1
  have hconv := htest (by norm_num)
  simpa using hconv

/-- Example 2.2.14: Using the ratio test on the sequence `(n / (1 + ε)^n)`,
for any `ε > 0` we get `n / (1 + ε)^n → 0`, which forces
`1 ≤ n^(1/n) < 1 + ε` for large `n`. Hence `lim_{n → ∞} n^(1/n) = 1`. -/
lemma nth_root_sequence_converges_to_one :
    ConvergesTo (fun n : ℕ => ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ))) 1 := by
  -- auxiliary ratio computation
  have n_over_one_plus_eps_ratio_limit (ε : ℝ) (hε : 0 < ε) :
      ConvergesTo
        (fun n : ℕ =>
          |((n + 2 : ℝ) / ((1 + ε) ^ (n + 2)))| /
            |((n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))|)
        (1 / (1 + ε)) := by
    have hbase_pos : 0 < 1 + ε := by linarith
    have hpos : ∀ n : ℕ, 0 < (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) := by
      intro n
      have hnum : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hden : 0 < (1 + ε) ^ (n + 1) := pow_pos hbase_pos _
      exact div_pos hnum hden
    have hratio :
        (fun n : ℕ =>
          |((n + 2 : ℝ) / ((1 + ε) ^ (n + 2)))| /
            |((n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))|)
          =
            fun n : ℕ =>
              ((n + 2 : ℝ) / (n + 1)) * (1 / (1 + ε)) := by
      funext n
      have hpos_n : 0 < (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) := hpos n
      have hpos_succ : 0 < (n + 2 : ℝ) / ((1 + ε) ^ (n + 2)) := by
        have hnum : 0 < (n + 2 : ℝ) := by exact_mod_cast Nat.succ_pos (n + 1)
        have hden : 0 < (1 + ε) ^ (n + 2) := pow_pos hbase_pos _
        exact div_pos hnum hden
      have hden_ne : (n + 1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hbase_ne : (1 + ε) ≠ 0 := by linarith
      have hpow_ne : ((1 + ε) ^ (n + 1)) ≠ 0 := pow_ne_zero _ hbase_ne
      have hpow_ne' : ((1 + ε) ^ (n + 2)) ≠ 0 := pow_ne_zero _ hbase_ne
      have hpos_abs :
          |((n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))| =
            (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) :=
        abs_of_pos hpos_n
      have hpos_abs_succ :
          |((n + 2 : ℝ) / ((1 + ε) ^ (n + 2)))| =
            (n + 2 : ℝ) / ((1 + ε) ^ (n + 2)) :=
        abs_of_pos hpos_succ
      calc
        |((n + 2 : ℝ) / ((1 + ε) ^ (n + 2)))| /
            |((n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))|
            =
              ((n + 2 : ℝ) / ((1 + ε) ^ (n + 2))) /
                ((n + 1 : ℝ) / ((1 + ε) ^ (n + 1))) := by
                  simp [hpos_abs, hpos_abs_succ]
        _ = ((n + 2 : ℝ) / (n + 1)) * (1 / (1 + ε)) := by
          field_simp [hden_ne, hpow_ne, hpow_ne', hbase_ne, pow_succ,
            mul_comm, mul_left_comm, mul_assoc]
          ring
    have hinv : ConvergesTo (fun n : ℕ => (1 : ℝ) / (n + 1)) 0 :=
      inv_nat_converges_to_zero
    have hconst1 : ConvergesTo (fun _ : ℕ => (1 : ℝ)) 1 :=
      constant_seq_converges 1
    have hsum :
        ConvergesTo (fun n : ℕ => 1 + (1 : ℝ) / (n + 1)) 1 :=
      by
        have h := limit_add_of_convergent hconst1 hinv
        simpa using h
    have hfun :
        (fun n : ℕ => (n + 2 : ℝ) / (n + 1)) =
          fun n : ℕ => 1 + (1 : ℝ) / (n + 1) := by
      funext n
      have hden_ne : (n + 1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hcalc : (n + 2 : ℝ) / (n + 1) = 1 + 1 / (n + 1) := by
        field_simp [hden_ne]
        ring
      simpa using hcalc
    have hlim_ratio :
        ConvergesTo (fun n : ℕ => (n + 2 : ℝ) / (n + 1)) 1 := by
      simpa [hfun] using hsum
    have hconst :
        ConvergesTo (fun _ : ℕ => (1 : ℝ) / (1 + ε)) (1 / (1 + ε)) :=
      constant_seq_converges _
    have hfinal := limit_mul_of_convergent hlim_ratio hconst
    simpa [hratio, one_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal
  -- the sequence `(n + 1)/(1 + ε)^(n + 1)` tends to `0`
  have n_over_one_plus_eps_converges_to_zero (ε : ℝ) (hε : 0 < ε) :
      ConvergesTo (fun n : ℕ => (n + 1 : ℝ) / ((1 + ε) ^ (n + 1))) 0 := by
    have hx_ne : ∀ n : ℕ,
        (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) ≠ 0 := by
      intro n
      have hnum : (n + 1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      have hbase_ne : (1 + ε) ≠ 0 := by linarith
      have hden : ((1 + ε) ^ (n + 1)) ≠ 0 := pow_ne_zero _ hbase_ne
      exact div_ne_zero hnum hden
    have hratio := n_over_one_plus_eps_ratio_limit ε hε
    have hratio' :
        ConvergesTo
          (fun n : ℕ =>
            |(((n + 1 : ℝ) + 1) / ((1 + ε) ^ (n + 1 + 1)))| /
              |((n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))|)
          (1 / (1 + ε)) := by
      simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, one_add_one_eq_two,
        add_comm, add_left_comm, add_assoc] using hratio
    have htest :=
        (ratio_test_for_sequences
            (x := fun n : ℕ => (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)))
            (L := 1 / (1 + ε)) hx_ne
            (by
              simpa [Nat.cast_succ, Nat.succ_eq_add_one, add_comm, add_left_comm,
                add_assoc] using hratio')).1
    have hlt : 1 / (1 + ε) < 1 := by
      have hpos : 0 < (1 : ℝ) := by norm_num
      have hlt' : (1 : ℝ) < 1 + ε := by linarith
      have h := one_div_lt_one_div_of_lt hpos hlt'
      simpa using h
    exact htest hlt
  -- eventual upper bound `((n+1)^(1/(n+1))) < 1 + ε`
  have nth_root_eventually_lt_one_plus_eps (ε : ℝ) (hε : 0 < ε) :
      ∃ M : ℕ,
        ∀ n ≥ M, ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) < 1 + ε := by
    have hconv := n_over_one_plus_eps_converges_to_zero ε hε
    rcases hconv 1 (by norm_num) with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n hn
    have hbound : (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) < 1 := by
      have habs := hM n hn
      have hpos :
          (n + 1 : ℝ) / ((1 + ε) ^ (n + 1)) - 0 <
            (1 : ℝ) := (abs_lt.mp habs).2
      simpa using hpos
    have hden_pos : 0 < (1 + ε) ^ (n + 1) := pow_pos (by linarith) _
    have hden_ne : (1 + ε) ^ (n + 1) ≠ 0 := by
      exact pow_ne_zero _ (by linarith : (1 + ε) ≠ 0)
    have hlt : (n + 1 : ℝ) < (1 + ε) ^ (n + 1) := by
      have h := hbound
      have hden_ne' := hden_ne
      field_simp [hden_ne'] at h
      simpa [one_mul] using h
    have hexp_pos : 0 < (1 / (n + 1 : ℝ)) := by
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      simpa [one_div] using inv_pos.mpr hpos
    have hbase_nonneg : 0 ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.zero_le (n + 1)
    have hroot_lt :
        ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) <
          ((1 + ε) ^ (n + 1 : ℕ) : ℝ).rpow (1 / (n + 1 : ℝ)) :=
      Real.rpow_lt_rpow hbase_nonneg hlt hexp_pos
    have hpow_rpow :
        ((1 + ε) ^ (n + 1 : ℕ) : ℝ).rpow (1 / (n + 1 : ℝ)) =
          1 + ε := by
      have hnonneg : 0 ≤ 1 + ε := by linarith
      have hne : (n + 1 : ℕ) ≠ 0 := by exact Nat.succ_ne_zero n
      simpa [one_div] using
        (Real.pow_rpow_inv_natCast (x := 1 + ε) (hx := hnonneg) (hn := hne))
    have hroot_lt' :
        ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) < 1 + ε := by
      linarith
    exact hroot_lt'
  -- basic lower bound `((n+1)^(1/(n+1))) ≥ 1`
  have nth_root_ge_one :
      ∀ n : ℕ, 1 ≤ ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) := by
    intro n
    have hbase : 1 ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hexp_nonneg :
        0 ≤ (1 / (n + 1 : ℝ)) := by
      have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      have hinv : 0 ≤ (1 : ℝ) / (n + 1) := le_of_lt (one_div_pos.mpr hpos)
      simpa using hinv
    exact Real.one_le_rpow hbase hexp_nonneg
  -- assemble the two-sided bounds
  intro ε hε
  rcases nth_root_eventually_lt_one_plus_eps ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hlower : 1 ≤ ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) := nth_root_ge_one n
  have hupper : ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) < 1 + ε := hM n hn
  have hnonneg :
      0 ≤ ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) - 1 :=
    sub_nonneg.mpr hlower
  have hlt : ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) - 1 < ε := by
    linarith
  have habs :
      |((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) - 1| =
        ((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) - 1 :=
    abs_of_nonneg hnonneg
  have hfinal : |((n + 1 : ℝ)).rpow (1 / (n + 1 : ℝ)) - 1| < ε := by
    linarith
  simpa using hfinal

end Section02
end Chap02

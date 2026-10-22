/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Set SignType

section Chap04
section Section03

/-- Definition 4.3.1: For an `n`-times differentiable function `f` near
`x0 ∈ ℝ`, the nth-order Taylor polynomial at `x0` is
`P_n^{x0}(x) = ∑_{k=0}^n f^(k)(x0) / k! * (x - x0)^k`. -/
noncomputable def taylorPolynomial (f : ℝ → ℝ) (x0 : ℝ) (n : ℕ) :
    Polynomial ℝ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    Polynomial.C ((iteratedDeriv k f x0) / (Nat.factorial k)) *
      (Polynomial.X - Polynomial.C x0) ^ k

/-- On an interior point of `Icc x₀ x`, within-iterated derivatives agree with ordinary ones. -/
lemma iteratedDerivWithin_eq_iteratedDeriv_Icc {f : ℝ → ℝ} {x0 x c : ℝ} {k n : ℕ}
    (hx0x : x0 < x) (hc : c ∈ Set.Ioo x0 x)
    (hcont : ContDiffOn ℝ (n + 1) f (Set.Icc x0 x)) (hk : k ≤ n + 1) :
    iteratedDerivWithin k f (Set.Icc x0 x) c = iteratedDeriv k f c := by
  have hcIcc : c ∈ Set.Icc x0 x := Set.Ioo_subset_Icc_self hc
  have hcontWithin : ContDiffWithinAt ℝ (n + 1) f (Set.Icc x0 x) c :=
    hcont.contDiffWithinAt hcIcc
  have hcontAt : ContDiffAt ℝ (n + 1) f c :=
    (contDiffWithinAt_iff_contDiffAt (Icc_mem_nhds hc.1 hc.2)).1 hcontWithin
  exact
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx0x)
      (hcontAt.of_le (by exact_mod_cast hk)) hcIcc

/-- Identify `taylorWithinEval` on an interval with the explicit Taylor polynomial. -/
lemma taylorWithinEval_eq_taylorPolynomial {f : ℝ → ℝ} {x0 x : ℝ} {n : ℕ}
    (hx0x : x0 < x) (hcontAt : ContDiffAt ℝ (n + 1) f x0) :
    taylorWithinEval f n (Set.Icc x0 x) x0 x =
      (taylorPolynomial f x0 n).eval x := by
  classical
  have huniq : UniqueDiffOn ℝ (Set.Icc x0 x) := uniqueDiffOn_Icc hx0x
  have hx0mem : x0 ∈ Set.Icc x0 x := ⟨le_rfl, le_of_lt hx0x⟩
  have hderiv_eq :
      ∀ k ∈ Finset.range (n + 1),
        iteratedDerivWithin k f (Set.Icc x0 x) x0 = iteratedDeriv k f x0 := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hcontAt' : ContDiffAt ℝ k f x0 :=
      hcontAt.of_le (by exact_mod_cast Nat.le_trans hk_le (Nat.le_succ n))
    exact iteratedDerivWithin_eq_iteratedDeriv huniq hcontAt' hx0mem
  have htaylor :
      taylorWithinEval f n (Set.Icc x0 x) x0 x =
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k) • iteratedDeriv k f x0 := by
    classical
    have hsum :
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k) •
            iteratedDerivWithin k f (Set.Icc x0 x) x0 =
          ∑ k ∈ Finset.range (n + 1),
            ((Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k) • iteratedDeriv k f x0 := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [hderiv_eq k hk]
    simpa [taylor_within_apply] using hsum
  have hpoly :
      (taylorPolynomial f x0 n).eval x =
        ∑ k ∈ Finset.range (n + 1),
          ((Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k) • iteratedDeriv k f x0 := by
    classical
    simp [taylorPolynomial, Polynomial.eval_finset_sum, smul_eq_mul, div_eq_mul_inv,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, mul_comm, mul_assoc]
  exact htaylor.trans hpoly.symm

/-- Taylor's theorem on a positively oriented interval. -/
lemma taylor_with_remainder_pos {f : ℝ → ℝ} {x0 x : ℝ} {n : ℕ}
    (hx0x : x0 < x) (hcont : ContDiffOn ℝ (n + 1) f (Set.Icc x0 x))
    (hcontAt : ContDiffAt ℝ (n + 1) f x0) :
    ∃ c ∈ Set.Icc x0 x,
      f x =
        (taylorPolynomial f x0 n).eval x +
          (iteratedDeriv (n + 1) f c) / (Nat.factorial (n + 1)) *
            (x - x0) ^ (n + 1) := by
  classical
  have hcont' : ContDiffOn ℝ (n + 1) f (Set.uIcc x0 x) := by
    simpa [Set.uIcc_of_lt hx0x] using hcont
  rcases taylor_mean_remainder_lagrange_iteratedDeriv hx0x.ne hcont' with ⟨c, hc, hceq⟩
  have hpoly := taylorWithinEval_eq_taylorPolynomial (n := n) hx0x hcontAt
  have hc' : c ∈ Set.Ioo x0 x := by
    simpa [Set.uIoo_of_lt hx0x] using hc
  have hcIcc : c ∈ Set.Icc x0 x := Set.Ioo_subset_Icc_self hc'
  have hceq' :
      f x =
        taylorWithinEval f n (Set.Icc x0 x) x0 x +
          iteratedDeriv (n + 1) f c * (x - x0) ^ (n + 1) /
            (Nat.factorial (n + 1)) := by
    have h := eq_add_of_sub_eq hceq
    simpa [Set.uIcc_of_lt hx0x, add_comm] using h
  refine ⟨c, hcIcc, ?_⟩
  calc
    f x =
        taylorWithinEval f n (Set.Icc x0 x) x0 x +
          iteratedDeriv (n + 1) f c * (x - x0) ^ (n + 1) /
            (Nat.factorial (n + 1)) := hceq'
    _ =
        (taylorPolynomial f x0 n).eval x +
          iteratedDeriv (n + 1) f c * (x - x0) ^ (n + 1) /
            (Nat.factorial (n + 1)) := by
      simp [hpoly]
    _ =
        (taylorPolynomial f x0 n).eval x +
          (iteratedDeriv (n + 1) f c) / (Nat.factorial (n + 1)) *
            (x - x0) ^ (n + 1) := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Taylor's theorem on a negatively oriented interval, obtained by reflection. -/
lemma taylor_with_remainder_neg {f : ℝ → ℝ} {x0 x : ℝ} {n : ℕ}
    (hx0x : x < x0) (hcont : ContDiffOn ℝ (n + 1) f (Set.Icc x x0))
    (hcontAt : ContDiffAt ℝ (n + 1) f x0) :
    ∃ c ∈ Set.Icc x x0,
      f x =
        (taylorPolynomial f x0 n).eval x +
          (iteratedDeriv (n + 1) f c) / (Nat.factorial (n + 1)) *
            (x - x0) ^ (n + 1) := by
  classical
  let g : ℝ → ℝ := fun t => f (-t)
  have hxneg : -x0 < -x := by linarith
  have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Icc (-x0) (-x)) (Set.Icc x x0) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcont_neg : ContDiffOn ℝ (n + 1) g (Set.Icc (-x0) (-x)) :=
    hcont.comp (contDiff_neg.contDiffOn) hmaps
  have hcontAt_neg : ContDiffAt ℝ (n + 1) g (-x0) :=
    by
      have houter : ContDiffAt ℝ (n + 1) f (-(-x0)) := by
        simpa [neg_neg] using hcontAt
      simpa [g] using houter.comp (-x0) (by simpa using contDiff_neg.contDiffAt)
  obtain ⟨c, hc, hceq⟩ :=
    taylor_with_remainder_pos (f := g) (x0 := -x0) (x := -x) (n := n)
      hxneg hcont_neg hcontAt_neg
  have hc' : -c ∈ Set.Icc x x0 := by
    have hcIcc : c ∈ Set.Icc (-x0) (-x) := hc
    constructor <;> linarith [hcIcc.1, hcIcc.2]
  have hpow :
      ∀ k, ((-x) - (-x0)) ^ k = (-1 : ℝ) ^ k * (x - x0) ^ k := by
    intro k
    have hx : (-x) - (-x0) = (-1 : ℝ) * (x - x0) := by ring
    calc
      ((-x) - (-x0)) ^ k = ((-1 : ℝ) * (x - x0)) ^ k := by simp [hx]
      _ = (-1 : ℝ) ^ k * (x - x0) ^ k := by
        simpa [mul_comm] using (mul_pow (-1 : ℝ) (x - x0) k)
  have hpoly :
      (taylorPolynomial g (-x0) n).eval (-x) =
        (taylorPolynomial f x0 n).eval x := by
    classical
    have hrewrite :
        ∀ k, iteratedDeriv k g (-x0) = (-1 : ℝ) ^ k * iteratedDeriv k f x0 := by
      intro k
      simp [g, iteratedDeriv_comp_neg, smul_eq_mul]
    simp [taylorPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      div_eq_mul_inv]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hderiv := hrewrite k
    have hpow' : (-x + x0) ^ k = (-1 : ℝ) ^ k * (x - x0) ^ k := by
      have hx : (-x) - (-x0) = -x + x0 := by ring
      calc
        (-x + x0) ^ k = ((-x) - (-x0)) ^ k := by simp [hx]
        _ = (-1 : ℝ) ^ k * (x - x0) ^ k := hpow k
    calc
      (iteratedDeriv k g (-x0) * (Nat.factorial k : ℝ)⁻¹) *
          (-x + x0) ^ k =
          ((-1 : ℝ) ^ k * iteratedDeriv k f x0 * (Nat.factorial k : ℝ)⁻¹) *
            ((-1 : ℝ) ^ k * (x - x0) ^ k) := by
        simp [hderiv, hpow']
      _ =
          (-1 : ℝ) ^ (2 * k) *
            (iteratedDeriv k f x0 * (Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k) := by
        ring
      _ =
          iteratedDeriv k f x0 * (Nat.factorial k : ℝ)⁻¹ * (x - x0) ^ k := by
        have hsign : (-1 : ℝ) ^ (2 * k) = (1 : ℝ) := by
          calc
            (-1 : ℝ) ^ (2 * k) = ((-1 : ℝ) ^ 2) ^ k := by
              simp [pow_mul]
            _ = (1 : ℝ) := by simp
        simp [hsign]
  have hiter :
      iteratedDeriv (n + 1) g c =
        (-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) f (-c) := by
    simp [g, iteratedDeriv_comp_neg, smul_eq_mul]
  have hpow_succ :
      ((-x) - (-x0)) ^ (n + 1) =
        (-1 : ℝ) ^ (n + 1) * (x - x0) ^ (n + 1) :=
    hpow (n + 1)
  have hsign : (-1 : ℝ) ^ (2 * (n + 1)) = (1 : ℝ) := by
    calc
      (-1 : ℝ) ^ (2 * (n + 1)) = ((-1 : ℝ) ^ 2) ^ (n + 1) := by
        simp [pow_mul]
      _ = (1 : ℝ) := by simp
  have hterm :
      iteratedDeriv (n + 1) g c / Nat.factorial (n + 1) *
          (-x + x0) ^ (n + 1) =
        iteratedDeriv (n + 1) f (-c) / Nat.factorial (n + 1) *
          (x - x0) ^ (n + 1) := by
    have hpow' : (-x + x0) ^ (n + 1) =
        (-1 : ℝ) ^ (n + 1) * (x - x0) ^ (n + 1) := by
      have hx : (-x) - (-x0) = -x + x0 := by ring
      calc
        (-x + x0) ^ (n + 1) = ((-x) - (-x0)) ^ (n + 1) := by simp [hx]
        _ = (-1 : ℝ) ^ (n + 1) * (x - x0) ^ (n + 1) := hpow_succ
    calc
      iteratedDeriv (n + 1) g c / Nat.factorial (n + 1) *
          (-x + x0) ^ (n + 1)
          = ((-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) f (-c)) /
              Nat.factorial (n + 1) *
            ((-1 : ℝ) ^ (n + 1) * (x - x0) ^ (n + 1)) := by
            simp [hiter, hpow', div_eq_mul_inv]
      _ =
          ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
            (iteratedDeriv (n + 1) f (-c) / Nat.factorial (n + 1) *
              (x - x0) ^ (n + 1)) := by
        ring
      _ =
          iteratedDeriv (n + 1) f (-c) / Nat.factorial (n + 1) *
            (x - x0) ^ (n + 1) := by
        have hsign' : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = (1 : ℝ) := by
          calc
            (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)
                = (-1 : ℝ) ^ ((n + 1) + (n + 1)) := by
                  simpa using (pow_add (-1 : ℝ) (n + 1) (n + 1)).symm
            _ = (-1 : ℝ) ^ (2 * (n + 1)) := by ring
            _ = (1 : ℝ) := hsign
        simp [hsign', div_eq_mul_inv]
  have hxg : g (-x) = f x := by simp [g]
  refine ⟨-c, hc', ?_⟩
  calc
    f x =
        (taylorPolynomial g (-x0) n).eval (-x) +
          iteratedDeriv (n + 1) g c / Nat.factorial (n + 1) *
            ((-x) - (-x0)) ^ (n + 1) := by
      simpa [hxg] using hceq
    _ =
        (taylorPolynomial g (-x0) n).eval (-x) +
          iteratedDeriv (n + 1) g c / Nat.factorial (n + 1) *
            (-x + x0) ^ (n + 1) := by
      have hx : (-x) - (-x0) = -x + x0 := by ring
      simp [hx]
    _ =
        (taylorPolynomial f x0 n).eval x +
          iteratedDeriv (n + 1) f (-c) / Nat.factorial (n + 1) *
            (x - x0) ^ (n + 1) := by
      simp [hpoly, hterm]

/-- Theorem 4.3.2 (Taylor): If `f : ℝ → ℝ` has `n` continuous derivatives on
`[a, b]` and the `(n+1)`st derivative exists on `(a, b)`, then for distinct
points `x₀, x ∈ [a, b]` there is a point `c` between them such that
`f x = Pₙ^{x₀}(x) + f^{(n+1)}(c) / (n+1)! * (x - x₀)^{n+1}`. -/
theorem taylor_with_remainder {f : ℝ → ℝ} {a b x0 x : ℝ} {n : ℕ}
    (hx0 : x0 ∈ Set.Ioo a b) (hx : x ∈ Set.Icc a b) (hx0x : x0 ≠ x)
    (hcont : ContDiffOn ℝ (n + 1) f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc (min x0 x) (max x0 x),
      f x =
        (taylorPolynomial f x0 n).eval x +
          (iteratedDeriv (n + 1) f c) / (Nat.factorial (n + 1)) *
            (x - x0) ^ (n + 1) := by
  classical
  have hx0Icc : x0 ∈ Set.Icc a b := ⟨le_of_lt hx0.1, le_of_lt hx0.2⟩
  have hcontAt :
      ContDiffAt ℝ (n + 1) f x0 :=
    (contDiffWithinAt_iff_contDiffAt (Icc_mem_nhds hx0.1 hx0.2)).1 (hcont x0 hx0Icc)
  rcases lt_or_gt_of_ne hx0x with hlt | hgt
  · -- case `x0 < x`
    have hsubset : Set.Icc x0 x ⊆ Set.Icc a b := by
      intro y hy
      have hx_le : x ≤ b := hx.2
      have ha_le : a ≤ x0 := hx0Icc.1
      exact ⟨le_trans ha_le hy.1, le_trans hy.2 hx_le⟩
    have hcont' : ContDiffOn ℝ (n + 1) f (Set.Icc x0 x) := hcont.mono hsubset
    obtain ⟨c, hc, hceq⟩ := taylor_with_remainder_pos hlt hcont' hcontAt
    refine ⟨c, ?_, hceq⟩
    have hmin : min x0 x = x0 := min_eq_left (le_of_lt hlt)
    have hmax : max x0 x = x := max_eq_right (le_of_lt hlt)
    simpa [hmin, hmax] using hc
  · -- case `x < x0`
    have hsubset : Set.Icc x x0 ⊆ Set.Icc a b := by
      intro y hy
      have ha : a ≤ x := hx.1
      have hb : x0 ≤ b := hx0Icc.2
      exact ⟨le_trans ha hy.1, le_trans hy.2 hb⟩
    have hcont' : ContDiffOn ℝ (n + 1) f (Set.Icc x x0) := hcont.mono hsubset
    obtain ⟨c, hc, hceq⟩ := taylor_with_remainder_neg hgt hcont' hcontAt
    refine ⟨c, ?_, hceq⟩
    have hmin : min x0 x = x := min_eq_right (le_of_lt hgt)
    have hmax : max x0 x = x0 := max_eq_left (le_of_lt hgt)
    simpa [hmin, hmax] using hc

/-- If `y` lies between `x` and `x₀`, then the distance from `y` to `x₀` is bounded by the
distance from `x` to `x₀`. -/
lemma abs_sub_le_of_mem_interval {x x0 y : ℝ}
    (hy : y ∈ Set.Icc (min x x0) (max x x0)) : |y - x0| ≤ |x - x0| := by
  classical
  by_cases hx : x ≤ x0
  · have hmin : min x x0 = x := min_eq_left hx
    have hmax : max x x0 = x0 := max_eq_right hx
    have hy' : x ≤ y ∧ y ≤ x0 := by simpa [hmin, hmax] using hy
    have hy_le : y ≤ x0 := hy'.2
    have hy_ge : x ≤ y := hy'.1
    have hy_nonneg : 0 ≤ x0 - y := sub_nonneg.mpr hy_le
    have hx_nonneg : 0 ≤ x0 - x := sub_nonneg.mpr hx
    have hcmp : x0 - y ≤ x0 - x := by
      linarith
    have hy_abs : |y - x0| = x0 - y := by
      have : |x0 - y| = x0 - y := abs_of_nonneg hy_nonneg
      simpa [abs_sub_comm] using this
    have hx_abs : |x - x0| = x0 - x := by
      have : |x0 - x| = x0 - x := abs_of_nonneg hx_nonneg
      simpa [abs_sub_comm] using this
    simpa [hy_abs, hx_abs] using hcmp
  · have hx' : x0 ≤ x := le_of_lt (not_le.mp hx)
    have hmin : min x x0 = x0 := min_eq_right hx'
    have hmax : max x x0 = x := max_eq_left hx'
    have hy' : x0 ≤ y ∧ y ≤ x := by simpa [hmin, hmax] using hy
    have hy_le : y ≤ x := hy'.2
    have hy_ge : x0 ≤ y := hy'.1
    have hy_nonneg : 0 ≤ y - x0 := sub_nonneg.mpr hy_ge
    have hx_nonneg : 0 ≤ x - x0 := sub_nonneg.mpr hx'
    have hcmp : y - x0 ≤ x - x0 := by
      linarith
    have hy_abs : |y - x0| = y - x0 := by
      simp [abs_of_nonneg hy_nonneg]
    have hx_abs : |x - x0| = x - x0 := by
      simp [abs_of_nonneg hx_nonneg]
    simpa [hy_abs, hx_abs] using hcmp

/-- Points sufficiently close to `x₀` stay inside `(a, b)`, and the whole interval between
them and `x₀` also lies in `(a, b)`. -/
lemma interval_subset_Ioo_of_abs_sub_lt {a b x0 x : ℝ}
    (hx0 : x0 ∈ Set.Ioo a b)
    (hx : |x - x0| < min (x0 - a) (b - x0)) :
    Set.Icc (min x x0) (max x x0) ⊆ Set.Ioo a b := by
  intro y hy
  have hx0_left : a < x0 := hx0.1
  have hx0_right : x0 < b := hx0.2
  have hx_lt_left : |x - x0| < x0 - a := lt_of_lt_of_le hx (min_le_left _ _)
  have hx_lt_right : |x - x0| < b - x0 := lt_of_lt_of_le hx (min_le_right _ _)
  have hx_gt : a < x := by
    have hx_lower : a - x0 < x - x0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (abs_lt.mp hx_lt_left).1
    have hx_lower' := add_lt_add_right hx_lower x0
    simpa using hx_lower'
  have hx_lt' : x < b := by
    have hx_upper : x - x0 < b - x0 := (abs_lt.mp hx_lt_right).2
    have hx_upper' := add_lt_add_right hx_upper x0
    simpa using hx_upper'
  have hmin : a < min x x0 := lt_min hx_gt hx0_left
  have hmax : max x x0 < b := max_lt_iff.mpr ⟨hx_lt', hx0_right⟩
  refine ⟨lt_of_lt_of_le hmin hy.1, lt_of_le_of_lt hy.2 hmax⟩

/-- Proposition 4.3.3 (Second derivative test). If `f : (a, b) → ℝ` is twice
continuously differentiable, `x0 ∈ (a, b)`, `f' x0 = 0`, and `f'' x0 > 0`, then
`x0` is a strict relative minimum of `f`. -/
theorem second_derivative_test {f : ℝ → ℝ} {a b x0 : ℝ}
    (hx0 : x0 ∈ Set.Ioo a b) (hcont : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hderiv_zero : deriv f x0 = 0) (hpos : deriv (deriv f) x0 > 0) :
    ∃ ε > 0, ∀ {x}, x ∈ Set.Ioo a b → x ≠ x0 → |x - x0| < ε → f x0 < f x := by
  classical
  obtain ⟨hx0_left, hx0_right⟩ := hx0
  have hcont_on : ContinuousOn f (Set.Ioo a b) := hcont.continuousOn
  have hdiff_on : DifferentiableOn ℝ f (Set.Ioo a b) :=
    hcont.differentiableOn (by decide)
  have hsign :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos (f := fun y => deriv f y)
      (x₀ := x0) (hf := hpos) (hx := hderiv_zero)
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := (Metric.eventually_nhds_iff).1 hsign
  set ε₀ := min (x0 - a) (b - x0) with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    have h₁ : 0 < x0 - a := sub_pos.mpr hx0_left
    have h₂ : 0 < b - x0 := sub_pos.mpr hx0_right
    simpa [ε₀, hε₀_def] using lt_min h₁ h₂
  refine ⟨min ε₀ ε₁, lt_min hε₀_pos hε₁_pos, ?_⟩
  intro x hx_mem hx_ne hx_lt
  have hx_abs₀ : |x - x0| < ε₀ := lt_of_lt_of_le hx_lt (min_le_left _ _)
  have hx_abs₁ : |x - x0| < ε₁ := lt_of_lt_of_le hx_lt (min_le_right _ _)
  have hinterval_subset :
      Set.Icc (min x x0) (max x x0) ⊆ Set.Ioo a b :=
    interval_subset_Ioo_of_abs_sub_lt ⟨hx0_left, hx0_right⟩ hx_abs₀
  have hcont_interval :
      ContinuousOn f (Set.Icc (min x x0) (max x x0)) :=
    hcont_on.mono hinterval_subset
  have hdiff_interval :
      DifferentiableOn ℝ f (Set.Ioo (min x x0) (max x x0)) :=
    hdiff_on.mono <| subset_trans Set.Ioo_subset_Icc_self hinterval_subset
  have hx_cases := lt_or_gt_of_ne hx_ne
  cases hx_cases with
  | inl hx_lt' =>
      have hx_le : x ≤ x0 := le_of_lt hx_lt'
      have hmin : min x x0 = x := min_eq_left hx_le
      have hmax : max x x0 = x0 := max_eq_right hx_le
      have hcont' : ContinuousOn f (Set.Icc x x0) := by
        simpa [hmin, hmax] using hcont_interval
      have hdiff' : DifferentiableOn ℝ f (Set.Ioo x x0) := by
        simpa [hmin, hmax] using hdiff_interval
      obtain ⟨c, hc_mem, hc_eq⟩ :=
        exists_deriv_eq_slope (f := f) hx_lt' hcont' hdiff'
      have hc_Icc : c ∈ Set.Icc (min x x0) (max x x0) := by
        have : c ∈ Set.Icc x x0 := ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
        simpa [hmin, hmax] using this
      have hc_abs_le : |c - x0| ≤ |x - x0| := abs_sub_le_of_mem_interval hc_Icc
      have hc_abs_lt : |c - x0| < ε₁ := lt_of_le_of_lt hc_abs_le hx_abs₁
      have hsign_eq := hε₁ (by simpa [Real.dist_eq] using hc_abs_lt)
      have hxsign : sign (c - x0) = -1 :=
        sign_eq_neg_one_iff.mpr <| by linarith [hc_mem.2]
      have hderiv_neg : deriv f c < 0 := by
        have : sign (deriv f c) = -1 := by simpa [hxsign] using hsign_eq
        exact sign_eq_neg_one_iff.mp this
      have hx_neg : x - x0 < 0 := sub_lt_zero.mpr hx_lt'
      have hx0x_ne : x0 - x ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx_lt').symm
      have hc_mul' :
          deriv f c * (x0 - x) = f x0 - f x :=
        (eq_div_iff_mul_eq hx0x_ne).mp hc_eq
      have hx_neg_eq : x - x0 = -(x0 - x) :=
        (neg_sub x0 x).symm
      have hf_neg : f x - f x0 = -(f x0 - f x) :=
        (neg_sub (f x0) (f x)).symm
      have hx_neg_mul :
          (x - x0) * deriv f c = (-(x0 - x)) * deriv f c :=
        congrArg (fun t : ℝ => t * deriv f c) hx_neg_eq
      have hprod_eq :
          (x - x0) * deriv f c = f x - f x0 := by
        calc
          (x - x0) * deriv f c = (-(x0 - x)) * deriv f c := hx_neg_mul
          _ = -((x0 - x) * deriv f c) := by
            exact neg_mul (x0 - x) (deriv f c)
          _ = -(deriv f c * (x0 - x)) := by
            exact congrArg (fun t : ℝ => -t) (mul_comm (x0 - x) (deriv f c))
          _ = -(f x0 - f x) := by
            exact congrArg (fun t : ℝ => -t) hc_mul'
          _ = f x - f x0 := hf_neg.symm
      have hfx_pos : 0 < f x - f x0 := by
        have hprod := mul_pos_of_neg_of_neg hx_neg hderiv_neg
        simpa [hprod_eq] using hprod
      exact sub_pos.mp hfx_pos
  | inr hx_gt' =>
      have hx_ge : x0 ≤ x := le_of_lt hx_gt'
      have hmin : min x x0 = x0 := min_eq_right hx_ge
      have hmax : max x x0 = x := max_eq_left hx_ge
      have hcont' : ContinuousOn f (Set.Icc x0 x) := by
        simpa [hmin, hmax] using hcont_interval
      have hdiff' : DifferentiableOn ℝ f (Set.Ioo x0 x) := by
        simpa [hmin, hmax] using hdiff_interval
      obtain ⟨c, hc_mem, hc_eq⟩ :=
        exists_deriv_eq_slope (f := f) hx_gt' hcont' hdiff'
      have hc_Icc : c ∈ Set.Icc (min x x0) (max x x0) := by
        have : c ∈ Set.Icc x0 x := ⟨le_of_lt hc_mem.1, le_of_lt hc_mem.2⟩
        simpa [hmin, hmax] using this
      have hc_abs_le : |c - x0| ≤ |x - x0| := abs_sub_le_of_mem_interval hc_Icc
      have hc_abs_lt : |c - x0| < ε₁ := lt_of_le_of_lt hc_abs_le hx_abs₁
      have hsign_eq := hε₁ (by simpa [Real.dist_eq] using hc_abs_lt)
      have hxsign : sign (c - x0) = 1 :=
        sign_eq_one_iff.mpr <| sub_pos.mpr hc_mem.1
      have hderiv_pos' : 0 < deriv f c := by
        have : sign (deriv f c) = 1 := by simpa [hxsign] using hsign_eq
        exact sign_eq_one_iff.mp this
      have hx_pos : 0 < x - x0 := sub_pos.mpr hx_gt'
      have hx_ne' : x - x0 ≠ 0 := sub_ne_zero.mpr hx_gt'.ne'
      have hprod_eq :
          (x - x0) * deriv f c = f x - f x0 := by
        have hc_mul' :
            deriv f c * (x - x0) = f x - f x0 :=
          (eq_div_iff_mul_eq hx_ne').mp hc_eq
        simpa [mul_comm] using hc_mul'
      have hfx_pos : 0 < f x - f x0 := by
        have hprod := mul_pos hx_pos hderiv_pos'
        simpa [hprod_eq] using hprod
      exact sub_pos.mp hfx_pos

end Section03
end Chap04

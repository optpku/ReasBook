/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap04.section02_part2

open Classical

section Chap04
section Section02

/-- Helper for Proposition 4.2.6: smoothness of the shifted monomial with
constant factor. -/
lemma helperForProposition_4_2_6_contDiff_shiftedMonomial_constMul
    (n : ℕ) (a c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ => c * (x - a) ^ n) := by
  exact contDiff_const.mul ((contDiff_id.sub contDiff_const).pow n)

/-- Helper for Proposition 4.2.6: explicit iterated derivative formula for
`(x - a)^n` with falling-product coefficient. -/
lemma helperForProposition_4_2_6_iteratedDeriv_shiftedMonomial_fallingProd
    (n k : ℕ) (a x : ℝ) :
    iteratedDeriv k (fun y : ℝ => (y - a) ^ n) x =
      Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k) := by
  have hComp :=
    congrArg (fun g : ℝ → ℝ => g x)
      (iteratedDeriv_comp_add_const k (fun z : ℝ => z ^ n) (-a))
  have hPow :
      iteratedDeriv k (fun z : ℝ => z ^ n) (x + (-a)) =
        Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x + (-a)) ^ (n - k) := by
    calc
      iteratedDeriv k (fun z : ℝ => z ^ n) (x + (-a))
          = (deriv^[k] (fun z : ℝ => z ^ n)) (x + (-a)) := by
              rw [iteratedDeriv_eq_iterate]
      _ = Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x + (-a)) ^ (n - k) := by
            simpa using iter_deriv_pow n (x + (-a)) k
  calc
    iteratedDeriv k (fun y : ℝ => (y - a) ^ n) x
        = iteratedDeriv k (fun y : ℝ => (y + (-a)) ^ n) x := by
            simp [sub_eq_add_neg]
    _ = iteratedDeriv k (fun z : ℝ => z ^ n) (x + (-a)) := by
          simpa [sub_eq_add_neg] using hComp
    _ = Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x + (-a)) ^ (n - k) := hPow
    _ = Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k) := by
          simp [sub_eq_add_neg]

/-- Helper for Proposition 4.2.6: pull the constant factor `c` out of
iterated derivatives of the shifted monomial. -/
lemma helperForProposition_4_2_6_iteratedDeriv_constMul_shiftedMonomial_fallingProd
    (n k : ℕ) (a c x : ℝ) :
    iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x =
      c * (Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k)) := by
  have hContDiff : ContDiff ℝ ⊤ (fun y : ℝ => (y - a) ^ n) := by
    exact (contDiff_id.sub contDiff_const).pow n
  have hContDiffAtK : ContDiffAt ℝ (k : WithTop ℕ∞) (fun y : ℝ => (y - a) ^ n) x := by
    exact hContDiff.contDiffAt.of_le le_top
  have hConstMul :
      iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x =
        c * iteratedDeriv k (fun y : ℝ => (y - a) ^ n) x :=
    iteratedDeriv_const_mul (x := x) (n := k) (f := fun y : ℝ => (y - a) ^ n) c hContDiffAtK
  calc
    iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x
        = c * iteratedDeriv k (fun y : ℝ => (y - a) ^ n) x := hConstMul
    _ = c * (Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k)) := by
          rw [helperForProposition_4_2_6_iteratedDeriv_shiftedMonomial_fallingProd n k a x]

/-- Helper for Proposition 4.2.6: convert the falling-product coefficient
to the factorial-ratio coefficient when `k ≤ n`. -/
lemma helperForProposition_4_2_6_fallingProd_eq_factorialRatio
    (n : ℕ) {k : ℕ} (hk : k ≤ n) :
    Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) =
      (Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ) := by
  have hProdDesc :
      Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) = (n.descFactorial k : ℝ) := by
    have hEq :
        Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) =
          Finset.prod (Finset.range k) (fun i => ((n - i : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [Nat.cast_sub]
      exact le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hk
    rw [hEq]
    simp [Nat.descFactorial_eq_prod_range]
  have hFacNeZero : (Nat.factorial (n - k) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hNat : (n - k).factorial * n.descFactorial k = n.factorial :=
    Nat.factorial_mul_descFactorial hk
  have hCast :
      (Nat.factorial (n - k) : ℝ) * (n.descFactorial k : ℝ) = (Nat.factorial n : ℝ) := by
    exact_mod_cast hNat
  have hDescRatio :
      (n.descFactorial k : ℝ) = (Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ) := by
    apply (eq_div_iff hFacNeZero).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hCast
  calc
    Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) = (n.descFactorial k : ℝ) := hProdDesc
    _ = (Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ) := hDescRatio

/-- Helper for Proposition 4.2.6: the falling-product coefficient vanishes
when `k > n`. -/
lemma helperForProposition_4_2_6_fallingProd_eq_zero_of_lt
    (n : ℕ) {k : ℕ} (hnk : n < k) :
    Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) = 0 := by
  apply (Finset.prod_eq_zero_iff).2
  refine ⟨n, Finset.mem_range.mpr hnk, ?_⟩
  simp

/-- Proposition 4.2.6: let `n : ℕ` and `a c : ℝ`, and define
`f(x) = c * (x - a)^n`. Then `f` is infinitely differentiable on `ℝ`.
Moreover, for every `k` with `k ≤ n`,
`iteratedDeriv k f x = c * (n! / (n-k)!) * (x-a)^(n-k)` for all `x : ℝ`,
and for every `k > n`, `iteratedDeriv k f x = 0` for all `x : ℝ`. -/
theorem iteratedDeriv_monomial_shifted_const_mul
    (n : ℕ) (a c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ => c * (x - a) ^ n) ∧
      (∀ k : ℕ, k ≤ n →
        ∀ x : ℝ,
          iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x =
            c * ((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ)) * (x - a) ^ (n - k)) ∧
      (∀ k : ℕ, n < k →
        ∀ x : ℝ,
          iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x = 0) := by
  constructor
  · exact helperForProposition_4_2_6_contDiff_shiftedMonomial_constMul n a c
  constructor
  · intro k hk x
    calc
      iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x
          = c * (Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k)) :=
            helperForProposition_4_2_6_iteratedDeriv_constMul_shiftedMonomial_fallingProd n k a c x
      _ = c * (((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ)) * (x - a) ^ (n - k)) := by
            rw [helperForProposition_4_2_6_fallingProd_eq_factorialRatio n hk]
      _ = c * ((Nat.factorial n : ℝ) / (Nat.factorial (n - k) : ℝ)) * (x - a) ^ (n - k) := by
            rw [mul_assoc]
  · intro k hnk x
    calc
      iteratedDeriv k (fun y : ℝ => c * (y - a) ^ n) x
          = c * (Finset.prod (Finset.range k) (fun i => ((n : ℝ) - i)) * (x - a) ^ (n - k)) :=
            helperForProposition_4_2_6_iteratedDeriv_constMul_shiftedMonomial_fallingProd n k a c x
      _ = 0 := by
            rw [helperForProposition_4_2_6_fallingProd_eq_zero_of_lt n hnk]
            simp

/-- Proposition 4.2.7: let a, b ∈ ℝ and n ≥ 0 be an integer. Then for every x ∈ ℝ,
(x - a)^n = ∑_{m=0}^n (n! / (m!(n-m)!)) (b - a)^(n-m) (x - b)^m. -/
theorem shiftedPower_eq_sum_factorial_ratio_mul_shiftedPowers
    (a b : ℝ) (n : ℕ) (x : ℝ) :
    (x - a) ^ n =
      Finset.sum (Finset.range (n + 1))
        (fun m =>
          ((Nat.factorial n : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
            (b - a) ^ (n - m) * (x - b) ^ m) := by
  calc
    (x - a) ^ n = ((x - b) + (b - a)) ^ n := by ring
    _ =
        Finset.sum (Finset.range (n + 1))
          (fun m =>
            (x - b) ^ m * (b - a) ^ (n - m) * (Nat.choose n m : ℝ)) := by
            simpa [Finset.sum_range] using add_pow (x - b) (b - a) n
    _ =
        Finset.sum (Finset.range (n + 1))
          (fun m =>
            ((Nat.factorial n : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial (n - m) : ℝ))) *
              (b - a) ^ (n - m) * (x - b) ^ m) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            have hmle : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
            rw [Nat.cast_choose (K := ℝ) hmle]
            simp [mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 4.2.8: convert `|x| < r` with `r > 0` into
the geometric-series ratio bound `|x / r| < 1`. -/
lemma helperForProposition_4_2_8_absRatio_lt_one
    (r x : ℝ) (hr : 0 < r) (hx : |x| < r) :
    |x / r| < 1 := by
  rw [abs_div, abs_of_pos hr]
  exact (div_lt_one hr).2 hx

/-- Helper for Proposition 4.2.8: rewrite powers of `x / r` into
`x^n * (r⁻¹)^n`. -/
lemma helperForProposition_4_2_8_geometricRatioPow_rewrite
    (r x : ℝ) :
    (fun n : ℕ => (x / r) ^ n) = (fun n : ℕ => x ^ n * (r⁻¹) ^ n) := by
  funext n
  rw [div_eq_mul_inv, mul_pow]

/-- Helper for Proposition 4.2.8: identify the scaled rational expression with
the closed form of the geometric series. -/
lemma helperForProposition_4_2_8_scaledFraction_eq_geometricClosedForm
    (r x : ℝ) (hr : 0 < r) (hx : |x| < r) :
    r / (r - x) = (1 - x / r)⁻¹ := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hxRight : x < r := (abs_lt.mp hx).2
  have hsubPos : 0 < r - x := sub_pos.mpr hxRight
  have hsub : r - x ≠ 0 := ne_of_gt hsubPos
  have hRewrite : 1 - x / r = (r - x) / r := by
    calc
      1 - x / r = r / r - x / r := by rw [div_self hr0]
      _ = (r - x) / r := by rw [sub_div]
  calc
    r / (r - x) = ((r - x) / r)⁻¹ := by
      field_simp [hr0, hsub]
    _ = (1 - x / r)⁻¹ := by
      rw [hRewrite]

/-- Proposition 4.2.8: if `r > 0` and `|x| < r`, then
`r / (r - x) = ∑' n = 0..∞, x^n r^{-n}`. -/
theorem scaledGeometricSeries_tsum_eq_r_div_r_sub
    (r x : ℝ) (hr : 0 < r) (hx : |x| < r) :
    r / (r - x) = ∑' n : ℕ, x ^ n * (r⁻¹) ^ n := by
  have hRatio : |x / r| < 1 :=
    helperForProposition_4_2_8_absRatio_lt_one r x hr hx
  have hClosed : r / (r - x) = (1 - x / r)⁻¹ :=
    helperForProposition_4_2_8_scaledFraction_eq_geometricClosedForm r x hr hx
  have hPowRewrite :
      (fun n : ℕ => (x / r) ^ n) = (fun n : ℕ => x ^ n * (r⁻¹) ^ n) :=
    helperForProposition_4_2_8_geometricRatioPow_rewrite r x
  have hTsumRewrite :
      (∑' n : ℕ, (x / r) ^ n) = ∑' n : ℕ, x ^ n * (r⁻¹) ^ n := by
    exact congrArg tsum hPowRewrite
  calc
    r / (r - x) = (1 - x / r)⁻¹ := hClosed
    _ = ∑' n : ℕ, (x / r) ^ n := by
      symm
      exact tsum_geometric_of_abs_lt_one hRatio
    _ = ∑' n : ℕ, x ^ n * (r⁻¹) ^ n := hTsumRewrite


/-- Helper for Proposition 4.2.9: rewrite the factorial-ratio summand into a
constant multiple of the standard choose-geometric term. -/
lemma helperForProposition_4_2_9_factorialRatioTerm_eq_scaledChooseGeometricTerm
    (r x : ℝ) (m n : ℕ) :
    ((Nat.factorial (n + m) : ℝ) /
        ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
      x ^ n * (r⁻¹) ^ (n + m) =
      (r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n) := by
  have hchoose :
      ((Nat.factorial (n + m) : ℝ) /
          ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) =
        (Nat.choose (n + m) m : ℝ) := by
    symm
    simpa [Nat.add_sub_cancel] using
      (Nat.cast_choose (K := ℝ) (a := m) (b := n + m) (Nat.le_add_left m n))
  have hpow : x ^ n * (r⁻¹) ^ n = (x / r) ^ n := by
    rw [div_eq_mul_inv, mul_pow]
  calc
    ((Nat.factorial (n + m) : ℝ) /
          ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
        x ^ n * (r⁻¹) ^ (n + m)
        = (Nat.choose (n + m) m : ℝ) * x ^ n * (r⁻¹) ^ (n + m) := by
          rw [hchoose]
    _ = (Nat.choose (n + m) m : ℝ) * x ^ n * ((r⁻¹) ^ n * (r⁻¹) ^ m) := by
          rw [pow_add]
    _ = (Nat.choose (n + m) m : ℝ) * (x ^ n * (r⁻¹) ^ n) * (r⁻¹) ^ m := by
          ac_rfl
    _ = (Nat.choose (n + m) m : ℝ) * (x / r) ^ n * (r⁻¹) ^ m := by
          rw [hpow]
    _ = (r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n) := by
          ac_rfl

/-- Helper for Proposition 4.2.9: rewrite the left-hand side as the scaled
closed form matching the choose-geometric generating function. -/
lemma helperForProposition_4_2_9_lhs_eq_scaledClosedForm
    (r x : ℝ) (m : ℕ) (hr : 0 < r) (hx : |x| < r) :
    r / (r - x) ^ (m + 1) = (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hbase : r / (r - x) = (1 - x / r)⁻¹ :=
    helperForProposition_4_2_8_scaledFraction_eq_geometricClosedForm r x hr hx
  have hmul : (r⁻¹) ^ m * r ^ (m + 1) = r := by
    calc
      (r⁻¹) ^ m * r ^ (m + 1) = (r⁻¹) ^ m * (r ^ m * r) := by rw [pow_succ]
      _ = ((r⁻¹) ^ m * r ^ m) * r := by rw [mul_assoc]
      _ = ((r⁻¹ * r) ^ m) * r := by rw [← mul_pow]
      _ = (1 : ℝ) ^ m * r := by rw [inv_mul_cancel₀ hr0]
      _ = r := by simp
  have hEq :
      (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1)) = r / (r - x) ^ (m + 1) := by
    calc
      (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1))
          = (r⁻¹) ^ m * (((1 - x / r) ^ (m + 1))⁻¹) := by
            simp [one_div]
      _ = (r⁻¹) ^ m * (((1 - x / r)⁻¹) ^ (m + 1)) := by
            rw [← inv_pow]
      _ = (r⁻¹) ^ m * ((r / (r - x)) ^ (m + 1)) := by
            rw [hbase]
      _ = (r⁻¹) ^ m * (r ^ (m + 1) / (r - x) ^ (m + 1)) := by
            rw [div_pow]
      _ = ((r⁻¹) ^ m * r ^ (m + 1)) / (r - x) ^ (m + 1) := by
            rw [mul_div_assoc]
      _ = r / (r - x) ^ (m + 1) := by
            rw [hmul]
  exact hEq.symm

/-- Helper for Proposition 4.2.9: evaluate the reindexed factorial-ratio series
as the same scaled closed form. -/
lemma helperForProposition_4_2_9_tsum_targetTerm_eq_scaledClosedForm
    (r x : ℝ) (m : ℕ) (hr : 0 < r) (hx : |x| < r) :
    (∑' n : ℕ,
        ((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          x ^ n * (r⁻¹) ^ (n + m)) =
      (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1)) := by
  have hRatio : |x / r| < 1 :=
    helperForProposition_4_2_8_absRatio_lt_one r x hr hx
  have htermRewrite :
      (fun n : ℕ =>
        ((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          x ^ n * (r⁻¹) ^ (n + m)) =
        (fun n : ℕ => (r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n)) := by
    funext n
    exact
      helperForProposition_4_2_9_factorialRatioTerm_eq_scaledChooseGeometricTerm
        r x m n
  calc
    (∑' n : ℕ,
        ((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          x ^ n * (r⁻¹) ^ (n + m))
        = ∑' n : ℕ, (r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n) := by
          exact congrArg tsum htermRewrite
    _ = (r⁻¹) ^ m * (∑' n : ℕ, (Nat.choose (n + m) m : ℝ) * (x / r) ^ n) := by
          rw [tsum_mul_left]
    _ = (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1)) := by
          rw [tsum_choose_mul_geometric_of_norm_lt_one m hRatio]

/-- Helper for Proposition 4.2.9: absolute convergence of the reindexed
factorial-ratio series for `|x| < r`. -/
lemma helperForProposition_4_2_9_summable_abs_targetTerm
    (r x : ℝ) (m : ℕ) (hr : 0 < r) (hx : |x| < r) :
    Summable
      (fun n : ℕ =>
        |((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          x ^ n * (r⁻¹) ^ (n + m)|) := by
  have hRatio : |x / r| < 1 :=
    helperForProposition_4_2_8_absRatio_lt_one r x hr hx
  have hSummableChoose :
      Summable (fun n : ℕ => (Nat.choose (n + m) m : ℝ) * (x / r) ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one m hRatio
  have hSummableScaled :
      Summable (fun n : ℕ => (r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n)) :=
    hSummableChoose.mul_left ((r⁻¹) ^ m)
  have hAbsRewrite :
      (fun n : ℕ =>
        |((Nat.factorial (n + m) : ℝ) /
            ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
          x ^ n * (r⁻¹) ^ (n + m)|) =
        (fun n : ℕ => |(r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n)|) := by
    funext n
    rw [helperForProposition_4_2_9_factorialRatioTerm_eq_scaledChooseGeometricTerm r x m n]
  rw [hAbsRewrite]
  have hNorm :
      Summable
        (fun n : ℕ =>
          ‖(r⁻¹) ^ m * ((Nat.choose (n + m) m : ℝ) * (x / r) ^ n)‖) :=
    hSummableScaled.norm
  simpa [Real.norm_eq_abs, abs_div] using hNorm

/-- Proposition 4.2.9: if `r > 0`, `m : ℕ`, and `|x| < r`, then
`r / (r - x)^(m+1)` equals the binomial-coefficient power series, written in the
reindexed form `∑' n, ((n+m)!/(m!n!)) x^n r^{-(n+m)}` (equivalent to summing from
`n = m`); moreover this series converges absolutely for every such `x`. -/
theorem scaledGeometricSeries_higherDerivative_tsum_and_absConvergence
    (r x : ℝ) (m : ℕ) (hr : 0 < r) (hx : |x| < r) :
    r / (r - x) ^ (m + 1) =
        ∑' n : ℕ,
          ((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            x ^ n * (r⁻¹) ^ (n + m) ∧
      Summable
        (fun n : ℕ =>
          |((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            x ^ n * (r⁻¹) ^ (n + m)|) := by
  constructor
  · calc
      r / (r - x) ^ (m + 1) = (r⁻¹) ^ m * (1 / (1 - x / r) ^ (m + 1)) :=
        helperForProposition_4_2_9_lhs_eq_scaledClosedForm r x m hr hx
      _ =
          ∑' n : ℕ,
            ((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
              x ^ n * (r⁻¹) ^ (n + m) := by
            symm
            exact
              helperForProposition_4_2_9_tsum_targetTerm_eq_scaledClosedForm
                r x m hr hx
  · exact helperForProposition_4_2_9_summable_abs_targetTerm r x m hr hx

/-- Helper for Proposition 4.2.10: if `s > 0` then `(b - s, b + s)` is nonempty. -/
lemma helperForProposition_4_2_10_interval_left_right_strict
    (b s : ℝ) (hs : 0 < s) :
    b - s < b + s := by
  linarith

/-- Helper for Proposition 4.2.10: inclusion of open intervals yields endpoint bounds. -/
lemma helperForProposition_4_2_10_endpoint_bounds_of_Ioo_subset
    (a0 b r s : ℝ) (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo (a0 - r) (a0 + r)) :
    (a0 - r ≤ b - s) ∧ (b + s ≤ a0 + r) := by
  exact
    (Set.Ioo_subset_Ioo_iff
      (helperForProposition_4_2_10_interval_left_right_strict b s hs)).1 hsub

/-- Helper for Proposition 4.2.10: endpoint bounds control center distance by `r - s`. -/
lemma helperForProposition_4_2_10_abs_le_radius_subradius
    (a0 b r s : ℝ)
    (hleft : a0 - r ≤ b - s) (hright : b + s ≤ a0 + r) :
    |a0 - b| ≤ r - s := by
  refine abs_le.mpr ?_
  constructor
  · linarith
  · linarith

/-- Helper for Proposition 4.2.10: a bound by `r - s` improves to a strict bound by `r`. -/
lemma helperForProposition_4_2_10_abs_lt_radius_of_subradius_bound
    (a0 b r s : ℝ) (habs : |a0 - b| ≤ r - s) (hs : 0 < s) :
    |a0 - b| < r := by
  have hrs : r - s < r := by
    linarith
  exact lt_of_le_of_lt habs hrs

/-- Proposition 4.2.10: let `E ⊆ ℝ`, let `a` be an interior point of `E`, and let
`f : E → ℝ` be real analytic at `a` with a power-series expansion
`f(x) = ∑' n, c n * (x-a)^n` converging for all `x ∈ (a-r, a+r)` for some `r > 0`.
If `(b-s, b+s)` with `s > 0` is any open interval contained in `(a-r, a+r)`, then
`|a-b| ≤ r-s`; in particular `|a-b| < r`. -/
theorem center_distance_le_radius_subradius_of_interval_subset
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)) :
    |(a : ℝ) - b| ≤ r - s ∧ |(a : ℝ) - b| < r := by
  have hendpoints :
      ((a : ℝ) - r ≤ b - s) ∧ (b + s ≤ (a : ℝ) + r) :=
    helperForProposition_4_2_10_endpoint_bounds_of_Ioo_subset (a : ℝ) b r s hs hsub
  have hAbsLe : |(a : ℝ) - b| ≤ r - s :=
    helperForProposition_4_2_10_abs_le_radius_subradius
      (a : ℝ) b r s hendpoints.1 hendpoints.2
  have hAbsLt : |(a : ℝ) - b| < r :=
    helperForProposition_4_2_10_abs_lt_radius_of_subradius_bound
      (a : ℝ) b r s hAbsLe hs
  constructor
  · exact hAbsLe
  · exact hAbsLt

/-- Helper for Proposition 4.2.11: the point `a + (r - ε)` lies in `(a-r, a+r)`
whenever `0 < ε < r`. -/
lemma helperForProposition_4_2_11_subradius_point_mem_interval
    (a r ε : ℝ) (hr : 0 < r) (hε0 : 0 < ε) (hεr : ε < r) :
    a + (r - ε) ∈ Set.Ioo (a - r) (a + r) := by
  refine Set.mem_Ioo.mpr ?_
  constructor <;> linarith

/-- Helper for Proposition 4.2.11: evaluating the interval summability hypothesis
at `x = a + (r - ε)` yields summability of `n ↦ c n * (r - ε)^n`. -/
lemma helperForProposition_4_2_11_summable_scaled_terms_at_subradius
    {E : Set ℝ} (a : E) {r ε : ℝ} (c : ℕ → ℝ)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hr : 0 < r) (hε0 : 0 < ε) (hεr : ε < r) :
    Summable (fun n : ℕ => c n * (r - ε) ^ n) := by
  have hx0 : (a : ℝ) + (r - ε) ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) :=
    helperForProposition_4_2_11_subradius_point_mem_interval (a : ℝ) r ε hr hε0 hεr
  have hsumx0 :
      Summable (fun n : ℕ => c n * (((a : ℝ) + (r - ε)) - (a : ℝ)) ^ n) :=
    hsummable ((a : ℝ) + (r - ε)) hx0
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsumx0

/-- Helper for Proposition 4.2.11: every summable real sequence has a uniform
absolute-value bound. -/
lemma helperForProposition_4_2_11_exists_abs_bound_of_summable
    (u : ℕ → ℝ) (hu : Summable u) :
    ∃ B : ℝ, ∀ n : ℕ, |u n| ≤ B := by
  have hcauchy :
      CauchySeq (fun n : ℕ => Finset.sum (Finset.range n) (fun k => u k)) := by
    simpa using hu.hasSum.tendsto_sum_nat.cauchySeq
  obtain ⟨B, hB⟩ := exists_norm_le_of_cauchySeq (f := u) hcauchy
  refine ⟨B, ?_⟩
  intro n
  simpa [Real.norm_eq_abs] using hB n

/-- Helper for Proposition 4.2.11: from a uniform bound on
`|c n * ρ^n|`, recover a coefficient bound with inverse powers. -/
lemma helperForProposition_4_2_11_coeff_bound_from_scaled_bound
    (c : ℕ → ℝ) {ρ K : ℝ} (hρ : 0 < ρ)
    (hK : ∀ n : ℕ, |c n * ρ ^ n| ≤ K) :
    ∀ n : ℕ, |c n| ≤ K * (ρ⁻¹) ^ n := by
  intro n
  have hAbsMul : |c n * ρ ^ n| = |c n| * ρ ^ n := by
    calc
      |c n * ρ ^ n| = |c n| * |ρ ^ n| := abs_mul (c n) (ρ ^ n)
      _ = |c n| * ρ ^ n := by
            rw [abs_of_nonneg (pow_nonneg (le_of_lt hρ) n)]
  have hScaled : |c n| * ρ ^ n ≤ K := by
    rw [← hAbsMul]
    exact hK n
  have hMulRight :
      (|c n| * ρ ^ n) * (ρ⁻¹) ^ n ≤ K * (ρ⁻¹) ^ n := by
    exact
      mul_le_mul_of_nonneg_right hScaled
        (pow_nonneg (inv_nonneg.mpr (le_of_lt hρ)) n)
  have hPowCancel : ρ ^ n * (ρ⁻¹) ^ n = (1 : ℝ) := by
    calc
      ρ ^ n * (ρ⁻¹) ^ n = (ρ * ρ⁻¹) ^ n := by
        simpa using (mul_pow ρ (ρ⁻¹) n).symm
      _ = (1 : ℝ) ^ n := by
            simp [hρ.ne']
      _ = 1 := by simp
  calc
    |c n| = (|c n| * ρ ^ n) * (ρ⁻¹) ^ n := by
      calc
        |c n| = |c n| * 1 := by simp
        _ = |c n| * (ρ ^ n * (ρ⁻¹) ^ n) := by rw [hPowCancel]
        _ = (|c n| * ρ ^ n) * (ρ⁻¹) ^ n := by ring
    _ ≤ K * (ρ⁻¹) ^ n := hMulRight

/-- Proposition 4.2.11: under the same hypotheses and notation as the preceding
power-series setup, for every `ε` with `0 < ε < r` there exists `C > 0` such that
`|c n| ≤ C * (r - ε)^{-n}` for all integers `n ≥ 0` (encoded with `n : ℕ`). -/
theorem powerSeries_coeff_norm_le_of_subradius
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    (ε : ℝ) (hε0 : 0 < ε) (hεr : ε < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |c n| ≤ C * ((r - ε)⁻¹) ^ n := by
  have hρε : 0 < r - ε := sub_pos.mpr hεr
  have hSummableScaled :
      Summable (fun n : ℕ => c n * (r - ε) ^ n) :=
    helperForProposition_4_2_11_summable_scaled_terms_at_subradius
      a c hsummable hr hε0 hεr
  obtain ⟨B, hB⟩ :=
    helperForProposition_4_2_11_exists_abs_bound_of_summable
      (fun n : ℕ => c n * (r - ε) ^ n) hSummableScaled
  have hBabs : ∀ n : ℕ, |c n * (r - ε) ^ n| ≤ |B| := by
    intro n
    exact le_trans (hB n) (le_abs_self B)
  have hCoeff : ∀ n : ℕ, |c n| ≤ |B| * ((r - ε)⁻¹) ^ n :=
    helperForProposition_4_2_11_coeff_bound_from_scaled_bound c hρε hBabs
  refine ⟨|B| + 1, ?_, ?_⟩
  · positivity
  · intro n
    have hPowNonneg : 0 ≤ ((r - ε)⁻¹) ^ n := by
      exact pow_nonneg (inv_nonneg.mpr (le_of_lt hρε)) n
    have hMonotone :
        |B| * ((r - ε)⁻¹) ^ n ≤ (|B| + 1) * ((r - ε)⁻¹) ^ n := by
      have hLe : |B| ≤ |B| + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hLe hPowNonneg
    exact le_trans (hCoeff n) hMonotone

/-- Proposition 4.2.12: under the hypotheses and notation of the local power-series
setup, if `(b-s, b+s) ⊆ (a-r, a+r)` with `s > 0`, then for every `m : ℕ` the shifted
coefficient series
`∑' n, ((n+m)!/(m!n!)) * (b-a)^n * c (n+m)` (equivalently the original sum from
`n = m`) is absolutely convergent; hence the corresponding `d_m` is well-defined. -/
theorem shifted_coeffSeries_absSummable_of_interval_subset
    {E : Set ℝ} (a : E) (f : E → ℝ)
    (hanalytic : IsRealAnalyticAt E f a)
    {r : ℝ} (hr : 0 < r) (c : ℕ → ℝ)
    (hI : Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r) ⊆ E)
    (hsummable :
      ∀ x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r),
        Summable (fun n : ℕ => c n * (x - (a : ℝ)) ^ n))
    (hpowerSeries :
      ∀ x (hx : x ∈ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)),
        f ⟨x, hI hx⟩ = ∑' n : ℕ, c n * (x - (a : ℝ)) ^ n)
    {b s : ℝ} (hs : 0 < s)
    (hsub : Set.Ioo (b - s) (b + s) ⊆ Set.Ioo ((a : ℝ) - r) ((a : ℝ) + r)) :
    ∀ m : ℕ,
      Summable
        (fun n : ℕ =>
          |((Nat.factorial (n + m) : ℝ) /
                ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
              (b - (a : ℝ)) ^ n * c (n + m)|) := by
  intro m
  have hDistLt : |b - (a : ℝ)| < r := by
    have hCenter :=
      center_distance_le_radius_subradius_of_interval_subset
        a f hanalytic hr c hI hsummable hpowerSeries hs hsub
    simpa [abs_sub_comm] using hCenter.2
  let ε : ℝ := (r - |b - (a : ℝ)|) / 2
  have hε0 : 0 < ε := by
    dsimp [ε]
    linarith [hDistLt]
  have hεr : ε < r := by
    dsimp [ε]
    linarith [hDistLt, abs_nonneg (b - (a : ℝ))]
  have hρ0 : 0 < r - ε := sub_pos.mpr hεr
  have hDistSubradius : |b - (a : ℝ)| < r - ε := by
    dsimp [ε]
    linarith [hDistLt]
  obtain ⟨C, hC0, hCbound⟩ :=
    powerSeries_coeff_norm_le_of_subradius
      a f hanalytic hr c hI hsummable hpowerSeries ε hε0 hεr
  let A : ℕ → ℝ := fun n =>
    ((Nat.factorial (n + m) : ℝ) /
        ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
      (b - (a : ℝ)) ^ n
  let target : ℕ → ℝ := fun n => |A n * c (n + m)|
  let majorant : ℕ → ℝ := fun n => C * |A n * ((r - ε)⁻¹) ^ (n + m)|
  have hSummableBase :
      Summable (fun n : ℕ => |A n * ((r - ε)⁻¹) ^ (n + m)|) := by
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using
      helperForProposition_4_2_9_summable_abs_targetTerm
        (r - ε) (b - (a : ℝ)) m hρ0 hDistSubradius
  have hSummableMajorant : Summable majorant := by
    simpa [majorant] using hSummableBase.mul_left C
  have hTargetNonneg : ∀ n : ℕ, 0 ≤ target n := by
    intro n
    exact abs_nonneg (A n * c (n + m))
  have hPointwise : ∀ n : ℕ, target n ≤ majorant n := by
    intro n
    have hCoeff : |c (n + m)| ≤ C * ((r - ε)⁻¹) ^ (n + m) := hCbound (n + m)
    have hPowNonneg : 0 ≤ ((r - ε)⁻¹) ^ (n + m) := by
      exact pow_nonneg (inv_nonneg.mpr (le_of_lt hρ0)) (n + m)
    have hMulCoeff :
        |A n| * |c (n + m)| ≤ |A n| * (C * ((r - ε)⁻¹) ^ (n + m)) := by
      exact mul_le_mul_of_nonneg_left hCoeff (abs_nonneg (A n))
    have hAbsMajorant :
        |A n * ((r - ε)⁻¹) ^ (n + m)| = |A n| * ((r - ε)⁻¹) ^ (n + m) := by
      rw [abs_mul, abs_of_nonneg hPowNonneg]
    calc
      target n = |A n| * |c (n + m)| := by
        dsimp [target]
        rw [abs_mul]
      _ ≤ |A n| * (C * ((r - ε)⁻¹) ^ (n + m)) := hMulCoeff
      _ = C * (|A n| * ((r - ε)⁻¹) ^ (n + m)) := by ring
      _ = C * |A n * ((r - ε)⁻¹) ^ (n + m)| := by rw [hAbsMajorant]
      _ = majorant n := by rfl
  have hSummableTarget : Summable target :=
    hSummableMajorant.of_nonneg_of_le hTargetNonneg hPointwise
  have hTargetEq :
      (fun n : ℕ =>
        |((Nat.factorial (n + m) : ℝ) /
              ((Nat.factorial m : ℝ) * (Nat.factorial n : ℝ))) *
            (b - (a : ℝ)) ^ n * c (n + m)|) = target := by
    funext n
    simp [target, A, mul_assoc]
  rw [hTargetEq]
  exact hSummableTarget

end Section02
end Chap04

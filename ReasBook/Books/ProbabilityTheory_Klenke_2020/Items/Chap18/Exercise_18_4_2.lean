/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Exercise_18_4_1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/-- Helper for Exercise 18.4.2: the interval hypothesis forces the scale `σ` to be positive. -/
lemma gamblerRuinSigma_pos_of_mem_Ioo {r x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    0 < gamblerRuinSigma r := by
  -- Proof comment: the two strict inequalities imply `-σ < σ`, hence `σ > 0`.
  nlinarith [hx.1, hx.2]

/-- Helper for Exercise 18.4.2: normalizing by `σ` sends `(-σ, σ)` into `(-1, 1)`. -/
lemma abs_div_gamblerRuinSigma_lt_one {r x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    |x / gamblerRuinSigma r| < 1 := by
  let σ := gamblerRuinSigma r
  have hσpos : 0 < σ := by
    simpa [σ] using gamblerRuinSigma_pos_of_mem_Ioo (r := r) (x := x) hx
  -- Proof comment: divide the interval bounds by the positive scale `σ`.
  refine abs_lt.mpr ?_
  constructor
  · exact (lt_div_iff₀ hσpos).2 (by simpa [σ] using hx.1)
  · exact (div_lt_iff₀ hσpos).2 (by simpa [σ] using hx.2)

/-- Helper for Exercise 18.4.2: on the source interval, `σ²` is the gambler's ruin variance
parameter `4 r (1 - r)`. -/
lemma gamblerRuinSigma_sq_of_mem_Ioo {r x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    gamblerRuinSigma r ^ (2 : ℕ) = 4 * r * (1 - r) := by
  have hσpos := gamblerRuinSigma_pos_of_mem_Ioo (r := r) (x := x) hx
  have hradicand : 0 < 4 * r * (1 - r) := by
    -- Proof comment: a positive square root can only come from a positive radicand.
    exact Real.sqrt_pos.mp (by simpa [gamblerRuinSigma] using hσpos)
  -- Proof comment: now `sq_sqrt` identifies the square of `σ` with its radicand.
  rw [gamblerRuinSigma]
  exact Real.sq_sqrt hradicand.le

/-- Helper for Exercise 18.4.2: the evaluated characteristic-polynomial recursion matches the
corresponding Chebyshev-`U` recursion at the normalized point `x / σ`. -/
lemma gamblerRuinCharacteristicPolynomial_eval_eq_chebyshevU {r x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) (n : ℕ) :
    (gamblerRuinCharacteristicPolynomial r n).eval x =
      (-1 : ℝ) ^ n * (gamblerRuinSigma r / 2) ^ n * (1 - x) ^ (2 : ℕ) *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / gamblerRuinSigma r) := by
  have hσne : gamblerRuinSigma r ≠ 0 := (gamblerRuinSigma_pos_of_mem_Ioo (r := r) (x := x) hx).ne'
  have hσsq := gamblerRuinSigma_sq_of_mem_Ioo (r := r) (x := x) hx
  -- Route correction: the imported Exercise 18.4.1 statement is misindexed for this file, so we
  -- rebuild the evaluated Chebyshev bridge directly from the recursion.
  induction n using Nat.twoStepInduction with
  | zero =>
      -- Proof comment: the initial value `χ₁ = (1 - X)^2` matches `U₀ = 1`.
      simp [gamblerRuinCharacteristicPolynomial_chi_one, Polynomial.Chebyshev.U_zero]
  | one =>
      -- Proof comment: the initial value `χ₂ = -X (1 - X)^2` matches `U₁(y) = 2 y`.
      simp [gamblerRuinCharacteristicPolynomial_chi_two, Polynomial.Chebyshev.U_one]
      field_simp [hσne]
  | more n ih1 ih2 =>
      -- Proof comment: substitute both induction hypotheses into the characteristic recursion and
      -- then use the `U_{n+2}` recursion together with `σ² = 4 r (1 - r)`.
      have hrMul : r * (1 - r) = gamblerRuinSigma r ^ (2 : ℕ) / 4 := by
        linarith [hσsq]
      rw [gamblerRuinCharacteristicPolynomial_recurrence]
      simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ih1, ih2]
      field_simp [hσne]
      rw [hrMul]
      ring

/-- Helper for Exercise 18.4.2: on `(-1,1)`, the Chebyshev polynomial `U_n` evaluates to the
standard sine quotient. -/
lemma chebyshevUEval_eq_sineDivSqrt {y : ℝ} (hy : |y| < 1) (n : ℕ) :
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
      Real.sin ((n + 1 : ℝ) * Real.arccos y) / Real.sqrt (1 - y ^ (2 : ℕ)) := by
  have hyl : -1 ≤ y := (abs_lt.mp hy).1.le
  have hyr : y ≤ 1 := (abs_lt.mp hy).2.le
  have hsqrtne : Real.sqrt (1 - y ^ (2 : ℕ)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.2
    nlinarith [(abs_lt.mp hy).1, (abs_lt.mp hy).2]
  have hU := Polynomial.Chebyshev.U_real_cos (θ := Real.arccos y) (n := (n : ℤ))
  -- Proof comment: evaluate `U_n` at `cos (arccos y)` and then divide by the nonzero sine term.
  exact (eq_div_iff hsqrtne).2 <| by
    simpa [Real.cos_arccos hyl hyr, Real.sin_arccos, pow_two] using hU

/-- Helper for Exercise 18.4.2: reindexing `k = j + 1` turns a range product into an interval
product over `1, ..., n`. -/
lemma prod_range_succ_eq_prod_Icc {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    Finset.prod (Finset.range n) (fun k ↦ f (k + 1)) = ∏ k ∈ Finset.Icc 1 n, f k := by
  classical
  -- Proof comment: the bijection `k ↦ k + 1` sends `range n` onto `Icc 1 n`.
  refine Finset.prod_nbij (fun k ↦ k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_succ (Nat.zero_le k), Nat.succ_le_of_lt (Finset.mem_range.mp hk)⟩
  · intro a ha b hb hab
    exact Nat.succ.inj hab
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ n := (Finset.mem_Icc.mp hk).2
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa [Nat.add_comm] using Nat.sub_add_cancel hk1
  · intro a ha
    rfl

/-- Helper for Exercise 18.4.2: the Chebyshev polynomial `U_n` factors over its real roots in the
exact interval-product form used by the source formula. -/
lemma chebyshevUEval_eq_rootProduct (n : ℕ) (y : ℝ) :
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
      ((2 : ℝ) ^ n * (∏ k ∈ Finset.Icc 1 n, (y - Real.cos (Real.pi * k / (n + 1))))) := by
  have hroots : Multiset.card (Polynomial.Chebyshev.U ℝ n).roots =
      (Polynomial.Chebyshev.U ℝ n).natDegree := by
    rw [Polynomial.Chebyshev.roots_U_real, Polynomial.Chebyshev.natDegree_U_natCast]
    simpa using Finset.card_image_of_injOn
      ((Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n))
  have hprod :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Polynomial.Chebyshev.U ℝ n) hroots
  have hEval := congrArg (fun p : Polynomial ℝ ↦ p.eval y) hprod
  have hinj :
      Set.InjOn (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))) (Finset.range n) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n))
  have hRangeImage :
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod ((Finset.range n).image (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))))
            (fun z ↦ y - z)) := by
    -- Proof comment: evaluate the factorization theorem at `y` and simplify each linear factor.
    simpa [Polynomial.Chebyshev.roots_U_real, Polynomial.Chebyshev.leadingCoeff_U_natCast,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Polynomial.eval_sub,
      Polynomial.eval_X, mul_comm, mul_left_comm, mul_assoc] using hEval.symm
  have hRange :
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := by
    calc
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
          ((2 : ℝ) ^ n *
            Finset.prod
              ((Finset.range n).image (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))))
              (fun z ↦ y - z)) := hRangeImage
      _ =
          ((2 : ℝ) ^ n *
            Finset.prod (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := by
        congr 1
        exact Finset.prod_image hinj
  -- Proof comment: rewrite the range product as the interval product from the statement.
  calc
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := hRange
    _ =
        ((2 : ℝ) ^ n *
          ∏ k ∈ Finset.Icc 1 n, (y - Real.cos (Real.pi * k / (n + 1)))) := by
      congr 1
      simpa using prod_range_succ_eq_prod_Icc n
        (fun k ↦ y - Real.cos (Real.pi * k / (n + 1)))

/-- Helper for Exercise 18.4.2: after factoring each root term as `(-1 / σ) * (σ c - x)`, all
global scaling constants cancel. -/
lemma scaledChebyshevRootProduct_eq_gamblerRuinProduct {σ x : ℝ} {n : ℕ} (hσne : σ ≠ 0) :
    (-1 : ℝ) ^ n * (σ / 2) ^ n * (2 : ℝ) ^ n *
        ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1))) =
      ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x) := by
  have hprod :
      ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1))) =
        ∏ k ∈ Finset.Icc 1 n, ((-1 / σ) * (σ * Real.cos (Real.pi * k / (n + 1)) - x)) := by
    -- Proof comment: normalize each factor with a single field calculation.
    refine Finset.prod_congr rfl ?_
    intro k hk
    field_simp [hσne]
    ring
  have hscalar : (-1 : ℝ) ^ n * (σ / 2) ^ n * (2 : ℝ) ^ n * (-1 / σ) ^ n = 1 := by
    have hbase : (-1 : ℝ) * (σ / 2) * 2 * (-1 / σ) = 1 := by
      field_simp [hσne]
    -- Proof comment: combine the constant powers into one base and evaluate that base.
    repeat rw [← mul_pow]
    rw [hbase, one_pow]
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : (Finset.Icc 1 n).card = n := by
    simp
  rw [hcard]
  calc
    (-1 : ℝ) ^ n * (σ / 2) ^ n * (2 : ℝ) ^ n *
        (((-1 / σ) ^ n) * ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x)) =
      (((-1 : ℝ) ^ n * (σ / 2) ^ n * (2 : ℝ) ^ n * (-1 / σ) ^ n) *
        ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x)) := by
      ac_rfl
    _ = ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x) := by
      rw [hscalar, one_mul]

-- Proof sketch: rewrite the Chebyshev term in `(18.16)` using the standard identity
-- `U_{n-1}(cos θ) = sin (n θ) / sin θ` with `θ = arccos (x / σ)`, then use
-- `sin (arccos t) = √(1 - t^2)` and the factorization of the Chebyshev polynomial into its real
-- roots `cos (π k / N)` to obtain the product formula.
/-- Exercise 18.4.2: for the gambler's ruin characteristic polynomial from Example 18.20, the
Chebyshev formula from `(18.16)` for `χ_N`, namely
`(gamblerRuinCharacteristicPolynomial r (N - 1)).eval x`, agrees on `(-σ, σ)` both with the
trigonometric de Moivre formula and with the product factorization over the roots
`σ cos (π k / N)`. -/
theorem gamblerRuinCharacteristicPolynomial_eq_trigonometric_and_product_forms
    (r : ℝ) (N : ℕ) (hN : 2 ≤ N) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (-1 : ℝ) ^ (N - 1) * (gamblerRuinSigma r / 2) ^ (N - 1) * (1 - x) ^ (2 : ℕ) *
          (Real.sin (N * Real.arccos (x / gamblerRuinSigma r)) /
            Real.sqrt (1 - (x / gamblerRuinSigma r) ^ (2 : ℕ))) ∧
      (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (1 - x) ^ (2 : ℕ) *
          ∏ k ∈ Finset.Icc 1 (N - 1),
            (gamblerRuinSigma r * Real.cos (Real.pi * k / N) - x) := by
  let σ := gamblerRuinSigma r
  let n := N - 1
  have hn : n + 1 = N := by
    dsimp [n]
    omega
  have hnReal : (n : ℝ) + 1 = N := by
    exact_mod_cast hn
  have hσpos : 0 < σ := by
    simpa [σ] using gamblerRuinSigma_pos_of_mem_Ioo (r := r) (x := x) hx
  have hσne : σ ≠ 0 := hσpos.ne'
  have hy : |x / σ| < 1 := by
    simpa [σ] using abs_div_gamblerRuinSigma_lt_one (r := r) (x := x) hx
  have hEval := gamblerRuinCharacteristicPolynomial_eval_eq_chebyshevU (r := r) (x := x) hx n
  constructor
  · -- Proof comment: plug the Chebyshev bridge into the trigonometric evaluation formula for `U_n`.
    calc
      (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
          (-1 : ℝ) ^ n * (σ / 2) ^ n * (1 - x) ^ (2 : ℕ) *
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / σ) := by
        simpa [σ, n] using hEval
      _ =
          (-1 : ℝ) ^ n * (σ / 2) ^ n * (1 - x) ^ (2 : ℕ) *
            (Real.sin ((n + 1 : ℝ) * Real.arccos (x / σ)) /
              Real.sqrt (1 - (x / σ) ^ (2 : ℕ))) := by
        rw [chebyshevUEval_eq_sineDivSqrt hy]
      _ =
          (-1 : ℝ) ^ (N - 1) * (gamblerRuinSigma r / 2) ^ (N - 1) * (1 - x) ^ (2 : ℕ) *
            (Real.sin (N * Real.arccos (x / gamblerRuinSigma r)) /
              Real.sqrt (1 - (x / gamblerRuinSigma r) ^ (2 : ℕ))) := by
        simp [σ, n, hnReal]
  · -- Proof comment: use the root factorization of `U_n` and then cancel the scaling constants.
    calc
      (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
          (-1 : ℝ) ^ n * (σ / 2) ^ n * (1 - x) ^ (2 : ℕ) *
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / σ) := by
        simpa [σ, n] using hEval
      _ =
          (-1 : ℝ) ^ n * (σ / 2) ^ n * (1 - x) ^ (2 : ℕ) *
            ((2 : ℝ) ^ n *
              ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1)))) := by
        rw [chebyshevUEval_eq_rootProduct]
      _ =
          (1 - x) ^ (2 : ℕ) *
            (((-1 : ℝ) ^ n * (σ / 2) ^ n * (2 : ℝ) ^ n) *
              ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1)))) := by
        ac_rfl
      _ =
          (1 - x) ^ (2 : ℕ) *
            ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x) := by
        rw [scaledChebyshevRootProduct_eq_gamblerRuinProduct (n := n) (σ := σ) (x := x) hσne]
      _ =
          (1 - x) ^ (2 : ℕ) *
            ∏ k ∈ Finset.Icc 1 (N - 1), (gamblerRuinSigma r * Real.cos (Real.pi * k / N) - x) := by
        simp [σ, n, hnReal]

end ProbabilityTheory

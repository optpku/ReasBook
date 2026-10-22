/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped BigOperators Matrix
open Complex (exp I)

/-- The explicit real cosine matrix with first column `1 / √n` and remaining columns
`√(2 / n) * cos (((2 * i + 1) * j * π) / (2 * n))` in zero-based `Fin n` coordinates. -/
noncomputable def cosineMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if j.1 = 0 then
      1 / Real.sqrt n
    else
      Real.sqrt ((2 : ℝ) / n) *
        Real.cos (((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n))

/-- The entrywise formula for `cosineMatrix`. -/
theorem cosineMatrix_apply (n : ℕ) (i j : Fin n) :
    cosineMatrix n i j =
      if j.1 = 0 then
        1 / Real.sqrt n
      else
        Real.sqrt ((2 : ℝ) / n) *
          Real.cos (((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)) := by
  rfl

/-- Helper for Exercise 5.19: the product `T_j * T_k` has degree `< 2 * n` for
`j, k : Fin n`. -/
lemma chebyshevProduct_degree_lt_two_mul (n : ℕ) (j k : Fin n) :
    ((Polynomial.Chebyshev.T ℝ (j : ℤ)) * Polynomial.Chebyshev.T ℝ (k : ℤ)).degree < 2 * n := by
  -- Bound the product degree by the sum of the Chebyshev degrees.
  have hj : (Polynomial.Chebyshev.T ℝ (j : ℤ)).natDegree ≤ j := by
    simp [Polynomial.Chebyshev.natDegree_T]
  have hk : (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree ≤ k := by
    simp [Polynomial.Chebyshev.natDegree_T]
  have hmul :
      (((Polynomial.Chebyshev.T ℝ (j : ℤ)) * Polynomial.Chebyshev.T ℝ (k : ℤ))).natDegree ≤
        (j : ℕ) + k :=
    Polynomial.natDegree_mul_le_of_le hj hk
  have hjk : (j : ℕ) + k < 2 * n := by
    omega
  have hdeg :
      (((Polynomial.Chebyshev.T ℝ (j : ℤ)) * Polynomial.Chebyshev.T ℝ (k : ℤ))).degree ≤
        ((j : ℕ) + k : ℕ) :=
    Polynomial.degree_le_of_natDegree_le hmul
  exact lt_of_le_of_lt hdeg (by exact_mod_cast hjk)

/-- Helper for Exercise 5.19: the zero Chebyshev mode contributes `1` at every
odd Chebyshev-Gauss node. -/
lemma oddGridChebyshevModeSum_zero (n : ℕ) :
    ∑ i : Fin n,
      (Polynomial.Chebyshev.T ℝ 0).eval
        (Real.cos ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = n := by
  -- The zero Chebyshev mode is the constant polynomial `1`.
  simp

/-- Helper for Exercise 5.19: the odd-grid geometric denominator does not vanish
unless the mode is divisible by `2 * n`. -/
lemma oddGridExpSubOne_ne_zero {n : ℕ} {m : ℤ} (hn : n ≠ 0)
    (hm : ¬ (2 * n : ℤ) ∣ m) :
    exp (m / n * Real.pi * I) ≠ 1 := by
  -- Convert `exp z = 1` into an integral multiple of `2 * π * I`.
  contrapose! hm
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hm
  have hmul : m = 2 * n * k := by
    apply (@Int.cast_inj ℂ _ _).mp
    linear_combination
      (norm := (push_cast; field [show (n : ℂ) ≠ 0 by exact_mod_cast hn])) hk *
        ((n : ℂ) / Real.pi / I)
  exact ⟨k, hmul⟩

/-- Helper for Exercise 5.19: the odd-grid exponential mode sum has the same
closed form as in the Chebyshev-Gauss owner proof. -/
lemma oddGridExpSum_closedForm {n : ℕ} {m : ℤ} (hn : n ≠ 0)
    (hm : ¬ (2 * n : ℤ) ∣ m) :
    ∑ i ∈ Finset.range n, exp ((m * (((2 * i + 1 : ℝ) / (2 * n)) * Real.pi)) * I) =
      (exp (m / (2 * n) * Real.pi * I) / (exp (m / n * Real.pi * I) - 1)) * ((-1) ^ m - 1) := by
  -- Multiply by the geometric denominator and rewrite the sum as a geometric series.
  suffices
      (∑ i ∈ Finset.range n, exp ((m * (((2 * i + 1 : ℝ) / (2 * n)) * Real.pi)) * I)) *
          exp (-(m / (2 * n) * Real.pi * I)) * (exp (m / n * Real.pi * I) - 1) =
        (-1) ^ m - 1 by
    rw [Complex.exp_neg] at this
    have hsolve {s a b t : ℂ} (h : s * a⁻¹ * b = t) (ha : a ≠ 0) (hb : b ≠ 0) :
        s = a / b * t := by
      linear_combination (norm := field) h * a / b
    exact hsolve this (Complex.exp_ne_zero _)
      (by simpa using sub_ne_zero.mpr (oddGridExpSubOne_ne_zero hn hm))
  convert! geom_sum_mul (exp (m / n * Real.pi * I)) n using 1
  · -- Normalize each odd-grid point into a geometric progression term.
    simp_rw [Finset.sum_mul]
    congr! 1 with i hi
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    have hnC : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    have harg :
        (m : ℂ) * ((((2 * i + 1 : ℂ) / (2 * n)) * Real.pi)) * I +
            -(m / (2 * n) * Real.pi * I) =
          (i : ℂ) * (m / n * Real.pi * I) := by
      field_simp [hnC]
      ring
    simp [harg]
  · -- The endpoint term is `exp (m * π * I) = (-1)^m`.
    rw [← Complex.exp_nat_mul,
      show (n * (m / n * Real.pi * I)) = m * (Real.pi * I) by
        field [show (n : ℂ) ≠ 0 by exact_mod_cast hn],
      Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- Helper for Exercise 5.19: the doubled cosine mode vanishes on the odd
Chebyshev-Gauss grid when the mode is not divisible by `2 * n`. -/
lemma oddGridCosDoubleModeSum_range_eq_zero (n : ℕ) (m : ℤ)
    (hm : ¬ (2 * n : ℤ) ∣ m) :
    ∑ i ∈ Finset.range n,
      2 * Real.cos ((m : ℝ) * ((((2 * i + 1 : ℝ) / (2 * n)) * Real.pi))) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- The empty odd grid contributes the empty sum.
    simp
  · -- Recombine the `m` and `-m` exponentials into `2 cos`.
    have hnegm : ¬ (2 * n : ℤ) ∣ -m := by
      intro hneg
      apply hm
      rcases hneg with ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      linarith
    suffices
        ∑ i ∈ Finset.range n,
          (2 * Real.cos ((m : ℝ) * ((((2 * i + 1 : ℝ) / (2 * n)) * Real.pi))) : ℂ) = 0 by
      norm_cast at this ⊢
    suffices
        ∑ i ∈ Finset.range n,
          2 * Complex.cos ((m : ℂ) * ((((2 * i + 1 : ℂ) / (2 * n)) * Real.pi))) = 0 by
      simpa [Complex.ofReal_cos] using this
    simp_rw [Complex.two_cos, ← neg_mul, ← Int.cast_neg]
    have hnegPow : (-1 : ℂ) ^ (-m) = (-1) ^ m := by
      rw [← Int.cast_negOnePow, ← Int.cast_negOnePow]
      simp
    have hsumPos := oddGridExpSum_closedForm hn hm
    have hsumNeg := oddGridExpSum_closedForm hn hnegm
    have hsumPos' :
        ∑ x ∈ Finset.range n, exp ((m : ℂ) * ((2 * (x : ℂ) + 1) / (2 * n) * Real.pi) * I) =
          exp ((m : ℂ) / (2 * n) * Real.pi * I) / (exp ((m : ℂ) / n * Real.pi * I) - 1) *
            ((-1) ^ m - 1) := by
      simpa using hsumPos
    have hsumNeg' :
        ∑ x ∈ Finset.range n, exp (((-m : ℤ) : ℂ) * ((2 * (x : ℂ) + 1) / (2 * n) * Real.pi) * I) =
          exp (((-m : ℤ) : ℂ) / (2 * n) * Real.pi * I) /
              (exp (((-m : ℤ) : ℂ) / n * Real.pi * I) - 1) * ((-1) ^ (-m) - 1) := by
      simpa using hsumNeg
    rw [Finset.sum_add_distrib, hsumPos', hsumNeg', Int.cast_neg, neg_div, neg_mul, neg_mul,
      Complex.exp_neg, neg_div, neg_mul, neg_mul, Complex.exp_neg]
    rw [hnegPow, ← add_mul, mul_eq_zero_of_left]
    set z : ℂ := exp (m / (2 * n) * Real.pi * I) with hz
    have hzSq : exp (m / n * Real.pi * I) = z ^ 2 := by
      rw [hz, ← Complex.exp_nat_mul]
      have hnC : (n : ℂ) ≠ 0 := by
        exact_mod_cast hn
      have harg : (2 : ℂ) * (m / (2 * n) * Real.pi * I) = m / n * Real.pi * I := by
        field_simp [hnC]
      simpa [pow_two, mul_assoc] using congrArg exp harg.symm
    rw [hzSq, ← inv_pow z 2]
    have hz_ne : z ≠ 0 := by
      rw [hz]
      exact Complex.exp_ne_zero _
    have hzSq_ne : z ^ 2 - 1 ≠ 0 := by
      intro hzero
      apply oddGridExpSubOne_ne_zero hn hm
      rw [hzSq]
      exact sub_eq_zero.mp hzero
    have hOneSq_ne : 1 - z ^ 2 ≠ 0 := by
      intro hzero
      apply oddGridExpSubOne_ne_zero hn hm
      rw [hzSq]
      exact (sub_eq_zero.mp hzero).symm
    field [hz_ne, hzSq_ne, hOneSq_ne]

/-- Helper for Exercise 5.19: the doubled cosine mode vanishes on the local
`Fin n` spelling of the odd Chebyshev-Gauss grid. -/
lemma oddGridCosDoubleModeSum_eq_zero (n : ℕ) (m : ℤ)
    (hm : ¬ (2 * n : ℤ) ∣ m) :
    ∑ i : Fin n,
      2 * Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
  -- Convert the owner-style `range n` sum to the local `Fin n` index set.
  have hsum :
      (∑ i : Fin n,
          2 * Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi)))) =
        ∑ i ∈ Finset.range n,
          2 * Real.cos ((m : ℝ) * ((((2 * i + 1 : ℝ) / (2 * n)) * Real.pi))) := by
    simpa using
      (Fin.sum_univ_eq_sum_range (n := n)
        (f := fun i : ℕ ↦
          2 * Real.cos ((m : ℝ) * ((((2 * i + 1 : ℝ) / (2 * n)) * Real.pi)))))
  calc
    ∑ i : Fin n,
        2 * Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) =
      ∑ i ∈ Finset.range n,
        2 * Real.cos ((m : ℝ) * ((((2 * i + 1 : ℝ) / (2 * n)) * Real.pi))) := hsum
    _ = 0 := oddGridCosDoubleModeSum_range_eq_zero n m hm

/-- Helper for Exercise 5.19: a Chebyshev mode with index not divisible by
`2 * n` sums to zero on the odd Chebyshev-Gauss grid. -/
lemma oddGridChebyshevModeSum_eq_zero (n : ℕ) (m : ℤ)
    (hm : ¬ (2 * n : ℤ) ∣ m) :
    ∑ i : Fin n,
      (Polynomial.Chebyshev.T ℝ m).eval
        (Real.cos ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
  -- Route correction: prove the explicit cosine vanishing first, then rewrite
  -- each Chebyshev evaluation by `T_real_cos` and cancel the scalar `2`.
  have hdouble :
      ∑ i : Fin n,
        2 * Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 :=
    oddGridCosDoubleModeSum_eq_zero n m hm
  have hcos :
      ∑ i : Fin n,
        Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
    -- Pull the common factor `2` out of the sum and cancel it.
    have hscaled :
        (2 : ℝ) *
            ∑ i : Fin n,
              Real.cos ((m : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
      simpa [two_mul, Finset.mul_sum] using hdouble
    exact (mul_eq_zero.mp hscaled).resolve_left two_ne_zero
  -- Replace the Chebyshev evaluations by the corresponding cosine mode values.
  simpa [Polynomial.Chebyshev.T_real_cos] using hcos

/-- Helper for Exercise 5.19: the odd Chebyshev-Gauss cosine grid is orthogonal
for Chebyshev evaluations indexed by `Fin n`. -/
lemma chebyshevGaussInner_evalT (n : ℕ) (hn : n ≠ 0) (j k : Fin n) :
    ∑ i : Fin n,
      (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval
          (Real.cos ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
          (Real.cos ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) =
      if j = k then if j.1 = 0 then (n : ℝ) else (n : ℝ) / 2 else 0 := by
  let node : Fin n → ℝ := fun i ↦ Real.cos ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))
  have hproduct :
      2 * ∑ i : Fin n,
        (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) *
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (node i) =
        ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) + k)).eval (node i) +
          ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) - k)).eval (node i) := by
    -- Evaluate `T_mul_T` at each node and sum the resulting identity.
    calc
      2 * ∑ i : Fin n,
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) *
            (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (node i) =
          ∑ i : Fin n,
            ((Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) +
                (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i)) *
              (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (node i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      _ = ∑ i : Fin n,
            ((Polynomial.Chebyshev.T ℝ ((j : ℤ) + k)).eval (node i) +
              (Polynomial.Chebyshev.T ℝ ((j : ℤ) - k)).eval (node i)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hpoint :=
          congrArg (fun P : Polynomial ℝ => P.eval (node i))
            (Polynomial.Chebyshev.T_mul_T (R := ℝ) (j : ℤ) (k : ℤ))
        simpa [two_mul, mul_assoc, mul_left_comm, mul_comm] using hpoint
      _ = ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) + k)).eval (node i) +
            ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) - k)).eval (node i) := by
        rw [Finset.sum_add_distrib]
  by_cases hjk : j = k
  · subst hjk
    by_cases hj0 : j.1 = 0
    · have hj : j = ⟨0, Nat.pos_of_ne_zero hn⟩ := by
        apply Fin.ext
        simpa using hj0
      subst hj
      -- The zero-frequency diagonal case is the constant-one sum.
      simp
    · have hj_pos : 0 < (j : ℤ) := by
        exact_mod_cast Nat.pos_of_ne_zero hj0
      have hj_lt : (j : ℤ) < n := by
        exact_mod_cast j.2
      have htwoj_pos : 0 < 2 * (j : ℤ) := by
        omega
      have htwoj_lt : 2 * (j : ℤ) < 2 * n := by
        omega
      have htwo_n_pos : 0 < (2 * n : ℤ) := by
        omega
      have htwoj_not_dvd : ¬ (2 * n : ℤ) ∣ 2 * (j : ℤ) := by
        refine (Int.not_dvd_iff_lt_mul_succ (2 * (j : ℤ)) htwo_n_pos).mpr ?_
        refine ⟨0, ?_⟩
        constructor
        · simpa using htwoj_pos
        · omega
      have hsumDouble :
          ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) + j)).eval (node i) = 0 := by
        simpa [node, two_mul] using oddGridChebyshevModeSum_eq_zero n (2 * (j : ℤ)) htwoj_not_dvd
      have hsumZero :
          ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) - j)).eval (node i) = n := by
        rw [sub_self]
        exact oddGridChebyshevModeSum_zero n
      have hsum :
          ∑ i : Fin n,
            (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) *
              (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) = (n : ℝ) / 2 := by
        -- The nonzero diagonal leaves only the zero mode after `T_mul_T`.
        rw [hsumDouble, hsumZero] at hproduct
        nlinarith
      simpa [node, hj0] using hsum
  · have hj_lt : (j : ℤ) < n := by
      exact_mod_cast j.2
    have hk_lt : (k : ℤ) < n := by
      exact_mod_cast k.2
    have hplus_pos : 0 < (j : ℤ) + k := by
      by_cases hj0 : j.1 = 0
      · have hk0 : k.1 ≠ 0 := by
          intro hk0
          apply hjk
          exact Fin.ext (hj0.trans hk0.symm)
        have hk_pos : 0 < (k : ℤ) := by
          exact_mod_cast Nat.pos_of_ne_zero hk0
        omega
      · have hj_pos : 0 < (j : ℤ) := by
          exact_mod_cast Nat.pos_of_ne_zero hj0
        omega
    have hplus_not_dvd : ¬ (2 * n : ℤ) ∣ (j : ℤ) + k := by
      have hplus_lt : (j : ℤ) + k < 2 * n := by
        omega
      have htwo_n_pos : 0 < (2 * n : ℤ) := by
        omega
      refine (Int.not_dvd_iff_lt_mul_succ ((j : ℤ) + k) htwo_n_pos).mpr ?_
      refine ⟨0, ?_⟩
      constructor
      · simpa using hplus_pos
      · simpa using hplus_lt
    have hsub_ne : (j : ℤ) - k ≠ 0 := by
      intro hsub
      have hEqInt : (j : ℤ) = k := by
        linarith
      apply hjk
      apply Fin.ext
      exact Int.ofNat.inj hEqInt
    have hminus_not_dvd : ¬ (2 * n : ℤ) ∣ (j : ℤ) - k := by
      have hminus_low : -(2 * n : ℤ) < (j : ℤ) - k := by
        omega
      have hminus_high : (j : ℤ) - k < 2 * n := by
        omega
      have htwo_n_pos : 0 < (2 * n : ℤ) := by
        omega
      by_cases hminus_pos : 0 < (j : ℤ) - k
      · refine (Int.not_dvd_iff_lt_mul_succ ((j : ℤ) - k) htwo_n_pos).mpr ?_
        refine ⟨0, ?_⟩
        constructor
        · simpa using hminus_pos
        · simpa using hminus_high
      · have hminus_neg : (j : ℤ) - k < 0 := by
          have hminus_nonpos : (j : ℤ) - k ≤ 0 := by
            linarith
          exact lt_of_le_of_ne hminus_nonpos hsub_ne
        refine (Int.not_dvd_iff_lt_mul_succ ((j : ℤ) - k) htwo_n_pos).mpr ?_
        refine ⟨-1, ?_⟩
        constructor
        · simpa using hminus_low
        · simpa using hminus_neg
    have hsumPlus :
        ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) + k)).eval (node i) = 0 := by
      simpa [node] using oddGridChebyshevModeSum_eq_zero n ((j : ℤ) + k) hplus_not_dvd
    have hsumMinus :
        ∑ i : Fin n, (Polynomial.Chebyshev.T ℝ ((j : ℤ) - k)).eval (node i) = 0 := by
      simpa [node] using oddGridChebyshevModeSum_eq_zero n ((j : ℤ) - k) hminus_not_dvd
    have hsum :
        ∑ i : Fin n,
          (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (node i) *
            (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (node i) = 0 := by
      -- Off-diagonal modes leave only vanishing nonzero frequencies.
      rw [hsumPlus, hsumMinus] at hproduct
      nlinarith
    simpa [node, hjk] using hsum

/-- Helper for Exercise 5.19: the odd Chebyshev-Gauss cosine grid is orthogonal
for the discrete cosine modes indexed by `Fin n`. -/
lemma chebyshevGaussInner_cos (n : ℕ) (hn : n ≠ 0) (j k : Fin n) :
    ∑ i : Fin n,
      Real.cos ((j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) *
        Real.cos ((k : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) =
      if j = k then if j.1 = 0 then (n : ℝ) else (n : ℝ) / 2 else 0 := by
  -- Route correction: work owner-to-target. First prove orthogonality for the
  -- Chebyshev evaluations, then convert those evaluations to cosines.
  simpa [Polynomial.Chebyshev.T_real_cos] using chebyshevGaussInner_evalT n hn j k

/-- Helper for Exercise 5.19: the cosine-matrix angle separates into a mode and
the odd Chebyshev-Gauss grid angle. -/
lemma cosineMatrix_angle_eq (n : ℕ) (hn : n ≠ 0) (i j : Fin n) :
    (((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)) =
      (j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi)) := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  field_simp [hnR]

/-- Helper for Exercise 5.19: each entry of `(cosineMatrix n)ᵀ * cosineMatrix n`
matches the identity matrix. -/
lemma cosineMatrix_transpose_mul_self_entry (n : ℕ) (hn : n ≠ 0) (j k : Fin n) :
    ((cosineMatrix n)ᵀ * cosineMatrix n) j k = (1 : Matrix (Fin n) (Fin n) ℝ) j k := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  have hsqrt : Real.sqrt n ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
  by_cases hj0 : j.1 = 0
  · by_cases hk0 : k.1 = 0
    · have hjk : j = k := Fin.ext (hj0.trans hk0.symm)
      -- The first column is constant, so its norm is the normalized cardinality sum.
      calc
        ((cosineMatrix n)ᵀ * cosineMatrix n) j k =
            ∑ i : Fin n, (1 / Real.sqrt n) * (1 / Real.sqrt n) := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, cosineMatrix_apply, hj0, hk0]
        _ = (n : ℝ) * ((1 / Real.sqrt n) * (1 / Real.sqrt n)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = 1 := by
          have hsq : (Real.sqrt n) ^ 2 = n := by
            rw [sq, Real.mul_self_sqrt]
            positivity
          field_simp [hsqrt]
          simp [hsq]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) j k := by
          rw [Matrix.one_apply]
          simp [hjk]
    · -- The first column is orthogonal to every nonzero cosine mode.
      have hjk : j ≠ k := by
        intro h
        exact hk0 (h ▸ hj0)
      have hsum :
          ∑ i : Fin n, Real.cos ((k : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
        simpa [hj0, hk0, hjk] using chebyshevGaussInner_cos n hn j k
      have hangle :
          (∑ i : Fin n, Real.cos ((((2 * (i : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n)))) =
            ∑ i : Fin n, Real.cos ((k : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [cosineMatrix_angle_eq n hn i k]
      calc
        ((cosineMatrix n)ᵀ * cosineMatrix n) j k =
            ∑ i : Fin n,
              (1 / Real.sqrt n) *
                (Real.sqrt ((2 : ℝ) / n) *
                  Real.cos ((((2 * (i : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n)))) := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, cosineMatrix_apply, hj0, hk0]
        _ = (1 / Real.sqrt n) *
              ∑ i : Fin n,
                Real.sqrt ((2 : ℝ) / n) *
                  Real.cos ((((2 * (i : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n))) := by
          rw [Finset.mul_sum]
        _ = (1 / Real.sqrt n) *
              (Real.sqrt ((2 : ℝ) / n) *
                ∑ i : Fin n, Real.cos ((((2 * (i : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n)))) := by
          congr 1
          rw [Finset.mul_sum]
        _ = ((1 / Real.sqrt n) * Real.sqrt ((2 : ℝ) / n)) *
              ∑ i : Fin n, Real.cos ((k : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) := by
          rw [hangle]
          ring
        _ = 0 := by
          rw [hsum]
          ring
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) j k := by
          rw [Matrix.one_apply]
          simp [hjk]
  · by_cases hk0 : k.1 = 0
    · -- Symmetry gives the mixed zero/nonzero column case.
      have hjk : j ≠ k := by
        intro h
        exact hj0 (h ▸ hk0)
      have hsum :
          ∑ i : Fin n, Real.cos ((j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) = 0 := by
        simpa [hj0, hk0, hjk] using chebyshevGaussInner_cos n hn j k
      have hangle :
          (∑ i : Fin n, Real.cos ((((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)))) =
            ∑ i : Fin n, Real.cos ((j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [cosineMatrix_angle_eq n hn i j]
      calc
        ((cosineMatrix n)ᵀ * cosineMatrix n) j k =
            ∑ i : Fin n,
              (Real.sqrt ((2 : ℝ) / n) *
                  Real.cos ((((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)))) *
                (1 / Real.sqrt n) := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, cosineMatrix_apply, hj0, hk0]
        _ = (∑ i : Fin n,
              Real.sqrt ((2 : ℝ) / n) *
                Real.cos ((((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)))) *
              (1 / Real.sqrt n) := by
          rw [Finset.sum_mul]
        _ = (Real.sqrt ((2 : ℝ) / n) *
              ∑ i : Fin n, Real.cos ((((2 * (i : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)))) *
              (1 / Real.sqrt n) := by
          congr 1
          rw [Finset.mul_sum]
        _ = (Real.sqrt ((2 : ℝ) / n) *
              ∑ i : Fin n, Real.cos ((j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi)))) *
              (1 / Real.sqrt n) := by
          rw [hangle]
        _ = 0 := by
          rw [hsum]
          ring
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) j k := by
          rw [Matrix.one_apply]
          simp [hjk]
    · -- The nonzero columns reduce to the discrete cosine orthogonality helper.
      have hsum :
          ∑ i : Fin n,
            Real.cos ((j : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) *
              Real.cos ((k : ℝ) * ((((2 * (i : ℝ) + 1) / (2 * n)) * Real.pi))) =
            if j = k then (n : ℝ) / 2 else 0 := by
        simpa [hj0, hk0] using chebyshevGaussInner_cos n hn j k
      have hangle :
          (∑ x : Fin n,
              Real.cos ((((2 * (x : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n))) *
                Real.cos ((((2 * (x : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n))) =
            ∑ x : Fin n,
              Real.cos ((j : ℝ) * ((((2 * (x : ℝ) + 1) / (2 * n)) * Real.pi))) *
                Real.cos ((k : ℝ) * ((((2 * (x : ℝ) + 1) / (2 * n)) * Real.pi)))) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [cosineMatrix_angle_eq n hn x j, cosineMatrix_angle_eq n hn x k]
      calc
        ((cosineMatrix n)ᵀ * cosineMatrix n) j k =
            ∑ x : Fin n,
              (Real.sqrt ((2 : ℝ) / n) *
                  Real.cos ((((2 * (x : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n)))) *
                (Real.sqrt ((2 : ℝ) / n) *
                  Real.cos ((((2 * (x : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n)))) := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, cosineMatrix_apply, hj0, hk0]
        _ = ∑ x : Fin n,
              (Real.sqrt ((2 : ℝ) / n) * Real.sqrt ((2 : ℝ) / n)) *
                (Real.cos ((((2 * (x : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n))) *
                  Real.cos ((((2 * (x : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n)))) := by
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          ring
        _ = (Real.sqrt ((2 : ℝ) / n) * Real.sqrt ((2 : ℝ) / n)) *
              ∑ x : Fin n,
                Real.cos ((((2 * (x : ℝ) + 1) * (j : ℝ) * Real.pi) / (2 * n))) *
                  Real.cos ((((2 * (x : ℝ) + 1) * (k : ℝ) * Real.pi) / (2 * n))) := by
          rw [Finset.mul_sum]
        _ = (Real.sqrt ((2 : ℝ) / n) * Real.sqrt ((2 : ℝ) / n)) *
              ∑ x : Fin n,
                Real.cos ((j : ℝ) * ((((2 * (x : ℝ) + 1) / (2 * n)) * Real.pi))) *
                  Real.cos ((k : ℝ) * ((((2 * (x : ℝ) + 1) / (2 * n)) * Real.pi))) := by
          rw [hangle]
        _ = (Real.sqrt ((2 : ℝ) / n) * Real.sqrt ((2 : ℝ) / n)) *
              (if j = k then (n : ℝ) / 2 else 0) := by
          rw [hsum]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) j k := by
          have hnonneg : 0 ≤ (2 : ℝ) / n := by
            positivity
          rw [Real.mul_self_sqrt hnonneg]
          by_cases hjk : j = k
          · have : (2 / (n : ℝ)) * ((n : ℝ) / 2) = 1 := by
              field_simp [hnR]
            rw [if_pos hjk, this]
            rw [Matrix.one_apply]
            simp [hjk]
          · rw [if_neg hjk]
            rw [Matrix.one_apply]
            simp [hjk]

/-- Exercise 5.19. The explicit cosine matrix belongs to the real orthogonal
group. -/
theorem cosineMatrix_mem_orthogonalGroup (n : ℕ) :
    cosineMatrix n ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  -- Check orthogonality entrywise through the transpose-times-self identity.
  rw [Matrix.mem_orthogonalGroup_iff']
  by_cases hn : n = 0
  · subst hn
    ext j k
    exact Fin.elim0 j
  · ext j k
    exact cosineMatrix_transpose_mul_self_entry n hn j k

/-- Source-facing bridge for Exercise 5.19: over `ℝ`, the cosine matrix is
unitary because `Matrix.orthogonalGroup (Fin n) ℝ` is definitionally
`Matrix.unitaryGroup (Fin n) ℝ`. -/
theorem cosineMatrix_mem_unitaryGroup (n : ℕ) :
    cosineMatrix n ∈ Matrix.unitaryGroup (Fin n) ℝ :=
  cosineMatrix_mem_orthogonalGroup n

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_20

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

noncomputable section

namespace ProbabilityTheory

/-- The source-facing shifted family `chi_(N+1)` from Example 18.20, determined by the initial
values `chi_1 = (1 - X)^2`, `chi_2 = -X (1 - X)^2`, and the recursion `(18.15)`. Its canonical
owner is the characteristic polynomial of `gamblerRuinTransitionMatrixReal`, related below by
`gamblerRuinTransitionMatrix_charpoly_eq`. -/
def gamblerRuinCharacteristicPolynomial (r : ℝ) : ℕ → ℝ[X]
  | 0 => (1 - X) ^ 2
  | 1 => -X * (1 - X) ^ 2
  | n + 2 =>
      -X * gamblerRuinCharacteristicPolynomial r (n + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r n

-- Proof sketch: unfold the recursive definition at index `0`; this is exactly the chosen initial
-- value corresponding to `chi_1` in Example 18.20.
/-- The initial polynomial `chi_1` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_one (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 0 = (1 - X) ^ 2 := by
  -- Proof comment: the `0`-th clause of the recursive definition is exactly `χ₁ = (1 - X)^2`.
  rfl

-- Proof sketch: unfold the recursive definition at index `1`; this is exactly the chosen initial
-- value corresponding to `chi_2` in Example 18.20.
/-- The initial polynomial `chi_2` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_two (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 1 = -X * (1 - X) ^ 2 := by
  -- Proof comment: the `1`-st clause of the recursive definition is exactly `χ₂ = -X (1 - X)^2`.
  rfl

-- Proof sketch: unfold the recursive clause of `gamblerRuinCharacteristicPolynomial`; it is the
-- recursion `(18.15)` rewritten in the shifted indexing used by this file.
/-- The recursion `(18.15)` for the shifted characteristic-polynomial family. -/
theorem gamblerRuinCharacteristicPolynomial_recurrence (r : ℝ) (N : ℕ) :
    gamblerRuinCharacteristicPolynomial r (N + 2) =
      -X * gamblerRuinCharacteristicPolynomial r (N + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r N := by
  -- Proof comment: the recursive clause of `gamblerRuinCharacteristicPolynomial` is precisely
  -- the shifted recursion `(18.15)`.
  rfl

-- Proof sketch: evaluate the polynomial recursion termwise and compare it with the already
-- established scalar recursion for `gamblerRuinCharacteristicValue`.
/-- Helper for Exercise 18.4.1: evaluating the shifted characteristic-polynomial family at `x`
produces the scalar recurrence value times the absorbing boundary factor `(1 - x)^2`. -/
lemma gamblerRuinCharacteristicPolynomial_eval (r x : ℝ) (n : ℕ) :
    (gamblerRuinCharacteristicPolynomial r n).eval x =
      ((-1 : ℝ) ^ n) * (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      -- Proof comment: the initial polynomial `χ₁` evaluates to the boundary square factor.
      simp [gamblerRuinCharacteristicPolynomial_chi_one, gamblerRuinCharacteristicValue]
  | one =>
      -- Proof comment: the initial polynomial `χ₂` adds the extra factor `-x`.
      simp [gamblerRuinCharacteristicPolynomial_chi_two, gamblerRuinCharacteristicValue]
      ring
  | more n ih1 ih2 =>
      -- Proof comment: evaluate the polynomial recursion termwise and match it with the scalar
      -- recursion defining `gamblerRuinCharacteristicValue`.
      rw [gamblerRuinCharacteristicPolynomial_recurrence]
      simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ih1, ih2,
        gamblerRuinCharacteristicValue]
      ring

-- Proof sketch: for `N = 1`, both boundary states are absorbing, so the transition matrix is the
-- identity matrix and its characteristic polynomial is `(X - 1)^2 = (1 - X)^2`.
/-- Helper for Exercise 18.4.1: the two-state gambler's ruin transition matrix has characteristic
polynomial `(1 - X)^2`. -/
lemma gamblerRuinTransitionMatrixReal_one_charpoly (r : ℝ) :
    (gamblerRuinTransitionMatrixReal 1 r).charpoly = (1 - X) ^ 2 := by
  have hId : gamblerRuinTransitionMatrixReal 1 r = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    -- Proof comment: when `N = 1`, both states are boundary states, so every off-diagonal entry
    -- vanishes and the two diagonal entries are `1`.
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gamblerRuinTransitionMatrixReal]
  calc
    (gamblerRuinTransitionMatrixReal 1 r).charpoly = (1 : Matrix (Fin 2) (Fin 2) ℝ).charpoly := by
      rw [hId]
    _ = (X - 1) ^ 2 := by
      simpa using (Matrix.charpoly_one (n := Fin 2) (R := ℝ))
    _ = (1 - X) ^ 2 := by
      ring

-- Proof sketch: evaluate the closed-form polynomial directly at `x`, rewrite the Chebyshev term
-- using the imported scalar formula, and then regroup the scalar factors.
/-- Helper for Exercise 18.4.1: the polynomial closed form from `(18.16)` evaluates to the same
scalar recurrence expression as `gamblerRuinCharacteristicPolynomial`. -/
lemma gamblerRuinChebyshevClosedForm_eval {r x : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (C (((-1 : ℝ) ^ n) * ((gamblerRuinSigma r / 2) ^ n)) * (1 - X) ^ 2 *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).comp (C ((gamblerRuinSigma r)⁻¹) * X)).eval x =
      ((-1 : ℝ) ^ n) * (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x n := by
  -- Proof comment: evaluate the closed-form polynomial termwise and then substitute the imported
  -- scalar Chebyshev formula for `gamblerRuinCharacteristicValue`.
  rw [gamblerRuinCharacteristicValue_eq_chebyshevEval hr0 hr1]
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

-- Proof sketch: `Matrix.charpoly` is the canonical owner for characteristic polynomials in
-- mathlib. The source-facing `chi_(N+1)` is the same polynomial as
-- `det (gamblerRuinTransitionMatrixReal (N + 1) r - X • I)`, while `Matrix.charpoly` is
-- `det (X • I - gamblerRuinTransitionMatrixReal (N + 1) r)`; comparing the two determinants gives
-- the sign `(-1)^N` because the matrix size is `N + 2`.
/-- The canonical owner statement for the shifted family `chi_(N+1)`: up to the usual sign change
between `det (A - X • I)` and `det (X • I - A)`, it is the characteristic polynomial of the
real gambler's ruin transition matrix on `{0, ..., N + 1}`. -/
theorem gamblerRuinTransitionMatrix_charpoly_eq (r : ℝ) (N : ℕ) :
    (gamblerRuinTransitionMatrixReal (N + 1) r).charpoly =
      C ((-1 : ℝ) ^ N) * gamblerRuinCharacteristicPolynomial r N := by
  cases N with
  | zero =>
      -- Proof comment: the two-state matrix is the identity, so its characteristic polynomial is
      -- exactly `χ₁`.
      simp [gamblerRuinTransitionMatrixReal_one_charpoly,
        gamblerRuinCharacteristicPolynomial_chi_one]
  | succ n =>
      apply Polynomial.funext
      intro x
      -- Proof comment: both sides evaluate to the same absorbing boundary factor times the same
      -- scalar characteristic value.
      calc
        ((gamblerRuinTransitionMatrixReal (n + 2) r).charpoly).eval x =
            (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x (n + 1) := by
          rw [gamblerRuinCharpolyEval_eq_boundarySquare_mul_characteristicValue]
        _ = (C ((-1 : ℝ) ^ (n + 1)) * gamblerRuinCharacteristicPolynomial r (n + 1)).eval x := by
          have hsign : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) = 1 := by
            calc
              ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) =
                  (((-1 : ℝ) * (-1 : ℝ)) ^ (n + 1)) := by
                rw [← mul_pow]
              _ = 1 := by simp
          calc
            (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x (n + 1)
                = (((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1))) *
                    ((1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x (n + 1)) := by
                  rw [hsign, one_mul]
            _ = (C ((-1 : ℝ) ^ (n + 1)) *
                  gamblerRuinCharacteristicPolynomial r (n + 1)).eval x := by
                  simp [Polynomial.eval_mul, gamblerRuinCharacteristicPolynomial_eval, mul_assoc,
                    mul_left_comm, mul_comm]

-- Proof sketch: prove the source-facing closed form for `χ_N`, encoded here as the shifted
-- family value `gamblerRuinCharacteristicPolynomial r (N - 1)` for `1 ≤ N`, by induction on
-- `N - 1` using
-- the two initial values and the recurrence `(18.15)`, together with the standard recursion for
-- `Polynomial.Chebyshev.U`.
/-- Exercise 18.4.1: for `r in (0,1)`, the polynomial `chi_N` from Example 18.20 satisfies
the closed formula `(18.16)` in terms of the Chebyshev polynomial of the second kind. In this
file, `chi_N` is represented by `gamblerRuinCharacteristicPolynomial r (N - 1)`. -/
theorem gamblerRuinCharacteristicPolynomial_eq_chebyshevU
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    gamblerRuinCharacteristicPolynomial r (N - 1) =
      C (((-1 : ℝ) ^ (N - 1)) * ((gamblerRuinSigma r / 2) ^ (N - 1))) *
        (1 - X) ^ 2 *
        (Polynomial.Chebyshev.U ℝ (((N - 1 : ℕ) : ℤ))).comp
          (C ((gamblerRuinSigma r)⁻¹) * X) := by
  cases N with
  | zero =>
      cases Nat.not_succ_le_zero 0 hN
  | succ n =>
      -- Proof comment: after rewriting `N = n + 1`, both polynomials have the same evaluation at
      -- every real `x`, so polynomial extensionality finishes the proof.
      apply Polynomial.funext
      intro x
      rw [gamblerRuinCharacteristicPolynomial_eval]
      symm
      simpa using gamblerRuinChebyshevClosedForm_eval (r := r) (x := x) hr0 hr1 n

end ProbabilityTheory

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {α : Type u} [Monoid α]

/-- Helper for Algorithm 7.11: the repeated-squaring recursion attached to an input `A`, with
initial values `X₀ = A` and `Y₀ = 1` and updates
`X_{i+1} = X_i^2`, `Y_{i+1} = Y_i X_i`. -/
def repeatedSquaringOutputs (A : α) : ℕ → α × α
  | 0 => (A, 1)
  | k + 1 =>
      let outputs := repeatedSquaringOutputs A k
      (outputs.1 * outputs.1, outputs.2 * outputs.1)

/-- The first output `X_k` of the repeated-squaring recursion. -/
def repeatedSquaringX (A : α) (k : ℕ) : α :=
  (repeatedSquaringOutputs A k).1

/-- The second output `Y_k` of the repeated-squaring recursion. -/
def repeatedSquaringY (A : α) (k : ℕ) : α :=
  (repeatedSquaringOutputs A k).2

/-- Helper for Algorithm 7.11: the exponent `2^(k+1) - 1` splits as
`(2^k - 1) + 2^k`. -/
lemma twoPowSuccPred_eq_add (k : ℕ) : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 2 ^ k := by
  -- Rewrite the successor power once so the remaining arithmetic is linear.
  rw [Nat.pow_succ]
  omega

-- Proof sketch: prove by induction on `k`. The recursive step multiplies the previous first
-- component by itself and multiplies the previous second component by the previous first
-- component, so the exponents double and then add as in the textbook induction.
/-- Algorithm 7.11: the repeated-squaring recursion returns the pair
`(X_k, Y_k) = (A^(2^k), A^(2^k - 1))`; equivalently, for `p = 2^k` it outputs
`A^p` and `A^(p - 1)`. -/
theorem repeatedSquaringOutputs_eq_powers (A : α) (k : ℕ) :
    repeatedSquaringOutputs A k = (A ^ (2 ^ k), A ^ (2 ^ k - 1)) := by
  induction k with
  | zero =>
      -- The initial pair is exactly `(A, 1) = (A^(2^0), A^(2^0 - 1))`.
      simp [repeatedSquaringOutputs]
  | succ k ih =>
      -- Expand one recursive step and substitute the inductive description of the previous pair.
      rw [repeatedSquaringOutputs, ih]
      apply Prod.ext
      · -- The first component squares the previous power, so its exponent doubles.
        calc
          A ^ (2 ^ k) * A ^ (2 ^ k) = A ^ (2 ^ k + 2 ^ k) := by
            rw [← pow_add]
          _ = A ^ (2 ^ (k + 1)) := by
            have hExponent : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
              rw [Nat.pow_succ]
              omega
            rw [hExponent]
      · -- The second component multiplies `A^(2^k - 1)` by `A^(2^k)`, so the exponents add.
        calc
          A ^ (2 ^ k - 1) * A ^ (2 ^ k) = A ^ ((2 ^ k - 1) + 2 ^ k) := by
            rw [← pow_add]
          _ = A ^ (2 ^ (k + 1) - 1) := by
            rw [twoPowSuccPred_eq_add]

-- Proof sketch: apply `Prod.fst` to `repeatedSquaringOutputs_eq_powers`.
/-- The first output of the repeated-squaring recursion is `A^(2^k)`. -/
theorem repeatedSquaringX_eq_pow (A : α) (k : ℕ) :
    repeatedSquaringX A k = A ^ (2 ^ k) := by
  -- Project the pair formula to the first coordinate.
  simpa [repeatedSquaringX] using congrArg Prod.fst (repeatedSquaringOutputs_eq_powers A k)

-- Proof sketch: apply `Prod.snd` to `repeatedSquaringOutputs_eq_powers`.
/-- The second output of the repeated-squaring recursion is `A^(2^k - 1)`. -/
theorem repeatedSquaringY_eq_pow_pred (A : α) (k : ℕ) :
    repeatedSquaringY A k = A ^ (2 ^ k - 1) := by
  -- Project the pair formula to the second coordinate.
  simpa [repeatedSquaringY] using congrArg Prod.snd (repeatedSquaringOutputs_eq_powers A k)

end

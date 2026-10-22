/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_105

-- Declarations for this item will be appended below by the statement pipeline.

-- For an integer shape parameter `n > 0`, the generalized binomial coefficient in the
-- negative-binomial mass formula is the usual waiting-time coefficient.
private theorem negativeBinomialCoefficient_eq_natChoose {n k : ℕ} (hn : 0 < n) :
    Ring.choose (-(n : ℝ)) k * (-1 : ℝ) ^ k = (Nat.choose (n + k - 1) k : ℝ) := by
  rcases n with _ | n
  · cases Nat.not_lt_zero _ hn
  · have hreal : ((n.succ : ℝ) + k - 1) = (n + k : ℝ) := by
      calc
        ((n.succ : ℝ) + k - 1) = ((n : ℝ) + 1 + k - 1) := by norm_num
        _ = (n + k : ℝ) := by ring
    have hnat : n.succ + k - 1 = n + k := by
      omega
    have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add]
      simp
    rw [Ring.choose_neg, hreal, hnat, ← Nat.cast_add, Ring.choose_natCast]
    simpa [Units.smul_def, Int.cast_negOnePow_natCast, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun x : ℝ ↦ (Nat.choose (n + k) k : ℝ) * x) hsign

/-- Exercise 1.5.1: for an integer shape parameter `n > 0`, evaluating
`negativeBinomialMass` agrees with the combinatorial waiting-time mass for the `n`th success. -/
-- Proof sketch: rewrite the generalized binomial coefficient with `Ring.choose_neg` and
-- `Ring.choose_natCast`, then identify the resulting natural binomial coefficient as the number of
-- sequences with exactly `k` failures before the final success.
theorem negativeBinomialMass_eq_waitingTimeMass {n k : ℕ} (hn : 0 < n) (p : ℝ) :
    negativeBinomialMass (n : ℝ) p k =
      (Nat.choose (n + k - 1) k : ℝ) * p ^ n * (1 - p) ^ k := by
  simp [negativeBinomialMass, negativeBinomialCoefficient_eq_natChoose hn]

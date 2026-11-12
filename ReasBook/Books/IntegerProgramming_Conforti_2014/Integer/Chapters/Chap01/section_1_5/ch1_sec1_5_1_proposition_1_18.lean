/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_proposition_1_18.Euclidean

public section

/-- Proposition 1.18 (1): for `a ≥ b` with `0 < a`, the Euclidean algorithm terminates at the
state `(Nat.gcd a b, 0)`. -/
theorem euclideanAlgorithm_terminalState_eq
    (a b : ℕ) (ha : 0 < a) (hb : b ≤ a) :
    (EuclideanInput.ofLE a b ha hb).terminalState = (Nat.gcd a b, 0) := by
  -- Route correction: the current support theorem is proved directly by fuel induction.
  -- The imported fuel invariant specializes directly to the packaged input.
  simpa [EuclideanInput.ofLE] using
    EuclideanInput.terminalState_eq_gcd_zero (EuclideanInput.ofLE a b ha hb)

/-- Proposition 1.18 (2): for `a ≥ b` with `0 < a`, the Euclidean algorithm uses at most
`1 + 2 * Nat.log2 a` iterations. -/
theorem euclideanAlgorithm_iterationCount_le
    (a b : ℕ) (ha : 0 < a) (hb : b ≤ a) :
    (EuclideanInput.ofLE a b ha hb).iterationCount ≤ 1 + 2 * Nat.log2 a := by
  -- The imported logarithmic rank bound applies using the stored order invariant.
  simpa [EuclideanInput.ofLE] using
    EuclideanInput.iterationCount_le_log2 (EuclideanInput.ofLE a b ha hb)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18.lean`:
the linear running-time witness evaluates to four times its argument. -/
private theorem linearRunningTimeBound_eval (n : ℕ) :
    (Polynomial.C 4 * Polynomial.X : Polynomial ℕ).eval n = 4 * n := by
  -- Evaluate the constant and variable factors separately, then multiply their values.
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Proposition 1.18 (3): the Euclidean-algorithm running time is polynomially bounded by the
binary encoding length `Nat.size a + Nat.size b` of `(a, b)`. -/
theorem euclideanAlgorithm_runningTime_polynomiallyBounded :
    ∃ p : Polynomial ℕ, ∀ a b : ℕ, ∀ ha : 0 < a, ∀ hb : b ≤ a,
      (EuclideanInput.ofLE a b ha hb).runningTime ≤ p.eval (Nat.size a + Nat.size b) := by
  -- The linear polynomial `4 * X` absorbs two operations per logarithmically many iterations.
  refine ⟨Polynomial.C 4 * Polynomial.X, ?_⟩
  intro a b ha hb
  have hcount := euclideanAlgorithm_iterationCount_le a b ha hb
  -- Binary length strictly dominates the base-two logarithm of a positive input.
  have hpow : 2 ^ Nat.log2 a ≤ a := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt ha)
  have hlog : Nat.log2 a < Nat.size a := Nat.lt_size.mpr hpow
  -- Rewrite the chosen polynomial through its evaluation interface before arithmetic closure.
  rw [linearRunningTimeBound_eval]
  simp only [EuclideanInput.runningTime]
  omega

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_1_proposition_1_18.lean:
the three assertions of Proposition 1.18 packaged as one reusable proposition. -/
theorem euclideanAlgorithm_proposition_1_18 :
    (∀ (a b : ℕ) (ha : 0 < a) (hb : b ≤ a),
      (EuclideanInput.ofLE a b ha hb).terminalState = (Nat.gcd a b, 0)) ∧
    (∀ (a b : ℕ) (ha : 0 < a) (hb : b ≤ a),
      (EuclideanInput.ofLE a b ha hb).iterationCount ≤ 1 + 2 * Nat.log2 a) ∧
    (∃ p : Polynomial ℕ, ∀ a b : ℕ, ∀ ha : 0 < a, ∀ hb : b ≤ a,
      (EuclideanInput.ofLE a b ha hb).runningTime ≤
        p.eval (Nat.size a + Nat.size b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    exact euclideanAlgorithm_terminalState_eq a b ha hb
  · intro a b ha hb
    exact euclideanAlgorithm_iterationCount_le a b ha hb
  · exact euclideanAlgorithm_runningTime_polynomiallyBounded

/-- Proposition 1.18 packages the terminal-state, iteration-count, and running-time assertions. -/
theorem «euclideanAlgorithm_terminalState_eq; euclideanAlgorithm_iterationCount_le; euclideanAlgorithm_runningTime_polynomiallyBounded» :
    (∀ (a b : ℕ) (ha : 0 < a) (hb : b ≤ a),
      (EuclideanInput.ofLE a b ha hb).terminalState = (Nat.gcd a b, 0)) ∧
    (∀ (a b : ℕ) (ha : 0 < a) (hb : b ≤ a),
      (EuclideanInput.ofLE a b ha hb).iterationCount ≤ 1 + 2 * Nat.log2 a) ∧
    (∃ p : Polynomial ℕ, ∀ a b : ℕ, ∀ ha : 0 < a, ∀ hb : b ≤ a,
      (EuclideanInput.ofLE a b ha hb).runningTime ≤
        p.eval (Nat.size a + Nat.size b)) := by
  -- The compatibility declaration exposes the already proved bundled proposition.
  exact euclideanAlgorithm_proposition_1_18

end

#print axioms euclideanAlgorithm_proposition_1_18

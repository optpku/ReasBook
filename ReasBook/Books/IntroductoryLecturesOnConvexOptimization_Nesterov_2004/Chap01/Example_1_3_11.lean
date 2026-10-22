/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

local notation "L0" => (2 : NNReal)
local notation "eps0" => (1 / 100 : ℝ)

/-
Example 1.3.11 stays in the Chapter 1 value-oracle complexity domain.

Relevant owner-style declarations sampled before refining:
* `DeterministicValueOracleMethod (zeroOneBox 10)` in `Theorem_1_3_9.lean`, the owner object for
  deterministic value-oracle procedures on `B₁₀`
* `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Theorem_1_3_9.lean`, the owner correctness predicate for solving the textbook class
* `linftyLipschitz_value_oracle_complexity_lower_bound` in `Theorem_1_3_9.lean`, the canonical
  lower-bound theorem specialized here
* `uniformGridMethod_analyticalComplexity_bound` in `Corollary_1_3_8.lean`, the matching
  chapter-level upper-bound statement for the same problem class

Source/core/bridge triage:
* source-facing: the textbook numerical specialization `n = 10`, `L = 2`, `ε = 0.01`
* core/canonical: the solve predicate and lower-bound theorem from `Theorem_1_3_9.lean`
* bridge/view: the arithmetic evaluation of the instantiated lower-bound term, and the derived
  arithmetic-operation and runtime comparisons

Primitive data:
* `method : DeterministicValueOracleMethod (zeroOneBox 10)`
* `hmethod : method.SolvesLinftyLipschitzProblemClassWithin L0 eps0 k`

Derived API:
* the oracle-call lower bound `10 ^ 20 ≤ k`
* the arithmetic lower bound `10 ^ 21 ≤ 10 * k`
* the runtime lower bound `(10 : ℝ) ^ 15 ≤ ((10 : ℝ) * k) / (10 : ℝ) ^ 6`

The refinement therefore keeps the owner theorem as the public mathematical source and removes the
redundant local arithmetic-equality wrappers, letting `norm_num` evaluate the instantiated
constants directly at the use sites.
-/

section

variable {k : ℕ} (method : DeterministicValueOracleMethod (zeroOneBox 10))

/-- The instantiated lower bound from Theorem 1.3.9 forces at least `10^20` oracle calls for the
`n = 10`, `L = 2`, `ε = 0.01` box-Lipschitz problem class. -/
theorem oracleCallLowerBound_n10_L2_eps001
    (hmethod : method.SolvesLinftyLipschitzProblemClassWithin L0 eps0 k) :
    10 ^ 20 ≤ k := by
  have hbound :
      Nat.floor ((L0 : ℝ) / (2 * eps0)) ^ 10 ≤ k :=
    linftyLipschitz_value_oracle_complexity_lower_bound
      (by norm_num) (by norm_num) method hmethod
  norm_num at hbound ⊢
  exact hbound

/-- Any method achieving the Example 1.3.11 accuracy target needs at least `10^21` arithmetic
operations if each oracle call costs at least `10` arithmetic operations. -/
theorem arithmeticComplexityLowerBound_n10_L2_eps001
    (hmethod : method.SolvesLinftyLipschitzProblemClassWithin L0 eps0 k) :
    10 ^ 21 ≤ 10 * k := by
  simpa using Nat.mul_le_mul_left 10 (oracleCallLowerBound_n10_L2_eps001 method hmethod)

/-- At processor throughput `10^6` arithmetic operations per second, the Example 1.3.11
arithmetic lower bound yields a runtime lower bound of `10^15` seconds. -/
theorem runtimeLowerBound_n10_L2_eps001
    (hmethod : method.SolvesLinftyLipschitzProblemClassWithin L0 eps0 k) :
    (10 : ℝ) ^ 15 ≤ ((10 : ℝ) * k) / (10 : ℝ) ^ 6 := by
  have hops : (10 ^ 21 : ℝ) ≤ (10 : ℝ) * k := by
    exact_mod_cast arithmeticComplexityLowerBound_n10_L2_eps001 method hmethod
  have htime :
      (10 ^ 21 : ℝ) / (10 : ℝ) ^ 6 ≤ ((10 : ℝ) * k) / (10 : ℝ) ^ 6 := by
    exact div_le_div_of_nonneg_right hops (by positivity)
  norm_num at htime ⊢
  exact htime

/-- Example 1.3.11: for the box-Lipschitz problem class with `L = 2`, `n = 10`, and
`ε = 0.01`, any deterministic value-oracle method needs at least `10^20` oracle calls; with at
least `10` arithmetic operations per call and processor throughput `10^6` operations per second,
this yields lower bounds `10^21` on arithmetic operations and `10^15` seconds on runtime. -/
theorem complexityBounds_n10_L2_eps001
    (hmethod : method.SolvesLinftyLipschitzProblemClassWithin L0 eps0 k) :
    10 ^ 20 ≤ k ∧
      10 ^ 21 ≤ 10 * k ∧
      (10 : ℝ) ^ 15 ≤ ((10 : ℝ) * k) / (10 : ℝ) ^ 6 := by
  exact ⟨oracleCallLowerBound_n10_L2_eps001 method hmethod,
    arithmeticComplexityLowerBound_n10_L2_eps001 method hmethod,
    runtimeLowerBound_n10_L2_eps001 method hmethod⟩

end

end

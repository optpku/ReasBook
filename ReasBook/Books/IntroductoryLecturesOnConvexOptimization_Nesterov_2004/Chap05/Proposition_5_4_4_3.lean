/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Alg_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 5.4.4.3 is a bridge/view item in the chapter's semidefinite Newton-step
arithmetic-cost domain.

Sampled owner-style declarations in the same domain:
* `IsSemidefiniteNewtonDirectionOutput` in `Alg_5_4_4_1`, the Chapter 5 source-facing owner for
  one execution of the Newton-step subroutine;
* `semidefiniteNewtonNormalMatrix` in `Alg_5_4_4_1`, the owner for the dense multiplier system
  `S λ = d`;
* `semidefiniteNewtonDirectionFromMultiplier` in `Alg_5_4_4_1`, the owner for the recovered
  Newton direction `Δ = X (-U + ∑ λ_j A_j) X`;
* `GeneralIterativeScheme.totalArithmeticWork` in `Chap01/Definition_1_2_12`, the broader
  project owner for accumulated arithmetic work across iterations.

Best owner abstraction:
* source-facing: the Chapter 5 Newton-step owner `IsSemidefiniteNewtonDirectionOutput`;
* core/canonical: `ℕ`-valued arithmetic-cost expressions and polynomial inequalities on `(n, m)`;
* bridge/view: the dimension-only dense arithmetic-work model for one execution of that owner.

Primitive data:
* `n`, `m : ℕ`.

Derived API:
* the concrete dense-work expression `semidefiniteNewtonStepDenseArithmeticWorkBound n m`;
* its definitional expansion;
* the regime-specific bound by `n^2 * (m + n) * m`.

Source/core/bridge triage:
* source-facing: `IsSemidefiniteNewtonDirectionOutput`;
* core/canonical: arithmetic work as an `ℕ`-valued expression on primitive dimensions;
* bridge/view: this file's dense one-step arithmetic-cost estimate.

This refinement keeps the source-facing Newton-step owner upstream in `Alg_5_4_4_1` and leaves
this file responsible only for the dimension-level dense arithmetic model and its asymptotic
bound. -/

/- Proposition 5.4.4.3 is the arithmetic-cost companion to the Chapter 5 Newton-step owner. -/
set_option linter.hashCommand false in
#check IsSemidefiniteNewtonDirectionOutput

/-- A parameter-only dense arithmetic upper bound for one execution of the Newton-step subroutine
that computes the matrices `B_j = X * A_j * X`, assembles the dense linear system `S λ = d`,
solves that system, and forms `Δ = X * (-U + ∑ λ_j A_j) * X` using standard dense routines. -/
def semidefiniteNewtonStepDenseArithmeticWorkBound (n m : ℕ) : ℕ :=
  2 * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3

-- Proof sketch: unfold `semidefiniteNewtonStepDenseArithmeticWorkBound`; the right-hand side is
-- exactly the sum of the dense-operation counts assigned to the four steps of the subroutine.
/-- Expanding `semidefiniteNewtonStepDenseArithmeticWorkBound` recovers the stepwise dense
operation count used for the Newton-step subroutine. -/
theorem semidefiniteNewtonStepDenseArithmeticWorkBound_eq (n m : ℕ) :
    semidefiniteNewtonStepDenseArithmeticWorkBound n m =
      2 * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3 :=
  rfl

-- Proof sketch: bound the Step 1 and Step 4 matrix-multiplication terms by multiples of
-- `n^3 * m`, bound the assembly and solve terms by multiples of `n^2 * m^2`, use
-- `m ≤ n (n + 1) / 2` to absorb the `m^3` term into `n^2 * m^2`, and then factor the result as a
-- constant multiple of `n^2 * (m + n) * m`.
/-- Proposition 5.4.4.3: if `1 ≤ m ≤ n(n + 1) / 2`, then one dense execution of the Newton-step
subroutine has arithmetic work bounded by a constant multiple of `n^2 * (m + n) * m`, and hence
has arithmetic complexity `O(n^2 * (m + n) * m)`. -/
theorem semidefiniteNewtonStepDenseArithmeticComplexity_bound
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n * (n + 1) / 2) :
    semidefiniteNewtonStepDenseArithmeticWorkBound n m ≤
      8 * n ^ 2 * (m + n) * m := by
  rw [semidefiniteNewtonStepDenseArithmeticWorkBound_eq]
  have hn : 1 ≤ n := by
    by_cases h0 : n = 0
    · subst h0
      simp at hmn
      omega
    · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  have hmn_sq : m ≤ n ^ 2 := by
    calc
      m ≤ n * (n + 1) / 2 := hmn
      _ ≤ n * (2 * n) / 2 := by
        have hn_two : n + 1 ≤ 2 * n := by
          nlinarith [hn]
        gcongr
      _ = n ^ 2 := by
        simpa [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (Nat.mul_div_right (n * n) (show 0 < 2 by decide))
  have hm_two : m + 1 ≤ 2 * m := by
    nlinarith [hm]
  have hmQ : (1 : ℚ) ≤ m := by
    exact_mod_cast hm
  have hnQ : (1 : ℚ) ≤ n := by
    exact_mod_cast hn
  have hmn_sqQ : (m : ℚ) ≤ n ^ 2 := by
    exact_mod_cast hmn_sq
  have hm_twoQ : (m : ℚ) + 1 ≤ 2 * m := by
    exact_mod_cast hm_two
  have hm_sq_geQ : (m : ℚ) ≤ m ^ 2 := by
    nlinarith [hmQ]
  have hn_sq_nonnegQ : 0 ≤ (n : ℚ) ^ 2 := by
    positivity
  have hn_cube_nonnegQ : 0 ≤ (n : ℚ) ^ 3 := by
    positivity
  have hm_cubeQ : (m : ℚ) ^ 3 ≤ m ^ 2 * n ^ 2 := by
    nlinarith [hmn_sqQ]
  have hmn_sq_mulQ : (2 : ℚ) * m * n ^ 2 ≤ 2 * m ^ 2 * n ^ 2 := by
    nlinarith [hm_sq_geQ, hn_sq_nonnegQ]
  have hn_cubeQ : (2 : ℚ) * n ^ 3 ≤ 2 * m * n ^ 3 := by
    nlinarith [hmQ, hn_cube_nonnegQ]
  exact_mod_cast (show
    (2 : ℚ) * m * n ^ 3 + m ^ 2 * n ^ 2 + m ^ 3 + (m + 1) * n ^ 2 + 2 * n ^ 3 ≤
      8 * n ^ 2 * (m + n) * m by
    nlinarith [hm_cubeQ, hmn_sq_mulQ, hn_cubeQ, hm_twoQ])

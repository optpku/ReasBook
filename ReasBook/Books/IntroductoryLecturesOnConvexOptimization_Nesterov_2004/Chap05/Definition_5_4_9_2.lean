/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 5.4.9.2 lies in the chapter's algorithmic complexity-model domain.

Sampled owner declarations before refining:
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the project
  pattern where a complexity notion is a `Prop` on primitive data;
* `HasLpBarrierShortStepIterationBound` in `Definition_5_4_9_6`, the nearby Chapter 5 owner for a
  direct iteration-count bound predicate on the primitive function `N_it`;
* `HasLpBarrierShortStepTotalArithmeticComplexityBound` in `Theorem_5_4_9_3`, the nearby Chapter
  5 owner for a direct total-cost bound predicate on primitive arithmetic-work data;
* `HasConvergenceRateOfOrder` in `Chap01/Definition_1_6_9`, the project owner for a source-facing
  bound with a uniform constant and a derived asymptotic bridge.

Best owner abstraction:
* source-facing: the textbook complexity model consisting of the accuracy-indexed iteration-count
  family `N_it`, the oracle arithmetic cost per iteration, and the additional per-iteration
  arithmetic overhead;
* core/canonical: a direct `Prop`-valued bound owner on those three primitive cost functions;
* bridge/view: downstream total-cost constructions obtained by combining the three primitive
  functions, rather than a separate packaged owner.

Primitive data:
* the accuracy-indexed iteration-count family;
* the oracle arithmetic cost per iteration;
* the additional per-iteration arithmetic overhead.

Derived API:
* the small-accuracy hypothesis `ε ∈ (0, 1)`;
* the three textbook bounds with constants uniform in `ε`;
* the restriction to positive dimensions, avoiding spurious zero-dimension obligations.
-/

/-- Definition 5.4.9.2: the ellipsoid method satisfies the textbook complexity model when there
exist positive constants, independent of the target accuracy `ε ∈ (0, 1)`, such that the
accuracy-indexed iteration count `N_it`, oracle arithmetic cost per iteration, and additional
per-iteration arithmetic overhead obey the bounds `N_it = O(n^2 log (1 / ε))`,
`C_oracle = O(m n)`, and `C_iter = O(n^2)` in positive dimensions. -/
def HasEllipsoidMethodComplexityBounds
    (iterationCount : ℝ → ℕ → ℕ)
    (oracleCostPerIteration : ℕ → ℕ → ℕ)
    (extraCostPerIteration : ℕ → ℕ) : Prop :=
  ∃ C_it C_oracle C_iter : ℝ,
    0 < C_it ∧
      0 < C_oracle ∧
      0 < C_iter ∧
      (∀ {ε : ℝ} {n : ℕ}, ε ∈ Set.Ioo (0 : ℝ) 1 → 0 < n →
        (iterationCount ε n : ℝ) ≤ C_it * (n : ℝ) ^ 2 * Real.log (1 / ε)) ∧
      (∀ {m n : ℕ}, 0 < m → 0 < n →
        (oracleCostPerIteration m n : ℝ) ≤ C_oracle * (m : ℝ) * (n : ℝ)) ∧
      (∀ {n : ℕ}, 0 < n →
        (extraCostPerIteration n : ℝ) ≤ C_iter * (n : ℝ) ^ 2)

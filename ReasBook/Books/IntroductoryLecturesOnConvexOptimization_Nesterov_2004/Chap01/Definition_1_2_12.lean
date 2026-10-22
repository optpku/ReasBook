/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Primary domain: arithmetic complexity of information-set-based black-box iterative schemes.

Relevant owner-style declarations sampled before refining:
* `GeneralIterativeScheme` and `GeneralIterativeScheme.HaltsAt` in
  `Algorithm_1_2_10.lean`, which supply the source-facing informational-state dynamics and halting
  predicate;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Definition_1_2_11.lean`, the source-facing
  analytical-complexity predicate;
* `GeneralIterativeScheme.isAnalyticalComplexity_iff` in `Definition_1_2_11.lean`, the chapter
  bridge to the textbook “halts first at `N`” phrasing;
* `IsLeast` in mathlib `Order.Bounds.Defs`, the canonical least-element predicate used internally
  by `IsAnalyticalComplexity`.

Owner abstraction:
the pair consisting of the informational-state owner object `GeneralIterativeScheme` and the
source-facing analytical-complexity witness `scheme.IsAnalyticalComplexity N`.

Primitive data:
the scheme together with the per-call oracle work `oracleWork` and informational-state update work
`methodWork`.

Derived API:
the per-iteration and cumulative arithmetic work, and the source-facing predicate saying that
`M` is the total arithmetic work at the least halting iteration. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)
variable (oracleWork : Query → Answer → ℕ)
variable (methodWork : Set (Query × Answer) → ℕ)

/-- The arithmetic work of iteration `k` is the sum of the oracle work performed at the current
query point and the method work needed to choose the next point from the updated informational
set. -/
def iterationArithmeticWork (k : ℕ) : ℕ :=
  oracleWork (scheme.currentPoint k) (scheme.currentAnswer k) + methodWork (scheme (k + 1))

/-- The total arithmetic work up to iteration `N` is the sum of the oracle and method work over
the first `N` iterations. -/
def totalArithmeticWork (N : ℕ) : ℕ :=
  (Finset.range N).sum (scheme.iterationArithmeticWork oracleWork methodWork)

/- Definition 1.2.12 is the derived complexity predicate on the owner object
`GeneralIterativeScheme`, built from the analytical-complexity witness
`scheme.IsAnalyticalComplexity N` and the accumulated arithmetic work up to that iteration. -/

/-- Definition 1.2.12: A natural number `M` is the arithmetical complexity of a method when `M`
is the total number of arithmetic operations, counting both oracle work and method work, required
to reach the analytical complexity threshold for the chosen stopping criterion. -/
def IsArithmeticalComplexity (M : ℕ) : Prop :=
  ∃ N : ℕ,
    scheme.IsAnalyticalComplexity N ∧
      M = scheme.totalArithmeticWork oracleWork methodWork N

variable {scheme} {oracleWork} {methodWork}

/-- Arithmetical complexity is exactly total arithmetic work evaluated at an analytical-complexity
index. -/
@[simp]
theorem isArithmeticalComplexity_iff {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.IsAnalyticalComplexity N ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N :=
  Iff.rfl

/-- Arithmetical complexity is the total accumulated oracle and method work at the least halting
iteration. -/
theorem isArithmeticalComplexity_iff_haltsAt {M : ℕ} :
    scheme.IsArithmeticalComplexity oracleWork methodWork M ↔
      ∃ N : ℕ,
        scheme.HaltsAt N ∧
          (∀ m < N, ¬ scheme.HaltsAt m) ∧
          M = scheme.totalArithmeticWork oracleWork methodWork N := by
  rw [scheme.isArithmeticalComplexity_iff]
  constructor
  · rintro ⟨N, hN, hM⟩
    rw [scheme.isAnalyticalComplexity_iff] at hN
    exact ⟨N, hN.1, hN.2, hM⟩
  · rintro ⟨N, hN, hlt, hM⟩
    refine ⟨N, ?_, hM⟩
    rw [scheme.isAnalyticalComplexity_iff]
    exact ⟨hN, hlt⟩

end GeneralIterativeScheme

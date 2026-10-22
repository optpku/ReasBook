/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_2_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Primary domain: analytical complexity of information-set-based black-box iterative schemes.

Source/core/bridge triage for Definition 1.2.11:
* source-facing: `GeneralIterativeScheme.IsAnalyticalComplexity`, the textbook predicate saying
  that `N` oracle-call/update cycles are required to reach the `ε`-stopping criterion;
* core/canonical: `IsLeast {k : ℕ | scheme.HaltsAt k} N` on the halting set;
* bridge/view: `GeneralIterativeScheme.isAnalyticalComplexity_iff`, which unpacks the source
  predicate as “halts at `N` and not earlier”.

Relevant declarations sampled before refining:
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`;
* `IsLeast` in mathlib `Order.Bounds.Defs`;
* `Nat.isLeast_find` in mathlib `Order/Nat.lean`;
* `Nat.find_eq_iff` in mathlib `Data/Nat/Find.lean`.

Primitive data:
* the scheme and its halting predicate `HaltsAt`.

Derived API:
* the source-facing analytical-complexity predicate and its owner/textbook bridge lemmas. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)

/-- Definition 1.2.11: a natural number `N` is the analytical complexity of a general iterative
scheme when `N` is the first oracle-call count at which the scheme reaches the chosen stopping
criterion. If the scheme never reaches that stopping criterion, no such `N` exists. -/
def IsAnalyticalComplexity (N : ℕ) : Prop :=
  IsLeast {k : ℕ | scheme.HaltsAt k} N

variable {scheme}
variable {N : ℕ}

/-- Analytical complexity means that the scheme reaches the chosen stopping criterion at `N` and
at no smaller oracle-call count. -/
-- Proof sketch: unfold the owner predicate `IsLeast`; the lower-bound clause says every halting
-- index is at least `N`, which on `ℕ` is equivalent to the absence of smaller halting indices.
@[simp] theorem isAnalyticalComplexity_iff :
    scheme.IsAnalyticalComplexity N ↔
      scheme.HaltsAt N ∧ ∀ m < N, ¬ scheme.HaltsAt m := by
  change IsLeast {k : ℕ | scheme.HaltsAt k} N ↔
    scheme.HaltsAt N ∧ ∀ m < N, ¬ scheme.HaltsAt m
  constructor
  · rintro ⟨hN, hleast⟩
    refine ⟨hN, fun m hm hmhalts ↦ ?_⟩
    exact (not_le_of_gt hm) (hleast hmhalts)
  · rintro ⟨hN, hlt⟩
    refine ⟨hN, fun m hm ↦ le_of_not_gt fun hmn ↦ ?_⟩
    exact hlt m hmn hm

end GeneralIterativeScheme

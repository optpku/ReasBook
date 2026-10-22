/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {α : Type u}

attribute [local instance] Classical.decPred

/- Definition 3.53 lies in the chapter's feasible-index counting / ordered enumeration domain.

Sampled owner-style declarations in the same domain:
- `Nat.count`, the canonical owner for prefix counts of indices satisfying a predicate;
- `Nat.count_zero`, the owner theorem for the initial counter value;
- `Nat.nth`, the canonical owner for the ordered enumeration of indices satisfying a predicate;
- `Nat.nth_count`, the owner theorem identifying a feasible index with its counted position.

Best owner abstraction:
- core/canonical: the predicate `fun j ↦ y j ∈ Q` on `ℕ`, together with
  `Nat.count (fun j ↦ y j ∈ Q)` and `Nat.nth (fun j ↦ y j ∈ Q)`;
- source-facing: the selected feasible sequence `feasibleSubsequence Q y`, defined directly from
  that canonical enumeration;
- bridge/view: the selected-term consequence obtained by applying `y` to `Nat.nth_count`.

Primitive data:
- the feasibility predicate `fun j ↦ y j ∈ Q`.

Derived API:
- the textbook counter `i(k) = Nat.count (fun j ↦ y j ∈ Q) k`;
- the selected feasible sequence `feasibleSubsequence Q y`;
- the corresponding selected-term identity
  `feasibleSubsequence Q y (Nat.count (fun j ↦ y j ∈ Q) k) = y k`.

Source/core/bridge triage:
- source-facing: the selected feasible sequence and its counted-position identity;
- core/canonical: `Nat.count`, `Nat.nth`, and `Nat.nth_count`;
- bridge/view: the selected-term consequence derived directly from `Nat.nth_count`.

This file therefore keeps the counter and ordered enumeration at the canonical `Nat.count` /
`Nat.nth` level, while exposing the textbook selected feasible sequence only as the thin owner
specialization built from those canonical declarations. -/

section

variable (Q : Set α) (y : ℕ → α) (k : ℕ)

/- Definition 3.53: the textbook counter `i(k)` is the canonical prefix count below. -/
#check Nat.count (fun j ↦ y j ∈ Q) k

/-- Definition 3.53: the selected feasible sequence is the original sequence sampled at the
canonical feasible indices given by `Nat.nth`. -/
abbrev feasibleSubsequence (Q : Set α) (y : ℕ → α) (i : ℕ) : α :=
  y (Nat.nth (fun j ↦ y j ∈ Q) i)

/-- If `y k` is feasible, then the selected feasible sequence at counted position
`Nat.count (fun j ↦ y j ∈ Q) k` recovers `y k`. -/
theorem feasibleSubsequence_count_eq_self_of_feasible
    (Q : Set α) (y : ℕ → α) {k : ℕ} (hk : y k ∈ Q) :
    feasibleSubsequence Q y (Nat.count (fun j ↦ y j ∈ Q) k) = y k := by
  simpa [feasibleSubsequence] using congrArg y (Nat.nth_count hk)

end

end

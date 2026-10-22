/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.1.5.6 lies in the chapter's extended-valued convex-analysis / subdifferential domain.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `mem_subdifferential_iff`
- `isMinOn_iff`

Best owner abstraction:
- the subdifferential owner `subdifferential`, derived from `IsSubgradientAt`
- the minimizer owner `IsMinOn`

Primitive data:
- a feasible set `Q`, an extended-real objective `f`, points `x0`, `xStar`, `g`
- the feasibility hypothesis `hx0 : x0 ∈ Q`
- the minimizing hypothesis `hxStar : IsMinOn f Q xStar`
- the owner-membership hypothesis `hg : g ∈ ∂ f(x0)`

Derived API:
- `x0 ∈ dom f`, extracted from `hg`
- `xStar ∈ dom f`, extracted from `hxStar` and `hg`
- the real inequality obtained by comparing the subgradient lower-support bound with the minimizer
  inequality

Source/core/bridge triage:
- source-facing: the minimizer-pairing theorem stated in the textbook
- core/canonical: `subdifferential` / `IsSubgradientAt` and `IsMinOn`
- bridge/view: the passage from `IsMinOn f Q xStar` to the sublevel inequality `f xStar ≤ f x0`

The textbook states the result on `ℝⁿ`, but the theorem itself only uses the inner-product-space
owner abstractions. This file therefore removes the unnecessary Euclidean wrapper and proves the
source-facing statement directly from the canonical owner data. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 3.1.5.6: if `xStar` minimizes `f` on `Q` and `x0 ∈ Q`, then every subgradient
`g ∈ ∂f(x0)` has nonnegative pairing with the displacement `x0 - xStar`. -/
-- Proof sketch: extract the owner subgradient inequality from `hg` and evaluate it at `xStar`.
-- Since `xStar` minimizes `f` on `Q` and `x0 ∈ Q`, we have `f xStar ≤ f x0`, so the owner
-- sublevel-set inequality applies directly at `xStar`.
theorem subgradient_inner_sub_nonneg_of_isMinOn
    {Q : Set V} {f : V → WithTop ℝ} {x0 xStar g : V}
    (hx0 : x0 ∈ Q) (hxStar : IsMinOn f Q xStar) (hg : g ∈ ∂ f(x0)) :
    0 ≤ inner ℝ g (x0 - xStar) := by
  exact
    subgradient_nonneg_on_sublevelSet_of_mem_subdifferential hg
      ((isMinOn_iff.mp hxStar) x0 hx0)

end

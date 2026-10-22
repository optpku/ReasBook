/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_4_2_Average_Individual_Expense_Bound

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped BigOperators

section

variable {X : Type u} {ι : Type*} [Fintype ι]

/-
Proposition 6.18 lies in the Chapter 6 objective-scaling / optimal-value domain.

Sampled owner-style declarations:
* `averageIndividualExpense` in `Text_6_1_4_2_Average_Individual_Expense_Bound`, the chapter's
  source-facing owner for scaling a real-valued objective by a positive factor;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  whole-space owner `(.mk Set.univ f).optimalValue : EReal` for unconstrained exact optimal
  values;
* `average_individual_expense_suboptimality_bound` in
  `Text_6_1_4_2_Average_Individual_Expense_Bound`, the exact owner theorem for the scaled-gap
  estimate.

Best owner abstraction:
* source-facing: Proposition 6.18, the population-multiplicity specialization of the average
  individual expense bound;
* core/canonical: `averageIndividualExpense` together with the Chapter 1 whole-space owner
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: specialization to the scale factor `P = ∑ j, (m j : ℝ)`.

Primitive data:
* the multiplicity family `m`;
* the objective `f`, iterate `xHat`, bound constant `fBar`, and index `N`.

Derived API:
* the scaling owner `averageIndividualExpense`;
* the optimal-value owner `(.mk Set.univ f).optimalValue`;
* the specialized rate bound below, whose only finite-family input is the total mass
  `∑ j, (m j : ℝ)`.

The previous file already reused the scaling owner, but it still inherited a noncanonical local
real-valued `optimalValue` from the dependency, and it fixed the multiplicity family to the
coordinate model `Fin p`. The refined file keeps only the source-facing specialization, states its
gap directly through the Chapter 1 whole-space owner in `EReal`, and exposes the multiplicities
through the canonical finite-family owner `[Fintype ι]`.
-/

-- Proof sketch: specialize `average_individual_expense_suboptimality_bound` to the scaling factor
-- `P = ∑ j, (m j : ℝ)`.
/-- Proposition 6.18: if `P = \sum_j m_j` is positive and an iterate `xHat` satisfies
`f(xHat) - f* ≤ 2 P \bar f / √(N (N + 1))`, then the scaled objective
`\bar f(x) = f(x) / P` satisfies
`\bar f(xHat) - \bar f* ≤ 2 \bar f / √(N (N + 1))`, with both optimal values taken through the
Chapter 1 whole-space owner in `EReal`. -/
theorem scaledObjective_convergence_rate_bound
    (m : ι → ℕ) (f : X → ℝ) (xHat : X) {fBar : ℝ} {N : ℕ}
    (hP : 0 < ∑ j, (m j : ℝ))
    (hbound :
      (f xHat : EReal) -
          ((.mk Set.univ f : SetConstrainedMinimizationProblem X).optimalValue) ≤
        (2 * (∑ j, (m j : ℝ)) * fBar) /
          Real.sqrt ((N : ℝ) * ((N : ℝ) + 1))) :
    (averageIndividualExpense (∑ j, (m j : ℝ)) f xHat : EReal) -
        ((.mk Set.univ (averageIndividualExpense (∑ j, (m j : ℝ)) f) :
          SetConstrainedMinimizationProblem X).optimalValue) ≤
      (2 * fBar) / Real.sqrt ((N : ℝ) * ((N : ℝ) + 1)) := by
  simpa using
    average_individual_expense_suboptimality_bound (∑ j, (m j : ℝ)) f xHat hP hbound

end

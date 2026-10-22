/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

open scoped BigOperators

/-
Text 6.1.4.2 lies in the whole-space objective-scaling / optimal-value domain.

Mandatory domain-style sampling before refinement:
- pointwise scalar multiplication on function spaces, the canonical owner for scaling a real-valued
  objective;
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` in
  `Chap01/Definition_1_3_7`, the Chapter 1 owner for exact optimal values in `EReal`;
- `scaledObjective_convergence_rate_bound` in `Chap06/Proposition_6_18`, the direct downstream
  specialization to a finite population split.

Best owner abstraction:
- source-facing: `averageIndividualExpense`, the textbook average-cost objective;
- core/canonical: pointwise scalar multiplication on `X → ℝ` together with the whole-space owner
  `SetConstrainedMinimizationProblem.mk Set.univ`;
- bridge/view: `averageIndividualExpense P f = P⁻¹ • f`.

Primitive data:
- the population factor `P`;
- the total-expense objective `f`.

Derived API:
- the pointwise evaluation lemma below;
- the whole-space optimal values of `f` and `averageIndividualExpense P f`.

Source/core/bridge triage:
- source-facing: the average individual expense objective and its suboptimality bound;
- core/canonical: function-space scaling and `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the identification of the source-facing average objective with `P⁻¹ • f`.
-/

/-- The average individual expense objective `x ↦ f(x) / P` obtained by dividing the total
expense by the positive population factor `P`. -/
abbrev averageIndividualExpense (P : ℝ) (f : X → ℝ) : X → ℝ :=
  P⁻¹ • f

/-- Evaluating `averageIndividualExpense P f` at `x` gives `f(x) / P`. -/
@[simp] theorem averageIndividualExpense_apply (P : ℝ) (f : X → ℝ) (x : X) :
    averageIndividualExpense P f x = f x / P := by
  simp [averageIndividualExpense, div_eq_mul_inv, mul_comm]

/-- Helper for Text 6 1 4 2 Average Individual Expense Bound: comparing the Chapter 1 owner
optimal value of the total expense objective with the concrete value at `y` yields the pointwise
total-expense gap estimate. -/
lemma total_expense_gap_le_value_at
    (P : ℝ) (f : X → ℝ) (xHat y : X) {rBar : ℝ} {N : ℕ}
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (f xHat : EReal) - (f y : EReal) ≤
      (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
  let problem : SetConstrainedMinimizationProblem X := .mk Set.univ f
  let Δ : EReal := (((2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ) : ℝ) : EReal)
  -- Replace the unknown optimal value by the concrete feasible value at `y`.
  have hy_opt : problem.optimalValue ≤ (f y : EReal) := by
    simpa [problem] using problem.optimalValue_le_of_mem_feasibleSet (x := y) (by simp [problem])
  -- Rewrite the assumed suboptimality gap into an additive comparison.
  have hx_le :
      (f xHat : EReal) ≤
        Δ + problem.optimalValue := by
    exact
      (EReal.sub_le_iff_le_add
        (Or.inr (EReal.coe_ne_top _))
        (Or.inr (EReal.coe_ne_bot _))).mp (by simpa [problem, Δ] using hbound)
  have hx_le' :
      (f xHat : EReal) ≤
        Δ + (f y : EReal) := by
    have hΔ : problem.optimalValue + Δ ≤ (f y : EReal) + Δ := add_le_add hy_opt le_rfl
    exact hx_le.trans (by simpa [add_comm, add_left_comm, add_assoc] using hΔ)
  -- Move the comparison value back to the left to recover the textbook total-expense gap.
  simpa [Δ] using EReal.sub_le_of_le_add hx_le'

/-- Helper for Text 6 1 4 2 Average Individual Expense Bound: dividing the total-expense
comparison by the positive population factor `P` yields the pointwise average-expense bound. -/
lemma average_expense_gap_le_value_at
    (P : ℝ) (f : X → ℝ) (xHat y : X) {rBar : ℝ} {N : ℕ}
    (hP : 0 < P)
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (averageIndividualExpense P f xHat : ℝ) -
        (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) ≤
      averageIndividualExpense P f y := by
  -- First read the `EReal` comparison back on the real surface.
  have htotal_ereal :
      ((f xHat - f y : ℝ) : EReal) ≤
        (((2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ) : ℝ) : EReal) := by
    simpa [EReal.coe_sub] using total_expense_gap_le_value_at P f xHat y hbound
  have htotal_real :
      f xHat - f y ≤ (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
    exact EReal.coe_le_coe_iff.mp htotal_ereal
  have hscaled :
      (f xHat - f y) / P ≤ (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
    refine (div_le_iff₀ hP).2 ?_
    calc
      f xHat - f y ≤ (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ) := htotal_real
      _ = ((2 * rBar) / Real.sqrt (N * (N + 1) : ℝ)) * P := by
        ring
  have hscaled' :
      f xHat / P - f y / P ≤ (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
    simpa [sub_div] using hscaled
  -- Rewrite the divided comparison as the average-expense pointwise bound.
  have hpoint :
      f xHat / P ≤ f y / P + (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
    exact sub_le_iff_le_add'.1 hscaled'
  refine sub_le_iff_le_add'.2 ?_
  simpa [averageIndividualExpense, Pi.smul_apply, div_eq_mul_inv, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hpoint

/-- Helper for Text 6 1 4 2 Average Individual Expense Bound: the shifted average expense at
`xHat` is bounded above by the Chapter 1 owner optimal value of the average objective. -/
lemma average_expense_lower_le_optimalValue
    (P : ℝ) (f : X → ℝ) (xHat : X) {rBar : ℝ} {N : ℕ}
    (hP : 0 < P)
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (averageIndividualExpense P f xHat : EReal) -
        (((2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) : ℝ) : EReal) ≤
      (SetConstrainedMinimizationProblem.mk Set.univ
        (averageIndividualExpense P f)).optimalValue := by
  let problem : SetConstrainedMinimizationProblem X := .mk Set.univ (averageIndividualExpense P f)
  -- Rewrite the owner optimal value as an infimum over all feasible average-expense values.
  rw [show
      (SetConstrainedMinimizationProblem.mk Set.univ (averageIndividualExpense P f)).optimalValue =
        problem.optimalValue by rfl]
  rw [problem.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨y, -, rfl⟩
  -- Each feasible value dominates the shifted average expense by the previous pointwise lemma.
  have hpoint :
      (((averageIndividualExpense P f xHat : ℝ) -
          (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) : ℝ) : EReal) ≤
        (averageIndividualExpense P f y : EReal) := by
    exact EReal.coe_le_coe <| average_expense_gap_le_value_at P f xHat y hP hbound
  simpa [EReal.coe_sub] using hpoint

-- Proof sketch: rewrite `averageIndividualExpense P f` as the canonical scalar multiple `P⁻¹ • f`,
-- compare the Chapter 1 whole-space optimal values of `f` and `averageIndividualExpense P f`, and
-- divide the assumed total-expense bound by the positive factor `P`.
/-- Text 6 1 4 2 Average Individual Expense Bound: if
`f(xHat) - f* ≤ 2 P * rBar / √(N (N + 1))` with positive population factor `P`, then the average
individual expense `\bar f(x) = f(x) / P` satisfies
`\bar f(xHat) - \bar f* ≤ 2 rBar / √(N (N + 1))`, where both optimal values are taken through the
Chapter 1 whole-space owner in `EReal`. -/
theorem average_individual_expense_suboptimality_bound
    (P : ℝ) (f : X → ℝ) (xHat : X) {rBar : ℝ} {N : ℕ}
    (hP : 0 < P)
    (hbound :
      (f xHat : EReal) - (SetConstrainedMinimizationProblem.mk Set.univ f).optimalValue ≤
        (2 * P * rBar) / Real.sqrt (N * (N + 1) : ℝ)) :
    (averageIndividualExpense P f xHat : EReal) -
        (SetConstrainedMinimizationProblem.mk Set.univ
          (averageIndividualExpense P f)).optimalValue ≤
      (2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) := by
  let Δ : EReal := (((2 * rBar) / Real.sqrt (N * (N + 1) : ℝ) : ℝ) : EReal)
  -- First place the Chapter 1 optimal value above the shifted average expense.
  have hlower :
      (averageIndividualExpense P f xHat : EReal) -
          Δ ≤
        (SetConstrainedMinimizationProblem.mk Set.univ
          (averageIndividualExpense P f)).optimalValue := by
    simpa [Δ] using average_expense_lower_le_optimalValue P f xHat hP hbound
  -- Then rearrange that lower bound back into the announced suboptimality estimate.
  have hsum :
      (averageIndividualExpense P f xHat : EReal) ≤
        (SetConstrainedMinimizationProblem.mk Set.univ
          (averageIndividualExpense P f)).optimalValue +
          Δ := by
    have hsum' :=
      (EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mp hlower
    simpa [Δ, add_comm, add_left_comm, add_assoc] using hsum'
  simpa [Δ] using EReal.sub_le_of_le_add' hsum

end

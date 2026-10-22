/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

namespace SeparableOptimizationProblem

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Theorem 5.4.8.1 lies in the separable optimization / standard-form epigraph domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` and `SetConstrainedMinimizationProblem.optimalValue` from
  `Chap01/Definition_1_3_7`, the Chapter 1 owner for feasible-set / objective minimization;
- `LagrangianProblem.toSetConstrainedMinimizationProblem` from `Chap01/Definition_1_10_2`, the
  inherited Chapter 1 owner bridge reached from the source-facing map
  `SeparableOptimizationProblem.toLagrangianProblem`;
- `functionalConstraintStandardFormProblem` from `Proposition_5_3_6_1`, the chapter's standard
  pattern for expressing lifted reformulations directly as a `SetConstrainedMinimizationProblem`
  over raw product data rather than through an extra wrapper structure.

Best owner abstraction:
- source-facing: `problem : SeparableOptimizationProblem E m` together with the textbook
  standard-form variables `(x, τ, t)`;
- core/canonical: `SetConstrainedMinimizationProblem`;
- bridge/view: `StandardFormDecisionVariable problem` and
  `standardFormOptimizationProblem problem`.

Primitive data:
- the base point `x : E`;
- the slack family `τ : Fin (m + 1) → ℝ`;
- the blockwise epigraph family `t`.

Derived API:
- the projection helpers `point`, `epigraphSlack`, and `termSlack`;
- the standard-form Chapter 1 owner `standardFormOptimizationProblem`;
- its objective-evaluation and feasible-set-membership lemmas.

The previous version used a dedicated wrapper structure for the triple `(x, τ, t)`. The chapter's
owner style for standard-form lifts is lighter: keep the Chapter 1 minimization owner primary and
expose the raw lifted data through a thin reusable alias plus projection helpers. The public names
stay the same, but the duplicate wrapper layer is removed. -/

/-- A decision variable of the standard-form epigraph reformulation consists of the original point
`x ∈ E`, slack variables `τ₀, …, τₘ`, and blockwise epigraph variables `tᵢⱼ`. -/
abbrev StandardFormDecisionVariable (problem : SeparableOptimizationProblem E m) :=
  E × (Fin (m + 1) → ℝ) × ((i : Fin (m + 1)) → Fin (problem.blockSize i) → ℝ)

namespace StandardFormDecisionVariable

/-- The original optimization variable `x ∈ E`. -/
abbrev point
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem) : E :=
  decision.1

/-- The slack variables `τ₀, …, τₘ` controlling the weighted block sums. -/
abbrev epigraphSlack
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem) :
    Fin (m + 1) → ℝ :=
  decision.2.1

/-- The epigraph variables `tᵢⱼ` dominating the scalar convex terms. -/
abbrev termSlack
    {problem : SeparableOptimizationProblem E m}
    (decision : StandardFormDecisionVariable problem)
    (i : Fin (m + 1)) :
    Fin (problem.blockSize i) → ℝ :=
  decision.2.2 i

end StandardFormDecisionVariable

open StandardFormDecisionVariable

/-- The standard-form epigraph reformulation minimizes `τ₀` over the triples `(x, τ, t)`
satisfying the weighted block inequalities `∑ⱼ αᵢⱼ tᵢⱼ ≤ τᵢ`, the side constraints
`τᵢ ≤ βᵢ` for `i = 1, …, m`, and the epigraph inequalities
`fᵢⱼ(ℓᵢⱼ(x)) ≤ tᵢⱼ`. -/
def standardFormOptimizationProblem
    (problem : SeparableOptimizationProblem E m) :
    SetConstrainedMinimizationProblem (StandardFormDecisionVariable problem) where
  feasibleSet := {decision |
    (∀ i : Fin (m + 1),
      ∑ j : Fin (problem.blockSize i), problem.weight i j * decision.termSlack i j ≤
        decision.epigraphSlack i) ∧
      (∀ i : Fin m, decision.epigraphSlack i.succ ≤ problem.constraintBound i) ∧
      ∀ i : Fin (m + 1), ∀ j : Fin (problem.blockSize i),
        problem.scalarFunction i j (problem.affineMap i j decision.point) ≤ decision.termSlack i j}
  objective := fun decision ↦ decision.epigraphSlack 0

/-- Evaluating the standard-form objective returns the zeroth slack variable `τ₀`. -/
@[simp] theorem standardFormOptimizationProblem_apply
    (problem : SeparableOptimizationProblem E m)
    (decision : StandardFormDecisionVariable problem) :
    standardFormOptimizationProblem problem decision = decision.epigraphSlack 0 :=
  rfl

/-- Membership in the feasible set of the standard-form reformulation is exactly the conjunction
of the displayed block-sum, side, and epigraph inequalities. -/
@[simp] theorem mem_standardFormOptimizationProblem_feasibleSet_iff
    (problem : SeparableOptimizationProblem E m)
    (decision : StandardFormDecisionVariable problem) :
    decision ∈ (standardFormOptimizationProblem problem).feasibleSet ↔
      (∀ i : Fin (m + 1),
        ∑ j : Fin (problem.blockSize i), problem.weight i j * decision.termSlack i j ≤
          decision.epigraphSlack i) ∧
        (∀ i : Fin m, decision.epigraphSlack i.succ ≤ problem.constraintBound i) ∧
        ∀ i : Fin (m + 1), ∀ j : Fin (problem.blockSize i),
          problem.scalarFunction i j (problem.affineMap i j decision.point) ≤
            decision.termSlack i j :=
  Iff.rfl

-- Proof sketch: lift each feasible `x` for the inherited Chapter 1 owner
-- `(problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem` to the standard-form
-- decision variable with `tᵢⱼ = fᵢⱼ(ℓᵢⱼ(x))` and
-- `τᵢ = ∑ⱼ αᵢⱼ tᵢⱼ`, which preserves the objective value. Conversely, project any feasible
-- standard-form decision variable to its `x`-component; positivity of the weights and the
-- epigraph inequalities imply that the original objective value is bounded by `τ₀`. Comparing
-- the two induced Chapter 1 optimal values yields equality.
/-- Theorem 5.4.8.1: the original separable optimization problem and its standard-form epigraph
reformulation have the same canonical Chapter 1 optimal value. -/
theorem separableOptimizationProblem_optimalValue_eq_standardFormOptimalValue
    (problem : SeparableOptimizationProblem E m) :
    (problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem.optimalValue =
      (standardFormOptimizationProblem problem).optimalValue := by
  let originalProblem : SetConstrainedMinimizationProblem E :=
    (problem : LagrangianProblem E m).toSetConstrainedMinimizationProblem
  let standardProblem := standardFormOptimizationProblem problem
  apply le_antisymm
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨decision, hdecision, rfl⟩
    rw [mem_standardFormOptimizationProblem_feasibleSet_iff] at hdecision
    rcases hdecision with
      ⟨hweighted, hbound, hepigraph⟩
    have hpoint_problem :
        decision.point ∈ problem.feasibleSet := by
      rw [mem_feasibleSet_iff]
      intro i
      calc
        problem.qFunction i.succ decision.point =
            ∑ j : Fin (problem.blockSize i.succ),
              problem.weight i.succ j *
                problem.scalarFunction i.succ j (problem.affineMap i.succ j decision.point) := by
              rw [qFunction_apply]
        _ ≤ ∑ j : Fin (problem.blockSize i.succ),
              problem.weight i.succ j * decision.termSlack i.succ j := by
              refine Finset.sum_le_sum fun j _ ↦ ?_
              exact mul_le_mul_of_nonneg_left (hepigraph i.succ j)
                (le_of_lt (problem.weight_pos i.succ j))
        _ ≤ decision.epigraphSlack i.succ := hweighted i.succ
        _ ≤ problem.constraintBound i := hbound i
    have hpoint : decision.point ∈ originalProblem.feasibleSet := by
      simpa [originalProblem, SeparableOptimizationProblem.feasibleSet] using hpoint_problem
    have horiginal :
        originalProblem.optimalValue ≤ (originalProblem decision.point : EReal) :=
      originalProblem.optimalValue_le_of_mem_feasibleSet hpoint
    have hvalue :
        (originalProblem decision.point : EReal) ≤ (decision.epigraphSlack 0 : EReal) := by
      have hvalue' : problem decision.point ≤ decision.epigraphSlack 0 := by
        calc
          problem decision.point = problem.qFunction 0 decision.point := by simp
          _ =
              ∑ j : Fin (problem.blockSize 0),
                problem.weight 0 j *
                  problem.scalarFunction 0 j (problem.affineMap 0 j decision.point) := by
                rw [qFunction_apply]
          _ ≤ ∑ j : Fin (problem.blockSize 0),
                problem.weight 0 j * decision.termSlack 0 j := by
                refine Finset.sum_le_sum fun j _ ↦ ?_
                exact mul_le_mul_of_nonneg_left (hepigraph 0 j)
                  (le_of_lt (problem.weight_pos 0 j))
          _ ≤ decision.epigraphSlack 0 := hweighted 0
      exact_mod_cast hvalue'
    simpa [originalProblem, standardProblem] using horiginal.trans hvalue
  · rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    let decision : StandardFormDecisionVariable problem :=
      (x,
        fun i ↦
          ∑ j : Fin (problem.blockSize i),
            problem.weight i j * problem.scalarFunction i j (problem.affineMap i j x),
        fun i j ↦ problem.scalarFunction i j (problem.affineMap i j x))
    have hx_problem : x ∈ problem.feasibleSet := by
      simpa [originalProblem, SeparableOptimizationProblem.feasibleSet] using hx
    have hfeasible :
        decision ∈ standardProblem.feasibleSet := by
      rw [mem_standardFormOptimizationProblem_feasibleSet_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp [decision]
      · intro i
        exact (mem_feasibleSet_iff problem x).mp hx_problem i
      · intro i j
        simp [decision]
    have hstandard :
        standardProblem.optimalValue ≤ (standardProblem decision : EReal) :=
      standardProblem.optimalValue_le_of_mem_feasibleSet hfeasible
    simpa [originalProblem, standardProblem, decision, qFunction_apply] using hstandard

end SeparableOptimizationProblem

end

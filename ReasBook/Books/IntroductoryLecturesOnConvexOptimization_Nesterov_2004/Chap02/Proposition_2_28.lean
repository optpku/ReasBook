/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_23

noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Proposition 2.28 lies in the auxiliary max-violation value-function domain for
inequality-constrained problems.

Sampled owner declarations before refining:
- `LagrangianProblem.constrainedAuxiliaryObjective` in `Lemma_2_21`, the canonical owner
  `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue` in `Lemma_2_21`, the owner value
  `f^*(t)` as an `EReal` infimum;
- `LagrangianProblem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn` in `Lemma_2_21`, the
  attained-value bridge from the owner infimum to a real minimizer evaluation;
- `LagrangianProblem.objective_sub_le_constrainedAuxiliaryObjective` and
  `LagrangianProblem.constraint_le_constrainedAuxiliaryObjective` in `Lemma_2_21`, the canonical
  component bounds extracted from the owner auxiliary objective.

Best owner abstraction:
- core/canonical: `problem : LagrangianProblem Q m` together with its derived auxiliary objective
  and auxiliary optimal value;
- source-facing: Proposition 2.28's bounds for an exact minimizer of the owner auxiliary
  objective;
- bridge/view: the attained-minimum identity
  `problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn`.

Primitive data:
- the owner problem `problem : LagrangianProblem Q m`;
- the parameter `t`;
- an exact minimizer witness `hx : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x`.

Derived API:
- the real inequality `problem.constrainedAuxiliaryObjective t x ≤ ε` obtained from the owner
  value bound `problem.constrainedAuxiliaryOptimalValue t ≤ ε`;
- the source-facing Proposition 2.28 bounds extracted directly from the owner component
  inequalities in `Lemma_2_21`.

The refined API keeps Proposition 2.28 at the owner level and avoids a parallel global wrapper.
The trivial attained-value step is the only companion theorem kept here; the proposition itself
uses the owner component inequalities directly rather than introducing extra wrapper lemmas for
their arithmetic consequences. The source-facing proposition keeps the explicit side condition
`t ≤ tStar` as a theorem input rather than a nested implication in the conclusion.
-/

section ExactMinimizerBounds

variable (problem : LagrangianProblem Q m)

/-- An exact minimizer of the auxiliary objective inherits any upper bound on the owner auxiliary
optimal value. -/
theorem constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn
    {t ε : ℝ} {x : Q}
    (hx : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x)
    (hopt : problem.constrainedAuxiliaryOptimalValue t ≤ ε) :
    problem.constrainedAuxiliaryObjective t x ≤ ε := by
  simpa [problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn hx] using hopt

/-- Proposition 2.28: if the owner auxiliary optimal value at `tk` is at most `ε`, then any exact
minimizer `xStar` of the owner auxiliary objective at `tk` satisfies `f₀(xStar) ≤ tStar + ε` and
every constraint value `fᵢ(xStar)` is at most `ε`, provided `tk ≤ tStar`. The companion theorem
`constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn` records the attained-value bound
on the auxiliary objective itself. -/
theorem objective_and_constraint_bounds_of_constrainedAuxiliaryOptimalValue_le
    {tk ε tStar : ℝ} {xStar : Q}
    (hxStar : IsMinOn (problem.constrainedAuxiliaryObjective tk) Set.univ xStar)
    (hopt : problem.constrainedAuxiliaryOptimalValue tk ≤ ε)
    (htk : tk ≤ tStar) :
    problem xStar ≤ tStar + ε ∧
      ∀ i : Fin m, problem.constraints i xStar ≤ ε := by
  have haux :
      problem.constrainedAuxiliaryObjective tk xStar ≤ ε :=
    problem.constrainedAuxiliaryObjective_le_of_optimalValue_le_of_isMinOn hxStar hopt
  constructor
  · have hobjective : problem xStar - tk ≤ ε :=
      (problem.objective_sub_le_constrainedAuxiliaryObjective tk xStar).trans haux
    linarith
  · intro i
    exact (problem.constraint_le_constrainedAuxiliaryObjective tk xStar i).trans haux

end ExactMinimizerBounds

end LagrangianProblem

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E}

/- Definition 6.52 lies in the chapter's conditional-gradient oracle / constrained-minimization
domain.

Mandatory domain-style sampling before refinement:
- `linearOptimizationOracleObjective` in `Theorem_6_11`, the Chapter 6 owner of the source-facing
  oracle objective `x ↦ s x + Ψ x` on the feasible subtype `Q`;
- `constrainedArgmin` with notation `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the project owner for minimizer sets on a feasible set;
- `LinearOracleCompositeMethod.oraclePoint_mem_argmin` in `Algorithm_6_4`, the downstream chapter
  surface already using oracle outputs as points of the canonical argmin set for
  `linearOptimizationOracleObjective`;
- `IsSmoothedDualMinimizerSelection` in `Definition_6_33`, the nearby Chapter 6 pattern for a
  source-facing oracle-selection predicate built on top of an existing argmin owner instead of a
  duplicate wrapper structure.

Best owner abstraction:
- source-facing: `IsLinearOptimizationOracle`;
- core/canonical: `linearOptimizationOracleObjective` together with
  `argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)`;
- bridge/view: the pointwise argmin-membership, `IsMinOn`, and objective-comparison lemmas below.

Primitive data:
- a feasible set `Q : Set E`;
- a regularizer `Ψ : Q → ℝ`;
- a candidate oracle selection `vPsi : StrongDual ℝ E → Q`.

Derived API:
- pointwise membership of `vPsi s` in the canonical argmin set for the oracle objective;
- the induced `IsMinOn` statement on the feasible subtype `Q`;
- the resulting objective comparison against any feasible point.

Source/core/bridge triage:
- source-facing: the selected oracle map `s ↦ v_Ψ(s)`;
- core/canonical: `linearOptimizationOracleObjective` and `argmin[Set.univ]`;
- bridge/view: `IsLinearOptimizationOracle.apply`,
  `IsLinearOptimizationOracle.isMinOn`, and
  `IsLinearOptimizationOracle.objective_le`.

The previous file introduced a second public owner `LinearOptimizationOracle` whose primitive data
stored a bare linear minimization rule `x ↦ s x`, dropping the regularizer `Ψ` that is part of the
Chapter 6 conditional-gradient oracle notion. This refinement keeps only the source-facing
selection predicate on top of the existing chapter owner
`linearOptimizationOracleObjective`, so downstream oracle usage stays on the canonical argmin
surface already used in `Theorem_6_11` and `Algorithm_6_4`.
-/

/-- Definition 6.52: a conditional-gradient linear optimization oracle for the regularizer `Ψ`
assigns to each linear functional `s` a feasible point `v_Ψ(s)` belonging to the canonical argmin
set of the Chapter 6 oracle objective `x ↦ s x + Ψ x` on the feasible subtype `Q`. -/
def IsLinearOptimizationOracle
    (Ψ : Q → ℝ) (vPsi : StrongDual ℝ E → Q) : Prop :=
  ∀ s : StrongDual ℝ E,
    vPsi s ∈ argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)

/-- Evaluating a linear optimization oracle at `s` yields a point of the canonical argmin set
defining the conditional-gradient oracle output `v_Ψ(s)`. -/
theorem IsLinearOptimizationOracle.apply
    {Ψ : Q → ℝ} {vPsi : StrongDual ℝ E → Q}
    (hvPsi : IsLinearOptimizationOracle Ψ vPsi) (s : StrongDual ℝ E) :
    vPsi s ∈ argmin[Set.univ] (linearOptimizationOracleObjective s Ψ) :=
  hvPsi s

/-- Evaluating a linear optimization oracle at `s` yields a minimizer of the Chapter 6 oracle
objective on the feasible subtype `Q`. -/
theorem IsLinearOptimizationOracle.isMinOn
    {Ψ : Q → ℝ} {vPsi : StrongDual ℝ E → Q}
    (hvPsi : IsLinearOptimizationOracle Ψ vPsi) (s : StrongDual ℝ E) :
    IsMinOn (linearOptimizationOracleObjective s Ψ) Set.univ (vPsi s) :=
  (mem_constrainedArgmin_iff.mp (hvPsi.apply s)).2

/-- The oracle value `v_Ψ(s)` has oracle-objective value at most that of any other feasible
point. -/
theorem IsLinearOptimizationOracle.objective_le
    {Ψ : Q → ℝ} {vPsi : StrongDual ℝ E → Q}
    (hvPsi : IsLinearOptimizationOracle Ψ vPsi)
    (s : StrongDual ℝ E) (x : Q) :
    linearOptimizationOracleObjective s Ψ (vPsi s) ≤
      linearOptimizationOracleObjective s Ψ x :=
  isMinOn_univ_iff.mp (hvPsi.isMinOn s) x

end

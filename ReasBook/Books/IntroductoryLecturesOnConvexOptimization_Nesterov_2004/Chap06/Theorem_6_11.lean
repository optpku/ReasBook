/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q : Set E}

/- Theorem 6.11 lies in the Chapter 6 constrained-minimization / primal-oracle domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` with notation `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the project owner for minimizer sets;
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the Chapter 6 pattern of keeping the
  objective/problem as the source-facing owner and deriving minimizers canonically;
- `AffineVariationalInequalityProblem.gapProblem` in `Chap06/Definition_6_18`, the nearby Chapter
  6 owner pattern using `Set.univ` on a feasible subtype.

Best owner abstraction:
- source-facing: `linearOptimizationOracleObjective`;
- core/canonical: `argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)`;
- bridge/view: the pointwise evaluation formula and the translation from `IsMinOn` attainment to
  argmin membership.

Primitive data:
- a feasible set `Q : Set E`;
- a linear functional `s : StrongDual ℝ E`;
- a regularizer `Ψ : Q → ℝ`.

Derived API:
- the affine-plus-regularizer objective on the feasible subtype `Q`;
- its canonical minimizer set `argmin[Set.univ] (linearOptimizationOracleObjective s Ψ)`.

Source/core/bridge triage:
- source-facing: `linearOptimizationOracleObjective`;
- core/canonical: `argmin[Set.univ]`;
- bridge/view: `linearOptimizationOracleObjective_apply` and
  `exists_linear_optimization_oracle_point`.

The previous theorem encoded existence of an optimal point through equality with
`sInf (Set.range ...)`. In this project domain, minimizers are canonically owned by `argmin`,
so the main existence theorem now lands in that owner instead of keeping a parallel value-level
existence surface.
-/

/-- The affine-plus-regularizer objective `x ↦ ⟨s, x⟩ + Ψ(x)` on the feasible set `Q`, viewed as
a function on the subtype `Q`. -/
def linearOptimizationOracleObjective (s : StrongDual ℝ E) (Ψ : Q → ℝ) : Q → ℝ :=
  fun x ↦ s x + Ψ x

/-- Evaluating `linearOptimizationOracleObjective s Ψ` at a feasible point `x : Q` gives the sum
of the linear functional value `s x` and the regularizer value `Ψ x`. -/
@[simp]
theorem linearOptimizationOracleObjective_apply
    (s : StrongDual ℝ E) (Ψ : Q → ℝ) (x : Q) :
    linearOptimizationOracleObjective s Ψ x = s x + Ψ x :=
  rfl

/-- Theorem 6.11: if the problem
`min_{x ∈ Q} {⟨s, x⟩ + Ψ(x)}`
admits an optimal solution, then there exists a feasible point `v_Ψ(s)` in the canonical minimizer
set of `linearOptimizationOracleObjective s Ψ` on the feasible subtype `Q`. -/
theorem exists_linear_optimization_oracle_point
    (s : StrongDual ℝ E) (Ψ : Q → ℝ)
    (hattains : ∃ x : Q, IsMinOn (linearOptimizationOracleObjective s Ψ) Set.univ x) :
    ∃ vPsi : Q,
      vPsi ∈ argmin[Set.univ] (linearOptimizationOracleObjective s Ψ) := by
  rcases hattains with ⟨vPsi, hvPsi⟩
  refine ⟨vPsi, ?_⟩
  rw [mem_constrainedArgmin_iff]
  exact ⟨by simp, hvPsi⟩

end

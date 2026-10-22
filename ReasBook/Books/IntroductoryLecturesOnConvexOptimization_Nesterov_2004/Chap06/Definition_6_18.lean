/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.18 lies in the affine variational-inequality / gap-function / constrained-
minimization domain.

Sampled owner-style declarations:
- `AffineVariationalInequalityProblem` in `Definition_6_17`, the Chapter 6 owner of the primitive
  data `(Q, B)` for an affine variational inequality;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of an
  optimization problem with a feasible set and real-valued objective;
- `constrainedArgmin` / `argmin[Q]` in `Chap01/Definition_1_3_3`, the canonical owner of feasible
  minimizers on a set;
- `explicitModelSmoothedProblem` in `Definition_6_9`, the chapter pattern of keeping the
  optimization problem itself as the owner and deriving its argmin through the Chapter 1 API.

Best owner abstraction:
- source-facing: the gap function of `problem : AffineVariationalInequalityProblem E`;
- core/canonical: `AffineVariationalInequalityProblem E`, `SetConstrainedMinimizationProblem`, and
  `argmin[Q] f`;
- bridge/view: the associated gap-minimization problem on the feasible subtype.

Primitive data:
- no new primitive data beyond the owner `problem : AffineVariationalInequalityProblem E`.

Derived API:
- `problem.gapFunction : problem.feasibleSet → ℝ`;
- `problem.gapProblem : SetConstrainedMinimizationProblem problem.feasibleSet`;
- the canonical minimizer set `argmin[Set.univ] problem.gapFunction`.

Source/core/bridge triage:
- source-facing: `AffineVariationalInequalityProblem.gapFunction`;
- core/canonical: `AffineVariationalInequalityProblem E` and the Chapter 1 minimization owners;
- bridge/view: `AffineVariationalInequalityProblem.gapProblem`.

The previous file duplicated the primitive VI data by taking `(Q, B)` as separate parameters and
introduced a second public argmin wrapper. This refinement reuses the Chapter 6 owner
`AffineVariationalInequalityProblem E`, keeps the gap function as the mathematical object defined
by the source, and lets feasible minimizers be derived canonically via `argmin`.
-/

namespace AffineVariationalInequalityProblem

/-- For Definition 6.18, the associated gap function `ψ : Q → ℝ` sends a feasible point `w` to
`max_{v ∈ Q} ⟪B(v), w - v⟫`, encoded as the supremum over the feasible subtype `Q`. -/
def gapFunction (problem : AffineVariationalInequalityProblem E) :
    problem.feasibleSet → ℝ :=
  fun w ↦
    sSup
      (Set.range fun v : problem.feasibleSet ↦
        problem (v : E) ((w : E) - (v : E)))

/-- Definition 6.18: expanding the gap function at a feasible point recovers the defining
supremum of affine residuals over all feasible comparison points. -/
-- Proof sketch: unfold `gapFunction`.
theorem gapFunction_def
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapFunction w =
      sSup
        (Set.range fun v : problem.feasibleSet ↦
          problem (v : E) ((w : E) - (v : E))) := by
  -- Unfold the definition so the goal becomes a definitional equality.
  rfl

/-- Evaluating the gap function gives the supremum of the affine residuals over the feasible
set. -/
@[simp] theorem gapFunction_apply
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapFunction w =
      sSup
        (Set.range fun v : problem.feasibleSet ↦
          problem (v : E) ((w : E) - (v : E))) :=
  rfl

/-- The associated optimization problem `min_{w ∈ Q} ψ(w)`, viewed canonically on the feasible
subtype. Its minimizer set is the Chapter 1 owner `argmin[Set.univ] problem.gapFunction`. -/
def gapProblem (problem : AffineVariationalInequalityProblem E) :
    SetConstrainedMinimizationProblem problem.feasibleSet where
  feasibleSet := Set.univ
  objective := problem.gapFunction

/-- The feasible set of the associated gap-minimization problem is the whole feasible subtype. -/
@[simp] theorem gapProblem_feasibleSet
    (problem : AffineVariationalInequalityProblem E) :
    problem.gapProblem.feasibleSet = Set.univ :=
  rfl

/-- Evaluating the associated gap-minimization problem recovers the gap function. -/
@[simp] theorem gapProblem_apply
    (problem : AffineVariationalInequalityProblem E) (w : problem.feasibleSet) :
    problem.gapProblem w = problem.gapFunction w :=
  rfl

end AffineVariationalInequalityProblem

end

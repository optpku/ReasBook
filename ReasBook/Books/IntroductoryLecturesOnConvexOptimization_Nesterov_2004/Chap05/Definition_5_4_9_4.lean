/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/- Definition 5.4.9.4 lies in the Chapter 5 box-constrained `ℓ_p` approximation / barrier-model
Lagrangian domain.

Sampled owner declarations:
- `LpApproximationEpigraphPoint`, `objectiveSlack`, and `residualSlack` in
  `Theorem_5_4_8_9`, the existing chapter owner for the lifted decision variables;
- `lpApproximationEpigraphProblem` and
  `mem_lpApproximationEpigraphProblem_feasibleSet_iff` in `Theorem_5_4_8_9`, the chapter owner
  for the lifted reformulation and its feasible-set expansion;
- `LagrangianProblem` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite families of inequality constraints;
- `LpApproximationBoxProblem.feasibleSet` in `Definition_5_4_9_1`, the source-facing chapter
  owner for the box constraints.

Best owner abstraction:
- source-facing: the barrier-model reformulation attached to a box-constrained `ℓ_p`
  approximation problem;
- core/canonical: `LagrangianProblem (LpApproximationEpigraphPoint n m) (m + (1 + (n + n)))`;
- bridge/view: `barrierModelProblem`, whose objective and feasible set are compared directly with
  the existing epigraph owners.

Primitive data:
- no new primitive data beyond `problem : LpApproximationBoxProblem n m`;
- the lifted decision variables are reused from `LpApproximationEpigraphPoint n m`, with
  `objectiveSlack` playing the role of the textbook `ξ` and `residualSlack` the role of `τ`.

Derived API:
- `problem.barrierModelProblem`;
- the objective evaluation bridge `barrierModelProblem_apply`;
- the feasible-set bridge `mem_barrierModelProblem_feasibleSet_iff`.

The previous version introduced a second public owner `LpBarrierModelPoint` for the same lifted
decision data already provided by `LpApproximationEpigraphPoint`. This refinement deletes that
duplicate wheel and makes Definition 5.4.9.4 a direct Lagrangian-owner presentation of the
existing epigraph lift.
-/

/-- Definition 5.4.9.4: the barrier-model reformulation of a box-constrained `ℓ_p`
approximation problem is the Chapter 1 Lagrangian problem on the existing lifted decision points
`LpApproximationEpigraphPoint n m`, where `objectiveSlack` plays the role of the scalar variable
`ξ` and `residualSlack` plays the role of the residual bounds `τ`. Its inequality constraints are
the residual epigraph constraints, the coupling inequality `∑ i, τᵢ ≤ ξ`, and the coordinatewise
box constraints. -/
def barrierModelProblem
    (problem : LpApproximationBoxProblem n m) :
    LagrangianProblem (LpApproximationEpigraphPoint n m) (m + (1 + (n + n))) where
  objective := objectiveSlack
  constraints :=
    Fin.addCases
      (fun i decision ↦
        |⟪problem.a i, decision.point⟫ - problem.b i| ^ (problem.p : ℝ) -
          decision.residualSlack i)
      (Fin.addCases
        (fun _ decision ↦ (∑ i : Fin m, decision.residualSlack i) - decision.objectiveSlack)
        (Fin.addCases
          (fun j decision ↦ problem.α j - decision.point j)
          (fun j decision ↦ decision.point j - problem.β j)))

/-- Evaluating the barrier-model problem returns the lifted objective slack `ξ`. -/
@[simp] theorem barrierModelProblem_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    problem.barrierModelProblem decision = decision.objectiveSlack :=
  rfl

/-- Membership in the feasible set of `problem.barrierModelProblem` is exactly membership in the
existing epigraph feasible-set owner for the same lifted reformulation. -/
@[simp] theorem mem_barrierModelProblem_feasibleSet_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    decision ∈ problem.barrierModelProblem.feasibleSet ↔
      decision ∈
        (lpApproximationEpigraphProblem
          problem.p problem.a problem.b problem.α problem.β).feasibleSet := by
  rw [problem.barrierModelProblem.mem_feasibleSet_iff,
    mem_lpApproximationEpigraphProblem_feasibleSet_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact sub_nonpos.mp <| by
        simpa [barrierModelProblem] using h (Fin.castAdd (1 + (n + n)) i)
    · exact sub_nonpos.mp <| by
        simpa [barrierModelProblem] using
          h (Fin.natAdd m (Fin.castAdd (n + n) (0 : Fin 1)))
    · rw [mem_lpApproximationProblem_feasibleSet_iff]
      intro j
      refine ⟨?_, ?_⟩
      · exact sub_nonpos.mp <| by
          simpa [barrierModelProblem] using
            h (Fin.natAdd m (Fin.natAdd 1 (Fin.castAdd n j)))
      · have hj := h (Fin.natAdd m (Fin.natAdd 1 (Fin.natAdd n j)))
        dsimp [barrierModelProblem] at hj
        rwa [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, sub_nonpos] at hj
  · rintro ⟨hres, hsum, hbox⟩
    rw [mem_lpApproximationProblem_feasibleSet_iff] at hbox
    intro k
    induction k using Fin.addCases with
    | left i =>
        simpa [barrierModelProblem] using sub_nonpos.mpr (hres i)
    | right k =>
        induction k using Fin.addCases with
        | left _ =>
            simpa [barrierModelProblem] using sub_nonpos.mpr hsum
        | right k =>
            induction k using Fin.addCases with
            | left j =>
                simpa [barrierModelProblem] using sub_nonpos.mpr (hbox j).1
            | right j =>
                dsimp [barrierModelProblem]
                rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, sub_nonpos]
                exact (hbox j).2

end LpApproximationBoxProblem

end

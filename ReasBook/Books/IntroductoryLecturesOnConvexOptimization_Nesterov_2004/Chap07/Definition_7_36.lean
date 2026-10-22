/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n - 1))

/- Definition 7.36 lies in the finite max-type objective / unconstrained minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.mk Set.univ f` in `Chap03/Definition_3_33`, the chapter
  pattern for whole-space unconstrained problems;
- `maxTypeObjective` and `maxTypeObjective_apply` in `Chap02/Definition_2_39`, the project owner for
  pointwise maxima of nonempty finite families;
- `maxAbsoluteValueOptimizationObjective` and `maxAbsoluteValueOptimizationProblem` in
  `Chap06/Definition_6_21`, the nearby source-facing pattern of building a max-type objective
  first and then packaging the associated minimization problem through the Chapter 1 owner.

Best owner abstraction:
- source-facing: the residual objective `minMaxAbsoluteDeviationObjective hm a c`;
- core/canonical: `maxTypeObjective` for the finite maximum and
  `SetConstrainedMinimizationProblem E` for the optimization layer;
- bridge/view: `linearProgrammingMinMaxAbsoluteDeviationProblem hm a c`.

Primitive data:
- the positive number of residuals `m`, expressed by `hm : 0 < m`;
- the row vectors `a : Fin m → E`;
- the offsets `c : Fin m → ℝ`.

Derived API:
- the max-type objective `y ↦ maxᵢ |⟪aᵢ, y⟫ - cᵢ|`;
- the whole-space optimization problem
  `SetConstrainedMinimizationProblem.mk Set.univ (minMaxAbsoluteDeviationObjective hm a c)`;
- the objective and feasible-set evaluation lemmas below.

Source/core/bridge triage:
- source-facing: Definition 7.36's min-max absolute deviation objective and its associated
  whole-space minimization problem;
- core/canonical: `maxTypeObjective` and `SetConstrainedMinimizationProblem`;
- bridge/view: the explicit `Finset.sup'` expansion of the objective and the `Set.univ` feasible
  set identity.

This refinement deletes the duplicate local minimization-problem wrapper and reuses the Chapter 1
owner directly. The source-facing objective remains explicit, but its finite-maximum structure is
now owned by `maxTypeObjective` rather than a bespoke `Finset.sup'` definition.
-/

/-- The objective `y ↦ maxᵢ |⟪aᵢ, y⟫ - cᵢ|` of the min-max absolute deviation problem on
`ℝ^(n - 1)`. -/
def minMaxAbsoluteDeviationObjective
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) : E → ℝ :=
  let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  maxTypeObjective fun i y ↦ |inner ℝ (a i) y - c i|

/-- Evaluating the min-max absolute deviation objective gives the finite maximum of the absolute
residuals `|⟪aᵢ, y⟫ - cᵢ|`. -/
@[simp] theorem minMaxAbsoluteDeviationObjective_apply
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) (y : E) :
    minMaxAbsoluteDeviationObjective hm a c y =
      Finset.univ.sup' ⟨⟨0, hm⟩, by simp⟩ (fun i : Fin m ↦ |inner ℝ (a i) y - c i|) := by
  let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simpa [minMaxAbsoluteDeviationObjective] using
    (maxTypeObjective_apply (fun i y ↦ |inner ℝ (a i) y - c i|) y)

/-- Definition 7.36: given vectors `a i ∈ ℝ^(n - 1)` and scalars `c i ∈ ℝ` for `i = 1, …, m`,
the linear-programming min-max absolute deviation problem is the unconstrained minimization
problem on `ℝ^(n - 1)` with objective `y ↦ maxᵢ |⟪aᵢ, y⟫ - cᵢ|`. -/
def linearProgrammingMinMaxAbsoluteDeviationProblem
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    SetConstrainedMinimizationProblem E :=
  .mk Set.univ (minMaxAbsoluteDeviationObjective hm a c)

/-- The feasible set of the min-max absolute deviation problem is all of `ℝ^(n - 1)`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_feasibleSet
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    (linearProgrammingMinMaxAbsoluteDeviationProblem hm a c).feasibleSet = Set.univ :=
  rfl

/-- The Definition 7.36 problem is exactly the Chapter 1 whole-space minimization owner with
objective `minMaxAbsoluteDeviationObjective hm a c`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_mk
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    linearProgrammingMinMaxAbsoluteDeviationProblem hm a c =
      SetConstrainedMinimizationProblem.mk Set.univ
        (minMaxAbsoluteDeviationObjective hm a c) :=
  rfl

/-- The objective field of the min-max absolute deviation problem is exactly the source-facing
objective `minMaxAbsoluteDeviationObjective hm a c`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_objective
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    (linearProgrammingMinMaxAbsoluteDeviationProblem hm a c).objective =
      minMaxAbsoluteDeviationObjective hm a c :=
  rfl

-- Proof sketch: unfold `linearProgrammingMinMaxAbsoluteDeviationProblem`; coercing the packaged
-- Chapter 1 owner to a function exposes its `objective` field.
/-- Coercing the Definition 7.36 problem to a function recovers the source-facing min-max
absolute deviation objective. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_coe
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    ⇑(linearProgrammingMinMaxAbsoluteDeviationProblem hm a c) =
      minMaxAbsoluteDeviationObjective hm a c :=
  rfl

/-- Unfolding the min-max absolute deviation problem recovers the whole-space constrained problem
with objective `minMaxAbsoluteDeviationObjective hm a c`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_def
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) :
    linearProgrammingMinMaxAbsoluteDeviationProblem hm a c =
      { feasibleSet := Set.univ
        objective := minMaxAbsoluteDeviationObjective hm a c } :=
  rfl

/-- Evaluating the min-max absolute deviation problem as a function returns its objective. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_apply
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) (y : E) :
    linearProgrammingMinMaxAbsoluteDeviationProblem hm a c y =
      minMaxAbsoluteDeviationObjective hm a c y :=
  rfl

-- Proof sketch: rewrite the feasible set with
-- `linearProgrammingMinMaxAbsoluteDeviationProblem_feasibleSet`.
/-- A point is feasible for the Definition 7.36 problem automatically, since its feasible set is
all of `ℝ^(n - 1)`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_mem_feasibleSet_iff
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) {y : E} :
    y ∈ (linearProgrammingMinMaxAbsoluteDeviationProblem hm a c).feasibleSet ↔ True := by
  -- Rewrite feasibility through the owner-level description of the whole-space feasible set.
  rw [linearProgrammingMinMaxAbsoluteDeviationProblem_feasibleSet]
  -- Membership in the universal feasible set is tautologically true.
  simp

/-- Evaluating the objective of the min-max absolute deviation problem gives
`maxᵢ |⟪aᵢ, y⟫ - cᵢ|`. -/
@[simp] theorem linearProgrammingMinMaxAbsoluteDeviationProblem_objective_apply
    (hm : 0 < m) (a : Fin m → E) (c : Fin m → ℝ) (y : E) :
    (linearProgrammingMinMaxAbsoluteDeviationProblem hm a c).objective y =
      Finset.univ.sup' ⟨⟨0, hm⟩, by simp⟩ (fun i : Fin m ↦ |inner ℝ (a i) y - c i|) := by
  exact minMaxAbsoluteDeviationObjective_apply hm a c y

end

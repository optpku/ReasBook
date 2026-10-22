/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_48

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.66 lies in the chapter's set-constrained convex optimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the owner of a feasible set
  together with a real-valued ambient objective;
- `SetConstrainedMinimizationProblem.comap` in `Chap01/Definition_1_3_3`, the canonical bridge
  for transporting a constrained problem along an equivalence;
- `kelleyCompleteObjective` in `Chap03/Proposition_3_48`, the source-facing objective
  `f(y, x) = max {|y|, ‖x‖²}`;
- `kelleyCompleteFeasibleSet` in `Chap03/Proposition_3_48`, the source-facing feasible set
  `Q = {(y, x) | y² + ‖x‖² ≤ 1}`.

Best owner abstraction:
- source-facing: the constrained problem `min {f(y, x) | (y, x) ∈ Q}`;
- core/canonical:
  `SetConstrainedMinimizationProblem.mk kelleyCompleteFeasibleSet kelleyCompleteObjective`;
- bridge/view: the `WithLp` transport `kelleyCompleteProblemL2`.

Primitive data:
- the explicit objective `kelleyCompleteObjective`;
- the explicit feasible set `kelleyCompleteFeasibleSet`.

Derived API:
- the packaged owner problem `kelleyCompleteProblem`;
- the `L²` transport `kelleyCompleteProblemL2`.

Definition 3.66 therefore contributes the canonical constrained-problem owner built from the
already exposed explicit objective and feasible set, while keeping the `WithLp` transport only as a
downstream bridge for the Kelley-method API.
-/

noncomputable section

open scoped ConstrainedArgmin

section

variable (n : ℕ)

local notation "Z" => ℝ × EuclideanSpace ℝ (Fin n)

/-- Definition 3.66: the complete-data optimization problem is the constrained minimization
problem on `ℝ × ℝⁿ` with objective `f(y, x) = max {|y|, ‖x‖²}` and feasible set
`Q = {(y, x) | y² + ‖x‖² ≤ 1}`. -/
abbrev kelleyCompleteProblem :
    SetConstrainedMinimizationProblem Z where
  feasibleSet := kelleyCompleteFeasibleSet
  objective := kelleyCompleteObjective

/-- The feasible set of `kelleyCompleteProblem n` is exactly the complete-data set `Q`. -/
@[simp] theorem kelleyCompleteProblem_feasibleSet :
    (kelleyCompleteProblem n).feasibleSet = kelleyCompleteFeasibleSet :=
  rfl

/-- Evaluating `kelleyCompleteProblem n` recovers the complete-data objective
`f(y, x) = max {|y|, ‖x‖²}`. -/
@[simp] theorem kelleyCompleteProblem_apply
    (z : Z) :
    kelleyCompleteProblem n z = kelleyCompleteObjective z :=
  rfl

/-- Minimizing `kelleyCompleteProblem n` on its feasible set is exactly minimizing
`kelleyCompleteObjective` on the complete-data feasible set `Q`. -/
@[simp] theorem kelleyCompleteProblem_isMinOn_iff
    {z : Z} :
    IsMinOn (kelleyCompleteProblem n) (kelleyCompleteProblem n).feasibleSet z ↔
      IsMinOn kelleyCompleteObjective kelleyCompleteFeasibleSet z :=
  Iff.rfl

/-- Membership in the feasible set of `kelleyCompleteProblem n` is exactly the defining
quadratic constraint `y² + ‖x‖² ≤ 1`. -/
@[simp] theorem mem_kelleyCompleteProblem_feasibleSet_iff
    {z : Z} :
    z ∈ (kelleyCompleteProblem n).feasibleSet ↔
      z.1 ^ (2 : ℕ) + ‖z.2‖ ^ (2 : ℕ) ≤ 1 := by
  rw [kelleyCompleteProblem_feasibleSet, mem_kelleyCompleteFeasibleSet_iff]

/-- The constrained minimizer set of `kelleyCompleteProblem n` is the singleton containing the
origin. -/
theorem kelleyCompleteProblem_argmin_eq_singleton_origin :
    (argmin[(kelleyCompleteProblem n).feasibleSet] (kelleyCompleteProblem n) : Set Z) =
      ({(0 : Z)} : Set Z) := by
  have h :
      (argmin[kelleyCompleteFeasibleSet] kelleyCompleteObjective : Set Z) =
        ({(0 : Z)} : Set Z) :=
    kelleyCompleteArgmin_eq_singleton_origin
  simpa [kelleyCompleteProblem] using h

/-- The complete-data problem transported to the intrinsic `L²` product used by `KelleyMethod`.
-/
abbrev kelleyCompleteProblemL2 :
    SetConstrainedMinimizationProblem (WithLp 2 Z) :=
  (kelleyCompleteProblem n).comap (WithLp.equiv 2 Z)

/-- Evaluating the `L²`-transported complete-data problem amounts to evaluating the original
problem after the canonical `WithLp` equivalence. -/
@[simp] theorem kelleyCompleteProblemL2_apply
    (z : WithLp 2 Z) :
    kelleyCompleteProblemL2 n z =
      kelleyCompleteProblem n ((WithLp.equiv 2 Z) z) := by
  simp [kelleyCompleteProblemL2]

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient PositiveDefMatrixNorm SmoothConvex

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.39 lies in constrained smooth convex minimization on `ℝⁿ` with a weighted
Euclidean norm.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for the
  primitive feasible-set and objective data;
- `ConvexC1SeminormSmooth` in `Chap02/Theorem_2_5`, the canonical owner for convex `C¹`
  objectives with a gradient-Lipschitz bound relative to a seminorm and its dual norm;
- `positiveDefMatrixNorm` in `Chap07/Definition_7_23`, the source-facing weighted seminorm
  attached to a positive-definite matrix;
- `Definition_3_64`, which keeps the feasible-set side on the ambient constrained owner rather
  than duplicating that data inside a second objective wrapper.

Best owner abstraction:
- source-facing: `CompositeSmoothConvexMinimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem E` for `Q` and `φ`, together with
  `ConvexC1SeminormSmooth (positiveDefMatrixNorm G hG) L φ`;
- bridge/view: the notations `‖·‖[G]` and `‖·‖[G,*]` supplied by `positiveDefMatrixNorm`.

Primitive data:
- the feasible set and objective, owned by `SetConstrainedMinimizationProblem E`;
- a positive-definite matrix `G`;
- a positive Lipschitz constant encoded canonically by `NNRealˣ`;
- nonemptiness, closedness, and convexity of the feasible set;
- the single smoothness owner witness for the objective.

Derived API:
- whole-space convexity of the objective;
- whole-space differentiability of the objective;
- the weighted dual-norm gradient-Lipschitz inequality.

The previous version stored the objective-side convexity, differentiability, and
gradient-Lipschitz properties as separate primitive fields. This refinement keeps the
source-facing problem structure, but moves the ambient problem data onto
`SetConstrainedMinimizationProblem` and the smoothness package onto the canonical Chapter 2 owner
`ConvexC1SeminormSmooth`. -/

/-- Definition 7.39: a composite smooth convex minimization problem consists of a nonempty closed
convex feasible set `Q ⊆ ℝⁿ`, a convex differentiable objective `φ : ℝⁿ → ℝ`, a positive-definite
matrix `G` defining the weighted norm `‖·‖_G`, and a positive constant `L` such that
`‖∇φ(x) - ∇φ(y)‖*_G ≤ L ‖x - y‖_G` for all `x, y ∈ ℝⁿ`. The feasible-set and objective pair is
owned canonically by `SetConstrainedMinimizationProblem`, and the objective-side smoothness data
is owned by `ConvexC1SeminormSmooth` for the weighted seminorm from Definition 7.23. -/
structure CompositeSmoothConvexMinimizationProblem (n : ℕ)
    extends SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  /-- The positive-definite matrix defining the weighted norm `‖·‖_G`. -/
  metricMatrix : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}
  /-- The Lipschitz constant `L > 0`, encoded canonically as a positive nonnegative real. -/
  lipschitzConstant : NNRealˣ
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective belongs to the weighted smooth-convex class
  `𝓕[(L : NNReal), positiveDefMatrixNorm G]¹¹`. -/
  objective_smooth :
    ConvexC1SeminormSmooth
      (positiveDefMatrixNorm metricMatrix.1 metricMatrix.2)
      (lipschitzConstant : NNReal)
      objective

namespace CompositeSmoothConvexMinimizationProblem

variable {n : ℕ}

/-- A composite smooth convex minimization problem can be used as its underlying objective
function. -/
instance : CoeFun (CompositeSmoothConvexMinimizationProblem n)
    (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply
    (problem : CompositeSmoothConvexMinimizationProblem n)
    (x : EuclideanSpace ℝ (Fin n)) :
    problem x = problem.objective x :=
  rfl

/-- The objective lies in the weighted smooth-convex class attached to `problem.metricMatrix`
with constant `problem.lipschitzConstant`. -/
theorem objective_mem_F11
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    problem.objective ∈
      𝓕[(problem.lipschitzConstant : NNReal),
        positiveDefMatrixNorm problem.metricMatrix.1 problem.metricMatrix.2]¹¹ := by
  simpa [mem_F11_iff] using problem.objective_smooth

/-- The objective of a composite smooth convex minimization problem is convex on all of `ℝⁿ`. -/
theorem objective_convex
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    ConvexOn ℝ Set.univ problem.objective :=
  problem.objective_smooth.convexOn

/-- The objective of a composite smooth convex minimization problem is differentiable on all of
`ℝⁿ`. -/
theorem objective_differentiable
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    Differentiable ℝ problem.objective :=
  let hcontDiff : ContDiff ℝ 1 problem.objective := problem.objective_smooth.contDiff
  hcontDiff.differentiable_one

/-- The weighted smoothness constant is strictly positive because it is encoded by `NNRealˣ`. -/
theorem lipschitzConstant_pos
    (problem : CompositeSmoothConvexMinimizationProblem n) :
    0 < (problem.lipschitzConstant : ℝ) := by
  exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero problem.lipschitzConstant))

/-- The gradient of the objective is `(problem.lipschitzConstant)`-Lipschitz from the weighted
norm `‖·‖[problem.metricMatrix]` to the dual norm `‖·‖[problem.metricMatrix,*]`. -/
theorem gradient_lipschitz
    (problem : CompositeSmoothConvexMinimizationProblem n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖∇ problem.objective x - ∇ problem.objective y‖[problem.metricMatrix,*] ≤
      (problem.lipschitzConstant : ℝ) * ‖x - y‖[problem.metricMatrix] := by
  simpa using problem.objective_smooth.dualNorm_gradient_sub_le x y

end CompositeSmoothConvexMinimizationProblem

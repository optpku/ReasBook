/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Remark_6_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PositiveDefMatrixNorm

variable {m : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Definition 7.46 lies in the weighted Euclidean prox-function domain.

Sampled owner-style declarations:
- `Seminorm.quadraticDistanceTo` in `Chap06/Remark_6_1_1`, the chapter owner of quadratic prox
  terms attached to a chosen seminorm;
- `positiveDefMatrixNorm` in `Definition_7_23`, the Chapter 7 owner of the weighted norm induced
  by a positive-definite matrix;
- `PositiveDefMatrixNorm` notation `‖x‖[G]` in `Definition_7_23`, the canonical source-facing
  surface for that norm;
- `quadraticDistanceTo` in `Chap06/Remark_6_1_1`, the Euclidean special case of the same
  quadratic prox construction.

Best owner abstraction:
- source-facing: Definition 7.46's matrix-weighted quadratic prox function centered at `x₀`;
- core/canonical: the seminorm-centered owner `Seminorm.quadraticDistanceTo`;
- bridge/view: the weighted seminorm `positiveDefMatrixNorm` and the notation `‖x - x₀‖[G]`.

Primitive data:
- a seminorm owner `p` and center `x₀` for the intrinsic quadratic prox construction;
- a positive-definite matrix owner `G` realizing the weighted geometry;
- the chosen center `x₀`.

Derived API:
- the intrinsic prox owner `p.quadraticDistanceTo x₀`;
- the matrix-weighted specialization used in Definition 7.46;
- its pointwise formula `x ↦ (1 / 2) * ‖x - x₀‖[G]^2`.

Source/core/bridge triage:
- source-facing: Definition 7.46's weighted prox term attached to the chosen matrix geometry;
- core/canonical: `Seminorm.quadraticDistanceTo`;
- bridge/view: the specialization from `positiveDefMatrixNorm` to the displayed `‖·‖[G]` formula.

The previous local declaration stayed at the matrix-wrapper surface. This refinement instead makes
the intrinsic seminorm-centered quadratic owner primary and presents Definition 7.46 as a direct
recall of its positive-definite-matrix specialization. -/

section

variable (G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef}) (x0 : Eₘ)

/- Definition 7.46 recalls the weighted quadratic prox owner
`(positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x₀`. -/
#check (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0

end

-- Proof sketch: expand the recalled owner; the displayed formula is exactly the defining
-- quadratic expression for the `positiveDefMatrixNorm` specialization.
/-- Evaluating the weighted quadratic prox owner from Definition 7.46 yields the formula
`(1 / 2) ‖x - x₀‖_G²`. -/
@[simp] theorem positiveDefMatrixNorm_quadraticDistanceTo_apply
    (G : {G : Matrix (Fin m) (Fin m) ℝ // G.PosDef}) (x0 x : Eₘ) :
    (positiveDefMatrixNorm G.1 G.2).quadraticDistanceTo x0 x =
      (1 / 2 : ℝ) * ‖x - x0‖[G] ^ (2 : ℕ) :=
  rfl

end

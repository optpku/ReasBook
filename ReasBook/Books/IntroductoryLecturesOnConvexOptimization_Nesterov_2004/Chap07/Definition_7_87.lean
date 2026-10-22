/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.87 lies in the positive-definite weighted-norm / quadratic-prox domain.

Mandatory domain-style sampling before refinement:
- `positiveDefMatrixNorm` and the notation `‖x‖[G]` in `Definition_7_23`, the chapter owner of
  the primal norm induced by a positive-definite matrix;
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Definition_7_23`, the canonical inverse-
  matrix formula for the dual norm of that owner;
- `Seminorm.quadraticDistanceTo` in `Chap06/Remark_6_1_1`, the project owner of centered
  quadratic prox terms attached to a seminorm;
- `positiveDefMatrixNorm_quadraticDistanceTo_apply` in `Definition_7_46`, the Chapter 7 weighted
  specialization of that prox owner.

Best owner abstraction:
- source-facing: Definition 7.87's initial matrix geometry and the resulting initial estimating
  function centered at `x₀`;
- core/canonical: `positiveDefMatrixNorm G₀.1 G₀.2`, its dual norm, and
  `(positiveDefMatrixNorm G₀.1 G₀.2).quadraticDistanceTo x₀`;
- bridge/view: the notation `‖x‖[G₀]`, `‖g‖[G₀,*]`, and the explicit displayed formulas recalled
  below.

Primitive data:
- a positive-definite matrix `G₀`;
- a center `x₀`.

Derived API:
- the primal norm `‖x‖[G₀]`;
- the dual norm `‖g‖[G₀,*]`;
- the initial estimating function `(positiveDefMatrixNorm G₀.1 G₀.2).quadraticDistanceTo x₀`.

Source/core/bridge triage:
- source-facing: Definition 7.87's initial estimating function in the `G₀`-metric;
- core/canonical: the weighted seminorm owner and its dual-norm / quadratic-distance companions;
- bridge/view: the formulas `√⟪G₀ x, x⟫`, `√⟪g, G₀⁻¹ g⟫`, and `(1 / 2) ‖x - x₀‖[G₀]^2`.

This item is recall-only after the earlier chapter refinements. Keeping separate public owners
`quasiNewtonMetricPrimalNorm`, `quasiNewtonMetricDualNorm`, and
`quasiNewtonInitialEstimatingFunction` would duplicate `positiveDefMatrixNorm`, its dual norm, and
`Seminorm.quadraticDistanceTo` without adding new mathematics. -/

section

variable (G0 : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x0 : E)

/- Definition 7.87 recalls the initial estimating function as the weighted quadratic prox owner
centered at `x₀`, with the associated `G₀`-primal and dual norms supplied by the canonical
weighted-norm API. -/
#check (positiveDefMatrixNorm G0.1 G0.2).quadraticDistanceTo x0

/- The `G₀`-primal norm is the canonical weighted norm owner attached to the positive-definite
matrix. -/
set_option linter.hashCommand false in
#check positiveDefMatrixNorm G0.1 G0.2

/- Its dual norm is the canonical owner applied to that weighted norm. -/
set_option linter.hashCommand false in
#check (positiveDefMatrixNorm G0.1 G0.2).dualNorm

end

/- The primal norm formula is recalled through the canonical companion theorem. -/
recall positiveDefMatrixNorm_def
    (G0 : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x : E) :
    ‖x‖[G0] = Real.sqrt (inner ℝ ((Matrix.toEuclideanLin G0.1) x) x)

/- The dual norm formula is recalled through the canonical inverse-matrix theorem. -/
recall positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv
    (G0 : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (g : E) :
    ‖g‖[G0,*] = Real.sqrt (inner ℝ g ((Matrix.toEuclideanLin G0.1⁻¹) g))

/- The initial estimating-function formula is recalled through the weighted prox specialization
from Definition 7.46. -/
recall positiveDefMatrixNorm_quadraticDistanceTo_apply
    (G0 : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x0 x : E) :
    (positiveDefMatrixNorm G0.1 G0.2).quadraticDistanceTo x0 x =
      (1 / 2 : ℝ) * ‖x - x0‖[G0] ^ (2 : ℕ)

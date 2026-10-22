/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_8_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonSystem (AdmissiblePoint)

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 1.8.2 lies in the domain of second-order Taylor models for Euclidean optimization.

Sampled owner-style declarations:
* `secondOrderTaylorModelAt` in `Definition_1_4_17`, the source-facing quadratic Taylor model;
* `hessianMatrix` in `Definition_1_4_16`, the Euclidean matrix view of the Hessian operator;
* `NewtonSystem.step` in `Algorithm_1_7_1`, the chapter owner of the full Newton update for
  the stationarity system `∇ f = 0`;
* `UnconstrainedQuadraticMinimizationProblem.isMinOn_translate` in `Lemma_1_8_8`, the translated
  quadratic minimization theorem used internally.

Owner abstractions:
* the source-facing quadratic model `secondOrderTaylorModelAt`;
* the Newton update owner `NewtonSystem.step (∇ f)`.

Primitive data:
* the objective `f`;
* the center `xBar`;
* the positive-definite Hessian matrix `∇² f xBar`.

Derived API:
* the coordinate realization
  `quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar)`;
* the canonical Newton step `NewtonSystem.step (∇ f)` at the admissible point given by Hessian
  nondegeneracy;
* the inverse-Hessian coordinate formula
  `xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar)` as a bridge view of that step;
* the internal translated quadratic problem used to prove global minimality.

Source/core/bridge triage:
* source-facing: the quadratic Taylor model `secondOrderTaylorModelAt f xBar` together with its
  minimizer statement;
* core/canonical: `secondOrderTaylorModelAt`, `NewtonSystem.step (∇ f)`, and the owner bridge
  `DampedNewton.step_eq_hessianMatrixFormula`;
* bridge/view: the matrix realization via `hessianMatrix` and `quadraticObjective`, plus the
  inverse-Hessian coordinate formula specialized from the damped-Newton owner at `h = 1`.
-/

/-- A positive-definite Hessian matrix gives the Jacobian nondegeneracy needed to view `xBar` as
an admissible Newton point for the stationarity system `∇ f = 0`. -/
theorem hessian_det_ne_zero_of_posDef (f : E → ℝ) (xBar : E) (hH : (∇² f xBar).PosDef) :
    (fderiv ℝ (∇ f) xBar).det ≠ 0 := by
  change LinearMap.det (fderiv ℝ (∇ f) xBar).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (fderiv ℝ (∇ f) xBar).toLinearMap]
  simpa [hessianMatrix] using hH.det_pos.ne'

/-- The canonical Newton step for the stationarity system `∇ f = 0` agrees with the textbook
inverse-Hessian formula when the Hessian at `xBar` is positive definite. -/
theorem newtonSystem_step_eq_matrixFormula (f : E → ℝ) (xBar : E)
    (hH : (∇² f xBar).PosDef) :
    NewtonSystem.step (∇ f) ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩ =
      xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
  let xN : AdmissiblePoint (∇ f) := ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩
  calc
    NewtonSystem.step (∇ f) xN = DampedNewton.step f xN 1 := by
      simp [DampedNewton.step]
    _ = xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
      simpa [xN] using DampedNewton.step_eq_hessianMatrixFormula f xN (1 : ℝ)

/-- Proposition 1.8.2: if the Hessian matrix `∇² f xBar` is positive definite, then the
quadratic Taylor model `φ₂ = secondOrderTaylorModelAt f xBar` is minimized at the canonical
Newton step for the stationarity equation `∇ f = 0`. The source-facing inverse-Hessian formula
for that step is recovered from `DampedNewton.step_eq_hessianMatrixFormula` at `h = 1`; the
matrix quadratic problem is used only as an internal bridge to Lemma 1.8.8. -/
-- Proof sketch: rewrite `secondOrderTaylorModelAt f xBar` as its canonical Euclidean matrix
-- realization and apply the translated quadratic minimization theorem from Lemma 1.8.8.
theorem newtonQuadraticModel_isMinOn (f : E → ℝ) (xBar : E)
    (hH : (∇² f xBar).PosDef) :
    IsMinOn
      (secondOrderTaylorModelAt f xBar)
      Set.univ
      (NewtonSystem.step (∇ f) ⟨xBar, hessian_det_ne_zero_of_posDef f xBar hH⟩) := by
  have hxN_det : (fderiv ℝ (∇ f) xBar).det ≠ 0 :=
    hessian_det_ne_zero_of_posDef f xBar hH
  let xN : AdmissiblePoint (∇ f) := ⟨xBar, hxN_det⟩
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := f xBar
      a := ∇ f xBar
      A := ∇² f xBar
      posDef := hH }
  have hmodel :
      secondOrderTaylorModelAt f xBar =
        fun x ↦ quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar) := by
    funext x
    rw [secondOrderTaylorModelAt_apply_hessianMatrix, quadraticObjective]
  have hstep :
      xBar + problem.minimizer = NewtonSystem.step (∇ f) xN := by
    calc
      xBar + problem.minimizer = xBar - ((∇² f xBar)⁻¹).toEuclideanLin (∇ f xBar) := by
        simp [problem, UnconstrainedQuadraticMinimizationProblem.minimizer, sub_eq_add_neg]
      _ = NewtonSystem.step (∇ f) xN := by
        simpa [xN] using (newtonSystem_step_eq_matrixFormula f xBar hH).symm
  have hbridge :
      IsMinOn
        (fun x ↦ quadraticObjective (f xBar) (∇ f xBar) (∇² f xBar) (x - xBar))
        Set.univ
        (NewtonSystem.step (∇ f) xN) := by
    simpa only [problem, UnconstrainedQuadraticMinimizationProblem.coe_apply, hstep] using
      problem.isMinOn_translate xBar
  simpa [xN, hmodel] using hbridge

end

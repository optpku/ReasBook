/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.BFGSMethod
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator
open scoped Topology

section Chapter05Theorem5416

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * `GeneralQuasiNewtonMethod` is the Chapter 5 owner for quasi-Newton trajectory data.
-- * `bfgsInverseUpdate` is the Chapter 5 owner for the inverse-BFGS matrix formula.
-- * `HasLocalLipschitzHessianMatrixAt` is the Chapter 3 owner for the local Hessian model.
-- * `HasQSuperlinearConvergenceTo` is the canonical Chapter 1 owner for the
--   `Q`-superlinear rate predicate.
--
/-- Chapter05 Theorem 5.4.16: if `f` is twice continuously differentiable, `G` is a local
Lipschitz Hessian matrix field at the local minimizer `xStar`, `A` is a BFGS sequence
converging to `xStar`, and `∑' k, ‖A k - xStar‖ < ∞`, then `A` converges to `xStar` at a
`Q`-superlinear rate. -/
theorem bfgs_hasQSuperlinearConvergenceTo_of_tendsto_minimizer_and_summable_dist
    (f : Point → ℝ) (G : Point → MatrixN) (xStar : Point)
    (A : GeneralQuasiNewtonMethod f)
    (hBFGS : IsBFGSMethod A)
    (hC2 : ContDiff ℝ 2 f)
    (h_hessian : HasLocalLipschitzHessianMatrixAt f G xStar)
    (h_min : IsLocalMin f xStar)
    (h_tendsto : Tendsto A atTop (nhds xStar))
    (h_summable : Summable (fun k ↦ ‖A k - xStar‖)) :
    HasQSuperlinearConvergenceTo A xStar := sorry

end Chapter05Theorem5416

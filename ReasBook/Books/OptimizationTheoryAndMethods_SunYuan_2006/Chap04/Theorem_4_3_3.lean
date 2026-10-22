/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_4

open Filter

noncomputable section

section

variable {n : ℕ}

local notation "Point" => ConjugateGradientPoint n

/-- Chapter04 Theorem 4.3.3: let `f : ℝ^n → ℝ` be twice continuously differentiable, let
`method` be a Polak-Ribiere-Polyak conjugate-gradient run with exact line search, and assume the
source stationary-step condition `x (k + 1) = x k` whenever `g k = 0`. Assume there is a
constant `m > 0` such that the Hessian quadratic form has the canonical lower-level-set bound
`HasLowerLevelHessianLowerBound Set.univ f method.x0 m` on
`lowerLevelSetOn Set.univ f method.x0 = {x | f x ≤ f method.x0}`. Then the generated sequence
converges to a global minimizer `xStar` of `f`, and every global minimizer of `f` coincides with
`xStar`. The boundedness clause in the source assumptions is redundant once this lower Hessian
bound is imposed on the canonical lower level set. -/
theorem polakRibierePolyakConjugateGradient_tendsto_uniqueGlobalMinimizer
    (f : Point → ℝ)
    (hC2 : ContDiff ℝ 2 f)
    (method : PolakRibierePolyakConjugateGradientMethod n f)
    (hStationaryUpdate : ∀ k : ℕ, method.g k = 0 → method.x (k + 1) = method.x k)
    (hLevelHessian : ∃ m > 0, HasLowerLevelHessianLowerBound Set.univ f method.x0 m) :
    ∃ xStar : Point,
      IsMinOn f Set.univ xStar ∧
        Tendsto method.x atTop (nhds xStar) ∧
        ∀ y : Point, IsMinOn f Set.univ y → y = xStar := sorry

end

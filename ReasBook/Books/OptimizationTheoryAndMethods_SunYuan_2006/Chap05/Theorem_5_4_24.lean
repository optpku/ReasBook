/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_23

noncomputable section

section Chapter05Theorem5424

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter05 Theorem 5.4.24: suppose the assumptions of Chapter05 Theorem 5.4.23 hold for the
restricted-Broyden run `A`; assume in addition that each step size `A.α k` is chosen by exact
line search on the ray `Set.Ici 0`, expressed by the canonical Chapter 5 exact-line-search owner
`A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay` on the inverse-form bridge from
`RestrictedBroydenRun`. Then the generated sequence converges to `h.xStar` `Q`-superlinearly,
expressed by the reusable convergence owner
`RestrictedBroydenRun.ConvergesQSuperlinearlyTo`. -/
theorem restrictedBroyden_tendsto_and_superlinear_of_uniformConvex_and_exactLineSearch
    (f : Point → ℝ) (D : Set Point)
    (h : HasRestrictedBroydenLocalSuperlinearAssumptions D f)
    (A : RestrictedBroydenRun D f)
    (hA0_local : A 0 ∈ Metric.ball h.xStar h.ε)
    (hB0_posDef : A.B0.PosDef)
    (hExactLineSearch : A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay) :
    RestrictedBroydenRun.ConvergesQSuperlinearlyTo h.xStar A := sorry

end Chapter05Theorem5424

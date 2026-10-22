/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_3_3

noncomputable section

open Filter Metric

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace SubgradientMethod

/-- The source stepsize conditions `(14.3.14)` and `(14.3.15)` for Algorithm 14.3.1:
the positive stepsizes recorded by `method.stepSize` tend to `0` and remain nonsummable.
The positivity itself is already part of the chapter owner `SubgradientMethod`. -/
def HasVanishingNonsummableStepSizes (method : SubgradientMethod E) : Prop :=
  Tendsto (fun k : ℕ ↦ method.stepSize (k + 1)) atTop (nhds 0) ∧
    ¬ Summable (fun k : ℕ ↦ method.stepSize (k + 1))

/-- Unfolding `method.HasVanishingNonsummableStepSizes` gives the vanishing and nonsummability
conditions on the shifted stepsize sequence from `(14.3.14)` and `(14.3.15)`. -/
theorem hasVanishingNonsummableStepSizes_iff
    (method : SubgradientMethod E) :
    method.HasVanishingNonsummableStepSizes ↔
      Tendsto (fun k : ℕ ↦ method.stepSize (k + 1)) atTop (nhds 0) ∧
        ¬ Summable (fun k : ℕ ↦ method.stepSize (k + 1)) :=
  Iff.rfl

end SubgradientMethod

/-- Chapter14 Theorem 14.3.4: let `f` be convex, let `sunYuanOptimalSolutionSet f` be nonempty and
bounded, and let `method` be an Algorithm 14.3.1 execution for `f`. If the stepsizes satisfy
`(14.3.14)` and `(14.3.15)`, encoded by
`method.HasVanishingNonsummableStepSizes`, then the distance from the iterates to the optimal
solution set tends to `0`. -/
theorem tendsto_infDist_sunYuanOptimalSolutionSet_zero_of_convexOn
    (method : SubgradientMethod E)
    (h_convex : ConvexOn ℝ Set.univ method.objective)
    (h_solution : Set.Nonempty S⋆[method.objective])
    (h_bounded : Bornology.IsBounded S⋆[method.objective])
    (h_steps : method.HasVanishingNonsummableStepSizes) :
    Tendsto
      (fun k : ℕ ↦ infDist (method.iterate (k + 1)) S⋆[method.objective])
      atTop
      (nhds 0) := sorry

#print axioms SubgradientMethod.HasVanishingNonsummableStepSizes
#print axioms tendsto_infDist_sunYuanOptimalSolutionSet_zero_of_convexOn

end

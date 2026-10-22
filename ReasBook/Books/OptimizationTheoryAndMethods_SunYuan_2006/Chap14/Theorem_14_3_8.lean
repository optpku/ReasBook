/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_7

noncomputable section

open Filter Metric

section

variable {n : ℕ}

-- Domain sampling for this item:
-- * source-facing layer: the Theorem 14.3.8 subsequence bound for Algorithm 14.3.7
-- * core/canonical owner: `SpaceDilationMethod n`
-- * upstream Chapter 14 optimality owners: `S⋆[f]`, `f⋆[f]`, `spaceDilationRateFactor`
-- * primitive data already live in `SpaceDilationMethod`; the scaled objective-gap expression and
--   its subsequence boundedness are theorem-level derived API on that owner.

namespace SpaceDilationMethod

variable (method : _root_.SpaceDilationMethod n)

/-- The geometrically scaled objective gap
`(f(x_k) - f⋆[method.objective]) / q^k`, where `q = spaceDilationRateFactor n`. -/
def scaledObjectiveGapAt (k : ℕ) : ℝ :=
  (method.objectiveValueAt k - f⋆[method.objective]) / spaceDilationRateFactor n ^ k

/-- Unfolding `method.scaledObjectiveGapAt k` gives the source scaled objective-gap expression. -/
@[simp] theorem scaledObjectiveGapAt_eq (k : ℕ) :
    method.scaledObjectiveGapAt k =
      (method.objectiveValueAt k - f⋆[method.objective]) / spaceDilationRateFactor n ^ k :=
  rfl

/-- `method.HasBoundedScaledObjectiveGapAlongSubsequence` means that some real constant `C`
dominates `method.scaledObjectiveGapAt (k + 1)` frequently along `atTop`, equivalently along an
unbounded subsequence. -/
def HasBoundedScaledObjectiveGapAlongSubsequence : Prop :=
  ∃ C : ℝ, ∃ᶠ k : ℕ in atTop, method.scaledObjectiveGapAt (k + 1) ≤ C

/-- Unfolding `method.HasBoundedScaledObjectiveGapAlongSubsequence` gives the source subsequence
boundedness statement for the geometrically scaled objective gap. -/
theorem hasBoundedScaledObjectiveGapAlongSubsequence_iff :
    method.HasBoundedScaledObjectiveGapAlongSubsequence ↔
      ∃ C : ℝ, ∀ N : ℕ, ∃ k ≥ N, method.scaledObjectiveGapAt (k + 1) ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    rw [Filter.frequently_atTop] at hC
    exact ⟨C, fun N ↦ by
      rcases hC N with ⟨k, hk, hkC⟩
      exact ⟨k, hk, hkC⟩⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rw [Filter.frequently_atTop]
    intro N
    rcases hC N with ⟨k, hk, hkC⟩
    exact ⟨k, hk, hkC⟩

end SpaceDilationMethod

/-- Chapter14 Theorem 14.3.8: let `method` be a run of Algorithm 14.3.7 for a convex objective on
`ℝⁿ`, and assume `S⋆[method.objective]` is nonempty. If
`infDist method.initialPoint S⋆[method.objective] ≤ method.initialScale`, then
its geometrically scaled objective error is bounded above along an unbounded subsequence, encoded
by the owner-level predicate `method.HasBoundedScaledObjectiveGapAlongSubsequence`. This
formalizes the source statement
`liminf_(k → ∞) ((f (x_k) - f*) / q^k) < +∞` by asserting the existence of `C` such that
arbitrarily late indices satisfy `method.scaledObjectiveGapAt (k + 1) ≤ C`,
where `q = spaceDilationRateFactor n`; the valid-dimension assumption `n ≥ 2` is carried by the
owner `SpaceDilationMethod n` itself. -/
theorem exists_geometric_ratio_bound_along_subsequence_of_convexOn_spaceDilationMethod
    (method : SpaceDilationMethod n)
    (h_convex : ConvexOn ℝ Set.univ method.objective)
    (h_solution : Set.Nonempty (S⋆[method.objective]))
    (h_initial_dist : infDist method.initialPoint (S⋆[method.objective]) ≤ method.initialScale) :
    method.HasBoundedScaledObjectiveGapAlongSubsequence := sorry

end

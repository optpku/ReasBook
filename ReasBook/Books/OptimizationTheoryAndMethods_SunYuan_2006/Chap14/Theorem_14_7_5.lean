/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Theorem_14_7_2

noncomputable section

open Filter
open scoped BigOperators Matrix.Norms.L2Operator

section

variable {n m : ℕ}
variable {ρ : (Fin n → ℝ) → ℝ} [IsVectorNorm ρ]

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "MonotoneMethod" => @_root_.CompositeNonsmoothTrustRegionMethod n m ρ _

-- Domain sampling:
-- * primary domain: accumulation-point existence for composite nonsmooth trust-region runs whose
--   Hessian approximation sequence `B_k` is primitive and only required to satisfy `(14.7.12)`;
-- * inspected owner declarations in the minimal semantic closure:
--   `CompositeNonsmoothTrustRegionMethod` and
--   `CompositeNonsmoothTrustRegionMethod.hessianApproximationAt` from `Algorithm_14_7_1`,
--   `HasSubsequenceTendstoTo` from `Chapter05.Definition_5_4_extra_1`,
--   `IsClarkeStationaryPoint` from `Definition_14_1_extra_4`,
--   and `compositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint` from
--   `Theorem_14_7_2`;
-- * best owner abstraction: the source-facing generalized method owner below, whose primitive
--   stage data includes the matrix sequence `B_k`;
-- * primitive data vs derived API:
--   primitive data are the composite problem, the `C²` regularity of the component functions,
--   the stage sequences `x_k`, `λ_k`, `d_k`, `Δ_k`, and the primitive Hessian approximation
--   sequence `B_k`;
--   derived API is the trust-region model, reduction ratio, accumulation-point packaging through
--   `HasSubsequenceTendstoTo`, and Clarke stationarity;
-- * layer triage:
--   - source-facing: `GeneralizedCompositeNonsmoothTrustRegionMethod`,
--     `SatisfiesHessianApproximationCondition14712`, and Theorem 14.7.5 below;
--   - core/canonical: `HasSubsequenceTendstoTo` and `IsClarkeStationaryPoint`;
--   - bridge/view:
--     `CompositeNonsmoothTrustRegionMethod.toGeneralizedCompositeNonsmoothTrustRegionMethod`,
--     which embeds the stricter `(14.7.7)` owner into this more general source-facing owner.

namespace GeneralizedCompositeNonsmoothTrustRegion

/-- The trust-region model `φ_k` attached to the stage data `(x_k, B_k)`. -/
def modelAt
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (hessianApproximation : ℕ → MatrixN) (k : ℕ) : Point → ℝ :=
  compositeNonsmoothTrustRegionModel problem (iterate k) (hessianApproximation k)

/-- The ratio `r_k` from `(14.7.8)` formed from the current iterate, direction, and primitive
matrix sequence `B_k`. -/
def reductionRatioAt
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (hessianApproximation : ℕ → MatrixN)
    (direction : ℕ → Point) (k : ℕ) : ℝ :=
  (problem (iterate k) - problem (CompositeNonsmoothTrustRegion.trialPoint iterate direction k)) /
    (modelAt problem iterate hessianApproximation k 0 -
      modelAt problem iterate hessianApproximation k (direction k))

end GeneralizedCompositeNonsmoothTrustRegion

/-- Chapter14 Theorem 14.7.5 works with the source-facing generalization of Algorithm 14.7.1 in
which the Hessian approximation sequence `B_k` is primitive data rather than the special choice
from `(14.7.7)`. The remaining trust-region subproblem, radius update, iterate update, and
accepted-step multiplier rules are unchanged, but they use the recorded `B_k` directly. The
specialized Chapter 14.7 owner is recovered by the bridge
`CompositeNonsmoothTrustRegionMethod.toGeneralizedCompositeNonsmoothTrustRegionMethod`. -/
structure GeneralizedCompositeNonsmoothTrustRegionMethod
    (n m : ℕ) (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] where
  problem : CompositeNonsmoothOptimizationProblem n m
  componentContDiff :
    ∀ i : Fin m, ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) ↦ problem.smoothMap y i)
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialMultiplier : EuclideanSpace ℝ (Fin m)
  initialRadius : ℝ
  epsilon : ℝ
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  multiplier : ℕ → EuclideanSpace ℝ (Fin m)
  hessianApproximation : ℕ → Matrix (Fin n) (Fin n) ℝ
  direction : ℕ → EuclideanSpace ℝ (Fin n)
  trustRegionRadius : ℕ → ℝ
  initialRadius_pos : 0 < initialRadius
  epsilon_nonneg : 0 ≤ epsilon
  iterate_one : iterate 1 = initialPoint
  multiplier_zero : multiplier 0 = initialMultiplier
  trustRegionRadius_one : trustRegionRadius 1 = initialRadius
  direction_subproblem_solution
      (k : ℕ) (_hk : 1 ≤ k) :
      IsCompositeNonsmoothTrustRegionSolution
        ρ
        problem
        (iterate k)
        (hessianApproximation k)
        (trustRegionRadius k)
        (direction k)
  predictedReduction_pos
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      0 <
        trustRegionPredictedReduction
          (GeneralizedCompositeNonsmoothTrustRegion.modelAt
            problem
            iterate
            hessianApproximation
            k)
          (direction k)
  trustRegionRadius_succ
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      trustRegionRadius (k + 1) =
        if GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
              problem
              iterate
              hessianApproximation
              direction
              k <
            (1 / 4 : ℝ) then
          ρ (direction k).ofLp / 4
        else if (3 / 4 : ℝ) <
              GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
                problem
                iterate
                hessianApproximation
                direction
                k ∧
              ρ (direction k).ofLp = trustRegionRadius k then
          2 * trustRegionRadius k
        else
          trustRegionRadius k
  iterate_succ_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            hessianApproximation
            direction
            k) :
      iterate (k + 1) = CompositeNonsmoothTrustRegion.trialPoint iterate direction k
  multiplier_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            hessianApproximation
            direction
            k) :
      IsCompositeNonsmoothAcceptedStepMultiplier
        problem
        (CompositeNonsmoothTrustRegion.trialPoint iterate direction k)
        (direction k)
        (multiplier k)
  iterate_succ_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            hessianApproximation
            direction
            k ≤
          0) :
      iterate (k + 1) = iterate k
  multiplier_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt
            problem
            iterate
            hessianApproximation
            direction
            k ≤
          0) :
      multiplier k = multiplier (k - 1)

local notation "Method" => @_root_.GeneralizedCompositeNonsmoothTrustRegionMethod n m ρ _

/-- `SatisfiesHessianApproximationCondition14712 method` is the source growth condition
`(14.7.12)` on the primitive matrix sequence `B_k`: there are nonnegative constants `c₅` and
`c₆` such that `‖B_k‖ ≤ c₅ + c₆ * ∑ i in Finset.Icc 1 k, Δ_i` for every stage `k`. -/
def SatisfiesHessianApproximationCondition14712
    (method : Method) : Prop :=
  ∃ c₅ c₆ : ℝ,
    0 ≤ c₅ ∧
      0 ≤ c₆ ∧
        ∀ k : ℕ,
          ‖method.hessianApproximation k‖ ≤
            c₅ + c₆ * Finset.sum (Finset.Icc 1 k) method.trustRegionRadius

/-- Unfolding `SatisfiesHessianApproximationCondition14712 method` gives the source condition
`(14.7.12)` on the primitive sequence `B_k`. -/
theorem satisfiesHessianApproximationCondition14712_iff
    (method : Method) :
    SatisfiesHessianApproximationCondition14712 method ↔
      ∃ c₅ c₆ : ℝ,
        0 ≤ c₅ ∧
          0 ≤ c₆ ∧
            ∀ k : ℕ,
              ‖method.hessianApproximation k‖ ≤
                c₅ + c₆ * Finset.sum (Finset.Icc 1 k) method.trustRegionRadius :=
  Iff.rfl

namespace CompositeNonsmoothTrustRegionMethod

/-- The stricter Chapter 14.7 owner with `B_k` fixed by `(14.7.7)` canonically induces the
more general Theorem 14.7.5 owner with primitive `B_k`. -/
def toGeneralizedCompositeNonsmoothTrustRegionMethod
    (method : MonotoneMethod) : Method :=
  { problem := method.problem
    componentContDiff := method.componentContDiff
    initialPoint := method.initialPoint
    initialMultiplier := method.initialMultiplier
    initialRadius := method.initialRadius
    epsilon := method.epsilon
    iterate := method.iterate
    multiplier := method.multiplier
    hessianApproximation := method.hessianApproximationAt
    direction := method.direction
    trustRegionRadius := method.trustRegionRadius
    initialRadius_pos := method.initialRadius_pos
    epsilon_nonneg := method.epsilon_nonneg
    iterate_one := method.iterate_one
    multiplier_zero := method.multiplier_zero
    trustRegionRadius_one := method.trustRegionRadius_one
    direction_subproblem_solution := fun k hk ↦ by
      simpa using method.direction_subproblem_solution_at hk
    predictedReduction_pos := by
      intro k hk hContinue
      simpa [GeneralizedCompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegionMethod.hessianApproximationAt,
        CompositeNonsmoothTrustRegion.modelAt, CompositeNonsmoothTrustRegion.hessianApproximationAt]
        using method.predictedReduction_pos k hk hContinue
    trustRegionRadius_succ := by
      intro k hk hContinue
      change method.trustRegionRadius (k + 1) =
        if CompositeNonsmoothTrustRegion.reductionRatioAt
              method.problem
              method.iterate
              method.multiplier
              method.direction
              k <
            (1 / 4 : ℝ) then
          ρ (method.direction k).ofLp / 4
        else if (3 / 4 : ℝ) <
              CompositeNonsmoothTrustRegion.reductionRatioAt
                method.problem
                method.iterate
                method.multiplier
                method.direction
                k ∧
              ρ (method.direction k).ofLp = method.trustRegionRadius k then
          2 * method.trustRegionRadius k
        else
          method.trustRegionRadius k
      exact method.trustRegionRadius_succ k hk hContinue
    iterate_succ_of_positive_ratio := by
      intro k hk hContinue hrk
      simpa [GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt,
        GeneralizedCompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegionMethod.hessianApproximationAt,
        CompositeNonsmoothTrustRegion.reductionRatioAt,
        CompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegion.hessianApproximationAt,
        CompositeNonsmoothTrustRegionMethod.trialPointAt]
        using method.iterate_succ_of_positive_ratio k hk hContinue hrk
    multiplier_of_positive_ratio := by
      intro k hk hContinue hrk
      simpa [GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt,
        GeneralizedCompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegionMethod.hessianApproximationAt,
        CompositeNonsmoothTrustRegion.reductionRatioAt,
        CompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegion.hessianApproximationAt,
        CompositeNonsmoothTrustRegionMethod.trialPointAt]
        using method.multiplier_of_positive_ratio k hk hContinue hrk
    iterate_succ_of_nonpositive_ratio := by
      intro k hk hContinue hrk
      simpa [GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt,
        GeneralizedCompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegionMethod.hessianApproximationAt,
        CompositeNonsmoothTrustRegion.reductionRatioAt, CompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegion.hessianApproximationAt] using
        method.iterate_succ_of_nonpositive_ratio k hk hContinue hrk
    multiplier_of_nonpositive_ratio := by
      intro k hk hContinue hrk
      simpa [GeneralizedCompositeNonsmoothTrustRegion.reductionRatioAt,
        GeneralizedCompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegionMethod.hessianApproximationAt,
        CompositeNonsmoothTrustRegion.reductionRatioAt, CompositeNonsmoothTrustRegion.modelAt,
        CompositeNonsmoothTrustRegion.hessianApproximationAt] using
        method.multiplier_of_nonpositive_ratio k hk hContinue hrk }

/-- Under the specialization bridge, the primitive sequence `B_k` is exactly the canonical
matrix sequence from `(14.7.7)`. -/
theorem toGeneralizedCompositeNonsmoothTrustRegionMethod_hessianApproximation
    (method : MonotoneMethod) (k : ℕ) :
    (toGeneralizedCompositeNonsmoothTrustRegionMethod method).hessianApproximation k =
      method.hessianApproximationAt k :=
  rfl

end CompositeNonsmoothTrustRegionMethod

/-- Chapter14 Theorem 14.7.5: for the source-facing generalization of Algorithm 14.7.1 with a
primitive Hessian approximation sequence `B_k` satisfying `(14.7.12)`, every bounded iterate
sequence has an accumulation point that is Clarke stationary for the underlying composite
nonsmooth optimization problem. -/
theorem generalizedCompositeNonsmoothTrustRegion_exists_stationaryAccumulationPoint
    (method : Method)
    (h_growth : SatisfiesHessianApproximationCondition14712 method)
    (h_bounded : Bornology.IsBounded (Set.range method.iterate)) :
    ∃ xStar : Point, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        Tendsto (method.iterate ∘ φ) atTop (nhds xStar) ∧
        IsClarkeStationaryPoint method.problem xStar := by
  sorry

/-- Theorem 14.7.5 rewritten through the Chapter 5 accumulation-point owner
`HasSubsequenceTendstoTo`. -/
theorem generalizedCompositeNonsmoothTrustRegion_exists_clarkeStationaryAccumulationPoint
    (method : Method)
    (h_growth : SatisfiesHessianApproximationCondition14712 method)
    (h_bounded : Bornology.IsBounded (Set.range method.iterate)) :
    ∃ xStar : Point,
      HasSubsequenceTendstoTo method.iterate xStar ∧
        IsClarkeStationaryPoint method.problem xStar := by
  rcases
      generalizedCompositeNonsmoothTrustRegion_exists_stationaryAccumulationPoint
        method
        h_growth
        h_bounded with
    ⟨xStar, φ, hφmono, hφtendsto, hstationary⟩
  exact
    ⟨xStar, (hasSubsequenceTendstoTo_iff method.iterate xStar).2 ⟨φ, hφmono, hφtendsto⟩,
      hstationary⟩

end

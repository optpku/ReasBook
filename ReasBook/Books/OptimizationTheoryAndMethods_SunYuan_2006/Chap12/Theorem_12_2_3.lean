/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Algorithm_12_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_1_3
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

noncomputable section

section Chapter12Theorem1223

variable {n m : ℕ}

local notation "Point" => WilsonHanPowellPoint n
local notation "Multiplier" => WilsonHanPowellMultiplier m

-- Domain sampling:
-- * primary domain: Wilson-Han-Powell SQP accumulation-point theory and KKT multipliers for a
--   fixed equality-constrained problem
-- * inspected owner abstractions:
--   `EqualityConstrainedProblem`, `EqualityConstrainedProblem.IsKKTPoint`,
--   `EqualityConstrainedProblem.toStandardPenaltyProblem`,
--   `LagrangeNewtonMethod.IsFor` in `Theorem_12_1_2`,
--   `SmoothExactPenaltyMethodFor` in `Theorem_12_7_3`, and
--   `WilsonHanPowellMethod`, `WilsonHanPowellMethod.toStandardPenaltyProblem`,
--   `WilsonHanPowellMethod.approximatePenaltyStepAt`, and
--   `WilsonHanPowellMethod.subproblemAt` in `Algorithm_12_2_2`,
--   together with `StandardPenaltyProblem.IsLagrangeMultiplier` in `Theorem_10_6_1`
-- * source/core/bridge triage:
--   - source-facing layer here: a Wilson-Han-Powell run specialized to a fixed
--     equality-constrained problem;
--   - core/canonical owner for the problem data: `EqualityConstrainedProblem`;
--   - bridge/view layer here: the theorem-local compatibility predicate
--     `method.IsFor problem`, together with the equality-only Chapter 10 bridge
--     `problem.toStandardPenaltyProblem` used only for the Lagrange-multiplier conclusion
-- * primitive data vs. derived API:
--   - primitive owner data are the fixed `EqualityConstrainedProblem` and the underlying
--     `WilsonHanPowellMethod`;
--   - the specialization equalities `objectiveFunction = problem.objective` and
--     `constraintFunction = problem.constraintVector` are theorem-local bridge data relating
--     the canonical method owner to the fixed problem owner;
--   - the mixed-constraint `StandardPenaltyProblem` surface is derived only as the equality-only
--     bridge used by the conclusion

namespace WilsonHanPowellMethod

/-- A Wilson-Han-Powell run has uniform positive lower and upper quadratic Hessian bounds when
there are constants `mLower, MUpper > 0` with
`mLower * ‖d‖^2 ≤ dᵀ B_k d ≤ MUpper * ‖d‖^2` for every active stage `k ≥ 1` and direction `d`. -/
def HasUniformHessianBounds (method : WilsonHanPowellMethod n m) : Prop :=
  ∃ mLower MUpper : ℝ,
    0 < mLower ∧
      0 < MUpper ∧
        (∀ k : ℕ, 1 ≤ k → ∀ d : Point,
          mLower * ‖d‖ ^ (2 : ℕ) ≤
            dotProduct d (WithLp.toLp 2 ((method.hessianApproximation k).mulVec d.ofLp))) ∧
        ∀ k : ℕ, 1 ≤ k → ∀ d : Point,
          dotProduct d (WithLp.toLp 2 ((method.hessianApproximation k).mulVec d.ofLp)) ≤
            MUpper * ‖d‖ ^ (2 : ℕ)

/-- Unfolding `method.HasUniformHessianBounds` gives the source existential quadratic-form bounds
for the Hessian approximations `B_k` along the active stages `k ≥ 1`. -/
theorem hasUniformHessianBounds_iff
    (method : WilsonHanPowellMethod n m) :
    method.HasUniformHessianBounds ↔
      ∃ mLower MUpper : ℝ,
        0 < mLower ∧
          0 < MUpper ∧
            (∀ k : ℕ, 1 ≤ k → ∀ d : Point,
              mLower * ‖d‖ ^ (2 : ℕ) ≤
                dotProduct d (WithLp.toLp 2 ((method.hessianApproximation k).mulVec d.ofLp))) ∧
            ∀ k : ℕ, 1 ≤ k → ∀ d : Point,
              dotProduct d (WithLp.toLp 2 ((method.hessianApproximation k).mulVec d.ofLp)) ≤
                MUpper * ‖d‖ ^ (2 : ℕ) :=
  Iff.rfl

/-- `method.IsFor problem` is the theorem-local bridge saying that the canonical
Algorithm 12.2.2 owner `method` is being run for the fixed equality-constrained problem
`problem`: its recorded objective and constraint maps are exactly the canonical Chapter 12
owners `problem.objective` and `problem.constraintVector`. -/
def IsFor
    (method : WilsonHanPowellMethod n m)
    (problem : EqualityConstrainedProblem n m) : Prop :=
  method.objectiveFunction = problem.objective ∧
    method.constraintFunction = problem.constraintVector

/-- Under `method.IsFor problem`, the recorded Wilson-Han-Powell objective is the fixed
objective `problem.objective`. -/
theorem IsFor.objectiveFunction_eq
    {method : WilsonHanPowellMethod n m} {problem : EqualityConstrainedProblem n m}
    (h : method.IsFor problem) :
    method.objectiveFunction = problem.objective :=
  h.1

/-- Under `method.IsFor problem`, the recorded Wilson-Han-Powell constraint map is the fixed
constraint vector `problem.constraintVector`. -/
theorem IsFor.constraintFunction_eq
    {method : WilsonHanPowellMethod n m} {problem : EqualityConstrainedProblem n m}
    (h : method.IsFor problem) :
    method.constraintFunction = problem.constraintVector :=
  h.2

/-- Under `method.IsFor problem`, the equality-only Chapter 10 owner recorded by `method`
agrees with the canonical equality-only bridge of `problem`. -/
theorem IsFor.toStandardPenaltyProblem_eq
    {method : WilsonHanPowellMethod n m} {problem : EqualityConstrainedProblem n m}
    (h : method.IsFor problem) :
    method.toStandardPenaltyProblem = problem.toStandardPenaltyProblem := by
  rcases h with ⟨hObjective, hConstraint⟩
  have hConstraint' :
      (fun i x ↦ method.constraintFunction x i) = problem.constraint := by
    funext i x
    simpa [EqualityConstrainedProblem.constraintVector] using
      congrArg (fun v : Multiplier ↦ v i) (congrFun hConstraint x)
  have hPenaltyProblem :
      wilsonHanPowellPenaltyProblem method.objectiveFunction method.constraintFunction =
        problem.toStandardPenaltyProblem := by
    change
      StandardPenaltyProblem.mk
          m
          le_rfl
          method.objectiveFunction
          (fun i x ↦ method.constraintFunction x i) =
        StandardPenaltyProblem.mk
          m
          le_rfl
          problem.objective
          problem.constraint
    congr
  simpa [WilsonHanPowellMethod.toStandardPenaltyProblem] using hPenaltyProblem

/-- The theorem-local bridge `method.IsFor problem` is equivalent to saying that the
equality-only Chapter 10 owner recorded by `method` matches the canonical bridge of `problem`. -/
theorem isFor_iff_toStandardPenaltyProblem_eq
    (method : WilsonHanPowellMethod n m)
    (problem : EqualityConstrainedProblem n m) :
    method.IsFor problem ↔
      method.toStandardPenaltyProblem = problem.toStandardPenaltyProblem := by
  constructor
  · exact fun h ↦ h.toStandardPenaltyProblem_eq
  · intro h
    refine ⟨?_, ?_⟩
    · simpa
        [ WilsonHanPowellMethod.toStandardPenaltyProblem
        , EqualityConstrainedProblem.toStandardPenaltyProblem
        , wilsonHanPowellPenaltyProblem
        ]
      using congrArg StandardPenaltyProblem.objective h
    · funext x
      ext i
      simpa
        [ WilsonHanPowellMethod.toStandardPenaltyProblem
        , EqualityConstrainedProblem.toStandardPenaltyProblem
        , EqualityConstrainedProblem.constraintVector
        , wilsonHanPowellPenaltyProblem
        ]
      using congrFun (congrFun (congrArg StandardPenaltyProblem.constraint h) i) x

end WilsonHanPowellMethod

/-- Chapter12 Theorem 12.2.3 in source-facing KKT form: let `method` be a Wilson-Han-Powell
sequence generated by Algorithm 12.2.2 for the fixed equality-constrained problem `problem`,
with theorem-local compatibility hypothesis `hMethod : method.IsFor problem`, so the recorded
objective and constraint surfaces agree with the canonical ones coming from `problem`. Assume
`problem.objective` and every component of `problem.constraint` are continuously
differentiable, the Hessian approximations of `method` satisfy uniform positive quadratic lower
and upper bounds along the active stages `k ≥ 1`, and `‖λ_k‖∞ ≤ σ` for every active-stage
multiplier. Then every accumulation point of the primal iterate sequence `{x_k}` is a KKT
point of `problem`. -/
theorem wilsonHanPowell_accumulationPoint_isKKTPoint
    (problem : EqualityConstrainedProblem n m)
    (method : WilsonHanPowellMethod n m)
    (hMethod : method.IsFor problem)
    (hObjectiveC1 : ContDiff ℝ 1 problem.objective)
    (hConstraintC1 : ∀ i : Fin m, ContDiff ℝ 1 (problem.constraint i))
    (hHessianBounds : method.HasUniformHessianBounds)
    (hMultiplierBound : ∀ k : ℕ, 1 ≤ k → ‖method.multiplier k‖∞ ≤ method.sigma)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    ∃ lamStar : Multiplier, problem.IsKKTPoint xStar lamStar := by
  sorry

/-- Chapter12 Theorem 12.2.3: the source-facing KKT conclusion above yields the Chapter 10
Lagrange-multiplier owner for the equality-only mixed-constraint bridge
`problem.toStandardPenaltyProblem`. -/
theorem wilsonHanPowell_accumulationPoint_hasLagrangeMultiplier
    (problem : EqualityConstrainedProblem n m)
    (method : WilsonHanPowellMethod n m)
    (hMethod : method.IsFor problem)
    (hObjectiveC1 : ContDiff ℝ 1 problem.objective)
    (hConstraintC1 : ∀ i : Fin m, ContDiff ℝ 1 (problem.constraint i))
    (hHessianBounds : method.HasUniformHessianBounds)
    (hMultiplierBound : ∀ k : ℕ, 1 ≤ k → ‖method.multiplier k‖∞ ≤ method.sigma)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    ∃ lamStar : Multiplier,
      problem.toStandardPenaltyProblem.IsLagrangeMultiplier xStar lamStar := by
  rcases
      wilsonHanPowell_accumulationPoint_isKKTPoint
        problem method hMethod hObjectiveC1 hConstraintC1 hHessianBounds hMultiplierBound
        hφ hxStar
    with
    ⟨lamStar, hKKT⟩
  exact ⟨lamStar, hKKT.toIsLagrangeMultiplier_of_contDiff hObjectiveC1 hConstraintC1⟩

end Chapter12Theorem1223

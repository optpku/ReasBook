/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_4_1

noncomputable section

section

variable {ambientDim eqConstraintDim ineqConstraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "EqConstraintPoint" => EuclideanSpace ℝ (Fin eqConstraintDim)
local notation "IneqConstraintPoint" => EuclideanSpace ℝ (Fin ineqConstraintDim)
local notation "TangentPoint" => EuclideanSpace ℝ (Fin tangentDim)
local notation "EqJacobian" => Matrix (Fin ambientDim) (Fin eqConstraintDim) ℝ
local notation "IneqJacobian" => Matrix (Fin ambientDim) (Fin ineqConstraintDim) ℝ

-- Domain sampling for this exercise:
-- * core/canonical owner: `NullSpaceTrustRegionMethod` from `Algorithm_13_4_1`
-- * inspected companion API there: `nullSpaceReducedGradient`,
--   `NullSpaceTrustRegionMethod.terminatedAt`, and
--   `NullSpaceTrustRegionMethod.nextRadiusConditionAt`
-- * checked nearby Chapter 13 feasible-set owners such as `cauchyScaleSet` in
--   `Definition_13_3_extra_2`
-- The equality-constrained null-space method already has its owner upstream, so this file keeps
-- only the inequality-specific working-set layer.

/-- The linearized equality-constraint residual `c_eq + A_eqᵀ d`. -/
def nullSpaceEqLinearizedResidual
    (cEq : EqConstraintPoint) (AEq : EqJacobian) (d : Point) : EqConstraintPoint :=
  cEq + Matrix.toEuclideanLin AEq.transpose d

/-- Unfolding `nullSpaceEqLinearizedResidual cEq AEq d` gives the source affine equality
linearization `c_eq + A_eqᵀ d`. -/
theorem nullSpaceEqLinearizedResidual_eq
    (cEq : EqConstraintPoint) (AEq : EqJacobian) (d : Point) :
    nullSpaceEqLinearizedResidual cEq AEq d = cEq + Matrix.toEuclideanLin AEq.transpose d := rfl

/-- The linearized inequality-constraint residual `c_ineq + A_ineqᵀ d`. -/
def nullSpaceIneqLinearizedResidual
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian) (d : Point) : IneqConstraintPoint :=
  cIneq + Matrix.toEuclideanLin AIneq.transpose d

/-- Unfolding `nullSpaceIneqLinearizedResidual cIneq AIneq d` gives the source affine
inequality linearization `c_ineq + A_ineqᵀ d`. -/
theorem nullSpaceIneqLinearizedResidual_eq
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian) (d : Point) :
    nullSpaceIneqLinearizedResidual cIneq AIneq d =
      cIneq + Matrix.toEuclideanLin AIneq.transpose d := rfl

/-- The homogeneous working linearized constraint system uses the equality Jacobian together
with the rows of the inequality Jacobian indexed by the current working set. -/
def inWorkingLinearizedNullSpace
    (AEq : EqJacobian) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) (d : Point) : Prop :=
  Matrix.toEuclideanLin AEq.transpose d = 0 ∧
    ∀ i : Fin ineqConstraintDim,
      i ∈ workingSet → Matrix.toEuclideanLin AIneq.transpose d i = 0

/-- Unfolding `inWorkingLinearizedNullSpace AEq AIneq workingSet d` gives the homogeneous
equality conditions defining the working linearized null space. -/
theorem inWorkingLinearizedNullSpace_iff
    (AEq : EqJacobian) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) (d : Point) :
    inWorkingLinearizedNullSpace AEq AIneq workingSet d ↔
      Matrix.toEuclideanLin AEq.transpose d = 0 ∧
        ∀ i : Fin ineqConstraintDim,
          i ∈ workingSet → Matrix.toEuclideanLin AIneq.transpose d i = 0 :=
  Iff.rfl

/-- The linearized inequality constraints are imposed as equalities on the working set and
weak inequalities off the working set. -/
def satisfiesWorkingSetLinearizedInequalities
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) (d : Point) : Prop :=
  (∀ i : Fin ineqConstraintDim,
      i ∈ workingSet → nullSpaceIneqLinearizedResidual cIneq AIneq d i = 0) ∧
    ∀ i : Fin ineqConstraintDim,
      i ∉ workingSet → 0 ≤ nullSpaceIneqLinearizedResidual cIneq AIneq d i

/-- Unfolding `satisfiesWorkingSetLinearizedInequalities cIneq AIneq workingSet d` gives the
active-set equality conditions and inactive-set inequality conditions. -/
theorem satisfiesWorkingSetLinearizedInequalities_iff
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) (d : Point) :
    satisfiesWorkingSetLinearizedInequalities cIneq AIneq workingSet d ↔
      (∀ i : Fin ineqConstraintDim,
          i ∈ workingSet → nullSpaceIneqLinearizedResidual cIneq AIneq d i = 0) ∧
        ∀ i : Fin ineqConstraintDim,
          i ∉ workingSet → 0 ≤ nullSpaceIneqLinearizedResidual cIneq AIneq d i :=
  Iff.rfl

/-- The mixed equality/inequality trust-region feasible set used by the inequality-constrained
null-space step: the step stays in the trust region, satisfies the linearized equalities exactly,
and satisfies the working-set interpretation of the linearized inequalities. -/
def mixedNullSpaceTrustRegionFeasibleSet
    (Δ : ℝ) (cEq : EqConstraintPoint) (AEq : EqJacobian)
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) : Set Point :=
  {d |
    ‖d‖ ≤ Δ ∧
      nullSpaceEqLinearizedResidual cEq AEq d = 0 ∧
      satisfiesWorkingSetLinearizedInequalities cIneq AIneq workingSet d}

/-- Membership in `mixedNullSpaceTrustRegionFeasibleSet Δ cEq AEq cIneq AIneq workingSet` is
exactly the trust-region bound together with the mixed linearized equality/inequality
constraints. -/
theorem mem_mixedNullSpaceTrustRegionFeasibleSet_iff
    (Δ : ℝ) (cEq : EqConstraintPoint) (AEq : EqJacobian)
    (cIneq : IneqConstraintPoint) (AIneq : IneqJacobian)
    (workingSet : Set (Fin ineqConstraintDim)) (d : Point) :
    d ∈ mixedNullSpaceTrustRegionFeasibleSet Δ cEq AEq cIneq AIneq workingSet ↔
      ‖d‖ ≤ Δ ∧
        nullSpaceEqLinearizedResidual cEq AEq d = 0 ∧
        satisfiesWorkingSetLinearizedInequalities cIneq AIneq workingSet d :=
  Iff.rfl

/-- Chapter13 Exercise 13.2: an inequality-constrained null-space trust-region method extends the
equality-constrained `NullSpaceTrustRegionMethod` of Algorithm 13.4.1 by adding a fixed
inequality residual map and inequality Jacobian map for the constrained problem, the stagewise
evaluations of those maps along the iterate sequence, feasible inequality residuals at the
iterates, and working sets whose recorded indices are active inequalities. It requires
`nullSpaceBasis k` to parametrize the null space of the combined equality and active-inequality
linearization while `trialStep k` stays in the mixed trust-region feasible set. -/
structure InequalityConstrainedNullSpaceTrustRegionMethod
    (ambientDim eqConstraintDim ineqConstraintDim tangentDim : ℕ)
    extends NullSpaceTrustRegionMethod ambientDim eqConstraintDim tangentDim where
  inequalityResidualAt :
    EuclideanSpace ℝ (Fin ambientDim) → EuclideanSpace ℝ (Fin ineqConstraintDim)
  inequalityJacobianAt :
    EuclideanSpace ℝ (Fin ambientDim) →
      Matrix (Fin ambientDim) (Fin ineqConstraintDim) ℝ
  inequalityResidual : ℕ → EuclideanSpace ℝ (Fin ineqConstraintDim)
  inequalityJacobian : ℕ → Matrix (Fin ambientDim) (Fin ineqConstraintDim) ℝ
  workingSet : ℕ → Set (Fin ineqConstraintDim)
  inequalityResidual_spec :
    ∀ k : ℕ, 1 ≤ k →
      inequalityResidual k = inequalityResidualAt (iterate k)
  inequalityJacobian_spec :
    ∀ k : ℕ, 1 ≤ k →
      inequalityJacobian k = inequalityJacobianAt (iterate k)
  iterate_inequality_feasible :
    ∀ k : ℕ, 1 ≤ k →
      ∀ i : Fin ineqConstraintDim, 0 ≤ inequalityResidual k i
  workingSet_subset_activeSet :
    ∀ k : ℕ, 1 ≤ k →
      ∀ i : Fin ineqConstraintDim,
        i ∈ workingSet k → inequalityResidual k i = 0
  nullSpaceBasis_parametrizes_workingLinearizedNullSpace :
    ∀ k : ℕ, 1 ≤ k →
      ∀ d : EuclideanSpace ℝ (Fin ambientDim),
        inWorkingLinearizedNullSpace
            (constraintJacobian k)
            (inequalityJacobian k)
            (workingSet k)
            d ↔
          ∃ p : EuclideanSpace ℝ (Fin tangentDim),
            d = Matrix.toEuclideanLin (nullSpaceBasis k) p
  trialStep_feasible :
    ∀ k : ℕ, 1 ≤ k →
      trialStep k ∈
        mixedNullSpaceTrustRegionFeasibleSet
          (radius k)
          (constraintResidual k)
          (constraintJacobian k)
          (inequalityResidual k)
          (inequalityJacobian k)
          (workingSet k)

namespace InequalityConstrainedNullSpaceTrustRegionMethod

instance instCoeNullSpaceTrustRegionMethod :
    CoeTC
      (InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
      (NullSpaceTrustRegionMethod ambientDim eqConstraintDim tangentDim) where
  coe method := method.toNullSpaceTrustRegionMethod

/-- An `InequalityConstrainedNullSpaceTrustRegionMethod` can be evaluated as its iterate
sequence `k ↦ x_k`. -/
instance instCoeFun :
    CoeFun
      (InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
      (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating an inequality-constrained null-space trust-region method as a function returns
its iterate sequence. -/
theorem coe_apply
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ) :
    method k = method.iterate k := rfl

/-- At stage `k ≥ 1`, the stored inequality residual is the fixed inequality residual map
evaluated at the iterate `x_k`. -/
theorem inequalityResidual_eq_inequalityResidualAt_iterate
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k) :
    method.inequalityResidual k = method.inequalityResidualAt (method.iterate k) :=
  method.inequalityResidual_spec k hk

/-- At stage `k ≥ 1`, the stored inequality Jacobian is the fixed inequality Jacobian map
evaluated at the iterate `x_k`. -/
theorem inequalityJacobian_eq_inequalityJacobianAt_iterate
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k) :
    method.inequalityJacobian k = method.inequalityJacobianAt (method.iterate k) :=
  method.inequalityJacobian_spec k hk

/-- At stage `k ≥ 1`, every stored inequality residual component is feasible. -/
theorem inequalityResidual_nonneg
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k)
    (i : Fin ineqConstraintDim) :
    0 ≤ method.inequalityResidual k i :=
  method.iterate_inequality_feasible k hk i

/-- At stage `k ≥ 1`, each index in the recorded working set is active for the stored
inequality residual. -/
theorem workingSet_mem_inequalityResidual_eq_zero
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k)
    (i : Fin ineqConstraintDim)
    (hi : i ∈ method.workingSet k) :
    method.inequalityResidual k i = 0 :=
  method.workingSet_subset_activeSet k hk i hi

/-- The recorded mixed linearized trust-region feasible set at stage `k`. -/
def feasibleSetAt
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ) : Set Point :=
  mixedNullSpaceTrustRegionFeasibleSet
    (method.radius k)
    (method.constraintResidual k)
    (method.constraintJacobian k)
    (method.inequalityResidual k)
    (method.inequalityJacobian k)
    (method.workingSet k)

/-- The homogeneous equality-plus-working-set linearized system at stage `k`. -/
def workingLinearizedNullSpaceAt
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ) : Set Point :=
  {d |
    inWorkingLinearizedNullSpace
      (method.constraintJacobian k)
      (method.inequalityJacobian k)
      (method.workingSet k)
      d}

/-- Membership in `method.workingLinearizedNullSpaceAt k` is exactly the homogeneous working
linearized null-space condition recorded at stage `k`. -/
theorem mem_workingLinearizedNullSpaceAt_iff
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (d : Point) :
    d ∈ method.workingLinearizedNullSpaceAt k ↔
      inWorkingLinearizedNullSpace
        (method.constraintJacobian k)
        (method.inequalityJacobian k)
        (method.workingSet k)
        d :=
  Iff.rfl

/-- At stage `k ≥ 1`, the stored basis `method.nullSpaceBasis k` parametrizes the null space of
the combined equality and active-inequality linearization. -/
theorem mem_workingLinearizedNullSpaceAt_iff_exists
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k)
    (d : Point) :
    d ∈ method.workingLinearizedNullSpaceAt k ↔
      ∃ p : TangentPoint,
        d = Matrix.toEuclideanLin (method.nullSpaceBasis k) p := by
  simpa [workingLinearizedNullSpaceAt] using
    method.nullSpaceBasis_parametrizes_workingLinearizedNullSpace k hk d

/-- Unfolding `method.feasibleSetAt k` gives the mixed linearized trust-region feasible set
stored at stage `k`. -/
theorem feasibleSetAt_eq
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ) :
    method.feasibleSetAt k =
      mixedNullSpaceTrustRegionFeasibleSet
        (method.radius k)
        (method.constraintResidual k)
        (method.constraintJacobian k)
        (method.inequalityResidual k)
        (method.inequalityJacobian k)
        (method.workingSet k) := rfl

/-- The stored trial step at stage `k` lies in the recorded mixed feasible set. -/
theorem trialStep_mem_feasibleSetAt
    (method :
      InequalityConstrainedNullSpaceTrustRegionMethod
        ambientDim eqConstraintDim ineqConstraintDim tangentDim)
    (k : ℕ)
    (hk : 1 ≤ k) :
    method.trialStep k ∈ method.feasibleSetAt k := by
  simpa [feasibleSetAt] using method.trialStep_feasible k hk

end InequalityConstrainedNullSpaceTrustRegionMethod

end

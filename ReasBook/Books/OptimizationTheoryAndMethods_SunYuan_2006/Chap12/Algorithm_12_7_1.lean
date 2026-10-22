/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Definition_12_2_extra_1
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

section

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: Chapter 12 Powell-Yuan SQP line search and stage updates;
-- * inspected project owners:
--   `WilsonHanPowellSubproblem.IsSearchDirection` in `Definition_12_2_extra_1` for the
--   canonical Step-2 SQP search-direction surface,
--   `StandardPenaltyProblem.nonsmoothExactPenalty` in `Chapter10.Definition_10_6_extra_1` as the
--   chapter's penalty owner reused by the Section 12.7 analysis, and
--   `IsOneSidedDescentDirection` in `Lemma_12_2_1` as the line-search-side predicate layer;
-- * source-facing layer kept here: the Powell-Yuan algorithm data with its recorded initial
--   point, initial penalty parameter, Hessian approximation, and Step-4 update rule;
-- * primitive data vs. derived API: the Step-2 SQP subproblem is primitive through the chapter
--   owner `WilsonHanPowellSubproblem`, while the Step-3 acceptance predicate remains local here
--   because the later Section 12.7 theory files already import this algorithm file.

/-- The accepted Step-4 trial point of Powell-Yuan's method is `x + β • d`. -/
def powellYuanTrialPoint
    (x d : Point) (β : ℝ) : Point :=
  x + β • d

/-- Unfolding `powellYuanTrialPoint x d β` gives the source Step-4 formula `x + β d`. -/
theorem powellYuanTrialPoint_eq
    (x d : Point) (β : ℝ) :
    powellYuanTrialPoint x d β = x + β • d :=
  rfl

/-- The Step-3 sufficient-decrease test `(12.7.8)` for the stage merit model `Φ`, namely
`Φ(β) ≤ Φ(0) + μ β Φ'(0)`. -/
def powellYuanSufficientDecrease
    (Φ : ℝ → ℝ) (phiDerivAtZero μ β : ℝ) : Prop :=
  Φ β ≤ Φ 0 + μ * β * phiDerivAtZero

/-- Unfolding `powellYuanSufficientDecrease Φ phiDerivAtZero μ β` gives the source inequality
`Φ(β) ≤ Φ(0) + μ β Φ'(0)`. -/
theorem powellYuanSufficientDecrease_iff
    (Φ : ℝ → ℝ) (phiDerivAtZero μ β : ℝ) :
    powellYuanSufficientDecrease Φ phiDerivAtZero μ β ↔
      Φ β ≤ Φ 0 + μ * β * phiDerivAtZero :=
  Iff.rfl

/-- A new trial steplength `βNext` belongs to the Step-3 backtracking interval
`[β₁, β₂] βPrev`, i.e. to `[β₁ * βPrev, β₂ * βPrev]`. -/
def powellYuanBacktrackingInterval
    (β₁ β₂ βPrev βNext : ℝ) : Prop :=
  βNext ∈ Set.Icc (β₁ * βPrev) (β₂ * βPrev)

/-- Unfolding `powellYuanBacktrackingInterval β₁ β₂ βPrev βNext` gives the source interval
condition `βNext ∈ [β₁ * βPrev, β₂ * βPrev]`. -/
theorem powellYuanBacktrackingInterval_iff
    (β₁ β₂ βPrev βNext : ℝ) :
    powellYuanBacktrackingInterval β₁ β₂ βPrev βNext ↔
      βNext ∈ Set.Icc (β₁ * βPrev) (β₂ * βPrev) :=
  Iff.rfl

/-- `IsPowellYuanAcceptedInnerLoop β₁ β₂ μ Φ phiDerivAtZero sigmaCondition beta sigma i`
means that the Step-3 inner loop starts from `βₖ,0 = 1`, chooses `σₖ,j` satisfying `(12.7.7)`
for every attempted index `j ≤ i`, rejects all earlier trial pairs `(σₖ,j, βₖ,j)` with
`j < i`, updates each later `βₖ,j+1` inside `[β₁, β₂] βₖ,j`, and accepts the index `i`
because `(12.7.8)` holds there. -/
def IsPowellYuanAcceptedInnerLoop
    (β₁ β₂ μ : ℝ)
    (Φ : ℕ → ℝ → ℝ)
    (phiDerivAtZero : ℕ → ℝ)
    (sigmaCondition : ℕ → ℝ → Prop)
    (beta sigma : ℕ → ℝ)
    (acceptedIndex : ℕ) : Prop :=
  beta 0 = 1 ∧
    sigmaCondition acceptedIndex (sigma acceptedIndex) ∧
    powellYuanSufficientDecrease
      (Φ acceptedIndex)
      (phiDerivAtZero acceptedIndex)
      μ
      (beta acceptedIndex) ∧
    (∀ j : ℕ, j < acceptedIndex →
      sigmaCondition j (sigma j) ∧
        ¬ powellYuanSufficientDecrease
          (Φ j)
          (phiDerivAtZero j)
          μ
          (beta j)) ∧
    ∀ j : ℕ, j < acceptedIndex →
      powellYuanBacktrackingInterval β₁ β₂ (beta j) (beta (j + 1))

/-- Unfolding `IsPowellYuanAcceptedInnerLoop` gives the source Step-3 initialization
`βₖ,0 = 1`, admissible `σₖ,j`, rejection of the earlier trial indices, and the accepted
index where `(12.7.8)` holds. -/
theorem isPowellYuanAcceptedInnerLoop_iff
    (β₁ β₂ μ : ℝ)
    (Φ : ℕ → ℝ → ℝ)
    (phiDerivAtZero : ℕ → ℝ)
    (sigmaCondition : ℕ → ℝ → Prop)
    (beta sigma : ℕ → ℝ)
    (acceptedIndex : ℕ) :
    IsPowellYuanAcceptedInnerLoop
        β₁ β₂ μ Φ phiDerivAtZero sigmaCondition beta sigma acceptedIndex ↔
      beta 0 = 1 ∧
        sigmaCondition acceptedIndex (sigma acceptedIndex) ∧
        powellYuanSufficientDecrease
          (Φ acceptedIndex)
          (phiDerivAtZero acceptedIndex)
          μ
          (beta acceptedIndex) ∧
        (∀ j : ℕ, j < acceptedIndex →
          sigmaCondition j (sigma j) ∧
            ¬ powellYuanSufficientDecrease
              (Φ j)
              (phiDerivAtZero j)
              μ
              (beta j)) ∧
        ∀ j : ℕ, j < acceptedIndex →
          powellYuanBacktrackingInterval β₁ β₂ (beta j) (beta (j + 1)) :=
  Iff.rfl

/-- The Step-4 update of Powell-Yuan's method at stage `k`: the next iterate is
`x_(k + 1) = x_k + βₖ,i d_k`, the next stage starts with `σ_(k + 1),-1 = σₖ,i`, and the
next Hessian approximation is produced by the recorded update rule. -/
def powellYuanStepUpdate
    (iterate searchDirection : ℕ → Point)
    (beta : ℕ → ℕ → ℝ)
    (acceptedInnerIndex : ℕ → ℕ)
    (sigmaStart : ℕ → ℝ)
    (sigma : ℕ → ℕ → ℝ)
    (hessianApproximation : ℕ → MatrixN)
    (hessianUpdateRule : ℕ → MatrixN → MatrixN → Prop)
    (k : ℕ) : Prop :=
  iterate (k + 1) =
      powellYuanTrialPoint
        (iterate k)
        (searchDirection k)
        (beta k (acceptedInnerIndex k)) ∧
    sigmaStart (k + 1) = sigma k (acceptedInnerIndex k) ∧
    hessianUpdateRule k (hessianApproximation k) (hessianApproximation (k + 1))

/-- Unfolding `powellYuanStepUpdate` gives the source Step-4 iterate, penalty-parameter, and
Hessian-update clauses. -/
theorem powellYuanStepUpdate_iff
    (iterate searchDirection : ℕ → Point)
    (beta : ℕ → ℕ → ℝ)
    (acceptedInnerIndex : ℕ → ℕ)
    (sigmaStart : ℕ → ℝ)
    (sigma : ℕ → ℕ → ℝ)
    (hessianApproximation : ℕ → MatrixN)
    (hessianUpdateRule : ℕ → MatrixN → MatrixN → Prop)
    (k : ℕ) :
    powellYuanStepUpdate
        iterate
        searchDirection
        beta
        acceptedInnerIndex
        sigmaStart
        sigma
        hessianApproximation
        hessianUpdateRule
        k ↔
      iterate (k + 1) =
          powellYuanTrialPoint
            (iterate k)
            (searchDirection k)
            (beta k (acceptedInnerIndex k)) ∧
        sigmaStart (k + 1) = sigma k (acceptedInnerIndex k) ∧
        hessianUpdateRule k (hessianApproximation k) (hessianApproximation (k + 1)) :=
  Iff.rfl

/-- Chapter12 Algorithm 12.7.1: Powell-Yuan's method records an initial point `x₁ : ℝ^n`,
line-search parameters `β₁ ∈ (0, 1)`, `β₂ ∈ (β₁, 1)`, and `μ ∈ (0, 1 / 2)`, an initial
positive penalty parameter `σ_(1,-1)`, an initial Hessian approximation `B₁`, and a tolerance
`ε ≥ 0`. At each stage `k ≥ 1`, Step 2 solves the SQP subproblem `(12.2.1)`-`(12.2.3)` for the
recorded direction `d_k` via the chapter's canonical Wilson-Han-Powell SQP subproblem owner and
stops when
`‖d_k‖ ≤ ε`. Otherwise the inner Step-3 loop starts from `βₖ,0 = 1`, chooses each `σₖ,i`
so that `(12.7.7)` holds, accepts the first index satisfying
`Φₖ,i(βₖ,i) ≤ Φₖ,i(0) + μ βₖ,i Φₖ,i'(0)`, and otherwise replaces `βₖ,i` by some
`βₖ,i+1 ∈ [β₁, β₂] βₖ,i`. Step 4 updates `x_(k + 1) = x_k + βₖ,i d_k`, sets
`σ_(k + 1),-1 = σₖ,i`, and updates `B_(k + 1)` by the recorded Hessian-update rule. -/
structure PowellYuanMethod (n me mi : ℕ) where
  beta₁ : ℝ
  beta₂ : ℝ
  μ : ℝ
  tolerance : ℝ
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialSigma : ℝ
  initialHessianApproximation : Matrix (Fin n) (Fin n) ℝ
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  searchDirection : ℕ → EuclideanSpace ℝ (Fin n)
  acceptedInnerIndex : ℕ → ℕ
  beta : ℕ → ℕ → ℝ
  sigmaStart : ℕ → ℝ
  sigma : ℕ → ℕ → ℝ
  phi : ℕ → ℕ → ℝ → ℝ
  phiDerivAtZero : ℕ → ℕ → ℝ
  phiHasDerivAtZero : ∀ k i : ℕ, HasDerivAt (phi k i) (phiDerivAtZero k i) 0
  sqpSubproblem : ℕ → WilsonHanPowellSubproblem n me mi
  sigmaCondition : ℕ → ℕ → ℝ → Prop
  hessianApproximation : ℕ → Matrix (Fin n) (Fin n) ℝ
  hessianUpdateRule :
    ℕ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → Prop
  beta₁_mem : beta₁ ∈ Set.Ioo (0 : ℝ) 1
  beta₂_mem : beta₂ ∈ Set.Ioo beta₁ 1
  mu_mem : μ ∈ Set.Ioo (0 : ℝ) ((1 / 2 : ℝ))
  initialSigma_pos : 0 < initialSigma
  tolerance_nonneg : 0 ≤ tolerance
  iterate_one : iterate 1 = initialPoint
  sigmaStart_one : sigmaStart 1 = initialSigma
  hessianApproximation_one : hessianApproximation 1 = initialHessianApproximation
  direction_solution :
    ∀ k : ℕ, 1 ≤ k →
      (sqpSubproblem k).IsSearchDirection (searchDirection k)
  stop_or_step :
    ∀ k : ℕ, 1 ≤ k →
      ‖searchDirection k‖ ≤ tolerance ∨
        IsPowellYuanAcceptedInnerLoop
            beta₁
            beta₂
            μ
            (phi k)
            (phiDerivAtZero k)
            (sigmaCondition k)
            (beta k)
            (sigma k)
            (acceptedInnerIndex k) ∧
          powellYuanStepUpdate
            iterate
            searchDirection
            beta
            acceptedInnerIndex
            sigmaStart
            sigma
            hessianApproximation
            hessianUpdateRule
            k

namespace PowellYuanMethod

/-- A `PowellYuanMethod` coerces to its recorded iterate sequence `k ↦ x_k`. -/
instance : CoeFun (PowellYuanMethod n me mi) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe method := method.iterate

/-- The recorded accepted Step-3 steplength at stage `k` is `βₖ,i` at the accepted inner-loop
index `i = method.acceptedInnerIndex k`. -/
def stepSizeAt
    (method : PowellYuanMethod n me mi) (k : ℕ) : ℝ :=
  method.beta k (method.acceptedInnerIndex k)

/-- Unfolding `method.stepSizeAt k` gives the accepted trial steplength `βₖ,i`. -/
theorem stepSizeAt_eq
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.stepSizeAt k = method.beta k (method.acceptedInnerIndex k) :=
  rfl

/-- The recorded accepted Step-3 penalty parameter at stage `k` is `σₖ,i` at the accepted
inner-loop index `i = method.acceptedInnerIndex k`. -/
def acceptedPenaltyParameter
    (method : PowellYuanMethod n me mi) (k : ℕ) : ℝ :=
  method.sigma k (method.acceptedInnerIndex k)

/-- Unfolding `method.acceptedPenaltyParameter k` gives the accepted penalty parameter
`σₖ,i`. -/
theorem acceptedPenaltyParameter_eq
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.acceptedPenaltyParameter k = method.sigma k (method.acceptedInnerIndex k) :=
  rfl

/-- The recorded Hessian approximation `B_k` viewed as a continuous linear self-map of
`ℝ^n`. -/
def hessianOperator
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    Point →L[ℝ] Point :=
  (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
    (method.hessianApproximation k)

/-- Unfolding `method.hessianOperator k` converts the recorded Hessian matrix `B_k` to its
continuous-linear-map action on `ℝ^n`. -/
theorem hessianOperator_eq
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.hessianOperator k =
      (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        (method.hessianApproximation k) :=
  rfl

/-- The source stopping test at stage `k` is `‖d_k‖ ≤ ε`. -/
def terminatedAt
    (method : PowellYuanMethod n me mi) (k : ℕ) : Prop :=
  ‖method.searchDirection k‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the Step-2 stopping inequality `‖d_k‖ ≤ ε`. -/
theorem terminatedAt_iff
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.terminatedAt k ↔ ‖method.searchDirection k‖ ≤ method.tolerance :=
  Iff.rfl

/-- The recorded scalar `Φₖ,i'(0)` is the derivative of the recorded merit model `Φₖ,i` at
`0`. -/
theorem phiHasDerivAtZero_at
    (method : PowellYuanMethod n me mi) (k i : ℕ) :
    HasDerivAt (method.phi k i) (method.phiDerivAtZero k i) 0 :=
  method.phiHasDerivAtZero k i

/-- The recorded scalar `Φₖ,i'(0)` agrees with `deriv (Φₖ,i) 0`. -/
theorem phiDerivAtZero_eq_deriv
    (method : PowellYuanMethod n me mi) (k i : ℕ) :
    method.phiDerivAtZero k i = deriv (method.phi k i) 0 := by
  simpa using (method.phiHasDerivAtZero_at k i).deriv.symm

/-- The recorded Step-3 data at stage `k` satisfy the accepted inner-loop predicate attached to
the accepted index `method.acceptedInnerIndex k`. -/
def acceptedInnerLoopAt
    (method : PowellYuanMethod n me mi) (k : ℕ) : Prop :=
  IsPowellYuanAcceptedInnerLoop
    method.beta₁
    method.beta₂
    method.μ
    (method.phi k)
    (method.phiDerivAtZero k)
    (method.sigmaCondition k)
    (method.beta k)
    (method.sigma k)
    (method.acceptedInnerIndex k)

/-- Unfolding `method.acceptedInnerLoopAt k` gives the Step-3 accepted inner-loop predicate
attached to the recorded data at stage `k`. -/
theorem acceptedInnerLoopAt_iff
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.acceptedInnerLoopAt k ↔
      IsPowellYuanAcceptedInnerLoop
        method.beta₁
        method.beta₂
        method.μ
        (method.phi k)
        (method.phiDerivAtZero k)
        (method.sigmaCondition k)
        (method.beta k)
        (method.sigma k)
        (method.acceptedInnerIndex k) :=
  Iff.rfl

/-- The recorded direction `d_k` satisfies the recorded Step-2 subproblem predicate at every
stage `k ≥ 1`. -/
theorem direction_solution_at
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k) :
    (method.sqpSubproblem k).IsSearchDirection (method.searchDirection k) :=
  method.direction_solution k hk

/-- When stage `k` does not terminate, the recorded accepted inner-loop index satisfies the
Step-3 admissibility and sufficient-decrease conditions. -/
theorem acceptedInnerLoopAt_of_not_terminated
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.acceptedInnerLoopAt k := by
  rcases method.stop_or_step k hk with hStop | hStep
  · exact (hNotTerminated hStop).elim
  · exact hStep.1

/-- If stage `k ≥ 1` does not terminate, then the Step-3 inner loop starts from `βₖ,0 = 1`. -/
theorem beta_zero_at
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.beta k 0 = 1 :=
  (method.acceptedInnerLoopAt_of_not_terminated hk hNotTerminated).1

/-- If stage `k ≥ 1` does not terminate, then the accepted index satisfies the Step-3
admissibility condition `(12.7.7)`. -/
theorem acceptedSigmaCondition_at
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.sigmaCondition k
      (method.acceptedInnerIndex k)
      (method.sigma k (method.acceptedInnerIndex k)) :=
  (method.acceptedInnerLoopAt_of_not_terminated hk hNotTerminated).2.1

/-- If stage `k ≥ 1` does not terminate, then the accepted Step-3 trial steplength satisfies
the sufficient-decrease condition `(12.7.8)`. -/
theorem sufficientDecrease_at
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    powellYuanSufficientDecrease
      (method.phi k (method.acceptedInnerIndex k))
      (method.phiDerivAtZero k (method.acceptedInnerIndex k))
      method.μ
      (method.stepSizeAt k) := by
  simpa [PowellYuanMethod.stepSizeAt] using
    (method.acceptedInnerLoopAt_of_not_terminated hk hNotTerminated).2.2.1

/-- If stage `k ≥ 1` does not terminate, then every earlier Step-3 trial index `j` satisfies
the admissibility condition `(12.7.7)` and is rejected by the sufficient-decrease test. -/
theorem rejectedBeforeAccepted_at
    (method : PowellYuanMethod n me mi) {k j : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) (hj : j < method.acceptedInnerIndex k) :
    method.sigmaCondition k j (method.sigma k j) ∧
      ¬ powellYuanSufficientDecrease
        (method.phi k j)
        (method.phiDerivAtZero k j)
        method.μ
        (method.beta k j) :=
  (method.acceptedInnerLoopAt_of_not_terminated hk hNotTerminated).2.2.2.1 j hj

/-- If stage `k ≥ 1` does not terminate, then every earlier Step-3 trial steplength is updated
inside the source backtracking interval `[β₁ * βₖ,j, β₂ * βₖ,j]`. -/
theorem backtrackingInterval_at
    (method : PowellYuanMethod n me mi) {k j : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) (hj : j < method.acceptedInnerIndex k) :
    powellYuanBacktrackingInterval
      method.beta₁
      method.beta₂
      (method.beta k j)
      (method.beta k (j + 1)) :=
  (method.acceptedInnerLoopAt_of_not_terminated hk hNotTerminated).2.2.2.2 j hj

/-- The recorded Step-4 data at stage `k` satisfy the Powell-Yuan update predicate. -/
def stepUpdateAt
    (method : PowellYuanMethod n me mi) (k : ℕ) : Prop :=
  powellYuanStepUpdate
    method.iterate
    method.searchDirection
    method.beta
    method.acceptedInnerIndex
    method.sigmaStart
    method.sigma
    method.hessianApproximation
    method.hessianUpdateRule
    k

/-- Unfolding `method.stepUpdateAt k` gives the Step-4 update predicate attached to the recorded
data at stage `k`. -/
theorem stepUpdateAt_iff
    (method : PowellYuanMethod n me mi) (k : ℕ) :
    method.stepUpdateAt k ↔
      powellYuanStepUpdate
        method.iterate
        method.searchDirection
        method.beta
        method.acceptedInnerIndex
        method.sigmaStart
        method.sigma
        method.hessianApproximation
        method.hessianUpdateRule
        k :=
  Iff.rfl

/-- When stage `k` does not terminate, Step 4 updates the iterate, the carry-over penalty
parameter, and the Hessian approximation according to the recorded accepted inner-loop index. -/
theorem stepUpdateAt_of_not_terminated
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.stepUpdateAt k := by
  rcases method.stop_or_step k hk with hStop | hStep
  · exact (hNotTerminated hStop).elim
  · exact hStep.2

/-- If stage `k ≥ 1` does not terminate, then Step 4 updates the iterate by the source formula
`x_(k + 1) = x_k + βₖ,i d_k` using the accepted Step-3 steplength. -/
theorem iterate_succ_eq_trialPoint
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.iterate (k + 1) =
      powellYuanTrialPoint
        (method.iterate k)
        (method.searchDirection k)
        (method.stepSizeAt k) := by
  simpa [PowellYuanMethod.stepSizeAt] using
    (method.stepUpdateAt_of_not_terminated hk hNotTerminated).1

/-- If stage `k ≥ 1` does not terminate, then Step 4 carries the accepted penalty parameter to
the next stage as `σ_(k + 1),-1 = σₖ,i`. -/
theorem sigmaStart_succ_eq_sigma
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.sigmaStart (k + 1) =
      method.sigma k (method.acceptedInnerIndex k) :=
  (method.stepUpdateAt_of_not_terminated hk hNotTerminated).2.1

/-- If stage `k ≥ 1` does not terminate, then the next Hessian approximation is produced by the
recorded Step-4 update rule from `B_k` and `B_(k + 1)`. -/
theorem hessianApproximation_succ_spec
    (method : PowellYuanMethod n me mi) {k : ℕ} (hk : 1 ≤ k)
    (hNotTerminated : ¬ method.terminatedAt k) :
    method.hessianUpdateRule
      k
      (method.hessianApproximation k)
      (method.hessianApproximation (k + 1)) :=
  (method.stepUpdateAt_of_not_terminated hk hNotTerminated).2.2

end PowellYuanMethod

/-- A `SmoothExactPenaltyMethod` is Algorithm 12.7.1 specialized to equality constraints.
It keeps the full Powell-Yuan algorithm owner and adds the stagewise constraint values
`c(x_k)` and Jacobian maps `A(x)` so that the recorded Step-2 subproblem is exactly the
chapter's canonical equality-constrained `WilsonHanPowellSubproblem`. -/
structure SmoothExactPenaltyMethod (n m : ℕ)
    extends PowellYuanMethod n m 0 where
  constraintValue : ℕ → EuclideanSpace ℝ (Fin m)
  constraintJacobian :
    EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)
  sqpSubproblem_mem_iff :
    ∀ k : ℕ, ∀ d : EuclideanSpace ℝ (Fin n),
      d.ofLp ∈ sqpSubproblem k ↔
        ContinuousLinearMap.adjoint (constraintJacobian (iterate k)) d = -constraintValue k

namespace SmoothExactPenaltyMethod

/-- The Step-2 feasibility predicate of the recorded equality-constrained SQP subproblem,
expressed directly on the Euclidean search-direction space. -/
def stageFeasible
    (method : SmoothExactPenaltyMethod n m) (k : ℕ)
    (d : EuclideanSpace ℝ (Fin n)) : Prop :=
  d.ofLp ∈ method.sqpSubproblem k

/-- Unfolding `method.stageFeasible k d` gives the source linearized equality system
`A(x_k)ᵀ d = -c(x_k)`. -/
theorem stageFeasible_iff
    (method : SmoothExactPenaltyMethod n m) (k : ℕ)
    (d : EuclideanSpace ℝ (Fin n)) :
    method.stageFeasible k d ↔
      ContinuousLinearMap.adjoint (method.constraintJacobian (method.iterate k)) d =
        -method.constraintValue k :=
  method.sqpSubproblem_mem_iff k d

end SmoothExactPenaltyMethod

end

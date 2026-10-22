/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

noncomputable section

/-- The Euclidean primal space `ℝ^n` used in the Chapter 12 specialization of
Algorithm 12.1.1. -/
abbrev LagrangeNewtonPoint (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The Euclidean multiplier space `ℝ^m` used in the Chapter 12 specialization of
Algorithm 12.1.1. -/
abbrev LagrangeNewtonMultiplier (m : ℕ) := EuclideanSpace ℝ (Fin m)

-- Semantic recall: `lean_leansearch` did not surface a canonical mathlib/project owner for the
-- SQP Lagrange-Newton loop in this item. The source-facing owner therefore stays local to this
-- file, but its core API is lifted from the coordinate model `ℝ^n × ℝ^m` to abstract primal
-- and multiplier `ℝ`-modules. The Euclidean Chapter 12 specialization is recovered by
-- `LagrangeNewtonPoint n` and `LagrangeNewtonMultiplier m`.

/-- The Step-3 trial step after exactly `quarteringCount` quarterings from the initial choice
`α = 1`; equivalently, `α = 1 / 4 ^ quarteringCount`. -/
def lagrangeNewtonStepSize (quarteringCount : ℕ) : ℝ :=
  (1 : ℝ) / (4 : ℝ) ^ quarteringCount

/-- Unfolding `lagrangeNewtonStepSize quarteringCount` gives the Step-3 quartering formula
`α = 1 / 4 ^ quarteringCount`. -/
theorem lagrangeNewtonStepSize_eq
    (quarteringCount : ℕ) :
    lagrangeNewtonStepSize quarteringCount =
      (1 : ℝ) / (4 : ℝ) ^ quarteringCount := rfl

section

variable {Point Multiplier : Type*}
variable [AddCommGroup Point] [Module ℝ Point]
variable [AddCommGroup Multiplier] [Module ℝ Multiplier]

/-- The Step-3 trial primal point `x + α δx` produced from the current iterate `x`, the Newton
direction `δx`, and a trial step size `α`. -/
def lagrangeNewtonTrialPoint
    (x δx : Point) (α : ℝ) : Point :=
  x + α • δx

/-- Unfolding `lagrangeNewtonTrialPoint x δx α` gives the source formula `x + α δx`. -/
theorem lagrangeNewtonTrialPoint_eq
    (x δx : Point) (α : ℝ) :
    lagrangeNewtonTrialPoint x δx α = x + α • δx := rfl

/-- The Step-3 trial multiplier `λ + α δλ` produced from the current multiplier `λ`, the Newton
multiplier direction `δλ`, and a trial step size `α`. -/
def lagrangeNewtonTrialMultiplier
    (lam δlam : Multiplier) (α : ℝ) : Multiplier :=
  lam + α • δlam

/-- Unfolding `lagrangeNewtonTrialMultiplier lam δlam α` gives the source formula
`λ + α δλ`. -/
theorem lagrangeNewtonTrialMultiplier_eq
    (lam δlam : Multiplier) (α : ℝ) :
    lagrangeNewtonTrialMultiplier lam δlam α = lam + α • δlam := rfl

/-- The Step-3 sufficient decrease condition `(12.1.11)` for the source merit function
`meritFunction : Point → Multiplier → ℝ`. -/
def lagrangeNewtonSufficientDecrease
    (meritFunction : Point → Multiplier → ℝ) (beta : ℝ)
    (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier) (α : ℝ) : Prop :=
  meritFunction
      (lagrangeNewtonTrialPoint x δx α)
      (lagrangeNewtonTrialMultiplier lam δlam α) ≤
    (1 - beta * α) * meritFunction x lam

/-- Unfolding `lagrangeNewtonSufficientDecrease meritFunction beta x lam δx δlam α` gives the
source inequality `(12.1.11)`. -/
theorem lagrangeNewtonSufficientDecrease_iff
    (meritFunction : Point → Multiplier → ℝ) (beta : ℝ)
    (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier) (α : ℝ) :
    lagrangeNewtonSufficientDecrease meritFunction beta x lam δx δlam α ↔
      meritFunction
          (lagrangeNewtonTrialPoint x δx α)
          (lagrangeNewtonTrialMultiplier lam δlam α) ≤
        (1 - beta * α) * meritFunction x lam := Iff.rfl

/-- `IsLagrangeNewtonAcceptedStep meritFunction beta x lam δx δlam quarteringCount` means that
the accepted Step-3 step size is `1 / 4 ^ quarteringCount`, satisfies the source sufficient
decrease condition `(12.1.11)`, and every earlier quartered trial step is rejected. -/
def IsLagrangeNewtonAcceptedStep
    (meritFunction : Point → Multiplier → ℝ) (beta : ℝ)
    (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier)
    (quarteringCount : ℕ) : Prop :=
  lagrangeNewtonSufficientDecrease
      meritFunction beta x lam δx δlam
      (lagrangeNewtonStepSize quarteringCount) ∧
    ∀ j : ℕ, j < quarteringCount →
      ¬ lagrangeNewtonSufficientDecrease
        meritFunction beta x lam δx δlam
        (lagrangeNewtonStepSize j)

/-- Unfolding `IsLagrangeNewtonAcceptedStep` gives the accepted quartered step and the rejection
of all earlier quartered trials. -/
theorem isLagrangeNewtonAcceptedStep_iff
    (meritFunction : Point → Multiplier → ℝ) (beta : ℝ)
    (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier)
    (quarteringCount : ℕ) :
    IsLagrangeNewtonAcceptedStep meritFunction beta x lam δx δlam quarteringCount ↔
      lagrangeNewtonSufficientDecrease
          meritFunction beta x lam δx δlam
          (lagrangeNewtonStepSize quarteringCount) ∧
        ∀ j : ℕ, j < quarteringCount →
          ¬ lagrangeNewtonSufficientDecrease
            meritFunction beta x lam δx δlam
            (lagrangeNewtonStepSize j) := Iff.rfl

/-- The Step-4 update formulas at stage `k`: the primal iterate and multiplier are updated by
the accepted Step-3 trial point and trial multiplier. -/
def lagrangeNewtonStepUpdate
    (iterate : ℕ → Point) (multiplier : ℕ → Multiplier)
    (pointDirection : ℕ → Point)
    (multiplierDirection : ℕ → Multiplier)
    (quarteringCount : ℕ → ℕ) (k : ℕ) : Prop :=
  iterate (k + 1) =
      lagrangeNewtonTrialPoint
        (iterate k)
        (pointDirection k)
        (lagrangeNewtonStepSize (quarteringCount k)) ∧
    multiplier (k + 1) =
      lagrangeNewtonTrialMultiplier
        (multiplier k)
        (multiplierDirection k)
        (lagrangeNewtonStepSize (quarteringCount k))

/-- Unfolding `lagrangeNewtonStepUpdate iterate multiplier pointDirection multiplierDirection
quarteringCount k` gives the two Step-4 update equalities. -/
theorem lagrangeNewtonStepUpdate_iff
    (iterate : ℕ → Point) (multiplier : ℕ → Multiplier)
    (pointDirection : ℕ → Point)
    (multiplierDirection : ℕ → Multiplier)
    (quarteringCount : ℕ → ℕ) (k : ℕ) :
    lagrangeNewtonStepUpdate iterate multiplier pointDirection multiplierDirection
        quarteringCount k ↔
      iterate (k + 1) =
          lagrangeNewtonTrialPoint
            (iterate k)
            (pointDirection k)
            (lagrangeNewtonStepSize (quarteringCount k)) ∧
        multiplier (k + 1) =
          lagrangeNewtonTrialMultiplier
            (multiplier k)
            (multiplierDirection k)
            (lagrangeNewtonStepSize (quarteringCount k)) := Iff.rfl

end

section

variable {Point Multiplier : Type*}
variable [AddCommGroup Point] [AddCommGroup Multiplier]

/-- `solvesLagrangeNewtonDirectionEquation directionEquation k x lam δx δlam` means that the
recorded Step-2 directions `(δx, δλ)` solve the source equation `(12.1.6)` at stage `k` and
current pair `(x, λ)`. Since no earlier Chapter 12 owner for `(12.1.6)` is available in this
file, the equation is kept explicit as a stagewise residual map in `(δx, δλ)`. -/
def solvesLagrangeNewtonDirectionEquation
    (directionEquation :
      ℕ →
        Point →
        Multiplier →
        Point →
        Multiplier →
        Point × Multiplier)
    (k : ℕ) (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier) : Prop :=
  directionEquation k x lam δx δlam = 0

/-- Unfolding `solvesLagrangeNewtonDirectionEquation` says that the Step-2 direction pair solves
`(12.1.6)` exactly when the recorded residual vanishes. -/
theorem solvesLagrangeNewtonDirectionEquation_iff
    (directionEquation :
      ℕ →
        Point →
        Multiplier →
        Point →
        Multiplier →
        Point × Multiplier)
    (k : ℕ) (x : Point) (lam : Multiplier)
    (δx : Point) (δlam : Multiplier) :
    solvesLagrangeNewtonDirectionEquation directionEquation k x lam δx δlam ↔
      directionEquation k x lam δx δlam = 0 := Iff.rfl

end

section

variable {Point Multiplier : Type*}
variable [AddCommGroup Point] [Module ℝ Point]
variable [AddCommGroup Multiplier] [Module ℝ Multiplier]

/-- Chapter12 Algorithm 12.1.1: a source-facing owner over a primal `ℝ`-module `Point`
and multiplier `ℝ`-module `Multiplier`. The textbook `ℝ^n × ℝ^m` presentation is recovered by
specializing to `LagrangeNewtonPoint n` and `LagrangeNewtonMultiplier m`.

It records an initial primal point `x₁`, an initial multiplier `λ₁`, a line-search parameter
`β ∈ (0, 1)`, and a tolerance `ε ≥ 0`. At each stage `k ≥ 1`, Step 2 evaluates the source
merit function `P (x_k, λ_k)` and stops when `P (x_k, λ_k) ≤ ε`; otherwise `(δx)_k` and
`(δλ)_k` are the Newton directions obtained by solving `(12.1.6)`. Step 3 starts from
`α = 1`, repeatedly replaces `α` by `α / 4` until `(12.1.11)` holds, and Step 4 updates
`x_(k + 1) = x_k + α (δx)_k` and `λ_(k + 1) = λ_k + α (δλ)_k`. -/
structure LagrangeNewtonMethod (Point Multiplier : Type*)
    [AddCommGroup Point] [Module ℝ Point]
    [AddCommGroup Multiplier] [Module ℝ Multiplier] where
  meritFunction : Point → Multiplier → ℝ
  beta : ℝ
  tolerance : ℝ
  initialPoint : Point
  initialMultiplier : Multiplier
  iterate : ℕ → Point
  multiplier : ℕ → Multiplier
  directionEquation :
    ℕ →
      Point →
      Multiplier →
      Point →
      Multiplier →
      Point × Multiplier
  pointDirection : ℕ → Point
  multiplierDirection : ℕ → Multiplier
  quarteringCount : ℕ → ℕ
  beta_mem : beta ∈ Set.Ioo (0 : ℝ) 1
  tolerance_nonneg : 0 ≤ tolerance
  iterate_one : iterate 1 = initialPoint
  multiplier_one : multiplier 1 = initialMultiplier
  directionsSolveEquation
      (k : ℕ)
      (hk : 1 ≤ k)
      (hcontinue : ¬ meritFunction (iterate k) (multiplier k) ≤ tolerance) :
      solvesLagrangeNewtonDirectionEquation
        directionEquation
        k
        (iterate k)
        (multiplier k)
        (pointDirection k)
        (multiplierDirection k)
  stop_or_step
      (k : ℕ)
      (hk : 1 ≤ k) :
      meritFunction (iterate k) (multiplier k) ≤ tolerance ∨
        IsLagrangeNewtonAcceptedStep
          meritFunction beta
          (iterate k) (multiplier k)
          (pointDirection k) (multiplierDirection k)
          (quarteringCount k) ∧
        lagrangeNewtonStepUpdate
          iterate
          multiplier
          pointDirection
          multiplierDirection
          quarteringCount
          k

/-- A `LagrangeNewtonMethod` coerces to its primal iterate sequence `k ↦ x_k`. -/
instance :
    CoeFun (LagrangeNewtonMethod Point Multiplier) (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

namespace LagrangeNewtonMethod

/-- The primal-dual iterate at stage `k` is the pair `(x_k, λ_k)`. -/
def primalDualIterate
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    Point × Multiplier :=
  (method.iterate k, method.multiplier k)

/-- Unfolding `method.primalDualIterate k` gives the source pair `(x_k, λ_k)`. -/
theorem primalDualIterate_eq
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    method.primalDualIterate k = (method.iterate k, method.multiplier k) := rfl

/-- The recorded Step-3 step size at stage `k` is the initial value `1` quartered exactly
`quarteringCount k` times. -/
def stepSizeAt
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) : ℝ :=
  lagrangeNewtonStepSize (method.quarteringCount k)

/-- Unfolding `method.stepSizeAt k` gives the explicit quartered step size
`1 / 4 ^ quarteringCount k`. -/
theorem stepSizeAt_eq
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    method.stepSizeAt k = lagrangeNewtonStepSize (method.quarteringCount k) := rfl

/-- The source stopping test at stage `k` is `P (x_k, λ_k) ≤ ε`. -/
def terminatedAt
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) : Prop :=
  method.meritFunction (method.iterate k) (method.multiplier k) ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the Step-2 stopping inequality
`P (x_k, λ_k) ≤ ε`. -/
theorem terminatedAt_iff
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    method.terminatedAt k ↔
      method.meritFunction (method.iterate k) (method.multiplier k) ≤ method.tolerance :=
  Iff.rfl

/-- The Step-2 direction pair recorded at stage `k` solves the source equation `(12.1.6)` when
the corresponding residual of `method.directionEquation` vanishes. -/
def solvesDirectionEquationAt
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) : Prop :=
  solvesLagrangeNewtonDirectionEquation
    method.directionEquation
    k
    (method.iterate k)
    (method.multiplier k)
    (method.pointDirection k)
    (method.multiplierDirection k)

/-- Unfolding `method.solvesDirectionEquationAt k` says that the recorded Step-2 directions solve
`(12.1.6)` at stage `k`. -/
theorem solvesDirectionEquationAt_iff
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    method.solvesDirectionEquationAt k ↔
      solvesLagrangeNewtonDirectionEquation
        method.directionEquation
        k
        (method.iterate k)
        (method.multiplier k)
        (method.pointDirection k)
        (method.multiplierDirection k) := Iff.rfl

/-- The recorded Step-3 data at stage `k` satisfy the accepted quartering condition. -/
def acceptedStepAt
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) : Prop :=
  IsLagrangeNewtonAcceptedStep
    method.meritFunction
    method.beta
    (method.iterate k)
    (method.multiplier k)
    (method.pointDirection k)
    (method.multiplierDirection k)
    (method.quarteringCount k)

/-- Unfolding `method.acceptedStepAt k` gives the Step-3 accepted-step predicate attached to the
recorded directions and quartering count. -/
theorem acceptedStepAt_iff
    (method : LagrangeNewtonMethod Point Multiplier) (k : ℕ) :
    method.acceptedStepAt k ↔
      IsLagrangeNewtonAcceptedStep
        method.meritFunction
        method.beta
        (method.iterate k)
        (method.multiplier k)
        (method.pointDirection k)
        (method.multiplierDirection k)
        (method.quarteringCount k) := Iff.rfl

/-- If stage `k ≥ 1` does not terminate, then the recorded Step-2 direction pair solves the
source equation `(12.1.6)`. -/
theorem directionsSolveEquation_at
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.solvesDirectionEquationAt k :=
  method.directionsSolveEquation k hk hcont

/-- If stage `k ≥ 1` does not terminate, then the recorded Step-3 data satisfy the accepted
quartered-step predicate. -/
theorem acceptedStepAt_of_not_terminated
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.acceptedStepAt k := by
  rcases method.stop_or_step k hk with hstop | hstep
  · exact False.elim (hcont hstop)
  · exact hstep.1

/-- If stage `k ≥ 1` does not terminate, then the recorded Step-3 step size satisfies the
source sufficient decrease condition `(12.1.11)`. -/
theorem sufficientDecrease_at
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    lagrangeNewtonSufficientDecrease
      method.meritFunction
      method.beta
      (method.iterate k)
      (method.multiplier k)
      (method.pointDirection k)
      (method.multiplierDirection k)
      (method.stepSizeAt k) :=
  (method.acceptedStepAt_of_not_terminated hk hcont).1

/-- If stage `k ≥ 1` does not terminate, then every earlier quartered trial step is rejected
before the recorded accepted step. -/
theorem minimal_quarteringCount
    (method : LagrangeNewtonMethod Point Multiplier) {k j : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) (hj : j < method.quarteringCount k) :
    ¬ lagrangeNewtonSufficientDecrease
      method.meritFunction
      method.beta
      (method.iterate k)
      (method.multiplier k)
      (method.pointDirection k)
      (method.multiplierDirection k)
      (lagrangeNewtonStepSize j) :=
  (method.acceptedStepAt_of_not_terminated hk hcont).2 j hj

/-- If stage `k ≥ 1` does not terminate, then Step 4 updates both the primal iterate and the
multiplier by the recorded accepted quartered step. -/
theorem stepUpdate_at
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    lagrangeNewtonStepUpdate
      method.iterate
      method.multiplier
      method.pointDirection
      method.multiplierDirection
      method.quarteringCount
      k := by
  rcases method.stop_or_step k hk with hstop | hstep
  · exact False.elim (hcont hstop)
  · exact hstep.2

/-- If stage `k ≥ 1` does not terminate, then Step 4 updates the primal iterate by the source
formula `x_(k + 1) = x_k + α (δx)_k` using the accepted step size. -/
theorem iterate_succ_eq_trialPoint
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.iterate (k + 1) =
      lagrangeNewtonTrialPoint
        (method.iterate k)
        (method.pointDirection k)
        (method.stepSizeAt k) :=
  (method.stepUpdate_at hk hcont).1

/-- If stage `k ≥ 1` does not terminate, then Step 4 updates the multiplier by the source
formula `λ_(k + 1) = λ_k + α (δλ)_k` using the accepted step size. -/
theorem multiplier_succ_eq_trialMultiplier
    (method : LagrangeNewtonMethod Point Multiplier) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ¬ method.terminatedAt k) :
    method.multiplier (k + 1) =
      lagrangeNewtonTrialMultiplier
        (method.multiplier k)
        (method.multiplierDirection k)
        (method.stepSizeAt k) :=
  (method.stepUpdate_at hk hcont).2

end LagrangeNewtonMethod

end

#print axioms lagrangeNewtonStepSize
#print axioms lagrangeNewtonTrialPoint
#print axioms lagrangeNewtonTrialMultiplier

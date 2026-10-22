/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

section Chapter11Algorithm1141

variable {ambientDim constraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin constraintDim)
local notation "TangentPoint" => EuclideanSpace ℝ (Fin tangentDim)

-- Semantic recall: `lean_leansearch` surfaced only generic orthogonal-projection and
-- decomposition APIs, not a canonical projected-gradient owner with the textbook QR and
-- correction-loop data. Following nearby Chapter 11 algorithm files, this item is formalized as
-- explicit stagewise Euclidean, matrix, reduced-gradient, and backtracking data.

/-- The Jacobian transpose `∇ C(x)ᵀ` of a vector constraint map `C : ℝ^n → ℝ^m`, written as an
`ambientDim × constraintDim` matrix in the standard Euclidean bases. -/
def constraintJacobianTranspose
    (constraint : Point → ConstraintPoint) (x : Point) :
    Matrix (Fin ambientDim) (Fin constraintDim) ℝ :=
  (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin ambientDim) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin constraintDim) ℝ).toBasis
      (fderiv ℝ constraint x).toLinearMap).transpose

/-- Unfolding `constraintJacobianTranspose constraint x` gives the transpose of the matrix of
`fderiv ℝ constraint x` in the standard Euclidean bases. -/
theorem constraintJacobianTranspose_eq
    (constraint : Point → ConstraintPoint) (x : Point) :
    constraintJacobianTranspose constraint x =
      (LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin ambientDim) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin constraintDim) ℝ).toBasis
          (fderiv ℝ constraint x).toLinearMap).transpose :=
  rfl

/-- The reduced gradient `ḡ = Zᵀ ∇ f(x)` attached to a null-space block `Z`. -/
def projectedGradientReducedGradient
    (Z : Matrix (Fin ambientDim) (Fin tangentDim) ℝ) (g : Point) : TangentPoint :=
  Matrix.toEuclideanLin (Z.transpose) g

/-- Unfolding `projectedGradientReducedGradient Z g` gives the source formula `Zᵀ g`. -/
theorem projectedGradientReducedGradient_eq
    (Z : Matrix (Fin ambientDim) (Fin tangentDim) ℝ) (g : Point) :
    projectedGradientReducedGradient Z g =
      Matrix.toEuclideanLin (Z.transpose) g :=
  rfl

/-- The projected-gradient search direction `d = -Z ḡ`. -/
def projectedGradientDirection
    (Z : Matrix (Fin ambientDim) (Fin tangentDim) ℝ) (gBar : TangentPoint) : Point :=
  -Matrix.toEuclideanLin Z gBar

/-- Unfolding `projectedGradientDirection Z gBar` gives the source formula `-Z ḡ`. -/
theorem projectedGradientDirection_eq
    (Z : Matrix (Fin ambientDim) (Fin tangentDim) ℝ) (gBar : TangentPoint) :
    projectedGradientDirection Z gBar =
      -Matrix.toEuclideanLin Z gBar :=
  rfl

/-- One Step-4 correction map `y ↦ y - Y (R⁻¹ C(y))` from Algorithm 11.4.1. The algorithm
separately records that the Step-2 QR factor `R` is nonsingular on active stages. -/
def projectedGradientCorrection
    (constraint : Point → ConstraintPoint)
    (Y : Matrix (Fin ambientDim) (Fin constraintDim) ℝ)
    (R : Matrix (Fin constraintDim) (Fin constraintDim) ℝ) :
    Point → Point :=
  fun y ↦
    y -
      Matrix.toEuclideanLin Y
        (Matrix.toEuclideanLin
          ((R⁻¹) : Matrix (Fin constraintDim) (Fin constraintDim) ℝ)
          (constraint y))

/-- Unfolding `projectedGradientCorrection constraint Y R y` gives the source correction
formula `y - Y (R⁻¹ C(y))`. -/
theorem projectedGradientCorrection_eq
    (constraint : Point → ConstraintPoint)
    (Y : Matrix (Fin ambientDim) (Fin constraintDim) ℝ)
    (R : Matrix (Fin constraintDim) (Fin constraintDim) ℝ)
    (y : Point) :
    projectedGradientCorrection constraint Y R y =
      y -
        Matrix.toEuclideanLin Y
          (Matrix.toEuclideanLin
            ((R⁻¹) : Matrix (Fin constraintDim) (Fin constraintDim) ℝ)
            (constraint y)) :=
  rfl

/-- `IsProjectedGradientCorrectionAccepted objective constraint ε̄ x y` records the Step-4
acceptance tests `‖C(y)‖ ≤ ε̄` and `f(y) < f(x)` for a corrected trial point `y`. -/
def IsProjectedGradientCorrectionAccepted
    (objective : Point → ℝ) (constraint : Point → ConstraintPoint)
    (correctionTolerance : ℝ) (x y : Point) : Prop :=
  ‖constraint y‖ ≤ correctionTolerance ∧
    objective y < objective x

/-- Unfolding `IsProjectedGradientCorrectionAccepted` gives the Step-4 acceptance inequalities. -/
theorem isProjectedGradientCorrectionAccepted_iff
    (objective : Point → ℝ) (constraint : Point → ConstraintPoint)
    (correctionTolerance : ℝ) (x y : Point) :
    IsProjectedGradientCorrectionAccepted objective constraint correctionTolerance x y ↔
      ‖constraint y‖ ≤ correctionTolerance ∧
        objective y < objective x :=
  Iff.rfl

/-- `IsProjectedGradientAcceptedTrial objective constraint ε̄ N Y R x d α i y` means that
starting from the Step-3 trial point `x + α d`, exactly `i` applications of the Step-4
correction map built from the QR factor `R` produce `y`, with `0 < i` and `i ≤ N`; every
earlier correction iterate `j < i` fails the Step-4 acceptance test; and `y` satisfies the
source acceptance tests `‖C(y)‖ ≤ ε̄` and `f(y) < f(x)`. -/
def IsProjectedGradientAcceptedTrial
    (objective : Point → ℝ) (constraint : Point → ConstraintPoint)
    (correctionTolerance : ℝ) (maxCorrectionSteps : ℕ)
    (Y : Matrix (Fin ambientDim) (Fin constraintDim) ℝ)
    (R : Matrix (Fin constraintDim) (Fin constraintDim) ℝ)
    (x d : Point) (α : ℝ) (correctionCount : ℕ) (y : Point) : Prop :=
  0 < correctionCount ∧
    correctionCount ≤ maxCorrectionSteps ∧
    y =
      Nat.iterate
        (projectedGradientCorrection constraint Y R)
        correctionCount
        (x + α • d) ∧
    (∀ j, j < correctionCount →
      ¬ IsProjectedGradientCorrectionAccepted
          objective
          constraint
          correctionTolerance
          x
          (Nat.iterate
            (projectedGradientCorrection constraint Y R)
            j
            (x + α • d))) ∧
    IsProjectedGradientCorrectionAccepted
      objective
      constraint
      correctionTolerance
      x
      y

/-- Unfolding `IsProjectedGradientAcceptedTrial` gives the bounded Step-4 correction loop and
the source acceptance inequalities, together with failure of earlier correction iterates. -/
theorem isProjectedGradientAcceptedTrial_iff
    (objective : Point → ℝ) (constraint : Point → ConstraintPoint)
    (correctionTolerance : ℝ) (maxCorrectionSteps : ℕ)
    (Y : Matrix (Fin ambientDim) (Fin constraintDim) ℝ)
    (R : Matrix (Fin constraintDim) (Fin constraintDim) ℝ)
    (x d : Point) (α : ℝ) (correctionCount : ℕ) (y : Point) :
    IsProjectedGradientAcceptedTrial
        objective constraint correctionTolerance maxCorrectionSteps Y R x d α correctionCount y ↔
      0 < correctionCount ∧
        correctionCount ≤ maxCorrectionSteps ∧
        y =
          Nat.iterate
            (projectedGradientCorrection constraint Y R)
            correctionCount
            (x + α • d) ∧
        (∀ j, j < correctionCount →
          ¬ IsProjectedGradientCorrectionAccepted
              objective
              constraint
              correctionTolerance
              x
              (Nat.iterate
                (projectedGradientCorrection constraint Y R)
                j
                (x + α • d))) ∧
        IsProjectedGradientCorrectionAccepted
          objective
          constraint
          correctionTolerance
          x
          y :=
  Iff.rfl

/-- The feasible set of the equality-constrained system `constraint x = 0`. -/
def projectedGradientFeasibleSet (constraint : Point → ConstraintPoint) : Set Point :=
  {x | constraint x = 0}

/-- Membership in `projectedGradientFeasibleSet constraint` is exactly the source feasibility
equation `constraint x = 0`. -/
theorem mem_projectedGradientFeasibleSet_iff
    (constraint : Point → ConstraintPoint) (x : Point) :
    x ∈ projectedGradientFeasibleSet constraint ↔ constraint x = 0 :=
  Iff.rfl

/-- Chapter11 Algorithm 11.4.1: a projected gradient method on `ℝ^ambientDim` with constraint
map `C : ℝ^ambientDim → ℝ^constraintDim` records a feasible initial point `x₁ ∈ X`, tolerances
`ε ≥ 0` and `ε̄ > 0`, a positive integer bound `N` for the Step-4 correction loop, and for
each active stage `k ≥ 1` concrete QR data `Y_k`, `Z_k`, `R_k`, reduced gradient `ḡ_k`,
search direction `d_k`, initial trial step `α_k^(0)`, dyadic backtracking count, accepted
step size `α_k`, accepted correction count, and accepted trial point `y_k`. The feasible set is
the zero set of `constraint`, the QR data satisfy `∇ C(x_k)ᵀ = Y_k R_k`, `R_k` is upper
triangular, and `[Y_k  Z_k]`
forms an orthogonal block decomposition via orthonormality, cross-orthogonality, and the
identity decomposition `Y_k Y_kᵀ + Z_k Z_kᵀ = 1`; active stages carry explicit
`DifferentiableAt` hypotheses for `objective` and `constraint` at `x_k`; Step 2 computes
`ḡ_k = Z_kᵀ ∇ f(x_k)` and, on continuing stages, `d_k = -Z_k ḡ_k`; the active stages satisfy
`active (k + 1) ↔ active k ∧ ε < ‖ḡ_k‖`; Step 4 uses the explicit nonsingularity of `R_k`
for the correction map, and accepts `y_k` after a positive number of explicit correction
steps bounded by `N`, with failure of all earlier correction iterates;
and every earlier dyadic backtracking exponent fails to yield any accepted Step-4 outcome,
with `x_(k + 1) = y_k`. -/
structure ProjectedGradientMethod (ambientDim constraintDim tangentDim : ℕ) where
  objective : EuclideanSpace ℝ (Fin ambientDim) → ℝ
  constraint : EuclideanSpace ℝ (Fin ambientDim) → EuclideanSpace ℝ (Fin constraintDim)
  tolerance : ℝ
  correctionTolerance : ℝ
  maxCorrectionSteps : ℕ
  initialPoint : EuclideanSpace ℝ (Fin ambientDim)
  active : ℕ → Prop
  iterate : ℕ → EuclideanSpace ℝ (Fin ambientDim)
  yFactor : ℕ → Matrix (Fin ambientDim) (Fin constraintDim) ℝ
  zFactor : ℕ → Matrix (Fin ambientDim) (Fin tangentDim) ℝ
  rFactor : ℕ → Matrix (Fin constraintDim) (Fin constraintDim) ℝ
  reducedGradient : ℕ → EuclideanSpace ℝ (Fin tangentDim)
  direction : ℕ → EuclideanSpace ℝ (Fin ambientDim)
  initialStep : ℕ → ℝ
  backtrackingCount : ℕ → ℕ
  stepSize : ℕ → ℝ
  correctionCount : ℕ → ℕ
  acceptedTrial : ℕ → EuclideanSpace ℝ (Fin ambientDim)
  qrBlockSize : constraintDim + tangentDim = ambientDim
  tolerance_nonneg : 0 ≤ tolerance
  correctionTolerance_pos : 0 < correctionTolerance
  maxCorrectionSteps_pos : 0 < maxCorrectionSteps
  initialPoint_mem : initialPoint ∈ projectedGradientFeasibleSet constraint
  active_one : active 1
  iterate_one : iterate 1 = initialPoint
  active_succ_iff :
    ∀ k, 1 ≤ k →
      (active (k + 1) ↔ active k ∧ tolerance < ‖reducedGradient k‖)
  objectiveDifferentiableAt :
    ∀ k, 1 ≤ k → active k → DifferentiableAt ℝ objective (iterate k)
  constraintDifferentiableAt :
    ∀ k, 1 ≤ k → active k → DifferentiableAt ℝ constraint (iterate k)
  qrFactorization :
    ∀ k, 1 ≤ k → active k →
      constraintJacobianTranspose constraint (iterate k) =
        yFactor k * rFactor k
  rFactor_upperTriangular :
    ∀ k, 1 ≤ k → active k →
      (rFactor k).BlockTriangular id
  yFactor_orthonormal :
    ∀ k, 1 ≤ k → active k →
      (yFactor k).transpose * yFactor k = 1
  yz_orthogonal :
    ∀ k, 1 ≤ k → active k →
      (yFactor k).transpose * zFactor k = 0
  zFactor_orthonormal :
    ∀ k, 1 ≤ k → active k →
      (zFactor k).transpose * zFactor k = 1
  orthogonalDecomposition :
    ∀ k, 1 ≤ k → active k →
      yFactor k * (yFactor k).transpose +
          zFactor k * (zFactor k).transpose =
        1
  rFactor_nonsingular :
    ∀ k, 1 ≤ k → active k →
      IsUnit (Matrix.det (rFactor k))
  reducedGradient_eq :
    ∀ k, 1 ≤ k → active k →
      reducedGradient k =
        projectedGradientReducedGradient
          (zFactor k)
          (gradient objective (iterate k))
  direction_eq :
    ∀ k, 1 ≤ k → active (k + 1) →
      direction k =
        projectedGradientDirection (zFactor k) (reducedGradient k)
  initialStep_pos :
    ∀ k, 1 ≤ k → active (k + 1) → 0 < initialStep k
  stepSize_eq :
    ∀ k, 1 ≤ k → active (k + 1) →
      stepSize k = initialStep k / (2 : ℝ) ^ backtrackingCount k
  earlierBacktrackingRejected :
    ∀ k, 1 ≤ k → active k → active (k + 1) →
      ∀ b, b < backtrackingCount k →
        ∀ i, i ≤ maxCorrectionSteps →
          ∀ y,
            ¬ IsProjectedGradientAcceptedTrial
                objective
                constraint
                correctionTolerance
                maxCorrectionSteps
                (yFactor k)
                (rFactor k)
                (iterate k)
                (direction k)
                (initialStep k / (2 : ℝ) ^ b)
                i
                y
  acceptedTrial_spec :
    ∀ k, 1 ≤ k → active k → active (k + 1) →
      IsProjectedGradientAcceptedTrial
        objective
        constraint
        correctionTolerance
        maxCorrectionSteps
        (yFactor k)
        (rFactor k)
        (iterate k)
        (direction k)
        (stepSize k)
        (correctionCount k)
        (acceptedTrial k)
  iterate_succ :
    ∀ k, 1 ≤ k → active (k + 1) →
      iterate (k + 1) = acceptedTrial k

namespace ProjectedGradientMethod

/-- `method` can be evaluated as its iterate sequence `x_k`. -/
instance : CoeFun (_root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The Step-3 trial point at stage `k` is `x_k + α_k d_k`. -/
def trialPointAt
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) : Point :=
  method.iterate k + method.stepSize k • method.direction k

/-- Unfolding `method.trialPointAt k` gives the Step-3 trial-point formula `x_k + α_k d_k`. -/
theorem trialPointAt_eq
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    method.trialPointAt k = method.iterate k + method.stepSize k • method.direction k :=
  rfl

/-- The Step-4 correction map attached to stage `k` uses the recorded factors `Y_k` and `R_k`. -/
def correctionMapAt
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) : Point → Point :=
  projectedGradientCorrection method.constraint (method.yFactor k) (method.rFactor k)

/-- Unfolding `method.correctionMapAt k` gives the stagewise Step-4 correction map. -/
theorem correctionMapAt_eq
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    method.correctionMapAt k =
      projectedGradientCorrection method.constraint (method.yFactor k) (method.rFactor k) :=
  rfl

/-- Algorithm 11.4.1 is terminated at stage `k` exactly when `‖ḡ_k‖ ≤ ε`. -/
def terminatedAt
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) : Prop :=
  ‖method.reducedGradient k‖ ≤ method.tolerance

/-- Unfolding `method.terminatedAt k` gives the Step-2 stopping test `‖ḡ_k‖ ≤ ε`. -/
theorem terminatedAt_iff
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    method.terminatedAt k ↔ ‖method.reducedGradient k‖ ≤ method.tolerance :=
  Iff.rfl

/-- The initial point recorded by Algorithm 11.4.1 lies in the zero set of the source
constraint map. -/
theorem initialPoint_mem_feasibleSet
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    :
    method.initialPoint ∈ projectedGradientFeasibleSet method.constraint :=
  method.initialPoint_mem

/-- The initial point recorded by Algorithm 11.4.1 is feasible for the source constraint map. -/
theorem constraint_initialPoint_eq_zero
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim) :
    method.constraint method.initialPoint = 0 :=
  (mem_projectedGradientFeasibleSet_iff method.constraint method.initialPoint).1
    method.initialPoint_mem

/-- For each stage `k ≥ 1`, the algorithm continues to `k + 1` exactly when stage `k` is
active and the Step-2 stopping test fails. -/
theorem active_succ_iff_not_terminatedAt
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) :
    method.active (k + 1) ↔ method.active k ∧ ¬ method.terminatedAt k := by
  simpa [terminatedAt, not_le] using method.active_succ_iff k hk

/-- Any active stage `k + 1` comes from an active previous stage `k`; later stages do not
reappear after the Step-2 stopping condition terminates the method. -/
theorem active_of_active_succ
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.active k :=
  (method.active_succ_iff_not_terminatedAt hk).1 hactive |>.1

/-- On each active stage, the source objective gradient data are taken at a genuinely
differentiable point `x_k`. -/
theorem objectiveDifferentiableAt_of_active
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    DifferentiableAt ℝ method.objective (method.iterate k) :=
  method.objectiveDifferentiableAt k hk hactive

/-- On each active stage, the source constraint Jacobian data are taken at a genuinely
differentiable point `x_k`. -/
theorem constraintDifferentiableAt_of_active
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    DifferentiableAt ℝ method.constraint (method.iterate k) :=
  method.constraintDifferentiableAt k hk hactive

/-- On each active stage, the Step-2 QR factor `R_k` is upper triangular. -/
theorem rFactor_upperTriangular_of_active
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    (method.rFactor k).BlockTriangular id :=
  method.rFactor_upperTriangular k hk hactive

/-- On each active stage, the Step-2 QR data satisfy `∇ C(x_k)ᵀ = Y_k R_k`. -/
theorem qrFactorization_of_active
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    constraintJacobianTranspose method.constraint (method.iterate k) =
      method.yFactor k * method.rFactor k :=
  method.qrFactorization k hk hactive

/-- On each active stage, the reduced gradient is the source quantity `ḡ_k = Z_kᵀ ∇ f(x_k)`. -/
theorem reducedGradient_eq_of_active
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active k) :
    method.reducedGradient k =
      projectedGradientReducedGradient
        (method.zFactor k)
        (gradient method.objective (method.iterate k)) :=
  method.reducedGradient_eq k hk hactive

/-- On each continuing stage, the Step-2 QR factor `R_k` is nonsingular, so the Step-4
correction uses the intended inverse. -/
theorem rFactor_nonsingular_of_active_succ
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    IsUnit (Matrix.det (method.rFactor k)) :=
  method.rFactor_nonsingular k hk (method.active_of_active_succ hk hactive)

/-- On each continuing stage, the recorded search direction is the source projected-gradient
direction `d_k = -Z_k ḡ_k`. -/
theorem direction_eq_of_active_succ
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.direction k =
      projectedGradientDirection (method.zFactor k) (method.reducedGradient k) :=
  method.direction_eq k hk hactive

/-- On each continuing stage, the accepted step size is obtained from the source initial trial
step by dyadic backtracking. -/
theorem stepSize_eq_initialStep_div_pow
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.stepSize k = method.initialStep k / (2 : ℝ) ^ method.backtrackingCount k :=
  method.stepSize_eq k hk hactive

/-- On each continuing stage, every earlier dyadic trial step fails to produce an accepted
Step-4 outcome within the bounded correction loop. -/
theorem earlierBacktrackingExponent_notAccepted
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1))
    {b i : ℕ} (hb : b < method.backtrackingCount k)
    (hi : i ≤ method.maxCorrectionSteps) (y : Point) :
    ¬ IsProjectedGradientAcceptedTrial
        method.objective
        method.constraint
        method.correctionTolerance
        method.maxCorrectionSteps
        (method.yFactor k)
        (method.rFactor k)
        (method.iterate k)
        (method.direction k)
        (method.initialStep k / (2 : ℝ) ^ b)
        i
        y :=
  method.earlierBacktrackingRejected
    k
    hk
    (method.active_of_active_succ hk hactive)
    hactive
    b
    hb
    i
    hi
    y

/-- On each continuing stage, the recorded accepted trial satisfies the bounded Step-4
correction-loop acceptance predicate. -/
theorem acceptedTrial_isAccepted
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    IsProjectedGradientAcceptedTrial
      method.objective
      method.constraint
      method.correctionTolerance
      method.maxCorrectionSteps
      (method.yFactor k)
      (method.rFactor k)
      (method.iterate k)
      (method.direction k)
      (method.stepSize k)
      (method.correctionCount k)
      (method.acceptedTrial k) :=
  method.acceptedTrial_spec
    k
    hk
    (method.active_of_active_succ hk hactive)
    hactive

/-- Unfolding the recorded accepted Step-4 trial at stage `k` gives the bounded correction loop
from the Step-3 trial point, the failure of earlier correction iterates, and the source
acceptance inequalities. -/
theorem acceptedTrial_spec_iff
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    IsProjectedGradientAcceptedTrial
        method.objective
        method.constraint
        method.correctionTolerance
        method.maxCorrectionSteps
        (method.yFactor k)
        (method.rFactor k)
        (method.iterate k)
        (method.direction k)
        (method.stepSize k)
        (method.correctionCount k)
        (method.acceptedTrial k) ↔
      0 < method.correctionCount k ∧
        method.correctionCount k ≤ method.maxCorrectionSteps ∧
        method.acceptedTrial k =
          Nat.iterate
            (method.correctionMapAt k)
            (method.correctionCount k)
            (method.trialPointAt k) ∧
        (∀ j, j < method.correctionCount k →
          ¬ IsProjectedGradientCorrectionAccepted
              method.objective
              method.constraint
              method.correctionTolerance
              (method.iterate k)
              (Nat.iterate
                (method.correctionMapAt k)
                j
                (method.trialPointAt k))) ∧
        IsProjectedGradientCorrectionAccepted
          method.objective
          method.constraint
          method.correctionTolerance
          (method.iterate k)
          (method.acceptedTrial k) :=
  Iff.rfl

/-- On each continuing stage, the recorded accepted trial is the `correctionCount k`-th Step-4
iterate of the stagewise correction map applied to the Step-3 trial point. -/
theorem acceptedTrial_eq_iterate_correctionMapAt
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.acceptedTrial k =
      Nat.iterate
        (method.correctionMapAt k)
        (method.correctionCount k)
        (method.trialPointAt k) := by
  exact (method.acceptedTrial_spec_iff k).mp (method.acceptedTrial_isAccepted hk hactive) |>.2.2.1

/-- On each continuing stage, every earlier Step-4 correction iterate fails the source
acceptance test. -/
theorem earlierCorrectionIterate_notAccepted
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k j : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1))
    (hj : j < method.correctionCount k) :
    ¬ IsProjectedGradientCorrectionAccepted
        method.objective
        method.constraint
        method.correctionTolerance
        (method.iterate k)
        (Nat.iterate (method.correctionMapAt k) j (method.trialPointAt k)) := by
  exact
    ((method.acceptedTrial_spec_iff k).mp
      (method.acceptedTrial_isAccepted hk hactive) |>.2.2.2.1) j hj

/-- On each continuing stage, the recorded accepted trial satisfies the final Step-4 acceptance
test relative to the current iterate `x_k`. -/
theorem acceptedTrial_correctionAccepted
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    IsProjectedGradientCorrectionAccepted
      method.objective
      method.constraint
      method.correctionTolerance
      (method.iterate k)
      (method.acceptedTrial k) := by
  exact (method.acceptedTrial_spec_iff k).mp (method.acceptedTrial_isAccepted hk hactive) |>.2.2.2.2

/-- On each continuing stage, Step 5 updates the next iterate by `x_(k + 1) = y_k`. -/
theorem iterate_succ_eq_acceptedTrial
    (method : _root_.ProjectedGradientMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (hactive : method.active (k + 1)) :
    method.iterate (k + 1) = method.acceptedTrial k :=
  method.iterate_succ k hk hactive

end ProjectedGradientMethod

#print axioms constraintJacobianTranspose
#print axioms projectedGradientReducedGradient
#print axioms projectedGradientDirection
#print axioms projectedGradientCorrection
#print axioms projectedGradientFeasibleSet

end Chapter11Algorithm1141

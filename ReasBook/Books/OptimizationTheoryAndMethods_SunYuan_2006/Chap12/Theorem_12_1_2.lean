/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.EqualityConstrainedProblem

open Filter
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

section

variable {n m : ℕ}

local notation "Point" => LagrangeNewtonPoint n
local notation "Multiplier" => LagrangeNewtonMultiplier m
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ

-- Domain-style sampling:
-- * primary domain: equality-constrained Lagrange-Newton accumulation-point theory for the
--   Chapter 12 KKT residual and block system
-- * inspected owner declarations in the minimal semantic closure:
--   - `LagrangeNewtonMethod` from `Algorithm_12_1_1`
--   - `EqualityConstrainedProblem` and
--     `EqualityConstrainedProblem.lagrangeNewtonKKTMatrix` from
--     `Chapter12.EqualityConstrainedProblem`
--   - the generic Chapter 12 Jacobian owner `lagrangeNewtonConstraintJacobian` from
--     `Theorem_12_1_4`
-- * best owner abstraction: the source-facing problem data are owned by
--   `EqualityConstrainedProblem`, and the algorithm run is owned by the canonical
--   `LagrangeNewtonMethod`; this file keeps only thin bridge predicates and owner-side derived
--   API connecting them
-- * primitive data vs derived API:
--   - primitive data: `problem : EqualityConstrainedProblem n m`, the recorded
--     `LagrangeNewtonMethod`, and the explicit Hessian field
--     `W : Point → Multiplier → HessianMatrix`
--   - derived API here: the theorem-local residual `lagrangeNewtonRootResidual`, the
--     Step-2 residual map, the thin bridge predicate `method.IsFor problem W`, and the
--     bounded-inverse hypothesis for the source KKT matrices

-- Semantic recall: `lean_leansearch` surfaced generic accumulation-point APIs such as `AccPt`,
-- while Chapter 10/12 precedent encodes accumulation points of algorithmic sequences by
-- convergent subsequences `φ` with `StrictMono φ`. The canonical Algorithm 12.1.1 owner now
-- lives in `Algorithm_12_1_1`, while the fixed equality-constrained problem data now live in
-- `Chapter12.EqualityConstrainedProblem`.

local notation "Method" => _root_.LagrangeNewtonMethod Point Multiplier

/-- The concrete Step-2 Newton residual from `(12.1.18)` for Algorithm 12.1.1 at the fixed
problem `problem`: its upper block is the Lagrangian stationarity residual, while its lower
block is the canonical vector of linearized equality constraints
`i ↦ problem.constraintLinearization x δx i`. -/
def lagrangeNewtonDirectionEquation
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) :
    ℕ → Point → Multiplier → Point → Multiplier → Point × Multiplier :=
  fun _ x lam δx δlam ↦
    let A := problem.constraintGradientMatrix x
    ( Matrix.toEuclideanLin (W x lam) δx
        - Matrix.toEuclideanLin A δlam
        + (gradient problem.objective x - Matrix.toEuclideanLin A lam)
    , WithLp.toLp 2 (fun i ↦ problem.constraintLinearization x δx i) )

/-- The lower block of `lagrangeNewtonDirectionEquation` is the canonical vector of
linearized equality constraints. -/
@[simp] theorem lagrangeNewtonDirectionEquation_constraint_apply
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix)
    (k : ℕ) (x : Point) (lam : Multiplier) (δx : Point) (δlam : Multiplier) (i : Fin m) :
    (lagrangeNewtonDirectionEquation problem W k x lam δx δlam).2 i =
      problem.constraintLinearization x δx i :=
  rfl

/-- The Chapter 12 root residual at `(x, λ)`, namely the KKT residual
`(∇f(x) - A(x) λ, c(x))` whose vanishing encodes the source conclusion `P(x, λ) = 0`. -/
def lagrangeNewtonRootResidual
    (problem : EqualityConstrainedProblem n m) (x : Point) (lam : Multiplier) :
    Point × Multiplier :=
  let A := problem.constraintGradientMatrix x
  (gradient problem.objective x - Matrix.toEuclideanLin A lam, problem.constraintVector x)

/-- Unfolding `lagrangeNewtonRootResidual problem x lam` gives the concrete KKT residual
`(∇f(x) - A(x) λ, c(x))`. -/
theorem lagrangeNewtonRootResidual_eq
    (problem : EqualityConstrainedProblem n m) (x : Point) (lam : Multiplier) :
    lagrangeNewtonRootResidual problem x lam =
      ( gradient problem.objective x
          - Matrix.toEuclideanLin (problem.constraintGradientMatrix x) lam
      , problem.constraintVector x ) := rfl

/-- `IsLagrangeNewtonRoot problem x lam` means that `(x, λ)` is a root of the Chapter 12
residual condition `P(x, λ) = 0`, encoded here by vanishing of the concrete KKT residual
`(∇f(x) - A(x) λ, c(x))`. -/
def IsLagrangeNewtonRoot
    (problem : EqualityConstrainedProblem n m) (x : Point) (lam : Multiplier) : Prop :=
  lagrangeNewtonRootResidual problem x lam = 0

/-- Unfolding `IsLagrangeNewtonRoot problem x lam` says that the Chapter 12 root condition is
exactly the vanishing of `lagrangeNewtonRootResidual problem x lam`. -/
theorem isLagrangeNewtonRoot_iff
    (problem : EqualityConstrainedProblem n m) (x : Point) (lam : Multiplier) :
    IsLagrangeNewtonRoot problem x lam ↔
      lagrangeNewtonRootResidual problem x lam = 0 := Iff.rfl

namespace LagrangeNewtonMethod

/-- `method.IsFor problem W` records the theorem-local bridge saying that the canonical
Algorithm 12.1.1 owner `method` is being used for the fixed equality-constrained problem
`problem` with Hessian field `W`: its recorded Step-2 equation is the concrete Newton system
`(12.1.18)`, and its merit-function zero set is exactly the Chapter 12 root condition
`IsLagrangeNewtonRoot problem`. -/
def IsFor
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) : Prop :=
  method.directionEquation = lagrangeNewtonDirectionEquation problem W ∧
    ∀ x : Point, ∀ lam : Multiplier,
      method.meritFunction x lam = 0 ↔ IsLagrangeNewtonRoot problem x lam

/-- Under `method.IsFor problem W`, the recorded Step-2 equation is the concrete Newton
equation `(12.1.18)` for `problem`. -/
theorem IsFor.directionEquation_eq
    {method : Method} {problem : EqualityConstrainedProblem n m}
    {W : Point → Multiplier → HessianMatrix}
    (h : method.IsFor problem W) :
    method.directionEquation = lagrangeNewtonDirectionEquation problem W :=
  h.1

/-- Under `method.IsFor problem W`, the source merit-function root condition agrees with the
concrete Chapter 12 root residual. -/
theorem IsFor.meritFunction_eq_zero_iff
    {method : Method} {problem : EqualityConstrainedProblem n m}
    {W : Point → Multiplier → HessianMatrix}
    (h : method.IsFor problem W) (x : Point) (lam : Multiplier) :
    method.meritFunction x lam = 0 ↔ IsLagrangeNewtonRoot problem x lam :=
  h.2 x lam

/-- The stage-`k` KKT matrix `(12.1.12)` attached to `method` for the fixed problem `problem`
and Hessian field `W`, namely `[[W(x_k, λ_k), -A(x_k)], [-(A(x_k))ᵀ, 0]]`. -/
def kktMatrixAt
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix)
    (k : ℕ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  problem.lagrangeNewtonKKTMatrix
    (method.iterate k)
    (W (method.iterate k) (method.multiplier k))

/-- Unfolding `method.kktMatrixAt problem W k` gives the source KKT matrix `(12.1.12)` at
stage `k`. -/
theorem kktMatrixAt_eq
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix)
    (k : ℕ) :
    method.kktMatrixAt problem W k =
      problem.lagrangeNewtonKKTMatrix
        (method.iterate k)
        (W (method.iterate k) (method.multiplier k)) :=
  rfl

/-- `method.HasUniformlyBoundedKKTInverse problem W` means that along the stage indices
`k ≥ 1` of the Algorithm 12.1.1 sequence generated for the fixed problem `problem`, each source
KKT block matrix `[[W(x_k, λ_k), -A(x_k)], [-A(x_k)ᵀ, 0]]` from `(12.1.12)` built from the
explicit Hessian field `W` and the canonical Jacobian `A = problem.constraintGradientMatrix`
is invertible and its inverse has norm bounded by one common constant. -/
def HasUniformlyBoundedKKTInverse
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) : Prop :=
  ∃ bound : ℝ,
    0 ≤ bound ∧
      ∀ k : ℕ, 1 ≤ k →
        IsUnit (method.kktMatrixAt problem W k) ∧
          ‖(method.kktMatrixAt problem W k)⁻¹‖ ≤ bound

/-- Unfolding `method.HasUniformlyBoundedKKTInverse problem W` gives a common norm bound for
the inverse KKT matrices `[[W(x_k, λ_k), -A(x_k)], [-A(x_k)ᵀ, 0]]⁻¹` along the stages `k ≥ 1`,
together with explicit invertibility of each stagewise KKT matrix. -/
theorem hasUniformlyBoundedKKTInverse_iff
    (method : Method)
    (problem : EqualityConstrainedProblem n m)
    (W : Point → Multiplier → HessianMatrix) :
    method.HasUniformlyBoundedKKTInverse problem W ↔
      ∃ bound : ℝ,
        0 ≤ bound ∧
          ∀ k : ℕ, 1 ≤ k →
            IsUnit (method.kktMatrixAt problem W k) ∧
              ‖(method.kktMatrixAt problem W k)⁻¹‖ ≤ bound :=
  Iff.rfl

end LagrangeNewtonMethod

/-- Chapter12 Theorem 12.1.2: assume `problem.objective` and each component of
`problem.constraint` are twice continuously differentiable. If the inverse of the source KKT
matrix `[[W(x_k, λ_k), -A(x_k)], [-A(x_k)ᵀ, 0]]` from `(12.1.12)` has uniformly bounded inverse
norm along the Algorithm 12.1.1 sequence generated by the canonical owner `method`, whose
Step 2 equation and merit-function root condition are connected to the fixed problem `problem`
by `hMethod : method.IsFor problem W`, then every accumulation point of the primal-dual
iterate sequence `{(x_k, λ_k)}` is a root of the source equation
`IsLagrangeNewtonRoot problem xStar lamStar`; equivalently, under `hMethod`, the recorded merit
function also vanishes there. The subsequence encoding `φ k + 1` matches the source indexing
from stage `1`. -/
theorem lagrangeNewtonMethod_accumulationPoint_isRoot
    (problem : EqualityConstrainedProblem n m)
    (method : Method)
    (W : Point → Multiplier → HessianMatrix)
    (hMethod : method.IsFor problem W)
    (hObjectiveC2 : ContDiff ℝ 2 problem.objective)
    (hConstraintC2 : ∀ i : Fin m, ContDiff ℝ 2 (problem.constraint i))
    (hBoundedInverse : method.HasUniformlyBoundedKKTInverse problem W)
    {xStar : Point} {lamStar : Multiplier} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hAccumulation :
      Tendsto
        (fun k : ℕ ↦ method.primalDualIterate (φ k + 1))
        atTop
        (nhds (xStar, lamStar))) :
    IsLagrangeNewtonRoot problem xStar lamStar := sorry

#print axioms lagrangeNewtonStepSize
#print axioms lagrangeNewtonTrialPoint
#print axioms lagrangeNewtonTrialMultiplier
#print axioms EqualityConstrainedProblem.lagrangeNewtonKKTMatrix
#print axioms _root_.LagrangeNewtonMethod.primalDualIterate

end

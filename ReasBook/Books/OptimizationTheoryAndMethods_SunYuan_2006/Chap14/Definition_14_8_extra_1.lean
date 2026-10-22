/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

noncomputable section

open Filter

section

-- Domain sampling:
-- * primary domain: generalized Jacobians in real normed-space nonsmooth analysis
-- * mathlib owners sampled in this domain: `fderiv`, `convexHull`, `LinearMap.toMatrix`
-- * Chapter 14 owner pattern sampled nearby: `clarkeDifferential` in `Lemma_14_1_3` and the
--   bridge file `Definition_14_2_extra_1` keep only the intrinsic owner public, with view
--   surfaces derived from it.
-- * source/core/bridge triage here:
--   source-facing owner: `generalizedJacobian F x : Set (X →L[ℝ] Y)`
--   bridge/view layer: the Euclidean coordinate-matrix specialization
--   `jacobianMatrixOfMap` and `generalizedJacobianMatrix`
-- The sequential differentiability/limit construction is therefore kept only inside the owner
-- definition instead of being exported as parallel public helper sets.
universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Chapter14 Definition 14.8-extra-1: for a map `F : X → Y`, the generalized Jacobian `∂F(x)`
is the convex hull of all Jacobian-map limits obtained from sequences `x_i → x` through
differentiability points, with the intrinsic Fréchet derivative `fderiv ℝ F (x_i)` as the
primitive Jacobian object. The source Euclidean `ℝ^n → ℝ^m` case is recovered by specializing
`X` and `Y` to finite-dimensional real Euclidean spaces; the matrix layer is a separate bridge
below. -/
def generalizedJacobian (F : X → Y) (x : X) : Set (X →L[ℝ] Y) :=
  convexHull ℝ
    {V : X →L[ℝ] Y | ∃ xs : ℕ → X,
        Tendsto xs atTop (nhds x) ∧
        (∀ i : ℕ, DifferentiableAt ℝ F (xs i)) ∧
        Tendsto (fun i : ℕ ↦ fderiv ℝ F (xs i)) atTop (nhds V)}

scoped[GeneralizedJacobian] prefix:100 "∂ " => generalizedJacobian

open scoped GeneralizedJacobian

/-- A Jacobian map belongs to `(∂ F) x = ∂F(x)` exactly when it belongs to the convex hull of the
Fréchet-derivative limits from Chapter14 Definition 14.8-extra-1. -/
theorem mem_generalizedJacobian_iff (F : X → Y) (x : X) (V : X →L[ℝ] Y) :
    V ∈ (∂ F) x ↔
      V ∈ convexHull ℝ
        {A : X →L[ℝ] Y | ∃ xs : ℕ → X,
            Tendsto xs atTop (nhds x) ∧
            (∀ i : ℕ, DifferentiableAt ℝ F (xs i)) ∧
            Tendsto (fun i : ℕ ↦ fderiv ℝ F (xs i)) atTop (nhds A)} := by
  rfl

/-- The generalized-Jacobian notation `∂ F` is just the owner `generalizedJacobian F`. -/
theorem generalizedJacobian_eq (F : X → Y) : (∂ F) = generalizedJacobian F :=
  rfl

end

open scoped GeneralizedJacobian

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "JacobianMap" => Point →L[ℝ] ValuePoint
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

/-- The standard-basis matrix of a Jacobian map `A : ℝ^n →L[ℝ] ℝ^m`. -/
abbrev jacobianMatrixOfMap (A : JacobianMap) : JacobianMatrix :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    A.toLinearMap

/-- The canonical continuous-linear-map view of a Jacobian matrix `V : ℝ^(m×n)`. -/
abbrev jacobianMapOfMatrix (V : JacobianMatrix) : JacobianMap :=
  (Matrix.toEuclideanLin V).toContinuousLinearMap

@[simp] theorem jacobianMapOfMatrix_jacobianMatrixOfMap (A : JacobianMap) :
    jacobianMapOfMatrix (jacobianMatrixOfMap A) = A := by
  ext x i
  simp [jacobianMapOfMatrix, jacobianMatrixOfMap, Matrix.toEuclideanLin_eq_toLin_orthonormal]

@[simp] theorem jacobianMatrixOfMap_jacobianMapOfMatrix (V : JacobianMatrix) :
    jacobianMatrixOfMap (jacobianMapOfMatrix V) = V := by
  simp [jacobianMapOfMatrix, jacobianMatrixOfMap, Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- The coordinate-matrix view of `(∂ F) x = ∂F(x)`, used only in files that genuinely need
matrix inversion or matrix-coordinate formulas. -/
def generalizedJacobianMatrix (F : Point → ValuePoint) (x : Point) : Set JacobianMatrix :=
  Set.image jacobianMatrixOfMap ((∂ F) x)

/-- A matrix belongs to `generalizedJacobianMatrix F x` exactly when it is the standard-basis
matrix of some generalized Jacobian map in `(∂ F) x = ∂F(x)`. -/
theorem mem_generalizedJacobianMatrix_iff
    (F : Point → ValuePoint) (x : Point) (V : JacobianMatrix) :
    V ∈ generalizedJacobianMatrix F x ↔
      ∃ A : JacobianMap, A ∈ (∂ F) x ∧ jacobianMatrixOfMap A = V := by
  rfl

#print axioms jacobianMatrixOfMap
#print axioms generalizedJacobian
#print axioms generalizedJacobianMatrix

end

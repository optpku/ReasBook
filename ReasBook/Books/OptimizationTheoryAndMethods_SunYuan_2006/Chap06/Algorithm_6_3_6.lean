/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.NthRoot.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Theorem_6_3_4

noncomputable section

-- Domain-style sampling for Algorithm 6.3.6:
-- * Primary domain: tensor-interpolation trial models and quadratic trust-region trial models on
--   `ℝ^n`.
-- * Sampled project owners in that domain:
--   `tensorGramInverseCombination`, `quarticTensorGramInverseCombination`,
--   `TrustRegionSubproblem`, `TrustRegionSubproblem.feasibleSet`, `hessianAt`, and
--   `hessianMatrixAt`.
-- * Best owner abstractions:
--   the Step `4` interpolation tensors belong to the Chapter 6 interpolation owners
--   `tensorGramInverseCombination` and `quarticTensorGramInverseCombination`, while the Step `6`
--   quadratic model belongs to the Chapter 6 owner `TrustRegionSubproblem`; the Hessian link is
--   the Chapter 3 owner `hessianAt`, and its Euclidean matrix surface is the upstream bridge/view
--   `hessianMatrixAt`.
-- * Primitive data for the transition are therefore the selected interpolation sites, their
--   interpolation right-hand sides, the canonical quadratic trust-region subproblem, the
--   gradient at `xc`, the Step `6` Hessian-matrix owner `HasHessianMatrixAt f xc`, and the
--   recorded Step `5`/`6` trial outputs. The tensors `Tc` and `Vc` are derived API, not
--   primitive stored fields.

section

variable {n p : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "Tensor3N" => ThirdOrderTensor n
local notation "Tensor4N" => _root_.Tensor4 n

/-- `HasHessianMatrixAt f x H` means that `H` is the Euclidean matrix representing the Hessian of
`f` at `x`, so `Matrix.toEuclideanCLM H` is the derivative of `gradient f` at `x`. -/
def HasHessianMatrixAt (f : Point → ℝ) (x : Point) (H : MatrixN) : Prop :=
  HasFDerivAt (gradient f)
    ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) H) x

namespace HasHessianMatrixAt

/-- A Hessian matrix witness makes `gradient f` differentiable at the base point. -/
theorem differentiableAt {f : Point → ℝ} {x : Point} {H : MatrixN}
    (h : HasHessianMatrixAt f x H) :
    DifferentiableAt ℝ (gradient f) x := by
  exact
    (show HasFDerivAt (gradient f)
      ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) H) x from h).differentiableAt

/-- A Hessian matrix witness agrees with the canonical Chapter 3 Hessian matrix owner
`hessianMatrixAt`. -/
theorem eq_hessianMatrixAt {f : Point → ℝ} {x : Point} {H : MatrixN}
    (h : HasHessianMatrixAt f x H) :
    H = hessianMatrixAt f x := by
  have hunique :
      ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) H) = hessianAt f x := by
    simpa [HasHessianMatrixAt, hessianAt] using
      (show HasFDerivAt (gradient f)
        ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) H) x from h).unique
        (h.differentiableAt.hasFDerivAt)
  rw [hessianMatrixAt]
  simpa using congrArg
    (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm hunique

/-- Converting the Hessian matrix witness back to a continuous linear map recovers the canonical
Hessian owner `hessianAt f x`. -/
theorem toEuclideanCLM_eq_hessianAt {f : Point → ℝ} {x : Point} {H : MatrixN}
    (h : HasHessianMatrixAt f x H) :
    ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) H) = hessianAt f x := by
  rw [h.eq_hessianMatrixAt]
  exact toEuclideanCLM_hessianMatrixAt f x

end HasHessianMatrixAt

/-- Chapter06 Algorithm 6.3.6: a single non-stopping tensor-method transition on `ℝ^n` from the
current state `xc`, together with the `Nat.nthRoot 3 n` most recent past points, to the Step
`7`-`8` update determined by Steps `3`-`6`. Step `3` selects `p` recent points; Step `4`
supplies the interpolation right-hand sides from which the chapter's canonical tensors `Tc` and
`Vc` are derived; Step `5` records the tensor-model trial data `dT` and `ΔT`; and Step `6`
records the canonical quadratic trust-region subproblem together with its source-facing gradient
and Hessian compatibility with `f` at `xc`, its trial step `dN`, and the updated radius `ΔN`.
The next iterate, next radius, and next objective value are then derived from this source-facing
data by the branch comparison in Step `7`. The selected interpolation family is stored through
its linear independence, and the distinctness of the selected indices is derived from that owner
data rather than stored separately. -/
structure TensorMethodTransition (n p : ℕ) where
  f : EuclideanSpace ℝ (Fin n) → ℝ
  xc : EuclideanSpace ℝ (Fin n)
  quadraticSubproblem : TrustRegionSubproblem n
  quadraticSubproblem_fAtCenter_eq : quadraticSubproblem.fAtCenter = f xc
  hasGradientAt : HasGradientAt f quadraticSubproblem.gradient xc
  hasHessianApproxAt : HasHessianMatrixAt f xc quadraticSubproblem.hessianApprox
  recentPastPoint : Fin (Nat.nthRoot 3 n) → EuclideanSpace ℝ (Fin n)
  selectedPastIndex : Fin p → Fin (Nat.nthRoot 3 n)
  selectedPastPoint_linearIndependent :
    LinearIndependent ℝ (fun i ↦ recentPastPoint (selectedPastIndex i))
  tensorInterpolationData : Fin p → EuclideanSpace ℝ (Fin n)
  quarticInterpolationData : EuclideanSpace ℝ (Fin p)
  dT : EuclideanSpace ℝ (Fin n)
  ΔT : ℝ
  dN : EuclideanSpace ℝ (Fin n)
  ΔN : ℝ
  tensorRadius_pos : 0 < ΔT
  quadraticRadius_pos : 0 < ΔN
  quadraticStep_feasible :
    dN ∈ (quadraticSubproblem.feasibleSet : Set (EuclideanSpace ℝ (Fin n)))

namespace TensorMethodTransition

/-- Step `6` records the exact gradient used by the quadratic trust-region subproblem. -/
theorem gradient_eq_quadraticSubproblem_gradient (A : TensorMethodTransition n p) :
    gradient A.f A.xc = A.quadraticSubproblem.gradient :=
  A.hasGradientAt.gradient

/-- Step `6` records that the trust-region Hessian matrix is a genuine Hessian matrix witness for
`f` at `xc`. -/
theorem hasHessianMatrixAt (A : TensorMethodTransition n p) :
    HasHessianMatrixAt A.f A.xc A.quadraticSubproblem.hessianApprox :=
  A.hasHessianApproxAt

/-- Step `6` identifies the trust-region Hessian matrix with the upstream Chapter 3 matrix bridge
`hessianMatrixAt`. -/
theorem hessianApprox_eq_hessianMatrixAt (A : TensorMethodTransition n p) :
    A.quadraticSubproblem.hessianApprox = hessianMatrixAt A.f A.xc :=
  A.hasHessianMatrixAt.eq_hessianMatrixAt

/-- Converting the Step `6` matrix identification back to a continuous linear map recovers the
canonical Hessian owner `hessianAt f xc`. -/
theorem hessianAt_eq_hessianApprox (A : TensorMethodTransition n p) :
    ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        A.quadraticSubproblem.hessianApprox) =
      hessianAt A.f A.xc := by
  exact A.hasHessianMatrixAt.toEuclideanCLM_eq_hessianAt

/-- Re-expressing the source-facing Hessian identification as a derivative statement recovers the
usual matrix-Hessian bridge for the Step `6` quadratic model. -/
theorem hasHessianAt (A : TensorMethodTransition n p) :
    HasFDerivAt (gradient A.f)
      (((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
        A.quadraticSubproblem.hessianApprox))
      A.xc := by
  exact A.hasHessianMatrixAt

/-- The `i`th selected past point is chosen from the `Nat.nthRoot 3 n` most recent past points by
the Step `3` selection map `selectedPastIndex`. -/
def selectedPastPoint (A : TensorMethodTransition n p) (i : Fin p) : Point :=
  A.recentPastPoint (A.selectedPastIndex i)

/-- Expanding `selectedPastPoint` shows that it is the recent past point at the selected index. -/
theorem selectedPastPoint_eq (A : TensorMethodTransition n p) (i : Fin p) :
    A.selectedPastPoint i = A.recentPastPoint (A.selectedPastIndex i) := rfl

/-- Step `3` chooses `p` pairwise distinct indices from the recent-point window. -/
theorem injective_selectedPastIndex (A : TensorMethodTransition n p) :
    Function.Injective A.selectedPastIndex := by
  intro i j hij
  apply A.selectedPastPoint_linearIndependent.injective
  simpa [selectedPastPoint_eq] using congrArg A.recentPastPoint hij

/-- Step `3` selects a linearly independent interpolation set from the recent-point window. -/
theorem linearIndependent_selectedPastPoint (A : TensorMethodTransition n p) :
    LinearIndependent ℝ A.selectedPastPoint := by
  change LinearIndependent ℝ (fun i ↦ A.recentPastPoint (A.selectedPastIndex i))
  exact A.selectedPastPoint_linearIndependent

/-- The Step `4` third-order interpolation tensor is the canonical least-norm interpolant attached
to the selected points and tensor interpolation data. -/
def Tc (A : TensorMethodTransition n p) : Tensor3N :=
  tensorGramInverseCombination A.selectedPastPoint A.tensorInterpolationData

/-- The Step `4` fourth-order interpolation tensor is the canonical least-norm interpolant
attached to the selected points and quartic interpolation data. -/
def Vc (A : TensorMethodTransition n p) : Tensor4N :=
  quarticTensorGramInverseCombination A.selectedPastPoint A.quarticInterpolationData

/-- The derived tensor `Tc` satisfies the interpolation conditions on the selected points. -/
theorem Tc_interpolates (A : TensorMethodTransition n p) :
    tensorLeastNormInterpolates A.selectedPastPoint A.tensorInterpolationData A.Tc :=
  tensorGramInverseCombination_interpolates A.selectedPastPoint A.tensorInterpolationData
    A.linearIndependent_selectedPastPoint

/-- The derived tensor `Tc` is a least-Frobenius-norm feasible tensor for the selected-point
interpolation problem. -/
theorem Tc_isMinOn_feasibleSet (A : TensorMethodTransition n p) :
    IsMinOn (fun T ↦ T.frobeniusNorm)
      (tensorLeastNormFeasibleSet A.selectedPastPoint A.tensorInterpolationData) A.Tc := by
  simpa [Tc] using
    tensorGramInverseCombination_isMinOn_feasibleSet A.selectedPastPoint A.tensorInterpolationData
      A.linearIndependent_selectedPastPoint

/-- The derived tensor `Vc` lies in the symmetric quartic interpolation feasible set attached to
the selected points. -/
theorem Vc_mem_feasibleSet (A : TensorMethodTransition n p) :
    A.Vc ∈ quarticTensorFeasibleSet A.selectedPastPoint A.quarticInterpolationData := by
  simpa [Vc] using
    quarticTensorGramInverseCombination_mem_feasibleSet A.selectedPastPoint
      A.quarticInterpolationData A.linearIndependent_selectedPastPoint

/-- The derived tensor `Vc` is a least-norm feasible tensor for the quartic interpolation
problem. -/
theorem Vc_isMinOn_feasibleSet (A : TensorMethodTransition n p) :
    IsMinOn (fun V ↦ V.frobeniusNorm)
      (quarticTensorFeasibleSet A.selectedPastPoint A.quarticInterpolationData) A.Vc := by
  simpa [Vc] using
    quarticTensorGramInverseCombination_isMinOn_feasibleSet A.selectedPastPoint
      A.quarticInterpolationData A.linearIndependent_selectedPastPoint

/-- Step `6` records a feasible trial step for the canonical quadratic trust-region subproblem. -/
theorem quadraticStep_mem_feasibleSet (A : TensorMethodTransition n p) :
    A.dN ∈ A.quadraticSubproblem.feasibleSet :=
  A.quadraticStep_feasible

/-- The Step `6` trial step satisfies the current trust-region bound from the canonical quadratic
subproblem. -/
theorem norm_dN_le_radius (A : TensorMethodTransition n p) :
    ‖A.dN‖ ≤ A.quadraticSubproblem.radius :=
  (TrustRegionSubproblem.mem_feasibleSet_iff A.quadraticSubproblem A.dN).1
    A.quadraticStep_feasible

/-- The tensor-model trial point from Step `5` is `xc + dT`. -/
def tensorTrialPoint (A : TensorMethodTransition n p) : Point :=
  A.xc + A.dT

/-- The quadratic-model trial point from Step `6` is `xc + dN`. -/
def quadraticTrialPoint (A : TensorMethodTransition n p) : Point :=
  A.xc + A.dN

/-- The Step `6` quadratic-model trial point lies in the translated trust region centered at the
current iterate `xc`. -/
theorem quadraticTrialPoint_mem_closedBall (A : TensorMethodTransition n p) :
    A.quadraticTrialPoint ∈ Metric.closedBall A.xc A.quadraticSubproblem.radius := by
  simpa [quadraticTrialPoint] using
    (TrustRegionSubproblem.center_add_mem_closedBall_iff
      A.quadraticSubproblem A.xc A.dN).2 A.quadraticStep_feasible

/-- Step `7` prefers the tensor-model trial data exactly when its trial value is no larger than
the quadratic-model trial value. -/
def tensorPreferred (A : TensorMethodTransition n p) : Prop :=
  A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint

/-- Step `7` chooses the next iterate by comparing the tensor-model and quadratic-model trial
objective values. -/
def xNext (A : TensorMethodTransition n p) : Point :=
  if A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint then
    A.tensorTrialPoint
  else
    A.quadraticTrialPoint

/-- Step `7` updates the next trust-region radius in parallel with the chosen trial point. -/
def ΔNext (A : TensorMethodTransition n p) : ℝ :=
  if A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint then
    A.ΔT
  else
    A.ΔN

/-- Step `8` records the objective value at the chosen next iterate. -/
def fNext (A : TensorMethodTransition n p) : ℝ :=
  A.f A.xNext

/-- Expanding `tensorPreferred` gives the Step `7` trial-value comparison. -/
theorem tensorPreferred_iff (A : TensorMethodTransition n p) :
    A.tensorPreferred ↔ A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint :=
  Iff.rfl

/-- Step `7` updates the next iterate by comparing the tensor-model and quadratic-model trial
objective values. -/
theorem xNext_eq_choose (A : TensorMethodTransition n p) :
    A.xNext =
      if A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint then
        A.tensorTrialPoint
      else
        A.quadraticTrialPoint :=
  rfl

/-- Step `7` updates the next trust-region radius in parallel with the chosen trial point. -/
theorem ΔNext_eq_choose (A : TensorMethodTransition n p) :
    A.ΔNext =
      if A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint then
        A.ΔT
      else
        A.ΔN :=
  rfl

/-- If the tensor-model trial value is no larger than the quadratic-model trial value, then Step
`7` keeps the tensor-model trial point. -/
theorem xNext_eq_tensorTrialPoint (A : TensorMethodTransition n p) (h : A.tensorPreferred) :
    A.xNext = A.tensorTrialPoint := by
  by_cases hchoose : A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint
  · simp [xNext, hchoose]
  · exact False.elim (hchoose h)

/-- If the tensor-model trial value is larger than the quadratic-model trial value, then Step `7`
keeps the quadratic-model trial point. -/
theorem xNext_eq_quadraticTrialPoint (A : TensorMethodTransition n p) (h : ¬A.tensorPreferred) :
    A.xNext = A.quadraticTrialPoint := by
  by_cases hchoose : A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint
  · exact False.elim (h hchoose)
  · simp [xNext, hchoose]

/-- If the tensor-model trial value is no larger than the quadratic-model trial value, then Step
`7` keeps the tensor-model trust-region radius. -/
theorem ΔNext_eq_tensorRadius (A : TensorMethodTransition n p) (h : A.tensorPreferred) :
    A.ΔNext = A.ΔT := by
  by_cases hchoose : A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint
  · simp [ΔNext, hchoose]
  · exact False.elim (hchoose h)

/-- If the tensor-model trial value is larger than the quadratic-model trial value, then Step `7`
keeps the quadratic-model trust-region radius. -/
theorem ΔNext_eq_quadraticRadius (A : TensorMethodTransition n p) (h : ¬A.tensorPreferred) :
    A.ΔNext = A.ΔN := by
  by_cases hchoose : A.f A.tensorTrialPoint ≤ A.f A.quadraticTrialPoint
  · exact False.elim (h hchoose)
  · simp [ΔNext, hchoose]

/-- Step `8` records the objective value at the chosen next iterate. -/
theorem fNext_eq_value (A : TensorMethodTransition n p) :
    A.fNext = A.f A.xNext := rfl

end TensorMethodTransition

end

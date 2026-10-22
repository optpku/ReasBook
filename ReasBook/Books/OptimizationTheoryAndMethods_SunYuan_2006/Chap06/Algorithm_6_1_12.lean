/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced only generic quadratic-form and `Matrix.PosDef`
-- APIs, not a dedicated Steihaug-CG or trust-region-subproblem owner. Nearby Chapter 6 precedent
-- formalizes optimization algorithms as explicit structures carrying their iterates and update
-- laws, so this file keeps the Steihaug-CG method on that concrete surface.

section

/-- The ambient Euclidean step space `ℝ^n` used for Steihaug-CG iterates. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ambient real `n × n` matrix type used for Hessian and preconditioner data. -/
abbrev MatrixN (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-- The scalar `xᵀ A x` appearing in the Steihaug-CG recurrences. -/
def matrixQuadratic (A : MatrixN n) (x : Point n) : ℝ :=
  dotProduct x (A.mulVec x)

/-- The `W`-norm `‖x‖_W = sqrt (xᵀ W x)` used by the Steihaug-CG algorithm. -/
def steihaugWeightedNorm (W : MatrixN n) (x : Point n) : ℝ :=
  Real.sqrt (matrixQuadratic W x)

/- The textbook weighted-norm notation `‖x‖_W` abbreviates `steihaugWeightedNorm W x`. -/
notation:100 "‖" x "‖_" W:max => steihaugWeightedNorm W x

/-- The preconditioned residual pairing `gᵀ v` used by Steihaug-CG. -/
def steihaugResidualPairing (g v : Point n) : ℝ :=
  dotProduct g v

/-- The preconditioned residual norm `sqrt (gᵀ v)` used in the Steihaug-CG stopping test. -/
def steihaugResidualNorm (g v : Point n) : ℝ :=
  Real.sqrt (steihaugResidualPairing g v)

/-- The source quantity `g_jᵀ v_j` at iteration `j`. -/
def steihaugResidualPairingAt
    (gradient preconditionedGradient : ℕ → Point n) (j : ℕ) : ℝ :=
  steihaugResidualPairing (gradient j) (preconditionedGradient j)

/-- The source residual norm `sqrt (g_jᵀ v_j)` at iteration `j`. -/
def steihaugResidualNormAt
    (gradient preconditionedGradient : ℕ → Point n) (j : ℕ) : ℝ :=
  steihaugResidualNorm (gradient j) (preconditionedGradient j)

/-- The initial Steihaug-CG residual norm `sqrt (g₀ᵀ v₀)`. -/
def steihaugInitialResidualNorm
    (gradient preconditionedGradient : ℕ → Point n) : ℝ :=
  steihaugResidualNormAt gradient preconditionedGradient 0

/-- The source residual threshold `ε * sqrt (g₀ᵀ v₀)` used by the stopping test. -/
def steihaugResidualThreshold
    (ε : ℝ) (gradient preconditionedGradient : ℕ → Point n) : ℝ :=
  ε * steihaugInitialResidualNorm gradient preconditionedGradient

#print axioms matrixQuadratic
#print axioms steihaugWeightedNorm
#print axioms steihaugResidualPairing
#print axioms steihaugResidualNorm
#print axioms steihaugResidualPairingAt
#print axioms steihaugResidualNormAt
#print axioms steihaugInitialResidualNorm
#print axioms steihaugResidualThreshold

/-- Chapter06 Algorithm 6.1.12: a Steihaug-CG algorithm for the trust-region subproblem.
The owner stores explicit Step `0` data, both boundary exits, the Step `2`-`4` recurrences,
loop-entry obligations, control-flow obligations, plus the returned step. The predicate
`activeIteration j` means that iteration `j` has been reached. The predicate
`continuingIteration j` means that iteration `j` enters Step `2` after the Step `1`
negative-curvature test. -/
structure SteihaugCGAlgorithm (n : ℕ) where
  initialGradient : Point n
  hessianApprox : MatrixN n
  weightMatrix : MatrixN n
  weightMatrixInv : MatrixN n
  ε : ℝ
  Δ : ℝ
  step : ℕ → Point n
  gradient : ℕ → Point n
  preconditionedGradient : ℕ → Point n
  searchDirection : ℕ → Point n
  α : ℕ → ℝ
  β : ℕ → ℝ
  τNegCurvature : ℕ → ℝ
  τBoundary : ℕ → ℝ
  returnedStep : Point n
  epsilonPos : 0 < ε
  radiusPos : 0 < Δ
  weightMatrixPosDef : weightMatrix.PosDef
  weightMatrixMulInv : weightMatrix * weightMatrixInv = 1
  weightMatrixInvMul : weightMatrixInv * weightMatrix = 1
  stepZero : step 0 = 0
  gradientZero : gradient 0 = initialGradient
  preconditionedGradientZero :
    preconditionedGradient 0 = weightMatrixInv.mulVec (gradient 0)
  searchDirectionZero : searchDirection 0 = -preconditionedGradient 0
  initialStop :
    steihaugInitialResidualNorm gradient preconditionedGradient <
        steihaugResidualThreshold ε gradient preconditionedGradient →
      returnedStep = step 0
  activeIteration : ℕ → Prop
  continuingIteration : ℕ → Prop
  loopEntry :
    steihaugResidualThreshold ε gradient preconditionedGradient ≤
        steihaugInitialResidualNorm gradient preconditionedGradient →
      activeIteration 0
  continuingIteration_active :
    ∀ j : ℕ, continuingIteration j → activeIteration j
  activeIteration_branch :
    ∀ j : ℕ, activeIteration j →
      matrixQuadratic hessianApprox (searchDirection j) ≤ 0 ∨ continuingIteration j
  negativeCurvatureTauPos :
    ∀ j : ℕ, activeIteration j → matrixQuadratic hessianApprox (searchDirection j) ≤ 0 →
      0 < τNegCurvature j
  negativeCurvatureBoundary :
    ∀ j : ℕ, activeIteration j → matrixQuadratic hessianApprox (searchDirection j) ≤ 0 →
      ‖step j + τNegCurvature j • searchDirection j‖_weightMatrix = Δ
  negativeCurvatureReturnedStep :
    ∀ j : ℕ, activeIteration j → matrixQuadratic hessianApprox (searchDirection j) ≤ 0 →
      returnedStep = step j + τNegCurvature j • searchDirection j
  continuingCurvaturePos :
    ∀ j : ℕ, continuingIteration j →
      0 < matrixQuadratic hessianApprox (searchDirection j)
  alphaUpdate :
    ∀ j : ℕ, continuingIteration j →
      α j =
        steihaugResidualPairingAt gradient preconditionedGradient j /
          matrixQuadratic hessianApprox (searchDirection j)
  stepUpdate :
    ∀ j : ℕ, continuingIteration j → step (j + 1) = step j + α j • searchDirection j
  boundaryTauPos :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix ≥ Δ →
      0 < τBoundary j
  boundaryOnSphere :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix ≥ Δ →
      ‖step j + τBoundary j • searchDirection j‖_weightMatrix = Δ
  boundaryReturnedStep :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix ≥ Δ →
      returnedStep = step j + τBoundary j • searchDirection j
  gradientUpdate :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      gradient (j + 1) = gradient j + α j • hessianApprox.mulVec (searchDirection j)
  preconditionedGradientUpdate :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      preconditionedGradient (j + 1) = weightMatrixInv.mulVec (gradient (j + 1))
  residualStop :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      steihaugResidualNormAt gradient preconditionedGradient (j + 1) <
          steihaugResidualThreshold ε gradient preconditionedGradient →
        returnedStep = step (j + 1)
  betaDenominatorNeZero :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      steihaugResidualThreshold ε gradient preconditionedGradient ≤
          steihaugResidualNormAt gradient preconditionedGradient (j + 1) →
      steihaugResidualPairingAt gradient preconditionedGradient j ≠ 0
  betaUpdate :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      steihaugResidualThreshold ε gradient preconditionedGradient ≤
          steihaugResidualNormAt gradient preconditionedGradient (j + 1) →
      β j =
        steihaugResidualPairingAt gradient preconditionedGradient (j + 1) /
          steihaugResidualPairingAt gradient preconditionedGradient j
  searchDirectionUpdate :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      steihaugResidualThreshold ε gradient preconditionedGradient ≤
          steihaugResidualNormAt gradient preconditionedGradient (j + 1) →
      searchDirection (j + 1) = -preconditionedGradient (j + 1) + β j • searchDirection j
  nextIterationActive :
    ∀ j : ℕ, continuingIteration j →
      ‖step (j + 1)‖_weightMatrix < Δ →
      steihaugResidualThreshold ε gradient preconditionedGradient ≤
          steihaugResidualNormAt gradient preconditionedGradient (j + 1) →
      activeIteration (j + 1)

/-- The source quantity `g_jᵀ v_j` governing the Steihaug-CG residual test and `β`-update. -/
abbrev SteihaugCGAlgorithm.residualPairing (A : SteihaugCGAlgorithm n) (j : ℕ) : ℝ :=
  steihaugResidualPairingAt A.gradient A.preconditionedGradient j

/-- The source residual norm `sqrt (g_jᵀ v_j)` at iteration `j`. -/
abbrev SteihaugCGAlgorithm.residualNorm (A : SteihaugCGAlgorithm n) (j : ℕ) : ℝ :=
  steihaugResidualNormAt A.gradient A.preconditionedGradient j

/-- The initial Steihaug-CG residual norm `sqrt (g₀ᵀ v₀)`. -/
abbrev SteihaugCGAlgorithm.initialResidualNorm (A : SteihaugCGAlgorithm n) : ℝ :=
  steihaugInitialResidualNorm A.gradient A.preconditionedGradient

/-- The weighted trust-region norm `‖s‖_W` attached to a Steihaug-CG run. -/
abbrev SteihaugCGAlgorithm.weightedNorm (A : SteihaugCGAlgorithm n) (s : Point n) : ℝ :=
  ‖s‖_A.weightMatrix

/-- The source residual threshold `ε * sqrt (g₀ᵀ v₀)` used by Step `4`. -/
abbrev SteihaugCGAlgorithm.residualThreshold (A : SteihaugCGAlgorithm n) : ℝ :=
  steihaugResidualThreshold A.ε A.gradient A.preconditionedGradient

/-- On a continuing Steihaug-CG iteration, Step `2` computes
`s_(j + 1) = s_j + α_j d_j`. -/
theorem SteihaugCGAlgorithm.step_next_eq (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j) :
    A.step (j + 1) = A.step j + A.α j • A.searchDirection j :=
  A.stepUpdate j hContinue

/-- On a continuing Steihaug-CG iteration that stays inside the trust region, Step `3` computes
`g_(j+1) = g_j + α_j B d_j`. -/
theorem SteihaugCGAlgorithm.gradient_next_eq (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j)
    (hInterior : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ) :
    A.gradient (j + 1) = A.gradient j + A.α j • A.hessianApprox.mulVec (A.searchDirection j) :=
  A.gradientUpdate j hContinue hInterior

/-- On a continuing Steihaug-CG iteration that stays inside the trust region, Step `4` computes
`v_(j+1) = W⁻¹ g_(j+1)`. -/
theorem SteihaugCGAlgorithm.preconditionedGradient_next_eq (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j)
    (hInterior : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ) :
    A.preconditionedGradient (j + 1) = A.weightMatrixInv.mulVec (A.gradient (j + 1)) :=
  A.preconditionedGradientUpdate j hContinue hInterior

/-- On a continuing Steihaug-CG iteration that stays inside the trust region and does not satisfy
the residual stopping test, Step `4` updates the next search direction by
`d_(j+1) = -v_(j+1) + β_j d_j`. -/
theorem SteihaugCGAlgorithm.searchDirection_next_eq (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j)
    (hInterior : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : A.residualThreshold ≤ A.residualNorm (j + 1)) :
    A.searchDirection (j + 1) =
      -A.preconditionedGradient (j + 1) + A.β j • A.searchDirection j :=
  A.searchDirectionUpdate j hContinue hInterior hResidual

/-- The quadratic model `q(s) = f + g₀ᵀ s + (1 / 2) sᵀ B s` attached to a Steihaug-CG run,
with explicit constant term `f`. -/
def SteihaugCGAlgorithm.quadraticModel (A : SteihaugCGAlgorithm n) (f : ℝ) (s : Point n) : ℝ :=
  f + dotProduct A.initialGradient s + (1 / 2 : ℝ) * matrixQuadratic A.hessianApprox s

#print axioms SteihaugCGAlgorithm.quadraticModel

/-- A Steihaug-CG algorithm can be used as its sequence of trial steps `s_j`. -/
instance {n : ℕ} :
    CoeFun (SteihaugCGAlgorithm n) (fun _ ↦ ℕ → Point n) where
  coe A := A.step

end

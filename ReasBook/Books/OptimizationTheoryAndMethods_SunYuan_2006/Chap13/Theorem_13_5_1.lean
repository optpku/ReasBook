/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix

noncomputable section

-- Semantic recall: the source-facing CDT owner in this file is the pair "feasible and globally
-- minimizing", built from the explicit quadratic model, feasible set, and multiplier conditions
-- on the canonical Euclidean `ℓ2` model `EuclideanSpace ℝ (Fin _)` and the standard matrix
-- surface.

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin n) (Fin m) ℝ

/-- The CDT quadratic model `d ↦ ⟪g, d⟫ + (1 / 2) ⟪d, B d⟫` from `(13.5.1)`. -/
def cdtObjective (B : MatrixN) (g : StepVector) (d : StepVector) : ℝ :=
  inner ℝ g d + ((1 : ℝ) / 2) * inner ℝ d (Matrix.toEuclideanLin B d)

/-- The affine linearized constraint residual `c + Aᵀ d` from `(13.5.3)`. -/
def cdtConstraintResidual
    (c : ConstraintVector) (A : JacobianMatrix) (d : StepVector) : ConstraintVector :=
  c + Matrix.toEuclideanLin A.transpose d

/-- The feasible set of the CDT subproblem is given by the trust-region bound `‖d‖ ≤ Δ` and
the linearized-constraint bound `‖c + Aᵀ d‖ ≤ ξ`, both on the Euclidean `ℓ2` surface. -/
def cdtFeasibleSet
    (Δ ξ : ℝ) (c : ConstraintVector) (A : JacobianMatrix) : Set StepVector :=
  {d | ‖d‖ ≤ Δ ∧ ‖cdtConstraintResidual c A d‖ ≤ ξ}

/-- Membership in `cdtFeasibleSet Δ ξ c A` is exactly the pair of source norm constraints. -/
theorem mem_cdtFeasibleSet_iff
    (Δ ξ : ℝ) (c : ConstraintVector) (A : JacobianMatrix) (d : StepVector) :
    d ∈ cdtFeasibleSet Δ ξ c A ↔ ‖d‖ ≤ Δ ∧ ‖cdtConstraintResidual c A d‖ ≤ ξ := Iff.rfl

/-- A step solves the CDT subproblem when it is feasible and minimizes the CDT quadratic model on
the feasible set. This is the source-facing solution owner, built from the canonical mathlib
predicate `IsMinOn`. -/
def IsCdtSolution
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) (d : StepVector) : Prop :=
  d ∈ cdtFeasibleSet Δ ξ c A ∧ IsMinOn (cdtObjective B g) (cdtFeasibleSet Δ ξ c A) d

/-- Unfolding `IsCdtSolution B g A c Δ ξ d` gives feasibility together with global minimization of
the CDT quadratic model on the feasible set. -/
theorem isCdtSolution_iff_mem_cdtFeasibleSet_and_isMinOn
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) (d : StepVector) :
    IsCdtSolution B g A c Δ ξ d ↔
      d ∈ cdtFeasibleSet Δ ξ c A ∧
        IsMinOn (cdtObjective B g) (cdtFeasibleSet Δ ξ c A) d :=
  Iff.rfl

/-- The set of linearized-constraint norms attained on the trust region `‖d‖ ≤ Δ`. -/
def cdtResidualNormValues
    (Δ : ℝ) (c : ConstraintVector) (A : JacobianMatrix) : Set ℝ :=
  {t | ∃ d : StepVector, ‖d‖ ≤ Δ ∧ ‖cdtConstraintResidual c A d‖ = t}

/-- The threshold `ξ_min` from `(13.5.10)`, formalized as the infimum of attained residual
norms `‖c + Aᵀ d‖` over the trust region `‖d‖ ≤ Δ`. -/
def cdtXiMin (Δ : ℝ) (c : ConstraintVector) (A : JacobianMatrix) : ℝ :=
  sInf (cdtResidualNormValues Δ c A)

/-- The shifted matrix `H(λ, μ) = B + λ I + μ A Aᵀ` from `(13.5.14)`. -/
def cdtShiftedHessian
    (B : MatrixN) (A : JacobianMatrix) (lambdaStar muStar : ℝ) : MatrixN :=
  B + lambdaStar • (1 : MatrixN) + muStar • (A * A.transpose)

/-- The matrix `H(λ, μ) = B + λ I + μ A Aᵀ` is symmetric whenever `B` is symmetric. -/
theorem cdtShiftedHessian_isSymm
    {B : MatrixN} (hB : B.IsSymm) (A : JacobianMatrix) (lambdaStar muStar : ℝ) :
    (cdtShiftedHessian B A lambdaStar muStar).IsSymm := by
  have hI : (1 : MatrixN).IsSymm := Matrix.isSymm_one
  have hAAT : (A * A.transpose).IsSymm := by
    change (A * A.transpose)ᵀ = A * A.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa [cdtShiftedHessian, add_assoc] using
    (hB.add (hI.smul lambdaStar)).add (hAAT.smul muStar)

/-- The matrix `H(λ, μ) = B + λ I + μ A Aᵀ` is Hermitian over `ℝ` whenever `B` is symmetric. -/
theorem cdtShiftedHessian_isHermitian
    {B : MatrixN} (hB : B.IsSymm) (A : JacobianMatrix) (lambdaStar muStar : ℝ) :
    (cdtShiftedHessian B A lambdaStar muStar).IsHermitian :=
  (Matrix.isHermitian_iff_isSymm).2 (cdtShiftedHessian_isSymm hB A lambdaStar muStar)

/-- An optimality pair `(λ, μ)` for a CDT solution `dStar` satisfies the source nonnegativity,
stationarity, and complementarity conditions `(13.5.11)`-`(13.5.13)`. -/
class IsCdtOptimalityPair
    (B : MatrixN) (g : StepVector) (A : JacobianMatrix) (c : ConstraintVector)
    (Δ ξ : ℝ) (dStar : StepVector) (lambdaStar muStar : ℝ) : Prop where
  lambda_nonneg : 0 ≤ lambdaStar
  mu_nonneg : 0 ≤ muStar
  stationarity :
    Matrix.toEuclideanLin (cdtShiftedHessian B A lambdaStar muStar) dStar =
      -(g + muStar • Matrix.toEuclideanLin A c)
  trustRegionComplementarity : lambdaStar * (Δ - ‖dStar‖) = 0
  residualComplementarity :
    muStar * (ξ - ‖cdtConstraintResidual c A dStar‖) = 0

namespace Matrix

/-- A real square matrix has at most one negative eigenvalue when it is Hermitian and no two
distinct ordered Hermitian eigenvalue indices carry negative values. -/
def HasAtMostOneNegativeEigenvalue (H : MatrixN) : Prop :=
  ∃ hH : H.IsHermitian,
    ∀ i j : Fin n, i ≠ j →
      ¬ (hH.eigenvalues i < 0 ∧ hH.eigenvalues j < 0)

/-- Bridge/view expansion of `H.HasAtMostOneNegativeEigenvalue` along a chosen Hermitian witness. -/
theorem hasAtMostOneNegativeEigenvalue_iff
    {H : MatrixN} (hH : H.IsHermitian) :
    H.HasAtMostOneNegativeEigenvalue ↔
      ∀ i j : Fin n, i ≠ j → ¬ (hH.eigenvalues i < 0 ∧ hH.eigenvalues j < 0) := by
  constructor
  · intro hAtMostOne i j hij
    rcases hAtMostOne with ⟨hH', hAtMostOne⟩
    have hh : hH' = hH := Subsingleton.elim _ _
    subst hh
    exact hAtMostOne i j hij
  · intro hAtMostOne
    exact ⟨hH, hAtMostOne⟩

end Matrix

/-- Chapter13 Theorem 13.5.1 (1): let `dStar` be a global solution of the CDT subproblem
`min cdtObjective B g d` on `cdtFeasibleSet Δ ξ c A`. Under the source assumption `(13.5.10)`,
formalized here as `cdtXiMin Δ c A < ξ`, there exist nonnegative multipliers `lambdaStar` and
`muStar` satisfying the stationarity equation
`(B + lambdaStar I + muStar A Aᵀ) dStar = -(g + muStar A c)` and the complementarity relations
`lambdaStar * (Δ - ‖dStar‖) = 0` and
`muStar * (ξ - ‖cdtConstraintResidual c A dStar‖) = 0`. -/
theorem existsCdtOptimalityMultipliers
    {B : MatrixN} {g : StepVector} {A : JacobianMatrix} {c : ConstraintVector}
    {Δ ξ : ℝ} {dStar : StepVector} (hB : B.IsSymm)
    (hConstraintQualification : cdtXiMin Δ c A < ξ)
    (hSolution : IsCdtSolution B g A c Δ ξ dStar) :
    ∃ lambdaStar muStar : ℝ, IsCdtOptimalityPair B g A c Δ ξ dStar lambdaStar muStar := sorry

/-- Chapter13 Theorem 13.5.1 (2): under the same CDT subproblem hypotheses as in `(1)`, if the
optimality multipliers `lambdaStar` and `muStar` are unique, then the shifted matrix
`H(lambdaStar, muStar) = B + lambdaStar I + muStar A Aᵀ` has at most one negative eigenvalue. -/
theorem cdtShiftedHessianHasAtMostOneNegativeEigenvalue_of_uniqueMultipliers
    {B : MatrixN} {g : StepVector} {A : JacobianMatrix} {c : ConstraintVector}
    {Δ ξ : ℝ} {dStar : StepVector} {lambdaStar muStar : ℝ} (hB : B.IsSymm)
    (hConstraintQualification : cdtXiMin Δ c A < ξ)
    (hSolution : IsCdtSolution B g A c Δ ξ dStar)
    (hOptimality : IsCdtOptimalityPair B g A c Δ ξ dStar lambdaStar muStar)
    (hUnique :
      ∀ {lambda mu},
        IsCdtOptimalityPair B g A c Δ ξ dStar lambda mu →
          lambda = lambdaStar ∧ mu = muStar) :
    (cdtShiftedHessian B A lambdaStar muStar).HasAtMostOneNegativeEigenvalue := sorry

end

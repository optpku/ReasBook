/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Diagonal
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_10

open Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` did not surface a dedicated Moré-type
-- Levenberg-Marquardt owner. Nearby Chapter 7 files package these methods as explicit
-- matrix/Euclidean-space iteration structures, so this item follows that local API.

/-- The Gauss-Newton pseudoinverse step `-J⁺ r`, equivalently the canonical least-squares
solution of `J s = -r`. -/
def morePseudoinverseStep (J : JacobianMatrix) (r : ResidualVector) : Point :=
  Matrix.pseudoinverseMulVec J (-r)

/-- The diagonal scaling matrix `D = diag d` used in Moré's scaled trust-region norm. -/
def moreScalingMatrix (d : Fin n → ℝ) : MatrixN :=
  Matrix.diagonal d

/-- Moré's diagonal scaling matrix is positive definite diagonal exactly when its diagonal data
are strictly positive. -/
theorem moreScalingMatrix_isPositiveDefiniteDiagonal_iff
    (d : Fin n → ℝ) :
    IsPositiveDefiniteDiagonalMatrix (moreScalingMatrix d) ↔ ∀ i : Fin n, 0 < d i := by
  constructor
  · intro hD
    rcases hD with ⟨d', hd', hd'pos⟩
    have hd : d = d' := Matrix.diagonal_injective <| by
      simpa [moreScalingMatrix] using hd'
    simpa [hd] using hd'pos
  · intro hd
    exact ⟨d, by simp [moreScalingMatrix], hd⟩

/-- The scaled trust-region norm `‖D s‖` with `D = diag d`. -/
def moreScaledStepNorm (d : Fin n → ℝ) (s : Point) : ℝ :=
  ‖Matrix.toEuclideanLin (moreScalingMatrix d) s‖

/-- The Euclidean norm of the `j`th Jacobian column. -/
def moreJacobianColumnNorm (J : JacobianMatrix) (j : Fin n) : ℝ :=
  ‖fun i : Fin m ↦ J i j‖

/-- Moré's diagonal scaling update from `(7.4.24)`, taking componentwise maxima of the current
diagonal data with the next Jacobian column norms. -/
def moreScalingUpdate (d : Fin n → ℝ) (JNext : JacobianMatrix) : Fin n → ℝ :=
  fun j ↦ max (d j) (moreJacobianColumnNorm JNext j)

/-- Moré's scaling update preserves the Chapter 7 positive-definite diagonal scaling condition. -/
theorem moreScalingUpdate_isPositiveDefiniteDiagonal
    {d : Fin n → ℝ} {JNext : JacobianMatrix}
    (hD : IsPositiveDefiniteDiagonalMatrix (moreScalingMatrix d)) :
    IsPositiveDefiniteDiagonalMatrix (moreScalingMatrix (moreScalingUpdate d JNext)) := by
  rw [moreScalingMatrix_isPositiveDefiniteDiagonal_iff] at hD ⊢
  intro j
  exact lt_of_lt_of_le (hD j) (le_max_left _ _)

/-- The stacked matrix `[J; √μ D]` used in Moré's damped least-squares subproblem. -/
def moreDampedLeastSquaresMatrix
    (J : JacobianMatrix) (d : Fin n → ℝ) (μ : ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ :=
  Matrix.fromRows J (Real.sqrt μ • moreScalingMatrix d)

/-- The stacked offset vector `[r; 0]` used when rewriting
`[J; √μ D] s ≈ -[r; 0]` as a residual minimization problem. -/
def moreDampedLeastSquaresOffset (r : ResidualVector) : EuclideanSpace ℝ (Fin m ⊕ Fin n) :=
  (EuclideanSpace.equiv (Fin m ⊕ Fin n) ℝ).symm
    (Sum.elim ((EuclideanSpace.equiv (Fin m) ℝ) r) 0)

/-- The squared residual of Moré's stacked least-squares problem
`[J; √μ D] s ≈ -[r; 0]`. -/
def moreDampedLeastSquaresObjective
    (J : JacobianMatrix) (r : ResidualVector) (d : Fin n → ℝ) (μ : ℝ) (s : Point) : ℝ :=
  ‖Matrix.toEuclideanLin (moreDampedLeastSquaresMatrix J d μ) s +
      moreDampedLeastSquaresOffset r‖ ^ (2 : ℕ)

/-- A step `s` is a Moré damped least-squares step when it minimizes the squared stacked residual
for `[J; √μ D] s ≈ -[r; 0]`. -/
def IsMoreDampedLeastSquaresStep
    (J : JacobianMatrix) (r : ResidualVector) (d : Fin n → ℝ) (μ : ℝ) (s : Point) : Prop :=
  IsMinOn (moreDampedLeastSquaresObjective J r d μ) Set.univ s

/-- The nonlinear least-squares objective `x ↦ (1 / 2) * ‖r x‖²`. -/
abbrev moreLeastSquaresObjective (r : Point → ResidualVector) : Point → ℝ :=
  nonlinearLeastSquaresObjective r

/-- The predicted reduction
`(1 / 2) * (‖r_k‖² - ‖J_k s_k + r_k‖²)` from the linearized least-squares model. -/
abbrev morePredictedReduction
    (J : JacobianMatrix) (rk : ResidualVector) (step : Point) : ℝ :=
  trustRegionLevenbergMarquardtPredictedReduction J rk step

/-- The actual-to-predicted reduction ratio used in Moré's trust-region update. -/
abbrev moreReductionRatio
    (r : Point → ResidualVector) (J : JacobianMatrix) (xk step : Point) : ℝ :=
  trustRegionLevenbergMarquardtReductionRatio r J xk step

/-- The damped-step branch in Moré's Levenberg-Marquardt update: positive damping, a minimizer
of the stacked least-squares problem, plus the lower and upper scaled trust-region bounds. -/
structure MoreLevenbergMarquardtDampedStep
    (J : JacobianMatrix) (r : ResidualVector) (d : Fin n → ℝ)
    (sigma Δ : ℝ) (mu : ℝ) (step : Point) : Prop where
  mu_pos : 0 < mu
  isMin : IsMoreDampedLeastSquaresStep J r d mu step
  lower_bound : (1 - sigma) * Δ ≤ moreScaledStepNorm d step
  upper_bound : moreScaledStepNorm d step ≤ (1 + sigma) * Δ

/-- The radius-expansion trigger in Moré's update: either `1 / 4 ≤ ρ ≤ 1 / 3` with `μ = 0`, or
`3 / 4 ≤ ρ`. -/
inductive MoreLevenbergMarquardtExpansionTrigger (rho mu : ℝ) : Prop
  | of_midrange_zero
      (quarter_le : (1 / 4 : ℝ) ≤ rho)
      (le_third : rho ≤ (1 / 3 : ℝ))
      (mu_eq_zero : mu = 0)
  | of_large_ratio
      (threeQuarters_le : (3 / 4 : ℝ) ≤ rho)

/-- Chapter07 Algorithm 7.4.2: a Moré Levenberg-Marquardt iteration at `x_k` with trust-region
radius `Δ_k`, strictly positive diagonal scaling data `d_k`, parameter `σ ∈ (0, 1)`, damping
value `μ_k`, step `s_k`, ratio `ρ_k`, next iterate `x_(k + 1)`, next Jacobian `J_(k + 1)`,
next trust-region radius `Δ_(k + 1)`, next diagonal scaling data `d_(k + 1)`. If the scaled
Gauss-Newton
pseudoinverse step satisfies
`moreScaledStepNorm d_k (morePseudoinverseStep (J x_k) (r x_k)) ≤ (1 + σ) * Δ_k`, then `μ_k = 0`
with `s_k` equal to that pseudoinverse step; otherwise `μ_k > 0`, `s_k` minimizes the stacked
least-squares problem `[J_k; √μ_k D_k] s ≈ -[r_k; 0]`, with
`(1 - σ) * Δ_k ≤ moreScaledStepNorm d_k s_k` plus
`moreScaledStepNorm d_k s_k ≤ (1 + σ) * Δ_k`. The predicted reduction in the ratio `ρ_k` is
assumed positive so that `ρ_k` is the genuine actual-to-predicted reduction quotient for the
nonlinear least-squares objective. The iterate/Jacobian update follows
the threshold `ρ_k ≤ 1 / 10000`. The radius update uses the source `1 / 4`, `1 / 3`, `3 / 4`
branches. The current scaling matrix `diag d_k` is positive definite diagonal, and the next
scaling data satisfy `d_(k + 1) = max(d_k, columnNorms J_(k + 1))`, matching `(7.4.24)`. -/
structure MoreLevenbergMarquardtIteration
    (r : Point → ResidualVector) (J : Point → JacobianMatrix)
    (xk : Point) (Δk : ℝ) (dk : Fin n → ℝ) where
  sigma : ℝ
  mu : ℝ
  step : Point
  rho : ℝ
  xNext : Point
  jacobianNext : JacobianMatrix
  deltaNext : ℝ
  scalingNext : Fin n → ℝ
  sigma_mem_Ioo : sigma ∈ Set.Ioo 0 1
  delta_pos : 0 < Δk
  scalingMatrix_posDef :
    IsPositiveDefiniteDiagonalMatrix (moreScalingMatrix dk)
  step_case :
    if moreScaledStepNorm dk (morePseudoinverseStep (J xk) (r xk)) ≤ (1 + sigma) * Δk then
      mu = 0 ∧ step = morePseudoinverseStep (J xk) (r xk)
    else
      MoreLevenbergMarquardtDampedStep (J xk) (r xk) dk sigma Δk mu step
  predictedReduction_pos :
    0 < morePredictedReduction (J xk) (r xk) step
  rho_eq :
    rho =
      TrustRegionSubproblem.actualReduction xk (nonlinearLeastSquaresObjective r) step /
        morePredictedReduction (J xk) (r xk) step
  xNext_eq_of_small_ratio :
    rho ≤ (1 / 10000 : ℝ) → xNext = xk
  jacobianNext_eq_of_small_ratio :
    rho ≤ (1 / 10000 : ℝ) → jacobianNext = J xk
  xNext_eq_of_large_ratio :
    (1 / 10000 : ℝ) < rho → xNext = xk + step
  jacobianNext_eq_of_large_ratio :
    (1 / 10000 : ℝ) < rho → jacobianNext = J (xk + step)
  deltaNext_mem_of_ratio_le_quarter :
    rho ≤ (1 / 4 : ℝ) →
      deltaNext ∈ Set.Icc (((1 : ℝ) / 10) * Δk) (((1 : ℝ) / 2) * Δk)
  deltaNext_eq_of_expansion :
    MoreLevenbergMarquardtExpansionTrigger rho mu →
      deltaNext = 2 * moreScaledStepNorm dk step
  scalingNext_eq :
    scalingNext = moreScalingUpdate dk jacobianNext

/-- A Moré Levenberg-Marquardt iteration coerces to its next iterate `x_(k + 1)`. -/
instance moreLevenbergMarquardtIterationCoe
    (r : Point → ResidualVector) (J : Point → JacobianMatrix)
    (xk : Point) (Δk : ℝ) (dk : Fin n → ℝ) :
    CoeOut (MoreLevenbergMarquardtIteration r J xk Δk dk) Point where
  coe iter := iter.xNext

/-- The current diagonal scaling matrix `D_k = diag d_k` used by a Moré iteration. -/
def MoreLevenbergMarquardtIteration.currentScalingMatrix
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    {xk : Point} {Δk : ℝ} {dk : Fin n → ℝ}
    (_ : MoreLevenbergMarquardtIteration r J xk Δk dk) : MatrixN :=
  moreScalingMatrix dk

/-- The current scaling matrix `D_k = diag d_k` satisfies the Chapter 7 positive-definite
diagonal condition. -/
theorem MoreLevenbergMarquardtIteration.currentScalingMatrix_posDef
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    {xk : Point} {Δk : ℝ} {dk : Fin n → ℝ}
    (iter : MoreLevenbergMarquardtIteration r J xk Δk dk) :
    IsPositiveDefiniteDiagonalMatrix iter.currentScalingMatrix :=
  iter.scalingMatrix_posDef

/-- The next scaling matrix `D_(k + 1) = diag d_(k + 1)` produced by a Moré iteration. -/
def MoreLevenbergMarquardtIteration.nextScalingMatrix
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    {xk : Point} {Δk : ℝ} {dk : Fin n → ℝ}
    (iter : MoreLevenbergMarquardtIteration r J xk Δk dk) : MatrixN :=
  moreScalingMatrix iter.scalingNext

/-- The scaling update preserves the Chapter 7 positive-definite diagonal condition. -/
theorem MoreLevenbergMarquardtIteration.nextScalingMatrix_posDef
    {r : Point → ResidualVector} {J : Point → JacobianMatrix}
    {xk : Point} {Δk : ℝ} {dk : Fin n → ℝ}
    (iter : MoreLevenbergMarquardtIteration r J xk Δk dk) :
    IsPositiveDefiniteDiagonalMatrix iter.nextScalingMatrix := by
  simpa [MoreLevenbergMarquardtIteration.nextScalingMatrix, iter.scalingNext_eq] using
    moreScalingUpdate_isPositiveDefiniteDiagonal
      (d := dk) (JNext := iter.jacobianNext) iter.scalingMatrix_posDef

end

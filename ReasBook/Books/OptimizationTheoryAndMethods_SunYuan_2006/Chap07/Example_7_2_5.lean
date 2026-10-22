/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Order.IntermediateValue

open Asymptotics
open scoped Topology

-- Domain sampling:
-- * primary domain: one-dimensional nonlinear least-squares Gauss-Newton updates;
-- * sampled owner declarations reused here:
--   `nonlinearLeastSquaresObjective`,
--   `solvesGaussNewtonNormalEquation`,
--   `Function.iterate`,
--   `Function.IsFixedPt`;
-- * core/canonical owner for the update semantics:
--   `solvesGaussNewtonNormalEquation (example725ResidualMap lam)`;
-- * primitive data kept here: the example residual map and its explicit point-level
--   Gauss-Newton update;
-- * derived API here: scalar-coordinate views, the objective formula, and orbit views.

noncomputable section

/-- The one-dimensional Euclidean ambient space used for Example 7.2.5. -/
abbrev Example725PointSpace := EuclideanSpace ℝ (Fin 1)

/-- The two-dimensional residual space used for Example 7.2.5. -/
abbrev Example725ResidualSpace := EuclideanSpace ℝ (Fin 2)

/-- The coordinate equivalence for the one-dimensional ambient space in Example 7.2.5. -/
abbrev example725PointCoords := EuclideanSpace.equiv (Fin 1) ℝ

/-- The coordinate equivalence for the residual space in Example 7.2.5. -/
abbrev example725ResidualCoords := EuclideanSpace.equiv (Fin 2) ℝ

/-- The scalar variable `x ∈ ℝ` viewed in the chapter's one-dimensional Euclidean ambient
space. -/
def example725Point (x : ℝ) : Example725PointSpace :=
  WithLp.toLp 2 <| ![x]

/-- The residual map in Example 7.2.5, packaged as the canonical `ℝ¹ → ℝ²` least-squares
owner. -/
def example725ResidualMap (lam : ℝ) (x : Example725PointSpace) : Example725ResidualSpace :=
  let x0 := example725PointCoords x 0
  WithLp.toLp 2 <| ![x0 + 1, lam * x0 ^ (2 : ℕ) + x0 - 1]

/-- The same residual map, specialized back to the textbook scalar variable `x ∈ ℝ`. -/
abbrev example725ResidualVector (lam : ℝ) (x : ℝ) : Example725ResidualSpace :=
  example725ResidualMap lam (example725Point x)

/-- The first residual coordinate in Example 7.2.5 is `x + 1`. -/
theorem example725ResidualVector_apply_zero (lam x : ℝ) :
    example725ResidualCoords (example725ResidualVector lam x) 0 = x + 1 := by
  simp [example725ResidualVector, example725ResidualMap, example725Point]

/-- The second residual coordinate in Example 7.2.5 is `λ x² + x - 1`. -/
theorem example725ResidualVector_apply_one (lam x : ℝ) :
    example725ResidualCoords (example725ResidualVector lam x) 1 = lam * x ^ (2 : ℕ) + x - 1 := by
  simp [example725ResidualVector, example725ResidualMap, example725Point]

/-- Helper for Chapter07 Example 7.2.5: the textbook objective is
`f(x) = (x + 1)^2 + (λ x^2 + x - 1)^2`. -/
def example725Objective (lam x : ℝ) : ℝ :=
  (x + 1) ^ (2 : ℕ) + (lam * x ^ (2 : ℕ) + x - 1) ^ (2 : ℕ)

/-- Helper for Chapter07 Example 7.2.5: the chapter's canonical normalized least-squares owner
is one half of the textbook objective. -/
theorem example725Objective_eq_half_norm_sq (lam x : ℝ) :
    nonlinearLeastSquaresObjective (example725ResidualMap lam) (example725Point x) =
      ((1 : ℝ) / 2) * example725Objective lam x := by
  -- Rewrite the canonical least-squares owner as half the squared Euclidean residual norm.
  rw [nonlinearLeastSquaresObjective_eq_half_norm_sq]
  congr 1
  -- Expand the two residual coordinates to recover the textbook scalar objective.
  calc
    ‖example725ResidualVector lam x‖ ^ (2 : ℕ)
        = (example725ResidualVector lam x).ofLp 0 ^ (2 : ℕ) +
            (example725ResidualVector lam x).ofLp 1 ^ (2 : ℕ) := by
            simpa using EuclideanSpace.real_norm_sq_eq (example725ResidualVector lam x)
    _ = example725Objective lam x := by
      simp [example725Objective, example725ResidualVector, example725ResidualMap, example725Point]

/-- Helper for Chapter07 Example 7.2.5: the textbook objective is the squared residual norm. -/
theorem example725Objective_eq_norm_sq (lam x : ℝ) :
    example725Objective lam x = ‖example725ResidualVector lam x‖ ^ (2 : ℕ) := by
  -- Expand the squared norm into the two residual coordinates and match the textbook formula.
  calc
    example725Objective lam x
        = (example725ResidualVector lam x).ofLp 0 ^ (2 : ℕ) +
            (example725ResidualVector lam x).ofLp 1 ^ (2 : ℕ) := by
            simp [example725Objective, example725ResidualVector, example725ResidualMap, example725Point]
    _ = ‖example725ResidualVector lam x‖ ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq (example725ResidualVector lam x)).symm

/-- The explicit Gauss-Newton self-map in Example 7.2.5, viewed on the chapter's
one-dimensional Euclidean ambient space. -/
def example725GaussNewtonMap (lam : ℝ) (x : Example725PointSpace) : Example725PointSpace :=
  let x0 := example725PointCoords x 0
  example725Point <|
    (2 * lam ^ (2 : ℕ) * x0 ^ (3 : ℕ) + lam * x0 ^ (2 : ℕ) + 2 * lam * x0) /
      (1 + (2 * lam * x0 + 1) ^ (2 : ℕ))

/-- Helper for Chapter07 Example 7.2.5: the residual map has the expected owner-level derivative
bridge to the explicit column matrix `!![1; 2 λ x + 1]`. -/
private theorem example725ResidualMap_hasFDerivAt (lam : ℝ) (x : Example725PointSpace) :
    HasFDerivAt (example725ResidualMap lam)
      ((Matrix.toEuclideanLin
        !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)]).toContinuousLinearMap) x := by
  let D : Example725PointSpace →L[ℝ] Example725ResidualSpace :=
    (Matrix.toEuclideanLin
      !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)]).toContinuousLinearMap
  let iso : Example725ResidualSpace ≃L[ℝ] (Fin 2 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)
  let rho : Example725PointSpace → Fin 2 → ℝ := fun y ↦
    ![example725PointCoords y 0 + 1,
      lam * (example725PointCoords y 0) ^ (2 : ℕ) + example725PointCoords y 0 - 1]
  let coord0 : Example725PointSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 ↦ ℝ) 0
  have hproj0 :
      (ContinuousLinearMap.proj 0).comp ((iso : Example725ResidualSpace →L[ℝ] (Fin 2 → ℝ)).comp D) =
        coord0 := by
    -- The first residual coordinate has derivative `v ↦ v 0`.
    ext v
    have hv0 : Matrix.vecHead v.ofLp = v.ofLp 0 := rfl
    simp [D, iso, coord0, Matrix.toEuclideanLin_apply, hv0]
  have hproj1 :
      (ContinuousLinearMap.proj 1).comp ((iso : Example725ResidualSpace →L[ℝ] (Fin 2 → ℝ)).comp D) =
        (2 * lam * example725PointCoords x 0 + 1) • coord0 := by
    -- The second residual coordinate has derivative `v ↦ (2 λ x + 1) v 0`.
    ext v
    have hv0 : Matrix.vecHead v.ofLp = v.ofLp 0 := rfl
    simp [D, iso, coord0, Matrix.toEuclideanLin_apply, hv0]
  have hy0 : HasFDerivAt (fun y : Example725PointSpace ↦ example725PointCoords y 0) coord0 x := by
    -- The unique point coordinate is the canonical `PiLp` projection.
    simpa [coord0, example725PointCoords] using
      (PiLp.hasFDerivAt_apply (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 1 ↦ ℝ) x 0)
  have hsq :
      HasFDerivAt
        (fun y : Example725PointSpace ↦ (example725PointCoords y 0) ^ (2 : ℕ))
        ((2 * example725PointCoords x 0) • coord0) x := by
    -- Differentiate the product `x₀ * x₀`.
    have hsqMul :=
      (hy0.mul hy0 :
        HasFDerivAt
          ((fun y : Example725PointSpace ↦ example725PointCoords y 0) *
            fun y : Example725PointSpace ↦ example725PointCoords y 0)
          (example725PointCoords x 0 • coord0 + example725PointCoords x 0 • coord0) x)
    have hsum :
        ((2 * example725PointCoords x 0) • coord0) =
          example725PointCoords x 0 • coord0 + example725PointCoords x 0 • coord0 := by
      rw [mul_smul, two_smul]
    have hsq'' :
        HasFDerivAt
          ((fun y : Example725PointSpace ↦ example725PointCoords y 0) *
            fun y : Example725PointSpace ↦ example725PointCoords y 0)
          ((2 * example725PointCoords x 0) • coord0) x :=
      hsqMul.congr_fderiv hsum.symm
    have hsq''' :
        HasFDerivAt
          (fun y : Example725PointSpace ↦ example725PointCoords y 0 * example725PointCoords y 0)
          ((2 * example725PointCoords x 0) • coord0) x := by
      refine hsq''.congr_of_eventuallyEq ?_
      filter_upwards with y
      rfl
    simpa [pow_two] using hsq'''
  have hquad :
      HasFDerivAt
        (fun y : Example725PointSpace ↦ lam * (example725PointCoords y 0) ^ (2 : ℕ))
        ((2 * lam * example725PointCoords x 0) • coord0) x := by
    -- Multiply the squared coordinate by the constant parameter `λ`.
    simpa [mul_smul, mul_assoc, mul_left_comm, mul_comm] using
      hsq.const_mul lam
  have hrho :
      HasFDerivAt rho ((iso : Example725ResidualSpace →L[ℝ] (Fin 2 → ℝ)).comp D) x := by
    -- Differentiate the two residual coordinates separately in the `PiLp` coordinates.
    rw [hasFDerivAt_pi']
    intro i
    fin_cases i
    · simpa [rho, hproj0, add_comm] using hy0.const_add (1 : ℝ)
    · convert (hquad.add hy0).sub_const (1 : ℝ) using 1
      · simp [rho, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
      · ext v
        simp [hproj1, add_smul]
  -- Transfer the coordinate derivative back across the Euclidean-space equivalence.
  exact (iso.comp_hasFDerivAt_iff (f := example725ResidualMap lam) (x := x) (f' := D)).mp <|
    by simpa [example725ResidualMap, rho, iso, D] using hrho

/-- Helper for Chapter07 Example 7.2.5: applying the canonical Jacobian matrix is the same as
applying the Fréchet derivative of the residual map. -/
private theorem example725ResidualJacobian_apply_eq_fderiv
    (lam : ℝ) (x v : Example725PointSpace) :
    Matrix.toEuclideanLin (residualJacobianMatrix (example725ResidualMap lam) x) v =
      fderiv ℝ (example725ResidualMap lam) x v := by
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (residualJacobianMatrix (example725ResidualMap lam) x) v =
        (fderiv ℝ (example725ResidualMap lam) x).toLinearMap v := by
    -- Reconstruct the derivative map from its matrix in the standard Euclidean bases.
    exact
      congrArg
        (fun L : Example725PointSpace →ₗ[ℝ] Example725ResidualSpace ↦ L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
          ((fderiv ℝ (example725ResidualMap lam) x).toLinearMap))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using hToLin

-- TODO: reconstruct `residualJacobianMatrix` from `example725ResidualMap_hasFDerivAt` via
-- `Matrix.toEuclideanLin.injective`.
theorem example725ResidualJacobian_eq (lam : ℝ) (x : Example725PointSpace) :
    residualJacobianMatrix (example725ResidualMap lam) x =
      !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)] := by
  let D : Example725PointSpace →L[ℝ] Example725ResidualSpace :=
    (Matrix.toEuclideanLin
      !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)]).toContinuousLinearMap
  -- Compare both Jacobian matrices through their Euclidean linear actions.
  apply Matrix.toEuclideanLin.injective
  ext v i
  have hcalc :
      Matrix.toEuclideanLin (residualJacobianMatrix (example725ResidualMap lam) x) v =
        (Matrix.toEuclideanLin !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)]) v := by
    calc
      Matrix.toEuclideanLin (residualJacobianMatrix (example725ResidualMap lam) x) v
          = fderiv ℝ (example725ResidualMap lam) x v := by
              simpa using example725ResidualJacobian_apply_eq_fderiv lam x v
      _ = D v := by
            rw [(example725ResidualMap_hasFDerivAt lam x).fderiv]
      _ = (Matrix.toEuclideanLin !![(1 : ℝ); (2 * lam * example725PointCoords x 0 + 1)]) v := by
            rfl
  exact congrArg (fun z : Example725ResidualSpace ↦ z i) hcalc

/-- Helper for Chapter07 Example 7.2.5: the scalar denominator in the Gauss-Newton update is
strictly positive. -/
theorem example725GaussNewtonDenominator_pos (lam x : ℝ) :
    0 < 1 + (2 * lam * x + 1) ^ (2 : ℕ) := by
  -- The denominator is `1` plus a square, so positivity is immediate.
  positivity

/-- Helper for Chapter07 Example 7.2.5: the scalar denominator in the Gauss-Newton update is
nonzero. -/
theorem example725GaussNewtonDenominator_ne (lam x : ℝ) :
    1 + (2 * lam * x + 1) ^ (2 : ℕ) ≠ 0 :=
  ne_of_gt (example725GaussNewtonDenominator_pos lam x)

/-- Helper for Chapter07 Example 7.2.5: `leastSquaresGradient` is the coordinate vector
`WithLp.toLp 2 (((J(x))ᵀ).mulVec r(x).ofLp)`. -/
private theorem example725LeastSquaresGradient_eq_coordinate
    (r : Example725PointSpace → Example725ResidualSpace) (x : Example725PointSpace) :
    leastSquaresGradient r x =
      WithLp.toLp 2 ((Matrix.transpose (residualJacobianMatrix r x)).mulVec (r x).ofLp) := by
  -- Unpack the Euclidean matrix action into the concrete `mulVec` formula.
  simpa [leastSquaresGradient] using
    (Matrix.toEuclideanLin_apply (Matrix.transpose (residualJacobianMatrix r x)) (r x))

/-- Helper for Chapter07 Example 7.2.5: the Gauss-Newton normal equation is equivalent to the
coordinate `mulVec` identity in the one-dimensional ambient space. -/
private theorem example725SolvesGaussNewtonNormalEquation_iff_coordinate
    (r : Example725PointSpace → Example725ResidualSpace)
    (xk xNext : Example725PointSpace) :
    solvesGaussNewtonNormalEquation r xk xNext ↔
      (gaussNewtonNormalMatrix r xk).mulVec (xNext - xk).ofLp =
        -(leastSquaresGradient r xk).ofLp := by
  -- Transport the point-valued normal equation through `WithLp.ofLp`.
  rw [solvesGaussNewtonNormalEquation_iff, example725LeastSquaresGradient_eq_coordinate]
  constructor
  · intro h
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.ofLp) h
  · intro h
    apply WithLp.ofLp_injective 2
    simpa [Matrix.toEuclideanLin_apply] using h

/-- The point-level update in Example 7.2.5 satisfies the chapter's canonical Gauss-Newton
normal equation for the example residual map. -/
theorem example725GaussNewtonMap_solvesNormalEquation (lam : ℝ) (x : Example725PointSpace) :
    solvesGaussNewtonNormalEquation (example725ResidualMap lam) x
      (example725GaussNewtonMap lam x) := by
  let x0 : ℝ := example725PointCoords x 0
  have hJ :
      residualJacobianMatrix (example725ResidualMap lam) x =
        !![(1 : ℝ); (2 * lam * x0 + 1)] := by
    -- Rewrite the Jacobian into the explicit column matrix from the derivative computation.
    simpa [x0] using example725ResidualJacobian_eq lam x
  have hgrad :
      leastSquaresGradient (example725ResidualMap lam) x =
        WithLp.toLp 2
          ![2 * lam ^ (2 : ℕ) * x0 ^ (3 : ℕ) + 3 * lam * x0 ^ (2 : ℕ) + (2 - 2 * lam) * x0] := by
    -- Multiply `J(x)ᵀ` by the explicit residual vector to recover the scalar gradient formula.
    rw [example725LeastSquaresGradient_eq_coordinate, hJ]
    ext i
    fin_cases i
    simp [x0, example725ResidualMap, example725Point, Matrix.mulVec, Fin.sum_univ_two]
    ring
  have hstep :
      (example725GaussNewtonMap lam x - x).ofLp =
        ![(-2 * lam ^ (2 : ℕ) * x0 ^ (3 : ℕ) - 3 * lam * x0 ^ (2 : ℕ) +
            (2 * lam - 2) * x0) /
          (1 + (2 * lam * x0 + 1) ^ (2 : ℕ))] := by
    -- The explicit update formula yields the scalar step `x_{k+1} - x_k`.
    ext i
    fin_cases i
    simp [x0, example725GaussNewtonMap, example725Point]
    field_simp [example725GaussNewtonDenominator_ne lam x0]
    ring_nf
  have hA :
      gaussNewtonNormalMatrix (example725ResidualMap lam) x =
        !![(1 + (2 * lam * x0 + 1) ^ (2 : ℕ) : ℝ)] := by
    -- The `1 × 1` normal matrix is the scalar Gram product `1 + (2 λ x + 1)^2`.
    rw [gaussNewtonNormalMatrix_eq, hJ]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]
  -- Route correction: solve the owner-level normal equation in `WithLp.ofLp` coordinates before
  -- returning to the point-valued statement.
  rw [example725SolvesGaussNewtonNormalEquation_iff_coordinate, hstep, hgrad, hA]
  ext i
  fin_cases i
  simp [Matrix.mulVec, Fin.sum_univ_one]
  field_simp [example725GaussNewtonDenominator_ne lam x0]
  ring_nf

/-- The textbook scalar Gauss-Newton update is the scalar-coordinate view of
`example725GaussNewtonMap`. -/
abbrev example725GaussNewtonStep (lam x : ℝ) : ℝ :=
  example725PointCoords (example725GaussNewtonMap lam (example725Point x)) 0

/-- Specialized to the textbook scalar variable, the Example 7.2.5 update still carries the
chapter's canonical Gauss-Newton normal-equation semantics. -/
theorem example725GaussNewtonStep_solvesNormalEquation (lam x : ℝ) :
    solvesGaussNewtonNormalEquation (example725ResidualMap lam) (example725Point x)
      (example725GaussNewtonMap lam (example725Point x)) :=
  example725GaussNewtonMap_solvesNormalEquation lam (example725Point x)

/-- The explicit scalar formula for the Example 7.2.5 Gauss-Newton update. -/
theorem example725GaussNewtonStep_eq (lam x : ℝ) :
    example725GaussNewtonStep lam x =
      (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
        (1 + (2 * lam * x + 1) ^ (2 : ℕ)) := by
  simp [example725GaussNewtonStep, example725GaussNewtonMap, example725Point]

/-- The scalar multiplier in the factorization `example725GaussNewtonStep lam x = x * m(lam, x)`.
-/
abbrev example725GaussNewtonMultiplier (lam x : ℝ) : ℝ :=
  (2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam) /
    (1 + (2 * lam * x + 1) ^ (2 : ℕ))

/-- Helper for Chapter07 Example 7.2.5: the Gauss-Newton step factors as `x` times an explicit
multiplier. -/
theorem example725GaussNewtonStep_eq_mul_multiplier (lam x : ℝ) :
    example725GaussNewtonStep lam x = x * example725GaussNewtonMultiplier lam x := by
  -- Factor a single copy of `x` out of the cubic numerator.
  rw [example725GaussNewtonStep_eq, example725GaussNewtonMultiplier]
  field_simp [example725GaussNewtonDenominator_ne lam x]

/-- Helper for Chapter07 Example 7.2.5: any nonzero scalar root of
`2 λ² x² + 3 λ x + 2 - 2 λ = 0` is a fixed point of the scalar Gauss-Newton step. -/
theorem example725GaussNewtonStep_eq_self_of_fixedPointPolynomial
    (lam x : ℝ)
    (hpoly : 2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + 3 * lam * x + 2 - 2 * lam = 0) :
    example725GaussNewtonStep lam x = x := by
  rw [example725GaussNewtonStep_eq_mul_multiplier]
  have hmult : example725GaussNewtonMultiplier lam x = 1 := by
    -- The fixed-point polynomial is exactly the cleared-denominator identity `m(λ, x) = 1`.
    rw [example725GaussNewtonMultiplier]
    apply (div_eq_iff (example725GaussNewtonDenominator_ne lam x)).2
    nlinarith [hpoly]
  simpa [hmult]

/-- The scalar remainder in the expansion
`example725GaussNewtonStep lam x - lam * x = x^2 * R(lam, x)`. -/
abbrev example725GaussNewtonRemainder (lam x : ℝ) : ℝ :=
  (lam + 2 * lam ^ (2 : ℕ) * x - 4 * lam ^ (2 : ℕ) - 4 * lam ^ (3 : ℕ) * x) /
    (1 + (2 * lam * x + 1) ^ (2 : ℕ))

/-- Helper for Chapter07 Example 7.2.5: subtracting the linear part `λ x` leaves a quadratic
remainder. -/
theorem example725GaussNewtonStep_sub_mul_eq_sq_remainder (lam x : ℝ) :
    example725GaussNewtonStep lam x - lam * x =
      x ^ (2 : ℕ) * example725GaussNewtonRemainder lam x := by
  -- Clear the common denominator and expand the numerator once.
  rw [example725GaussNewtonStep_eq, example725GaussNewtonRemainder]
  field_simp [example725GaussNewtonDenominator_ne lam x]
  ring_nf

/-- Helper for Chapter07 Example 7.2.5: the multiplier tends to `λ` as `x → 0`. -/
theorem example725GaussNewtonMultiplier_tendsto (lam : ℝ) :
    Filter.Tendsto (example725GaussNewtonMultiplier lam) (𝓝 (0 : ℝ)) (𝓝 lam) := by
  -- The multiplier is a rational function with denominator `2` at `x = 0`, so continuity
  -- gives the limit once we record that denominator value is nonzero.
  have hcont :
      ContinuousAt
        (fun x : ℝ ↦
          (2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam) /
            (1 + (2 * lam * x + 1) ^ (2 : ℕ))) 0 := by
    have hnum :
        ContinuousAt (fun x : ℝ ↦ 2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam) 0 := by
      fun_prop
    have hden :
        ContinuousAt (fun x : ℝ ↦ 1 + (2 * lam * x + 1) ^ (2 : ℕ)) 0 := by
      fun_prop
    exact hnum.div hden (by norm_num)
  convert hcont.tendsto using 1 <;> ring_nf

/-- Helper for Chapter07 Example 7.2.5: the two-step scalar multiplier tends to `λ²` as
`x → 0`. -/
theorem example725GaussNewtonTwoStepMultiplier_tendsto (lam : ℝ) :
    Filter.Tendsto
      (fun x : ℝ ↦
        example725GaussNewtonMultiplier lam (example725GaussNewtonStep lam x) *
          example725GaussNewtonMultiplier lam x)
      (𝓝 (0 : ℝ)) (𝓝 (lam ^ (2 : ℕ))) := by
  have hcont :
      ContinuousAt
        (fun x : ℝ ↦
          (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
            (1 + (2 * lam * x + 1) ^ (2 : ℕ))) 0 := by
    have hnum :
        ContinuousAt
          (fun x : ℝ ↦
            2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) 0 := by
      fun_prop
    have hden :
        ContinuousAt (fun x : ℝ ↦ 1 + (2 * lam * x + 1) ^ (2 : ℕ)) 0 := by
      fun_prop
    exact hnum.div hden (by norm_num)
  have hstep_zero_formula :
      Filter.Tendsto
        (fun x : ℝ ↦
          (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
            (1 + (2 * lam * x + 1) ^ (2 : ℕ)))
        (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    -- The explicit rational formula has value `0` at the origin.
    convert hcont.tendsto using 1 <;> ring_nf
  have hstep_eq :
      example725GaussNewtonStep lam =
        fun x : ℝ ↦
          (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
            (1 + (2 * lam * x + 1) ^ (2 : ℕ)) := by
    funext x
    exact example725GaussNewtonStep_eq lam x
  have hstep_zero :
      Filter.Tendsto (example725GaussNewtonStep lam) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [hstep_eq] using hstep_zero_formula
  have houter :
      Filter.Tendsto
        (fun x : ℝ ↦ example725GaussNewtonMultiplier lam (example725GaussNewtonStep lam x))
        (𝓝 (0 : ℝ)) (𝓝 lam) :=
    (example725GaussNewtonMultiplier_tendsto lam).comp hstep_zero
  -- Multiply the two one-step multiplier limits to obtain the two-step limit.
  simpa [pow_two] using houter.mul (example725GaussNewtonMultiplier_tendsto lam)

/-- Helper for Chapter07 Example 7.2.5: the quadratic remainder factor tends to its finite value
at `x = 0`. -/
theorem example725GaussNewtonRemainder_tendsto (lam : ℝ) :
    Filter.Tendsto (example725GaussNewtonRemainder lam) (𝓝 (0 : ℝ))
      (𝓝 ((lam - 4 * lam ^ (2 : ℕ)) / 2)) := by
  -- The remainder factor is another rational function whose denominator is still `2` at `0`.
  have hcont :
      ContinuousAt
        (fun x : ℝ ↦
          (lam + 2 * lam ^ (2 : ℕ) * x - 4 * lam ^ (2 : ℕ) - 4 * lam ^ (3 : ℕ) * x) /
            (1 + (2 * lam * x + 1) ^ (2 : ℕ))) 0 := by
    have hnum :
        ContinuousAt
          (fun x : ℝ ↦ lam + 2 * lam ^ (2 : ℕ) * x - 4 * lam ^ (2 : ℕ) - 4 * lam ^ (3 : ℕ) * x) 0 := by
      fun_prop
    have hden :
        ContinuousAt (fun x : ℝ ↦ 1 + (2 * lam * x + 1) ^ (2 : ℕ)) 0 := by
      fun_prop
    exact hnum.div hden (by norm_num)
  convert hcont.tendsto using 1 <;> ring_nf

/-- The canonical point-level Gauss-Newton orbit from initial value `x₀`, obtained by iterating
the Example 7.2.5 Gauss-Newton self-map. -/
def example725GaussNewtonPointOrbit (lam x0 : ℝ) : ℕ → Example725PointSpace :=
  fun n ↦ ((example725GaussNewtonMap lam)^[n]) (example725Point x0)

/-- Every point-level orbit step satisfies the chapter's canonical Gauss-Newton normal equation
for the example residual map. -/
theorem example725GaussNewtonPointOrbit_solvesNormalEquation
    (lam x0 : ℝ) (n : ℕ) :
    solvesGaussNewtonNormalEquation (example725ResidualMap lam)
      (example725GaussNewtonPointOrbit lam x0 n)
      (example725GaussNewtonPointOrbit lam x0 (n + 1)) := by
  -- Each orbit step is exactly one application of the point-level Gauss-Newton map.
  simpa [example725GaussNewtonPointOrbit, Function.iterate_succ_apply'] using
    example725GaussNewtonMap_solvesNormalEquation lam (example725GaussNewtonPointOrbit lam x0 n)

/-- The scalar Gauss-Newton orbit is the coordinate view of the canonical point-level orbit. -/
abbrev example725GaussNewtonOrbit (lam x0 : ℝ) : ℕ → ℝ :=
  fun n ↦ example725PointCoords (example725GaussNewtonPointOrbit lam x0 n) 0

/-- Helper for Chapter07 Example 7.2.5: every point in the one-dimensional ambient space is
recovered from its unique scalar coordinate. -/
theorem example725Point_pointCoords (x : Example725PointSpace) :
    example725Point (example725PointCoords x 0) = x := by
  -- The ambient space is one-dimensional, so equality is determined by the unique coordinate.
  ext i
  fin_cases i
  simp [example725Point]

/-- Helper for Chapter07 Example 7.2.5: the scalar orbit satisfies the expected one-step
recursion. -/
theorem example725GaussNewtonOrbit_succ (lam x0 : ℝ) (n : ℕ) :
    example725GaussNewtonOrbit lam x0 (n + 1) =
      example725GaussNewtonStep lam (example725GaussNewtonOrbit lam x0 n) := by
  -- Rewrite the next point-iterate as one application of the Gauss-Newton map.
  rw [example725GaussNewtonOrbit, example725GaussNewtonPointOrbit, example725GaussNewtonStep,
    Function.iterate_succ_apply']
  let y : Example725PointSpace := ((example725GaussNewtonMap lam)^[n]) (example725Point x0)
  change example725PointCoords (example725GaussNewtonMap lam y) 0 =
    example725PointCoords (example725GaussNewtonMap lam
      (example725Point (example725PointCoords y 0))) 0
  have hy : example725Point (example725PointCoords y 0) = y := example725Point_pointCoords y
  -- Replace the intermediate point by `example725Point` of its unique scalar coordinate.
  simpa [y] using congrArg (fun z : Example725PointSpace ↦ example725PointCoords
    (example725GaussNewtonMap lam z) 0) hy.symm

/-- Helper for Chapter07 Example 7.2.5: the scalar orbit is exactly the iteration of the scalar
Gauss-Newton step map. -/
theorem example725GaussNewtonOrbit_eq_iterate_step (lam x0 : ℝ) (n : ℕ) :
    example725GaussNewtonOrbit lam x0 n = ((example725GaussNewtonStep lam)^[n]) x0 := by
  induction n with
  | zero =>
      -- The zeroth orbit element is the initial scalar iterate.
      simp [example725GaussNewtonOrbit, example725GaussNewtonPointOrbit, example725Point]
  | succ n ih =>
      -- One orbit step matches one application of the scalar step map.
      rw [example725GaussNewtonOrbit_succ, ih, Function.iterate_succ_apply']

/-- Helper for Chapter07 Example 7.2.5: two scalar Gauss-Newton steps factor through the product
of the two local multipliers. -/
theorem example725GaussNewtonStep_iterate_two_eq_mul_multiplierProduct (lam x : ℝ) :
    example725GaussNewtonStep lam (example725GaussNewtonStep lam x) =
      x *
        (example725GaussNewtonMultiplier lam (example725GaussNewtonStep lam x) *
          example725GaussNewtonMultiplier lam x) := by
  -- Expand each step once through the scalar multiplier factorization and regroup the factors.
  rw [example725GaussNewtonStep_eq_mul_multiplier, example725GaussNewtonStep_eq_mul_multiplier]
  ring

/-- Helper for Chapter07 Example 7.2.5: on the box `|λ| < 1 / 4`, `|x| < 1`, the scalar step is a
uniform `7/8` contraction. -/
theorem example725GaussNewtonStep_norm_le_small_abs {lam x : ℝ}
    (hlam : |lam| < (1 / 4 : ℝ)) (hx : |x| < 1) :
    |example725GaussNewtonStep lam x| ≤ (7 / 8 : ℝ) * |x| := by
  have hlam_le : |lam| ≤ (1 / 4 : ℝ) := le_of_lt hlam
  have hx_le : |x| ≤ 1 := le_of_lt hx
  have hlam_sq : |lam| ^ (2 : ℕ) ≤ (1 / 4 : ℝ) ^ (2 : ℕ) := by
    nlinarith [abs_nonneg lam, hlam_le]
  have hx_sq : |x| ^ (2 : ℕ) ≤ (1 : ℝ) := by
    nlinarith [abs_nonneg x, hx_le]
  have hterm1 : 2 * |lam| ^ (2 : ℕ) * |x| ^ (2 : ℕ) ≤ (1 / 8 : ℝ) := by
    nlinarith [hlam_sq, hx_sq]
  have hterm2 : |lam| * |x| ≤ (1 / 4 : ℝ) := by
    nlinarith [abs_nonneg lam, abs_nonneg x, hlam_le, hx_le]
  have hterm3 : 2 * |lam| ≤ (1 / 2 : ℝ) := by
    nlinarith [hlam_le]
  have hnum_le :
      |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam|
        ≤ 2 * |lam| ^ (2 : ℕ) * |x| ^ (2 : ℕ) + |lam| * |x| + 2 * |lam| := by
    calc
      |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam|
          ≤ |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x| + |2 * lam| := by
              simpa [Real.norm_eq_abs, add_assoc] using
                norm_add_le (2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x) (2 * lam)
      _ ≤ |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ)| + |lam * x| + |2 * lam| := by
            have htri : |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x| ≤
                |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ)| + |lam * x| := by
              simpa [Real.norm_eq_abs] using
                norm_add_le (2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ)) (lam * x)
            nlinarith
      _ = 2 * |lam| ^ (2 : ℕ) * |x| ^ (2 : ℕ) + |lam| * |x| + 2 * |lam| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hnum : |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam| ≤ (7 / 8 : ℝ) := by
    nlinarith [hnum_le, hterm1, hterm2, hterm3]
  have hden_pos : 0 < |1 + (2 * lam * x + 1) ^ (2 : ℕ)| := by
    rw [abs_of_pos (example725GaussNewtonDenominator_pos lam x)]
    exact example725GaussNewtonDenominator_pos lam x
  have hden_ge : (1 : ℝ) ≤ |1 + (2 * lam * x + 1) ^ (2 : ℕ)| := by
    rw [abs_of_pos (example725GaussNewtonDenominator_pos lam x)]
    nlinarith
  have hmult : |example725GaussNewtonMultiplier lam x| ≤ (7 / 8 : ℝ) := by
    rw [example725GaussNewtonMultiplier, abs_div]
    have hfrac :
        |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam| /
            |1 + (2 * lam * x + 1) ^ (2 : ℕ)|
          ≤ |2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam| := by
      refine (div_le_iff₀ hden_pos).2 ?_
      have hmul := mul_le_mul_of_nonneg_left hden_ge
        (abs_nonneg (2 * lam ^ (2 : ℕ) * x ^ (2 : ℕ) + lam * x + 2 * lam))
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_trans hfrac hnum
  -- Convert the uniform multiplier bound into the one-step contraction estimate.
  calc
    |example725GaussNewtonStep lam x|
        = |x| * |example725GaussNewtonMultiplier lam x| := by
            rw [example725GaussNewtonStep_eq_mul_multiplier, abs_mul]
    _ ≤ |x| * (7 / 8 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hmult (abs_nonneg x)
    _ = (7 / 8 : ℝ) * |x| := by ring

/-- Helper for Chapter07 Example 7.2.5: for `|λ| < 1 / 4` and `|x₀| < 1`, the scalar orbit is
dominated by the geometric sequence `(7/8)^n |x₀|`. -/
theorem example725GaussNewtonOrbit_abs_le_geometric {lam x0 : ℝ}
    (hlam : |lam| < (1 / 4 : ℝ)) (hx0 : |x0| < 1) :
    ∀ n : ℕ,
      |example725GaussNewtonOrbit lam x0 n| ≤ (7 / 8 : ℝ) ^ n * |x0| := by
  intro n
  induction n with
  | zero =>
      -- The zeroth orbit element is the initial value.
      simp [example725GaussNewtonOrbit, example725GaussNewtonPointOrbit, example725Point]
  | succ n ihn =>
      have hpow_le : (7 / 8 : ℝ) ^ n ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num : (7 / 8 : ℝ) ≤ 1)
      have horbit_le : |example725GaussNewtonOrbit lam x0 n| ≤ |x0| := by
        have hmajor : (7 / 8 : ℝ) ^ n * |x0| ≤ |x0| := by
          nlinarith [hpow_le, abs_nonneg x0]
        exact le_trans ihn hmajor
      have horbit_lt : |example725GaussNewtonOrbit lam x0 n| < 1 := by
        exact lt_of_le_of_lt horbit_le hx0
      calc
        |example725GaussNewtonOrbit lam x0 (n + 1)|
            = |example725GaussNewtonStep lam (example725GaussNewtonOrbit lam x0 n)| := by
                rw [example725GaussNewtonOrbit_succ]
        _ ≤ (7 / 8 : ℝ) * |example725GaussNewtonOrbit lam x0 n| := by
              exact example725GaussNewtonStep_norm_le_small_abs hlam horbit_lt
        _ ≤ (7 / 8 : ℝ) * ((7 / 8 : ℝ) ^ n * |x0|) := by
              exact mul_le_mul_of_nonneg_left ihn (by norm_num)
        _ = (7 / 8 : ℝ) ^ (n + 1) * |x0| := by
              rw [pow_succ]
              ring

/-- The Example 7.2.5 Gauss-Newton step has the reference point `x* = 0` as a fixed point. -/
theorem example725GaussNewtonStep_isFixedPt_zero (lam : ℝ) :
    Function.IsFixedPt (example725GaussNewtonStep lam) 0 := by
  -- The explicit scalar formula vanishes at `x = 0`.
  rw [Function.IsFixedPt, example725GaussNewtonStep_eq]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the first displayed table entry is
`1.000000`. -/
theorem example725GaussNewtonOrbit_pointOne_value1 :
    example725GaussNewtonOrbit (1 / 10 : ℝ) 1 0 = 1 := by
  -- The zeroth orbit element is the initial value itself.
  simp [example725GaussNewtonOrbit, example725GaussNewtonPointOrbit, example725Point]

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the second displayed table entry is
`0.131148` to six decimal places. -/
theorem example725GaussNewtonOrbit_pointOne_value2 :
    |example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 - 0.131148| ≤ (1 / 2000000 : ℝ) := by
  -- Evaluate the first nontrivial iterate exactly, then compare with the printed decimal.
  have hExact : example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 = (8 / 61 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_pointOne_value1,
      example725GaussNewtonStep_eq]
    norm_num
  rw [hExact]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the third displayed table entry is
`0.013635` to six decimal places. -/
theorem example725GaussNewtonOrbit_pointOne_value3 :
    |example725GaussNewtonOrbit (1 / 10 : ℝ) 1 2 - 0.013635| ≤ (1 / 2000000 : ℝ) := by
  -- The second iterate is another exact rational value, which refines the six-decimal table.
  have hExact1 : example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 = (8 / 61 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_pointOne_value1,
      example725GaussNewtonStep_eq]
    norm_num
  have hExact2 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 2 = (79428 / 5825317 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 1, hExact1, example725GaussNewtonStep_eq]
    norm_num
  rw [hExact2]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the fourth displayed table entry is
`0.001369` to six decimal places. -/
theorem example725GaussNewtonOrbit_pointOne_value4 :
    |example725GaussNewtonOrbit (1 / 10 : ℝ) 1 3 - 0.001369| ≤ (1 / 2000000 : ℝ) := by
  -- Continue the exact rational recursion once more before comparing to the displayed decimal.
  have hExact1 : example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 = (8 / 61 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_pointOne_value1,
      example725GaussNewtonStep_eq]
    norm_num
  have hExact2 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 2 = (79428 / 5825317 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 1, hExact1, example725GaussNewtonStep_eq]
    norm_num
  have hExact3 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 3 =
        (6784401331300200078 / 4955449060647457790449 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 2, hExact2, example725GaussNewtonStep_eq]
    norm_num
  rw [hExact3]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the fifth displayed table entry is
`0.000137` to six decimal places. -/
theorem example725GaussNewtonOrbit_pointOne_value5 :
    |example725GaussNewtonOrbit (1 / 10 : ℝ) 1 4 - 0.000137| ≤ (1 / 2000000 : ℝ) := by
  -- The fourth iterate still evaluates exactly to a rational number, so the decimal check is
  -- an exact inequality over rationals.
  have hExact1 : example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 = (8 / 61 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_pointOne_value1,
      example725GaussNewtonStep_eq]
    norm_num
  have hExact2 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 2 = (79428 / 5825317 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 1, hExact1, example725GaussNewtonStep_eq]
    norm_num
  have hExact3 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 3 =
        (6784401331300200078 / 4955449060647457790449 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 2, hExact2, example725GaussNewtonStep_eq]
    norm_num
  have hExact4 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 4 =
        (416787651323442674663716041361815962651820113989820300516795478 /
          3043042191902379991366726113063138026790186506211599550424493591473 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 3, hExact3, example725GaussNewtonStep_eq]
    norm_num
  rw [hExact4]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: for `λ = 0.1`, the sixth displayed table entry is
`0.000014` to six decimal places. -/
theorem example725GaussNewtonOrbit_pointOne_value6 :
    |example725GaussNewtonOrbit (1 / 10 : ℝ) 1 5 - 0.000014| ≤ (1 / 2000000 : ℝ) := by
  -- One more exact rational iterate matches the printed sixth decimal-place entry.
  have hExact1 : example725GaussNewtonOrbit (1 / 10 : ℝ) 1 1 = (8 / 61 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_pointOne_value1,
      example725GaussNewtonStep_eq]
    norm_num
  have hExact2 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 2 = (79428 / 5825317 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 1, hExact1, example725GaussNewtonStep_eq]
    norm_num
  have hExact3 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 3 =
        (6784401331300200078 / 4955449060647457790449 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 2, hExact2, example725GaussNewtonStep_eq]
    norm_num
  have hExact4 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 4 =
        (416787651323442674663716041361815962651820113989820300516795478 /
          3043042191902379991366726113063138026790186506211599550424493591473 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 3, hExact3, example725GaussNewtonStep_eq]
    norm_num
  have hExact5 :
      example725GaussNewtonOrbit (1 / 10 : ℝ) 1 5 =
        (9649405133478914657424947482051304107392721219351474987718844720261716805688921329820600374317188257429667382941117176052527705068816565338982048812199618724442821827090202740677494860037278623658 /
          704491612632662927027145683671073234241790442038226858200025050519027174114645859822450469582963111707764498849483503691476229517511987873112352295017653583328310551075572119082941747907007657884836201 : ℝ) := by
    rw [example725GaussNewtonOrbit_succ _ _ 4, hExact4, example725GaussNewtonStep_eq]
    norm_num
  rw [hExact5]
  norm_num

/-- Helper for Chapter07 Example 7.2.5: when `λ = 0`, the Gauss-Newton step map sends every
starting value to the minimizer `x* = 0` in one step. -/
theorem example725GaussNewtonStep_zero_lam (x : ℝ) :
    example725GaussNewtonStep 0 x = 0 := by
  -- Setting `λ = 0` annihilates the explicit numerator.
  rw [example725GaussNewtonStep_eq]
  ring_nf

/-- Helper for Chapter07 Example 7.2.5: the Gauss-Newton update has the local expansion
`x ↦ λ x + O(x^2)` at `x = 0`. -/
theorem example725GaussNewtonStep_isBigOAtZero (lam : ℝ) :
    (fun x : ℝ ↦ example725GaussNewtonStep lam x - lam * x) =O[𝓝 (0 : ℝ)] fun x : ℝ ↦
      x ^ (2 : ℕ) := by
  let limit : ℝ := (lam - 4 * lam ^ (2 : ℕ)) / 2
  have hRemBound :
      ∀ᶠ x in 𝓝 (0 : ℝ), |example725GaussNewtonRemainder lam x| ≤ |limit| + 1 := by
    have hNear :
        ∀ᶠ x in 𝓝 (0 : ℝ), example725GaussNewtonRemainder lam x ∈ Metric.ball limit 1 := by
      exact (example725GaussNewtonRemainder_tendsto lam).eventually (Metric.ball_mem_nhds limit zero_lt_one)
    filter_upwards [hNear] with x hx
    have hx' : |example725GaussNewtonRemainder lam x - limit| < 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    have htriangle : |example725GaussNewtonRemainder lam x| ≤
        |example725GaussNewtonRemainder lam x - limit| + |limit| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (_root_.abs_sub_le (example725GaussNewtonRemainder lam x) limit 0)
    nlinarith [htriangle, abs_nonneg (example725GaussNewtonRemainder lam x),
      abs_nonneg limit, le_of_lt hx']
  -- Rewrite the error exactly as `x^2` times the bounded remainder factor.
  refine IsBigO.of_bound (|limit| + 1) ?_
  filter_upwards [hRemBound] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, example725GaussNewtonStep_sub_mul_eq_sq_remainder, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hx (abs_nonneg (x ^ (2 : ℕ)))

/-- Helper for Chapter07 Example 7.2.5: when `|λ|` is small enough, Gauss-Newton orbits that
start sufficiently close to `x* = 0` converge to `0`. -/
theorem example725GaussNewtonOrbit_tendsto_zero_for_small_abs :
    ∃ ε : Set.Ioi (0 : ℝ),
      ∀ {lam : ℝ}, |lam| < (ε : ℝ) →
        ∃ δ : Set.Ioi (0 : ℝ),
          ∀ {x0 : ℝ}, |x0| < (δ : ℝ) →
            Filter.Tendsto (example725GaussNewtonOrbit lam x0) Filter.atTop (𝓝 (0 : ℝ)) := by
  refine ⟨⟨(1 / 4 : ℝ), by norm_num⟩, ?_⟩
  intro lam hlam
  refine ⟨⟨(1 : ℝ), by norm_num⟩, ?_⟩
  intro x0 hx0
  have hbound := example725GaussNewtonOrbit_abs_le_geometric hlam hx0
  have hmajor :
      Filter.Tendsto (fun n : ℕ ↦ (7 / 8 : ℝ) ^ n * |x0|) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
        (by norm_num : (7 / 8 : ℝ) < 1)).mul_const |x0|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- Squeeze the orbit norm between `0` and its geometric majorant.
  simpa [Real.norm_eq_abs] using
    (squeeze_zero' (Filter.Eventually.of_forall fun n ↦ abs_nonneg (example725GaussNewtonOrbit lam x0 n))
      (Filter.Eventually.of_forall hbound) hmajor)

/-- Helper for Chapter07 Example 7.2.5: when `|λ|` is small enough, Gauss-Newton orbits that
start sufficiently close to `x* = 0` satisfy an eventual linear one-step error bound with some
rate `c < 1`. -/
theorem example725GaussNewtonOrbit_eventually_linearRate_for_small_abs :
    ∃ ε : Set.Ioi (0 : ℝ),
      ∀ {lam : ℝ}, |lam| < (ε : ℝ) →
        ∃ δ : Set.Ioi (0 : ℝ), ∃ c : Set.Ico (0 : ℝ) 1,
          ∀ {x0 : ℝ}, |x0| < (δ : ℝ) →
            ∀ᶠ n in Filter.atTop,
              |example725GaussNewtonOrbit lam x0 (n + 1)| ≤
                (c : ℝ) * |example725GaussNewtonOrbit lam x0 n| := by
  refine ⟨⟨(1 / 4 : ℝ), by norm_num⟩, ?_⟩
  intro lam hlam
  refine ⟨⟨(1 : ℝ), by norm_num⟩, ⟨⟨(7 / 8 : ℝ), by norm_num, by norm_num⟩, ?_⟩⟩
  intro x0 hx0
  have hbound := example725GaussNewtonOrbit_abs_le_geometric hlam hx0
  refine Filter.Eventually.of_forall fun n ↦ ?_
  have hpow_le : (7 / 8 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num : (7 / 8 : ℝ) ≤ 1)
  have horbit_le : |example725GaussNewtonOrbit lam x0 n| ≤ |x0| := by
    have hmajor : (7 / 8 : ℝ) ^ n * |x0| ≤ |x0| := by
      nlinarith [hpow_le, abs_nonneg x0]
    exact le_trans (hbound n) hmajor
  have horbit_lt : |example725GaussNewtonOrbit lam x0 n| < 1 := by
    exact lt_of_le_of_lt horbit_le hx0
  -- The orbit remains inside the small box, so the same `7/8` contraction applies at every step.
  rw [example725GaussNewtonOrbit_succ]
  exact example725GaussNewtonStep_norm_le_small_abs
    (lam := lam) (x := example725GaussNewtonOrbit lam x0 n) hlam horbit_lt

/-- Chapter07 Example 7.2.5 (5): when `|λ| > 1`, the Gauss-Newton method can fail to
converge to the minimizer `x* = 0` from a nonzero starting value. -/
theorem example725GaussNewtonOrbit_notTendsto_zero_of_one_lt_abs
    {lam : ℝ} (hlam : 1 < |lam|) :
    ∃ x0 : ℝ, x0 ≠ 0 ∧
        ¬ Filter.Tendsto (example725GaussNewtonOrbit lam x0) Filter.atTop (𝓝 (0 : ℝ)) := by
  have hsplit : 1 < lam ∨ lam < -1 := by
    by_cases hnonneg : 0 ≤ lam
    · left
      rwa [abs_of_nonneg hnonneg] at hlam
    · right
      have hlt : lam < 0 := lt_of_not_ge hnonneg
      have habs : 1 < -lam := by
        rwa [abs_of_neg hlt] at hlam
      nlinarith
  rcases hsplit with hpos | hneg
  · let x0 : ℝ := (-3 + Real.sqrt (16 * lam - 7)) / (4 * lam)
    have hdisc_nonneg : 0 ≤ 16 * lam - 7 := by
      nlinarith
    have hsqrt_gt : 3 < Real.sqrt (16 * lam - 7) := by
      have hdisc_gt : 9 < 16 * lam - 7 := by
        nlinarith
      nlinarith [Real.sq_sqrt hdisc_nonneg, Real.sqrt_nonneg (16 * lam - 7)]
    have hx0_pos : 0 < x0 := by
      -- The positive-`λ` fixed-point witness comes from the positive quadratic root.
      have hden_pos : 0 < 4 * lam := by
        nlinarith
      have hnum_pos : 0 < -3 + Real.sqrt (16 * lam - 7) := by
        nlinarith
      dsimp [x0]
      exact div_pos hnum_pos hden_pos
    have hx0_ne : x0 ≠ 0 := ne_of_gt hx0_pos
    have hpoly :
        2 * lam ^ (2 : ℕ) * x0 ^ (2 : ℕ) + 3 * lam * x0 + 2 - 2 * lam = 0 := by
      -- Clearing the denominator shows that the quadratic root satisfies the fixed-point
      -- polynomial exactly.
      have hden_ne : (4 * lam : ℝ) ≠ 0 := by
        nlinarith
      calc
        2 * lam ^ (2 : ℕ) * x0 ^ (2 : ℕ) + 3 * lam * x0 + 2 - 2 * lam
            = ((Real.sqrt (16 * lam - 7)) ^ (2 : ℕ) - (16 * lam - 7)) / 8 := by
                dsimp [x0]
                field_simp [hden_ne]
                ring
        _ = 0 := by
              rw [Real.sq_sqrt hdisc_nonneg]
              ring
    have hfix : example725GaussNewtonStep lam x0 = x0 :=
      example725GaussNewtonStep_eq_self_of_fixedPointPolynomial lam x0 hpoly
    have horbit_const : ∀ n : ℕ, example725GaussNewtonOrbit lam x0 n = x0 := by
      intro n
      rw [example725GaussNewtonOrbit_eq_iterate_step]
      induction n with
      | zero =>
          rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, hfix]
    refine ⟨x0, hx0_ne, ?_⟩
    intro hTendsto
    have hconst : example725GaussNewtonOrbit lam x0 = fun _ : ℕ ↦ x0 := by
      funext n
      exact horbit_const n
    have hconst_zero : Filter.Tendsto (fun _ : ℕ ↦ x0) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [hconst] using hTendsto
    have hx0_eq : (0 : ℝ) = x0 := tendsto_nhds_unique hconst_zero tendsto_const_nhds
    exact hx0_ne hx0_eq.symm
  · let g : ℝ → ℝ := example725GaussNewtonStep lam
    let h : ℝ → ℝ := fun x ↦ g (g x) - x
    let product : ℝ → ℝ := fun x ↦
      example725GaussNewtonMultiplier lam (g x) * example725GaussNewtonMultiplier lam x
    let b : ℝ := -1 / lam
    have hlam_ne : lam ≠ 0 := by
      nlinarith
    have hb_pos : 0 < b := by
      dsimp [b]
      exact div_pos_of_neg_of_neg (by norm_num) (by nlinarith)
    have hlam_sq_gt : 1 < lam ^ (2 : ℕ) := by
      nlinarith
    have hprod_mem : {x : ℝ | 1 < product x} ∈ 𝓝 (0 : ℝ) := by
      exact (example725GaussNewtonTwoStepMultiplier_tendsto lam).eventually (Ioi_mem_nhds hlam_sq_gt)
    rcases Metric.mem_nhds_iff.mp hprod_mem with ⟨δ, hδ_pos, hδsub⟩
    let a : ℝ := min (δ / 2) (b / 2)
    have ha_pos : 0 < a := by
      dsimp [a]
      have hb_half_pos : 0 < b / 2 := by positivity
      positivity
    have ha_lt_b : a < b := by
      dsimp [a]
      have hb_half_lt : b / 2 < b := by nlinarith
      exact lt_of_le_of_lt (min_le_right _ _) hb_half_lt
    have ha_mem_ball : a ∈ Metric.ball (0 : ℝ) δ := by
      -- Pick `a` inside the small neighborhood where the two-step multiplier is `> 1`.
      simp [Metric.mem_ball, Real.dist_eq, abs_of_pos ha_pos]
      dsimp [a]
      have hhalf_lt : δ / 2 < δ := by nlinarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
    have hprod_a_gt : 1 < product a := hδsub ha_mem_ball
    have hga_gt : 0 < h a := by
      -- At the small positive point `a`, the two-step multiplier exceeds `1`.
      dsimp [h, g, product]
      rw [example725GaussNewtonStep_iterate_two_eq_mul_multiplierProduct]
      nlinarith [ha_pos, hprod_a_gt]
    have hg_b :
        g b = -(2 * lam + 1) / (2 * lam) := by
      -- The special endpoint `b = -1 / λ` simplifies the first Gauss-Newton step.
      dsimp [g, b]
      rw [example725GaussNewtonStep_eq]
      field_simp [hlam_ne]
      ring_nf
    have hh_b :
        h b = -((2 * lam - 1) * (2 * lam ^ (2 : ℕ) + lam + 2)) /
          (2 * lam * (4 * lam ^ (2 : ℕ) + 1)) := by
      -- Evaluating the two-step deviation at `b = -1 / λ` gives an explicit negative quantity.
      dsimp [h, b]
      have hg_b' : g (-1 / lam) = -(2 * lam + 1) / (2 * lam) := by
        simpa [b] using hg_b
      rw [hg_b']
      dsimp [g]
      rw [example725GaussNewtonStep_eq]
      field_simp [hlam_ne]
      ring_nf
    have hh_b_lt : h b < 0 := by
      have hquad_pos : 0 < 2 * lam ^ (2 : ℕ) + lam + 2 := by
        nlinarith
      have hnum_neg : (2 * lam - 1) * (2 * lam ^ (2 : ℕ) + lam + 2) < 0 := by
        nlinarith
      have hden_neg : 2 * lam * (4 * lam ^ (2 : ℕ) + 1) < 0 := by
        nlinarith
      rw [hh_b]
      have hneg_num_pos : 0 < -((2 * lam - 1) * (2 * lam ^ (2 : ℕ) + lam + 2)) := by
        nlinarith
      exact div_neg_of_pos_of_neg hneg_num_pos hden_neg
    have hcontStep : Continuous g := by
      have hcont :
          Continuous
            (fun x : ℝ ↦
              (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
                (1 + (2 * lam * x + 1) ^ (2 : ℕ))) := by
        have hnum :
            Continuous
              (fun x : ℝ ↦
                2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) := by
          fun_prop
        have hden : Continuous (fun x : ℝ ↦ 1 + (2 * lam * x + 1) ^ (2 : ℕ)) := by
          fun_prop
        exact hnum.div hden (fun x ↦ example725GaussNewtonDenominator_ne lam x)
      have hg_eq :
          g =
            fun x : ℝ ↦
              (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
                (1 + (2 * lam * x + 1) ^ (2 : ℕ)) := by
        funext x
        simpa [g] using example725GaussNewtonStep_eq lam x
      simpa [hg_eq] using hcont
    have hcontH : Continuous h := by
      -- The two-step deviation is continuous because the one-step map is continuous.
      exact hcontStep.comp hcontStep |>.sub continuous_id
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (h b) (h a) := by
      exact ⟨hh_b_lt.le, hga_gt.le⟩
    have hroot_image : (0 : ℝ) ∈ h '' Set.Icc a b := by
      exact intermediate_value_Icc' ha_lt_b.le hcontH.continuousOn hzero_mem
    rcases hroot_image with ⟨x0, hx0Icc, hx0root⟩
    have hx0_pos : 0 < x0 := lt_of_lt_of_le ha_pos hx0Icc.1
    have hx0_ne : x0 ≠ 0 := ne_of_gt hx0_pos
    have htwoFix : g (g x0) = x0 := by
      dsimp [h] at hx0root
      linarith
    have heven_const : ∀ n : ℕ, example725GaussNewtonOrbit lam x0 (2 * n) = x0 := by
      intro n
      induction n with
      | zero =>
          simp [example725GaussNewtonOrbit, example725GaussNewtonPointOrbit, example725Point]
      | succ n ih =>
          have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by
            omega
          rw [hindex, example725GaussNewtonOrbit_succ, example725GaussNewtonOrbit_succ, ih]
          simpa [g] using htwoFix
    refine ⟨x0, hx0_ne, ?_⟩
    intro hTendsto
    have hEven :
        Filter.Tendsto (fun n : ℕ ↦ 2 * n) Filter.atTop Filter.atTop := by
      have hStrict : StrictMono (fun n : ℕ ↦ 2 * n) := by
        intro m n hmn
        exact Nat.mul_lt_mul_of_pos_left hmn (by decide : 0 < 2)
      exact hStrict.tendsto_atTop
    have hEvenTendsto :
        Filter.Tendsto (fun n : ℕ ↦ example725GaussNewtonOrbit lam x0 (2 * n))
          Filter.atTop (𝓝 (0 : ℝ)) :=
      hTendsto.comp hEven
    have hconstEven : (fun n : ℕ ↦ example725GaussNewtonOrbit lam x0 (2 * n)) = fun _ : ℕ ↦ x0 := by
      funext n
      exact heven_const n
    have hconst_zero : Filter.Tendsto (fun _ : ℕ ↦ x0) Filter.atTop (𝓝 (0 : ℝ)) := by
      convert hEvenTendsto using 1
      exact hconstEven.symm
    have hx0_eq : (0 : ℝ) = x0 := tendsto_nhds_unique hconst_zero tendsto_const_nhds
    exact hx0_ne hx0_eq.symm

/-- Part (1) of Chapter07 Example 7.2.5: for `r₁(x) = x + 1` and
`r₂(x) = λ x^2 + x - 1`, the Gauss-Newton update is
`x ↦ (2 λ^2 x^3 + λ x^2 + 2 λ x) / (1 + (2 λ x + 1)^2)`. -/
theorem example725 :
    ∀ lam x : ℝ,
      example725GaussNewtonStep lam x =
        (2 * lam ^ (2 : ℕ) * x ^ (3 : ℕ) + lam * x ^ (2 : ℕ) + 2 * lam * x) /
          (1 + (2 * lam * x + 1) ^ (2 : ℕ)) := by
  -- This is exactly the explicit scalar formula already proved for the step map.
  intro lam x
  exact example725GaussNewtonStep_eq lam x

/-- Part (2) of Chapter07 Example 7.2.5: when `λ = 0`, the Gauss-Newton method reaches
`x* = 0` in one step. -/
theorem example725_2 :
    ∀ x : ℝ, example725GaussNewtonStep 0 x = 0 := by
  -- The `λ = 0` specialization is the previously established one-step collapse.
  intro x
  exact example725GaussNewtonStep_zero_lam x

/-- Part (3) of Chapter07 Example 7.2.5: near `x = 0`, the Gauss-Newton update satisfies
`x ↦ λ x + O(x^2)`. -/
theorem example725_3 :
    ∀ lam : ℝ,
      (fun x : ℝ ↦ example725GaussNewtonStep lam x - lam * x) =O[𝓝 (0 : ℝ)]
        fun x : ℝ ↦ x ^ (2 : ℕ) := by
  -- Reuse the dedicated quadratic-error theorem verbatim.
  intro lam
  exact example725GaussNewtonStep_isBigOAtZero lam

/-- Part (4) of Chapter07 Example 7.2.5: for sufficiently small `|λ|`, Gauss-Newton
orbits starting sufficiently close to `x* = 0` have a linear convergence rate. -/
theorem example725_4 :
    ∃ ε : Set.Ioi (0 : ℝ),
      ∀ {lam : ℝ}, |lam| < (ε : ℝ) →
        ∃ δ : Set.Ioi (0 : ℝ), ∃ c : Set.Ico (0 : ℝ) 1,
          ∀ {x0 : ℝ}, |x0| < (δ : ℝ) →
            ∀ᶠ n in Filter.atTop,
              |example725GaussNewtonOrbit lam x0 (n + 1)| ≤
                (c : ℝ) * |example725GaussNewtonOrbit lam x0 n| := by
  -- The public wrapper is exactly the explicit small-`|λ|` linear-rate theorem.
  exact example725GaussNewtonOrbit_eventually_linearRate_for_small_abs

/-- Restatement of Chapter07 Example 7.2.5 (5): when `|λ| > 1`, the Gauss-Newton method can
fail to converge to `x* = 0` from a nonzero starting value. -/
theorem example725_5 :
    ∀ {lam : ℝ}, 1 < |lam| →
      ∃ x0 : ℝ, x0 ≠ 0 ∧
        ¬ Filter.Tendsto (example725GaussNewtonOrbit lam x0) Filter.atTop (𝓝 (0 : ℝ)) := by
  -- Forward the statement to the dedicated repelling-orbit theorem.
  intro lam hlam
  exact example725GaussNewtonOrbit_notTendsto_zero_of_one_lt_abs hlam

/-- The derivative of the Example 7.2.5 Gauss-Newton update at `x = 0` is `λ`. -/
theorem example725GaussNewtonStep_hasDerivAt_zero (lam : ℝ) :
    HasDerivAt (example725GaussNewtonStep lam) lam 0 := by
  have hzero : example725GaussNewtonStep lam 0 = 0 :=
    example725GaussNewtonStep_isFixedPt_zero lam
  have hError :
      (fun x : ℝ ↦ example725GaussNewtonStep lam x - example725GaussNewtonStep lam 0 - (x - 0) * lam)
        =O[𝓝 (0 : ℝ)] fun x : ℝ ↦ x ^ (2 : ℕ) := by
    -- Recenter the big-O statement at the fixed point `x* = 0`.
    simpa [hzero, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using
      example725GaussNewtonStep_isBigOAtZero lam
  have hLittle :
      (fun x : ℝ ↦ example725GaussNewtonStep lam x - example725GaussNewtonStep lam 0 - (x - 0) * lam)
        =o[𝓝 (0 : ℝ)] fun x : ℝ ↦ x - 0 := by
    -- Compose the quadratic error estimate with the standard `x^2 = o(x)` fact.
    simpa using hError.trans_isLittleO (isLittleO_pow_id (by norm_num : (1 : ℕ) < 2))
  exact HasDerivAt.of_isLittleO hLittle

end

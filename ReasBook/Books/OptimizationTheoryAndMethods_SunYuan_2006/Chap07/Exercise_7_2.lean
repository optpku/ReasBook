/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Notation_7_1_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

open Matrix

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced mathlib's canonical `gradient` API.
-- Local repository precedent already exposes the Chapter 7 least-squares owners
-- `nonlinearLeastSquaresObjective`, `leastSquaresGradient`, `gaussNewtonNormalMatrix`,
-- `leastSquaresCorrectionMatrix`, and `leastSquaresHessianMatrix`. This exercise therefore keeps
-- the concrete residual/Jacobian/matrix data explicit while bridging its labeled formulas to that
-- canonical nonlinear least-squares API.

local notation "Point" => EuclideanSpace ℝ (Fin 3)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin 5)

/-- The residual vector `(r₁(x), ..., r₅(x))` from Exercise 7.2. -/
def exercise72ResidualVector (x : Point) : ResidualVector :=
  WithLp.toLp 2 <|
    ![
      x 0 ^ (2 : ℕ) + x 1 ^ (2 : ℕ) + x 2 ^ (2 : ℕ) - 1,
      x 0 ^ (2 : ℕ) + x 1 ^ (2 : ℕ) + (x 2 - 2) ^ (2 : ℕ) - 1,
      x 0 + x 1 + x 2 - 1,
      x 0 + x 1 - x 2 + 1,
      x 0 ^ (3 : ℕ) + 3 * x 1 ^ (2 : ℕ) + (5 * x 2 - x 0 + 1) ^ (2 : ℕ) - 36
    ]

/-- The nonlinear least-squares objective `f(x) = (1 / 2) * ‖r(x)‖^2` from Exercise 7.2. -/
def exercise72Objective (x : Point) : ℝ :=
  nonlinearLeastSquaresObjective exercise72ResidualVector x

/-- The Jacobian matrix `J(x)` of the residual map in Exercise 7.2. -/
def exercise72JacobianMatrix (x : Point) : Matrix (Fin 5) (Fin 3) ℝ :=
  !![
    (2 * x 0 : ℝ), 2 * x 1, 2 * x 2;
    (2 * x 0 : ℝ), 2 * x 1, 2 * (x 2 - 2);
    (1 : ℝ), 1, 1;
    (1 : ℝ), 1, -1;
    3 * x 0 ^ (2 : ℕ) - 2 * (5 * x 2 - x 0 + 1), 6 * x 1, 10 * (5 * x 2 - x 0 + 1)
  ]

/-- The explicit gradient formula `J(x)ᵀ r(x)` for the objective in Exercise 7.2. -/
def exercise72GradientVector (x : Point) : Point :=
  let r := exercise72ResidualVector x
  WithLp.toLp 2 <|
    ![
      2 * x 0 * r 0 + 2 * x 0 * r 1 + r 2 + r 3 +
        (3 * x 0 ^ (2 : ℕ) - 2 * (5 * x 2 - x 0 + 1)) * r 4,
      2 * x 1 * r 0 + 2 * x 1 * r 1 + r 2 + r 3 + (6 * x 1) * r 4,
      2 * x 2 * r 0 + 2 * (x 2 - 2) * r 1 + r 2 - r 3 + 10 * (5 * x 2 - x 0 + 1) * r 4
    ]

/-- The explicit matrix `J(x)ᵀ J(x)` computed from the Jacobian in Exercise 7.2. -/
def exercise72NormalMatrix (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  let a := x 0
  let b := x 1
  let c := x 2
  let g₁ := 3 * a ^ (2 : ℕ) - 2 * (5 * c - a + 1)
  let g₃ := 10 * (5 * c - a + 1)
  !![
    (2 * a) ^ (2 : ℕ) + (2 * a) ^ (2 : ℕ) + 1 + 1 + g₁ ^ (2 : ℕ),
    (2 * a) * (2 * b) + (2 * a) * (2 * b) + 1 + 1 + g₁ * (6 * b),
    (2 * a) * (2 * c) + (2 * a) * (2 * (c - 2)) + 1 - 1 + g₁ * g₃;
    (2 * a) * (2 * b) + (2 * a) * (2 * b) + 1 + 1 + g₁ * (6 * b),
    (2 * b) ^ (2 : ℕ) + (2 * b) ^ (2 : ℕ) + 1 + 1 + (6 * b) ^ (2 : ℕ),
    (2 * b) * (2 * c) + (2 * b) * (2 * (c - 2)) + 1 - 1 + (6 * b) * g₃;
    (2 * a) * (2 * c) + (2 * a) * (2 * (c - 2)) + 1 - 1 + g₁ * g₃,
    (2 * b) * (2 * c) + (2 * b) * (2 * (c - 2)) + 1 - 1 + (6 * b) * g₃,
    (2 * c) ^ (2 : ℕ) + (2 * (c - 2)) ^ (2 : ℕ) + 1 + 1 + g₃ ^ (2 : ℕ)
  ]

/-- The residual-weighted second-derivative correction `∑ rᵢ(x) ∇² rᵢ(x)` for the
nonlinear least-squares Hessian in Exercise 7.2. -/
def exercise72ResidualCorrectionMatrix (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  let r := exercise72ResidualVector x
  r 0 • !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2] +
    r 1 • !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2] +
      r 4 • !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50]

/-- The explicit Hessian matrix `∇² f(x)` of the objective in Exercise 7.2. -/
def exercise72HessianMatrix (x : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  exercise72NormalMatrix x + exercise72ResidualCorrectionMatrix x

/-- The zero point in the ambient `ℝ³` problem of Exercise 7.2. -/
def exercise72ZeroPoint : Point :=
  0

/-- Helper for Chapter07 Exercise 7.2: the Euclidean matrix attached to a point-valued derivative
acts on vectors exactly as that derivative does. -/
private theorem pointDerivativeMatrix_apply_eq_fderiv
    (F : Point → Point) (x v : Point) :
    Matrix.toEuclideanLin
        (LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
          (fderiv ℝ F x).toLinearMap) v =
      fderiv ℝ F x v := by
  -- Reconstruct the derivative map from its matrix in the standard Euclidean basis.
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
          (LinearMap.toMatrix
            (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
            (fderiv ℝ F x).toLinearMap) v =
        (fderiv ℝ F x).toLinearMap v := by
    exact
      congrArg
        (fun L : Point →ₗ[ℝ] Point ↦ L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
          ((fderiv ℝ F x).toLinearMap))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using hToLin

/-- Helper for Chapter07 Exercise 7.2: once a scalar coordinate is `C²` at `x`, its Euclidean
gradient is differentiable there. -/
private theorem explicitGradient_differentiableAt_of_contDiffAt
    (φ : Point → ℝ) (x : Point) (hφ : ContDiffAt ℝ 2 φ x) :
    DifferentiableAt ℝ (gradient φ) x := by
  let e : StrongDual ℝ Point ≃L[ℝ] Point :=
    (InnerProductSpace.toDual ℝ Point).symm.toContinuousLinearEquiv
  -- Differentiate `fderiv` once and then transport that derivative through the Riesz isomorphism.
  have hfd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x := by
    exact
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
        |>.hasFDerivAt
  have hgrad := by
    simpa [gradient, Function.comp, e] using ((e.hasFDerivAt).comp x hfd)
  exact hgrad.differentiableAt

/-- Helper for Chapter07 Exercise 7.2: the `i`-th coordinate projection on `Point` has
Fréchet derivative `PiLp.proj 2 (fun _ : Fin 3 => ℝ) i`. -/
private theorem pointCoord_hasFDerivAt (x : Point) (i : Fin 3) :
    HasFDerivAt
      (fun y : Point ↦ y i)
      (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i : Point →L[ℝ] ℝ) x := by
  simpa using (PiLp.hasFDerivAt_apply (p := 2) x i)

/-- Helper for Chapter07 Exercise 7.2: the square of the `i`-th coordinate has the expected
Fréchet derivative. -/
private theorem pointCoordSq_hasFDerivAt (x : Point) (i : Fin 3) :
    HasFDerivAt
      (fun y : Point ↦ y i ^ (2 : ℕ))
      (((2 : ℝ) * x i) • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i : Point →L[ℝ] ℝ)) x := by
  simpa using (pointCoord_hasFDerivAt x i).pow 2

/-- Helper for Chapter07 Exercise 7.2: the cube of the `i`-th coordinate has the expected
Fréchet derivative. -/
private theorem pointCoordCube_hasFDerivAt (x : Point) (i : Fin 3) :
    HasFDerivAt
      (fun y : Point ↦ y i ^ (3 : ℕ))
      ((3 * x i ^ (2 : ℕ) : ℝ) •
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i : Point →L[ℝ] ℝ)) x := by
  simpa using (pointCoord_hasFDerivAt x i).pow 3

/-- Helper for Chapter07 Exercise 7.2: the affine residual
`y ↦ y.ofLp 0 + y.ofLp 1 + y.ofLp 2 - 1` has constant gradient `![1, 1, 1]`. -/
private theorem exercise72ResidualAffinePlus_gradient_eq :
    gradient (fun y : Point ↦ y 0 + y 1 + y 2 - 1) =
      fun _ : Point ↦ WithLp.toLp 2 ![(1 : ℝ), 1, 1] := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  have hRaw :
      HasFDerivAt
        (fun y : Point ↦ y 0 + y 1 + y 2 - 1)
        (((coord0 + coord1) + coord2)) x := by
    simpa [coord0, coord1, coord2, add_assoc] using
      (((pointCoord_hasFDerivAt x 0).add (pointCoord_hasFDerivAt x 1)).add
        (pointCoord_hasFDerivAt x 2)).sub_const (1 : ℝ)
  -- Route correction: rewrite only the derivative map, not the whole goal, to avoid the old
  -- instance-normalization detour.
  refine hRaw.congr_fderiv ?_
  ext v
  simp [coord0, coord1, coord2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]

/-- Helper for Chapter07 Exercise 7.2: the affine residual
`y ↦ y.ofLp 0 + y.ofLp 1 - y.ofLp 2 + 1` has constant gradient `![1, 1, -1]`. -/
private theorem exercise72ResidualAffineMinus_gradient_eq :
    gradient (fun y : Point ↦ y 0 + y 1 - y 2 + 1) =
      fun _ : Point ↦ WithLp.toLp 2 ![(1 : ℝ), 1, -1] := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  have hBaseRaw :
      HasFDerivAt
        (((fun y : Point ↦ y 0) + fun y : Point ↦ y 1) - fun y : Point ↦ y 2)
        ((coord0 + coord1) - coord2) x := by
    exact ((pointCoord_hasFDerivAt x 0).add (pointCoord_hasFDerivAt x 1)).sub
      (pointCoord_hasFDerivAt x 2)
  have hBase :
      HasFDerivAt
        (fun y : Point ↦ (y 0 + y 1) - y 2)
        ((coord0 + coord1) - coord2) x := by
    refine hBaseRaw.congr_of_eventuallyEq ?_
    exact Filter.EventuallyEq.of_eq (by
      funext y
      rfl)
  have hRaw :
      HasFDerivAt
        (fun y : Point ↦ y 0 + y 1 - y 2 + 1)
        ((coord0 + coord1) - coord2) x := by
    refine (hBase.add_const (1 : ℝ)).congr_of_eventuallyEq ?_
    exact Filter.EventuallyEq.of_eq (by
      funext y
      ring)
  -- Route correction: keep the scalar derivative witness in the affine normal form and only
  -- replace the target derivative map at the end.
  refine hRaw.congr_fderiv ?_
  ext v
  simp [coord0, coord1, coord2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Helper for Chapter07 Exercise 7.2: the spherical residual
`y ↦ y 0^2 + y 1^2 + y 2^2 - 1` has gradient `![2 y 0, 2 y 1, 2 y 2]`. -/
private theorem exercise72ResidualSphere_gradient_eq :
    gradient (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1) =
      fun y : Point ↦ WithLp.toLp 2 ![(2 : ℝ) * y 0, 2 * y 1, 2 * y 2] := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  have hRaw :
      HasFDerivAt
        (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1)
        ((((2 * x 0 : ℝ) • coord0) + (2 * x 1 : ℝ) • coord1) + (2 * x 2 : ℝ) • coord2) x := by
    -- Differentiate the three quadratic coordinates before comparing with the Euclidean gradient.
    simpa [coord0, coord1, coord2, add_assoc] using
      (((pointCoordSq_hasFDerivAt x 0).add (pointCoordSq_hasFDerivAt x 1)).add
        (pointCoordSq_hasFDerivAt x 2)).sub_const (1 : ℝ)
  -- Route correction: keep the scalar derivative in coordinate form and only identify the
  -- Euclidean gradient map in the final step.
  refine hRaw.congr_fderiv ?_
  ext v
  simp [coord0, coord1, coord2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring_nf

/-- Helper for Chapter07 Exercise 7.2: the shifted spherical residual
`y ↦ y 0^2 + y 1^2 + (y 2 - 2)^2 - 1` has gradient `![2 y 0, 2 y 1, 2 (y 2 - 2)]`. -/
private theorem exercise72ResidualShiftedSphere_gradient_eq :
    gradient (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1) =
      fun y : Point ↦ WithLp.toLp 2 ![(2 : ℝ) * y 0, 2 * y 1, 2 * (y 2 - 2)] := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  have hRaw :
      HasFDerivAt
        (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1)
        ((((2 * x 0 : ℝ) • coord0) + (2 * x 1 : ℝ) • coord1) +
          (2 * (x 2 - 2) : ℝ) • coord2) x := by
    have hShift :
        HasFDerivAt (fun y : Point ↦ y 2 - 2) coord2 x := by
      -- The shifted third coordinate has the same derivative as the raw coordinate.
      simpa [coord2, sub_eq_add_neg] using (pointCoord_hasFDerivAt x 2).sub_const (2 : ℝ)
    have hShiftSq :
        HasFDerivAt
          (fun y : Point ↦ (y 2 - 2) ^ (2 : ℕ))
          ((2 * (x 2 - 2) : ℝ) • coord2) x := by
      simpa using hShift.pow 2
    simpa [coord0, coord1, coord2, add_assoc] using
      (((pointCoordSq_hasFDerivAt x 0).add (pointCoordSq_hasFDerivAt x 1)).add
        hShiftSq).sub_const (1 : ℝ)
  -- Route correction: compare with the Euclidean gradient only after the shifted-coordinate
  -- derivative is fully normalized.
  refine hRaw.congr_fderiv ?_
  ext v
  simp [coord0, coord1, coord2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring_nf

/-- Helper for Chapter07 Exercise 7.2: the polynomial residual
`y ↦ y 0^3 + 3 y 1^2 + (5 y 2 - y 0 + 1)^2 - 36` has the displayed gradient field. -/
private theorem exercise72ResidualPolynomial_gradient_eq :
    gradient (fun y : Point ↦
      y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36) =
      fun y : Point ↦
        WithLp.toLp 2 <|
          ![
            3 * y 0 ^ (2 : ℕ) + 2 * y 0 - 10 * y 2 - 2,
            6 * y 1,
            50 * y 2 - 10 * y 0 + 10
          ] := by
  apply gradient_eq
  intro x
  rw [hasGradientAt_iff_hasFDerivAt]
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  have hRaw :
      HasFDerivAt
        (fun y : Point ↦
          y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
        ((((3 * x 0 ^ (2 : ℕ) - 2 * (5 * x 2 - x 0 + 1) : ℝ) • coord0) +
            (6 * x 1 : ℝ) • coord1) +
          (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2) x := by
    have hLinear :
        HasFDerivAt
          (fun y : Point ↦ 5 * y 2 - y 0 + 1)
          (((5 : ℝ) • coord2) - coord0) x := by
      have hBase :
          HasFDerivAt
            (fun y : Point ↦ 5 * y 2 - y 0)
            (((5 : ℝ) • coord2) - coord0) x := by
        exact ((pointCoord_hasFDerivAt x 2).const_mul (5 : ℝ)).sub
          (pointCoord_hasFDerivAt x 0)
      refine (hBase.add_const (1 : ℝ)).congr_of_eventuallyEq ?_
      exact Filter.EventuallyEq.of_eq (by
        funext y
        ring)
    have hLinearSq :
        HasFDerivAt
          (fun y : Point ↦ (5 * y 2 - y 0 + 1) ^ (2 : ℕ))
          ((-(2 * (5 * x 2 - x 0 + 1) : ℝ)) • coord0 +
            (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2) x := by
      have hRawSq :
          HasFDerivAt
            (fun y : Point ↦ (5 * y 2 - y 0 + 1) ^ (2 : ℕ))
            (((2 * (5 * x 2 - x 0) + 2 : ℝ)) • (((5 : ℝ) • coord2) - coord0)) x := by
        simpa [two_mul, mul_add, add_assoc, add_left_comm, add_comm] using hLinear.pow 2
      refine hRawSq.congr_fderiv ?_
      ext v
      simp [coord0, coord2, sub_eq_add_neg]
      ring
    have hY1 :
        HasFDerivAt
          (fun y : Point ↦ 3 * y 1 ^ (2 : ℕ))
          ((6 * x 1 : ℝ) • coord1) x := by
      have hRawY1 :
          HasFDerivAt
            (fun y : Point ↦ 3 * y 1 ^ (2 : ℕ))
            ((3 : ℝ) • ((2 * x 1 : ℝ) • coord1)) x := by
        simpa using (pointCoordSq_hasFDerivAt x 1).const_mul (3 : ℝ)
      refine hRawY1.congr_fderiv ?_
      ext v
      simp [coord1]
      ring
    have hBase :
        HasFDerivAt
          (fun y : Point ↦
            y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
          (((3 * x 0 ^ (2 : ℕ) : ℝ) • coord0 + (6 * x 1 : ℝ) • coord1) +
            ((-(2 * (5 * x 2 - x 0 + 1) : ℝ)) • coord0 +
              (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2)) x := by
      -- Combine the cubic, quadratic, and shifted-square pieces before simplifying the final row.
      simpa [add_assoc] using
        (((pointCoordCube_hasFDerivAt x 0).add hY1).add hLinearSq).sub_const (36 : ℝ)
    refine hBase.congr_fderiv ?_
    ext v
    simp [coord0, coord1, coord2, sub_eq_add_neg]
    ring
  -- Route correction: reduce the polynomial gradient to a single coordinate derivative witness.
  refine hRaw.congr_fderiv ?_
  ext v
  simp [coord0, coord1, coord2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Helper for Chapter07 Exercise 7.2: the spherical gradient field has constant derivative
equal to the `2 I` matrix. -/
private theorem exercise72ResidualSphereGradient_hasFDerivAt (x : Point) :
    HasFDerivAt
      (fun y : Point ↦ WithLp.toLp 2 ![(2 : ℝ) * y 0, 2 * y 1, 2 * y 2])
      ((Matrix.toEuclideanLin !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]).toContinuousLinearMap) x := by
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  -- Differentiate the displayed vector field coordinatewise.
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 0) ((2 : ℝ) • coord0) x := by
      simpa [coord0] using (pointCoord_hasFDerivAt x 0).const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 1) ((2 : ℝ) • coord1) x := by
      simpa [coord1] using (pointCoord_hasFDerivAt x 1).const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord1, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 2) ((2 : ℝ) • coord2) x := by
      simpa [coord2] using (pointCoord_hasFDerivAt x 2).const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord2, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

/-- Helper for Chapter07 Exercise 7.2: the shifted spherical gradient field still has constant
derivative `2 I`. -/
private theorem exercise72ResidualShiftedSphereGradient_hasFDerivAt (x : Point) :
    HasFDerivAt
      (fun y : Point ↦ WithLp.toLp 2 ![(2 : ℝ) * y 0, 2 * y 1, 2 * (y 2 - 2)])
      ((Matrix.toEuclideanLin !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]).toContinuousLinearMap) x := by
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  -- Differentiate the shifted-coordinate vector field coordinatewise.
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 0) ((2 : ℝ) • coord0) x := by
      simpa [coord0] using (pointCoord_hasFDerivAt x 0).const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 1) ((2 : ℝ) • coord1) x := by
      simpa [coord1] using (pointCoord_hasFDerivAt x 1).const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord1, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  ·
    have hShift :
        HasFDerivAt (fun y : Point ↦ y 2 - 2) coord2 x := by
      simpa [coord2, sub_eq_add_neg] using (pointCoord_hasFDerivAt x 2).sub_const (2 : ℝ)
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (2 : ℝ) * (y 2 - 2)) ((2 : ℝ) • coord2) x := by
      simpa [two_mul] using hShift.const_mul (2 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord2, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]

/-- Helper for Chapter07 Exercise 7.2: differentiating the polynomial residual gradient gives the
displayed residual Hessian matrix. -/
private theorem exercise72ResidualPolynomialGradient_hasFDerivAt (x : Point) :
    HasFDerivAt
      (fun y : Point ↦
        WithLp.toLp 2 <|
          ![
            3 * y 0 ^ (2 : ℕ) + 2 * y 0 - 10 * y 2 - 2,
            6 * y 1,
            50 * y 2 - 10 * y 0 + 10
          ])
      ((Matrix.toEuclideanLin
        !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50]).toContinuousLinearMap) x := by
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ 3 * y 0 ^ (2 : ℕ) + 2 * y 0 - 10 * y 2 - 2)
          (((6 * x 0 + 2 : ℝ) • coord0) - (10 : ℝ) • coord2) x := by
      have hSquare :
          HasFDerivAt
            (fun y : Point ↦ 3 * y 0 ^ (2 : ℕ))
            ((6 * x 0 : ℝ) • coord0) x := by
        have hRawSq :
            HasFDerivAt
              (fun y : Point ↦ 3 * y 0 ^ (2 : ℕ))
              ((3 : ℝ) • ((2 * x 0 : ℝ) • coord0)) x := by
          simpa using (pointCoordSq_hasFDerivAt x 0).const_mul (3 : ℝ)
        refine hRawSq.congr_fderiv ?_
        ext v
        simp [coord0]
        ring
      have hCoord0 :
          HasFDerivAt (fun y : Point ↦ (2 : ℝ) * y 0) ((2 : ℝ) • coord0) x := by
        simpa [two_mul, coord0] using (pointCoord_hasFDerivAt x 0).const_mul (2 : ℝ)
      have hCoord2 :
          HasFDerivAt (fun y : Point ↦ (10 : ℝ) * y 2) ((10 : ℝ) • coord2) x := by
        simpa [coord2] using (pointCoord_hasFDerivAt x 2).const_mul (10 : ℝ)
      have hBaseRaw :
            HasFDerivAt
            (fun y : Point ↦ 3 * y 0 ^ (2 : ℕ) + (2 : ℝ) * y 0 - (10 : ℝ) * y 2 - 2)
            ((2 : ℝ) • coord0 + ((6 * x 0 : ℝ) • coord0 + -(10 : ℝ) • coord2)) x := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          ((hSquare.add hCoord0).sub hCoord2).sub_const (2 : ℝ)
      refine hBaseRaw.congr_fderiv ?_
      ext v
      simp [coord0, coord2, sub_eq_add_neg]
      ring
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord2, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_three, sub_eq_add_neg]
  ·
    have hRaw :
        HasFDerivAt (fun y : Point ↦ (6 : ℝ) * y 1) ((6 : ℝ) • coord1) x := by
      simpa [coord1] using (pointCoord_hasFDerivAt x 1).const_mul (6 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord1, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_three]
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ 50 * y 2 - 10 * y 0 + 10)
          (((50 : ℝ) • coord2) - (10 : ℝ) • coord0) x := by
      have hCoord2 :
          HasFDerivAt (fun y : Point ↦ (50 : ℝ) * y 2) ((50 : ℝ) • coord2) x := by
        simpa [coord2] using (pointCoord_hasFDerivAt x 2).const_mul (50 : ℝ)
      have hCoord0 :
          HasFDerivAt (fun y : Point ↦ (10 : ℝ) * y 0) ((10 : ℝ) • coord0) x := by
        simpa [coord0] using (pointCoord_hasFDerivAt x 0).const_mul (10 : ℝ)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (hCoord2.sub hCoord0).add_const (10 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord2, Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct,
      Fin.sum_univ_three, sub_eq_add_neg]
    ring

/-- Helper for Chapter07 Exercise 7.2: the residual map has derivative given by the displayed
Jacobian matrix. -/
private theorem exercise72Residual_hasFDerivAt (x : Point) :
    HasFDerivAt exercise72ResidualVector
      ((Matrix.toEuclideanLin (exercise72JacobianMatrix x)).toContinuousLinearMap) x := by
  -- The displayed Jacobian is exactly the derivative obtained by differentiating each residual
  -- coordinate and then repackaging the result on Euclidean space.
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 1
  let coord2 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1)
          ((((2 * x 0 : ℝ) • coord0) + (2 * x 1 : ℝ) • coord1) + (2 * x 2 : ℝ) • coord2) x := by
      simpa [coord0, coord1, coord2, add_assoc] using
        (((pointCoordSq_hasFDerivAt x 0).add (pointCoordSq_hasFDerivAt x 1)).add
          (pointCoordSq_hasFDerivAt x 2)).sub_const (1 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord1, coord2, exercise72JacobianMatrix, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1)
          ((((2 * x 0 : ℝ) • coord0) + (2 * x 1 : ℝ) • coord1) +
            (2 * (x 2 - 2) : ℝ) • coord2) x := by
      have hShift :
          HasFDerivAt (fun y : Point ↦ y 2 - 2) coord2 x := by
        simpa [coord2, sub_eq_add_neg] using (pointCoord_hasFDerivAt x 2).sub_const (2 : ℝ)
      have hShiftSq :
          HasFDerivAt
            (fun y : Point ↦ (y 2 - 2) ^ (2 : ℕ))
            ((2 * (x 2 - 2) : ℝ) • coord2) x := by
        simpa using hShift.pow 2
      simpa [coord0, coord1, coord2, add_assoc] using
        (((pointCoordSq_hasFDerivAt x 0).add (pointCoordSq_hasFDerivAt x 1)).add
          hShiftSq).sub_const (1 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord1, coord2, exercise72JacobianMatrix, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ y 0 + y 1 + y 2 - 1)
          (((coord0 + coord1) + coord2)) x := by
      simpa [coord0, coord1, coord2, add_assoc] using
        (((pointCoord_hasFDerivAt x 0).add (pointCoord_hasFDerivAt x 1)).add
          (pointCoord_hasFDerivAt x 2)).sub_const (1 : ℝ)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord1, coord2, exercise72JacobianMatrix, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦ y 0 + y 1 - y 2 + 1)
          ((coord0 + coord1) - coord2) x := by
      have hBaseRaw :
          HasFDerivAt
            (((fun y : Point ↦ y 0) + fun y : Point ↦ y 1) - fun y : Point ↦ y 2)
            ((coord0 + coord1) - coord2) x := by
        exact ((pointCoord_hasFDerivAt x 0).add (pointCoord_hasFDerivAt x 1)).sub
          (pointCoord_hasFDerivAt x 2)
      have hBase :
          HasFDerivAt
            (fun y : Point ↦ (y 0 + y 1) - y 2)
            ((coord0 + coord1) - coord2) x := by
        refine hBaseRaw.congr_of_eventuallyEq ?_
        exact Filter.EventuallyEq.of_eq (by
          funext y
          rfl)
      -- Route correction: keep the affine coordinate in the `(... ) + 1` normal form instead of
      -- asking `convert` to transport through multiple instance spellings.
      refine (hBase.add_const (1 : ℝ)).congr_of_eventuallyEq ?_
      exact Filter.EventuallyEq.of_eq (by
        funext y
        ring)
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord1, coord2, exercise72JacobianMatrix, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]
    ring
  ·
    have hRaw :
        HasFDerivAt
          (fun y : Point ↦
            y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
          ((((3 * x 0 ^ (2 : ℕ) - 2 * (5 * x 2 - x 0 + 1) : ℝ) • coord0) +
              (6 * x 1 : ℝ) • coord1) +
            (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2) x := by
      have hLinear :
          HasFDerivAt
            (fun y : Point ↦ 5 * y 2 - y 0 + 1)
            (((5 : ℝ) • coord2) - coord0) x := by
        have hBase :
            HasFDerivAt
              (fun y : Point ↦ 5 * y 2 - y 0)
              (((5 : ℝ) • coord2) - coord0) x := by
          exact ((pointCoord_hasFDerivAt x 2).const_mul (5 : ℝ)).sub
            (pointCoord_hasFDerivAt x 0)
        refine (hBase.add_const (1 : ℝ)).congr_of_eventuallyEq ?_
        exact Filter.EventuallyEq.of_eq (by
          funext y
          ring)
      have hLinearSq :
          HasFDerivAt
            (fun y : Point ↦ (5 * y 2 - y 0 + 1) ^ (2 : ℕ))
            ((-(2 * (5 * x 2 - x 0 + 1) : ℝ)) • coord0 +
              (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2) x := by
        have hRawSq :
            HasFDerivAt
              (fun y : Point ↦ (5 * y 2 - y 0 + 1) ^ (2 : ℕ))
              (((2 * (5 * x 2 - x 0) + 2 : ℝ)) • (((5 : ℝ) • coord2) - coord0)) x := by
          simpa [two_mul, mul_add, add_assoc, add_left_comm, add_comm] using hLinear.pow 2
        refine hRawSq.congr_fderiv ?_
        ext v
        simp [coord0, coord2, sub_eq_add_neg]
        ring
      have hY1 :
          HasFDerivAt
            (fun y : Point ↦ 3 * y 1 ^ (2 : ℕ))
            ((6 * x 1 : ℝ) • coord1) x := by
        have hRawY1 :
            HasFDerivAt
              (fun y : Point ↦ 3 * y 1 ^ (2 : ℕ))
              ((3 : ℝ) • ((2 * x 1 : ℝ) • coord1)) x := by
          simpa using (pointCoordSq_hasFDerivAt x 1).const_mul (3 : ℝ)
        refine hRawY1.congr_fderiv ?_
        ext v
        simp [coord1]
        ring
      have hBase :
          HasFDerivAt
            (fun y : Point ↦
              y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
            (((3 * x 0 ^ (2 : ℕ) : ℝ) • coord0 + (6 * x 1 : ℝ) • coord1) +
              ((-(2 * (5 * x 2 - x 0 + 1) : ℝ)) • coord0 +
                (10 * (5 * x 2 - x 0 + 1) : ℝ) • coord2)) x := by
        simpa [add_assoc] using
          (((pointCoordCube_hasFDerivAt x 0).add hY1).add hLinearSq).sub_const (36 : ℝ)
      refine hBase.congr_fderiv ?_
      ext v
      simp [coord0, coord1, coord2, sub_eq_add_neg]
      ring
    refine (hRaw.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp [coord0, coord1, coord2, exercise72JacobianMatrix, Matrix.toEuclideanLin,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]

/-- Helper for Chapter07 Exercise 7.2: the canonical residual Jacobian matrix acts as the
Fréchet derivative of the residual map. -/
private theorem exercise72ResidualJacobian_apply_eq_fderiv (x v : Point) :
    Matrix.toEuclideanLin (residualJacobianMatrix exercise72ResidualVector x) v =
      fderiv ℝ exercise72ResidualVector x v := by
  -- Reconstruct the derivative map from its canonical Jacobian matrix in the standard bases.
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
          (residualJacobianMatrix exercise72ResidualVector x) v =
        (fderiv ℝ exercise72ResidualVector x).toLinearMap v := by
    exact
      congrArg
        (fun L : Point →ₗ[ℝ] ResidualVector ↦ L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis)
          ((fderiv ℝ exercise72ResidualVector x).toLinearMap))
  simpa [residualJacobianMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal] using hToLin

/-- Helper for Chapter07 Exercise 7.2: every scalar residual coordinate has differentiable
gradient because each coordinate is a polynomial and hence `C²`. -/
private theorem exercise72ResidualCoordinateGradient_differentiableAt
    (x : Point) (i : Fin 5) :
    DifferentiableAt ℝ
      (gradient (fun y : Point ↦ residualCoords 5 (exercise72ResidualVector y) i)) x := by
  -- Each scalar residual coordinate is a polynomial, so its Euclidean gradient is differentiable.
  fin_cases i
  ·
    simpa [exercise72ResidualVector] using
      explicitGradient_differentiableAt_of_contDiffAt
        (φ := fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1)
        x
        (by fun_prop)
  ·
    simpa [exercise72ResidualVector] using
      explicitGradient_differentiableAt_of_contDiffAt
        (φ := fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1)
        x
        (by fun_prop)
  ·
    simpa [exercise72ResidualVector] using
      explicitGradient_differentiableAt_of_contDiffAt
        (φ := fun y : Point ↦ y 0 + y 1 + y 2 - 1)
        x
        (by fun_prop)
  ·
    simpa [exercise72ResidualVector] using
      explicitGradient_differentiableAt_of_contDiffAt
        (φ := fun y : Point ↦ y 0 + y 1 - y 2 + 1)
        x
        (by fun_prop)
  ·
    simpa [exercise72ResidualVector] using
      explicitGradient_differentiableAt_of_contDiffAt
        (φ := fun y : Point ↦
          y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
        x
        (by fun_prop)

/-- Helper for Chapter07 Exercise 7.2: the residual-coordinate Hessian owner is the Hessian
matrix of the corresponding scalar residual coordinate. -/
private theorem exercise72ResidualCoordinateHessian_eq_hessianMatrixAt
    (x : Point) (i : Fin 5) :
    residualCoordinateHessianMatrix exercise72ResidualVector i x =
      hessianMatrixAt (fun y : Point ↦ residualCoords 5 (exercise72ResidualVector y) i) x := by
  ext a b
  simp [residualCoordinateHessianMatrix, hessianMatrixAt, hessianAt, Matrix.toEuclideanCLM]

/-- Helper for Chapter07 Exercise 7.2: a Hessian matrix is determined by the derivative of the
corresponding gradient field. -/
private theorem hessianMatrixAt_eq_of_gradientHasFDerivAt
    (φ : Point → ℝ) (x : Point) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA :
      HasFDerivAt
        (gradient φ)
        ((Matrix.toEuclideanLin A).toContinuousLinearMap) x) :
    hessianMatrixAt φ x = A := by
  have hEq :
      (Matrix.toEuclideanCLM :
        Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessianMatrixAt φ x) =
        (Matrix.toEuclideanLin A).toContinuousLinearMap := by
    calc
      (Matrix.toEuclideanCLM :
          Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (hessianMatrixAt φ x)
          = fderiv ℝ (gradient φ) x := by
              rw [toEuclideanCLM_hessianMatrixAt, hessianAt]
      _ = (Matrix.toEuclideanLin A).toContinuousLinearMap := by rw [hA.fderiv]
  exact (Matrix.toEuclideanCLM :
    Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point).injective hEq

/-- Helper for Chapter07 Exercise 7.2: each scalar residual coordinate has the displayed
Hessian matrix. -/
private theorem exercise72ResidualCoordinateHessianMatrix_eq
    (x : Point) (i : Fin 5) :
    residualCoordinateHessianMatrix exercise72ResidualVector i x =
      match i with
      | 0 => !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]
      | 1 => !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]
      | 2 => (0 : Matrix (Fin 3) (Fin 3) ℝ)
      | 3 => (0 : Matrix (Fin 3) (Fin 3) ℝ)
      | 4 => !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50] := by
  fin_cases i
  ·
    -- Route correction: identify the first residual Hessian by differentiating its explicit
    -- gradient field instead of reopening the old matrix-to-CLM normalization branch.
    calc
      residualCoordinateHessianMatrix exercise72ResidualVector 0 x
          = hessianMatrixAt
              (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1) x := by
                simpa [exercise72ResidualVector] using
                  exercise72ResidualCoordinateHessian_eq_hessianMatrixAt (x := x) (i := (0 : Fin 5))
      _ = !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2] := by
            have hGrad :
                HasFDerivAt
                  (gradient (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1))
                  ((Matrix.toEuclideanLin !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]).toContinuousLinearMap) x := by
              rw [exercise72ResidualSphere_gradient_eq]
              simpa using exercise72ResidualSphereGradient_hasFDerivAt x
            exact
              hessianMatrixAt_eq_of_gradientHasFDerivAt
                (φ := fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1)
                (x := x)
                (A := !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2])
                hGrad
  ·
    -- The shifted sphere has the same constant second-derivative matrix as the first sphere.
    calc
      residualCoordinateHessianMatrix exercise72ResidualVector 1 x
          = hessianMatrixAt
              (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1) x := by
                simpa [exercise72ResidualVector] using
                  exercise72ResidualCoordinateHessian_eq_hessianMatrixAt (x := x) (i := (1 : Fin 5))
      _ = !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2] := by
            have hGrad :
                HasFDerivAt
                  (gradient (fun y : Point ↦
                    y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1))
                  ((Matrix.toEuclideanLin !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2]).toContinuousLinearMap) x := by
              rw [exercise72ResidualShiftedSphere_gradient_eq]
              simpa using exercise72ResidualShiftedSphereGradient_hasFDerivAt x
            exact
              hessianMatrixAt_eq_of_gradientHasFDerivAt
                (φ := fun y : Point ↦
                  y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1)
                (x := x)
                (A := !![(2 : ℝ), 0, 0; 0, 2, 0; 0, 0, 2])
                hGrad
  ·
    -- The affine residual `y 0 + y 1 + y 2 - 1` has constant gradient, so its Hessian vanishes.
    calc
      residualCoordinateHessianMatrix exercise72ResidualVector 2 x
          = hessianMatrixAt (fun y : Point ↦ y 0 + y 1 + y 2 - 1) x := by
                simpa [exercise72ResidualVector] using
                  exercise72ResidualCoordinateHessian_eq_hessianMatrixAt (x := x) (i := (2 : Fin 5))
      _ = (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
            have hGrad :
                HasFDerivAt
                  (gradient (fun y : Point ↦ y 0 + y 1 + y 2 - 1))
                  ((Matrix.toEuclideanLin (0 : Matrix (Fin 3) (Fin 3) ℝ)).toContinuousLinearMap) x := by
              rw [exercise72ResidualAffinePlus_gradient_eq]
              simpa using
                (hasFDerivAt_const
                  (c := WithLp.toLp 2 ![(1 : ℝ), 1, 1])
                  (x := x))
            exact
              hessianMatrixAt_eq_of_gradientHasFDerivAt
                (φ := fun y : Point ↦ y 0 + y 1 + y 2 - 1)
                (x := x)
                (A := (0 : Matrix (Fin 3) (Fin 3) ℝ))
                hGrad
  ·
    -- The affine residual `y 0 + y 1 - y 2 + 1` also has zero Hessian.
    calc
      residualCoordinateHessianMatrix exercise72ResidualVector 3 x
          = hessianMatrixAt (fun y : Point ↦ y 0 + y 1 - y 2 + 1) x := by
                simpa [exercise72ResidualVector] using
                  exercise72ResidualCoordinateHessian_eq_hessianMatrixAt (x := x) (i := (3 : Fin 5))
      _ = (0 : Matrix (Fin 3) (Fin 3) ℝ) := by
            have hGrad :
                HasFDerivAt
                  (gradient (fun y : Point ↦ y 0 + y 1 - y 2 + 1))
                  ((Matrix.toEuclideanLin (0 : Matrix (Fin 3) (Fin 3) ℝ)).toContinuousLinearMap) x := by
              rw [exercise72ResidualAffineMinus_gradient_eq]
              simpa using
                (hasFDerivAt_const
                  (c := WithLp.toLp 2 ![(1 : ℝ), 1, -1])
                  (x := x))
            exact
              hessianMatrixAt_eq_of_gradientHasFDerivAt
                (φ := fun y : Point ↦ y 0 + y 1 - y 2 + 1)
                (x := x)
                (A := (0 : Matrix (Fin 3) (Fin 3) ℝ))
                hGrad
  ·
    -- The final residual contributes the only nonconstant residual Hessian.
    calc
      residualCoordinateHessianMatrix exercise72ResidualVector 4 x
          = hessianMatrixAt
              (fun y : Point ↦
                y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36) x := by
                simpa [exercise72ResidualVector] using
                  exercise72ResidualCoordinateHessian_eq_hessianMatrixAt (x := x) (i := (4 : Fin 5))
      _ = !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50] := by
            have hGrad :
                HasFDerivAt
                  (gradient (fun y : Point ↦
                    y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36))
                  ((Matrix.toEuclideanLin
                    !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50]).toContinuousLinearMap) x := by
              rw [exercise72ResidualPolynomial_gradient_eq]
              simpa using exercise72ResidualPolynomialGradient_hasFDerivAt x
            exact
              hessianMatrixAt_eq_of_gradientHasFDerivAt
                (φ := fun y : Point ↦
                  y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36)
                (x := x)
                (A := !![(6 * x 0 + 2 : ℝ), 0, -10; 0, 6, 0; -10, 0, 50])
                hGrad

/-- The exercise-specific objective is the Chapter 7 nonlinear least-squares objective
specialized to the Exercise 7.2 residual vector. -/
theorem exercise72Objective_eq_nonlinearLeastSquaresObjective :
    exercise72Objective = nonlinearLeastSquaresObjective exercise72ResidualVector :=
  rfl

/-- Helper for Chapter07 Exercise 7.2: the nonlinear least-squares objective gradient for the
exercise residual map is the canonical vector `J(x)ᵀ r(x)`. -/
private theorem exercise72Objective_gradient_eq_leastSquaresGradient
    (x : Point) :
    gradient exercise72Objective x = leastSquaresGradient exercise72ResidualVector x := by
  have hResidualDiff : DifferentiableAt ℝ exercise72ResidualVector x :=
    (exercise72Residual_hasFDerivAt x).differentiableAt
  -- Route correction: use the public least-squares gradient identity directly once the residual
  -- differentiability bridge is available.
  simpa [exercise72Objective_eq_nonlinearLeastSquaresObjective, leastSquaresGradient] using
    leastSquaresObjective_gradient_eq exercise72ResidualVector x hResidualDiff

/-- The explicit Jacobian matrix is the canonical residual Jacobian specialized to
`exercise72ResidualVector`. -/
theorem exercise72JacobianMatrix_eq_residualJacobianMatrix (x : Point) :
    exercise72JacobianMatrix x = residualJacobianMatrix exercise72ResidualVector x := by
  -- Compare the two Jacobian owners through their actions on arbitrary tangent vectors.
  apply Matrix.toEuclideanLin.injective
  ext v i
  have hcalc :
      Matrix.toEuclideanLin (exercise72JacobianMatrix x) v =
        Matrix.toEuclideanLin (residualJacobianMatrix exercise72ResidualVector x) v := by
    calc
      Matrix.toEuclideanLin (exercise72JacobianMatrix x) v
          = ((Matrix.toEuclideanLin (exercise72JacobianMatrix x)).toContinuousLinearMap) v := by
              rfl
      _ = fderiv ℝ exercise72ResidualVector x v := by
            rw [(exercise72Residual_hasFDerivAt x).fderiv]
      _ = Matrix.toEuclideanLin (residualJacobianMatrix exercise72ResidualVector x) v := by
            symm
            exact exercise72ResidualJacobian_apply_eq_fderiv x v
  exact congrArg (fun z : ResidualVector ↦ z i) hcalc

/-- The explicit gradient vector agrees with the canonical Chapter 7 least-squares gradient. -/
theorem exercise72GradientVector_eq_leastSquaresGradient (x : Point) :
    exercise72GradientVector x = leastSquaresGradient exercise72ResidualVector x := by
  -- Compare the explicit coordinate formula with the matrix product `J(x)ᵀ r(x)`.
  calc
    exercise72GradientVector x
        = Matrix.toEuclideanLin
            ((exercise72JacobianMatrix x).transpose)
            (exercise72ResidualVector x) := by
              ext i
              fin_cases i
              ·
                simp [exercise72GradientVector, exercise72JacobianMatrix, Matrix.toEuclideanLin,
                  Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
              ·
                simp [exercise72GradientVector, exercise72JacobianMatrix, Matrix.toEuclideanLin,
                  Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
              ·
                simp [exercise72GradientVector, exercise72JacobianMatrix, Matrix.toEuclideanLin,
                  Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
                ring
    _ = leastSquaresGradient exercise72ResidualVector x := by
          rw [leastSquaresGradient, ← exercise72JacobianMatrix_eq_residualJacobianMatrix]

/-- The explicit matrix `J(x)ᵀ J(x)` agrees with the canonical Gauss-Newton normal matrix. -/
theorem exercise72NormalMatrix_eq_gaussNewtonNormalMatrix (x : Point) :
    exercise72NormalMatrix x = gaussNewtonNormalMatrix exercise72ResidualVector x := by
  -- Expand both sides entrywise and normalize the resulting finite sums.
  rw [gaussNewtonNormalMatrix_eq, ← exercise72JacobianMatrix_eq_residualJacobianMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [exercise72NormalMatrix, exercise72JacobianMatrix, Matrix.mul_apply, Fin.sum_univ_five] <;>
    ring

/-- The exercise-specific second-derivative correction agrees with the canonical Chapter 7
least-squares correction matrix. -/
theorem exercise72ResidualCorrectionMatrix_eq_leastSquaresCorrectionMatrix (x : Point) :
    exercise72ResidualCorrectionMatrix x =
      leastSquaresCorrectionMatrix exercise72ResidualVector x := by
  -- Only residual coordinates `0`, `1`, and `4` contribute nontrivial Hessian terms.
  rw [leastSquaresCorrectionMatrix]
  simp [exercise72ResidualCorrectionMatrix, exercise72ResidualVector,
    exercise72ResidualCoordinateHessianMatrix_eq, Fin.sum_univ_five]

/-- The explicit Hessian matrix agrees with the canonical Chapter 7 least-squares Hessian matrix. -/
theorem exercise72HessianMatrix_eq_leastSquaresHessianMatrix (x : Point) :
    exercise72HessianMatrix x = leastSquaresHessianMatrix exercise72ResidualVector x := by
  -- Reassemble the exercise-specific Hessian from its Gauss-Newton and correction pieces.
  calc
    exercise72HessianMatrix x
        = exercise72NormalMatrix x + exercise72ResidualCorrectionMatrix x := by
            rfl
    _ = gaussNewtonNormalMatrix exercise72ResidualVector x +
          leastSquaresCorrectionMatrix exercise72ResidualVector x := by
            rw [exercise72NormalMatrix_eq_gaussNewtonNormalMatrix,
              exercise72ResidualCorrectionMatrix_eq_leastSquaresCorrectionMatrix]
    _ = leastSquaresHessianMatrix exercise72ResidualVector x := by
          rw [leastSquaresHessianMatrix, gaussNewtonNormalMatrix_eq]

/-- Gradient formula for Chapter07 Exercise 7.2 (1): the gradient `gradient exercise72Objective x` is the explicit
vector obtained from the nonlinear least-squares formula `J(x)ᵀ r(x)`. -/
theorem exercise72_gradientFormula (x : Point) :
    gradient exercise72Objective x = exercise72GradientVector x := by
  -- Apply the generic least-squares gradient identity and then rewrite to the exercise owner.
  rw [exercise72Objective_gradient_eq_leastSquaresGradient]
  exact (exercise72GradientVector_eq_leastSquaresGradient x).symm

/-- The explicit gradient vector is the standard nonlinear least-squares quantity
`Matrix.toEuclideanLin (J(x)ᵀ) (r(x))`. -/
theorem exercise72GradientVector_eq_jacobianTranspose_mulResidual (x : Point) :
    exercise72GradientVector x =
      Matrix.toEuclideanLin
        ((exercise72JacobianMatrix x).transpose)
        (exercise72ResidualVector x) := by
  -- This is the explicit coordinate spelling of `J(x)ᵀ r(x)`.
  rw [exercise72GradientVector_eq_leastSquaresGradient, leastSquaresGradient]
  simp [exercise72JacobianMatrix_eq_residualJacobianMatrix]

/-- Jacobian Gram formula for Chapter07 Exercise 7.2 (2): the matrix `J(x)ᵀ J(x)` is the explicit matrix
`exercise72NormalMatrix x`. -/
theorem exercise72_jacobianGramFormula (x : Point) :
    (exercise72JacobianMatrix x).transpose * exercise72JacobianMatrix x =
      exercise72NormalMatrix x := by
  -- Reinterpret the explicit Gram matrix through the canonical Gauss-Newton owner.
  calc
    (exercise72JacobianMatrix x).transpose * exercise72JacobianMatrix x
        = (residualJacobianMatrix exercise72ResidualVector x).transpose *
            residualJacobianMatrix exercise72ResidualVector x := by
              rw [exercise72JacobianMatrix_eq_residualJacobianMatrix]
    _ = gaussNewtonNormalMatrix exercise72ResidualVector x := by
          rfl
    _ = exercise72NormalMatrix x := by
          rw [← exercise72NormalMatrix_eq_gaussNewtonNormalMatrix]

/-- Hessian formula for Chapter07 Exercise 7.2 (3): the Hessian of `exercise72Objective` at `x` is the
Gauss-Newton matrix plus the residual-weighted second-derivative correction, viewed as a linear
map by `Matrix.toEuclideanLin`. -/
theorem exercise72_hessianFormula (x : Point) :
    fderiv ℝ (gradient exercise72Objective) x =
      Matrix.toEuclideanLin (exercise72HessianMatrix x) := by
  have hResidualC2 : ContDiffAt ℝ 2 exercise72ResidualVector x := by
    -- Every residual coordinate is polynomial, so the residual map is `C²` at every point.
    rw [contDiffAt_piLp (p := 2)]
    intro i
    fin_cases i
    ·
      simpa [exercise72ResidualVector] using
        (show ContDiffAt ℝ 2
          (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + y 2 ^ (2 : ℕ) - 1) x from by
            fun_prop)
    ·
      simpa [exercise72ResidualVector] using
        (show ContDiffAt ℝ 2
          (fun y : Point ↦ y 0 ^ (2 : ℕ) + y 1 ^ (2 : ℕ) + (y 2 - 2) ^ (2 : ℕ) - 1) x from by
            fun_prop)
    ·
      simpa [exercise72ResidualVector] using
        (show ContDiffAt ℝ 2 (fun y : Point ↦ y 0 + y 1 + y 2 - 1) x from by
          fun_prop)
    ·
      simpa [exercise72ResidualVector] using
        (show ContDiffAt ℝ 2 (fun y : Point ↦ y 0 + y 1 - y 2 + 1) x from by
          fun_prop)
    ·
      simpa [exercise72ResidualVector] using
        (show ContDiffAt ℝ 2
          (fun y : Point ↦
            y 0 ^ (3 : ℕ) + 3 * y 1 ^ (2 : ℕ) + (5 * y 2 - y 0 + 1) ^ (2 : ℕ) - 36) x from by
              fun_prop)
  -- Compare the canonical Hessian owner with the explicit matrix through the public least-squares
  -- Hessian theorem and the exercise-specific matrix identification.
  calc
    fderiv ℝ (gradient exercise72Objective) x
        = Matrix.toEuclideanLin (hessianMatrixAt exercise72Objective x) := by
            ext v i
            have hApply :
                Matrix.toEuclideanLin (hessianMatrixAt exercise72Objective x) v =
                  fderiv ℝ (gradient exercise72Objective) x v := by
              rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
              simpa [hessianAt] using
                congrArg (fun L : Point →L[ℝ] Point ↦ L v)
                  (toEuclideanCLM_hessianMatrixAt exercise72Objective x)
            exact congrArg (fun w : Point ↦ w i) hApply.symm
    _ = Matrix.toEuclideanLin (leastSquaresHessianMatrix exercise72ResidualVector x) := by
          rw [exercise72Objective_eq_nonlinearLeastSquaresObjective]
          simpa using congrArg Matrix.toEuclideanLin
            (leastSquaresObjective_hessianMatrix_eq exercise72ResidualVector x hResidualC2)
    _ = Matrix.toEuclideanLin (exercise72HessianMatrix x) := by
          rw [← exercise72HessianMatrix_eq_leastSquaresHessianMatrix]

/-- Helper for Chapter07 Exercise 7.2: at the ambient zero point, the explicit normal and Hessian
matrices already differ in their `(0, 0)` entries. -/
private theorem exercise72NormalMatrix_ne_hessianMatrix_atZero :
    exercise72NormalMatrix exercise72ZeroPoint ≠ exercise72HessianMatrix exercise72ZeroPoint := by
  intro hEq
  -- Compare the first diagonal entries of the two explicit matrices.
  have h00 :
      (exercise72NormalMatrix exercise72ZeroPoint) 0 0 =
        (exercise72HessianMatrix exercise72ZeroPoint) 0 0 := by
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M 0 0) hEq
  have h00' := h00
  norm_num [exercise72NormalMatrix, exercise72HessianMatrix, exercise72ResidualCorrectionMatrix,
    exercise72ResidualVector, exercise72ZeroPoint] at h00'
  have h00'' : 4 + (-35 : ℝ) * 2 = 0 := by
    simpa using h00'
  linarith

/-- Chapter07 Exercise 7.2 (4): repair note for the source typo. The residuals depend on three
variables, so the book's `x = (0, 0)ᵀ` is interpreted on the dimensionally consistent ambient
point `exercise72ZeroPoint : ℝ³`; at that point, `J(x)ᵀ J(x) = ∇² f(x)` does not hold. -/
theorem exercise72_jacobianGram_ne_hessianAtZero :
    Matrix.toEuclideanLin
        ((exercise72JacobianMatrix exercise72ZeroPoint).transpose *
          exercise72JacobianMatrix exercise72ZeroPoint) ≠
      fderiv ℝ (gradient exercise72Objective) exercise72ZeroPoint := by
  intro hEq
  apply exercise72NormalMatrix_ne_hessianMatrix_atZero
  apply Matrix.toEuclideanLin.injective
  -- Rewrite both linear maps to the exercise's explicit normal and Hessian matrices.
  calc
    Matrix.toEuclideanLin (exercise72NormalMatrix exercise72ZeroPoint)
        = Matrix.toEuclideanLin
            ((exercise72JacobianMatrix exercise72ZeroPoint).transpose *
              exercise72JacobianMatrix exercise72ZeroPoint) := by
              rw [exercise72_jacobianGramFormula]
    _ = fderiv ℝ (gradient exercise72Objective) exercise72ZeroPoint := hEq
    _ = Matrix.toEuclideanLin (exercise72HessianMatrix exercise72ZeroPoint) := by
          exact exercise72_hessianFormula exercise72ZeroPoint

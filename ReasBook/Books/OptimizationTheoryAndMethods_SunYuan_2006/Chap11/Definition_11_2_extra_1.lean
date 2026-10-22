/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

section

variable {nB nN : ℕ}

local notation "PointB" => EuclideanSpace ℝ (Fin nB)
local notation "PointN" => EuclideanSpace ℝ (Fin nN)

-- Domain sampling:
-- * source-facing layer: the reduced-space Lagrangian and reduced-gradient formulas in split
--   coordinates.
-- * core/canonical layer: mathlib's `gradient`, `fderiv`, `LinearMap.toMatrix`, and
--   `Matrix.toEuclideanLin`.
-- * bridge/view layer: the partial gradients and Jacobian blocks on the basic/nonbasic split.

/-- The `x_B`-partial gradient of `f`. -/
abbrev partialGradientB
    (f : PointB → PointN → ℝ) (xB : PointB) (xN : PointN) : PointB :=
  gradient (fun yB : PointB ↦ f yB xN) xB

/-- Unfolding formula for `partialGradientB`. -/
theorem partialGradientB_eq
    (f : PointB → PointN → ℝ) (xB : PointB) (xN : PointN) :
    partialGradientB f xB xN = gradient (fun yB : PointB ↦ f yB xN) xB :=
  rfl

/-- The `x_N`-partial gradient of `f`. -/
abbrev partialGradientN
    (f : PointB → PointN → ℝ) (xB : PointB) (xN : PointN) : PointN :=
  gradient (fun yN : PointN ↦ f xB yN) xN

/-- Unfolding formula for `partialGradientN`. -/
theorem partialGradientN_eq
    (f : PointB → PointN → ℝ) (xB : PointB) (xN : PointN) :
    partialGradientN f xB xN = gradient (fun yN : PointN ↦ f xB yN) xN :=
  rfl

/-- The Jacobian matrix of the basic-variable map `xBMap : x_N ↦ x_B(x_N)`. -/
abbrev basicVariableJacobian
    (xBMap : PointN → PointB) (xN : PointN) : Matrix (Fin nB) (Fin nN) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
    (fderiv ℝ xBMap xN).toLinearMap

/-- Unfolding formula for `basicVariableJacobian`. -/
theorem basicVariableJacobian_eq
    (xBMap : PointN → PointB) (xN : PointN) :
    basicVariableJacobian xBMap xN =
      LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
        (fderiv ℝ xBMap xN).toLinearMap :=
  rfl

/-- The `x_B`-Jacobian matrix of the constraint map `c`. -/
abbrev constraintJacobianB
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) :
    Matrix (Fin nB) (Fin nB) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
    (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB).toLinearMap

/-- Unfolding formula for `constraintJacobianB`. -/
theorem constraintJacobianB_eq
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) :
    constraintJacobianB c xB xN =
      LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
        (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB).toLinearMap :=
  rfl

/-- The `x_N`-Jacobian matrix of the constraint map `c`. -/
abbrev constraintJacobianN
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) :
    Matrix (Fin nB) (Fin nN) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
    (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN).toLinearMap

/-- Unfolding formula for `constraintJacobianN`. -/
theorem constraintJacobianN_eq
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) :
    constraintJacobianN c xB xN =
      LinearMap.toMatrix
        (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
        (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN).toLinearMap :=
  rfl

/-- The reduced objective `x_N ↦ f (x_B(x_N), x_N)`. -/
def reducedObjective
    (f : PointB → PointN → ℝ) (xBMap : PointN → PointB) (xN : PointN) : ℝ :=
  f (xBMap xN) xN

/-- Unfolding formula for `reducedObjective`. -/
theorem reducedObjective_eq
    (f : PointB → PointN → ℝ) (xBMap : PointN → PointB) (xN : PointN) :
    reducedObjective f xBMap xN = f (xBMap xN) xN :=
  rfl

/-- The reduced constraint map `x_N ↦ c (x_B(x_N), x_N)`. -/
def reducedConstraint
    (c : PointB → PointN → PointB) (xBMap : PointN → PointB) (xN : PointN) : PointB :=
  c (xBMap xN) xN

/-- Unfolding formula for `reducedConstraint`. -/
theorem reducedConstraint_eq
    (c : PointB → PointN → PointB) (xBMap : PointN → PointB) (xN : PointN) :
    reducedConstraint c xBMap xN = c (xBMap xN) xN :=
  rfl

/-- The reduced-space Lagrangian
`x_N ↦ reducedObjective f xBMap x_N - ⟪λ, reducedConstraint c xBMap x_N⟫`. -/
def reducedLagrangian
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (lam : PointB) (xBMap : PointN → PointB) (xN : PointN) : ℝ :=
  reducedObjective f xBMap xN - inner ℝ lam (reducedConstraint c xBMap xN)

/-- Unfolding formula for `reducedLagrangian`. -/
theorem reducedLagrangian_eq
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (lam : PointB) (xBMap : PointN → PointB) (xN : PointN) :
    reducedLagrangian f c lam xBMap xN =
      reducedObjective f xBMap xN - inner ℝ lam (reducedConstraint c xBMap xN) :=
  rfl

/-- The reduced gradient at `x_N` is the gradient of the
reduced objective `x_N ↦ f (x_B(x_N), x_N)`, where `xBMap : PointN → PointB` is the basic-variable
map determined by the elimination equations. -/
def reducedGradient
    (f : PointB → PointN → ℝ) (xBMap : PointN → PointB) (xN : PointN) : PointN :=
  gradient (reducedObjective f xBMap) xN

/-- Unfolding formula for `reducedGradient`. -/
theorem reducedGradient_eq
    (f : PointB → PointN → ℝ) (xBMap : PointN → PointB) (xN : PointN) :
    reducedGradient f xBMap xN = gradient (reducedObjective f xBMap) xN :=
  rfl

/-- The multiplier formula `[(∂ cᵀ / ∂ x_B)]⁻¹ * (∂ f / ∂ x_B)` from `(11.2.13)`. -/
def reducedMultiplier
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN) : PointB :=
  Matrix.toEuclideanLin
    ((((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹) : Matrix (Fin nB) (Fin nB) ℝ)
    (partialGradientB f (xBMap xN) xN)

/-- Unfolding formula for `reducedMultiplier`. -/
theorem reducedMultiplier_eq
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN) :
    reducedMultiplier f c xBMap xN =
      Matrix.toEuclideanLin
        ((((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹) :
          Matrix (Fin nB) (Fin nB) ℝ)
        (partialGradientB f (xBMap xN) xN) :=
  rfl

/-- Helper for Chapter11 Definition 11.2-extra-1: pairing against `Aᵀ g_B` is the same as
pairing `g_B` against `A v`. -/
lemma inner_toEuclideanLin_transpose_apply
    (A : Matrix (Fin nB) (Fin nN) ℝ) (gB : PointB) (v : PointN) :
    inner ℝ (Matrix.toEuclideanLin A.transpose gB) v =
      inner ℝ gB (Matrix.toEuclideanLin A v) := by
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin A.transpose) = Matrix.toEuclideanLin A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := A.transpose)).symm
  -- Rewrite the transpose action through the adjoint of `Matrix.toEuclideanLin A.transpose`.
  calc
    inner ℝ (Matrix.toEuclideanLin A.transpose gB) v
        = inner ℝ gB ((Matrix.toEuclideanLin A.transpose).adjoint v) := by
            symm
            simpa using
              (LinearMap.adjoint_inner_right (Matrix.toEuclideanLin A.transpose) gB v)
    _ = inner ℝ gB (Matrix.toEuclideanLin A v) := by
          rw [hadj]

/-- Helper for Chapter11 Definition 11.2-extra-1: the matrix `basicVariableJacobian`
acts by the derivative of the basic-variable map. -/
lemma basicVariableJacobian_apply
    (xBMap : PointN → PointB) (xN : PointN) (v : PointN) :
    Matrix.toEuclideanLin (basicVariableJacobian xBMap xN) v =
      fderiv ℝ xBMap xN v := by
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
          (basicVariableJacobian xBMap xN) v =
        (fderiv ℝ xBMap xN).toLinearMap v := by
    -- Reconstruct the derivative map from its matrix on the Euclidean bases.
    rw [basicVariableJacobian_eq]
    exact
      congrArg
        (fun L : PointN →ₗ[ℝ] PointB => L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
          ((fderiv ℝ xBMap xN).toLinearMap))
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact hToLin

/-- Helper for Chapter11 Definition 11.2-extra-1: the basic constraint Jacobian matrix acts by
the derivative of the `x_B`-slice of the constraint map. -/
lemma constraintJacobianB_apply
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) (v : PointB) :
    Matrix.toEuclideanLin (constraintJacobianB c xB xN) v =
      fderiv ℝ (fun yB : PointB ↦ c yB xN) xB v := by
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
          (constraintJacobianB c xB xN) v =
        (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB).toLinearMap v := by
    -- Reconstruct the basic slice derivative from its Jacobian matrix.
    rw [constraintJacobianB_eq]
    exact
      congrArg
        (fun L : PointB →ₗ[ℝ] PointB => L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
          ((fderiv ℝ (fun yB : PointB ↦ c yB xN) xB).toLinearMap))
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact hToLin

/-- Helper for Chapter11 Definition 11.2-extra-1: the nonbasic constraint Jacobian matrix acts by
the derivative of the `x_N`-slice of the constraint map. -/
lemma constraintJacobianN_apply
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) (v : PointN) :
    Matrix.toEuclideanLin (constraintJacobianN c xB xN) v =
      fderiv ℝ (fun yN : PointN ↦ c xB yN) xN v := by
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
          (constraintJacobianN c xB xN) v =
        (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN).toLinearMap v := by
    -- Reconstruct the nonbasic slice derivative from its Jacobian matrix.
    rw [constraintJacobianN_eq]
    exact
      congrArg
        (fun L : PointN →ₗ[ℝ] PointB => L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
          ((fderiv ℝ (fun yN : PointN ↦ c xB yN) xN).toLinearMap))
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact hToLin

/-- Helper for Chapter11 Definition 11.2-extra-1: composing `Function.uncurry g` with the
basic-variable slice recovers `fun yB ↦ g yB xN`. -/
lemma uncurryCompBasicSlice_eq
    {α : Type*} (g : PointB → PointN → α) (xN : PointN) :
    (Function.uncurry g) ∘ (fun yB : PointB ↦ (yB, xN)) = fun yB ↦ g yB xN := by
  funext yB
  rfl

/-- Helper for Chapter11 Definition 11.2-extra-1: composing `Function.uncurry g` with the
nonbasic-variable slice recovers `fun yN ↦ g xB yN`. -/
lemma uncurryCompNonbasicSlice_eq
    {α : Type*} (g : PointB → PointN → α) (xB : PointB) :
    (Function.uncurry g) ∘ (fun yN : PointN ↦ (xB, yN)) = fun yN ↦ g xB yN := by
  funext yN
  rfl

/-- Helper for Chapter11 Definition 11.2-extra-1: composing `Function.uncurry g` with the
elimination graph `yN ↦ (xBMap yN, yN)` recovers `fun yN ↦ g (xBMap yN) yN`. -/
lemma uncurryCompGraph_eq
    {α : Type*} (g : PointB → PointN → α) (xBMap : PointN → PointB) :
    (Function.uncurry g) ∘ (fun yN : PointN ↦ (xBMap yN, yN)) =
      fun yN ↦ g (xBMap yN) yN := by
  funext yN
  rfl

/-- Helper for Chapter11 Definition 11.2-extra-1: the derivative of `Function.uncurry f`
along a split direction `(u, v)` is the sum of the two partial-gradient pairings. -/
lemma uncurryFDeriv_apply_eq_inner_partialGradients
    (f : PointB → PointN → ℝ) (xB : PointB) (xN : PointN) (u : PointB) (v : PointN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xB, xN)) :
    fderiv ℝ (Function.uncurry f) (xB, xN) (u, v) =
      inner ℝ (partialGradientB f xB xN) u +
        inner ℝ (partialGradientN f xB xN) v := by
  have hBasicSlice :
      HasFDerivAt (fun yB : PointB ↦ f yB xN)
        ((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
          (ContinuousLinearMap.inl ℝ PointB PointN))
        xB := by
    have hInl :
        HasFDerivAt (fun yB : PointB ↦ (yB, xN))
          (ContinuousLinearMap.inl ℝ PointB PointN)
          xB := by
      simpa using (hasFDerivAt_prodMk_left (e₀ := xB) (f₀ := xN))
    -- Normalize the left slice before reading off the derivative on `(u, 0)`.
    simpa [uncurryCompBasicSlice_eq] using
      (hf.hasFDerivAt.comp xB hInl)
  have hNonbasicSlice :
      HasFDerivAt (fun yN : PointN ↦ f xB yN)
        ((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
          (ContinuousLinearMap.inr ℝ PointB PointN))
        xN := by
    -- Normalize the right slice before reading off the derivative on `(0, v)`.
    simpa [uncurryCompNonbasicSlice_eq] using
      (hf.hasFDerivAt.comp xN (hasFDerivAt_prodMk_right (e₀ := xB) (f₀ := xN)))
  have hBasicGrad :
      HasGradientAt (fun yB : PointB ↦ f yB xN) (partialGradientB f xB xN) xB := by
    -- The basic slice gradient is exactly `partialGradientB`.
    simpa [partialGradientB_eq] using hBasicSlice.differentiableAt.hasGradientAt
  have hNonbasicGrad :
      HasGradientAt (fun yN : PointN ↦ f xB yN) (partialGradientN f xB xN) xN := by
    -- The nonbasic slice gradient is exactly `partialGradientN`.
    simpa [partialGradientN_eq] using hNonbasicSlice.differentiableAt.hasGradientAt
  have hBasicEval :
      fderiv ℝ (Function.uncurry f) (xB, xN) (u, 0) =
        inner ℝ (partialGradientB f xB xN) u := by
    -- Evaluating the derivative on `(u, 0)` reduces to the basic slice derivative.
    calc
      fderiv ℝ (Function.uncurry f) (xB, xN) (u, 0)
          = (((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
                (ContinuousLinearMap.inl ℝ PointB PointN)) u) := by
              simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      _ = fderiv ℝ (fun yB : PointB ↦ f yB xN) xB u := by
            rw [← hBasicSlice.fderiv]
      _ = inner ℝ (partialGradientB f xB xN) u := by
            rw [hBasicGrad.hasFDerivAt.fderiv]
            simp [InnerProductSpace.toDual_apply_apply]
  have hNonbasicEval :
      fderiv ℝ (Function.uncurry f) (xB, xN) (0, v) =
        inner ℝ (partialGradientN f xB xN) v := by
    -- Evaluating the derivative on `(0, v)` reduces to the nonbasic slice derivative.
    calc
      fderiv ℝ (Function.uncurry f) (xB, xN) (0, v)
          = (((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
                (ContinuousLinearMap.inr ℝ PointB PointN)) v) := by
              simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      _ = fderiv ℝ (fun yN : PointN ↦ f xB yN) xN v := by
            rw [← hNonbasicSlice.fderiv]
      _ = inner ℝ (partialGradientN f xB xN) v := by
            rw [hNonbasicGrad.hasFDerivAt.fderiv]
            simp [InnerProductSpace.toDual_apply_apply]
  -- Split the product direction into the basic and nonbasic axes.
  calc
    fderiv ℝ (Function.uncurry f) (xB, xN) (u, v)
        = fderiv ℝ (Function.uncurry f) (xB, xN) ((u, 0) + (0, v)) := by
            congr 1
            ext <;> simp
    _ = fderiv ℝ (Function.uncurry f) (xB, xN) (u, 0) +
          fderiv ℝ (Function.uncurry f) (xB, xN) (0, v) := by
            rw [map_add]
    _ = inner ℝ (partialGradientB f xB xN) u +
          inner ℝ (partialGradientN f xB xN) v := by
            rw [hBasicEval, hNonbasicEval]

/-- Helper for Chapter11 Definition 11.2-extra-1: the derivative of `Function.uncurry c`
along a split direction `(u, v)` is the sum of the basic and nonbasic slice derivatives. -/
lemma uncurryConstraintFDeriv_apply_eq_sum
    (c : PointB → PointN → PointB) (xB : PointB) (xN : PointN) (u : PointB) (v : PointN)
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xB, xN)) :
    fderiv ℝ (Function.uncurry c) (xB, xN) (u, v) =
      fderiv ℝ (fun yB : PointB ↦ c yB xN) xB u +
        fderiv ℝ (fun yN : PointN ↦ c xB yN) xN v := by
  have hBasicSlice :
      HasFDerivAt (fun yB : PointB ↦ c yB xN)
        ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
          (ContinuousLinearMap.inl ℝ PointB PointN))
        xB := by
    have hInl :
        HasFDerivAt (fun yB : PointB ↦ (yB, xN))
          (ContinuousLinearMap.inl ℝ PointB PointN)
          xB := by
      simpa using (hasFDerivAt_prodMk_left (e₀ := xB) (f₀ := xN))
    -- Normalize the basic slice before evaluating the product derivative on `(u, 0)`.
    simpa [uncurryCompBasicSlice_eq] using
      (hc.hasFDerivAt.comp xB hInl)
  have hNonbasicSlice :
      HasFDerivAt (fun yN : PointN ↦ c xB yN)
        ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
          (ContinuousLinearMap.inr ℝ PointB PointN))
        xN := by
    -- Normalize the nonbasic slice before evaluating the product derivative on `(0, v)`.
    simpa [uncurryCompNonbasicSlice_eq] using
      (hc.hasFDerivAt.comp xN (hasFDerivAt_prodMk_right (e₀ := xB) (f₀ := xN)))
  have hBasicEval :
      fderiv ℝ (Function.uncurry c) (xB, xN) (u, 0) =
        fderiv ℝ (fun yB : PointB ↦ c yB xN) xB u := by
    -- The left product direction is the basic slice derivative.
    calc
      fderiv ℝ (Function.uncurry c) (xB, xN) (u, 0)
          = (((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
                (ContinuousLinearMap.inl ℝ PointB PointN)) u) := by
              simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      _ = fderiv ℝ (fun yB : PointB ↦ c yB xN) xB u := by
            rw [← hBasicSlice.fderiv]
  have hNonbasicEval :
      fderiv ℝ (Function.uncurry c) (xB, xN) (0, v) =
        fderiv ℝ (fun yN : PointN ↦ c xB yN) xN v := by
    -- The right product direction is the nonbasic slice derivative.
    calc
      fderiv ℝ (Function.uncurry c) (xB, xN) (0, v)
          = (((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
                (ContinuousLinearMap.inr ℝ PointB PointN)) v) := by
              simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      _ = fderiv ℝ (fun yN : PointN ↦ c xB yN) xN v := by
            rw [← hNonbasicSlice.fderiv]
  -- Split the product direction into the two coordinate axes.
  calc
    fderiv ℝ (Function.uncurry c) (xB, xN) (u, v)
        = fderiv ℝ (Function.uncurry c) (xB, xN) ((u, 0) + (0, v)) := by
            congr 1
            ext <;> simp
    _ = fderiv ℝ (Function.uncurry c) (xB, xN) (u, 0) +
          fderiv ℝ (Function.uncurry c) (xB, xN) (0, v) := by
            rw [map_add]
    _ = fderiv ℝ (fun yB : PointB ↦ c yB xN) xB u +
          fderiv ℝ (fun yN : PointN ↦ c xB yN) xN v := by
            rw [hBasicEval, hNonbasicEval]

/-- Helper for Chapter11 Definition 11.2-extra-1: the `x_B` partial gradient of the full-space
Lagrangian is the objective basic partial gradient minus the transposed basic constraint block. -/
lemma lagrangianPartialGradientB_eq
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (lam : PointB) (xB : PointB) (xN : PointN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xB, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xB, xN)) :
    partialGradientB
        (fun yB yN ↦ f yB yN - inner ℝ lam (c yB yN))
        xB
        xN =
      partialGradientB f xB xN -
        Matrix.toEuclideanLin
          (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
          lam := by
  have hObjectiveSlice :
      HasFDerivAt (fun yB : PointB ↦ f yB xN)
        ((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
          (ContinuousLinearMap.inl ℝ PointB PointN))
        xB := by
    have hInl :
        HasFDerivAt (fun yB : PointB ↦ (yB, xN))
          (ContinuousLinearMap.inl ℝ PointB PointN)
          xB := by
      simpa using (hasFDerivAt_prodMk_left (e₀ := xB) (f₀ := xN))
    -- Normalize the objective basic slice before taking its gradient.
    simpa [uncurryCompBasicSlice_eq] using
      (hf.hasFDerivAt.comp xB hInl)
  have hObjectiveGrad :
      HasGradientAt (fun yB : PointB ↦ f yB xN) (partialGradientB f xB xN) xB := by
    -- The objective slice gradient is `partialGradientB`.
    simpa [partialGradientB_eq] using hObjectiveSlice.differentiableAt.hasGradientAt
  have hConstraintSlice :
      HasFDerivAt (fun yB : PointB ↦ c yB xN)
        ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
          (ContinuousLinearMap.inl ℝ PointB PointN))
        xB := by
    have hInl :
        HasFDerivAt (fun yB : PointB ↦ (yB, xN))
          (ContinuousLinearMap.inl ℝ PointB PointN)
          xB := by
      simpa using (hasFDerivAt_prodMk_left (e₀ := xB) (f₀ := xN))
    -- Normalize the constraint basic slice before differentiating the pairing term.
    simpa [uncurryCompBasicSlice_eq] using
      (hc.hasFDerivAt.comp xB hInl)
  have hPairFunction :
      (fun z : PointB ↦ inner ℝ lam z) =
        (((InnerProductSpace.toDual ℝ PointB) lam) : PointB → ℝ) := by
    funext z
    simp [InnerProductSpace.toDual_apply_apply]
  have hPair :
      HasFDerivAt (fun yB : PointB ↦ inner ℝ lam (c yB xN))
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB))
        xB := by
    -- Compose the basic slice of `c` with the fixed linear functional `z ↦ ⟪λ, z⟫`.
    have hLinear :
        HasFDerivAt (fun z : PointB ↦ inner ℝ lam z)
          ((InnerProductSpace.toDual ℝ PointB) lam)
          (c xB xN) := by
      rw [hPairFunction]
      exact (((InnerProductSpace.toDual ℝ PointB) lam) : PointB →L[ℝ] ℝ).hasFDerivAt
    have hSliceDeriv :
        fderiv ℝ (fun yB : PointB ↦ c yB xN) xB =
          (fderiv ℝ (Function.uncurry c) (xB, xN)).comp
            (ContinuousLinearMap.inl ℝ PointB PointN) :=
      hConstraintSlice.fderiv
    have hPairRaw :
        HasFDerivAt (fun yB : PointB ↦ inner ℝ lam (c yB xN))
          (((InnerProductSpace.toDual ℝ PointB) lam).comp
            ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
              (ContinuousLinearMap.inl ℝ PointB PointN)))
          xB := by
      change HasFDerivAt
        (((fun z : PointB ↦ inner ℝ lam z) ∘ fun yB : PointB ↦ c yB xN))
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
            (ContinuousLinearMap.inl ℝ PointB PointN)))
        xB
      exact hLinear.comp xB hConstraintSlice
    simpa [hSliceDeriv, ContinuousLinearMap.comp_assoc] using hPairRaw
  have hPairGrad :
      HasGradientAt
        (fun yB : PointB ↦ inner ℝ lam (c yB xN))
        (Matrix.toEuclideanLin
          (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
          lam)
        xB := by
    -- Identify the derivative of the pairing term with the transpose basic Jacobian block.
    have hDerivative :
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB)) =
          InnerProductSpace.toDual ℝ PointB
            (Matrix.toEuclideanLin
              (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
              lam) := by
      ext u
      calc
        ((((InnerProductSpace.toDual ℝ PointB) lam).comp
            (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB)) u)
            = inner ℝ (fderiv ℝ (fun yB : PointB ↦ c yB xN) xB u) lam := by
                simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
                  real_inner_comm]
        _ = inner ℝ (Matrix.toEuclideanLin (constraintJacobianB c xB xN) u) lam := by
              rw [constraintJacobianB_apply]
        _ = (InnerProductSpace.toDual ℝ PointB
              (Matrix.toEuclideanLin
                (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
                lam)) u := by
              simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
                (inner_toEuclideanLin_transpose_apply
                  (constraintJacobianB c xB xN) lam u).symm
    rw [hDerivative] at hPair
    simpa using hPair.hasGradientAt
  have hLagrangianGrad :
      HasGradientAt
        (fun yB : PointB ↦ f yB xN - inner ℝ lam (c yB xN))
        (partialGradientB f xB xN -
          Matrix.toEuclideanLin
            (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
            lam)
        xB := by
    have hSub :
        HasFDerivAt
          (fun yB : PointB ↦ f yB xN - inner ℝ lam (c yB xN))
          (InnerProductSpace.toDual ℝ PointB (partialGradientB f xB xN) -
            InnerProductSpace.toDual ℝ PointB
              (Matrix.toEuclideanLin
                (((constraintJacobianB c xB xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
                lam))
          xB := by
      -- Differentiate the basic Lagrangian slice as a difference of the objective and pairing.
      exact hObjectiveGrad.hasFDerivAt.sub hPairGrad.hasFDerivAt
    simpa using hSub.hasGradientAt
  -- Convert the gradient identity back to `partialGradientB`.
  simpa [partialGradientB_eq] using hLagrangianGrad.gradient

/-- Helper for Chapter11 Definition 11.2-extra-1: the `x_N` partial gradient of the full-space
Lagrangian is the objective nonbasic partial gradient minus the transposed nonbasic constraint
block. -/
lemma lagrangianPartialGradientN_eq
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (lam : PointB) (xB : PointB) (xN : PointN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xB, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xB, xN)) :
    partialGradientN
        (fun yB yN ↦ f yB yN - inner ℝ lam (c yB yN))
        xB
        xN =
      partialGradientN f xB xN -
        Matrix.toEuclideanLin
          (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
          lam := by
  have hObjectiveSlice :
      HasFDerivAt (fun yN : PointN ↦ f xB yN)
        ((fderiv ℝ (Function.uncurry f) (xB, xN)).comp
          (ContinuousLinearMap.inr ℝ PointB PointN))
        xN := by
    -- Normalize the objective nonbasic slice before taking its gradient.
    simpa [uncurryCompNonbasicSlice_eq] using
      (hf.hasFDerivAt.comp xN (hasFDerivAt_prodMk_right (e₀ := xB) (f₀ := xN)))
  have hObjectiveGrad :
      HasGradientAt (fun yN : PointN ↦ f xB yN) (partialGradientN f xB xN) xN := by
    -- The objective slice gradient is `partialGradientN`.
    simpa [partialGradientN_eq] using hObjectiveSlice.differentiableAt.hasGradientAt
  have hConstraintSlice :
      HasFDerivAt (fun yN : PointN ↦ c xB yN)
        ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
          (ContinuousLinearMap.inr ℝ PointB PointN))
        xN := by
    -- Normalize the constraint nonbasic slice before differentiating the pairing term.
    simpa [uncurryCompNonbasicSlice_eq] using
      (hc.hasFDerivAt.comp xN (hasFDerivAt_prodMk_right (e₀ := xB) (f₀ := xN)))
  have hPairFunction :
      (fun z : PointB ↦ inner ℝ lam z) =
        (((InnerProductSpace.toDual ℝ PointB) lam) : PointB → ℝ) := by
    funext z
    simp [InnerProductSpace.toDual_apply_apply]
  have hPair :
      HasFDerivAt (fun yN : PointN ↦ inner ℝ lam (c xB yN))
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN))
        xN := by
    -- Compose the nonbasic slice of `c` with the fixed linear functional `z ↦ ⟪λ, z⟫`.
    have hLinear :
        HasFDerivAt (fun z : PointB ↦ inner ℝ lam z)
          ((InnerProductSpace.toDual ℝ PointB) lam)
          (c xB xN) := by
      rw [hPairFunction]
      exact (((InnerProductSpace.toDual ℝ PointB) lam) : PointB →L[ℝ] ℝ).hasFDerivAt
    have hSliceDeriv :
        fderiv ℝ (fun yN : PointN ↦ c xB yN) xN =
          (fderiv ℝ (Function.uncurry c) (xB, xN)).comp
            (ContinuousLinearMap.inr ℝ PointB PointN) :=
      hConstraintSlice.fderiv
    have hPairRaw :
        HasFDerivAt (fun yN : PointN ↦ inner ℝ lam (c xB yN))
          (((InnerProductSpace.toDual ℝ PointB) lam).comp
            ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
              (ContinuousLinearMap.inr ℝ PointB PointN)))
          xN := by
      change HasFDerivAt
        (((fun z : PointB ↦ inner ℝ lam z) ∘ fun yN : PointN ↦ c xB yN))
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          ((fderiv ℝ (Function.uncurry c) (xB, xN)).comp
            (ContinuousLinearMap.inr ℝ PointB PointN)))
        xN
      exact hLinear.comp xN hConstraintSlice
    simpa [hSliceDeriv, ContinuousLinearMap.comp_assoc] using hPairRaw
  have hPairGrad :
      HasGradientAt
        (fun yN : PointN ↦ inner ℝ lam (c xB yN))
        (Matrix.toEuclideanLin
          (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
          lam)
        xN := by
    -- Identify the derivative of the pairing term with the transpose nonbasic Jacobian block.
    have hDerivative :
        (((InnerProductSpace.toDual ℝ PointB) lam).comp
          (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN)) =
          InnerProductSpace.toDual ℝ PointN
            (Matrix.toEuclideanLin
              (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
              lam) := by
      ext u
      calc
        ((((InnerProductSpace.toDual ℝ PointB) lam).comp
            (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN)) u)
            = inner ℝ (fderiv ℝ (fun yN : PointN ↦ c xB yN) xN u) lam := by
                simp [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
                  real_inner_comm]
        _ = inner ℝ (Matrix.toEuclideanLin (constraintJacobianN c xB xN) u) lam := by
              rw [constraintJacobianN_apply]
        _ = (InnerProductSpace.toDual ℝ PointN
              (Matrix.toEuclideanLin
                (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
                lam)) u := by
              simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
                (inner_toEuclideanLin_transpose_apply
                  (constraintJacobianN c xB xN) lam u).symm
    rw [hDerivative] at hPair
    simpa using hPair.hasGradientAt
  have hLagrangianGrad :
      HasGradientAt
        (fun yN : PointN ↦ f xB yN - inner ℝ lam (c xB yN))
        (partialGradientN f xB xN -
          Matrix.toEuclideanLin
            (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
            lam)
        xN := by
    have hSub :
        HasFDerivAt
          (fun yN : PointN ↦ f xB yN - inner ℝ lam (c xB yN))
          (InnerProductSpace.toDual ℝ PointN (partialGradientN f xB xN) -
            InnerProductSpace.toDual ℝ PointN
              (Matrix.toEuclideanLin
                (((constraintJacobianN c xB xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
                lam))
          xN := by
      -- Differentiate the nonbasic Lagrangian slice as a difference of the objective and pairing.
      exact hObjectiveGrad.hasFDerivAt.sub hPairGrad.hasFDerivAt
    simpa using hSub.hasGradientAt
  -- Convert the gradient identity back to `partialGradientN`.
  simpa [partialGradientN_eq] using hLagrangianGrad.gradient

/-- Helper for Chapter11 Definition 11.2-extra-1: differentiating the reduced constraint along
the elimination graph gives the untransposed Jacobian relation
`(∂ c / ∂ x_B) * (∂ x_B / ∂ x_N) + (∂ c / ∂ x_N) = 0`. -/
lemma basicVariableConstraintJacobianRelation_untransposed
    (c : PointB → PointN → PointB) (xBMap : PointN → PointB) (xN : PointN)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hConstraint : ∀ᶠ yN in nhds xN, reducedConstraint c xBMap yN = 0) :
    (constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
      constraintJacobianN c (xBMap xN) xN =
        0 := by
  let bN := (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis
  let bB := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis
  let graphMap : PointN → PointB × PointN := fun yN ↦ (xBMap yN, yN)
  have hGraph :
      HasFDerivAt graphMap
        ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN))
        xN := by
    -- Differentiate the elimination graph `yN ↦ (xBMap yN, yN)`.
    change HasFDerivAt (fun yN : PointN ↦ (xBMap yN, yN))
      ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) xN
    exact hxBMap.hasFDerivAt.prodMk (hasFDerivAt_id xN)
  have hGraphDiff : DifferentiableAt ℝ graphMap xN := hGraph.differentiableAt
  have hReducedConstraintFDeriv :
      fderiv ℝ (reducedConstraint c xBMap) xN =
        (fderiv ℝ (Function.uncurry c) (xBMap xN, xN)).comp
          ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) := by
    have hEq : reducedConstraint c xBMap = ((Function.uncurry c) ∘ graphMap) := by
      funext yN
      rfl
    calc
      fderiv ℝ (reducedConstraint c xBMap) xN
          = fderiv ℝ (((Function.uncurry c) ∘ graphMap)) xN := by
              rw [← (Filter.EventuallyEq.of_eq hEq).fderiv_eq]
      _ = (fderiv ℝ (Function.uncurry c) (xBMap xN, xN)).comp
            (fderiv ℝ graphMap xN) := by
            simpa [graphMap] using
              (fderiv_comp (x := xN) (f := graphMap) (g := Function.uncurry c) hc hGraphDiff)
      _ = (fderiv ℝ (Function.uncurry c) (xBMap xN, xN)).comp
            ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) := by
            rw [hGraph.fderiv]
  have hConst :
      HasFDerivAt (reducedConstraint c xBMap) (0 : PointN →L[ℝ] PointB) xN :=
    -- Neighborhood feasibility makes the reduced constraint derivative vanish.
    hasFDerivAt_zero_of_eventually_const (0 : PointB) hConstraint
  -- Convert the derivative identity on the graph into the matrix identity on Jacobian blocks.
  apply (Matrix.toLin bN bB).injective
  ext v i
  have hBasicMap :
      Matrix.toLin bN bB (basicVariableJacobian xBMap xN) v =
        fderiv ℝ xBMap xN v := by
    simpa only [bN, bB, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      basicVariableJacobian_apply xBMap xN v
  have hConstraintBasic :
      Matrix.toLin bB bB (constraintJacobianB c (xBMap xN) xN)
          (Matrix.toLin bN bB (basicVariableJacobian xBMap xN) v) =
        fderiv ℝ (fun yB : PointB ↦ c yB xN) (xBMap xN) (fderiv ℝ xBMap xN v) := by
    rw [hBasicMap]
    simpa only [bB, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      constraintJacobianB_apply c (xBMap xN) xN (fderiv ℝ xBMap xN v)
  have hConstraintNonbasic :
      Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN) v =
        fderiv ℝ (fun yN : PointN ↦ c (xBMap xN) yN) xN v := by
    simpa only [bN, bB, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      constraintJacobianN_apply c (xBMap xN) xN v
  have hZeroApply :
      fderiv ℝ (reducedConstraint c xBMap) xN v = 0 := by
    rw [hConst.fderiv]
    simp
  have hChainApply :
      fderiv ℝ (reducedConstraint c xBMap) xN v =
        fderiv ℝ (fun yB : PointB ↦ c yB xN) (xBMap xN) (fderiv ℝ xBMap xN v) +
          fderiv ℝ (fun yN : PointN ↦ c (xBMap xN) yN) xN v := by
    -- Evaluate the graph derivative through the already proved split-derivative lemma.
    calc
      fderiv ℝ (reducedConstraint c xBMap) xN v
          = fderiv ℝ (Function.uncurry c) (xBMap xN, xN)
              (((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) v) := by
                rw [hReducedConstraintFDeriv]
                simp [ContinuousLinearMap.comp_apply]
      _ = fderiv ℝ (Function.uncurry c) (xBMap xN, xN) (fderiv ℝ xBMap xN v, v) := by
            simp [ContinuousLinearMap.prod_apply]
      _ = fderiv ℝ (fun yB : PointB ↦ c yB xN) (xBMap xN) (fderiv ℝ xBMap xN v) +
            fderiv ℝ (fun yN : PointN ↦ c (xBMap xN) yN) xN v := by
              simpa using
                uncurryConstraintFDeriv_apply_eq_sum
                  c (xBMap xN) xN (fderiv ℝ xBMap xN v) v hc
  have hVec :
      Matrix.toLin bN bB
          ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
            constraintJacobianN c (xBMap xN) xN)
          v =
        0 := by
    have hToLinAdd :
        Matrix.toLin bN bB
            ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
              constraintJacobianN c (xBMap xN) xN) =
          Matrix.toLin bN bB
              ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN) +
            Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN) := by
      exact
        map_add
          (Matrix.toLin bN bB)
          ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN)
          (constraintJacobianN c (xBMap xN) xN)
    have hToLinAddApply :
        Matrix.toLin bN bB
            ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
              constraintJacobianN c (xBMap xN) xN)
            v =
          (Matrix.toLin bN bB
              ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN)) v +
            (Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN)) v := by
      exact congrArg (fun L : PointN →ₗ[ℝ] PointB => L v) hToLinAdd
    calc
      Matrix.toLin bN bB
          ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
            constraintJacobianN c (xBMap xN) xN)
          v
          = (Matrix.toLin bN bB
              ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN)) v +
              (Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN)) v := by
                exact hToLinAddApply
      _ = fderiv ℝ (fun yB : PointB ↦ c yB xN) (xBMap xN) (fderiv ℝ xBMap xN v) +
            fderiv ℝ (fun yN : PointN ↦ c (xBMap xN) yN) xN v := by
              calc
                (Matrix.toLin bN bB
                    ((constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN)) v +
                    (Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN)) v
                    =
                  Matrix.toLin bB bB (constraintJacobianB c (xBMap xN) xN)
                      (Matrix.toLin bN bB (basicVariableJacobian xBMap xN) v) +
                    (Matrix.toLin bN bB (constraintJacobianN c (xBMap xN) xN)) v := by
                      simpa using
                        (Matrix.toLin_mul_apply
                          (v₁ := bN) (v₂ := bB) (v₃ := bB)
                          (constraintJacobianB c (xBMap xN) xN)
                          (basicVariableJacobian xBMap xN)
                          v)
                _ = fderiv ℝ (fun yB : PointB ↦ c yB xN) (xBMap xN) (fderiv ℝ xBMap xN v) +
                      fderiv ℝ (fun yN : PointN ↦ c (xBMap xN) yN) xN v := by
                        rw [hConstraintBasic, hConstraintNonbasic]
      _ = 0 := by
            simpa [hChainApply] using hZeroApply
  simpa using congrArg (fun z : PointB => z i) hVec

/-- The chain-rule expansion `(11.2.8)` for the reduced gradient: it is the `x_N`-partial
gradient plus the transpose Jacobian contribution from the basic-variable map, under the
needed differentiability hypotheses. -/
theorem reducedGradient_eq_partialGradientN_add_basicVariableContribution
    (f : PointB → PointN → ℝ) (xBMap : PointN → PointB) (xN : PointN)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xBMap xN, xN)) :
    reducedGradient f xBMap xN =
      partialGradientN f (xBMap xN) xN +
        Matrix.toEuclideanLin
          (((basicVariableJacobian xBMap xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
          (partialGradientB f (xBMap xN) xN) := by
  let graphMap : PointN → PointB × PointN := fun yN ↦ (xBMap yN, yN)
  have hGraph :
      HasFDerivAt graphMap
        ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN))
        xN := by
    -- Differentiate the elimination graph used in the reduced objective.
    change HasFDerivAt (fun yN : PointN ↦ (xBMap yN, yN))
      ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) xN
    exact hxBMap.hasFDerivAt.prodMk (hasFDerivAt_id xN)
  have hGraphDiff : DifferentiableAt ℝ graphMap xN := hGraph.differentiableAt
  have hReducedObjectiveFDeriv :
      fderiv ℝ (reducedObjective f xBMap) xN =
        (fderiv ℝ (Function.uncurry f) (xBMap xN, xN)).comp
          ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) := by
    have hEq : reducedObjective f xBMap = ((Function.uncurry f) ∘ graphMap) := by
      funext yN
      rfl
    calc
      fderiv ℝ (reducedObjective f xBMap) xN
          = fderiv ℝ (((Function.uncurry f) ∘ graphMap)) xN := by
              rw [← (Filter.EventuallyEq.of_eq hEq).fderiv_eq]
      _ = (fderiv ℝ (Function.uncurry f) (xBMap xN, xN)).comp
            (fderiv ℝ graphMap xN) := by
            simpa [graphMap] using
              (fderiv_comp (x := xN) (f := graphMap) (g := Function.uncurry f) hf hGraphDiff)
      _ = (fderiv ℝ (Function.uncurry f) (xBMap xN, xN)).comp
            ((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) := by
            rw [hGraph.fderiv]
  have hReducedObjectiveDiff : DifferentiableAt ℝ (reducedObjective f xBMap) xN := by
    have hEq : reducedObjective f xBMap = ((Function.uncurry f) ∘ graphMap) := by
      funext yN
      rfl
    have hCompDiff : DifferentiableAt ℝ (((Function.uncurry f) ∘ graphMap)) xN := by
      exact (hf.comp (x := xN) (f := graphMap) hGraphDiff)
    exact hCompDiff.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq.symm)
  have hReducedGrad :
      HasGradientAt (reducedObjective f xBMap) (reducedGradient f xBMap xN) xN := by
    -- The reduced gradient is the gradient of the reduced objective by definition.
    simpa [reducedGradient_eq] using hReducedObjectiveDiff.hasGradientAt
  -- Compare both vectors through their inner-product functionals.
  apply (InnerProductSpace.toDual ℝ PointN).injective
  ext v
  calc
    (InnerProductSpace.toDual ℝ PointN (reducedGradient f xBMap xN)) v
        = fderiv ℝ (reducedObjective f xBMap) xN v := by
            rw [hReducedGrad.hasFDerivAt.fderiv]
    _ = fderiv ℝ (Function.uncurry f) (xBMap xN, xN)
          (((fderiv ℝ xBMap xN).prod (1 : PointN →L[ℝ] PointN)) v) := by
            rw [hReducedObjectiveFDeriv]
            simp [ContinuousLinearMap.comp_apply]
    _ = fderiv ℝ (Function.uncurry f) (xBMap xN, xN) (fderiv ℝ xBMap xN v, v) := by
          simp [ContinuousLinearMap.prod_apply]
    _ = inner ℝ (partialGradientB f (xBMap xN) xN) (fderiv ℝ xBMap xN v) +
          inner ℝ (partialGradientN f (xBMap xN) xN) v := by
            simpa using
              uncurryFDeriv_apply_eq_inner_partialGradients
                f (xBMap xN) xN (fderiv ℝ xBMap xN v) v hf
    _ = inner ℝ
          (Matrix.toEuclideanLin
            (((basicVariableJacobian xBMap xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
            (partialGradientB f (xBMap xN) xN))
          v +
          inner ℝ (partialGradientN f (xBMap xN) xN) v := by
            congr 1
            calc
              inner ℝ (partialGradientB f (xBMap xN) xN) (fderiv ℝ xBMap xN v)
                  = inner ℝ (partialGradientB f (xBMap xN) xN)
                      (Matrix.toEuclideanLin (basicVariableJacobian xBMap xN) v) := by
                        rw [basicVariableJacobian_apply]
              _ = inner ℝ
                    (Matrix.toEuclideanLin
                      (((basicVariableJacobian xBMap xN).transpose) :
                        Matrix (Fin nN) (Fin nB) ℝ)
                      (partialGradientB f (xBMap xN) xN))
                    v := by
                      symm
                      exact inner_toEuclideanLin_transpose_apply
                        (basicVariableJacobian xBMap xN)
                        (partialGradientB f (xBMap xN) xN)
                        v
    _ = (InnerProductSpace.toDual ℝ PointN
          (partialGradientN f (xBMap xN) xN +
            Matrix.toEuclideanLin
              (((basicVariableJacobian xBMap xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
              (partialGradientB f (xBMap xN) xN))) v := by
          simp [InnerProductSpace.toDual_apply_apply, real_inner_comm, add_comm]

/-- If the reduced basic-variable map keeps the constraints satisfied in a neighborhood of
`xN`, then the Jacobian matrices satisfy the transpose relation `(11.2.9)`, under the
needed differentiability hypotheses. -/
theorem basicVariableConstraintJacobianRelation
    (c : PointB → PointN → PointB) (xBMap : PointN → PointB) (xN : PointN)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hConstraint : ∀ᶠ yN in nhds xN, reducedConstraint c xBMap yN = 0) :
    ((basicVariableJacobian xBMap xN).transpose *
        (constraintJacobianB c (xBMap xN) xN).transpose) +
      (constraintJacobianN c (xBMap xN) xN).transpose =
        0 := by
  have hUntransposed :
      (constraintJacobianB c (xBMap xN) xN) * basicVariableJacobian xBMap xN +
        constraintJacobianN c (xBMap xN) xN =
          0 :=
    basicVariableConstraintJacobianRelation_untransposed c xBMap xN hxBMap hc hConstraint
  -- Transpose the untransposed chain-rule relation to reach the source matrix form `(11.2.9)`.
  simpa [Matrix.transpose_add, Matrix.transpose_mul] using congrArg Matrix.transpose hUntransposed

/-- Chapter11 Definition 11.2-extra-1: when the basic-constraint block is nonsingular, the
reduced gradient has the closed
matrix form `(11.2.10)`, assuming the elimination data and objective/constraint maps are
differentiable at the evaluation point. -/
theorem reducedGradient_eq_partialGradientN_sub_constraintTerm
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xBMap xN, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hConstraint : ∀ᶠ yN in nhds xN, reducedConstraint c xBMap yN = 0)
    (hNonsingular : IsUnit ((constraintJacobianB c (xBMap xN) xN).transpose)) :
    reducedGradient f xBMap xN =
      partialGradientN f (xBMap xN) xN -
        Matrix.toEuclideanLin
          ((((constraintJacobianN c (xBMap xN) xN).transpose) *
              ((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹) :
            Matrix (Fin nN) (Fin nB) ℝ)
          (partialGradientB f (xBMap xN) xN) := by
  let constraintB : Matrix (Fin nB) (Fin nB) ℝ :=
    (constraintJacobianB c (xBMap xN) xN).transpose
  let constraintN : Matrix (Fin nN) (Fin nB) ℝ :=
    (constraintJacobianN c (xBMap xN) xN).transpose
  let basicJacT : Matrix (Fin nN) (Fin nB) ℝ :=
    (basicVariableJacobian xBMap xN).transpose
  have hBasicRelation :
      basicJacT * constraintB + constraintN = 0 := by
    simpa [basicJacT, constraintB, constraintN] using
      basicVariableConstraintJacobianRelation c xBMap xN hxBMap hc hConstraint
  have hConstraintBUnit :
      IsUnit constraintB := by
    simpa [constraintB] using hNonsingular
  have hConstraintBDet :
      IsUnit constraintB.det :=
    (Matrix.isUnit_iff_isUnit_det constraintB).mp hConstraintBUnit
  have hBasicSolved :
      basicJacT = -(constraintN * constraintB⁻¹) := by
    have hMulRight :
        (basicJacT * constraintB + constraintN) * constraintB⁻¹ =
          (0 : Matrix (Fin nN) (Fin nB) ℝ) * constraintB⁻¹ := by
      have h :=
        congrArg (fun M : Matrix (Fin nN) (Fin nB) ℝ => M * constraintB⁻¹) hBasicRelation
      simpa using h
    have hExpanded :
        basicJacT * (constraintB * constraintB⁻¹) + constraintN * constraintB⁻¹ = 0 := by
      simpa [Matrix.add_mul, Matrix.mul_assoc, zero_mul]
        using hMulRight
    have hExpanded' :
        basicJacT + constraintN * constraintB⁻¹ = 0 := by
      have hMulId : constraintB * constraintB⁻¹ = 1 := Matrix.mul_nonsing_inv _ hConstraintBDet
      simpa [hMulId] using hExpanded
    exact eq_neg_of_add_eq_zero_left hExpanded'
  -- Substitute the solved transpose Jacobian relation into `(11.2.8)`.
  calc
    reducedGradient f xBMap xN
        = partialGradientN f (xBMap xN) xN +
            Matrix.toEuclideanLin basicJacT (partialGradientB f (xBMap xN) xN) := by
              simpa [basicJacT] using
                reducedGradient_eq_partialGradientN_add_basicVariableContribution
                  f xBMap xN hxBMap hf
    _ = partialGradientN f (xBMap xN) xN +
          Matrix.toEuclideanLin (-(constraintN * constraintB⁻¹))
            (partialGradientB f (xBMap xN) xN) := by
              rw [hBasicSolved]
    _ = partialGradientN f (xBMap xN) xN -
          Matrix.toEuclideanLin (constraintN * constraintB⁻¹)
            (partialGradientB f (xBMap xN) xN) := by
              simp [sub_eq_add_neg]
    _ = partialGradientN f (xBMap xN) xN -
          Matrix.toEuclideanLin
            ((((constraintJacobianN c (xBMap xN) xN).transpose) *
                ((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹) :
              Matrix (Fin nN) (Fin nB) ℝ)
            (partialGradientB f (xBMap xN) xN) := by
              simp [constraintB, constraintN]

/-- If `λ` satisfies the basic-block multiplier equation `(11.2.12)` and the reduced
constraint remains satisfied near `xN`, then the reduced gradient is the `x_N`-gradient of
the reduced-space Lagrangian `(11.2.11)`, under the needed differentiability hypotheses. -/
theorem reducedGradient_eq_reducedLagrangianGradient
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN) (lam : PointB)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xBMap xN, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hConstraint : ∀ᶠ yN in nhds xN, reducedConstraint c xBMap yN = 0)
    (hMultiplier :
      partialGradientB f (xBMap xN) xN =
        Matrix.toEuclideanLin
          (((constraintJacobianB c (xBMap xN) xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
          lam) :
    reducedGradient f xBMap xN =
      gradient (reducedLagrangian f c lam xBMap) xN := by
  -- Record the source hypotheses even though this neighborhood argument only uses feasibility.
  let _ := hxBMap
  let _ := hf
  let _ := hc
  let _ := hMultiplier
  -- The reduced constraint vanishes near `xN`, so the reduced Lagrangian agrees with the
  -- reduced objective there.
  have hEventually :
      reducedLagrangian f c lam xBMap =ᶠ[nhds xN] reducedObjective f xBMap := by
    filter_upwards [hConstraint] with yN hyN
    simp [reducedLagrangian, hyN]
  -- Transport the reduced gradient across this neighborhood equality.
  simpa [reducedGradient_eq] using hEventually.gradient_eq.symm

/-- Helper for Chapter11 Definition 11.2-extra-1: applying the basic-constraint transpose block
to the chosen reduced multiplier recovers `partialGradientB f (x_B(x_N)) x_N`. -/
lemma basicConstraintTranspose_reducedMultiplier_eq_partialGradientB
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN)
    (hNonsingular : IsUnit ((constraintJacobianB c (xBMap xN) xN).transpose)) :
    Matrix.toEuclideanLin
      (((constraintJacobianB c (xBMap xN) xN).transpose) : Matrix (Fin nB) (Fin nB) ℝ)
      (reducedMultiplier f c xBMap xN) =
        partialGradientB f (xBMap xN) xN := by
  let A : Matrix (Fin nB) (Fin nB) ℝ := (constraintJacobianB c (xBMap xN) xN).transpose
  have hAUnit : IsUnit A := by
    simpa [A] using hNonsingular
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAUnit
  rw [reducedMultiplier_eq]
  change Matrix.toEuclideanLin A
      (Matrix.toEuclideanLin A⁻¹ (partialGradientB f (xBMap xN) xN)) =
    partialGradientB f (xBMap xN) xN
  have hCompose :
      Matrix.toEuclideanLin A
          (Matrix.toEuclideanLin A⁻¹ (partialGradientB f (xBMap xN) xN)) =
        Matrix.toEuclideanLin (A * A⁻¹) (partialGradientB f (xBMap xN) xN) := by
    -- Compose the two Euclidean matrix actions before cancelling the inverse.
    simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_mul_apply
        (v₁ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
        (v₂ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
        (v₃ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
        A A⁻¹ (partialGradientB f (xBMap xN) xN)).symm
  rw [hCompose, Matrix.mul_nonsing_inv A hdet]
  simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]

/-- With the multiplier choice `(11.2.13)`, the `x_B`-block of the Lagrangian gradient
vanishes, which is the zero top block in `(11.2.14)`, assuming the objective and constraint
basic partial gradients are represented by the displayed Jacobian blocks. -/
theorem reducedMultiplier_partialGradientB_lagrangian_eq_zero
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xBMap xN, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hNonsingular : IsUnit ((constraintJacobianB c (xBMap xN) xN).transpose)) :
    partialGradientB
        (fun yB yN ↦
          f yB yN - inner ℝ (reducedMultiplier f c xBMap xN) (c yB yN))
        (xBMap xN)
        xN =
      0 := by
  -- Rewrite the basic Lagrangian block and cancel it with the defining multiplier equation.
  rw [lagrangianPartialGradientB_eq
      (f := f)
      (c := c)
      (lam := reducedMultiplier f c xBMap xN)
      (xB := xBMap xN)
      (xN := xN)
      hf
      hc]
  rw [basicConstraintTranspose_reducedMultiplier_eq_partialGradientB f c xBMap xN hNonsingular]
  simp

/-- With the multiplier choice `(11.2.13)`, the `x_N`-block of the Lagrangian gradient is the
reduced gradient, which is the lower block in `(11.2.14)`, under the needed differentiability
hypotheses. -/
theorem reducedMultiplier_partialGradientN_lagrangian_eq_reducedGradient
    (f : PointB → PointN → ℝ) (c : PointB → PointN → PointB)
    (xBMap : PointN → PointB) (xN : PointN)
    (hxBMap : DifferentiableAt ℝ xBMap xN)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (xBMap xN, xN))
    (hc : DifferentiableAt ℝ (Function.uncurry c) (xBMap xN, xN))
    (hConstraint : ∀ᶠ yN in nhds xN, reducedConstraint c xBMap yN = 0)
    (hNonsingular : IsUnit ((constraintJacobianB c (xBMap xN) xN).transpose)) :
    partialGradientN
        (fun yB yN ↦
          f yB yN - inner ℝ (reducedMultiplier f c xBMap xN) (c yB yN))
        (xBMap xN)
        xN =
      reducedGradient f xBMap xN := by
  -- Route correction: compute the fixed-multiplier `x_N` slice directly and rewrite the
  -- correction term with the already proved closed reduced-gradient formula `(11.2.10)`.
  have hCompose :
      Matrix.toEuclideanLin
          (((constraintJacobianN c (xBMap xN) xN).transpose) : Matrix (Fin nN) (Fin nB) ℝ)
          (reducedMultiplier f c xBMap xN) =
        Matrix.toEuclideanLin
          ((((constraintJacobianN c (xBMap xN) xN).transpose) *
              ((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹) :
            Matrix (Fin nN) (Fin nB) ℝ)
          (partialGradientB f (xBMap xN) xN) := by
    rw [reducedMultiplier_eq]
    -- Compose the nonbasic transpose block with the chosen inverse basic block.
    simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      (Matrix.toLin_mul_apply
        (v₁ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
        (v₂ := (EuclideanSpace.basisFun (Fin nB) ℝ).toBasis)
        (v₃ := (EuclideanSpace.basisFun (Fin nN) ℝ).toBasis)
        ((constraintJacobianN c (xBMap xN) xN).transpose)
        (((constraintJacobianB c (xBMap xN) xN).transpose)⁻¹)
        (partialGradientB f (xBMap xN) xN)).symm
  rw [lagrangianPartialGradientN_eq
      (f := f)
      (c := c)
      (lam := reducedMultiplier f c xBMap xN)
      (xB := xBMap xN)
      (xN := xN)
      hf
      hc]
  rw [hCompose]
  rw [reducedGradient_eq_partialGradientN_sub_constraintTerm
      f
      c
      xBMap
      xN
      hxBMap
      hf
      hc
      hConstraint
      hNonsingular]

#print axioms reducedObjective
#print axioms reducedConstraint
#print axioms reducedLagrangian
#print axioms reducedGradient
#print axioms reducedMultiplier

end

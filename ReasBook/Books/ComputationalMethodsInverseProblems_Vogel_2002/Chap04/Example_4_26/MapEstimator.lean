/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_2_2.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_4.QuadraticFunctional
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

open scoped Matrix

namespace LinearGaussian

universe u v

section

variable {m : Type u} {n : Type v}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]

/-- The linear-Gaussian posterior energy in `x` associated to `K`, `C_N`, `C_X`, and the
observation `z`. Minimizing this objective is equivalent to maximizing the posterior
log-likelihood up to an additive constant independent of `x`. -/
def posteriorObjective (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m) :
    EuclideanSpace ℝ n → ℝ :=
  fun x ↦
    (1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin (z - K.toEuclideanLin x))
      (z - K.toEuclideanLin x) +
    (1 / 2 : ℝ) * inner ℝ ((C_X⁻¹).toEuclideanLin x) x

/-- The defining residual-plus-prior formula for `LinearGaussian.posteriorObjective`. -/
theorem posteriorObjective_def (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    posteriorObjective K C_N C_X z x =
      (1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin (z - K.toEuclideanLin x))
        (z - K.toEuclideanLin x) +
      (1 / 2 : ℝ) * inner ℝ ((C_X⁻¹).toEuclideanLin x) x := by
  -- Unfold the objective once to expose the residual and prior terms.
  rfl

/-- For positive-definite noise covariance `C_N`, the posterior energy is the quadratic
functional with matrix part `Kᵀ * C_N⁻¹ * K + C_X⁻¹` and linear term `-Kᵀ * C_N⁻¹ z`. -/
theorem posteriorObjective_eq_quadraticFunctional (K : Matrix m n ℝ)
    (C_N : Matrix m m ℝ) (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m)
    (hCN : C_N.PosDef) :
    posteriorObjective K C_N C_X z =
      QuadraticOptimization.quadraticFunctional
        ((1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin z) z)
        (-Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z)
        (Kᵀ * C_N⁻¹ * K + C_X⁻¹) := by
  funext x
  -- Move the noise precision across the inner product through its adjoint.
  have hKAdj : (K.toEuclideanLin).adjoint = (Kᵀ).toEuclideanLin := by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint K).symm
  have hCNinvSymm : (C_N⁻¹)ᵀ = C_N⁻¹ := by
    simpa using hCN.inv.isHermitian.eq
  have hCNinvAdj :
      ((C_N⁻¹).toEuclideanLin).adjoint = (C_N⁻¹).toEuclideanLin := by
    calc
      ((C_N⁻¹).toEuclideanLin).adjoint = ((C_N⁻¹)ᵀ).toEuclideanLin := by
        simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (C_N⁻¹)).symm
      _ = (C_N⁻¹).toEuclideanLin := by
        rw [hCNinvSymm]
  have hCross :
      inner ℝ ((C_N⁻¹).toEuclideanLin z) (K.toEuclideanLin x) =
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x := by
    calc
      inner ℝ ((C_N⁻¹).toEuclideanLin z) (K.toEuclideanLin x)
          = inner ℝ (((K.toEuclideanLin).adjoint) ((C_N⁻¹).toEuclideanLin z)) x := by
              simpa using
                (LinearMap.adjoint_inner_left
                  (A := K.toEuclideanLin) (x := x) (y := (C_N⁻¹).toEuclideanLin z)).symm
      _ = inner ℝ ((Kᵀ).toEuclideanLin ((C_N⁻¹).toEuclideanLin z)) x := by
            rw [hKAdj]
      _ = inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x := by
            simpa using
              congrArg (fun v ↦ inner ℝ v x) (toEuclideanLin_mul_apply Kᵀ C_N⁻¹ z)
  have hCross' :
      inner ℝ ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x)) z =
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x := by
    calc
      inner ℝ ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x)) z
          = inner ℝ (K.toEuclideanLin x) (((C_N⁻¹).toEuclideanLin).adjoint z) := by
              simpa using
                (LinearMap.adjoint_inner_right
                  (A := (C_N⁻¹).toEuclideanLin) (x := K.toEuclideanLin x) (y := z)).symm
      _ = inner ℝ (K.toEuclideanLin x) ((C_N⁻¹).toEuclideanLin z) := by
            rw [hCNinvAdj]
      _ = inner ℝ ((C_N⁻¹).toEuclideanLin z) (K.toEuclideanLin x) := by
            rw [real_inner_comm]
      _ = inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x := hCross
  have hQuadratic :
      inner ℝ ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x)) (K.toEuclideanLin x) =
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x := by
    calc
      inner ℝ ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x)) (K.toEuclideanLin x)
          = inner ℝ (((K.toEuclideanLin).adjoint)
              ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x))) x := by
              simpa using
                (LinearMap.adjoint_inner_left
                  (A := K.toEuclideanLin) (x := x)
                  (y := (C_N⁻¹).toEuclideanLin (K.toEuclideanLin x))).symm
      _ = inner ℝ ((Kᵀ).toEuclideanLin ((C_N⁻¹).toEuclideanLin (K.toEuclideanLin x))) x := by
            rw [hKAdj]
      _ = inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x := by
            simpa using
              congrArg (fun v ↦ inner ℝ v x)
                (by
                  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
                  rfl)
  have hMatrixPart :
      inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x +
          inner ℝ ((C_X⁻¹).toEuclideanLin x) x =
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K + C_X⁻¹) x) x := by
    -- Assemble the two quadratic pieces into the final precision matrix.
    have hAddApply :
        Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K + C_X⁻¹) x =
          Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x + Matrix.toEuclideanLin C_X⁻¹ x := by
      simp [Matrix.toEuclideanLin_apply, Matrix.add_mulVec]
    calc
      inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x +
          inner ℝ ((C_X⁻¹).toEuclideanLin x) x
          = inner ℝ
              (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x + Matrix.toEuclideanLin C_X⁻¹ x) x := by
                rw [inner_add_left]
      _ = inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K + C_X⁻¹) x) x := by
            rw [← hAddApply]
  -- Expand the residual square, rewrite the two cross terms, and regroup.
  rw [posteriorObjective_def, QuadraticOptimization.quadraticFunctional_def, map_sub,
    inner_sub_left, inner_sub_right, inner_sub_right, hCross, hCross', hQuadratic]
  calc
    (1 / 2 : ℝ) *
        (inner ℝ ((C_N⁻¹).toEuclideanLin z) z -
          inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x -
          (inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x -
            inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x)) +
        (1 / 2 : ℝ) * inner ℝ ((C_X⁻¹).toEuclideanLin x) x
        =
      (1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin z) z -
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x +
        (1 / 2 : ℝ) *
          (inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K) x) x +
            inner ℝ ((C_X⁻¹).toEuclideanLin x) x) := by
          ring
    _ =
      (1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin z) z -
        inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x +
        (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K + C_X⁻¹) x) x := by
          rw [hMatrixPart]
    _ =
      (1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin z) z +
        inner ℝ (-Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z) x +
        (1 / 2 : ℝ) * inner ℝ (Matrix.toEuclideanLin (Kᵀ * C_N⁻¹ * K + C_X⁻¹) x) x := by
          rw [sub_eq_add_neg, ← inner_neg_left]

/-- A vector is a MAP estimator when it minimizes the posterior objective on `Set.univ`. -/
def IsMapEstimator (K : Matrix m n ℝ) (C_N : Matrix m m ℝ) (C_X : Matrix n n ℝ)
    (z : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) : Prop :=
  IsMinOn (posteriorObjective K C_N C_X z) Set.univ x

/-- The defining characterization of `LinearGaussian.IsMapEstimator`. -/
theorem isMapEstimator_iff (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m) (x : EuclideanSpace ℝ n) :
    IsMapEstimator K C_N C_X z x ↔
      IsMinOn (posteriorObjective K C_N C_X z) Set.univ x := by
  -- This is the defining proposition of `IsMapEstimator`.
  rfl

/-- The precision-form linear-Gaussian MAP candidate
`((Kᵀ * C_N⁻¹ * K + C_X⁻¹)⁻¹ * Kᵀ * C_N⁻¹) z`. -/
def precisionEstimator (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m) : EuclideanSpace ℝ n :=
  Matrix.toEuclideanLin ((Kᵀ * C_N⁻¹ * K + C_X⁻¹)⁻¹ * Kᵀ * C_N⁻¹) z

/-- The defining formula for `LinearGaussian.precisionEstimator`. -/
theorem precisionEstimator_eq (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (z : EuclideanSpace ℝ m) :
    precisionEstimator K C_N C_X z =
      Matrix.toEuclideanLin ((Kᵀ * C_N⁻¹ * K + C_X⁻¹)⁻¹ * Kᵀ * C_N⁻¹) z := by
  -- Unfold the explicit precision-form estimator once.
  rfl

/-- Helper for Example 4.26: the posterior precision matrix is positive definite. -/
lemma precisionMatrix_posDef (K : Matrix m n ℝ) (C_N : Matrix m m ℝ)
    (C_X : Matrix n n ℝ) (hCN : C_N.PosDef) (hCX : C_X.PosDef) :
    (Kᵀ * C_N⁻¹ * K + C_X⁻¹).PosDef := by
  -- The data-fit contribution is positive semidefinite after conjugating by `K`.
  have hData : (Kᵀ * C_N⁻¹ * K).PosSemidef := by
    simpa using Matrix.PosSemidef.conjTranspose_mul_mul_same hCN.inv.posSemidef K
  -- Adding the prior precision upgrades the sum to positive definite.
  simpa [add_comm] using hCX.inv.add_posSemidef hData

/-- Example 4.26 (1): for positive-definite noise and prior covariances, the precision-form
vector `((Kᵀ * C_N⁻¹ * K + C_X⁻¹)⁻¹ * Kᵀ * C_N⁻¹) z` is a MAP estimator for the linear-Gaussian
posterior objective. -/
theorem isMapEstimator_precisionEstimator
    (K : Matrix m n ℝ) (C_N : Matrix m m ℝ) (C_X : Matrix n n ℝ)
    (z : EuclideanSpace ℝ m) (hCN : C_N.PosDef) (hCX : C_X.PosDef) :
    IsMapEstimator K C_N C_X z (precisionEstimator K C_N C_X z) := by
  -- Rewrite the posterior objective into the quadratic normal form from Chapter 3.
  rw [isMapEstimator_iff, posteriorObjective_eq_quadraticFunctional K C_N C_X z hCN]
  -- Apply the abstract positive-definite quadratic minimizer theorem.
  simpa [precisionEstimator_eq, toEuclideanLin_mul_apply] using
    (QuadraticOptimization.isMinOn_quadraticFunctional_of_posDef
      ((1 / 2 : ℝ) * inner ℝ ((C_N⁻¹).toEuclideanLin z) z)
      (-Matrix.toEuclideanLin (Kᵀ * C_N⁻¹) z)
      (Kᵀ * C_N⁻¹ * K + C_X⁻¹)
      (precisionMatrix_posDef K C_N C_X hCN hCX))

/-- Helper for Example 4.26: the isotropic precision operator collapses to the
Tikhonov reconstruction operator with parameter `(σN / σX) ^ 2`. -/
lemma isotropicPrecisionOperator_eq_tikhonovOperator
    (K : Matrix m n ℝ) (σN σX : ℝ) (hσN : 0 < σN) (hσX : 0 < σX) :
    ((Kᵀ * (σN ^ 2 • (1 : Matrix m m ℝ))⁻¹ * K + (σX ^ 2 • (1 : Matrix n n ℝ))⁻¹)⁻¹ *
        Kᵀ * (σN ^ 2 • (1 : Matrix m m ℝ))⁻¹) =
      ((Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ))⁻¹ * Kᵀ) := by
  have hσN_sq_ne : σN ^ 2 ≠ 0 := by positivity
  have hσX_sq_ne : σX ^ 2 ≠ 0 := by positivity
  have hα_pos : 0 < (σN / σX) ^ 2 := by positivity
  have hShiftUnit : IsUnit ((Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)).det) := by
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      ((gramianShift_posDef K ((σN / σX) ^ 2) hα_pos).isUnit)
  have hNoiseInv :
      (σN ^ 2 • (1 : Matrix m m ℝ))⁻¹ = (σN ^ 2)⁻¹ • (1 : Matrix m m ℝ) := by
    -- Local instance justification (scalar inverse): `Matrix.inv_smul` needs an
    -- `Invertible` witness for the nonzero scalar `σN ^ 2`.
    letI : Invertible (σN ^ 2) := invertibleOfNonzero hσN_sq_ne
    simpa using
      (Matrix.inv_smul (A := (1 : Matrix m m ℝ)) (k := σN ^ 2) (h := by simpa))
  have hPriorInv :
      (σX ^ 2 • (1 : Matrix n n ℝ))⁻¹ = (σX ^ 2)⁻¹ • (1 : Matrix n n ℝ) := by
    -- Local instance justification (scalar inverse): `Matrix.inv_smul` needs an
    -- `Invertible` witness for the nonzero scalar `σX ^ 2`.
    letI : Invertible (σX ^ 2) := invertibleOfNonzero hσX_sq_ne
    simpa using
      (Matrix.inv_smul (A := (1 : Matrix n n ℝ)) (k := σX ^ 2) (h := by simpa))
  have hScalar :
      (σN ^ 2)⁻¹ * (σN / σX) ^ 2 = (σX ^ 2)⁻¹ := by
    field_simp [hσN_sq_ne, hσX_sq_ne]
  have hFactor :
      Kᵀ * ((σN ^ 2)⁻¹ • (1 : Matrix m m ℝ)) * K + (σX ^ 2)⁻¹ • (1 : Matrix n n ℝ) =
        (σN ^ 2)⁻¹ • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)) := by
    -- Factor the common scalar `(σN ^ 2)⁻¹` out of the isotropic precision matrix.
    calc
      Kᵀ * ((σN ^ 2)⁻¹ • (1 : Matrix m m ℝ)) * K + (σX ^ 2)⁻¹ • (1 : Matrix n n ℝ)
          = (σN ^ 2)⁻¹ • (Kᵀ * K) + (σX ^ 2)⁻¹ • (1 : Matrix n n ℝ) := by
              simp [Matrix.mul_assoc, mul_smul_comm, smul_mul_assoc]
      _ = (σN ^ 2)⁻¹ • (Kᵀ * K) +
            ((σN ^ 2)⁻¹ * (σN / σX) ^ 2) • (1 : Matrix n n ℝ) := by
            rw [hScalar]
      _ = (σN ^ 2)⁻¹ • (Kᵀ * K) +
            (σN ^ 2)⁻¹ • (((σN / σX) ^ 2) • (1 : Matrix n n ℝ)) := by
            simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = (σN ^ 2)⁻¹ • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)) := by
            rw [smul_add]
  have hScaledInv :
      ((σN ^ 2)⁻¹ • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)))⁻¹ =
        (σN ^ 2) • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ))⁻¹ := by
    -- Local instance justification (scalar inverse): `Matrix.inv_smul` needs an
    -- `Invertible` witness for the nonzero scalar `(σN ^ 2)⁻¹`.
    letI : Invertible ((σN ^ 2)⁻¹) := invertibleOfNonzero (inv_ne_zero hσN_sq_ne)
    simpa [hσN_sq_ne] using
      (Matrix.inv_smul
        (A := (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)))
        (k := (σN ^ 2)⁻¹) (h := hShiftUnit))
  -- Normalize both scalar identity inverses, factor the common scalar, and cancel it.
  calc
    ((Kᵀ * (σN ^ 2 • (1 : Matrix m m ℝ))⁻¹ * K + (σX ^ 2 • (1 : Matrix n n ℝ))⁻¹)⁻¹ *
        Kᵀ * (σN ^ 2 • (1 : Matrix m m ℝ))⁻¹)
        =
      (((σN ^ 2)⁻¹ • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ)))⁻¹ *
        Kᵀ * ((σN ^ 2)⁻¹ • (1 : Matrix m m ℝ))) := by
          rw [hNoiseInv, hPriorInv, hFactor]
    _ =
      (((σN ^ 2) • (Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ))⁻¹) *
        Kᵀ * ((σN ^ 2)⁻¹ • (1 : Matrix m m ℝ))) := by
          rw [hScaledInv]
    _ = ((Kᵀ * K + ((σN / σX) ^ 2) • (1 : Matrix n n ℝ))⁻¹ * Kᵀ) := by
          simp [Matrix.mul_assoc, mul_smul_comm, smul_mul_assoc, hσN_sq_ne]

/-- Example 4.26 (2): in the isotropic covariance case, the precision-form MAP estimator agrees
with the finite-dimensional Tikhonov reconstruction with parameter `(σN / σX) ^ 2`. -/
theorem precisionEstimator_eq_tikhonovReconstruction
    (K : Matrix m n ℝ) (σN σX : ℝ) (z : EuclideanSpace ℝ m)
    (hσN : 0 < σN) (hσX : 0 < σX) :
    precisionEstimator K (σN ^ 2 • (1 : Matrix m m ℝ)) (σX ^ 2 • (1 : Matrix n n ℝ)) z =
      Tikhonov.reconstruction K ((σN / σX) ^ 2) z := by
  -- Compare the two estimators at the matrix-operator level before applying them to `z`.
  rw [precisionEstimator_eq, Tikhonov.reconstruction_eq]
  simpa using congrArg (fun M ↦ Matrix.toEuclideanLin M z)
    (isotropicPrecisionOperator_eq_tikhonovOperator K σN σX hσN hσX)

end

end LinearGaussian

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

universe u v w

section PredictiveRisk

variable {n : Type u} [Fintype n]

/-- The predictive risk is the normalized squared Euclidean norm of a predictive error vector. -/
def predictiveRisk (p : EuclideanSpace ℝ n) : ℝ :=
  ‖p‖ ^ 2 / (Fintype.card n : ℝ)

/-- The defining formula for `predictiveRisk`. -/
@[simp] theorem predictiveRisk_def (p : EuclideanSpace ℝ n) :
    predictiveRisk p = ‖p‖ ^ 2 / (Fintype.card n : ℝ) := by
  simp [predictiveRisk]

/-- Scaling a discrete vector scales its predictive risk by the square of that
factor. -/
theorem predictiveRisk_smul (s : ℝ) (p : EuclideanSpace ℝ n) :
    predictiveRisk (s • p) = s ^ 2 * predictiveRisk p := by
  rw [predictiveRisk_def, predictiveRisk_def, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]

end PredictiveRisk

section RegularizedSolution

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {m : Type v}

/-- The regularized solution obtained by applying the regularization matrix to the data vector. -/
def regularizedSolution [Fintype m] [DecidableEq m]
    (R : Matrix m n ℝ) (d : EuclideanSpace ℝ n) : EuclideanSpace ℝ m :=
  R.toEuclideanLin d

/-- The defining formula for `regularizedSolution`. -/
@[simp] theorem regularizedSolution_eq [Fintype m] [DecidableEq m]
    (R : Matrix m n ℝ) (d : EuclideanSpace ℝ n) :
    regularizedSolution R d = R.toEuclideanLin d := by
  simp [regularizedSolution]

end RegularizedSolution

section InfluenceMatrix

variable {n : Type u} {m : Type v} [Fintype m]

/-- The influence matrix associated to a forward matrix and a regularization matrix. -/
def influenceMatrix (K : Matrix n m ℝ) (R : Matrix m n ℝ) : Matrix n n ℝ :=
  K * R

/-- The defining formula for `influenceMatrix`. -/
@[simp] theorem influenceMatrix_def (K : Matrix n m ℝ) (R : Matrix m n ℝ) :
    influenceMatrix K R = K * R := by
  simp [influenceMatrix]

end InfluenceMatrix

section RegularizedResidual

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The regularized residual associated to an influence matrix and the data vector. -/
def regularizedResidual (A : Matrix n n ℝ) (d : EuclideanSpace ℝ n) : EuclideanSpace ℝ n :=
  (A - 1).toEuclideanLin d

/-- The defining formula for `regularizedResidual`. -/
@[simp] theorem regularizedResidual_eq (A : Matrix n n ℝ) (d : EuclideanSpace ℝ n) :
    regularizedResidual A d = (A - 1).toEuclideanLin d := by
  simp [regularizedResidual]

end RegularizedResidual

section UPREValue

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The fixed-influence-matrix UPRE value built from the regularized residual and trace term. -/
def upreValue (A : Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) : ℝ :=
  predictiveRisk (regularizedResidual A d) +
    (2 * σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace A - σ ^ 2

/-- The defining formula for `upreValue`. -/
@[simp] theorem upreValue_def (A : Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) :
    upreValue A σ d =
      predictiveRisk (regularizedResidual A d) +
        (2 * σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace A - σ ^ 2 := by
  simp [upreValue]

end UPREValue

section UPRE

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {τ : Type w}

/-- Definition 7.1-extra-1 (1). The UPRE objective associated to a family of influence matrices. -/
def upre (Afamily : τ → Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) : τ → ℝ :=
  fun a ↦ upreValue (Afamily a) σ d

/-- The defining formula for `upre` in terms of `upreValue`. -/
@[simp] theorem upre_eq_upreValue (Afamily : τ → Matrix n n ℝ) (σ : ℝ)
    (d : EuclideanSpace ℝ n) (a : τ) :
    upre Afamily σ d a = upreValue (Afamily a) σ d := by
  simp [upre]

/-- Definition 7.1-extra-1 (2). A parameter is a UPRE parameter when it minimizes
`upre` on `Set.univ`. -/
def IsUPREParameter (Afamily : τ → Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n)
    (a : τ) : Prop :=
  IsMinOn (upre Afamily σ d) Set.univ a

/-- The defining characterization of `IsUPREParameter`. -/
@[simp] theorem IsUPREParameter_iff (Afamily : τ → Matrix n n ℝ) (σ : ℝ)
    (d : EuclideanSpace ℝ n) (a : τ) :
    IsUPREParameter Afamily σ d a ↔ IsMinOn (upre Afamily σ d) Set.univ a := Iff.rfl

end UPRE

section Bridges

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {m : Type v} [Fintype m] [DecidableEq m]

/-- Rewriting `regularizedResidual` through the factorization `A = K * R`. -/
theorem regularizedResidual_influenceMatrix (K : Matrix n m ℝ) (R : Matrix m n ℝ)
    (d : EuclideanSpace ℝ n) :
    regularizedResidual (influenceMatrix K R) d =
      K.toEuclideanLin (regularizedSolution R d) - d := by
  apply WithLp.ofLp_injective
  simp [regularizedResidual, influenceMatrix, regularizedSolution,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

end Bridges

end

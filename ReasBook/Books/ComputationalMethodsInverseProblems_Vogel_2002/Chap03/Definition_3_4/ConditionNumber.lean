/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

public section

noncomputable section

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The condition number of a nonzero real matrix, defined as the ratio of its
largest singular value to its smallest nonzero singular value. -/
def conditionNumber (A : Matrix n n ℝ) (hA : A ≠ 0) : ℝ :=
  let _ : A ≠ 0 := hA
  A.toEuclideanLin.singularValues 0 /
    A.toEuclideanLin.singularValues (Module.finrank ℝ A.toEuclideanLin.range - 1)

/-- The condition number of a positive-definite real matrix. The nonzero witness
needed by `Matrix.conditionNumber` is discharged from positive definiteness once
the index type is nonempty. -/
def posDefConditionNumber [Nonempty n] (A : Matrix n n ℝ) (hA : A.PosDef) : ℝ :=
  A.conditionNumber hA.isUnit.ne_zero

/-- Rewrites `conditionNumber` as the ratio of the extremal nonzero singular
values of `A.toEuclideanLin`. -/
theorem conditionNumber_eq_singularValueRatio (A : Matrix n n ℝ) (hA : A ≠ 0) :
    A.conditionNumber hA =
      A.toEuclideanLin.singularValues 0 /
        A.toEuclideanLin.singularValues (Module.finrank ℝ A.toEuclideanLin.range - 1) := by
  -- Unfold the definition of the condition number.
  rfl

/-- `Matrix.posDefConditionNumber` is the usual condition number specialized to
positive-definite matrices. -/
theorem posDefConditionNumber_eq_conditionNumber [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.PosDef) :
    A.posDefConditionNumber hA = A.conditionNumber hA.isUnit.ne_zero := by
  simp [Matrix.posDefConditionNumber]

/-- For a positive-definite real matrix, the condition number is the ratio of
the largest and smallest spectral values. -/
theorem conditionNumber_eq_spectralExtrema_of_posDef (A : Matrix n n ℝ) (hA : A ≠ 0)
    (hspd : A.PosDef) :
    A.conditionNumber hA = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
  sorry

/-- For a positive-definite real matrix, `Matrix.posDefConditionNumber` is the
ratio of the largest and smallest spectral values. -/
theorem posDefConditionNumber_eq_spectralExtrema [Nonempty n] (A : Matrix n n ℝ)
    (hA : A.PosDef) :
    A.posDefConditionNumber hA = sSup (spectrum ℝ A) / sInf (spectrum ℝ A) := by
  exact A.conditionNumber_eq_spectralExtrema_of_posDef hA.isUnit.ne_zero hA

end Matrix

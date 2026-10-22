/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_3_2

open Matrix

noncomputable section

section

variable {n m k : ℕ}

local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "ReducedBasisMatrix" => Matrix (Fin n) (Fin k) ℝ

private theorem injective_mulVec_of_rank_eq_width
    (A : ConstraintMatrix) (hA : Matrix.rank A = m) :
    Function.Injective A.mulVec := by
  rw [Matrix.mulVec_injective_iff]
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [Set.finrank, Matrix.rank_eq_finrank_span_cols] using hA.symm

/-- Chapter09 Exercise 9.10: if `A : ℝ^(n × m)` has full column rank, if `Z` is a reduced-null-
space matrix for `A`, and if the reduced Hessian `Zᵀ G Z` is positive definite, then the KKT
matrix `(9.3.47)` is nonsingular. -/
theorem kktMatrix_isUnit_of_fullColumnRank_of_reducedHessian_posDef
    (G : HessianMatrix) (A : ConstraintMatrix) (Z : ReducedBasisMatrix)
    (hA : Matrix.rank A = m)
    (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Z.transpose * G * Z).PosDef) :
    IsUnit (kktMatrix G A) :=
  kktMatrix_isUnit_of_reducedHessian_posDef G A Z
    (injective_mulVec_of_rank_eq_width A hA) hZ hReduced

end

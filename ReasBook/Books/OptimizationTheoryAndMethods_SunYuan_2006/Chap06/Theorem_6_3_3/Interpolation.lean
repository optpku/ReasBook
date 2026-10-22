/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_3_2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open scoped BigOperators
open scoped ThirdOrderTensor

section

variable {n p : ℕ}

/-- The matrix `M` with entries `M[i,j] = ((s i)ᵀ (s j))^2`. -/
def tensorSquaredGramMatrix (s : Fin p → EuclideanSpace ℝ (Fin n)) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ (dotProduct (s i) (s j)) ^ 2

/-- The interpolation matrix `Z` whose `k`-th column is `z k`. -/
def tensorInterpolationMatrix (z : Fin p → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin p) ℝ :=
  fun i k ↦ z k i

/-- The coefficient matrix `A = Z M⁻¹` attached to the squared Gram matrix `M` and data columns
`z k`. Under `LinearIndependent ℝ s`, Theorem 6.3.3 identifies the resulting tensor combination
with the least-Frobenius-norm interpolant. -/
def tensorGramInverseCoefficientMatrix (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin p) ℝ :=
  tensorInterpolationMatrix z * (tensorSquaredGramMatrix s)⁻¹

/-- The `k`-th column `a_k` of `tensorGramInverseCoefficientMatrix s z`. -/
def tensorGramInverseCoefficientColumn (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) (k : Fin p) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 <| fun i ↦ tensorGramInverseCoefficientMatrix s z i k

/-- The interpolation condition `T (s k) (s k) = z k` on the data sites `s`. -/
def tensorLeastNormInterpolates (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) (T : ThirdOrderTensor n) : Prop :=
  ∀ k, T.mulVecVec (s k) (s k) = z k

/-- The feasible set of third-order tensors interpolating the data `z` on the sites `s`. -/
def tensorLeastNormFeasibleSet (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) : Set (ThirdOrderTensor n) :=
  {T | tensorLeastNormInterpolates s z T}

/-- The explicit tensor `∑ k, a_k ⊗ s_k ⊗ s_k` with coefficients `a_k` coming from
`tensorGramInverseCoefficientMatrix s z = Z M⁻¹`. Under `LinearIndependent ℝ s`,
Theorem 6.3.3 identifies this candidate with the least-Frobenius-norm interpolant. -/
def tensorGramInverseCombination (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) : ThirdOrderTensor n :=
  ∑ k, ⟪tensorGramInverseCoefficientColumn s z k, s k, s k⟫₃

/-- Expanding `tensorGramInverseCombination s z` gives the source formula
`∑ k, a_k ⊗ s_k ⊗ s_k`. -/
theorem tensorGramInverseCombination_eq_sum (s : Fin p → EuclideanSpace ℝ (Fin n))
    (z : Fin p → EuclideanSpace ℝ (Fin n)) :
    tensorGramInverseCombination s z =
      ∑ k, ⟪tensorGramInverseCoefficientColumn s z k, s k, s k⟫₃ := rfl

end

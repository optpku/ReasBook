/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_4

noncomputable section

section Chapter14Lemma1481

variable {n m : ℕ}

open scoped GeneralizedJacobian

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "JacobianMap" => Point →L[ℝ] ValuePoint
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Domain sampling / source-core-bridge triage:
-- * source-facing: Lemma 14.8.1, a directional-derivative regularity and generalized-Jacobian
--   representation statement for maps `ℝ^n → ℝ^m`
-- * core/canonical Chapter 14 owners already present upstream:
--   the generalized-Jacobian owner `∂ F` and the matrix bridge `generalizedJacobianMatrix F x`
--   from
--   `Definition_14_8_extra_1`, together with the Euclidean matrix bridge
--   `jacobianMatrixOfMap`, `LocallyLipschitzAt` from `Definition_14_8_extra_4`, and the
--   Euclidean matrix action `Matrix.toEuclideanLin`
-- * primitive data in this file: local Lipschitz regularity at `x` and one-sided directional
--   differentiability in every direction
-- * derived API: the Lipschitz regularity of `h ↦ F'(x; h)`, the intrinsic operator-level
--   generalized-Jacobian representation, and the matrix-coordinate bridge for files that
--   genuinely need `generalizedJacobianMatrix`

variable (F : Point → ValuePoint) (x : Point)

/-- Chapter14 Lemma 14.8.1 (1): if `F : ℝ^n → ℝ^m` is locally Lipschitz at `x` and has a right
directional derivative in every direction at `x`, then the map `h ↦ F'(x; h)` is Lipschitz. -/
theorem oneSidedDirectionalDeriv_lipschitz
    (h_local : LocallyLipschitzAt F x)
    (h_dir :
      ∀ h : Point, HasOneSidedDirectionalDerivAt F (oneSidedDirectionalDeriv F x h) x h) :
    ∃ L : NNReal, LipschitzWith L (fun h ↦ oneSidedDirectionalDeriv F x h) := sorry

/-- Chapter14 Lemma 14.8.1 (2): if `F : ℝ^n → ℝ^m` is locally Lipschitz at `x` and has a right
directional derivative in every direction at `x`, then for every direction `h` there is a
generalized-Jacobian operator `A ∈ (∂ F) x = ∂F(x)` such that `F'(x; h) = A h`. -/
theorem exists_mem_generalizedJacobian_eq_oneSidedDirectionalDeriv
    (h_local : LocallyLipschitzAt F x)
    (h_dir :
      ∀ h : Point, HasOneSidedDirectionalDerivAt F (oneSidedDirectionalDeriv F x h) x h)
    (h : Point) :
    ∃ A : JacobianMap, A ∈ (∂ F) x ∧
      oneSidedDirectionalDeriv F x h = A h := sorry

/-- The matrix-coordinate companion to Lemma 14.8.1 (2): the intrinsic operator statement for
`(∂ F) x = ∂F(x)` specializes to a standard-basis matrix in the bridge view
`generalizedJacobianMatrix F x` with the same action on the direction `h`. -/
theorem exists_mem_generalizedJacobianMatrix_eq_oneSidedDirectionalDeriv
    (h_local : LocallyLipschitzAt F x)
    (h_dir :
      ∀ h : Point, HasOneSidedDirectionalDerivAt F (oneSidedDirectionalDeriv F x h) x h)
    (h : Point) :
    ∃ V : JacobianMatrix, V ∈ generalizedJacobianMatrix F x ∧
      oneSidedDirectionalDeriv F x h = Matrix.toEuclideanLin V h := sorry

#print axioms generalizedJacobian
#print axioms generalizedJacobianMatrix
#print axioms oneSidedDirectionalDeriv

end Chapter14Lemma1481

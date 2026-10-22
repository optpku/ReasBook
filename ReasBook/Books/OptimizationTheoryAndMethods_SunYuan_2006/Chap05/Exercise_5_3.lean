/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

open Matrix

/-
Domain sampling for this item:
- primary domain: quasi-Newton matrix updates on real Euclidean spaces;
- sampled owner declarations in this domain:
  `dfpInverseUpdate`,
  `bfgsHessianUpdate`,
  `bfgsInverseUpdate`,
  `dfpDualHessianUpdate`,
  `satisfiesQuasiNewtonEquation`,
  `right_ne_zero_of_dotProduct_ne_zero`,
  `posDef_dotProduct_mulVec_ne_zero`,
  `Matrix.PosDef`;
- best owner abstraction: the Chapter 5 update owners together with the operator-valued secant
  equation from `Definition_5_1_extra_1`, while the denominator helpers are already owned by
  `Definition_5_2_extra_1`;
- primitive data here: a current matrix and secant pair `s y`;
- derived API here: quasi-Newton, symmetry, positive-definiteness, and source-facing exchange
  recalls for the canonical update owners, reusing the established denominator lemmas instead of
  restating them.

This file therefore reuses the Chapter 5 owners directly instead of keeping parallel local
matrix-update definitions.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Exercise 5.3 (1): the canonical DFP inverse-Hessian update satisfies the
inverse-form quasi-Newton equation `Hₖ₊₁ y = s`. -/
theorem dfpInverseUpdate_satisfiesQuasiNewtonEquation
    (H : MatrixN) (s y : Point)
    (hsy : dotProduct s y ≠ 0) (hyHy : dotProduct y (H.mulVec y) ≠ 0) :
    satisfiesQuasiNewtonEquation (dfpInverseUpdate H s y).toEuclideanLin y s := by
  -- Bridge the source-facing secant equation to the matrix-vector identity for the DFP owner.
  refine satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr ?_
  -- The imported endpoint theorem already computes the DFP update on the secant vector.
  simpa using dfpInverseUpdate_mulVec H s y hsy hyHy

/-- Chapter05 Exercise 5.3 (2): if the current inverse-Hessian approximation `H` is symmetric,
then the canonical DFP inverse update is symmetric as well. -/
theorem dfpInverseUpdate_isSymm
    {H : MatrixN} (hH : H.IsSymm) (s y : Point) :
    (dfpInverseUpdate H s y).IsSymm := by
  -- Specialize the symmetric Broyden-class theorem at the DFP endpoint `φ = 0`.
  simpa [broydenClassInverseUpdate_zero] using
    broydenClassInverseUpdate_isSymm hH s y (0 : ℝ)

/-- Chapter05 Exercise 5.3 (3): if `H` is positive definite and `dotProduct s y > 0`, then the
canonical DFP inverse-Hessian update is positive definite. -/
theorem dfpInverseUpdate_posDef_of_posDef_of_curvature
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (hcurv : 0 < dotProduct s y) :
    (dfpInverseUpdate H s y).PosDef := by
  -- Specialize the positive-definite Broyden convex-class theorem at `φ = 0`.
  simpa [broydenClassInverseUpdate_zero] using
    broydenClassInverseUpdate_posDef H hH s y (0 : ℝ) (by norm_num) hcurv

/-- Chapter05 Exercise 5.3 (4): the inverse-Hessian BFGS update satisfies the inverse-form
quasi-Newton equation `Hₖ₊₁ y = s`. -/
theorem bfgsInverseUpdate_satisfiesQuasiNewtonEquation
    (H : MatrixN) (s y : Point) (hsy : dotProduct s y ≠ 0) :
    satisfiesQuasiNewtonEquation (bfgsInverseUpdate H s y).toEuclideanLin y s := by
  -- The BFGS endpoint theorem is already stated on the Euclidean linear-map side.
  simpa [satisfiesQuasiNewtonEquation] using bfgsInverseUpdate_mulVec H s y hsy

/-- Chapter05 Exercise 5.3 (5): if the current inverse-Hessian approximation `H` is symmetric,
then the inverse-Hessian BFGS update is symmetric as well. -/
theorem bfgsInverseUpdate_isSymm
    {H : MatrixN} (hH : H.IsSymm) (s y : Point) :
    (bfgsInverseUpdate H s y).IsSymm := by
  -- Specialize the symmetric Broyden-class theorem at the BFGS endpoint `φ = 1`.
  simpa [broydenClassInverseUpdate_one] using
    broydenClassInverseUpdate_isSymm hH s y (1 : ℝ)

/-- Chapter05 Exercise 5.3 (6): if `H` is positive definite and `dotProduct s y > 0`, then the
inverse-Hessian BFGS update is positive definite. -/
theorem bfgsInverseUpdate_posDef_of_posDef_of_curvature
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (hcurv : 0 < dotProduct s y) :
    (bfgsInverseUpdate H s y).PosDef := by
  -- Specialize the positive-definite Broyden convex-class theorem at `φ = 1`.
  simpa [broydenClassInverseUpdate_one] using
    broydenClassInverseUpdate_posDef H hH s y (1 : ℝ) (by norm_num) hcurv

/- Chapter05 Exercise 5.3 (7): after exchanging the inverse and Hessian roles and swapping the
secant data `(s, y) ↦ (y, s)`, the DFP matrix formula is exactly the canonical owner
`bfgsHessianUpdate`. -/
#check bfgsHessianUpdate

/- Chapter05 Exercise 5.3 (8): after exchanging the inverse and Hessian roles and swapping the
secant data `(s, y) ↦ (y, s)`, the inverse-Hessian BFGS formula is exactly the existing owner
theorem `dfpDualHessianUpdate_eq_bfgsInverseUpdate`. -/
#check dfpDualHessianUpdate_eq_bfgsInverseUpdate

end

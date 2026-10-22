/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1

/-
Domain sampling for this item:
- primary domain: quasi-Newton least-change secant updates on matrices over `ℝ`;
- upstream owner abstractions already present in the project:
  the secant-equation owners `satisfiesQuasiNewtonEquation` /
  `satisfiesQuasiNewtonEquationHessianForm` from `Chapter05.Definition_5_1_extra_1`;
- source/core/bridge triage:
  the least-change predicates defined here are source-facing, the secant-equation owners are the
  Chapter 5 core/canonical layer, and the `toEuclideanLin` equalities are the matrix-model bridge;
- primitive data here: an arbitrary change objective `δ : MatrixN → ℝ`, the least-change
  comparison inequality, and the canonical secant owner;
- derived API here: the projection lemmas extracting the canonical secant owner, its concrete
  `toEuclideanLin` equality, and the comparison inequality.

This file therefore keeps the source-facing least-change predicates, while deleting the duplicate
norm-class assumption and reusing the Chapter 5 secant owners directly.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

variable {δ : MatrixN → ℝ}

/-- Chapter05 Definition 5.1-extra-6 (1): the least-change secant property for an
inverse-Hessian update `Hk1` from `Hk` with secant data `y s : Point` and change objective `δ`
means that `Hk1` satisfies the inverse-form
quasi-Newton equation and minimizes `δ (H - Hk)` among all matrices `H` satisfying the same
secant equation. -/
def IsLeastChangeSecantUpdate
    (δ : MatrixN → ℝ) (Hk Hk1 : MatrixN) (y s : Point) : Prop :=
  satisfiesQuasiNewtonEquation Hk1.toEuclideanLin y s ∧
    ∀ H : MatrixN,
      satisfiesQuasiNewtonEquation H.toEuclideanLin y s → δ (Hk1 - Hk) ≤ δ (H - Hk)

/-- The least-change inverse-Hessian property includes the canonical inverse-form secant owner. -/
theorem IsLeastChangeSecantUpdate.secantEquation
    {Hk Hk1 : MatrixN} {y s : Point}
    (h : IsLeastChangeSecantUpdate δ Hk Hk1 y s) :
    satisfiesQuasiNewtonEquation Hk1.toEuclideanLin y s :=
  h.1

/-- The canonical secant owner here is exactly the concrete matrix equation
`Hk1.mulVec y.ofLp = s.ofLp`. -/
theorem IsLeastChangeSecantUpdate.secantEquation_apply
    {Hk Hk1 : MatrixN} {y s : Point}
    (h : IsLeastChangeSecantUpdate δ Hk Hk1 y s) :
    Hk1.mulVec y.ofLp = s.ofLp :=
  satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp h.1

/-- The least-change inverse-Hessian property gives the comparison inequality against any other
matrix satisfying the same canonical inverse-form secant owner. -/
theorem IsLeastChangeSecantUpdate.le_changeMeasure
    {Hk Hk1 : MatrixN} {y s : Point}
    (h : IsLeastChangeSecantUpdate δ Hk Hk1 y s) (H : MatrixN)
    (hH : satisfiesQuasiNewtonEquation H.toEuclideanLin y s) :
    δ (Hk1 - Hk) ≤ δ (H - Hk) :=
  h.2 H hH

/-- The comparison inequality can be invoked from the concrete matrix-model secant equation
`H.mulVec y.ofLp = s.ofLp`. -/
theorem IsLeastChangeSecantUpdate.le_changeMeasure_apply
    {Hk Hk1 : MatrixN} {y s : Point}
    (h : IsLeastChangeSecantUpdate δ Hk Hk1 y s) (H : MatrixN)
    (hH : H.mulVec y.ofLp = s.ofLp) :
    δ (Hk1 - Hk) ≤ δ (H - Hk) :=
  h.2 H <| satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr hH

/-- Chapter05 Definition 5.1-extra-6 (2): the least-change secant property for a Hessian update
`Bk1` from `Bk` with secant data `s y : Point` and change objective `δ` means that `Bk1`
satisfies the Hessian-form quasi-Newton equation and
minimizes `δ (B - Bk)` among all matrices `B` satisfying that same secant equation. -/
def IsLeastChangeSecantUpdateHessianForm
    (δ : MatrixN → ℝ) (Bk Bk1 : MatrixN) (s y : Point) : Prop :=
  satisfiesQuasiNewtonEquationHessianForm Bk1.toEuclideanLin s y ∧
    ∀ B : MatrixN,
      satisfiesQuasiNewtonEquationHessianForm B.toEuclideanLin s y →
        δ (Bk1 - Bk) ≤ δ (B - Bk)

/-- The least-change Hessian property includes the canonical Hessian-form secant owner. -/
theorem IsLeastChangeSecantUpdateHessianForm.secantEquation
    {Bk Bk1 : MatrixN} {s y : Point}
    (h : IsLeastChangeSecantUpdateHessianForm δ Bk Bk1 s y) :
    satisfiesQuasiNewtonEquationHessianForm Bk1.toEuclideanLin s y :=
  h.1

/-- The canonical Hessian-form secant owner here is exactly the concrete matrix equation
`Bk1.mulVec s.ofLp = y.ofLp`. -/
theorem IsLeastChangeSecantUpdateHessianForm.secantEquation_apply
    {Bk Bk1 : MatrixN} {s y : Point}
    (h : IsLeastChangeSecantUpdateHessianForm δ Bk Bk1 s y) :
    Bk1.mulVec s.ofLp = y.ofLp :=
  satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp h.1

/-- The least-change Hessian property gives the comparison inequality against any other matrix
satisfying the same canonical Hessian-form secant owner. -/
theorem IsLeastChangeSecantUpdateHessianForm.le_changeMeasure
    {Bk Bk1 : MatrixN} {s y : Point}
    (h : IsLeastChangeSecantUpdateHessianForm δ Bk Bk1 s y) (B : MatrixN)
    (hB : satisfiesQuasiNewtonEquationHessianForm B.toEuclideanLin s y) :
    δ (Bk1 - Bk) ≤ δ (B - Bk) :=
  h.2 B hB

/-- The comparison inequality can be invoked from the concrete matrix-model secant equation
`B.mulVec s.ofLp = y.ofLp`. -/
theorem IsLeastChangeSecantUpdateHessianForm.le_changeMeasure_apply
    {Bk Bk1 : MatrixN} {s y : Point}
    (h : IsLeastChangeSecantUpdateHessianForm δ Bk Bk1 s y) (B : MatrixN)
    (hB : B.mulVec s.ofLp = y.ofLp) :
    δ (Bk1 - Bk) ≤ δ (B - Bk) :=
  h.2 B <| satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mpr hB

end

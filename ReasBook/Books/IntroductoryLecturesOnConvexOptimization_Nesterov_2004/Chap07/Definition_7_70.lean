/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-
Definition 7.70 lies in Chapter 7's Boolean quadratic optimization domain.

Sampled owner-style declarations:
- `signVectorSet` in `Chap07/Definition_7_33`, the chapter owner for the feasible set of sign
  vectors on a finite coordinate type;
- `Matrix.toQuadraticMap'` in mathlib, the canonical matrix quadratic-form owner on `ι → ℝ`;
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for real-valued maxima over a
  finite index type;
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for faithful `EReal`-valued
  maximization over a feasible set.

Best owner abstraction:
- source-facing: the Boolean quadratic optimal value over `signVectorSet ι`;
- core/canonical: the objective `A.toQuadraticMap'`;
- bridge/view: the raw `sSup` expansion theorem below, and potentially the `EReal` owner
  `maximalValueOn` when a later file needs the faithful maximization codomain.

Primitive data:
- a finite coordinate type `ι`;
- a matrix `A : Matrix ι ι ℝ`.

Derived API:
- the feasible set owner `signVectorSet ι`;
- the quadratic objective owner `A.toQuadraticMap'`;
- the source-facing supremum value over that feasible set.

Source/core/bridge triage:
- source-facing: `booleanQuadraticOptimalValue`;
- core/canonical: `Matrix.toQuadraticMap'`;
- bridge/view: `booleanQuadraticOptimalValue_eq_sSup_image`.

The textbook value is still real-valued here, so the Chapter 7 `EReal` owner `maximalValueOn`
would be a bridge rather than the main entry. The refinement therefore keeps the source-facing
real value, but removes the coordinate-level duplicate objective `fun x ↦ dotProduct (A.mulVec x)
x` in favor of the canonical matrix quadratic-map owner. The textbook `n`-dimensional statement is
recovered by specializing `ι = Fin n`.
-/

/-- Definition 7.70: the Boolean quadratic optimum `f⋆` is the supremum of the quadratic-map
values `A.toQuadraticMap' x` over all sign vectors on the finite coordinate type `ι`. The
textbook `n`-dimensional case is the specialization `ι = Fin n`, and the later approximation
theorem specializes further to positive-definite matrices. -/
def booleanQuadraticOptimalValue (A : Matrix ι ι ℝ) : ℝ :=
  sSup (A.toQuadraticMap' '' signVectorSet ι)

-- Proof sketch: unfold `booleanQuadraticOptimalValue`; the right-hand side is exactly the
-- defining supremum of the quadratic values over the sign-vector feasible set.
/-- Expanding `booleanQuadraticOptimalValue A` gives the supremum of `⟪Ax, x⟫` over all Boolean
sign vectors. -/
theorem booleanQuadraticOptimalValue_eq_sSup_image
    (A : Matrix ι ι ℝ) :
    booleanQuadraticOptimalValue A = sSup (A.toQuadraticMap' '' signVectorSet ι) :=
  rfl

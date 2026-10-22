/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

noncomputable section

open Matrix
open scoped PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.31 lies in the positive-definite matrix / one-sided rounding domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the weighted primal norm;
- `positiveDefMatrixNorm_dualNorm_apply` in `Definition_7_23`, the canonical owner of the weighted
  dual norm `‖g‖[G,*]`;
- `Matrix.vecMulVec`, the canonical rank-one outer-product owner from mathlib.

Best owner abstraction:
- source-facing: the one-sided updated matrix `G(α)` attached to `G`, `g`, and `α`;
- core/canonical: `‖g‖[G,*]` and `Matrix.vecMulVec`;
- bridge/view: the defining closed-form expansion below.

Primitive data:
- a positive-definite matrix `G : {G : Mat // G.PosDef}`;
- a vector `g : E`;
- a scalar parameter `α : ℝ`.

Derived API:
- the weighted dual radius is the existing owner `‖g‖[G,*]`, not a second local wrapper;
- theorem-level nonvanishing assumptions belong to the later containment and determinant-ratio
  statements, not to the matrix-path owner itself;
- the textbook restriction `α ∈ [0, 1]` is theorem-level side data for later estimates, not part of
  the matrix-path data itself.

Source/core/bridge triage:
- source-facing: `oneSidedRoundingUpdatedMatrix`;
- core/canonical: `positiveDefMatrixNorm` and `Matrix.vecMulVec`;
- bridge/view: `oneSidedRoundingUpdatedMatrix_def`.

The previous file duplicated the weighted dual radius as a separate public definition and encoded
proof-only side conditions in the owner data. This refinement keeps the source-facing matrix path as
the owner, reuses the canonical dual norm directly, and leaves nonvanishing and interval
restrictions to the theorem layer where they actually matter.
-/

/-- Definition 7.31: for a positive-definite matrix `G` on `ℝⁿ`, a vector `g ∈ ℝⁿ`, and a scalar
parameter `α`, the one-sided updated matrix is
`(1 - α) G + (α / r + ((r - 1) / 2)^2 (α / r)^2) ggᵀ`, where `r = ‖g‖*_G`. The textbook
restriction `α ∈ [0, 1]` and any later nonvanishing hypotheses are imposed only on the theorem
layer. -/
def oneSidedRoundingUpdatedMatrix
    (G : {G : Mat // G.PosDef}) (g : E) (α : ℝ) : Mat :=
  let r := ‖g‖[G,*]
  (1 - α) • G.1 +
    ((α / r) + (((r - 1) / 2) ^ (2 : ℕ)) * (α / r) ^ (2 : ℕ)) •
      vecMulVec g g

/-- Expanding `oneSidedRoundingUpdatedMatrix G g α` gives the textbook formula for `G(α)` with
`r = ‖g‖*_G`. -/
theorem oneSidedRoundingUpdatedMatrix_def
    (G : {G : Mat // G.PosDef}) (g : E) (α : ℝ) :
    oneSidedRoundingUpdatedMatrix G g α =
      (1 - α) • G.1 +
        ((α / ‖g‖[G,*]) +
            (((‖g‖[G,*] - 1) / 2) ^ (2 : ℕ)) * (α / ‖g‖[G,*]) ^ (2 : ℕ)) •
          vecMulVec g g :=
  rfl

end

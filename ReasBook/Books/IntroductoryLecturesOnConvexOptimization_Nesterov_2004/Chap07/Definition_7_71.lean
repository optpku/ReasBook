/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators MatrixOrder RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.71 lies in Chapter 7's symmetric-matrix / semidefinite-relaxation domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n`, the project owner for real symmetric matrices;
- Chapter 5 `𝕊^n₊` and `mem_positiveSemidefiniteCone_iff`, the intrinsic positive-semidefinite
  cone inside `𝕊^n`;
- mathlib `Matrix.nonneg_iff_posSemidef`, the canonical bridge between matrix order and positive
  semidefiniteness;
- Chapter 1 `SetConstrainedMinimizationProblem.optimalValue`, a possible faithful `EReal` bridge
  for infima, but not the main owner here because Definition 7.71 itself is the source-facing
  real-valued quantity `ψ⋆`.

Best owner abstraction:
- source-facing: the feasible diagonal-majorant set and the real infimum `ψ⋆`;
- core/canonical: `𝕊^n`, `𝕊^n₊`, and `Matrix.diagonal`;
- bridge/view: the textbook order inequality `A ≤ D(y)` and the explicit `sInf` image formula.

Primitive data:
- `A : 𝕊^n`.

Derived API:
- feasibility expressed intrinsically by the diagonal slack matrix `D(y) - A ∈ 𝕊^n₊`;
- the companion order-form membership theorem below;
- the source-facing infimum of the coordinate-sum objective over the feasible set.

This refinement keeps Definition 7.71 source-facing, but removes the lower-level ambient-order
surface from the main feasible-set owner. The feasible set now grows from the chapter PSD-cone
owner `𝕊^n₊`, while the textbook matrix inequality survives as the companion bridge theorem.
The optimal value is also shortened to the canonical `Set.image` form on the ambient feasible set
instead of a `Set.range` over its subtype.
-/

/-- The feasible set of diagonal majorants `D(y) ⪰ A` for a symmetric real matrix `A`,
expressed intrinsically by requiring the slack matrix `D(y) - A` to lie in `𝕊^n₊`. -/
def diagonalSemidefiniteRelaxationFeasibleSet
    (A : 𝕊^n) : Set E :=
  {y |
    ((⟨Matrix.diagonal fun i : Fin n ↦ y i, by
        rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
        simp
      ⟩ : 𝕊^n) - A) ∈ 𝕊^n₊}

-- Proof sketch: the diagonal matrix `D(y)` is canonically an element of `𝕊^n`, so the feasible
-- set is cut out by the PSD-cone condition `(D(y) - A) ∈ 𝕊^n₊`. Expanding membership in
-- `𝕊^n₊` and using `Matrix.nonneg_iff_posSemidef` identifies this with the textbook order
-- inequality `A ≤ D(y)`.
/-- Membership in the diagonal semidefinite relaxation feasible set means exactly that the
diagonal matrix `D(y)` majorizes `A` in the semidefinite order. -/
theorem mem_diagonalSemidefiniteRelaxationFeasibleSet_iff
    {A : 𝕊^n} {y : E} :
    y ∈ diagonalSemidefiniteRelaxationFeasibleSet A ↔
      (A : Mₙ) ≤ Matrix.diagonal fun i : Fin n ↦ y i := by
  rw [diagonalSemidefiniteRelaxationFeasibleSet, Set.mem_setOf_eq,
    mem_positiveSemidefiniteCone_iff]
  constructor
  · intro h
    exact sub_nonneg.mp ((Matrix.nonneg_iff_posSemidef).mpr h)
  · intro h
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr h)

/-- Definition 7.71: for a symmetric matrix `A ∈ ℝ^{n × n}`, the value `ψ⋆` is the infimum of
`⟨\bar e_n, y⟩ = ∑ i, y i` over all vectors `y ∈ ℝⁿ` whose diagonal matrix `D(y)` satisfies
`D(y) ⪰ A`. -/
def diagonalSemidefiniteRelaxationOptimalValue
    (A : 𝕊^n) : ℝ :=
  sInf ((fun y : E ↦ ∑ i : Fin n, y i) '' diagonalSemidefiniteRelaxationFeasibleSet A)

-- Proof sketch: unfold `diagonalSemidefiniteRelaxationOptimalValue`; the right-hand side is
-- exactly the defining infimum of the linear objective over the feasible diagonal-majorant set.
/-- The diagonal semidefinite relaxation value is the infimum of the coordinate sum over all
feasible diagonal majorants. -/
theorem diagonalSemidefiniteRelaxationOptimalValue_eq_sInf
    (A : 𝕊^n) :
    diagonalSemidefiniteRelaxationOptimalValue A =
      sInf ((fun y : E ↦ ∑ i : Fin n, y i) '' diagonalSemidefiniteRelaxationFeasibleSet A) :=
  rfl

end

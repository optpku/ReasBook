/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_4

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.28 lies in the positive-definite matrix norm / rank-one update domain.

Sampled owner-style declarations:
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the primal weighted norm
  `x ↦ √⟪Gx, x⟫`;
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter ellipsoid owner whose inverse-matrix
  specialization recovers the primal unit ball of `positiveDefMatrixNorm`;
- `rankOneUpdateAugmentedHull` in `Lemma_7_4`, the existing owner of the convex hull obtained by
  adjoining `±g` to a unit ellipsoid;
- `rankOneUpdatedMatrix` in `Lemma_7_4`, the existing owner of the rank-one interpolation
  `G(α) = (1 - α) G + α ggᵀ`.

Best owner abstraction:
- source-facing: the primal unit ball `{x | ‖x‖[G] ≤ 1}`, the signed hull obtained from it, and the
  rank-one interpolation;
- core/canonical: `positiveDefMatrixNorm`, `affineEllipsoid`, `rankOneUpdateAugmentedHull`, and
  `rankOneUpdatedMatrix`;
- bridge/view: the inverse-matrix identification of the primal unit ball and the subtype-parameter
  companions below.

Primitive data:
- a positive-definite matrix `G : Mat`;
- a vector `g : E`;
- an interpolation parameter `α`.

Derived API:
- the weighted unit ball is the unit ball of `positiveDefMatrixNorm`;
- equivalently it is `affineEllipsoid G⁻¹ 0`;
- the signed hull is `rankOneUpdateAugmentedHull G⁻¹ g`;
- the matrix path is `rankOneUpdatedMatrix G g α`.

Source/core/bridge triage:
- source-facing: Definition 7.28's weighted unit ball, signed hull, and interpolated matrix;
- core/canonical: the existing chapter owners above;
- bridge/view: the two theorems below.

This file is therefore recall/bridge-only: the previous `weightedUnitBall`,
`signedConvexHullOfWeightedUnitBall`, and `rankOneInterpolatedMatrix` were duplicate public shells
around existing chapter owners and are removed.
-/

/- Definition 7.28 recalls the primal weighted norm owner `positiveDefMatrixNorm`. -/
#check positiveDefMatrixNorm

/- Definition 7.28 recalls the signed hull owner `rankOneUpdateAugmentedHull`. -/
#check rankOneUpdateAugmentedHull

/- Definition 7.28 recalls the rank-one interpolation owner `rankOneUpdatedMatrix`. -/
#check rankOneUpdatedMatrix

/-- The primal `G`-unit ball from Definition 7.28 is the inverse-matrix ellipsoid
`E(G⁻¹, 0)`. -/
theorem mem_affineEllipsoid_inv_iff_norm_le_one
    (G : {G : Mat // G.PosDef}) (x : E) :
    x ∈ E(G.1⁻¹, (0 : E)) ↔ ‖x‖[G] ≤ 1 := by
  let GInv : {G : Mat // G.PosDef} := ⟨G.1⁻¹, G.2.inv⟩
  rw [← centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le G.2.inv]
  rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv GInv x]
  rw [positiveDefMatrixNorm_def G x]
  let _ := G.2.isUnit.invertible
  simp [GInv, real_inner_comm]

/-- The signed hull from Definition 7.28 is the convex hull of the primal `G`-unit ball together
with the two points `±g`. -/
theorem rankOneUpdateAugmentedHull_inv_eq_convexHull_primalUnitBall
    (G : {G : Mat // G.PosDef}) (g : E) :
    rankOneUpdateAugmentedHull G.1⁻¹ g =
      convexHull ℝ ({x : E | ‖x‖[G] ≤ 1} ∪ ({g, -g} : Set E)) := by
  refine congrArg (convexHull ℝ) ?_
  ext x
  simp [mem_affineEllipsoid_inv_iff_norm_le_one]

end

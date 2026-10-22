/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_28

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.30 lies in the positive-definite ellipsoid / support-function domain.

Sampled owner-style declarations:
- `supportFunction` with notation `ξ[Q]` in `Chap03/Definition_3_9`, the chapter owner of support
  functions;
- `supportFunction_convexHull_union_eq_max` in `Chap03/Lemma_3_3`, the exact upstream support
  theorem for convex hulls of two-set unions;
- `positiveDefMatrixNorm` in `Definition_7_23`, the chapter owner of the weighted norm;
- `E(H, x̄)` in `Chap03/Lemma_3_2_7` together with the Chapter 7 bridge
  `mem_affineEllipsoid_inv_iff_norm_le_one` from `Definition_7_28`.

Best owner abstraction:
- source-facing: `convexHullOfWeightedUnitBallAndPoint`, the one-sided hull `C_g(G)`;
- core/canonical: `ξ[Q]`, `E(H, x̄)`, and `positiveDefMatrixNorm`;
- bridge/view: the primal-unit-ball reformulation and the support-function theorem below.

Primitive data:
- a positive-definite matrix `G : {G : Mat // G.PosDef}`;
- a vector `g : E`.

Derived API:
- the one-sided hull `C_g(G) = convexHull ℝ (E(G⁻¹, 0) ∪ {g})`;
- the equivalent source wording with the primal unit ball `{x | ‖x‖[G] ≤ 1}`;
- the support-function identity for `C_g(G)` derived from the chapter support-function owner.

Source/core/bridge triage:
- source-facing: `convexHullOfWeightedUnitBallAndPoint`;
- core/canonical: `supportFunction`, `affineEllipsoid`, and `positiveDefMatrixNorm`;
- bridge/view: the two theorem-level restatements below.

This file keeps only the genuinely source-facing hull owner. The previous local `supportFunction`
and `weightedUnitBall` declarations were duplicate public shells around the chapter owners
`ξ[Q]` and `E(G⁻¹, 0)`, so they are removed. -/

/-- Definition 7.30: for a positive-definite matrix `G` on `ℝⁿ` and a vector `g ∈ ℝⁿ`, the set
`C_g(G)` is the convex hull of the weighted unit ball `W₁(G) = E(G⁻¹, 0)` together with the point
`g`. -/
def convexHullOfWeightedUnitBallAndPoint
    (G : {G : Mat // G.PosDef}) (g : E) : Set E :=
  convexHull ℝ (E(G.1⁻¹, 0) ∪ ({g} : Set E))

namespace OneSidedHullNotation

/- Source-facing Lean notation for the textbook weighted unit ball `W₁(G)` and one-sided hull
`C_g(G)`. -/
scoped notation:max "W₁(" G:arg ")" =>
  W[1](G.1⁻¹)

scoped notation:max "C_[" g:arg "](" G:arg ")" =>
  convexHullOfWeightedUnitBallAndPoint G g

end OneSidedHullNotation

open scoped OneSidedHullNotation

/-- Expanding `C_[g](G)` gives the convex hull of `W₁(G)` and the point `g`. -/
theorem convexHullOfWeightedUnitBallAndPoint_def
    (G : {G : Mat // G.PosDef}) (g : E) :
    C_[g](G) = convexHull ℝ (W₁(G) ∪ ({g} : Set E)) := by
  rw [show W₁(G) = E(G.1⁻¹, (0 : E)) by
    simpa using centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  simp [convexHullOfWeightedUnitBallAndPoint]

/-- The weighted unit ball `W₁(G)` is exactly the primal `G`-unit ball `{x | ‖x‖[G] ≤ 1}`. -/
theorem weightedUnitBall_eq_primalUnitBall
    (G : {G : Mat // G.PosDef}) :
    W₁(G) = {x : E | ‖x‖[G] ≤ 1} := by
  rw [show W₁(G) = E(G.1⁻¹, (0 : E)) by
    simpa using centeredMatrixEllipsoid_one_eq_affineEllipsoid G.1⁻¹]
  ext x
  simp [mem_affineEllipsoid_inv_iff_norm_le_one]

/-- Expanding `C_[g](G)` gives the convex hull of the primal `G`-unit ball and the point `g`. -/
theorem convexHullOfWeightedUnitBallAndPoint_eq_convexHull_primalUnitBall
    (G : {G : Mat // G.PosDef}) (g : E) :
    C_[g](G) =
      convexHull ℝ ({x : E | ‖x‖[G] ≤ 1} ∪ ({g} : Set E)) := by
  rw [convexHullOfWeightedUnitBallAndPoint_def, weightedUnitBall_eq_primalUnitBall]

/-- The support function of `C_[g](G)` is the maximum of the support functions of `W₁(G)` and the
singleton `{g}`. Equivalently, this is the chapter-owner form of the textbook formula
`ξ[C_[g](G)] x = max (ξ[W₁(G)] x) ⟪g, x⟫`. -/
theorem supportFunction_convexHullOfWeightedUnitBallAndPoint_eq_max
    (G : {G : Mat // G.PosDef}) (g x : E) :
    ξ[C_[g](G)] x =
      max (ξ[W₁(G)] x) (inner ℝ g x : EReal) := by
  simpa [convexHullOfWeightedUnitBallAndPoint_def, supportFunction_apply] using
    supportFunction_convexHull_union_eq_max (W₁(G)) ({g} : Set E) x

end

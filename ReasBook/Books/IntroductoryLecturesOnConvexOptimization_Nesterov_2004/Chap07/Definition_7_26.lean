/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.26 lies in the Euclidean ellipsoid / positive-definite dual-norm domain.

Sampled owner-style declarations:
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the textbook unit-radius
  ellipsoid;
- `mem_affineEllipsoid_iff` in `Chap03/Lemma_3_2_7`, the exact membership companion theorem for
  that owner;
- `positiveDefMatrixNorm` in `Definition_7_23`, the source-facing owner for the primal norm
  induced by a positive-definite matrix;
- `positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv` in `Definition_7_23`, the canonical bridge
  from the dual norm to the inverse-matrix quadratic formula.

Best owner abstraction:
- source-facing: the radius-parametrized ellipsoid `matrixEllipsoid G v r`;
- core/canonical owners: the unit ellipsoid `affineEllipsoid` and the dual norm
  `positiveDefMatrixNorm`;
- bridge/view: the unit-radius identification and the positive-definite dual-norm membership
  theorem.

Primitive data:
- a matrix `G : Mat`;
- a center `v : E`;
- a radius `r : ℝ`.

Derived API:
- the centered specialization `centeredMatrixEllipsoid G r`;
- exact membership lemmas;
- the radius-`1` bridge to `affineEllipsoid`;
- the positive-definite dual-norm reformulation.

Source/core/bridge triage:
- source-facing: `matrixEllipsoid`, `centeredMatrixEllipsoid`;
- core/canonical: `affineEllipsoid`, `positiveDefMatrixNorm`;
- bridge/view: the companion equivalences below.

The source genuinely carries the extra radius parameter, so this file keeps that source-facing
owner. The duplicate wheel is only the unit-radius surface, which is refined back to the chapter
owner `affineEllipsoid`; under positive-definiteness the defining inequality is further refined to
the canonical dual-norm API from `Definition_7_23`.
-/

/-- Definition 7.26: the ellipsoid `W_r(v, G)` is the set of points `s` in `ℝⁿ` whose
`G`-dual distance from the center `v` is at most `r`, namely
`⟪G⁻¹ (s - v), s - v⟫ ^ (1 / 2) ≤ r`. -/
def matrixEllipsoid (G : Mat) (v : E) (r : ℝ) : Set E :=
  {s | Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - v)) (s - v)) ≤ r}

/-- The centered ellipsoid `W_r(G)`, obtained from `W_r(v, G)` by taking `v = 0`. -/
abbrev centeredMatrixEllipsoid (G : Mat) (r : ℝ) : Set E :=
  matrixEllipsoid G 0 r

namespace EllipsoidNotation

scoped notation:max "W[" r:arg "](" v:arg ", " G:arg ")" => matrixEllipsoid G v r

scoped notation:max "W[" r:arg "](" G:arg ")" => centeredMatrixEllipsoid G r

end EllipsoidNotation

open scoped EllipsoidNotation

/-- Membership in `W[r](v, G)` is exactly the defining quadratic-inequality bound. -/
theorem mem_matrixEllipsoid_iff
    {G : Mat} {v s : E} {r : ℝ} :
    s ∈ W[r](v, G) ↔
      Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - v)) (s - v)) ≤ r :=
  Iff.rfl

/-- Membership in the centered ellipsoid `W[r](G)` is the defining inequality with center `0`. -/
theorem mem_centeredMatrixEllipsoid_iff
    {G : Mat} {s : E} {r : ℝ} :
    s ∈ W[r](G) ↔
      Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) s) s) ≤ r := by
  have hmem :
      s ∈ W[r]((0 : E), G) ↔
        Real.sqrt (inner ℝ ((toEuclideanLin G⁻¹) (s - (0 : E))) (s - (0 : E))) ≤ r :=
    mem_matrixEllipsoid_iff
  simpa [centeredMatrixEllipsoid] using
    hmem

/-- At radius `1`, `W[1](v, G)` is exactly the chapter's unit-radius ellipsoid owner `E(G, v)`. -/
theorem matrixEllipsoid_one_eq_affineEllipsoid
    (G : Mat) (v : E) :
    W[1](v, G) = E(G, v) := by
  ext s
  rw [mem_matrixEllipsoid_iff, mem_affineEllipsoid_iff, Real.sqrt_le_iff]
  simp

/-- At radius `1`, the centered ellipsoid is exactly the chapter's centered unit ellipsoid owner
`E(G, 0)`. -/
theorem centeredMatrixEllipsoid_one_eq_affineEllipsoid
    (G : Mat) :
    W[1](G) = E(G, 0) := by
  simpa [centeredMatrixEllipsoid] using
    matrixEllipsoid_one_eq_affineEllipsoid G (0 : E)

/-- For a positive-definite matrix, membership in `W[r](v, G)` is exactly the dual-norm bound
`‖s - v‖[⟨G, hG⟩,*] ≤ r`. -/
theorem mem_matrixEllipsoid_iff_dualNorm_le
    {G : Mat} (hG : G.PosDef) {v s : E} {r : ℝ} :
    s ∈ W[r](v, G) ↔ ‖s - v‖[⟨G, hG⟩,*] ≤ r := by
  rw [mem_matrixEllipsoid_iff, positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
  simp [LinearMap.map_sub, real_inner_comm]

/-- For a positive-definite matrix, membership in the centered ellipsoid `W[r](G)` is exactly the
dual-norm bound `‖s‖[⟨G, hG⟩,*] ≤ r`. -/
theorem mem_centeredMatrixEllipsoid_iff_dualNorm_le
    {G : Mat} (hG : G.PosDef) {s : E} {r : ℝ} :
    s ∈ W[r](G) ↔ ‖s‖[⟨G, hG⟩,*] ≤ r := by
  have hmem :
      s ∈ W[r]((0 : E), G) ↔ ‖s - (0 : E)‖[⟨G, hG⟩,*] ≤ r :=
    mem_matrixEllipsoid_iff_dualNorm_le hG
  simpa [centeredMatrixEllipsoid] using
    hmem

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "SymmMat" => 𝕊^n

/-
Definition 5.4.5.3 lies in the Euclidean ellipsoid / polyhedral convex-geometry domain.

Sampled owner-style declarations:
* `innerLePolyhedron` and `mem_innerLePolyhedron_iff` in `Chap03/Definition_3_62`, the project
  owner/view for a set cut out by finitely many inequalities `⟪a i, x⟫ ≤ b i`;
* `affineEllipsoid` and the notation `E(H, x̄)` in `Chap03/Lemma_3_2_7`, the chapter owner for a
  matrix-defined ellipsoid centered at `x̄`;
* `mem_affineEllipsoid_iff` in the same file, the canonical companion view of ellipsoid
  membership;
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in `Chap05/Definition_5_4_4_5`, the
  chapter owner/bridge for positive-definite ellipsoid shapes;
* `IsMaximalVolumeInscribedEllipsoid` in `Chap03/Definition_3_61`, the nearby all-centers maximal
  inscribed-ellipsoid predicate built on the same owner ellipsoid.

Best owner abstraction:
* source-facing: the fixed-center maximality predicate `IsMaximumVolumeEllipsoidIn`;
* core/canonical owners: the strict-cone shape owner `𝕊^n₊₊` and the centered ellipsoid owner
  `affineEllipsoid`;
* bridge/view: the owner-level matrix realization
  `StrictPositiveSemidefiniteCone.toMatrix H` of a strict-cone point.

Primitive data:
* the ambient set `Q : Set E`;
* the center `v : E`;
* a candidate shape `H : 𝕊^n₊₊`.

Derived API:
* the candidate ellipsoid `E(toMatrix H, v)`;
* the derived positive-definite bridge `strictPositiveSemidefiniteCone_posDef H`;
* the derived interiority consequence `v ∈ interior Q`;
* the containment and volume-maximality statements for that owner ellipsoid;
* any textbook set-level phrase “the ellipsoid `W` centered at `v`” via the derived identity
  `W = E(toMatrix H, v)`.

This file therefore keeps only the source-facing fixed-center maximality notion stated directly on
the existing ellipsoid owner `E(toMatrix H, v)`, while lifting the primitive shape data to the
intrinsic Chapter 5 strict-cone owner `𝕊^n₊₊` instead of storing a raw matrix together with a
separate positive-definiteness field.
-/

/-- Definition 5.4.5.3: the ellipsoid `E(toMatrix H, v)` is a maximum-volume ellipsoid in `Q`
centered at `v` when it lies inside `Q`, and no other ellipsoid with the same center `v` and
strict-cone shape parameter has larger volume. The positive-definite matrix view of `H` is the
derived bridge `strictPositiveSemidefiniteCone_posDef H`. -/
structure IsMaximumVolumeEllipsoidIn
    (Q : Set E) (v : E) (H : 𝕊^n₊₊) : Prop where
  /-- The candidate ellipsoid lies inside `Q`. -/
  subset : E(toMatrix H, v) ⊆ Q
  /-- No other ellipsoid centered at `v` and contained in `Q` has larger volume. -/
  volume_maximal {shape' : 𝕊^n₊₊}
      (hsubset' : E(toMatrix shape', v) ⊆ Q) :
      volume (E(toMatrix shape', v)) ≤ volume (E(toMatrix H, v))

namespace IsMaximumVolumeEllipsoidIn

/-- The center of a maximum-volume ellipsoid in `Q` is automatically an interior point of `Q`. -/
theorem center_mem_interior
    {Q : Set E} {v : E} {H : 𝕊^n₊₊}
    (hH : IsMaximumVolumeEllipsoidIn Q v H) :
    v ∈ interior Q := by
  have hPos : (toMatrix H).PosDef := by
    simpa [toMatrix_def] using strictPositiveSemidefiniteCone_posDef H
  have hcenter : v ∈ interior (E(toMatrix H, v) : Set E) :=
    center_mem_interior_affineEllipsoid (toMatrix H) v hPos
  exact interior_mono hH.subset hcenter

end IsMaximumVolumeEllipsoidIn

end

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-
Definition 3.61 lies in the chapter's Euclidean ellipsoid / convex-geometry domain.

Primary domain:
- maximal-volume inscribed ellipsoids and their centers inside subsets of `ℝⁿ`.

Sampled owner-style declarations:
- `affineEllipsoid` in `Definition_3_56`, the earlier chapter recall surface for the textbook
  ellipsoid `E(H, x̄)`;
- `mem_affineEllipsoid_iff` in `Definition_3_56`, the canonical companion view of ellipsoid
  membership;
- `IsMaximumVolumeEllipsoidIn` in `Chap05/Definition_5_4_5_3`, a later fixed-center maximality
  predicate stated directly on the same owner ellipsoid.

Best owner abstraction:
- source-facing: `IsMaximalVolumeInscribedEllipsoid` and `IsInscribedEllipsoidCenter`;
- core/canonical owner reused here: `affineEllipsoid`, via the earlier Chapter 3 recall surface;
- bridge/view sampled but not used as owner:
  `IsMaximumVolumeEllipsoidIn`, because Definition 3.61 compares ellipsoids across all centers
  and uses the shape-matrix presentation directly.

Primitive data:
- an ambient set `Ek : Set E`;
- a shape matrix `H : Mat`;
- a center `y : E`.

Derived API:
- the inscribed ellipsoid `affineEllipsoid H y`;
- the containment consequence `IsMaximalVolumeInscribedEllipsoid.subset`;
- the existential center predicate `IsInscribedEllipsoidCenter`.

This file therefore keeps the source-facing maximality predicates, while reusing the earlier
chapter ellipsoid owner directly instead of redefining a local ellipsoid wrapper.
-/

/-- A centered ellipsoid is maximal-volume in `Ek` when it is positive definite, contained in
`Ek`, and has volume at least that of every other positive-definite ellipsoid contained in `Ek`.
-/
structure IsMaximalVolumeInscribedEllipsoid
    (Ek : Set E) (H : Mat) (y : E) : Prop where
  /-- The candidate ellipsoid has positive-definite shape matrix. -/
  posDef : H.PosDef
  /-- The candidate ellipsoid lies inside the ambient set `Ek`. -/
  subset : E(H, y) ⊆ Ek
  /-- No other positive-definite ellipsoid contained in `Ek` has larger volume. -/
  volume_maximal {H' : Mat} {y' : E} (hH' : H'.PosDef) (hsubset : E(H', y') ⊆ Ek) :
    volume (E(H', y')) ≤ volume (E(H, y))

/-- Definition 3.61: a point `y` is an inscribed-ellipsoid center of `Ek` when it is the center
of some maximal-volume ellipsoid contained in `Ek`. -/
def IsInscribedEllipsoidCenter (Ek : Set E) (y : E) : Prop :=
  ∃ H : Mat, IsMaximalVolumeInscribedEllipsoid Ek H y

/-- Expanding `IsInscribedEllipsoidCenter Ek y` produces a shape matrix whose ellipsoid centered
at `y` is maximal-volume among all ellipsoids contained in `Ek`. -/
@[simp] theorem isInscribedEllipsoidCenter_iff
    (Ek : Set E) (y : E) :
    IsInscribedEllipsoidCenter Ek y ↔
      ∃ H : Mat, IsMaximalVolumeInscribedEllipsoid Ek H y :=
  Iff.rfl

end

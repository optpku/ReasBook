/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.27 lies in the Chapter 7 ellipsoid-rounding domain.

Primary domain:
- ellipsoidal roundings of convex sets in `ℝⁿ`.

Sampled owner-style declarations:
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing owner of radius-parametrized
  ellipsoids;
- `matrixEllipsoid_one_eq_affineEllipsoid` in `Chap07/Definition_7_26`, the canonical radius-`1`
  bridge;
- `affineEllipsoid` in `Chap03/Lemma_3_2_7`, the chapter owner of the unit ellipsoid;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, which reuses the same `W[r](G)` owner in
  the centered case.

Best owner abstraction:
- source-facing: the `β`-rounding predicate itself;
- core/canonical owners: `matrixEllipsoid` for variable radius and `affineEllipsoid` for the unit
  ellipsoid;
- bridge/view: the radius-`1` identification from `Definition_7_26`.

Primitive data:
- a set `C : Set E`;
- a rounding parameter `β : ℝ`;
- a shape matrix `G : Mat`;
- a center `v : E`.

Derived API:
- the inner unit-ellipsoid inclusion, canonically phrased with `affineEllipsoid`;
- the outer inclusion in `W[β](v, G)`;
- the derived radius-`1` `matrixEllipsoid` inclusion used for the source wording.

Source/core/bridge triage:
- source-facing: `IsBetaRounding`;
- core/canonical: `matrixEllipsoid`, `affineEllipsoid`;
- bridge/view: `IsBetaRounding.unit_matrixEllipsoid_subset`.

This item defines only the rounding predicate, not a second ellipsoid owner. The previous local
`matrixEllipsoid` duplicate is therefore deleted in favor of the Chapter 7 owner from
`Definition_7_26`, and the primitive inner field is refined to the canonical unit-ellipsoid owner
`affineEllipsoid`. -/

/-- Definition 7.27: the ellipsoid `W₁(v,G)` is a `β`-rounding of `C` when the unit ellipsoid
`W₁(v,G)` is contained in `C` and `C` is contained in the dilated ellipsoid `W_β(v,G)`. -/
structure IsBetaRounding
    (C : Set E) (β : ℝ) (G : Mat) (v : E) : Prop where
  /-- The unit ellipsoid `W₁(v,G) = E(G, v)` lies inside `C`. -/
  unit_ellipsoid_subset : E(G, v) ⊆ C
  /-- The set `C` lies inside the outer ellipsoid `W_β(v,G)`. -/
  subset_beta_ellipsoid : C ⊆ W[β](v, G)

namespace IsBetaRounding

/-- The source-facing unit-radius inclusion `W₁(v,G) ⊆ C` is the radius-`1` view of the canonical
inner field `E(G, v) ⊆ C`. -/
theorem unit_matrixEllipsoid_subset
    {C : Set E} {β : ℝ} {G : Mat} {v : E}
    (h : IsBetaRounding C β G v) :
    W[1](v, G) ⊆ C := by
  simpa [matrixEllipsoid_one_eq_affineEllipsoid] using h.unit_ellipsoid_subset

end IsBetaRounding

/-- A `β`-rounding canonically supplies the source-facing inner and outer ellipsoid containments
from the definition. -/
instance {C : Set E} {β : ℝ} {G : Mat} {v : E}
    (h : IsBetaRounding C β G v) :
    Fact (W[1](v, G) ⊆ C ∧ C ⊆ W[β](v, G)) where
  out := ⟨h.unit_matrixEllipsoid_subset, h.subset_beta_ellipsoid⟩

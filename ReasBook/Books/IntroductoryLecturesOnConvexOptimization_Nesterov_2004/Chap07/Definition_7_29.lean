/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 7.29 lies in the Chapter 7 centered ellipsoid-rounding domain.

Sampled owner-style declarations:
- `matrixEllipsoid` in `Chap07/Definition_7_26`, the source-facing ellipsoid owner;
- `centeredMatrixEllipsoid_one_eq_affineEllipsoid` in `Chap07/Definition_7_26`, the unit-radius
  bridge for centered ellipsoids;
- `IsBetaRounding` in `Chap07/Definition_7_27`, the chapter owner of ellipsoid roundings with
  arbitrary center and outer radius;
- `IsGammaNRounding` in `Chap07/Definition_7_32`, a nearby positive-definite rounding predicate
  built on the same `W[r](v, G)` ellipsoid surface.

Best owner abstraction:
- source-facing: `IsEllipsoidalRounding` and `IsInitialApproximation`;
- core/canonical: `IsBetaRounding`;
- bridge/view: the centered specialization `v = 0` and the fixed outer radius
  `β = γ * Real.sqrt (n : ℝ)`.

Primitive data:
- a set `C : Set E`;
- a matrix `G : Mat`;
- positive definiteness of `G`;
- a centered `β`-rounding of `C`.

Derived API:
- the unit centered ellipsoid inclusion `W[1](G) ⊆ C`;
- the outer inclusion `C ⊆ W[(γ * Real.sqrt (n : ℝ))](G)`;
- the `Fact` instance and the existential outer-radius view for initial approximations.

The duplicate wheel in the previous file was the centered rounding data itself: it restated the
same inclusion pattern already owned by `IsBetaRounding`. This file now keeps the source-facing
names, but reuses the chapter owner directly and derives the centered view from it.
-/

/-- Definition 7.29: for a convex centrally symmetric body `C ⊆ ℝⁿ`, an ellipsoidal rounding of
radius `γ √n` is a positive-definite matrix `G` such that the unit centered ellipsoid `W₁(G)` is
contained in `C` and `C` is contained in `W_(γ √n)(G)`. -/
abbrev IsEllipsoidalRounding (C : Set E) (gamma : ℝ) (G : Mat) : Prop :=
  G.PosDef ∧ IsBetaRounding C (gamma * Real.sqrt (n : ℝ)) G (0 : E)

namespace IsEllipsoidalRounding

theorem posDef {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    G.PosDef :=
  h.1

theorem toIsBetaRounding {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    IsBetaRounding C (gamma * Real.sqrt (n : ℝ)) G (0 : E) :=
  h.2

theorem unit_ellipsoid_subset {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    W[1](G) ⊆ C := by
  simpa using h.toIsBetaRounding.unit_matrixEllipsoid_subset

theorem subset_outer_ellipsoid {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    C ⊆ W[(gamma * Real.sqrt (n : ℝ))](G) := by
  simpa using h.toIsBetaRounding.subset_beta_ellipsoid

end IsEllipsoidalRounding

/-- An ellipsoidal rounding records positive definiteness together with the inner and outer
centered-ellipsoid inclusions from the definition. -/
instance {C : Set E} {gamma : ℝ} {G : Mat}
    (h : IsEllipsoidalRounding C gamma G) :
    Fact (G.PosDef ∧ W[1](G) ⊆ C ∧ C ⊆ W[(gamma * Real.sqrt (n : ℝ))](G)) where
  out := ⟨h.posDef, h.unit_ellipsoid_subset, h.subset_outer_ellipsoid⟩

/-- An initial approximation is a positive-definite matrix whose unit centered ellipsoid lies in
`C` and for which `C` is contained in some centered ellipsoid `W_R(G0)` with `R ≥ 1`. -/
abbrev IsInitialApproximation (C : Set E) (G0 : Mat) : Prop :=
  G0.PosDef ∧ ∃ R : ℝ, 1 ≤ R ∧ IsBetaRounding C R G0 (0 : E)

namespace IsInitialApproximation

theorem posDef {C : Set E} {G0 : Mat} (h : IsInitialApproximation C G0) :
    G0.PosDef :=
  h.1

theorem exists_betaRounding {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    ∃ R : ℝ, 1 ≤ R ∧ IsBetaRounding C R G0 (0 : E) :=
  h.2

theorem unit_ellipsoid_subset {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    W[1](G0) ⊆ C := by
  rcases h.exists_betaRounding with ⟨R, hR, hrounding⟩
  simpa using hrounding.unit_matrixEllipsoid_subset

theorem exists_outer_radius {C : Set E} {G0 : Mat}
    (h : IsInitialApproximation C G0) :
    ∃ R : ℝ, 1 ≤ R ∧ C ⊆ W[R](G0) := by
  rcases h.exists_betaRounding with ⟨R, hR, hrounding⟩
  exact ⟨R, hR, by simpa using hrounding.subset_beta_ellipsoid⟩

end IsInitialApproximation

end

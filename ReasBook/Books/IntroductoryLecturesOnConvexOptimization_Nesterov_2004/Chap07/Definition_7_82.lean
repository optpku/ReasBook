/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n m : ℕ}

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin m)

/- Definition 7.82 lies in the chapter's affine-preimage / feasible-set pullback domain.

Mandatory domain-style sampling before refinement:
- `Set.preimage`, the canonical owner for inverse-image subsets;
- `LinearMap.toAffineMap`, the owner bridge from a linear map to an affine map;
- `AffineMap.const`, the canonical translation owner;
- `ClosedConvexOn.comp_linearMap_add` in `Chap03/Theorem_3_1_6`, the nearby chapter bridge that
  already packages `x ↦ A x + b` as an affine map instead of keeping a parallel set owner.

Best owner abstraction:
- `Set.preimage` along the affine map `A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b`.

Primitive data:
- the matrix `A`;
- the translation vector `b`;
- the target set `Qx`.

Derived API:
- the source-facing matrix-and-shift specialization of the preimage set;
- the atomic membership bridge `mem_preimage_linearMap_add_iff`.

Source/core/bridge triage:
- source-facing: Definition 7.82's set `Q_y` cut out by the condition `A y + b ∈ Q_x`;
- core/canonical: `Set.preimage`;
- bridge/view: the matrix specialization via `Matrix.toEuclideanLin`, `LinearMap.toAffineMap`,
  and `AffineMap.const`.

This item is exactly the inverse image of `Qx` under the affine map `y ↦ A y + b`. The refined
file therefore keeps the numbered item as a recall-style source-facing entry on the canonical
preimage surface and retains only the thin membership bridge theorem.
-/

section

variable (A : Matrix (Fin n) (Fin m) ℝ) (b : En) (Qx : Set En)

/- Definition 7.82: the associated set `Q_y` is the affine preimage of `Q_x` under
`y ↦ A y + b`. -/
#check ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx : Set Em)

end

/-- Membership in the affine-map preimage of `Qx` is exactly the condition
`A y + b ∈ Qx`. -/
@[simp] theorem mem_preimage_linearMap_add_iff
    {A : Matrix (Fin n) (Fin m) ℝ} {b : En} {Qx : Set En} {y : Em} :
    y ∈ ((A.toEuclideanLin.toAffineMap +ᵥ AffineMap.const ℝ Em b) ⁻¹' Qx) ↔
      A.toEuclideanLin y + b ∈ Qx :=
  Iff.rfl

end

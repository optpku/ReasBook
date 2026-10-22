/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-
Proposition 6.46 lies in the chapter's attained affine-minorant / tangent-identity domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the Chapter 6 owner for affine-dual
  supremum objectives;
- `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the canonical feasible-maximizer
  owner for that supremum;
- `smoothedPrimalObjectiveArgmax.value_eq` in `Chap06/Theorem_6_1`, the owner-level attained-value
  theorem;
- `ContinuousLinearMap.flip` together with `InnerProductSpace.toDual`, the canonical transpose /
  Riesz interface for the vector form of `A^* u`.

Best owner abstraction:
- source-facing: Proposition 6.46's affine tangent identity at an attained maximizer;
- core/canonical: `smoothedPrimalObjective A Qd 0 g 0 0` and
  `smoothedPrimalObjectiveArgmax A Qd g 0 0`;
- bridge/view: the zero-smoothing specialization and the vector representative
  `(InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)` of the transpose field.

Primitive data:
- a continuous linear pairing map `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- a dual feasible set `Qd : Set E₂`;
- a dual term `g : E₂ → ℝ`;
- a point `xBar : E₁` and an attained maximizer `uBar` in the canonical argmax owner.

Derived API:
- the zero-smoothed value function `smoothedPrimalObjective A Qd 0 g 0 0`;
- the attained value identity at `xBar`, via `smoothedPrimalObjectiveArgmax.value_eq`;
- the affine tangent identity once the gradient is identified with the Riesz representative of
  `A.flip uBar`.

Source/core/bridge triage:
- source-facing: the proposition below;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`, and `A.flip`;
- bridge/view: the specialization `hatf = 0`, `d₂ = 0`, `μ₂ = 0` and the Riesz identification of
  `A^* uBar`.

The previous file introduced a local owner `affineMinorantValueFunction` that was definitionally
the zero-smoothed Chapter 6 owner `smoothedPrimalObjective A Qd 0 g 0 0`, kept a redundant primal
set parameter only through subtype binders, and specialized the ambient spaces to coordinate
Euclidean models. This refinement states the proposition directly on the canonical owner surface,
removes the unused primal-set packaging, and weakens the ambient assumptions to the intrinsic
inner-product / dual-pairing layer actually used by the statement.
-/

-- Proof sketch: use `smoothedPrimalObjectiveArgmax.value_eq` to identify the value at `xBar` with
-- `A xBar uBar - g uBar`, rewrite the gradient term by `hgrad` and the pairing identity
-- `⟪(InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar), x - xBar⟫ = A (x - xBar) uBar`, and then
-- expand the linear term with `A.map_sub`.
/-- Proposition 6.46: if `uBar` attains the supremum defining the zero-smoothed Chapter 6 primal
objective at `xBar` and the gradient at `xBar` is the vector representative of `A^* uBar`, then
for every `x` the affine tangent identity
`f(xBar) + ⟪∇f(xBar), x - xBar⟫ = A x uBar - g uBar` holds for
`f = smoothedPrimalObjective A Qd 0 g 0 0`. -/
theorem affine_minorant_identity
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Qd : Set E₂} {g : E₂ → ℝ}
    {xBar x : E₁} {uBar : E₂}
    (huBar : uBar ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 xBar)
    (hgrad :
      ∇ (smoothedPrimalObjective A Qd 0 g 0 0) xBar =
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)) :
    smoothedPrimalObjective A Qd 0 g 0 0 xBar +
        inner ℝ (∇ (smoothedPrimalObjective A Qd 0 g 0 0) xBar) (x - xBar) =
      A x uBar - g uBar := by
  have hvalue := smoothedPrimalObjectiveArgmax.value_eq huBar
  have hvalue' :
      smoothedPrimalObjective A Qd 0 g 0 0 xBar = A xBar uBar - g uBar := by
    simpa [smoothedPrimalObjectiveMaximand] using hvalue
  have hpair :
      inner ℝ ((InnerProductSpace.toDual ℝ E₁).symm (A.flip uBar)) (x - xBar) =
        A (x - xBar) uBar := by
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.flip_apply]
  rw [hgrad, hpair]
  calc
    smoothedPrimalObjective A Qd 0 g 0 0 xBar + A (x - xBar) uBar
        = (A xBar uBar - g uBar) + A (x - xBar) uBar := by rw [hvalue']
    _ = (A xBar uBar - g uBar) + (A x uBar - A xBar uBar) := by
          simp
    _ = A x uBar - g uBar := by ring

end

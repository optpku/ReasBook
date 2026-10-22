/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {ι : Type v}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "E₂" => EuclideanSpace ℝ ι

/- Definition 6.24 lies in the Chapter 6 box-smoothing / regularized-supremum domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner of the regularized
  maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d(u)`;
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter owner of the corresponding supremum
  objective;
- mathlib `EuclideanSpace.proj`, the canonical coordinate linear functionals on
  `EuclideanSpace ℝ ι`;
- `Definition_6_19`, a nearby Chapter 6 specialization that keeps only the source-facing data and
  defines the final smoothing as a thin specialization of `smoothedPrimalObjective`.

Best owner abstraction:
- source-facing: the dual box `Q₂`, the weighted quadratic prox-function `d₂`, and the final
  smoothed objective attached to the row family `a` and offsets `b`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand`;
- bridge/view: the row-induced linear map `A`, the affine penalty `u ↦ ∑ⱼ bⱼ uⱼ`, and the
  coordinate expansion theorems below.

Primitive data:
- the row family `a : ι → StrongDual ℝ E`;
- the offset family `b : EuclideanSpace ℝ ι`;
- the positive smoothing parameter `μ`;
- the box set `Q₂` and the weighted quadratic prox-function `d₂`.

Derived API:
- the owner-level box specialization `quadratic_box_smoothed_objective`;
- the coordinate expansion of the canonical maximand;
- the coordinate expansion of the canonical supremum formula.

Source/core/bridge triage:
- source-facing: `quadratic_box_dual_set`, `quadratic_box_prox_function`,
  `quadratic_box_smoothed_objective`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveMaximand`;
- bridge/view: `quadraticBoxLinearMap`, `quadraticBoxAffinePenalty`, and the companion expansion
  theorems.

The previous revision duplicated the chapter owner by introducing a second public maximand and a
second public regularized-supremum objective specialized to the box model. This file keeps the
source-facing box set and prox term, but deletes the duplicate smoothing owners and defines the
final objective directly through `smoothedPrimalObjective`.
-/

/-- The dual box `Q₂ = {u : EuclideanSpace ℝ ι | |uⱼ| ≤ 1 for every j}` used in the quadratic
prox smoothing scheme; the textbook `ℝ^m` presentation is recovered by specializing
`ι = Fin m`. -/
def quadratic_box_dual_set : Set E₂ :=
  {u | ∀ j : ι, |u j| ≤ (1 : ℝ)}

/-- Membership in `quadratic_box_dual_set` is exactly the coordinatewise box condition
`|uⱼ| ≤ 1`. -/
@[simp] theorem mem_quadratic_box_dual_set_iff {u : E₂} :
    u ∈ quadratic_box_dual_set ↔ ∀ j : ι, |u j| ≤ (1 : ℝ) :=
  Iff.rfl

section

variable [Fintype ι]

/-- The weighted quadratic prox-function
`d₂(u) = (1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2` attached to the row family `a`. -/
def quadratic_box_prox_function (a : ι → StrongDual ℝ E) : E₂ → ℝ :=
  fun u ↦ (1 / 2 : ℝ) * ∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ)

/-- Evaluating `quadratic_box_prox_function a` gives the weighted half-sum
`(1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2`. -/
@[simp] theorem quadratic_box_prox_function_apply
    (a : ι → StrongDual ℝ E) (u : E₂) :
    quadratic_box_prox_function a u =
      (1 / 2 : ℝ) * ∑ j : ι, ‖a j‖ * (u j) ^ (2 : ℕ) :=
  rfl

/-- The affine penalty `u ↦ ∑ⱼ bⱼ uⱼ` feeding the chapter owner `smoothedPrimalObjective`. -/
private def quadraticBoxAffinePenalty (b : E₂) : E₂ → ℝ :=
  fun u ↦ ∑ j : ι, b j * u j

/-- The row family `a : ι → E₁*` as the linear map `x ↦ (u ↦ ∑ⱼ aⱼ(x) uⱼ)` into the dual of
`EuclideanSpace ℝ ι`; the textbook `a₁, …, aₘ` model is recovered by specializing `ι = Fin m`. -/
private def quadraticBoxLinearMap (a : ι → StrongDual ℝ E) :
    E →L[ℝ] StrongDual ℝ E₂ :=
  ∑ j : ι, (a j).smulRight (EuclideanSpace.proj j)

@[simp] private theorem quadraticBoxLinearMap_apply
    (a : ι → StrongDual ℝ E) (x : E) (u : E₂) :
    quadraticBoxLinearMap a x u = ∑ j : ι, a j x * u j := by
  simp [quadraticBoxLinearMap, EuclideanSpace.coe_proj, mul_comm]

/-- Expanding the chapter owner maximand for the quadratic box model gives the textbook coordinate
formula `⟪Ax - b, u⟫ - μ d₂(u)`. -/
@[simp] theorem quadratic_box_smoothed_maximand_apply
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) (u : E₂) :
    smoothedPrimalObjectiveMaximand
        (quadraticBoxLinearMap a)
        (quadraticBoxAffinePenalty b)
        (quadratic_box_prox_function a)
        (μ : ℝ) x u =
      (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u := by
  rw [smoothedPrimalObjectiveMaximand, quadraticBoxLinearMap_apply, quadraticBoxAffinePenalty]
  calc
    (∑ j : ι, a j x * u j) - ∑ j : ι, b j * u j - (μ : ℝ) * quadratic_box_prox_function a u
        = (∑ j : ι, (a j x * u j - b j * u j)) - (μ : ℝ) * quadratic_box_prox_function a u := by
            rw [← Finset.sum_sub_distrib]
    _ = (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u := by
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring

/-- The source-facing smooth objective from Definition 6.24: for a finite row family
`a : ι → E₁*`, offsets `b : EuclideanSpace ℝ ι`, the box
`Q₂ = {u : EuclideanSpace ℝ ι : |uⱼ| ≤ 1}`, and the weighted quadratic prox-function
`d₂(u) = (1 / 2) * ∑ⱼ ‖aⱼ‖ * (uⱼ)^2`, this is the Chapter 6 regularized-supremum owner
specialized to the box model; the textbook presentation is recovered by specializing `ι = Fin m`.
-/
abbrev quadratic_box_smoothed_objective
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  smoothedPrimalObjective
    (quadraticBoxLinearMap a)
    quadratic_box_dual_set
    0
    (quadraticBoxAffinePenalty b)
    (quadratic_box_prox_function a)
    (μ : ℝ)

/-- `quadratic_box_smoothed_objective` is exactly the Chapter 6 regularized-supremum owner
specialized to the box model data `(A, Q₂, \hat f, \hat φ, d₂)`. -/
@[simp] theorem quadratic_box_smoothed_objective_def
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) :
    quadratic_box_smoothed_objective a b μ =
      smoothedPrimalObjective
        (quadraticBoxLinearMap a)
        quadratic_box_dual_set
        0
        (quadraticBoxAffinePenalty b)
        (quadratic_box_prox_function a)
        (μ : ℝ) :=
  rfl

/-- Definition 6.24: evaluating `quadratic_box_smoothed_objective a b μ` gives the textbook
supremum of the penalized affine maximand over the dual box `Q₂`. -/
-- Proof sketch: unfold `quadratic_box_smoothed_objective`, rewrite by
-- `smoothedPrimalObjective_apply`, and simplify the maximand with
-- `quadratic_box_smoothed_maximand_apply`.
theorem quadratic_box_smoothed_objective_spec
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    quadratic_box_smoothed_objective a b μ x =
      sSup
        ((fun u : E₂ ↦
            (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u) ''
          quadratic_box_dual_set) := by
  -- Expand the box-smoothed objective through the chapter owner formula.
  rw [quadratic_box_smoothed_objective_def, smoothedPrimalObjective_apply]
  -- Simplify the zero source term and rewrite the owner maximand to coordinates.
  simp [quadratic_box_smoothed_maximand_apply]

/-- Evaluating `quadratic_box_smoothed_objective a b μ` recovers the supremum of the penalized
affine maximand over the dual box `Q₂`. -/
@[simp] theorem quadratic_box_smoothed_objective_apply
    (a : ι → StrongDual ℝ E) (b : E₂) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    quadratic_box_smoothed_objective a b μ x =
      sSup
        ((fun u : E₂ ↦
            (∑ j : ι, (a j x - b j) * u j) - (μ : ℝ) * quadratic_box_prox_function a u) ''
          quadratic_box_dual_set) :=
  quadratic_box_smoothed_objective_spec a b μ x

end

end

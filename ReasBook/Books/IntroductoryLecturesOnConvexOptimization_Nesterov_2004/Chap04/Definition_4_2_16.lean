/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelSetNotation

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 4.2.16 lies in the normed-space cubic-regularization / sublevel-radius domain.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the earlier project owner
  for a regularized objective centered at a base point;
* `𝓛[f](α)` / `mem_levelSet_iff` in `Chap01/Definition_1_4_8`, the project owner for lower level
  sets;
* `NonlinearConvexTransformation.D_isGreatest` in `Chap04/Definition_4_1_10`, the nearby project
  pattern for a textbook radius constant recorded by an attained maximum;
* `IsGreatest` in mathlib, the canonical order-theoretic owner for an attained maximum.

Source/core/bridge triage:
* source-facing: the cubically regularized objective and the textbook radius constant `D` of the
  initial sublevel set;
* core/canonical: `cubicallyRegularizedObjective f δ x₀`, `𝓛[f]((f x₀))`, and `IsGreatest`;
* bridge/view: the initial-sublevel distance set `initialSublevelDistanceSet f x₀`.

Primitive data:
* the objective `f`;
* the base point `x₀`;
* the regularization parameter `δ`.

Derived API:
* evaluation of the cubic regularization owner at a point;
* the bridge set of distances on the canonical initial sublevel set;
* membership in that bridge set from a sublevel inequality;
* the source-facing radius statement `IsGreatest (initialSublevelDistanceSet f x₀) D`.

The cubic perturbation is first introduced here, so it remains the public owner. The sublevel-set
part, however, is already canonical earlier in the chapter, and the textbook radius is an attained
maximum rather than an unconditional supremum. This file therefore keeps the sublevel set itself
canonical, exposes only the distance-image bridge set, and records the radius through
`IsGreatest` instead of a parallel always-defined `ℝ`-valued wrapper. -/

/-- Definition 4.2.16: the cubically regularized objective associated to `f`, the reference point
`x₀`, and the parameter `δ` is the function `x ↦ f x + (δ / 3) ‖x - x₀‖^3`. -/
def cubicallyRegularizedObjective
    (f : E → ℝ) (δ : ℝ) (x0 : E) : E → ℝ :=
  fun x ↦ f x + (δ / 3) * ‖x - x0‖ ^ (3 : ℕ)

/-- Evaluating the cubically regularized objective at `x` gives the defining cubic penalty term
centered at `x₀`. -/
@[simp]
theorem cubicallyRegularizedObjective_apply
    (f : E → ℝ) (δ : ℝ) (x0 x : E) :
    cubicallyRegularizedObjective f δ x0 x =
      f x + (δ / 3) * ‖x - x0‖ ^ (3 : ℕ) :=
  rfl

/-- A nonnegative cubic regularization parameter can only increase the objective value. -/
theorem le_cubicallyRegularizedObjective_of_nonneg
    (f : E → ℝ) (x0 x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    f x ≤ cubicallyRegularizedObjective f δ x0 x := by
  rw [cubicallyRegularizedObjective_apply]
  have hnonneg : 0 ≤ (δ / 3) * ‖x - x0‖ ^ (3 : ℕ) := by
    positivity
  linarith

/-- The set of distances from `x₀` attained on the initial sublevel set `{x | f x ≤ f x₀}`. -/
def initialSublevelDistanceSet (f : E → ℝ) (x0 : E) : Set ℝ :=
  (fun x : E ↦ ‖x - x0‖) '' (𝓛[f]((f x0)) : Set E)

/-- Membership in `initialSublevelDistanceSet f x₀` means that the radius is realized by some
point of the initial sublevel set `{x | f x ≤ f x₀}`. -/
@[simp]
theorem mem_initialSublevelDistanceSet_iff
    {f : E → ℝ} {x0 : E} {r : ℝ} :
    r ∈ initialSublevelDistanceSet f x0 ↔
      ∃ x : E, f x ≤ f x0 ∧ ‖x - x0‖ = r := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa using hx, rfl⟩
  · rintro ⟨x, hx, hnorm⟩
    exact ⟨x, by simpa using hx, hnorm⟩

/-- Any point of the initial sublevel set contributes its distance to `x₀` to the canonical
distance-image bridge set. -/
theorem norm_sub_mem_initialSublevelDistanceSet
    {f : E → ℝ} {x0 x : E} (hx : f x ≤ f x0) :
    ‖x - x0‖ ∈ initialSublevelDistanceSet f x0 :=
  Set.mem_image_of_mem _ (by simpa using hx)

/-- If `D` is an attained maximum of the initial-sublevel distance set, then every point of the
canonical initial level set `𝓛[f]((f x₀))` is at distance at most `D` from `x₀`. -/
theorem norm_sub_le_of_mem_levelSet_of_initialSublevelDistanceSet_isGreatest
    {f : E → ℝ} {x0 x : E} {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : x ∈ (𝓛[f]((f x0)) : Set E)) :
    ‖x - x0‖ ≤ D :=
  hD.2 (Set.mem_image_of_mem _ hx)

/-- If `D` is an attained maximum of the initial-sublevel distance set, then every point in the
initial sublevel set is at distance at most `D` from `x₀`. -/
theorem norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest
    {f : E → ℝ} {x0 x : E} {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : f x ≤ f x0) :
    ‖x - x0‖ ≤ D := by
  exact
    norm_sub_le_of_mem_levelSet_of_initialSublevelDistanceSet_isGreatest hD
      (by simpa using hx)

section

variable (f : E → ℝ) (x0 : E) (D : ℝ)

/- Definition 4.2.16: the textbook radius `D` of the initial sublevel set is recorded canonically
as the attained-maximum statement `IsGreatest (initialSublevelDistanceSet f x₀) D`. -/
#check IsGreatest (initialSublevelDistanceSet f x0) D

end

end

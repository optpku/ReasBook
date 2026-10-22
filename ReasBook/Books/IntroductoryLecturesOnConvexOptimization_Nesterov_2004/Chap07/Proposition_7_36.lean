/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin RelativeScaleTransformNotation

noncomputable section

universe u

variable {X : Type u}

/- Proposition 7.36 lies in the monotone objective-transform / constrained argmin domain.

Relevant owner-style declarations sampled before refinement:
- `relativeScaleTransformedObjective` and `relativeScaleTransformedObjective_apply` in
  `Chap07/Lemma_7_20`, the existing Chapter 7 owner for the half-squared transform
  `x ↦ (1 / 2) * f(x)^2`;
- mathlib `IsMinOn` and `IsMinOn.comp_mono`, the canonical minimizer owner and monotone transport
  lemma for objective transforms;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner for
  constrained minimizer sets.

Best owner abstraction:
- source-facing: Proposition 7.36's equivalence between minimizing `f` on `Q` and minimizing its
  half-squared transform on `Q`;
- core/canonical: `relativeScaleTransformedObjective`, `IsMinOn`, and `argmin[Q]`;
- bridge/view: the minimizer and argmin equivalence lemmas below.

Primitive data:
- the feasible set `Q`;
- the objective `f : X → ℝ`;
- pointwise nonnegativity of `f` on `Q`.

Derived API:
- `isMinOn_relativeScaleTransformedObjective_iff`;
- `mem_argmin_relativeScaleTransformedObjective_iff`;
- `argmin_eq_argmin_relativeScaleTransformedObjective`.

The previous version introduced a second local owner `halfSquaredObjective` and encoded argmin sets
as raw set comprehensions. This refinement deletes that duplicate owner, reuses the Chapter 7
transform directly, and states the proposition on the canonical constrained-argmin surface.
-/

/- On the feasible set, minimizing `f` is equivalent to minimizing `f̂` when `f` is nonnegative
there. -/
/-- Helper for Proposition 7.36: on nonnegative reals, the map `t ↦ (1 / 2) * t^2` preserves and
reflects order. -/
-- Proof sketch: pass between inequalities on half-squares and inequalities on squares using the
-- positive factor `(1 / 2 : ℝ)`, then use `sq_le_sq₀` on nonnegative inputs.
theorem halfSquared_le_halfSquared_iff_of_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((1 / 2 : ℝ) * a ^ 2 ≤ (1 / 2 : ℝ) * b ^ 2) ↔ a ≤ b := by
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 := hhalf_pos.le
  have hsquare_iff : a ^ 2 ≤ b ^ 2 ↔ a ≤ b := sq_le_sq₀ ha hb
  constructor
  · intro hhalf
    -- Remove the positive scalar factor to recover the square comparison.
    have hsquare : a ^ 2 ≤ b ^ 2 := le_of_mul_le_mul_left hhalf hhalf_pos
    exact hsquare_iff.mp hsquare
  · intro hab
    -- Reinsert the positive scalar factor after comparing the squares.
    have hsquare : a ^ 2 ≤ b ^ 2 := hsquare_iff.mpr hab
    exact mul_le_mul_of_nonneg_left hsquare hhalf_nonneg

-- Proof sketch: for `x ∈ Q`, the nonnegativity hypothesis gives `0 ≤ f x` and `0 ≤ f y` for every
-- `y ∈ Q`. On `ℝ≥0`, the scalar map `t ↦ (1 / 2) * t^2` is order-reflecting, so the inequalities
-- defining `IsMinOn` for `f` and for `f̂` are equivalent.
theorem isMinOn_relativeScaleTransformedObjective_iff
    {Q : Set X} {f : X → ℝ} {x : X}
    (hf_nonneg : ∀ y ∈ Q, 0 ≤ f y) (hx : x ∈ Q) :
    IsMinOn f̂ Q x ↔ IsMinOn f Q x := by
  have hx_nonneg : 0 ≤ f x := hf_nonneg x hx
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro hminHalf y hy
    have hy_nonneg : 0 ≤ f y := hf_nonneg y hy
    -- Rewrite the transformed-objective comparison into a scalar half-square inequality.
    have hhalf : (1 / 2 : ℝ) * (f x) ^ 2 ≤ (1 / 2 : ℝ) * (f y) ^ 2 := by
      simpa [relativeScaleTransformedObjective_apply] using hminHalf y hy
    exact (halfSquared_le_halfSquared_iff_of_nonneg hx_nonneg hy_nonneg).mp hhalf
  · intro hmin y hy
    have hy_nonneg : 0 ≤ f y := hf_nonneg y hy
    -- Use the same bridge lemma in the forward direction, then rewrite back to `f̂`.
    have hhalf : (1 / 2 : ℝ) * (f x) ^ 2 ≤ (1 / 2 : ℝ) * (f y) ^ 2 :=
      (halfSquared_le_halfSquared_iff_of_nonneg hx_nonneg hy_nonneg).mpr (hmin y hy)
    simpa [relativeScaleTransformedObjective_apply] using hhalf

@[simp] theorem mem_argmin_relativeScaleTransformedObjective_iff
    {Q : Set X} {f : X → ℝ} {x : X}
    (hf_nonneg : ∀ x ∈ Q, 0 ≤ f x) :
    x ∈ argmin[Q] f̂ ↔ x ∈ argmin[Q] f := by
  rw [mem_constrainedArgmin_iff, mem_constrainedArgmin_iff]
  constructor
  · rintro ⟨hx, hxmin⟩
    exact ⟨hx, (isMinOn_relativeScaleTransformedObjective_iff hf_nonneg hx).mp hxmin⟩
  · rintro ⟨hx, hxmin⟩
    exact ⟨hx, (isMinOn_relativeScaleTransformedObjective_iff hf_nonneg hx).mpr hxmin⟩

/-- Proposition 7.36: if `f` is nonnegative on `Q`, then the minimizers of `f` on `Q`
coincide with the minimizers of the transformed objective `f̂`, so the two
optimization problems are equivalent. -/
-- Proof sketch: identify `argmin[Q]` membership with feasibility plus `IsMinOn`, then apply
-- `isMinOn_relativeScaleTransformedObjective_iff` pointwise on feasible minimizers.
theorem argmin_eq_argmin_relativeScaleTransformedObjective
    {Q : Set X} {f : X → ℝ}
    (hf_nonneg : ∀ x ∈ Q, 0 ≤ f x) :
    argmin[Q] f = argmin[Q] f̂ := by
  ext x
  exact (mem_argmin_relativeScaleTransformedObjective_iff hf_nonneg).symm

end

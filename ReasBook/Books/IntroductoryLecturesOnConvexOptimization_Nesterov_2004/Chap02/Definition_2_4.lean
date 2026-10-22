/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Primary domain: first-order convex analysis on real normed spaces.

Sampled owner-style declarations in this domain:
* mathlib `ContDiffOn ℝ 1 f Q`
* mathlib `ConvexOn ℝ Q f`
* mathlib `ConcaveOn ℝ Q f`
* Chapter 2 `ConvexC1SeminormSmoothOn p L Q f`, which later specializes the present owner
  abstraction on Euclidean spaces by adding gradient-Lipschitz control

Best owner abstraction:
* primitive core: `ContDiffOn ℝ 1 f Q` together with `ConvexOn ℝ Q f`
* bridge/view: the concave side via the canonical sign change `f ↦ -f`

Source/core/bridge triage:
* source-facing: the textbook class `𝓕¹(Q)`
* core/canonical: the owner pair `ContDiffOn ℝ 1 f Q` and `ConvexOn ℝ Q f`
* bridge/view: the concave counterpart `ConcaveC1On Q f`, derived from `ConvexC1On Q (-f)`

Primitive data:
* the feasible set `Q`
* the objective `f`
* `ContDiffOn ℝ 1 f Q`
* `ConvexOn ℝ Q f`

Derived API:
* projections `convexC1On_contDiffOn` and `convexC1On_convexOn`
* affine-precomposition closure via `ConvexC1On.comp_continuousAffineMap` and its Euclidean
  specialization `ConvexC1On.comp_affineMap`
* the concave view `ConcaveC1On` and its owner projections
-/

/-- Definition 2.4: a function on a convex set `Q` belongs to `𝓕¹(Q)` when it is
continuously differentiable on `Q` and is convex there in the canonical owner sense
`ConvexOn ℝ Q f`. Supporting-nesterovHyperplane arguments should use the owner theorem
`ConvexOn.lower_tangent_plane` through `convexC1On_convexOn hf`, so no duplicate wrapper theorem
is kept here. -/
abbrev ConvexC1On (Q : Set E) (f : E → ℝ) : Prop :=
  ContDiffOn ℝ 1 f Q ∧ ConvexOn ℝ Q f

scoped[ConvexC1] notation "𝓕¹(" Q ")" => setOf (ConvexC1On Q)
open scoped ConvexC1

/-- A function on `Q` is `C¹` concave when its negative belongs to `ConvexC1On Q`. This keeps
the convex owner pair `ContDiffOn ℝ 1` plus `ConvexOn` as primitive data and treats concavity as
the canonical sign-reversed view. -/
abbrev ConcaveC1On (Q : Set E) (f : E → ℝ) : Prop :=
  ConvexC1On Q (-f)

variable {Q : Set E} {f : E → ℝ}

/-- The textbook class notation `𝓕¹(Q)` is the source-facing set view of the owner predicate
`ConvexC1On Q`. -/
theorem mem_F1_iff : f ∈ 𝓕¹(Q) ↔ ConvexC1On Q f :=
  Iff.rfl

/-- Membership in `ConvexC1On Q f` includes `C¹` regularity on `Q`. -/
theorem convexC1On_contDiffOn (hf : ConvexC1On Q f) : ContDiffOn ℝ 1 f Q :=
  hf.1

/-- Membership in `ConvexC1On Q f` includes convexity on `Q`. -/
theorem convexC1On_convexOn (hf : ConvexC1On Q f) : ConvexOn ℝ Q f :=
  hf.2

/-- Nonnegative scalar multiplication preserves membership in `ConvexC1On`. -/
theorem ConvexC1On.smul
    {Q : Set E} {f : E → ℝ} (hf : ConvexC1On Q f) {α : ℝ} (hα : 0 ≤ α) :
    ConvexC1On Q (α • f) := by
  refine ⟨?_, ?_⟩
  · simpa [Pi.smul_apply] using (convexC1On_contDiffOn hf).const_smul α
  · simpa [Pi.smul_apply] using (convexC1On_convexOn hf).smul hα

/-- Addition preserves membership in `ConvexC1On`. -/
theorem ConvexC1On.add
    {Q : Set E} {f g : E → ℝ} (hf : ConvexC1On Q f) (hg : ConvexC1On Q g) :
    ConvexC1On Q (f + g) := by
  refine ⟨?_, ?_⟩
  · simpa using (convexC1On_contDiffOn hf).add (convexC1On_contDiffOn hg)
  · simpa using (convexC1On_convexOn hf).add (convexC1On_convexOn hg)

/-- Nonnegative linear combinations preserve membership in `ConvexC1On`. -/
theorem ConvexC1On.nonneg_combo
    {Q : Set E} {f₁ f₂ : E → ℝ} (hf₁ : ConvexC1On Q f₁) (hf₂ : ConvexC1On Q f₂)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ConvexC1On Q (α • f₁ + β • f₂) := by
  exact (hf₁.smul hα).add (hf₂.smul hβ)

/-- Precomposing a `C¹` convex function with a continuous affine map preserves membership in
`ConvexC1On`. This is the canonical owner-level precomposition theorem; Euclidean affine-map
specializations should be derived from it. -/
theorem ConvexC1On.comp_continuousAffineMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : Set E} {f : E → ℝ} (hf : ConvexC1On Q f)
    (g : F →ᴬ[ℝ] E) :
    ConvexC1On (g ⁻¹' Q) (f ∘ g) := by
  refine ⟨?_, ?_⟩
  · exact (convexC1On_contDiffOn hf).comp g.contDiff.contDiffOn (fun _ hx ↦ hx)
  · simpa using (convexC1On_convexOn hf).comp_affineMap (g : F →ᵃ[ℝ] E)

/-- In Euclidean spaces, affine precomposition preserves membership in `ConvexC1On`. This is the
source-facing finite-dimensional specialization of `ConvexC1On.comp_continuousAffineMap`. -/
theorem ConvexC1On.comp_affineMap
    {m n : ℕ}
    {Q : Set (EuclideanSpace ℝ (Fin m))}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ConvexC1On Q f)
    (g : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ConvexC1On (g ⁻¹' Q) (f ∘ g) := by
  simpa using hf.comp_continuousAffineMap ⟨g, g.continuous_of_finiteDimensional⟩

/-- Membership in `ConcaveC1On Q f` includes `C¹` regularity on `Q`. -/
theorem concaveC1On_contDiffOn (hf : ConcaveC1On Q f) : ContDiffOn ℝ 1 f Q := by
  simpa using (convexC1On_contDiffOn hf).neg

/-- Membership in `ConcaveC1On Q f` includes concavity on `Q`. -/
theorem concaveC1On_concaveOn (hf : ConcaveC1On Q f) : ConcaveOn ℝ Q f := by
  simpa using (convexC1On_convexOn hf).neg

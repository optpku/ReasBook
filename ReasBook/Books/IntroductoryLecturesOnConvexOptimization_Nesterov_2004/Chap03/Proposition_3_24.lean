/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.24 lies in the chapter's constrained-subdifferential / feasible-set convexity
domain.

Mandatory domain-style sampling before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real part of an extended-real-valued function;
- `constrainedSubdifferential` together with the notation `∂[Q] f(x)` in `Definition_3_1_5`, the
  feasible-set owner for subgradients on a constrained domain;
- `convexOn_of_constrainedSubdifferential_nonempty` and
  `lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty` in `Corollary_3_1_8`, the
  chapter owners for the convexity and lower-semicontinuity consequences on a feasible set.

Best owner abstraction:
- source-facing main conclusion: convexity and lower semicontinuity of `withTopRealPart f` on
  `Q₁`;
- core/canonical owners: `dom f`, `∂[Q₁] f(x)`, `ConvexOn`, and `LowerSemicontinuousOn`;
- bridge/view: the feasible-set parameter `Q₁`, together with the ambient extension recording
  `dom f ⊆ Q₁`.

Primitive data:
- the feasible set `Q₁`;
- the extended-real-valued ambient extension `f`;
- the convexity of the feasible set `Q₁`;
- the properness hypothesis `(dom f).Nonempty`;
- the source-faithful domain inclusion `dom f ⊆ Q₁`;
- the owner-level constrained-subdifferential data on `Q₁`.

Derived API:
- convexity and lower semicontinuity of `withTopRealPart f` on `Q₁`;
- the source-facing bridge from a convex-hull presentation
  `∂[Q₁] f(x) = convexHull ℝ (Y x)` with `Y x` nonempty on `Q₁`.

Source/core/bridge triage:
- source-facing: a proper function on `Q₁`;
- core/canonical: the constrained subdifferential `∂[Q₁] f(x)` on the feasible set `Q₁` and the
  two owner consequences on `withTopRealPart f`;
- bridge/view: encoding a function on `Q₁` by an ambient `WithTop ℝ`-valued function whose
  effective domain lies in `Q₁`.

Semantic search note: `lean_leansearch` did not surface the chapter-local constrained-subgradient
corollary directly, so the owner choice here is fixed by the local APIs
`constrainedSubdifferential`,
`convexOn_of_constrainedSubdifferential_nonempty`, and
`lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty`.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Proposition 3.24: encode a function on `Q₁` by an ambient extension `f` with
`dom f ⊆ Q₁`. If `Q₁` is convex, `f` is proper, and every constrained subdifferential
`∂[Q₁] f(x)` on `Q₁` is nonempty, then the finite real part of `f` is convex and lower
semicontinuous on `Q₁`. -/
theorem closedConvexFunction_of_subdifferential_nonempty
    {Q₁ : Set E} {f : E → WithTop ℝ}
    (hQ₁_convex : Convex ℝ Q₁)
    (_hdom : dom f ⊆ Q₁)
    (_hproper : (dom f).Nonempty)
    (hsub_nonempty : ∀ x ∈ Q₁, (∂[Q₁] f(x)).Nonempty) :
    ConvexOn ℝ Q₁ (withTopRealPart f) ∧
      LowerSemicontinuousOn (withTopRealPart f) Q₁ := by
  -- The imported owner theorems already provide the two required consequences.
  exact ⟨convexOn_of_constrainedSubdifferential_nonempty
      (Q := Q₁) (f := f) hQ₁_convex hsub_nonempty,
    lowerSemicontinuousOn_of_constrainedSubdifferential_nonempty
      (Q := Q₁) (f := f) hsub_nonempty⟩

/-- Helper for Proposition 3.24: if `∂[Q₁] f(x)` is presented as `convexHull ℝ (Y x)` and `Y x`
is nonempty, then the constrained subdifferential at `x` is nonempty as well. -/
theorem constrainedSubdifferential_nonempty_of_eq_convexHull
    {Q₁ : Set E} {f : E → WithTop ℝ} {Y : E → Set E}
    {x : E} (hx : x ∈ Q₁)
    (hY_nonempty : ∀ x ∈ Q₁, (Y x).Nonempty)
    (hsubdiff : ∀ x ∈ Q₁, ∂[Q₁] f(x) = convexHull ℝ (Y x)) :
    (∂[Q₁] f(x)).Nonempty := by
  -- Rewrite the subdifferential to the convex-hull presentation and transport nonemptiness.
  simpa [hsubdiff x hx] using
    (convexHull_nonempty_iff (𝕜 := ℝ) (s := Y x)).2 (hY_nonempty x hx)

/-- Proposition 3.24: encode a function on `Q₁` by an ambient extension `f` with `dom f ⊆ Q₁`.
If `Q₁` is convex, `f` is proper, and every constrained subdifferential `∂[Q₁] f(x)` on `Q₁`
is presented as `convexHull ℝ (Y x)` for a nonempty family `Y`, then the finite real part of `f`
is convex and lower semicontinuous on `Q₁`. -/
theorem closedConvexFunction_of_subdifferential_eq_convexHull
    {Q₁ : Set E} {f : E → WithTop ℝ}
    (Y : E → Set E)
    (hQ₁_convex : Convex ℝ Q₁)
    (hdom : dom f ⊆ Q₁)
    (hproper : (dom f).Nonempty)
    (hY_nonempty : ∀ x ∈ Q₁, (Y x).Nonempty)
    (hsubdiff : ∀ x ∈ Q₁, ∂[Q₁] f(x) = convexHull ℝ (Y x)) :
    ConvexOn ℝ Q₁ (withTopRealPart f) ∧
      LowerSemicontinuousOn (withTopRealPart f) Q₁ := by
  -- First derive the pointwise nonemptiness hypothesis expected by the owner theorem package.
  have hsub_nonempty : ∀ x ∈ Q₁, (∂[Q₁] f(x)).Nonempty := by
    intro x hx
    exact constrainedSubdifferential_nonempty_of_eq_convexHull hx hY_nonempty hsubdiff
  -- Then assemble convexity and lower semicontinuity from the chapter-level owner result.
  exact closedConvexFunction_of_subdifferential_nonempty hQ₁_convex hdom hproper hsub_nonempty

end

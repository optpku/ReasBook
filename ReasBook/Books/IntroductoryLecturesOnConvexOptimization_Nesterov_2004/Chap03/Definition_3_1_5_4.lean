/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

/- Definition 3.1.5.4 lives in the chapter's extended-valued convex-analysis domain.

Primary domain:
- convex analysis of extended-real-valued functions on real inner product spaces.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt`
- `subdifferential`
- `mem_subdifferential_iff`
- `constrainedSubdifferential`

Best owner abstraction:
- the pointwise owner `subdifferential` from `Definition_3_1_5`

Primitive data reused from upstream owners:
- the pointwise subdifferentials `subdifferential f x`
- the indexing set `X`

Derived API introduced here:
- `commonRegularSubdifferential`
- the textbook surface notation `∂̂ f(X)`
- `mem_commonRegularSubdifferential_iff`
- the real-valued bridge/view `commonRegularSubdifferentialOn`
- `mem_commonRegularSubdifferentialOn_iff`

Source/core/bridge triage:
- source-facing: the common regular subdifferential `commonRegularSubdifferential f X`
- core/canonical: the pointwise owner `subdifferential`
- bridge/view: `mem_commonRegularSubdifferential_iff` and
  `commonRegularSubdifferentialOn`

The textbook states the notion on `ℝⁿ`, but this construction depends only on the ambient real
inner-product-space structure already used by the upstream subdifferential owner. This file
therefore keeps the same mathematical meaning while matching that owner ambient generality, so
Euclidean downstream uses specialize directly without a second local wrapper layer. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Definition 3.1.5.4: the common regular subdifferential of `f` on `X` is the intersection of
the pointwise subdifferentials `∂f(x)` over all `x ∈ X`. -/
def commonRegularSubdifferential (f : V → WithTop ℝ) (X : Set V) : Set V :=
  ⋂ x ∈ X, ∂ f(x)

/- Lean surface notation for the textbook common subdifferential `∂̂ f(X)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂̂ " f:arg "(" X:arg ")" =>
  commonRegularSubdifferential f X

/-- Membership in the common regular subdifferential means belonging to every pointwise
subdifferential `∂f(x)` for `x ∈ X`. -/
@[simp] theorem mem_commonRegularSubdifferential_iff
    {f : V → WithTop ℝ} {X : Set V} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, g ∈ ∂ f(x) := by
  simp [commonRegularSubdifferential]

/-- Every common regular subgradient on `X` is a pointwise subgradient at each `x ∈ X`. -/
theorem commonRegularSubdifferential_subset_subdifferential
    {f : V → WithTop ℝ} {X : Set V} {x : V} (hx : x ∈ X) :
    ∂̂ f(X) ⊆ ∂ f(x) := by
  intro g hg
  exact (mem_commonRegularSubdifferential_iff.mp hg) x hx

section Bridge

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bridge/view: the common regular subdifferential of a real-valued function on `X` is the
common regular subdifferential of its canonical `WithTop ℝ` lift. Public theorem surfaces for
real-valued objectives can therefore use the textbook notation `∂̂ f(X)` directly. -/
abbrev commonRegularSubdifferentialOn (X : Set V) (f : V → ℝ) : Set V :=
  commonRegularSubdifferential (fun x ↦ (f x : WithTop ℝ)) X

/- Real-valued surface notation for the common regular subdifferential, reusing the same
textbook spelling `∂̂ f(X)` as the upstream `WithTop` owner. -/
scoped[WithTopConvexAnalysis] notation:max "∂̂ " f:arg "(" X:arg ")" =>
  commonRegularSubdifferentialOn X f

/-- For real-valued objectives, membership in `∂̂ f(X)` is exactly the pointwise affine
lower-support inequality on every `x ∈ X`. -/
theorem mem_commonRegularSubdifferentialOn_iff
    {X : Set V} {f : V → ℝ} {g : V} :
    g ∈ ∂̂ f(X) ↔ ∀ x ∈ X, ∀ y : V, f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg x hx
    exact mem_subdifferential_coe_real_iff.mp <|
      (mem_commonRegularSubdifferential_iff.mp hg) x hx
  · intro hg
    rw [mem_commonRegularSubdifferential_iff]
    intro x hx
    exact mem_subdifferential_coe_real_iff.mpr <| hg x hx

end Bridge

/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u v

/- Definition 3.1.5 is the chapter's source-facing owner for extended-valued subgradients.

Primary domain:
- convex analysis of extended-real-valued functions on real inner product spaces.

Relevant owner-style declarations sampled before refinement:
- `withTopEffectiveDomain`
- `withTopRealPart`
- `ConvexOn ℝ (dom f) (withTopRealPart f)`
- there is no mathlib owner for this exact extended-valued subgradient notion

Best owner abstraction:
- the primitive predicate `IsSubgradientAt`

Primitive data:
- `dom f` from `Definition_3_3`
- the feasible-set condition for constrained subgradients
- the ambient inner-product-space structure used by the affine support inequality

Derived API:
- `subdifferential`
- `constrainedSubdifferential`
- their atomic membership lemmas

Source/core/bridge triage:
- source-facing: Definition 3.1.5's subgradient and subdifferential notions
- core/canonical: the owner bridge `withTopEffectiveDomain` from `Definition_3_3`
- bridge/view: the set-valued APIs derived from `IsSubgradientAt`

The textbook states the notion on `ℝⁿ`, but the source-facing owner declarations only need a real
inner-product space over a seminormed additive group. This file therefore keeps the same
mathematical meaning while lifting the owner API to that intrinsic ambient structure, so downstream
Euclidean uses specialize directly instead of carrying a second local wrapper layer. -/

variable {V : Type u} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Definition 3.1.5, generalized from the textbook Euclidean setting: a vector `g` is a
subgradient of an `ℝ ∪ {+∞}`-valued function `f` at `x0` if `x0` lies in the effective domain of
`f` and the affine function `y ↦ f x0 + ⟪g, y - x0⟫` supports `f` from below on that domain. -/
def IsSubgradientAt (f : V → WithTop ℝ) (x0 g : V) : Prop :=
  x0 ∈ dom f ∧
    ∀ ⦃y : V⦄, y ∈ dom f →
      f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)

/-- A subgradient can only be taken at a point of `dom f`. -/
-- Proof sketch: project the first conjunct from the definition of `IsSubgradientAt`.
theorem IsSubgradientAt.mem_dom
    {f : V → WithTop ℝ} {x0 g : V} (hg : IsSubgradientAt f x0 g) :
    x0 ∈ dom f :=
  hg.1

section AffinePullback

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Precomposing by an affine map pulls a subgradient back along the adjoint of the linear part. -/
theorem IsSubgradientAt.comp_affineMap
    {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {f : W → WithTop ℝ} {g : V →ᵃ[ℝ] W} {x0 : V} {h : W}
    (hh : IsSubgradientAt f (g x0) h) :
    IsSubgradientAt (f ∘ g) x0 (g.linear.adjoint h) := by
  refine ⟨?_, ?_⟩
  · simpa [Function.comp] using hh.mem_dom
  · intro y hy
    have hy' : g y ∈ dom f := by
      simpa [Function.comp] using hy
    have hineq := hh.2 hy'
    have hgsub : g y - g x0 = g.linear (y - x0) := by
      simpa using (g.linearMap_vsub y x0).symm
    have hinner : inner ℝ h (g y - g x0) = inner ℝ (g.linear.adjoint h) (y - x0) := by
      rw [hgsub, ← g.linear.adjoint_inner_left]
    rw [hinner] at hineq
    simpa [Function.comp] using hineq

end AffinePullback

/-- The subdifferential of `f` at `x0` is the set of all subgradients of `f` at `x0`. -/
def subdifferential (f : V → WithTop ℝ) (x0 : V) : Set V :=
  {g | IsSubgradientAt f x0 g}

/- Lean surface notation for the textbook unconstrained subdifferential `∂f(x0)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂ " f:arg "(" x:arg ")" =>
  subdifferential f x

/-- Membership in the subdifferential is exactly the defining subgradient inequality on the
effective domain. -/
-- Proof sketch: unfold `subdifferential`; membership in the defining set is exactly
-- `IsSubgradientAt f x0 g`.
@[simp]
theorem mem_subdifferential_iff
    {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂ f(x0) ↔ IsSubgradientAt f x0 g :=
  Iff.rfl

namespace IsSubgradientAt

/-- For a real-valued function, the canonical `WithTop`-valued subgradient owner is exactly the
usual real-valued affine lower-support inequality. -/
theorem coe_real_iff
    {f : V → ℝ} {x0 g : V} :
    IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x0 g ↔
      ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := by
  constructor
  · intro hg y
    have hy : y ∈ dom (fun z ↦ (f z : WithTop ℝ)) := by
      simp [withTopEffectiveDomain]
    have hineq :
        (((f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      simpa using hg.2 hy
    exact_mod_cast hineq
  · intro h
    refine ⟨by simp [withTopEffectiveDomain], ?_⟩
    intro y hy
    have hineq :
        (((f x0 + inner ℝ g (y - x0) : ℝ) : WithTop ℝ) ≤ (f y : WithTop ℝ)) := by
      exact_mod_cast h y
    simpa using hineq

end IsSubgradientAt

/-- Membership in the lifted subdifferential of a real-valued function is exactly the usual
real-valued affine lower-support inequality. -/
@[simp]
theorem mem_subdifferential_coe_real_iff
    {f : V → ℝ} {x0 g : V} :
    g ∈ ∂ (fun y ↦ (f y : WithTop ℝ))(x0) ↔
      ∀ y : V, f y ≥ f x0 + inner ℝ g (y - x0) := by
  rw [mem_subdifferential_iff, IsSubgradientAt.coe_real_iff]

/-- The constrained subdifferential of `f` at `x0` relative to `Q` is the set of vectors whose
affine minorant inequality holds for every `y ∈ Q`, with `x0` itself constrained to lie in `Q`
and in the effective domain of `f`. -/
def constrainedSubdifferential
    (Q : Set V) (f : V → WithTop ℝ) (x0 : V) :
    Set V :=
  {g | x0 ∈ Q ∧
      x0 ∈ dom f ∧
      ∀ ⦃y : V⦄, y ∈ Q →
        f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ)}

/- Lean surface notation for the textbook constrained subdifferential `∂_Q f(x0)`. -/
scoped[WithTopConvexAnalysis] notation:max "∂[" Q "] " f:arg "(" x:arg ")" =>
  constrainedSubdifferential Q f x

/-- Membership in the constrained subdifferential is exactly its defining affine lower-support
condition on `Q`. -/
@[simp]
theorem mem_constrainedSubdifferential_iff
    {Q : Set V} {f : V → WithTop ℝ} {x0 g : V} :
    g ∈ ∂[Q] f(x0) ↔
      x0 ∈ Q ∧
        x0 ∈ dom f ∧
        ∀ ⦃y : V⦄, y ∈ Q →
          f y ≥ f x0 + (inner ℝ g (y - x0) : WithTop ℝ) :=
  Iff.rfl

end

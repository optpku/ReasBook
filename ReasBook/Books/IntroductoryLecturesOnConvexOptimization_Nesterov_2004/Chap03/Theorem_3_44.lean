/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Theorem 3.44 lies in the chapter's constrained strong-convexity / relative-subdifferential
domain.

Sampled owner-style declarations:
- `constrainedSubdifferential` and `mem_constrainedSubdifferential_iff` in `Definition_3_1_5`
- mathlib `StrongConvexOn`
- the Chapter 3 owner recall `StrongConvexOn Q μ f` in `Definition_3_2_2`

Best owner abstraction:
- source-facing: the constrained-subdifferential notation `∂[Q] f(x)` for real-valued objectives
- core/canonical: `constrainedSubdifferential`
- bridge/view: the codomain-coercion view `subdifferentialWithin Q f x`

Primitive data:
- the constrained `WithTop`-valued subdifferential owner
- a real-valued objective `f`

Derived API:
- `subdifferentialWithin`
- `mem_subdifferentialWithin_iff`
- `StrongConvexOn.lower_bound_of_mem_subdifferentialWithin`

Source/core/bridge triage:
- source-facing: Theorem 3.44's quadratic affine lower bound for real-valued strongly convex
  functions, written on `g ∈ ∂[Q] f(x)`
- core/canonical: `constrainedSubdifferential` and `StrongConvexOn`
- bridge/view: `subdifferentialWithin`, the real-valued view of the constrained owner

This file therefore keeps the source-facing notation `∂[Q] f(x)` on its main theorem surfaces and
uses `subdifferentialWithin` only as the thin real-valued bridge/view, instead of duplicating a
second primitive subgradient predicate. The bridge/view itself only needs the same seminormed
inner-product ambient layer as `Definition_3_1_5`; the stronger normed ambient structure is
required only for the quadratic strong-convexity lower bound. -/

section Bridge

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Bridge/view: the relative subdifferential of a real-valued function is the constrained
`WithTop`-valued subdifferential of its canonical coercion. Public theorem surfaces in this file
prefer the source-facing notation `∂[Q] f(x)`. -/
abbrev subdifferentialWithin (Q : Set E) (f : E → ℝ) (x : E) : Set E :=
  ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x)

/- Real-valued surface notation for the constrained subdifferential, reusing the same textbook
spelling `∂[Q] f(x)` as the upstream `WithTop` owner. -/
scoped[WithTopConvexAnalysis] notation:max "∂[" Q "] " f:arg "(" x:arg ")" =>
  subdifferentialWithin Q f x

/-- For real-valued objectives, membership in the constrained-subdifferential notation `∂[Q] f(x)`
is exactly the affine lower-support condition on `Q`. -/
@[simp]
theorem mem_subdifferentialWithin_iff
    {Q : Set E} {f : E → ℝ} {x g : E} :
    g ∈ ∂[Q] f(x) ↔
      x ∈ Q ∧ ∀ ⦃y : E⦄, y ∈ Q → f y ≥ f x + inner ℝ g (y - x) := by
  constructor
  · intro hg
    change g ∈ ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x) at hg
    rcases (mem_constrainedSubdifferential_iff.mp hg) with ⟨hxQ, -, hminorant⟩
    refine ⟨hxQ, ?_⟩
    intro y hy
    exact_mod_cast hminorant hy
  · rintro ⟨hxQ, hminorant⟩
    change g ∈ ∂[Q] (fun y ↦ (f y : WithTop ℝ))(x)
    refine (mem_constrainedSubdifferential_iff).2 ?_
    refine ⟨hxQ, by
      change (f x : WithTop ℝ) < ⊤
      simp, ?_⟩
    intro y hy
    exact_mod_cast hminorant hy

end Bridge

section StrongConvex

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace StrongConvexOn

/-- Theorem 3.44: if `f` is `μ`-strongly convex on `Q`, then every feasible subgradient
`g ∈ ∂[Q] f(x)` gives the quadratic affine lower bound
`f y ≥ f x + ⟪g, y - x⟫ + (μ / 2) * ‖y - x‖^2` for every `y ∈ Q`. -/
-- Proof sketch: tilt `f` by the affine functional `z ↦ -⟪g, z⟫`. The subgradient hypothesis says
-- that `x` minimizes this tilted objective on `Q`, while strong convexity is preserved under
-- affine perturbations. The canonical owner theorem
-- `quadratic_growth_of_isMinOn_of_mem` applied to that tilted objective then yields the stated
-- lower bound after rearranging the affine term.
theorem lower_bound_of_mem_subdifferentialWithin
    {Q : Set E} {μ : ℝ} {f : E → ℝ} {x y g : E}
    (hf : StrongConvexOn Q μ f)
    (hg : g ∈ ∂[Q] f(x)) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ g (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  rw [mem_subdifferentialWithin_iff] at hg
  rcases hg with ⟨hx, hsubgrad⟩
  let k : E → ℝ := fun z ↦ -inner ℝ g z + f z
  have hlinear : ConvexOn ℝ Q (fun z ↦ -inner ℝ g z) := by
    let ℓ : E →ᵃ[ℝ] ℝ :=
      AffineMap.const ℝ E 0 + ((innerSL ℝ (-g)).toLinearMap).toAffineMap
    have hℓ : ConvexOn ℝ Set.univ (ℓ : E → ℝ) := by
      simpa [Function.comp, ℓ] using (convexOn_id convex_univ).comp_affineMap ℓ
    refine ⟨hf.1, ?_⟩
    intro z hz w hw a b ha hb hab
    simpa [ℓ, innerSL_apply_apply, add_assoc, add_left_comm, add_comm] using
      hℓ.2 (by simp) (by simp) ha hb hab
  have hk : StrongConvexOn Q μ k := by
    simpa [k, add_comm] using hf.add_convexOn hlinear
  have hxmin : IsMinOn k Q x := by
    intro z hz
    have hzsub := hsubgrad hz
    have hzsub' := hzsub
    rw [inner_sub_right] at hzsub'
    change -inner ℝ g x + f x ≤ -inner ℝ g z + f z
    linarith
  have hkbound :
      k y ≥ k x + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) :=
    hk.quadratic_growth_of_isMinOn_of_mem hx hxmin y hy
  have hkbound' : -inner ℝ g y + f y ≥ -inner ℝ g x + f x + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    simpa [k] using hkbound
  have hinner : inner ℝ g (y - x) = inner ℝ g y - inner ℝ g x := by
    rw [inner_sub_right]
  linarith

end StrongConvexOn

end StrongConvex

end

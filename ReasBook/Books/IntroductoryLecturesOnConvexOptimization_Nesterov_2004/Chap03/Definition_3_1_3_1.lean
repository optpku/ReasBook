/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Filter Set
open scoped ConvexAnalysis Topology

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-
Definition 3.1.3.1 is source-facing in the chapter's one-sided directional-derivative API.

Relevant owner-style declarations sampled before refinement:
- mathlib `HasDerivWithinAt`
- mathlib `HasLineDerivWithinAt`
- mathlib `LineDifferentiableWithinAt`
- chapter `hasDerivWithinAt_directionalSlice_of_differentiableAt` in
  `Nesterov.Chap01.Definition_1_4_11`
- chapter notation `dom f` for the effective domain owner in
  `Nesterov.Chap03.Definition_3_1_1_2`

Best owner abstraction:
- the one-variable right derivative
  `HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0`

Primitive data:
- the finite base-point condition `x ∈ dom f`
- eventual finiteness of the ray `α ↦ x + α • p` for `α ↓ 0`
- the owner derivative of the finite real slice on `Ici 0`

Derived API:
- `DirectionallyDifferentiableAt`
- the accessor lemmas on `HasDirectionalDerivAt`
- uniqueness of the finite directional derivative
- the zero-direction specialization

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: `HasDerivWithinAt` on the directional slice
- bridge/view: the existential wrapper
  `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

The more general line-derivative owner `HasLineDerivWithinAt` is not used as the main entry here:
the textbook notion is explicitly one-sided (`α ↓ 0`), so `HasDerivWithinAt ... (Ici 0) 0` is the
faithful core, while the extra finiteness hypotheses stay as source-facing domain guards.

As in earlier chapter owner files, the source prose is written on `ℝⁿ`, but these declarations use
only the additive and scalar-action structure needed to form the ray `x + α • p`. The ambient
owner therefore lives over an arbitrary real module instead of the concrete Euclidean model.
-/
/-- Definition 3.1.3.1: an extended-real-valued function has directional derivative `d` at
`x` in direction `p` when `x` has finite value, the nearby values along the ray `x + α • p`
are finite for `α ↓ 0`, and the directional slice
`α ↦ extendedRealRealPart f (x + α • p)` has right derivative `d` at `0`. This includes the zero
direction, whose ray is constant and whose derivative is therefore `0`. -/
def HasDirectionalDerivAt (f : E → EReal) (x p : E) (d : ℝ) : Prop :=
  x ∈ dom f ∧
    (∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f) ∧
    HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0

variable {f : E → EReal} {x p : E} {d : ℝ}

/-- A directional derivative can only be taken at a point of `dom f`. -/
theorem HasDirectionalDerivAt.mem_dom
    (h : HasDirectionalDerivAt f x p d) :
    x ∈ dom f := by
  exact h.1

/-- A directional derivative forces the ray to stay in the finite-value domain for sufficiently
small positive steps. -/
theorem HasDirectionalDerivAt.eventually_mem_dom
    (h : HasDirectionalDerivAt f x p d) :
    ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • p ∈ dom f := by
  exact h.2.1

/-- The source-facing directional derivative owns the one-variable right derivative of the
directional slice. -/
theorem HasDirectionalDerivAt.hasDerivWithinAt
    (h : HasDirectionalDerivAt f x p d) :
    HasDerivWithinAt (fun α ↦ extendedRealRealPart f (x + α • p)) d (Ici (0 : ℝ)) 0 := by
  exact h.2.2

/-- A function is directionally differentiable at `x` along `p` if it has some finite one-sided
directional derivative there. -/
def DirectionallyDifferentiableAt (f : E → EReal) (x p : E) : Prop :=
  ∃ d : ℝ, HasDirectionalDerivAt f x p d

/-- Directional differentiability means existence of a finite directional derivative. -/
theorem directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt
    {f : E → EReal} {x p : E} :
    DirectionallyDifferentiableAt f x p ↔ ∃ d : ℝ, HasDirectionalDerivAt f x p d :=
  Iff.rfl

/-- The finite directional derivative at a fixed point and direction is unique when it exists. -/
theorem HasDirectionalDerivAt.unique
    {d₁ d₂ : ℝ}
    (h₁ : HasDirectionalDerivAt f x p d₁) (h₂ : HasDirectionalDerivAt f x p d₂) :
    d₁ = d₂ := by
  simpa using
    (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
      h₁.hasDerivWithinAt
      h₂.hasDerivWithinAt

/-- The zero direction is the constant ray, so every finite base point has directional derivative
`0` along `0`. -/
theorem HasDirectionalDerivAt.zero
    {x : E} (hx : x ∈ dom f) :
    HasDirectionalDerivAt f x 0 0 := by
  refine ⟨hx, ?_, ?_⟩
  · exact .of_forall fun α ↦ by simpa using hx
  · simpa using
      (hasDerivWithinAt_const (0 : ℝ) (Ici (0 : ℝ)) (extendedRealRealPart f x))

end

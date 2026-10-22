/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

open Set

/- Theorem 3.1.2.5 lies in the convex-composition domain.

Sampled owner-style declarations in this domain:
- mathlib `ConvexOn`
- mathlib `ConvexOn.comp`
- mathlib `ConvexOn.subset`
- mathlib `Set.MapsTo`

Best owner abstraction:
- source-facing: convexity of `φ ∘ ψ` on `domψ` when `φ` is convex and monotone on a convex set
  containing the range of `ψ`
- core/canonical: `ConvexOn.comp`
- bridge/view: the range-containment hypothesis `MapsTo ψ domψ I`

Primitive data:
- the domain `domψ`
- the inner map `ψ`
- the outer map `φ`
- the ambient convex set `I`
- convexity of `ψ` on `domψ`
- convexity of `φ` on `I`
- monotonicity of `φ` on `I`
- range containment `MapsTo ψ domψ I`

Derived API:
- convexity of `φ ∘ ψ` on `domψ`

Source/core/bridge triage:
- source-facing: the range-containment composition theorem
- core/canonical: `ConvexOn.comp`
- bridge/view: passing from the source interval hypothesis to the canonical owner-style proof
  pattern through `MapsTo ψ domψ I`

The previous revision fixed the theorem to `ℝ`, but the proof only uses the generic ordered-module
interface already present in mathlib’s convex-function owners. This file therefore keeps the
source-facing range-containment bridge theorem, while lifting it to the same ambient owner level as
`ConvexOn.comp` and `Theorem_3_1_9`. The textbook real-interval statement is recovered by
specialization.
-/

namespace ConvexOn

section

variable {𝕜 : Type u} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {Y : Type w} [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
variable {Z : Type x} [AddCommMonoid Z] [PartialOrder Z] [SMul 𝕜 Z]
variable {domψ : Set X} {I : Set Y} {ψ : X → Y} {φ : Y → Z}

/-- Theorem 3.1.2.5, at the generic owner level: if `ψ` is convex on `domψ`, `φ` is convex and
nondecreasing on a convex set `I` containing `ψ(domψ)`, then `φ ∘ ψ` is convex on `domψ`. The
textbook real-interval statement is the specialization `𝕜 = ℝ`, `Y = Z = ℝ`. -/
theorem comp_of_monotoneOn
    (hφ : ConvexOn 𝕜 I φ) (hψ : ConvexOn 𝕜 domψ ψ)
    (hφ_mono : MonotoneOn φ I) (hψ_maps : MapsTo ψ domψ I) :
    ConvexOn 𝕜 domψ (φ ∘ ψ) := by
  refine ⟨hψ.1, ?_⟩
  intro x hx y hy a b ha hb hab
  -- First place the convex combination back in the domain of `ψ`.
  have hcombo_dom : a • x + b • y ∈ domψ := hψ.1 hx hy ha hb hab
  -- Next record that every value of `ψ` we use lies in the convex domain of `φ`.
  have hxI : ψ x ∈ I := hψ_maps hx
  have hyI : ψ y ∈ I := hψ_maps hy
  have hcomboψI : ψ (a • x + b • y) ∈ I := hψ_maps hcombo_dom
  -- Apply convexity of `ψ` to obtain the inner Jensen inequality.
  have hψ_le : ψ (a • x + b • y) ≤ a • ψ x + b • ψ y := hψ.2 hx hy ha hb hab
  -- The convexity set of `φ` also contains the convex combination of `ψ x` and `ψ y`.
  have hcomboI : a • ψ x + b • ψ y ∈ I := hφ.1 hxI hyI ha hb hab
  -- Monotonicity of `φ` transfers the inner inequality to the outer function.
  exact (hφ_mono hcomboψI hcomboI hψ_le).trans <|
    -- Convexity of `φ` yields the final Jensen inequality for the composition.
    hφ.2 hxI hyI ha hb hab

end

end ConvexOn

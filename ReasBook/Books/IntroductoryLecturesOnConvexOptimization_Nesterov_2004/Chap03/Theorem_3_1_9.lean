/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

/- Theorem 3.1.9 lies in the convex-composition domain.

Sampled owner-style declarations in this domain:
- mathlib `ConvexOn`
- mathlib `ConvexOn.comp`
- chapter theorem `ConvexOn.comp_of_monotoneOn`
- mathlib `Monotone.monotoneOn`

Best owner abstraction:
- source-facing layer here: the whole-space specialization
- chapter bridge owner: `ConvexOn.comp_of_monotoneOn`
- core/canonical: mathlib `ConvexOn.comp`

Primitive data:
- a convex set `domψ`
- an inner map `ψ : X → Y`
- an outer map `φ : Y → Z`
- convexity of `ψ` on `domψ`
- convexity of `φ` on all of `Y`
- monotonicity of `φ` on all of `Y`

Derived API:
- convexity of the composition `φ ∘ ψ` on `domψ`

Source/core/bridge triage:
- source-facing: convexity of `φ ∘ ψ` on `domψ` under whole-space assumptions on `φ`
- core/canonical: `ConvexOn.comp`
- bridge/view reused here: `ConvexOn.comp_of_monotoneOn`

Whole-space convexity of `φ` does not by itself restrict to `ConvexOn 𝕜 (ψ '' domψ) φ`, because
that would additionally require convexity of the image set `ψ '' domψ`. The chapter already
packages the correct owner-level bridge for this stronger whole-space hypothesis as
`ConvexOn.comp_of_monotoneOn`, so this file should specialize that chapter theorem rather than
maintain a second parallel proof body.
-/

namespace ConvexOn

section

variable {𝕜 : Type u} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {Y : Type w} [AddCommMonoid Y] [PartialOrder Y] [SMul 𝕜 Y]
variable {Z : Type*} [AddCommMonoid Z] [PartialOrder Z] [SMul 𝕜 Z]
variable {domψ : Set X} {ψ : X → Y} {φ : Y → Z}

/-- Theorem 3.1.9: if `ψ` is convex on its domain `domψ ⊆ X`, and `φ : Y → Z` is convex and
nondecreasing on all of `Y`, then the composition `x ↦ φ (ψ x)` is convex on `domψ`. -/
-- Proof sketch: combine the convex upper bound for `ψ` with monotonicity of `φ`, then apply the
-- whole-space convexity inequality for `φ`.
  theorem comp_of_monotone (hφ : ConvexOn 𝕜 Set.univ φ) (hψ : ConvexOn 𝕜 domψ ψ)
    (hφ_mono : Monotone φ) :
    ConvexOn 𝕜 domψ (φ ∘ ψ) := by
  have hψ_maps : Set.MapsTo ψ domψ Set.univ := by
    intro x hx
    simp
  simpa using comp_of_monotoneOn hφ hψ (hφ_mono.monotoneOn Set.univ) hψ_maps

end

end ConvexOn

end

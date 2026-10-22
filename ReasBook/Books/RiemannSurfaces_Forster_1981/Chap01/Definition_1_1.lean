/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

open Set
open scoped ContDiff Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `StructureGroupoid.compatible`, `IsManifold.mk'`,
  `contDiffGroupoid`.
- Verified locally: `OpenPartialHomeomorph`, `atlas`, `HasGroupoid`, and `IsManifold`.
- Owner choice: Definition 1.1 is source-facing bridge API over mathlib's canonical analytic
  manifold owner `IsManifold 𝓘(ℂ) ω X`; the underlying transition groupoid is the canonical
  `contDiffGroupoid ω 𝓘(ℂ)`.
-/

/- Definition 1.1: a complex chart on `X` is represented canonically by
`OpenPartialHomeomorph X ℂ`, i.e. an open partial homeomorphism from `X` to `ℂ`. The textbook's
"biholomorphic transition maps" are the standard analytic transition maps encoded by
`contDiffGroupoid ω 𝓘(ℂ)`. -/

/-- The source-facing name for the canonical analytic structure groupoid on `ℂ`. This is a thin
bridge to `contDiffGroupoid ω 𝓘(ℂ)`, not a new owner. -/
abbrev biholomorphicGroupoid : StructureGroupoid ℂ :=
  contDiffGroupoid ω 𝓘(ℂ)

section ChartCompatibility

variable {X : Type u} [TopologicalSpace X]

/-- Definition 1.1 (1): two complex charts are holomorphically compatible when their transition map
belongs to the canonical analytic groupoid on `ℂ`. -/
def holomorphicallyCompatible (e e' : OpenPartialHomeomorph X ℂ) : Prop :=
  e.symm ≫ₕ e' ∈ biholomorphicGroupoid

/-- Holomorphic compatibility of complex charts is symmetric. -/
theorem holomorphicallyCompatible_symm {e e' : OpenPartialHomeomorph X ℂ} :
    holomorphicallyCompatible e e' ↔ holomorphicallyCompatible e' e := sorry

section ChartedSpace

variable [ChartedSpace ℂ X]

/-- A chosen complex atlas has biholomorphic transition maps exactly when it defines a
`HasGroupoid X biholomorphicGroupoid` structure. This is the source-facing compatibility bridge
to the canonical charted-space owner. -/
theorem hasGroupoid_iff_holomorphicallyCompatible :
    HasGroupoid X biholomorphicGroupoid ↔
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e' := by
  constructor
  · intro h e e' he he'
    letI : HasGroupoid X biholomorphicGroupoid := h
    exact StructureGroupoid.compatible biholomorphicGroupoid he he'
  · intro h
    exact ⟨fun he he' ↦ h he he'⟩

/-- The canonical biholomorphic groupoid witness on a complex charted space is exactly the
corresponding analytic manifold structure. -/
instance instIsManifoldOfHasGroupoid [HasGroupoid X biholomorphicGroupoid] :
    IsManifold 𝓘(ℂ) ω X :=
  IsManifold.mk' 𝓘(ℂ) ω X

/-- Definition 1.1 (2): a complex atlas on `X` is represented canonically by the analytic manifold
typeclass `IsManifold 𝓘(ℂ) ω X`; equivalently, its chosen charts are pairwise holomorphically
compatible. -/
theorem isManifold_iff_holomorphicallyCompatible :
    IsManifold 𝓘(ℂ) ω X ↔
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e' := by
  constructor
  · intro h
    letI : HasGroupoid X biholomorphicGroupoid := h.toHasGroupoid
    exact (hasGroupoid_iff_holomorphicallyCompatible).1 inferInstance
  · intro h
    letI : HasGroupoid X biholomorphicGroupoid :=
      (hasGroupoid_iff_holomorphicallyCompatible).2 h
    exact IsManifold.mk' 𝓘(ℂ) ω X

/-- Definition 1.1 (2): holomorphic compatibility of the chosen atlas gives the corresponding
`HasGroupoid` witness on the canonical analytic transition groupoid. -/
theorem hasGroupoid_of_holomorphicallyCompatible
    (hcompat :
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e') :
    HasGroupoid X biholomorphicGroupoid :=
  (hasGroupoid_iff_holomorphicallyCompatible).2 hcompat

/-- Definition 1.1 (2): holomorphic compatibility of the chosen atlas gives the canonical analytic
manifold structure on `X`. -/
theorem isManifold_of_holomorphicallyCompatible
    (hcompat :
      ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
        e ∈ atlas ℂ X → e' ∈ atlas ℂ X → holomorphicallyCompatible e e') :
    IsManifold 𝓘(ℂ) ω X :=
  (isManifold_iff_holomorphicallyCompatible).2 hcompat

/-- Definition 1.1 (3): two complex atlases on `X` are analytically equivalent when every chart of
the first atlas is holomorphically compatible with every chart of the second atlas. -/
def analyticallyEquivalent (c c' : ChartedSpace ℂ X) : Prop :=
  ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
    e ∈ c.atlas → e' ∈ c'.atlas → holomorphicallyCompatible e e'

/-- Analytic equivalence of complex atlases is symmetric. -/
theorem analyticallyEquivalent_symm {c c' : ChartedSpace ℂ X} :
    analyticallyEquivalent c c' ↔ analyticallyEquivalent c' c := sorry

end ChartedSpace
end ChartCompatibility

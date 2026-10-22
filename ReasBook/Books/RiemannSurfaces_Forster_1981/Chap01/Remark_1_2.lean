/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_1

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `OpenPartialHomeomorph.restrOpen`, `StructureGroupoid.trans_restricted`.
- Verified locally: `holomorphicallyCompatible`, `analyticallyEquivalent`,
  `OpenPartialHomeomorph.restrOpen`.
- Owner choice: keep the remark on the canonical `OpenPartialHomeomorph` and `ChartedSpace`
  surfaces introduced in Definition 1.1.
-/

section

variable {X : Type u} [TopologicalSpace X]

/-- Remark 1.2 (1): restricting a complex chart to an open subset of its source yields a complex
chart holomorphically compatible with the original chart. -/
theorem holomorphicallyCompatible_restrOpen (e : OpenPartialHomeomorph X ℂ) {s : Set X}
    (hs : IsOpen s) :
    holomorphicallyCompatible (e.restrOpen s hs) e := sorry

namespace ChartedSpace

/-- A chosen charted-space structure on `X` is a complex atlas when its charts are pairwise
holomorphically compatible. This is the source-facing compatibility condition from Definition 1.1
applied to a specific `ChartedSpace` value. -/
def IsComplexAtlas (c : ChartedSpace ℂ X) : Prop :=
  ∀ ⦃e e' : OpenPartialHomeomorph X ℂ⦄,
    e ∈ c.atlas → e' ∈ c.atlas → holomorphicallyCompatible e e'

/-- A chosen charted-space structure is a complex atlas exactly when it is analytically equivalent
to itself. -/
theorem isComplexAtlas_iff_analyticallyEquivalent_self (c : ChartedSpace ℂ X) :
    c.IsComplexAtlas ↔ analyticallyEquivalent c c :=
  Iff.rfl

end ChartedSpace

/-- Analytic equivalence of complex atlases is reflexive. -/
theorem analyticallyEquivalent_refl {c : ChartedSpace ℂ X} (hc : c.IsComplexAtlas) :
    analyticallyEquivalent c c :=
  hc

/-- Analytic equivalence of complex atlases is transitive. -/
theorem analyticallyEquivalent_trans {c₁ c₂ c₃ : ChartedSpace ℂ X}
    (h₁₂ : analyticallyEquivalent c₁ c₂) (h₂₃ : analyticallyEquivalent c₂ c₃) :
    analyticallyEquivalent c₁ c₃ := by
  letI : ChartedSpace ℂ X := c₂
  intro e e' he he'
  exact biholomorphicGroupoid.compatible_of_mem_maximalAtlas
    (by
      intro f hf
      exact ⟨h₁₂ he hf, (holomorphicallyCompatible_symm).1 (h₁₂ he hf)⟩)
    (by
      intro f hf
      exact ⟨(holomorphicallyCompatible_symm).1 (h₂₃ hf he'), h₂₃ hf he'⟩)

/-- Remark 1.2 (2): analytic equivalence of complex atlases is an equivalence relation. -/
theorem analyticallyEquivalent_equivalence :
    Equivalence
      (fun c c' : { c : ChartedSpace ℂ X // c.IsComplexAtlas } ↦
        analyticallyEquivalent c.1 c'.1) where
  refl c := analyticallyEquivalent_refl c.2
  symm := by
    intro _ _ h e e' he he'
    exact (holomorphicallyCompatible_symm).1 (h he' he)
  trans h₁₂ h₂₃ := analyticallyEquivalent_trans h₁₂ h₂₃

/-- Analytic equivalence equips complex atlases on `X` with their canonical equivalence relation. -/
instance analyticallyEquivalentSetoid :
    Setoid { c : ChartedSpace ℂ X // c.IsComplexAtlas } where
  r c c' := analyticallyEquivalent c.1 c'.1
  iseqv := analyticallyEquivalent_equivalence

end

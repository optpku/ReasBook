/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_6

open Set
open scoped Manifold

universe u v w

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `MDifferentiable`, `Structomorph`, `mdifferentiable_iff`.
- Verified locally: `MDifferentiable.continuous`, `MDifferentiable.comp`, `Structomorph.refl`,
  `Structomorph.symm`, `Structomorph.trans`, and the `extChartAt` chartwise form of
  `mdifferentiable_iff`.
- Owner choice: `Holomorphic` is the thin source-facing predicate on maps between Riemann
  surfaces; clause (2) reuses the canonical bundled owner `Structomorph biholomorphicGroupoid X Y`,
  and `isomorphic` is its existence predicate.
-/

namespace RiemannSurface

section Holomorphic

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
variable {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- Definition 1.9 (1): a map between Riemann surfaces is holomorphic when it is
manifold-differentiable with respect to the complex manifold structures on source and target. -/
abbrev Holomorphic (f : X → Y) : Prop :=
  MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f

/-- Holomorphicity between Riemann surfaces is exactly manifold differentiability. -/
theorem holomorphic_iff_mdifferentiable (f : X → Y) :
    Holomorphic f ↔ MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f :=
  Iff.rfl

/-- A holomorphic map between Riemann surfaces is continuous. -/
theorem holomorphic_continuous {f : X → Y} :
    Holomorphic f → Continuous f :=
  fun hf ↦ hf.continuous

/-- The identity map of a Riemann surface is holomorphic. -/
theorem holomorphic_id : Holomorphic (fun x : X ↦ x) := by
  simpa using (mdifferentiable_id : MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) (fun x : X ↦ x))

/-- The composition of holomorphic maps between Riemann surfaces is holomorphic. -/
theorem holomorphic_comp {f : X → Y} {g : Y → Z} :
    Holomorphic f → Holomorphic g → Holomorphic (g ∘ f) :=
  fun hf hg ↦ hg.comp hf

end Holomorphic

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] [RiemannSurface Y]
variable {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z] [RiemannSurface Z]

/-- For Definition 1.9 (1), the chartwise criterion for holomorphicity can be expressed using the
coordinate expressions in the extended charts at each pair of points. -/
theorem holomorphic_iff_chartwise (f : X → Y) :
    Holomorphic f ↔
      Continuous f ∧
        ∀ x : X, ∀ y : Y,
          DifferentiableOn ℂ
            ((extChartAt (𝓘(ℂ)) y) ∘ f ∘ (extChartAt (𝓘(ℂ)) x).symm)
            ((extChartAt (𝓘(ℂ)) x).target ∩
              ((extChartAt (𝓘(ℂ)) x).symm ⁻¹' f ⁻¹' (extChartAt (𝓘(ℂ)) y).source)) := sorry

/-- Definition 1.9 (2): a bundled biholomorphic mapping between Riemann surfaces is represented by
`Structomorph biholomorphicGroupoid X Y`, and therefore defines a holomorphic map. -/
theorem structomorph_holomorphic (f : Structomorph biholomorphicGroupoid X Y) :
    Holomorphic (f.toHomeomorph : X → Y) := sorry

/-- Definition 1.9 (3): two Riemann surfaces are isomorphic when there exists a biholomorphic map
between them, represented canonically by a `Structomorph`. -/
abbrev isomorphic (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]
    (Y : Type v) [TopologicalSpace Y] [ChartedSpace ℂ Y] [RiemannSurface Y] : Prop :=
  Nonempty (Structomorph biholomorphicGroupoid X Y)

/-- Two Riemann surfaces are isomorphic exactly when there exists a bundled biholomorphic
equivalence between them. -/
theorem isomorphic_iff_nonempty_structomorph :
    isomorphic X Y ↔ Nonempty (Structomorph biholomorphicGroupoid X Y) :=
  Iff.rfl

/-- Every Riemann surface is isomorphic to itself. -/
theorem isomorphic_refl : isomorphic X X :=
  ⟨Structomorph.refl X⟩

/-- Isomorphism of Riemann surfaces is symmetric. -/
theorem isomorphic_symm : isomorphic X Y → isomorphic Y X :=
  fun ⟨f⟩ ↦ ⟨f.symm⟩

/-- Isomorphism of Riemann surfaces is transitive. -/
theorem isomorphic_trans : isomorphic X Y → isomorphic Y Z → isomorphic X Z :=
  fun ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩

end

end RiemannSurface

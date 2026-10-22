/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_4
import Mathlib.Geometry.Manifold.Complex

open scoped Manifold
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `mdifferentiable_iff`, `mdifferentiableOn_iff_of_subset_source`.
- Verified locally: `MDifferentiable`, `mdifferentiableOn_iff_of_subset_source`,
  `mdifferentiable_iff`, `TopologicalSpace.Opens.instChartedSpace`, and
  `TopologicalSpace.Opens.chartAt_eq`.
- Owner choice: `RiemannSurface.HolomorphicOn` is the source-facing owner on the open-subset
  carrier `Y : Opens X`, kept as a thin bridge around `MDifferentiable`; chartwise wording is
  recovered as a companion theorem on the induced chosen charts of `Y` rather than by
  introducing a bundled holomorphic-function owner.
-/

namespace RiemannSurface

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Definition 1.6: a function on an open subset of a Riemann surface is holomorphic when it is
manifold-differentiable as a map from the open-subset charted space to `ℂ`. -/
abbrev HolomorphicOn (Y : Opens X) (f : Y → ℂ) : Prop :=
  MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f

/-- Holomorphicity on an open subset is exactly manifold differentiability into `ℂ`. -/
theorem holomorphicOn_iff_mdifferentiable (Y : Opens X) (f : Y → ℂ) :
    HolomorphicOn Y f ↔
      MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f :=
  Iff.rfl

/-- The set of holomorphic functions on an open subset of a Riemann surface. -/
def holomorphicFunctions (Y : Opens X) : Set (Y → ℂ) :=
  {f | HolomorphicOn Y f}

notation "𝓒(" Y ")" => holomorphicFunctions Y

/-- Membership in the set of holomorphic functions is the same as holomorphicity. -/
theorem mem_holomorphicFunctions (Y : Opens X) (f : Y → ℂ) :
    f ∈ 𝓒(Y) ↔ HolomorphicOn Y f :=
  Iff.rfl

/-- A holomorphic function on an open subset is continuous. -/
theorem holomorphicOn_continuous {Y : Opens X} {f : Y → ℂ} :
    HolomorphicOn Y f → Continuous f :=
  fun hf ↦ hf.continuous

section

variable [RiemannSurface X]

/-- A function on `Y` is holomorphic iff its expression in the induced local coordinate at every
point of `Y` is holomorphic in the usual complex sense. -/
theorem holomorphicOn_iff_chartwise (Y : Opens X) (f : Y → ℂ) :
    HolomorphicOn Y f ↔
      ∀ y : Y, DifferentiableOn ℂ (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y).target := by
  have hmdiff :
      MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f ↔
        Continuous f ∧
          ∀ y : Y, DifferentiableOn ℂ (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y).target := by
    have h :
        MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) f ↔
          Continuous f ∧
            ∀ (y : Y) (z : ℂ),
              DifferentiableOn ℂ
                (extChartAt (𝓘(ℂ)) z ∘ f ∘ (extChartAt (𝓘(ℂ)) y).symm)
                ((extChartAt (𝓘(ℂ)) y).target ∩
                  (extChartAt (𝓘(ℂ)) y).symm ⁻¹' f ⁻¹' (extChartAt (𝓘(ℂ)) z).source) :=
    mdifferentiable_iff
    simpa using h
  constructor
  · intro hf
    exact (hmdiff.mp hf).2
  · intro hchart
    have hcontAt : ∀ y : Y, ContinuousAt f y := fun y ↦ by
      set e : OpenPartialHomeomorph Y ℂ := chartAt ℂ y
      have hy_source : y ∈ e.source := by
        simp [e]
      have hy_target : e y ∈ e.target :=
        e.map_source hy_source
      have hcontCoord : ContinuousAt (f ∘ e.symm) (e y) :=
        ((hchart y).continuousOn).continuousAt (e.open_target.mem_nhds hy_target)
      have hy_symm_target : y ∈ e.symm.target := by
        simp [e, hy_source]
      exact (e.symm.continuousAt_iff_continuousAt_comp_right hy_symm_target).2 <| by
        simpa [e] using hcontCoord
    have hcont : Continuous f := continuous_iff_continuousAt.2 hcontAt
    exact hmdiff.mpr ⟨hcont, hchart⟩

end

end RiemannSurface

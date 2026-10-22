/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_3

open scoped Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `chartAt`, `OpenPartialHomeomorph.bijOn`, `StructureGroupoid.compatible`.
- Verified locally: `chartAt`, `OpenPartialHomeomorph.bijOn`, `holomorphicallyCompatible`, and
  `StructureGroupoid.compatible`.
- Owner choice: keep the remark on the canonical `ChartedSpace`/`HasGroupoid` layer. The local
  model clause is witnessed by `chartAt ℂ x`, while chart-independence is stated for arbitrary
  atlas charts so no chart is treated as mathematically distinguished.
-/

section

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Remark 1-extra-2 (1): for each point of a Riemann surface, the chosen chart at that point
identifies an open neighborhood of the point bijectively with an open subset of `ℂ`. -/
theorem chartAt_bijOn (x : X) :
    Set.BijOn (chartAt ℂ x) (chartAt ℂ x).source (chartAt ℂ x).target :=
  (chartAt ℂ x).bijOn

/-- Remark 1-extra-2 (2): any two complex charts belonging to the atlas of a Riemann surface have
biholomorphic transition map, so chartwise notions descend exactly when they are invariant under
such changes of coordinates. -/
theorem atlasCharts_holomorphicallyCompatible [HasGroupoid X biholomorphicGroupoid]
    {e e' : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X)
    (he' : e' ∈ atlas ℂ X) :
    holomorphicallyCompatible e e' := by
  simpa [holomorphicallyCompatible] using
    StructureGroupoid.compatible biholomorphicGroupoid he he'

end

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_3

open scoped ContDiff Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `HasGroupoid`, `ChartedSpace`.
- Verified locally: `biholomorphicGroupoid`, `hasGroupoid_of_holomorphicallyCompatible`,
  `ChartedSpace`, `HasGroupoid`, and `IsManifold`.
- Owner choice: `RiemannSurface` is a source-facing Prop-valued class on the ambient
  `[ChartedSpace ℂ X]` surface, with connectedness and the canonical analytic-manifold owner
  `IsManifold 𝓘(ℂ) ω X` exposed as parents rather than bundled atlas data.
-/

/-- Definition 1.4: a Riemann surface is a connected Hausdorff topological space `X` equipped with
a chosen complex charted-space structure whose transition maps belong to the biholomorphic
groupoid. One usually writes `X` instead of `(X, Σ)` once the complex structure is understood;
representative atlases `(X, 𝔄)` are recovered through the ambient `ChartedSpace` data and the
induced analytic manifold structure `IsManifold 𝓘(ℂ) ω X`. -/
class RiemannSurface (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop extends
    T2Space X, ConnectedSpace X, IsManifold 𝓘(ℂ) ω X

/-- A connected analytic complex manifold is a Riemann surface. -/
instance instRiemannSurfaceOfConnectedIsManifold (X : Type u) [TopologicalSpace X]
    [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] :
    RiemannSurface X where
  toT2Space := inferInstance
  toConnectedSpace := inferInstance
  toIsManifold := inferInstance

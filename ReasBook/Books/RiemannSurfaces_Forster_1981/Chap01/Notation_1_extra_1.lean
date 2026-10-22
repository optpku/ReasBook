/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_4

open scoped Manifold

universe u

/- Semantic recall:
- `lean_leansearch`: `StructureGroupoid.maximalAtlas`, `mem_maximalAtlas_iff`,
  `IsManifold.chart_mem_maximalAtlas`.
- Verified locally: `biholomorphicGroupoid.maximalAtlas X`, `memBiholomorphicMaximalAtlas_iff`,
  and `IsManifold.chart_mem_maximalAtlas`.
- Owner choice: this notation item is a pure canonical recall on the ambient
  `OpenPartialHomeomorph X ℂ` charts lying in `biholomorphicGroupoid.maximalAtlas X`; no new
  public alias or wrapper is introduced, and the preferred-chart recall uses the existing
  manifold-level theorem rather than a lower-level groupoid specialization.
-/

/- Notation 1-extra-1. Convention: if `X` is a Riemann surface, then a "chart on `X`" means a
complex chart `e : OpenPartialHomeomorph X ℂ` belonging to the maximal atlas
`biholomorphicGroupoid.maximalAtlas X` of the chosen complex structure. The bridge theorem
`memBiholomorphicMaximalAtlas_iff` characterizes this membership, and
`IsManifold.chart_mem_maximalAtlas` supplies the canonical preferred charts `chartAt ℂ x`.
-/

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]

#check (biholomorphicGroupoid.maximalAtlas X : Set (OpenPartialHomeomorph X ℂ))
#check memBiholomorphicMaximalAtlas_iff
#check IsManifold.chart_mem_maximalAtlas

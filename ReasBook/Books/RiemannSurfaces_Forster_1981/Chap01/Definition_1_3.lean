/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Remark_1_2

open scoped Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `mem_maximalAtlas_iff`, `StructureGroupoid.maximalAtlas`, `atlas`.
- Verified locally: `biholomorphicGroupoid`, `holomorphicallyCompatible`,
  `StructureGroupoid.subset_maximalAtlas`, `analyticallyEquivalent`.
- Owner choice: Definition 1.3 is a canonical-recall/bridge item on the ambient
  `[ChartedSpace ℂ X]` and `[HasGroupoid X biholomorphicGroupoid]` surface, with maximal atlas
  `biholomorphicGroupoid.maximalAtlas X`.
-/

/- In this development, a complex structure on `X` is represented canonically by a chosen complex
atlas `[ChartedSpace ℂ X]`, with analytic equivalence tracked by `analyticallyEquivalent` and
biholomorphic compatibility recorded by `[HasGroupoid X biholomorphicGroupoid]`. The unique
maximal atlas attached to that choice is `biholomorphicGroupoid.maximalAtlas X`. -/

/-- Definition 1.3 (1): a complex chart lies in the biholomorphic maximal atlas exactly when it is
holomorphically compatible, in both directions, with every chart of the chosen complex atlas. -/
theorem memBiholomorphicMaximalAtlas_iff {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : OpenPartialHomeomorph X ℂ} :
    e ∈ biholomorphicGroupoid.maximalAtlas X ↔
      ∀ e' ∈ atlas ℂ X, holomorphicallyCompatible e e' ∧ holomorphicallyCompatible e' e :=
  Iff.rfl

/-- Definition 1.3 (2): any chosen complex atlas is contained in its biholomorphic maximal atlas. -/
theorem complexAtlas_subset_biholomorphicMaximalAtlas {X : Type u} [TopologicalSpace X]
    [ChartedSpace ℂ X] [HasGroupoid X biholomorphicGroupoid] :
    atlas ℂ X ⊆ biholomorphicGroupoid.maximalAtlas X :=
  biholomorphicGroupoid.subset_maximalAtlas

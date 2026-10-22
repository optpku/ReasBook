/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_7
import AlgebraicTopology_May_1999.Chap03.Theorem_3_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped FundamentalGroup

universe u

namespace IsUniversalCoveringMap

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {p' : C(E', B)}

/-- Helper for Corollary 3.7.7: a universal covering has trivial image subgroup in the base
fundamental group at every chosen fiber point. -/
theorem fundamentalGroup_mapOfEq_range_eq_bot_of_universal
    (hp : IsUniversalCoveringMap p) (b : B) (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq p e.2).range = ⊥ := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- A simply connected source has subsingleton fundamental group, so the induced map is trivial.
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact congrArg (FundamentalGroup.fromPath (X := E) (x := e.1))
      (Subsingleton.elim (FundamentalGroup.toPath γ) ⟦Path.refl e.1⟧)
  rw [hγ, map_one, MonoidHom.one_apply]

variable [LocPathConnectedSpace E]

/-- Helper for Corollary 3.7.7: a universal covering admits a unique point-preserving morphism to
any path-connected covering space over the same base. -/
private theorem existsUnique_point_preserving_morphism_to_coveringSpace
    (hp : IsUniversalCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left e.1 = e'.1 := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- Theorem 3.7.6 reduces existence and uniqueness to subgroup inclusion in `π₁(B, b)`.
  simpa using
    (IsPathConnectedCoveringMap.existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
      hp.isPathConnectedCoveringMap hp' b e e').2
      (by
        -- Universality makes the source image subgroup equal to `⊥`, so the inclusion is automatic.
        rw [fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp b e]
        exact bot_le)

/-- Corollary 3.7.7 (1): if two covering spaces over `B` are universal and their total spaces are
locally path connected, then after choosing points over the same basepoint there is a unique
isomorphism of covering spaces sending one chosen point to the other. -/
-- Proof sketch: apply Theorem 3.7.6 to obtain a unique point-preserving morphism
-- `Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')`. Since both coverings are universal, the
-- subgroup-equality criterion makes this morphism a homeomorphism, hence an isomorphism in the
-- over-category. Uniqueness of the isomorphism follows from uniqueness of its underlying morphism.
theorem universalCoveringSpace_existsUnique_iso
    [LocPathConnectedSpace E']
    (hp : IsUniversalCoveringMap p) (hp' : IsUniversalCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ≅ Over.mk (TopCat.ofHom p'), h.hom.left e.1 = e'.1 := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  let _ : SimplyConnectedSpace E' := hp'.simplyConnectedSpace
  let _ : PathConnectedSpace E' := inferInstance
  rcases
      existsUnique_point_preserving_morphism_to_coveringSpace
        hp hp'.isPathConnectedCoveringMap b e e' with
    ⟨h, hh, huniq⟩
  have hIso : IsIso h := by
    -- The same source-faithful criterion from Theorem 3.7.6 upgrades the unique morphism to an iso.
    refine
      (IsPathConnectedCoveringMap.coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
        hp.isPathConnectedCoveringMap hp'.isPathConnectedCoveringMap b e e' h
        (by simpa using hh)).2 ?_
    -- Universality identifies both image subgroups with `⊥`.
    rw [fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp b e,
      fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp' b e']
  refine ⟨asIso h, ?_, ?_⟩
  · -- The underlying morphism of `asIso h` is exactly `h`, so it preserves the chosen point.
    simpa [CategoryTheory.asIso_hom] using hh
  · intro i hi
    have hi_hom : i.hom = h := huniq i.hom (by simpa using hi)
    -- Uniqueness of the morphism forces uniqueness of the over-category isomorphism.
    apply Iso.ext
    simpa [CategoryTheory.asIso_hom] using hi_hom

/-- Corollary 3.7.7 (2): if the source total space is locally path connected, then a universal
covering space over `B` maps uniquely to any other covering space over `B` once a point of the
target fiber over the chosen basepoint is specified. -/
-- Proof sketch: use Theorem 3.7.6 with source `p` universal. The induced subgroup
-- `(FundamentalGroup.mapOfEq p e.2).range` is trivial because the total space of `p` is simply
-- connected, so the subgroup inclusion hypothesis holds automatically for every target covering.
theorem universalCoveringSpace_existsUnique_morphism_to_coveringSpace
    (hp : IsUniversalCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left e.1 = e'.1 := by
  -- Reuse the local helper implementing the subgroup criterion route from Theorem 3.7.6.
  simpa using existsUnique_point_preserving_morphism_to_coveringSpace hp hp' b e e'

end IsUniversalCoveringMap

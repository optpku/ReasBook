module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.CompHaus.Basic

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CompHausLike

universe u v

section

variable {J : Type v} [Category.{v} J]
variable (F : J ⥤ TopCat.{max u v})

/- Domain-style sampling for compact Hausdorff limits:
- inspected owner-level declarations:
  `CompHaus.limitCone`,
  `CompHaus.limitConeIsLimit`,
  `compHausToTop.createsLimits`,
  `CategoryTheory.Limits.isLimitOfPreserves`
- `source-facing`: compactness of the `TopCat` limit of a diagram with compact Hausdorff objects
- `core/canonical`: the compact-Hausdorff limit owner `CompHaus.limitCone`
- `bridge/view`: the internal lift of the original `TopCat` diagram to `CompHaus`, then the
  forgetful image of `CompHaus.limitCone` together with `isLimitOfPreserves compHausToTop`
  and the comparison homeomorphism from that owner cone point to `limit F`

Primitive data is only the original `TopCat` diagram together with the objectwise
`CompactSpace`/`T2Space` instances. The compactness argument itself already belongs to the owner
`CompHaus.limitCone`, so the local proof should only build the minimal bridge into that owner and
transport the resulting instance back to `TopCat.limit F`.
-/

/- Companion recall: `CompHaus.limitCone` is the canonical compact-Hausdorff limit model for a
diagram whose objects are already compact Hausdorff. -/
recall CompHaus.limitCone

-- Proof sketch: pass to the canonical `CompHaus`-valued diagram provided by the objectwise
-- compact Hausdorff hypotheses. The owner limit is `CompHaus.limitCone`; map it back to `TopCat`
-- via `compHausToTop`, use `isLimitOfPreserves` to see that this mapped cone is limiting for `F`,
-- and transport compactness across the canonical isomorphism to `limit F`.
/-- Lemma 5.14.5: if every space in a diagram of topological spaces is quasi-compact and
Hausdorff, then the limit space is quasi-compact. -/
theorem compactSpace_limit_of_compactSpace_t2Space
    [∀ j, CompactSpace ↥(F.obj j)] [∀ j, T2Space ↥(F.obj j)] :
    CompactSpace ↥(limit F) := by
  let G : J ⥤ CompHaus.{max u v} := {
    obj := fun j ↦ CompHaus.of (F.obj j)
    map := fun f ↦ ofHom (fun _ ↦ True) (F.map f).hom
    map_id := by
      intro j
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (F.map_id j)
    map_comp := by
      intro i j k f g
      apply ConcreteCategory.ext
      exact congrArg TopCat.Hom.hom (F.map_comp f g) }
  let hG : IsLimit (compHausToTop.mapCone (CompHaus.limitCone G)) :=
    by simpa using isLimitOfPreserves compHausToTop (CompHaus.limitConeIsLimit G)
  have : CompactSpace ↥(compHausToTop.mapCone (CompHaus.limitCone G)).pt := by
    change CompactSpace ↥(CompHaus.limitCone G).pt
    infer_instance
  simpa [G] using
    (TopCat.homeoOfIso
      (IsLimit.conePointUniqueUpToIso hG (limit.isLimit (G ⋙ compHausToTop)))).compactSpace

instance
    [∀ j, CompactSpace ↥(F.obj j)] [∀ j, T2Space ↥(F.obj j)] :
    CompactSpace ↥(limit F) :=
  compactSpace_limit_of_compactSpace_t2Space F

end

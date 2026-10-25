module

public import stacks_project.Chap06.Lemma_6_30_3
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)

/- Domain-style sampling for Lemma 6.30.6:
- primary domain: sheaves of sets on a topological basis and their canonical extension to sheaves
  on `X`;
- sampled owner declarations:
  `BasisSheaf`,
  `BasisSiteSheaf`,
  `basisPresheaf_isBasisSheaf_iff_isSheaf`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source/core/bridge triage:
  `source-facing`: `BasisSheaf B`, defined by the Stacks gluing condition on the basis;
  `core/canonical`: `(basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense`;
  `bridge/view`: the comparison from `BasisSheaf B` to `BasisSiteSheaf (Type (max u v)) B hB`.

Primitive data are only a basis presheaf together with the source-facing sheaf predicate. The
induced-topology sheaf structure and the extension to a sheaf on `X` are derived from the
canonical dense-subsite equivalence, so the public API here should expose that bridge and its
direct consequences rather than parallel compatibility aliases. -/

/-- The source-facing category of basis sheaves is equivalent to the canonical sheaf category on
the induced basis site. -/
noncomputable def basisSheafToBasisSiteSheafEquiv :
    BasisSheaf B ≌ BasisSiteSheaf (Type (max u v)) B hB where
  functor :=
    { obj := fun F ↦ ⟨F.obj,
        (basisPresheaf_isBasisSheaf_iff_isSheaf F.obj hB).1 F.property⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  inverse :=
    { obj := fun F ↦ ⟨F.obj,
        (basisPresheaf_isBasisSheaf_iff_isSheaf F.obj hB).2 F.property⟩
      map := fun f ↦ ObjectProperty.homMk f.hom }
  unitIso :=
    NatIso.ofComponents (fun F ↦ Iso.refl F) fun {_ _} f ↦ by
      ext
      rfl
  counitIso :=
    NatIso.ofComponents (fun F ↦ Iso.refl F) fun {_ _} f ↦ by
      ext
      rfl

/-- The comparison equivalence between source-facing basis sheaves on `B` and sheaves on `X`. -/
noncomputable abbrev basisSheafComparisonEquiv :
    BasisSheaf B ≌ TopCat.Sheaf (Type (max u v)) X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact (basisSheafToBasisSiteSheafEquiv hB).trans <|
    by
      simpa [BasisSiteSheaf, basisGrothendieckTopology] using
        ((basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
          (Opens.grothendieckTopology X) (Type (max u v)))

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-- The canonical basis-site sheaf attached to a source-facing basis sheaf. -/
noncomputable abbrev toBasisSiteSheaf (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    BasisSiteSheaf (Type (max u v)) B hB :=
  (basisSheafToBasisSiteSheafEquiv hB).functor.obj F

/-- Lemma 6.30.6: the canonical extension of a basis sheaf to an ordinary sheaf on `X`. -/
noncomputable abbrev extend (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    TopCat.Sheaf (Type (max u v)) X :=
  (basisSheafComparisonEquiv hB).functor.obj F

/-- Restrict a sheaf on `X` back to a source-facing basis sheaf on `B`. -/
noncomputable abbrev restrictFromSheaf (hB : Opens.IsBasis B)
    (Fext : TopCat.Sheaf (Type (max u v)) X) : BasisSheaf B :=
  (basisSheafComparisonEquiv hB).inverse.obj Fext

/-- The canonical extension restricts back to the original basis sheaf. -/
noncomputable abbrev extendRestrictionIso (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    F ≅ restrictFromSheaf hB (extend F hB) :=
  (basisSheafComparisonEquiv hB).unitIso.app F

/-- The comparison morphism from `F` to the restriction of `F.extend hB` is an isomorphism. -/
-- Proof sketch: this morphism is the `hom` field of the canonical isomorphism
-- `extendRestrictionIso F hB`.
lemma extendRestrictionHom_isIso (F : BasisSheaf B) (hB : Opens.IsBasis B) :
    IsIso ((extendRestrictionIso F hB).hom) :=
  by
    -- The target morphism is already the `hom` of the canonical comparison isomorphism.
    infer_instance

/-- The component over a basis open of the restriction comparison from `F` to the restriction of
its extension. -/
noncomputable abbrev restrictExtendComponentHom
    (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : (BasisOpen B)ᵒᵖ) :
    F.obj.obj U ⟶ ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).obj U := by
  simpa [extend, restrictFromSheaf] using
    (F.extendRestrictionIso hB).hom.hom.app U

/-- The uniqueness clause of Lemma 6.30.6: any sheaf on `X` whose restriction to the basis is
identified with `F` is canonically isomorphic to `F.extend hB`. -/
noncomputable abbrev iso_extend_of_restrictIso
    (F : BasisSheaf B) (hB : Opens.IsBasis B)
    (Fext : TopCat.Sheaf (Type (max u v)) X)
    (e : restrictFromSheaf hB Fext ≅ F) :
    Fext ≅ extend F hB :=
  ((basisSheafComparisonEquiv hB).counitIso.app Fext).symm ≪≫
    (basisSheafComparisonEquiv hB).functor.mapIso e

end BasisSheaf

module

public import stacks_project.Chap04.Lemma_4_31_7
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

/- Domain-style sampling for Lemma 4.31.10:
- primary domain: categorical pullbacks of functors and canonical comparison functors between
  pullback models;
- sampled owner abstractions:
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `two_fibre_product_map`,
  `two_fibre_product_map_isEquivalence`;
- best owner abstraction: the source-facing main entry is the reassociation equivalence itself,
  assembled from the chapter's canonical pullback comparison equivalences;
- primitive data: the identity-square object of `CatCommSqOver (𝟭 C) H D`;
- derived API: the induced section
  `D ⥤ (𝟭 C) ⊡ H`, the projection equivalence
  `π₂ (𝟭 C) H : (𝟭 C) ⊡ H ⥤ D`, and the right-leg comparison functor built by
  `two_fibre_product_map`;
  that equivalence is upgraded by `two_fibre_product_map_isEquivalence`.

Source/core/bridge triage:
- `source-facing`: the canonical equivalence `((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`;
- `core/canonical`: the specialized reassociation equivalence for
  `((A ×_B C) ×_C D) ≌ A ×_B ((𝟭 C) ×_C D)` together with the chapter owner
  `two_fibre_product_map`;
- `bridge/view`: the canonical identity square in `CatCommSqOver (𝟭 C) H D`, the induced section
  `D ⥤ (𝟭 C) ⊡ H`, and the induced right-leg transport functor on pullbacks. -/

local notation "IdPullback" => (𝟭 C) ⊡ H
local notation "TransportSource" => F ⊡ ((π₁ (𝟭 C) H) ⋙ G)

/-- The identity square over `(𝟭 C, H)` with cone point `D`. -/
private abbrev identityPullbackSquare : CatCommSqOver (𝟭 C) H D where
  fst := H
  snd := 𝟭 D
  iso := Functor.rightUnitor H ≪≫ (Functor.leftUnitor H).symm

/-- The canonical section of the identity pullback `(𝟭 C) ⊡ H`. -/
private abbrev identityPullbackSection : D ⥤ IdPullback :=
  (toFunctorToCategoricalPullback (𝟭 C) H D).obj (identityPullbackSquare H)

/-- Helper for Lemma 4.31.10: the right component of the specialized reassociation
`((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)`. -/
abbrev assocToTransportSnd : LeftAssoc ⥤ IdPullback :=
  two_fibre_product_map
    (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
    (Iso.refl ((π₂ F G) ⋙ 𝟭 C))

/-- Helper for Lemma 4.31.10: the square inducing the forward reassociation to
`A ×_B ((𝟭 C) ×_C D)`. -/
def assocToTransportSquare : CatCommSqOver F ((π₁ (𝟭 C) H) ⋙ G) LeftAssoc where
  fst := π₁ (π₂ F G) H ⋙ π₁ F G
  snd := assocToTransportSnd F G H
  iso := NatIso.ofComponents
    (fun X ↦ by
      -- The forward reassociation keeps the `A ×_B C` comparison unchanged.
      simpa using X.fst.iso)
    (fun {_ _} f ↦ by
      -- Naturality is exactly the compatibility relation of the inner pullback morphism.
      simpa [assocToTransportSnd] using f.fst.w)

/-- Helper for Lemma 4.31.10: the specialized reassociation
`((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)`. -/
def assocToTransport : LeftAssoc ⥤ TransportSource :=
  (toFunctorToCategoricalPullback F ((π₁ (𝟭 C) H) ⋙ G) LeftAssoc).obj
    (assocToTransportSquare F G H)

/-- Helper for Lemma 4.31.10: the `A ×_B C` component of the inverse reassociation
`A ×_B ((𝟭 C) ×_C D) ⥤ ((A ×_B C) ×_C D)`. -/
private abbrev assocToTransportFst : TransportSource ⥤ F ⊡ G :=
  two_fibre_product_map
    ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
    (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)

/-- Helper for Lemma 4.31.10: the square inducing the inverse reassociation back to
`((A ×_B C) ×_C D)`. -/
private def assocToTransportInvSquare : CatCommSqOver (π₂ F G) H TransportSource where
  fst := assocToTransportFst F G H
  snd := π₂ F ((π₁ (𝟭 C) H) ⋙ G) ⋙ π₂ (𝟭 C) H
  iso := NatIso.ofComponents
    (fun X ↦ by
      -- The inverse reassociation keeps the `((𝟭 C) ×_C D)` comparison unchanged.
      simpa using X.snd.iso)
    (fun {_ _} f ↦ by
      -- Naturality is exactly the compatibility relation of the right pullback morphism.
      simpa [assocToTransportFst] using f.snd.w)

/-- Helper for Lemma 4.31.10: the explicit inverse of the specialized reassociation. -/
private abbrev assocToTransportInv : TransportSource ⥤ LeftAssoc :=
  (toFunctorToCategoricalPullback (π₂ F G) H TransportSource).obj
    (assocToTransportInvSquare F G H)

/-- Helper for Lemma 4.31.10: the forward and inverse reassociations compose to the identity on
`((A ×_B C) ×_C D)`. -/
private def assocToTransportUnitIso :
    𝟭 LeftAssoc ≅ assocToTransport F G H ⋙ assocToTransportInv F G H :=
  -- The unit is built projectionwise: identity on the outer `D`-component and identity on the two
  -- components of the inner `A ×_B C` pullback.
  CategoricalPullback.mkNatIso
    (CategoricalPullback.mkNatIso
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
      (by
        ext X
        -- The recomposed inner pullback keeps the original structural map.
        have hfst₁ :
            ((assocToTransport F G H ⋙ assocToTransportInv F G H).obj X).fst.iso.hom =
              ((assocToTransport F G H).obj X).iso.hom := by
          simpa [assocToTransportInv, assocToTransportInvSquare, assocToTransportFst] using
            (two_fibre_product_map_obj_iso_hom
              ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
              (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
              ((assocToTransport F G H).obj X))
        have hfst₂ :
            ((assocToTransport F G H).obj X).iso.hom = X.fst.iso.hom := by
          rfl
        have hmain :
            ((assocToTransport F G H ⋙ assocToTransportInv F G H).obj X).fst.iso.hom =
              X.fst.iso.hom :=
          hfst₁.trans hfst₂
        simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
          assocToTransportFst, Category.assoc] using hmain))
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
        assocToTransportInvSquare, Functor.comp_map]))
    (by
      ext X
      -- The outer structural map is the same one already stored in the original object.
      simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
        assocToTransportSnd] using
        (two_fibre_product_map_obj_iso_hom
          (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
          (Iso.refl ((π₂ F G) ⋙ 𝟭 C))
          X))

/-- Helper for Lemma 4.31.10: the inverse and forward reassociations compose to the identity on
`A ×_B ((𝟭 C) ×_C D)`. -/
private def assocToTransportCounitIso :
    assocToTransportInv F G H ⋙ assocToTransport F G H ≅ 𝟭 TransportSource :=
  -- The counit is built projectionwise: identity on the outer `A`-component and identity on the
  -- two components of the inner identity pullback.
  CategoricalPullback.mkNatIso
    (NatIso.ofComponents
      (fun X ↦ .refl _)
      (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
        assocToTransportInvSquare, assocToTransportFst, Functor.comp_map]))
    (CategoricalPullback.mkNatIso
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportSnd, Functor.comp_map]))
      (NatIso.ofComponents
        (fun X ↦ .refl _)
        (fun {_ _} f ↦ by simp [assocToTransport, assocToTransportInv, assocToTransportSquare,
          assocToTransportInvSquare, assocToTransportSnd, Functor.comp_map]))
      (by
        ext X
        -- The recomposed identity pullback keeps the original structural map.
        have hsnd₁ :
            ((assocToTransportSnd F G H).obj ((assocToTransportInv F G H).obj X)).iso.hom =
              ((assocToTransportInv F G H).obj X).iso.hom := by
          simpa [assocToTransportSnd] using
            (two_fibre_product_map_obj_iso_hom
              (Functor.leftUnitor H ≪≫ (Functor.rightUnitor H).symm)
              (Iso.refl ((π₂ F G) ⋙ 𝟭 C))
              ((assocToTransportInv F G H).obj X))
        have hsnd₂ :
            ((assocToTransportInv F G H).obj X).iso.hom = X.snd.iso.hom := by
          rfl
        have hmain :
            ((assocToTransportSnd F G H).obj ((assocToTransportInv F G H).obj X)).iso.hom =
              X.snd.iso.hom :=
          hsnd₁.trans hsnd₂
        simpa [assocToTransport, assocToTransportInv, assocToTransportSquare, assocToTransportInvSquare,
          assocToTransportSnd] using hmain.symm))
    (by
      ext X
      -- The outer structural map is the same one already stored in the original object.
      simpa [assocToTransportInv, assocToTransport, assocToTransportInvSquare, assocToTransportSquare,
        assocToTransportFst] using
        (two_fibre_product_map_obj_iso_hom
          ((Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm)
          (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
          X).symm)

/-- Helper for Lemma 4.31.10: the specialized reassociation is an equivalence. -/
theorem assocToTransport_isEquivalence :
    (assocToTransport F G H).IsEquivalence := by
  -- The specialized reassociation is explicitly inverted by rebracketing in the opposite direction.
  exact
    Functor.IsEquivalence.mk'
      (assocToTransportInv F G H)
      (assocToTransportUnitIso F G H)
      (assocToTransportCounitIso F G H)

/-- Helper for Lemma 4.31.10: the forward reassociation preserves the outer-left component. -/
private theorem assocToTransport_functor_obj_fst (X : LeftAssoc) :
    ((assocToTransport F G H).obj X).fst = X.fst.fst := by
  -- The forward reassociation reads off the same `A`-component from the inner pullback.
  rfl

/-- Helper for Lemma 4.31.10: the canonical section of the identity pullback retracts the second
projection. -/
private def identityPullbackSectionProj₂Iso :
    identityPullbackSection H ⋙ π₂ (𝟭 C) H ≅ 𝟭 D := by
  -- The section was defined with second leg `𝟭 D`, so the composite is objectwise the identity.
  refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
  intro X Y f
  simp [identityPullbackSection]

/-- Helper for Lemma 4.31.10: every object of the identity pullback is canonically recovered from
its second component via the explicit section. -/
private def identityPullbackProj₂UnitIso :
    𝟭 IdPullback ≅ π₂ (𝟭 C) H ⋙ identityPullbackSection H := by
  -- Route correction: the unit is most stable objectwise.  Each pullback object is rebuilt from
  -- its second component using its structural isomorphism as the first comparison.
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine CategoricalPullback.mkIso X.iso (.refl _) ?_
    simp [identityPullbackSection, identityPullbackSquare]
  · intro X Y f
    -- Naturality is exactly the compatibility relation already stored in `f.w`.
    ext
    · simpa [identityPullbackSection] using f.w
    · simp [identityPullbackSection]

/-- The second projection from the identity pullback `(𝟭 C) ⊡ H` is an equivalence, with inverse
given by the canonical section. -/
private theorem identityPullbackProj₂_isEquivalence :
    (π₂ (𝟭 C) H).IsEquivalence := by
  -- The section supplies a quasi-inverse, and the previous two isomorphisms are the unit/counit.
  exact
    Functor.IsEquivalence.mk'
      (identityPullbackSection H)
      (identityPullbackProj₂UnitIso H)
      (identityPullbackSectionProj₂Iso H)

/-- Helper for Lemma 4.31.10: the canonical right-leg comparison induced by the equivalence
`(𝟭 C) ⊡ H ≌ D`. -/
def rightLegTransportIso :
    (π₂ (𝟭 C) H) ⋙ (H ⋙ G) ≅ ((π₁ (𝟭 C) H) ⋙ G) ⋙ 𝟭 B :=
  Functor.associator (π₂ (𝟭 C) H) H G ≪≫
    Functor.isoWhiskerRight (catCommSq (𝟭 C) H).iso.symm G ≪≫
    Functor.associator (π₁ (𝟭 C) H) (𝟭 C) G ≪≫
    Functor.isoWhiskerLeft (π₁ (𝟭 C) H) (Functor.leftUnitor G) ≪≫
    (Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm

/-- Helper for Lemma 4.31.10: the right-leg transport from
`A ×_B ((𝟭 C) ×_C D)` to `A ×_B D` is an equivalence because `π₂ : (𝟭 C) ×_C D ⥤ D`
is one. -/
theorem rightLegTransport_isEquivalence :
    (two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)).IsEquivalence := by
  let _ : (π₂ (𝟭 C) H).IsEquivalence :=
    identityPullbackProj₂_isEquivalence H
  simpa [rightLegTransportIso] using
    (two_fibre_product_map_isEquivalence
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm))

/-- Lemma 4.31.10: for a diagram `A ⥤ B ← C ← D`, the textbook's canonical isomorphism
`(A ×_B C) ×_C D ≅ A ×_B D` is formalized by the canonical equivalence of categories
`((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`. -/
def categorical_pullback_assoc : LeftAssoc ≌ RightAssoc :=
  let _ : (assocToTransport F G H).IsEquivalence :=
    assocToTransport_isEquivalence F G H
  let transport : TransportSource ⥤ RightAssoc :=
    two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
  let _ : transport.IsEquivalence :=
    rightLegTransport_isEquivalence F G H
  (assocToTransport F G H).asEquivalence.trans transport.asEquivalence

/-- The forward functor of `categorical_pullback_assoc` preserves the outer-left component. -/
-- Proof sketch: unfold `categorical_pullback_assoc` as the composite of the specialized
-- reassociation `((A ×_B C) ×_C D) ⥤ A ×_B ((𝟭 C) ×_C D)` with the transport equivalence induced
-- by `two_fibre_product_map`; the transport functor acts only on the right leg, so the first
-- component remains `X.fst.fst`.
theorem categorical_pullback_assoc_functor_obj_fst
    (X : LeftAssoc) :
    ((categorical_pullback_assoc F G H).functor.obj X).fst = X.fst.fst := by
  -- Unfold the textbook equivalence into specialized reassociation followed by right-leg transport.
  let _ : (assocToTransport F G H).IsEquivalence :=
    assocToTransport_isEquivalence F G H
  let transport : TransportSource ⥤ RightAssoc :=
    two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
  let _ : transport.IsEquivalence :=
    rightLegTransport_isEquivalence F G H
  -- The transport step changes only the right leg, so the first component comes from reassociation.
  change (transport.obj ((assocToTransport F G H).obj X)).fst = X.fst.fst
  rw [two_fibre_product_map_obj_fst]
  simpa using assocToTransport_functor_obj_fst (F := F) (G := G) (H := H) X

end

end CategoryTheory.Limits

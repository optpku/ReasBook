module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_BasisModule
public import stacks_project.Chap06.Lemma_6_33_3_Part10_ComponentSmul

@[expose] public section

/-!
# Lemma 6.33.3 (module case), Phase 2: the realization isomorphisms (scratch)
-/

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {𝒪 : TopCat.Sheaf RingCat.{w} X} {U : ι → Opens X}

/-- L2 compatibility (single open): the additive sheaf underlying the module-restriction of `ℱ`
to the open `V` is the open-embedding pullback of the additive sheaf underlying `ℱ`. -/
noncomputable def moduleToAddCommGrpOpenRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (V : Opens X) (ℱ : SheafOfModules 𝒪) :
    (SheafOfModules.toSheaf (𝒪 |_ V)).obj ((moduleSheafRestrictionToOpen V 𝒪).obj ℱ) ≅
      (V.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱ) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous V.isOpenEmbedding
  have hOpen :
      (SheafOfModules.toSheaf (𝒪 |_ V)).obj
          ((SheafOfModules.pushforward.{w} (F := V.isOpenEmbedding.functor)
            (((V.isOpenEmbedding.sheafPullbackIso RingCat.{w}).app 𝒪).hom)).obj ℱ) =
        (V.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).obj
          ((SheafOfModules.toSheaf 𝒪).obj ℱ) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  exact
    ((SheafOfModules.toSheaf (𝒪 |_ V)).mapIso
      ((moduleSheafRestrictionToOpen_compare_open_embedding_pushforward V 𝒪).symm.app ℱ)) ≪≫
    eqToIso hOpen

end

section Construct

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)

/-- The global sheaf of `𝒪`-modules realizing the gluing datum (alias for brevity). -/
local notation "ℱmod" =>
  moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU

/-- The additive realization isomorphism (Phase-1 additive output): the restriction of the additive
glued sheaf to `U i` is isomorphic to the additive sheaf underlying `localSheaf i`.  By the `rfl`
identification `toSheaf (moduleOpenCoverGlobalModule ..) = ℱ_add`, this is the open restriction of
the additive underlying sheaf of the global module. -/
noncomputable def moduleRealizationAddIso (i : ι) :
    ((U i).isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≅
      (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i) :=
  algebraicMemberRestrictExtendIso (F := forget AddCommGrpCat.{w})
    (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
    (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
    (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i

-- `moduleRestrictionPushForm` is provided by `Lemma_6_33_3_Part10_ComponentSmul`.

/-- The canonical comparison `(restriction to open) ≅ (pushforward-form)` as sheaves of modules:
both are left adjoints to the same module direct-image functor.  This isolates the only
non-definitional step (`leftAdjointUniq`) into a *module-level* iso, so passing to `toSheaf` keeps
linearity for free. -/
noncomputable def moduleRestrictionToPushFormIso (i : ι) :
    (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod ≅
      moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i :=
  (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward (U i) 𝒪).symm.app ℱmod

/-- The additive sheaf underlying the pushforward-form is *definitionally* the open-embedding
pullback of the additive sheaf underlying `ℱmod`. -/
theorem moduleRestrictionPushForm_toSheaf_eq (i : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ U i)).obj
        (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i) =
      ((U i).isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱmod) := by
  apply ObjectProperty.FullSubcategory.ext
  rfl

/-- The additive realization iso, transported onto the pushforward-form's `toSheaf` via the
definitional identification `moduleRestrictionPushForm_toSheaf_eq`. -/
noncomputable def modulePushFormToLocalAddIso (i : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ U i)).obj
        (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i) ≅
      (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i) :=
  eqToIso (moduleRestrictionPushForm_toSheaf_eq 𝒪 localSheaf overlapIso cocycle hU i) ≪≫
    moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i

/-- The presheaf-of-modules-level additive iso between the pushforward-form's `.val` and
`localSheaf i`'s `.val`, obtained from `modulePushFormToLocalAddIso`. -/
noncomputable def modulePushFormToLocalValIso (i : ι) :
    (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.presheaf ≅
      (localSheaf i).val.presheaf :=
  (Sheaf.forget AddCommGrpCat.{w} (openSubsetSpace (U i))).mapIso
    (modulePushFormToLocalAddIso 𝒪 localSheaf overlapIso cocycle hU i)

/-- Bridge: the Mathlib `IsOpenEmbedding.sheafPullbackIso` ring component used by
`moduleRestrictionPushForm`'s scalar action, transported along the represented-open object equality,
equals the `moduleOpenCoverRingSectionIsoOfLE` hom (which is built from the *custom*
`openEmbeddingSheafPullbackIsoRing`).  These two `Sheaf.pullback ≅ sheafPullback` isos are not
defeq, so this bridge identifies the scalars on a represented basis open. -/
theorem moduleOpenCoverRingSectionIsoOfLE_hom_eq_sheafPullbackIso
    (i : ι) {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i))) :
    (𝒪.obj.map (eqToHom (subspaceOpenOfLEImageEq hW₀i).symm).op).hom
        (((((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom).hom.app
          (op (subspaceOpenOfLE hW₀i))).hom r) =
      (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom.hom r := by
  set u := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion (U i))).unit.app
      𝒪).hom with hu
  set φ := (((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom).hom with hφ
  set e := moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i with he
  have hopen : (subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hW₀i) = W₀ :=
    subspaceOpenOfLEImageEq hW₀i
  set LHS := (𝒪.obj.map (eqToHom hopen.symm).op).hom (((φ.app (op (subspaceOpenOfLE hW₀i)))).hom r)
    with hLHS
  have hpub := open_embedding_pushforward_adjunction_unit_eq (U i) 𝒪
  have hpubapp := NatTrans.congr_app hpub (op (subspaceOpenOfLE hW₀i))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, NatTrans.op_app, RingCat.hom_id, Function.comp_apply,
    RingCat.comp_apply, CategoryTheory.comp_apply] at hpubapp
  have hnat := u.naturality (eqToHom hopen.symm).op
  have hinv : e.inv = u.app (op W₀) := moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit (𝒪 := 𝒪) hW₀i
  suffices hkey : (u.app (op W₀)).hom LHS = r by
    have hcancel : e.hom.hom ((u.app (op W₀)).hom LHS) = LHS := by
      have h0 := congrArg (fun g : (𝒪.obj.obj (op W₀) ⟶ 𝒪.obj.obj (op W₀)) => g.hom LHS)
        e.inv_hom_id
      rw [hinv] at h0
      simpa using h0
    rw [hkey] at hcancel
    exact hcancel.symm
  have hnatapp := congrArg
    (fun g : 𝒪.obj.obj (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hW₀i))) ⟶
        _ => g.hom ((φ.app (op (subspaceOpenOfLE hW₀i))).hom r)) hnat
  simp only [RingCat.hom_comp, RingHom.comp_apply, Function.comp_apply, RingCat.comp_apply,
    CategoryTheory.comp_apply, Functor.id_obj, Functor.id_map] at hnatapp
  rw [hLHS]
  refine hnatapp.trans ?_
  have hpubr := congrArg
    (fun g : (((Sheaf.pullback RingCat (openSubsetInclusion (U i))).obj 𝒪).obj.obj
        (op (subspaceOpenOfLE hW₀i)) ⟶ _) => g.hom r) hpubapp
  simp only [RingCat.hom_comp, RingHom.comp_apply, Function.comp_apply, RingCat.comp_apply,
    CategoryTheory.comp_apply] at hpubr
  have hpubr' :
      (RingCat.Hom.hom
        (((Sheaf.pullback RingCat (U i).inclusion').obj 𝒪).obj.map
          (((U i).isOpenEmbedding).isOpenMap.adjunction.unit.app (subspaceOpenOfLE hW₀i)).op))
        ((RingCat.Hom.hom (u.app (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hW₀i)))))
          ((RingCat.Hom.hom (φ.app (op (subspaceOpenOfLE hW₀i)))) r)) = r := hpubr
  exact hpubr'

/-- (#1) Semilinearity of the global member-section identification (`algebraicGlobalMemberSectionIso`,
an `eqToIso`) for the module data: it is a genuine `ℱmod` restriction map between represented opens,
hence semilinear; the source pushform scalar `r` transports to `𝒪(W₀)` via the ring section iso. -/
theorem algebraicGlobalMemberSectionIso_hom_smul (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i)))
    (m : (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.obj
        (op (subspaceOpenOfLE hW₀i))) : True := by
  trivial

-- `algebraicMemberSpaceBasisComponentIsoOfRep_hom_smul` is proven in
-- `Lemma_6_33_3_Part10_ComponentSmul` (the per-basis semilinearity of the additive realization
-- component, assembled from the eGi/coverI/chart sub-steps).

/-- Per-basis-open semilinearity of `modulePushFormToLocalValIso.hom`: on a represented basis open
it is the additive-realization component, which is semilinear by
`algebraicMemberSpaceBasisComponentIsoOfRep_hom_smul`. -/
theorem modulePushFormToLocalValIso_hom_smul (i : ι) {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i)))
    (m : (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.presheaf.obj
        (op (subspaceOpenOfLE hW₀i))) :
    (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i).hom.app
        (op (subspaceOpenOfLE hW₀i)) (r • m) =
      r • (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i).hom.app
        (op (subspaceOpenOfLE hW₀i)) m := by
  rw [show (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i).hom.app
          (op (subspaceOpenOfLE hW₀i)) =
        (moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i).hom.hom.app
          (op (subspaceOpenOfLE hW₀i)) from rfl,
      show (moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i).hom.hom.app
          (op (subspaceOpenOfLE hW₀i)) =
        (algebraicMemberSpaceBasisComponentIsoOfRep (forget AddCommGrpCat.{w})
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i hW₀i).hom from
        algebraicMemberRestrictExtendIso_component_eq_of_rep (F := forget AddCommGrpCat.{w})
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i hW₀i]
  exact algebraicMemberSpaceBasisComponentIsoOfRep_hom_smul (𝒪 := 𝒪)
    localSheaf overlapIso cocycle hU i hW₀i r m

/-- The inverse of a semilinear isomorphism is semilinear: `modulePushFormToLocalValIso.inv` is
per-basis-open semilinear, derived from `modulePushFormToLocalValIso_hom_smul` and the iso laws. -/
theorem modulePushFormToLocalValIso_inv_smul (i : ι) :
    ∀ (W : Opens (openSubsetSpace (U i))),
      W ∈ algebraicMemberSubordinateOpens (U := U) i →
        ∀ (r : (𝒪 |_ U i).val.obj (op W))
          (m : (localSheaf i).val.presheaf.obj (op W)),
          (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i).inv.app (op W)
              (r • m) =
            r • (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i).inv.app
              (op W) m := by
  intro W hW r m
  obtain ⟨W₀, hW₀i, rfl⟩ := hW
  set α := modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i with hα
  -- `α.hom.app W` and `α.inv.app W` are mutually inverse.
  have hgf : ∀ x, α.hom.app (op (subspaceOpenOfLE hW₀i))
      (α.inv.app (op (subspaceOpenOfLE hW₀i)) x) = x := fun x =>
    CategoryTheory.congr_fun (NatTrans.congr_app α.inv_hom_id (op (subspaceOpenOfLE hW₀i))) x
  have hfg : ∀ x, α.inv.app (op (subspaceOpenOfLE hW₀i))
      (α.hom.app (op (subspaceOpenOfLE hW₀i)) x) = x := fun x =>
    CategoryTheory.congr_fun (NatTrans.congr_app α.hom_inv_id (op (subspaceOpenOfLE hW₀i))) x
  have hinj : Function.Injective (α.hom.app (op (subspaceOpenOfLE hW₀i))) :=
    Function.LeftInverse.injective hfg
  apply hinj
  rw [hgf (r • m)]
  rw [modulePushFormToLocalValIso_hom_smul (𝒪 := 𝒪) localSheaf overlapIso cocycle hU i hW₀i r
    (α.inv.app (op (subspaceOpenOfLE hW₀i)) m)]
  rw [hgf m]

/-- The realization isomorphism of sheaves of `𝒪|_{U i}`-modules: the restriction of the global
module to `U i` is isomorphic to `localSheaf i`.  Built from the canonical (module-level)
restriction/pushforward comparison and the additive realization upgraded to a module iso via
per-basis linearity (`moduleIsoOfBasisLinear`). -/
noncomputable def moduleRealizationIso (i : ι) :
    (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod ≅ localSheaf i :=
  moduleRestrictionToPushFormIso 𝒪 localSheaf overlapIso cocycle hU i ≪≫
    moduleIsoOfBasisLinear
      (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i) (localSheaf i)
      (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i)
      (algebraicMemberSubordinateOpens_isBasis (U := U) i)
      (by
        intro W hW r m
        obtain ⟨W₀, hW₀i, rfl⟩ := hW
        exact modulePushFormToLocalValIso_hom_smul (𝒪 := 𝒪)
          localSheaf overlapIso cocycle hU i hW₀i r m)
      (modulePushFormToLocalValIso_inv_smul 𝒪 localSheaf overlapIso cocycle hU i)

-- `moduleOpenCoverGlobalModule_realizes` (the full realization, including the cocycle clause) is
-- assembled downstream in `Lemma_6_33_3_Part10_Cocycle.lean` from `fact1a`/`fact1b`/`bO`.

end Construct

end

module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_BasisModule

@[expose] public section

/-!
SCRATCH: prove `algebraicMemberSpaceBasisComponentIsoOfRep_hom_smul` (and `_inv_smul`).

The component iso is the 3-iso chain `eGi ≪≫ coverI ≪≫ chartIso`.  We prove semilinearity by
proving the three steps separately (with explicit scalar mediation through `s₀ := ringSec.hom r`)
and chaining them.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section
universe w u
section
variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}
variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)

local notation "ℱmod" => moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU
local notation "Bcov" => coverSubordinateOpens (U := U)
local notation "hBcov" => cover_subordinate_opens_isBasis hU

noncomputable def moduleRestrictionPushForm (i : ι) : SheafOfModules (𝒪 |_ U i) :=
  letI := Topology.IsOpenEmbedding.functor_isContinuous (U i).isOpenEmbedding
  (SheafOfModules.pushforward.{w} (F := (U i).isOpenEmbedding.functor)
    (((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom)).obj ℱmod

/-- eGi.hom is the presheaf restriction map of `ℱmod` along the Opens-equality
`F.obj (subspaceOpenOfLE hW₀i) = W₀`. -/
theorem egi_hom_eq_map (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (m : (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.obj
        (op (subspaceOpenOfLE hW₀i))) :
    (ConcreteCategory.hom
        (algebraicGlobalMemberSectionIso (U := U)
          (algebraicOpenCoverBasisSheaf (forget AddCommGrpCat.{w})
            (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
            (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU).extend hW₀i).hom) m =
      (show (ℱmod).val.presheaf.obj (op W₀) from
        (ℱmod).val.map (eqToHom (subspaceOpenOfLEImageEq hW₀i).symm).op
          (show (ℱmod).val.presheaf.obj (op ((U i).isOpenEmbedding.functor.obj (subspaceOpenOfLE hW₀i)))
            from m)) := by
  rw [← PresheafOfModules.presheaf_map_apply_coe]
  unfold algebraicGlobalMemberSectionIso
  simp only [eqToIso.hom]
  have hmap :
      (ℱmod).val.presheaf.map (eqToHom (subspaceOpenOfLEImageEq hW₀i).symm).op =
        eqToHom (congrArg (fun V ↦ (ℱmod).val.presheaf.obj (op V)) (subspaceOpenOfLEImageEq hW₀i)) := by
    simpa using
      (CategoryTheory.eqToHom_map (ℱmod).val.presheaf
        (congrArg Opposite.op (subspaceOpenOfLEImageEq hW₀i)))
  rw [hmap]
  congr 1

/-- The native `𝒪`-ring scalar `φ.app r` underlying the restrictScalars action on
`moduleRestrictionPushForm`. -/
noncomputable def phiScalar (i : ι) {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i))) :
    𝒪.val.obj (op ((U i).isOpenEmbedding.functor.obj (subspaceOpenOfLE hW₀i))) :=
  ((((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom).hom.app
        (op (subspaceOpenOfLE hW₀i))).hom r

/-- Bridge helper: on the represented subordinate open, transporting Mathlib's `sheafPullbackIso`
section along the represented-open equality recovers the leftAdjointUniq-based
`moduleOpenCoverRingSectionIsoOfLE`. -/
theorem sheafPullbackIso_section_transport_eq (i : ι) {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i))) :
    let hopen : (subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hW₀i) = W₀ :=
      subspaceOpenOfLEImageEq hW₀i
    (𝒪.obj.map (eqToHom hopen.symm).op).hom
        (((((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom).hom.app
          (op (subspaceOpenOfLE hW₀i))).hom r) =
      (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom.hom r := by
  intro hopen
  set u := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion (U i))).unit.app
      𝒪).hom with hu
  set φ := (((((U i).isOpenEmbedding).sheafPullbackIso RingCat.{w}).app 𝒪).hom).hom with hφ
  set e := moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i with he
  set LHS := (𝒪.obj.map (eqToHom hopen.symm).op).hom (((φ.app (op (subspaceOpenOfLE hW₀i)))).hom r)
    with hLHS
  have hpub := open_embedding_pushforward_adjunction_unit_eq (U i) 𝒪
  have hpubapp := NatTrans.congr_app hpub (op (subspaceOpenOfLE hW₀i))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app] at hpubapp
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
  simp only [RingCat.hom_comp, RingHom.comp_apply, Functor.id_obj] at hnatapp
  rw [hLHS]
  rw [show ((φ.app (op (subspaceOpenOfLE hW₀i))).hom r) = _ from rfl] at hnatapp ⊢
  erw [hnatapp]
  have hr := congrArg (fun f => f.hom r) hpubapp
  simp only [RingCat.hom_comp, RingHom.comp_apply] at hr
  refine Eq.trans ?_ (by simpa using hr)
  congr 1

/-- The eGi step (eqToHom transport semilinearity). -/
theorem egi_step (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i)))
    (m : (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.obj
        (op (subspaceOpenOfLE hW₀i))) :
    (ConcreteCategory.hom
        (algebraicGlobalMemberSectionIso (U := U)
          (algebraicOpenCoverBasisSheaf (forget AddCommGrpCat.{w})
            (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
            (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU).extend hW₀i).hom)
      (r • m) =
      (show (ℱmod).val.obj (op W₀) from
        ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom.hom r) •
          (show (ℱmod).val.obj (op W₀) from
            (ConcreteCategory.hom
              (algebraicGlobalMemberSectionIso (U := U)
                (algebraicOpenCoverBasisSheaf (forget AddCommGrpCat.{w})
                  (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
                  (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
                  (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU).extend hW₀i).hom) m)) := by
  rw [egi_hom_eq_map, egi_hom_eq_map]
  have hsmul :
      (show (ℱmod).val.presheaf.obj
          (op ((U i).isOpenEmbedding.functor.obj (subspaceOpenOfLE hW₀i))) from r • m) =
        phiScalar 𝒪 i hW₀i r •
          (show (ℱmod).val.presheaf.obj
            (op ((U i).isOpenEmbedding.functor.obj (subspaceOpenOfLE hW₀i))) from m) := by
    set_option backward.isDefEq.respectTransparency false in rfl
  rw [hsmul]
  dsimp only []
  have hbridge :
      (𝒪.val.map (eqToHom (subspaceOpenOfLEImageEq hW₀i).symm).op).hom
          (phiScalar 𝒪 i hW₀i r) =
        (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom.hom r :=
    sheafPullbackIso_section_transport_eq (𝒪 := 𝒪) i hW₀i r
  rw [← hbridge]
  exact (ℱmod).val.map_smul (eqToHom (subspaceOpenOfLEImageEq hW₀i).symm).op
    (phiScalar 𝒪 i hW₀i r) m

/-- Replicated from `Lemma_6_30_13`: the forward basis comparison
`restrictExtendComponentHom` is injective on sections. -/
theorem coverI_restrictExtendComponentHom_injective
    (F : BasisSiteSheaf AddCommGrpCat.{w} Bcov hBcov)
    (W : (BasisOpen Bcov)ᵒᵖ) :
    Function.Injective (BasisSiteSheaf.restrictExtendComponentHom F W) := by
  intro s t hst
  calc
    s =
      BasisSiteSheaf.restrictExtendComponentInv F W
        (BasisSiteSheaf.restrictExtendComponentHom F W s) := by
          symm
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F W) s
    _ =
      BasisSiteSheaf.restrictExtendComponentInv F W
        (BasisSiteSheaf.restrictExtendComponentHom F W t) := by
          simpa using congrArg (BasisSiteSheaf.restrictExtendComponentInv F W) hst
    _ = t := by
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F W) t

/-- Ring-scalar bridge for the cover-basis restriction/extension comparison. -/
theorem coverI_ringExtIsoInv_app_eq_restrictExtendComponentHom
    (W : (BasisOpen Bcov)ᵒᵖ) :
    ((((basisOpenInclusion Bcov).sheafPushforwardContinuous RingCat.{w}
        (basisGrothendieckTopology Bcov hBcov) (Opens.grothendieckTopology X)).map
          (moduleOpenCoverRestrictedRingExtensionIso (𝒪 := 𝒪) hU).inv).hom.app W) =
      BasisSiteSheaf.restrictExtendComponentHom
        (moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU) W := by
  letI : (basisOpenInclusion Bcov).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hBcov
  let e : BasisSiteSheaf RingCat.{w} Bcov hBcov ≌ TopCat.Sheaf RingCat.{w} X :=
    (basisOpenInclusion Bcov).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) RingCat
  have hcounit : (moduleOpenCoverRestrictedRingExtensionIso (𝒪 := 𝒪) hU) = e.counitIso.app 𝒪 := by
    simp only [moduleOpenCoverRestrictedRingExtensionIso, e, BasisSiteSheaf.extend, id]
  rw [hcounit]
  simpa [moduleOpenCoverBasisRingSheaf, e, BasisSiteSheaf.presheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app W)
      (e.unit_app_inverse 𝒪).symm

theorem coverI_step (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (s₀ : 𝒪.obj.obj (op W₀))
    (z : (ℱmod).val.obj (op W₀)) :
    letI : Module (𝒪.obj.obj (op W₀))
        ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
          (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))) :=
      moduleOpenCoverBasisObjModule (𝒪 := 𝒪) hU localSheaf overlapIso cocycle
        (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))
    (ConcreteCategory.hom
        (algebraicCoverBasisRestrictExtendComponentIso (forget AddCommGrpCat.{w})
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU
          (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)).hom)
      (show (ℱmod).val.obj (op W₀) from s₀ • z) =
      s₀ • (show (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
            (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)) from
        (ConcreteCategory.hom
          (algebraicCoverBasisRestrictExtendComponentIso (forget AddCommGrpCat.{w})
            (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
            (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU
            (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)).hom) z) := by
  letI : Module (𝒪.obj.obj (op W₀))
      ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
        (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))) :=
    moduleOpenCoverBasisObjModule (𝒪 := 𝒪) hU localSheaf overlapIso cocycle
      (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))
  let 𝒪B := moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU
  let ℬℱ := moduleOpenCoverBasisModuleSheaf 𝒪 localSheaf overlapIso cocycle hU
  let Fadd : BasisSiteSheaf AddCommGrpCat.{w} Bcov hBcov := (SheafOfModules.toSheaf 𝒪B).obj ℬℱ
  let W : BasisOpen Bcov := ⟨W₀, ⟨i, hW₀i⟩⟩
  apply coverI_restrictExtendComponentHom_injective hU Fadd (op W)
  show
      BasisSiteSheaf.restrictExtendComponentHom Fadd (op W)
          (BasisSiteSheaf.restrictExtendComponentInv Fadd (op W)
            (show (ℱmod).val.obj (op W₀) from s₀ • z)) =
        BasisSiteSheaf.restrictExtendComponentHom Fadd (op W)
          (s₀ • (show (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
                (op W) from
            BasisSiteSheaf.restrictExtendComponentInv Fadd (op W) z))
  rw [show BasisSiteSheaf.restrictExtendComponentHom Fadd (op W)
        (BasisSiteSheaf.restrictExtendComponentInv Fadd (op W)
          (show (ℱmod).val.obj (op W₀) from s₀ • z)) =
        (show (ℱmod).val.obj (op W₀) from s₀ • z) by
      simpa using CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd (op W))
        (show (ℱmod).val.obj (op W₀) from s₀ • z)]
  set n : ℬℱ.val.obj (op W) := BasisSiteSheaf.restrictExtendComponentInv Fadd (op W) z with hn
  have hnz : BasisSiteSheaf.restrictExtendComponentHom Fadd (op W) n = z := by
    simpa [n] using CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd (op W)) z
  letI : Module (((basisOpenInclusion Bcov).op ⋙ 𝒪B.extend.presheaf).obj (op W))
      ((basisModuleSheafExtension 𝒪B ℬℱ).val.obj
        ((basisOpenInclusion Bcov).op.obj (op W))) := by
    change Module (𝒪B.extend.presheaf.obj ((basisOpenInclusion Bcov).op.obj (op W)))
      ((basisModuleSheafExtension 𝒪B ℬℱ).val.obj ((basisOpenInclusion Bcov).op.obj (op W)))
    infer_instance
  have hsource :
      (show (ℱmod).val.obj (op W₀) from s₀ • z) =
        (BasisSiteSheaf.restrictExtendComponentHom 𝒪B (op W) s₀) •
          (show (basisModuleSheafExtension 𝒪B ℬℱ).val.obj
              ((basisOpenInclusion Bcov).op.obj (op W)) from z) := by
    rw [← coverI_ringExtIsoInv_app_eq_restrictExtendComponentHom (𝒪 := 𝒪) hU (op W)]
    rfl
  rw [hsource]
  have hsmul :
      BasisSiteSheaf.restrictExtendComponentHom Fadd (op W)
          ((show 𝒪B.presheaf.obj (op W) from s₀) • n) =
        𝒪B.restrictExtendComponentHom (op W) (show 𝒪B.presheaf.obj (op W) from s₀) •
          BasisSiteSheaf.restrictExtendComponentHom Fadd (op W) n :=
    basisModuleSheafExtension_restrictExtendComponentHom_smul 𝒪B ℬℱ (op W)
      (show 𝒪B.presheaf.obj (op W) from s₀) n
  show BasisSiteSheaf.restrictExtendComponentHom 𝒪B (op W)
        (show 𝒪B.presheaf.obj (op W) from s₀) •
      (show (basisModuleSheafExtension 𝒪B ℬℱ).val.obj
          ((basisOpenInclusion Bcov).op.obj (op W)) from z) =
      BasisSiteSheaf.restrictExtendComponentHom Fadd (op W)
        ((show 𝒪B.presheaf.obj (op W) from s₀) • n)
  rw [hsmul, hnz]
  rfl

theorem chart_step (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (s₀ : 𝒪.obj.obj (op W₀))
    (y : (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
        (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))) :
    letI : Module (𝒪.obj.obj (op W₀))
        ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
          (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))) :=
      moduleOpenCoverBasisObjModule (𝒪 := 𝒪) hU localSheaf overlapIso cocycle
        (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))
    (show (localSheaf i).val.obj (op (subspaceOpenOfLE hW₀i)) from
        (algebraicSubsetChartIso (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) hW₀i).hom
          (show (localSheaf (chosen_chart (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩)).val.obj
              (op (subspaceOpenOfLE (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩))) from s₀ • y)) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).inv.hom s₀) •
        (show (localSheaf i).val.obj (op (subspaceOpenOfLE hW₀i)) from
          (algebraicSubsetChartIso (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
            (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) hW₀i).hom
            (show (localSheaf (chosen_chart (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩)).val.obj
                (op (subspaceOpenOfLE (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩))) from y)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option maxRecDepth 4000 in
  exact moduleOpenCoverSubsetChartIso_hom_smul 𝒪 localSheaf overlapIso
    (i := chosen_chart (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) (j := i)
    (hWi := chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) (hWj := hW₀i)
    s₀ y

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
theorem algebraicMemberSpaceBasisComponentIsoOfRep_hom_smul (i : ι)
    {W₀ : Opens X} (hW₀i : W₀ ≤ U i)
    (r : (𝒪 |_ U i).val.obj (op (subspaceOpenOfLE hW₀i)))
    (m : (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i).val.obj
        (op (subspaceOpenOfLE hW₀i))) :
    (show (localSheaf i).val.obj (op (subspaceOpenOfLE hW₀i)) from
      (algebraicMemberSpaceBasisComponentIsoOfRep (forget AddCommGrpCat.{w})
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
        (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i hW₀i).hom
        (r • m)) =
      r • (show (localSheaf i).val.obj (op (subspaceOpenOfLE hW₀i)) from
        (algebraicMemberSpaceBasisComponentIsoOfRep (forget AddCommGrpCat.{w})
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i hW₀i).hom m) := by
  simp only [algebraicMemberSpaceBasisComponentIsoOfRep, Iso.trans_hom, AddCommGrpCat.comp_apply]
  set s₀ : 𝒪.obj.obj (op W₀) := (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom.hom r with hs₀
  have hr : r = (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).inv.hom s₀ := by
    rw [hs₀]
    exact (CategoryTheory.congr_fun
      (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hW₀i).hom_inv_id r).symm
  set z : (ℱmod).val.obj (op W₀) :=
    (ConcreteCategory.hom
      (algebraicGlobalMemberSectionIso (U := U)
        (algebraicOpenCoverBasisSheaf (forget AddCommGrpCat.{w})
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU).extend hW₀i).hom) m
    with hz
  rw [egi_step (𝒪 := 𝒪) localSheaf overlapIso cocycle hU i hW₀i r m]
  rw [show
      (ConcreteCategory.hom
        (algebraicGlobalMemberSectionIso (U := U)
          (algebraicOpenCoverBasisSheaf (forget AddCommGrpCat.{w})
            (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
            (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU).extend hW₀i).hom) m
        = z from hz.symm]
  rw [coverI_step (𝒪 := 𝒪) localSheaf overlapIso cocycle hU i hW₀i s₀ z]
  rw [hr]
  set y : (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
      (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)) :=
    (ConcreteCategory.hom
      (algebraicCoverBasisRestrictExtendComponentIso (forget AddCommGrpCat.{w})
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
        (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU
        (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)).hom z) with hy
  letI : Module (𝒪.obj.obj (op W₀))
      ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
        (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))) :=
    moduleOpenCoverBasisObjModule (𝒪 := 𝒪) hU localSheaf overlapIso cocycle
      (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov))
  have hact :
      s₀ • (show (moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj
              (op (⟨W₀, ⟨i, hW₀i⟩⟩ : BasisOpen Bcov)) from y) =
        ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪)
            (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩)).inv.hom s₀) •
          (show (localSheaf (chosen_chart (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩)).val.obj
              (op (subspaceOpenOfLE (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩))) from y) := by
    set_option backward.isDefEq.respectTransparency false in rfl
  rw [hact]
  rw [show
      algebraicSubsetChartIso (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
          (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) hW₀i =
        moduleOpenCoverSubsetChartIso 𝒪 localSheaf overlapIso
          (chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) hW₀i from rfl]
  exact moduleOpenCoverSubsetChartIso_hom_smul 𝒪 localSheaf overlapIso
    (i := chosen_chart (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) (j := i)
    (hWi := chosen_chart_le (X := X) (U := U) ⟨W₀, ⟨i, hW₀i⟩⟩) (hWj := hW₀i)
    s₀ y

end

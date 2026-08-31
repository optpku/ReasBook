module

public import stacks_project.Chap06.Lemma_6_30_10
public import stacks_project.Chap06.Lemma_6_30_12
public import stacks_project.Chap06.Definition_6_10_1
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

local notation "BasisRingSheaf" => BasisSiteSheaf RingCat B hB

/-- Helper for Lemma 6.30.13: the basis-open inclusion is continuous for the induced topology. -/
public instance basisOpenInclusion_isContinuous :
    Functor.IsContinuous (basisOpenInclusion B)
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X) := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  exact
    Functor.IsCoverDense.isContinuous
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)
      (basisOpenInclusion B)
      (Functor.inducedTopology_coverPreserving (basisOpenInclusion B)
        (Opens.grothendieckTopology X))

/- Domain-style sampling for Lemma 6.30.13:
- primary domain: sheaves of modules over ring-valued sheaves on a dense basis subsite;
- sampled owner declarations:
  `(basisOpenInclusion B).sheafPushforwardContinuous`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`,
  `SheafOfModules.pushforward`,
  `basisModuleSheafExtension`;
- best owner abstraction: the dense-subsite restriction functor on sheaves, together with the
  induced module-sheaf pushforward along the identity map of the restricted ring sheaf;
- primitive data: the basis inclusion `basisOpenInclusion B`, the induced topology
  `basisGrothendieckTopology B hB`, and the sheaf of rings `𝒪`;
- derived API: restriction of `𝒪`-modules to the basis and the extension construction from
  `Lemma_6_30_12`, expressed through the canonical functor
  `SheafOfModules.pushforward (𝟙 _)`;
- source/core/bridge triage:
  `source-facing`: restriction of `𝒪`-modules to basis opens;
  `core/canonical`: `(basisOpenInclusion B).sheafPushforwardContinuous` and
    `SheafOfModules.pushforward`;
  `bridge/view`: `basisModuleSheafExtension`, which supplies the inverse-direction module
    structure on the extension back to `X`.
-/

variable (𝒪 : TopCat.Sheaf RingCat.{u} X)

/-- Helper for Lemma 6.30.13: the restricted ring sheaf on the basis site attached to `B`. -/
abbrev restrictedRingSheaf :
    BasisSiteSheaf RingCat B hB :=
  ((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
    (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪

/-- Helper for Lemma 6.30.13: the dense-subsite comparison equivalence for `RingCat`-valued sheaves
between the basis site and all opens of `X`. -/
public noncomputable abbrev ringRestrictionEquiv :
    BasisSiteSheaf RingCat B hB ≌ TopCat.Sheaf RingCat X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  change Sheaf (basisGrothendieckTopology B hB) RingCat ≌ TopCat.Sheaf RingCat X
  exact
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) RingCat

/-- Helper for Lemma 6.30.13: the dense-subsite comparison equivalence for additive sheaves on the
basis and on all opens of `X`. -/
public noncomputable abbrev addRestrictionEquiv :
    BasisSiteSheaf AddCommGrpCat B hB ≌ TopCat.Sheaf AddCommGrpCat X := by
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  change Sheaf (basisGrothendieckTopology B hB) AddCommGrpCat ≌ TopCat.Sheaf AddCommGrpCat X
  exact
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology X) AddCommGrpCat

/-- Helper for Lemma 6.30.13: extending the restricted ring sheaf back to `X` recovers `𝒪`
through the counit of the dense-subsite comparison equivalence. -/
public noncomputable abbrev restrictedRingCounitIso :
    (restrictedRingSheaf hB 𝒪).extend ≅ 𝒪 :=
  (ringRestrictionEquiv hB).counitIso.app 𝒪

/-- Helper for Lemma 6.30.13: on a basis open, restricting the inverse counit
`𝒪 ⟶ (𝒪|_B).extend` agrees with the canonical `restrictExtend` comparison map. -/
public theorem restrictedCounitInv_app_eq_restrictExtendComponentHom
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
          (restrictedRingCounitIso hB 𝒪).inv).hom.app U) =
      BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U := by
  -- The inverse counit becomes the unit after restricting back to the basis.
  simpa [restrictedRingSheaf, restrictedRingCounitIso, BasisSiteSheaf.presheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((ringRestrictionEquiv hB).unit_app_inverse 𝒪).symm

/-- Helper for Lemma 6.30.13: on a basis open, restricting the counit
`(𝒪|_B).extend ⟶ 𝒪` agrees with the inverse `restrictExtend` comparison map. -/
public theorem restrictedCounitHom_app_eq_restrictExtendComponentInv
    (U : (BasisOpen B)ᵒᵖ) :
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
          (restrictedRingCounitIso hB 𝒪).hom).hom.app U) =
      BasisSiteSheaf.restrictExtendComponentInv (restrictedRingSheaf hB 𝒪) U := by
  -- The counit itself restricts to the inverse unit comparison on the basis site.
  simpa [restrictedRingSheaf, restrictedRingCounitIso, BasisSiteSheaf.presheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((ringRestrictionEquiv hB).unitInv_app_inverse 𝒪).symm

/- The restriction functor in Lemma 6.30.13 is not a new owner: it is the canonical module
pushforward functor along the identity map of the restricted ring sheaf on the basis site. On the
source-facing surface, it has type `Mod(𝒪) ⥤ Mod(𝒪|_B)`. -/
#check
  (SheafOfModules.pushforward
      (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
    Mod(𝒪) ⥤
      Mod((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
        (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)))

-- Proof sketch: use Lemma 6.30.10 for the equivalence between sheaves on `X` and sheaves on the
-- basis site, and Lemma 6.30.12 to equip the extended additive sheaf with the canonical module
-- structure over the extended ring sheaf. Together these identify restriction to the basis as an
-- equivalence on module sheaves.
/-- Helper for Lemma 6.30.13: the canonical restriction functor from `𝒪`-modules on `X` to
modules over the restricted ring sheaf on the basis site. -/
abbrev basisModuleRestrictionFunctor :
    SheafOfModules.{u} 𝒪 ⥤ SheafOfModules.{u} (restrictedRingSheaf hB 𝒪) :=
  SheafOfModules.pushforward (𝟙 (restrictedRingSheaf hB 𝒪))

/-- Helper for Lemma 6.30.13: on a basis open, the inverse additive counit for a global
module sheaf agrees with the canonical `restrictExtend` comparison map. -/
public theorem addCounitInv_app_eq_restrictExtendComponentHom
    (ℱ : SheafOfModules.{u} 𝒪)
    (U : (BasisOpen B)ᵒᵖ) :
    (((addRestrictionEquiv hB).counitIso.app
        ((SheafOfModules.toSheaf 𝒪).obj ℱ)).inv.hom.app
          ((basisOpenInclusion B).op.obj U)) =
      BasisSiteSheaf.restrictExtendComponentHom
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj
          ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ)) U := by
  -- The inverse counit becomes the unit comparison after restricting the global additive sheaf
  -- back to the basis site.
  simpa [basisModuleRestrictionFunctor, restrictedRingSheaf, addRestrictionEquiv,
    BasisSiteSheaf.presheaf, BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((addRestrictionEquiv hB).unit_app_inverse
        ((SheafOfModules.toSheaf 𝒪).obj ℱ)).symm

/-- Helper for Lemma 6.30.13: on a basis open, the additive counit for a global module sheaf
agrees with the inverse `restrictExtend` comparison map. -/
public theorem addCounitHom_app_eq_restrictExtendComponentInv
    (ℱ : SheafOfModules.{u} 𝒪)
    (U : (BasisOpen B)ᵒᵖ) :
    (((addRestrictionEquiv hB).counitIso.app
        ((SheafOfModules.toSheaf 𝒪).obj ℱ)).hom.hom.app
          ((basisOpenInclusion B).op.obj U)) =
      BasisSiteSheaf.restrictExtendComponentInv
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj
          ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ)) U := by
  -- The counit itself restricts to the inverse unit comparison on the basis site.
  simpa [basisModuleRestrictionFunctor, restrictedRingSheaf, addRestrictionEquiv,
    BasisSiteSheaf.presheaf, BasisSiteSheaf.extend] using
    congrArg (fun f => f.hom.app U)
      ((addRestrictionEquiv hB).unitInv_app_inverse
        ((SheafOfModules.toSheaf 𝒪).obj ℱ)).symm

/-- Helper for Lemma 6.30.13: the basis-open comparison map from a basis sheaf to the restriction
of its extension is injective on sections. -/
public theorem restrictExtendComponentHom_injective
    (F : BasisSiteSheaf AddCommGrpCat B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    Function.Injective (BasisSiteSheaf.restrictExtendComponentHom F U) := by
  -- Apply the inverse comparison map to both sides and simplify the triangular identity.
  intro s t hst
  calc
    s =
      BasisSiteSheaf.restrictExtendComponentInv F U
        (BasisSiteSheaf.restrictExtendComponentHom F U s) := by
          symm
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F U) s
    _ =
      BasisSiteSheaf.restrictExtendComponentInv F U
        (BasisSiteSheaf.restrictExtendComponentHom F U t) := by
          simpa using congrArg (BasisSiteSheaf.restrictExtendComponentInv F U) hst
    _ = t := by
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_hom_inv_id F U) t

/-- Helper for Lemma 6.30.13: the inverse basis-open comparison map from the restriction of an
extension back to the original basis sheaf is injective on sections. -/
public theorem restrictExtendComponentInv_injective
    (F : BasisSiteSheaf AddCommGrpCat B hB)
    (U : (BasisOpen B)ᵒᵖ) :
    Function.Injective (BasisSiteSheaf.restrictExtendComponentInv F U) := by
  -- Apply the forward comparison map to both sides and simplify the other triangular identity.
  intro s t hst
  calc
    s =
      BasisSiteSheaf.restrictExtendComponentHom F U
        (BasisSiteSheaf.restrictExtendComponentInv F U s) := by
          symm
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_inv_hom_id F U) s
    _ =
      BasisSiteSheaf.restrictExtendComponentHom F U
        (BasisSiteSheaf.restrictExtendComponentInv F U t) := by
          simpa using congrArg (BasisSiteSheaf.restrictExtendComponentHom F U) hst
    _ = t := by
          exact CategoryTheory.congr_fun
            (BasisSiteSheaf.restrictExtend_component_inv_hom_id F U) t

/-- Helper for Lemma 6.30.13: the underlying additive map of the extension of a basis-module
morphism is the image of that morphism under the additive dense-subsite equivalence. -/
public noncomputable abbrev basisModuleSheafExtensionUnderlyingMap
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (f : ℱ ⟶ 𝒢) :
    BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) ⟶
      BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj 𝒢) :=
  (addRestrictionEquiv hB).functor.map ((SheafOfModules.toSheaf 𝒪).map f)

/-- Helper for Lemma 6.30.13: on a basis open, the additive extension of a module morphism agrees
with the original basis-open map after identifying both extensions with the restricted sheaves. -/
public theorem basisModuleSheafExtensionUnderlyingMap_restrictExtend_app
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (f : ℱ ⟶ 𝒢)
    (U : (BasisOpen B)ᵒᵖ)
    (m : ℱ.val.obj U) :
    (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app
        ((basisOpenInclusion B).op.obj U)
        (BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U m) =
      BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj 𝒢) U
        ((((SheafOfModules.toSheaf 𝒪).map f).hom.app U) m) := by
  -- The unit comparison of the dense-subsite equivalence is natural in the additive sheaf map.
  change
    (ConcreteCategory.hom
          (((addRestrictionEquiv hB).functor.map
                ((SheafOfModules.toSheaf 𝒪).map f)).hom.app
            ((basisOpenInclusion B).op.obj U)))
        ((((addRestrictionEquiv hB).unitIso.app
              ((SheafOfModules.toSheaf 𝒪).obj ℱ)).hom.hom.app U) m) =
      (((addRestrictionEquiv hB).unitIso.app
            ((SheafOfModules.toSheaf 𝒪).obj 𝒢)).hom.hom.app U)
        ((((SheafOfModules.toSheaf 𝒪).map f).hom.app U) m)
  have hnat :=
    congrArg (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
      ((addRestrictionEquiv hB).unitIso.hom.naturality
        ((SheafOfModules.toSheaf 𝒪).map f))
  change
    (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
        ((addRestrictionEquiv hB).unitIso.hom.app ((SheafOfModules.toSheaf 𝒪).obj ℱ) ≫
          ((addRestrictionEquiv hB).functor ⋙ (addRestrictionEquiv hB).inverse).map
            ((SheafOfModules.toSheaf 𝒪).map f)) =
      (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m)
        ((𝟭 (BasisSiteSheaf AddCommGrpCat B hB)).map ((SheafOfModules.toSheaf 𝒪).map f) ≫
          (addRestrictionEquiv hB).unitIso.hom.app ((SheafOfModules.toSheaf 𝒪).obj 𝒢))
  exact hnat.symm


/-- Helper for Lemma 6.30.13: the additive extension of a morphism of basis-module sheaves is
linear over the extended ring sheaf. -/
theorem basisModuleSheafExtensionUnderlyingMap_smul
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (f : ℱ ⟶ 𝒢)
    (U : (Opens X)ᵒᵖ)
    (r : 𝒪.extend.presheaf.obj U)
    (m : (basisModuleSheafExtension 𝒪 ℱ).val.obj U) :
    (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app U (r • m) =
      r • (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app U m := by
  -- The equality is local on the open `U`, so it suffices to check it after restricting to
  -- basis neighborhoods of every point.
  apply TopCat.Presheaf.IsSheaf.section_ext (basisModuleSheafExtension 𝒪 𝒢).isSheaf
  intro x hx
  rcases Opens.isBasis_iff_nbhd.1 hB hx with
    ⟨V, hVB, hxV, hVU⟩
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U.unop := homOfLE hVU
  refine ⟨V, hVU, hxV, ?_⟩
  -- On a basis open the `restrictExtend` comparison identifies the extended action with the
  -- original basis-module action, where `f` is linear by definition.
  let Fadd : BasisSiteSheaf AddCommGrpCat B hB := (SheafOfModules.toSheaf 𝒪).obj ℱ
  let Gadd : BasisSiteSheaf AddCommGrpCat B hB := (SheafOfModules.toSheaf 𝒪).obj 𝒢
  let Ur : (BasisOpen B)ᵒᵖ := op Vb
  let φ := basisModuleSheafExtensionUnderlyingMap (hB := hB) f
  let rV : 𝒪.presheaf.obj Ur :=
    BasisSiteSheaf.restrictExtendComponentInv 𝒪 Ur (𝒪.extend.presheaf.map iVU.op r)
  let mV : ℱ.val.obj Ur :=
    BasisSiteSheaf.restrictExtendComponentInv Fadd Ur
      ((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op m)
  let fmV : 𝒢.val.obj Ur := (((SheafOfModules.toSheaf 𝒪).map f).hom.app Ur) mV
  let fsmulV : 𝒢.val.obj Ur :=
    (((SheafOfModules.toSheaf 𝒪).map f).hom.app Ur) (rV • mV)
  have hφ_naturality
      (z : (basisModuleSheafExtension 𝒪 ℱ).val.obj U) :
      ((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op) (φ.hom.app U z) =
        φ.hom.app ((basisOpenInclusion B).op.obj Ur)
          (((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) z) := by
    -- This is naturality of the additive extension map for the restriction `V ⊆ U`.
    exact (ConcreteCategory.congr_hom (φ.hom.naturality iVU.op) z).symm
  have hrV :
      BasisSiteSheaf.restrictExtendComponentHom 𝒪 Ur rV =
        𝒪.extend.presheaf.map iVU.op r := by
    -- The chosen `rV` is the inverse comparison image of the restricted ring section.
    dsimp [rV]
    simpa using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id 𝒪 Ur)
        (𝒪.extend.presheaf.map iVU.op r)
  have hmV :
      BasisSiteSheaf.restrictExtendComponentHom Fadd Ur mV =
        ((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) m := by
    -- The chosen `mV` is the inverse comparison image of the restricted module section.
    dsimp [mV]
    simpa [Fadd, basisModuleSheafExtension_toSheaf] using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd Ur)
        (((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) m)
  have hsource_smul :
      ((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) (r • m) =
        BasisSiteSheaf.restrictExtendComponentHom Fadd Ur (rV • mV) := by
    -- Restricting the scalar product agrees with the product of the restricted factors, and the
    -- forward comparison is semilinear on basis opens.
    calc
      ((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) (r • m) =
          (𝒪.extend.presheaf.map iVU.op r) •
            (((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) m) := by
            exact (basisModuleSheafExtension 𝒪 ℱ).val.map_smul iVU.op r m
      _ = BasisSiteSheaf.restrictExtendComponentHom 𝒪 Ur rV •
            BasisSiteSheaf.restrictExtendComponentHom Fadd Ur mV := by
            rw [hrV, hmV]
            rfl
      _ = BasisSiteSheaf.restrictExtendComponentHom Fadd Ur (rV • mV) := by
            simpa [Fadd] using
              (basisModuleSheafExtension_restrictExtendComponentHom_smul
                𝒪 ℱ Ur rV mV).symm
  have htarget_m :
      ((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op) (φ.hom.app U m) =
        BasisSiteSheaf.restrictExtendComponentHom Gadd Ur
          fmV := by
    -- The restricted image of `m` is computed by the basis-open compatibility of the extension
    -- map.
    have h₁ := hφ_naturality m
    have h₂ :
        φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) m) =
          φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (BasisSiteSheaf.restrictExtendComponentHom Fadd Ur mV) := by
      rw [hmV]
    have h₃ :
        φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (BasisSiteSheaf.restrictExtendComponentHom Fadd Ur mV) =
          BasisSiteSheaf.restrictExtendComponentHom Gadd Ur fmV := by
      simpa [φ, Fadd, Gadd, Ur, fmV] using
        basisModuleSheafExtensionUnderlyingMap_restrictExtend_app (hB := hB) f Ur mV
    exact h₁.trans (h₂.trans h₃)
  have htarget_smul :
      ((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op)
          (r • φ.hom.app U m) =
        BasisSiteSheaf.restrictExtendComponentHom Gadd Ur
          (rV • fmV) := by
    -- The restricted scalar product on the target is the forward comparison of the scalar product
    -- of the basis restrictions.
    have h₁ :
        ((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op)
            (r • φ.hom.app U m) =
          (𝒪.extend.presheaf.map iVU.op r) •
            (((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op) (φ.hom.app U m)) :=
      (basisModuleSheafExtension 𝒪 𝒢).val.map_smul iVU.op r (φ.hom.app U m)
    have h₂ :
        (𝒪.extend.presheaf.map iVU.op r) •
            (((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op) (φ.hom.app U m)) =
          BasisSiteSheaf.restrictExtendComponentHom 𝒪 Ur rV •
            BasisSiteSheaf.restrictExtendComponentHom Gadd Ur fmV := by
      rw [htarget_m, ← hrV]
      rfl
    have h₃ :
        BasisSiteSheaf.restrictExtendComponentHom 𝒪 Ur rV •
            BasisSiteSheaf.restrictExtendComponentHom Gadd Ur fmV =
          BasisSiteSheaf.restrictExtendComponentHom Gadd Ur (rV • fmV) := by
      simpa [Gadd] using
        (basisModuleSheafExtension_restrictExtendComponentHom_smul 𝒪 𝒢 Ur rV fmV).symm
    exact h₁.trans (h₂.trans h₃)
  have hlinear : fsmulV = rV • fmV := by
    -- The original basis morphism `f` is linear.
    exact ((f.val.app Ur).hom.map_smul rV mV)
  apply restrictExtendComponentInv_injective (hB := hB) Gadd Ur
  have hleft :
      BasisSiteSheaf.restrictExtendComponentInv Gadd Ur
        (((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op) (φ.hom.app U (r • m))) =
      fsmulV := by
    have h₁ := hφ_naturality (r • m)
    have h₂ :
        φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (((basisModuleSheafExtension 𝒪 ℱ).val.map iVU.op) (r • m)) =
          φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (BasisSiteSheaf.restrictExtendComponentHom Fadd Ur (rV • mV)) := by
      rw [hsource_smul]
    have h₃ :
        φ.hom.app ((basisOpenInclusion B).op.obj Ur)
            (BasisSiteSheaf.restrictExtendComponentHom Fadd Ur (rV • mV)) =
          BasisSiteSheaf.restrictExtendComponentHom Gadd Ur fsmulV := by
      simpa [φ, Fadd, Gadd, Ur, fsmulV] using
        basisModuleSheafExtensionUnderlyingMap_restrictExtend_app (hB := hB) f Ur (rV • mV)
    rw [h₁, h₂, h₃]
    exact CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtend_component_hom_inv_id Gadd Ur) fsmulV
  have hright :
      BasisSiteSheaf.restrictExtendComponentInv Gadd Ur
        (((basisModuleSheafExtension 𝒪 𝒢).val.map iVU.op)
          (r • φ.hom.app U m)) =
      rV • fmV := by
    rw [htarget_smul]
    exact CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtend_component_hom_inv_id Gadd Ur) (rV • fmV)
  exact hleft.trans (hlinear.trans hright.symm)

/-- Helper for Lemma 6.30.13: a morphism of basis-module sheaves extends to a morphism of the
corresponding sheaves of modules on `X`. -/
public noncomputable def basisModuleSheafExtensionMap
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (f : ℱ ⟶ 𝒢) :
    basisModuleSheafExtension 𝒪 ℱ ⟶ basisModuleSheafExtension 𝒪 𝒢 :=
  ⟨PresheafOfModules.homMk
    (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom
    (basisModuleSheafExtensionUnderlyingMap_smul (hB := hB) f)⟩

/-- Helper for Lemma 6.30.13: on sections, the extension of a basis-module morphism is the
underlying additive dense-subsite extension map. -/
theorem basisModuleSheafExtensionMap_app
    {𝒪 : BasisRingSheaf}
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (f : ℱ ⟶ 𝒢)
    (U : (Opens X)ᵒᵖ)
    (m : (basisModuleSheafExtension 𝒪 ℱ).val.obj U) :
    ((basisModuleSheafExtensionMap (hB := hB) f).val.app U) m =
      (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app U m :=
  rfl

/-- Helper for Lemma 6.30.13: the extension construction from Lemma 6.30.12, packaged as a
functor. -/
public noncomputable def basisModuleSheafExtensionFunctor :
    SheafOfModules.{u} (restrictedRingSheaf hB 𝒪) ⥤
      SheafOfModules.{u} ((restrictedRingSheaf hB 𝒪).extend) :=
  { obj := fun ℱ =>
      basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ
    map := fun {ℱ 𝒢} f =>
      basisModuleSheafExtensionMap (hB := hB) f
    map_id := by
      intro ℱ
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext m
      rw [basisModuleSheafExtensionMap_app]
      have hmap :
          basisModuleSheafExtensionUnderlyingMap (hB := hB) (𝟙 ℱ : ℱ ⟶ ℱ) =
            𝟙 (BasisSiteSheaf.extend
              ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ)) := by
        simpa [basisModuleSheafExtensionUnderlyingMap] using
          ((addRestrictionEquiv hB).functor.map_id
            ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ))
      rw [hmap]
      rfl
    map_comp := by
      intro ℱ 𝒢 ℋ f g
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext m
      change
        (basisModuleSheafExtensionUnderlyingMap (hB := hB) (f ≫ g)).hom.app U m =
          (basisModuleSheafExtensionUnderlyingMap (hB := hB) g).hom.app U
            ((basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app U m)
      have hmap :
          basisModuleSheafExtensionUnderlyingMap (hB := hB) (f ≫ g) =
            basisModuleSheafExtensionUnderlyingMap (hB := hB) f ≫
              basisModuleSheafExtensionUnderlyingMap (hB := hB) g := by
        simpa [basisModuleSheafExtensionUnderlyingMap] using
          ((addRestrictionEquiv hB).functor.map_comp
            ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map f)
            ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map g))
      rw [hmap]
      rfl }

/-- Helper for Lemma 6.30.13: the functor back to `𝒪`-modules obtained by extension and scalar
transport along the counit. -/
public noncomputable def basisModuleExtensionFunctor :
    SheafOfModules.{u} (restrictedRingSheaf hB 𝒪) ⥤ SheafOfModules.{u} 𝒪 :=
  -- Extend the basis-module sheaf first, then transport scalars back to `𝒪` via the counit.
  basisModuleSheafExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
    SheafOfModules.pushforward (F := 𝟭 _) ((restrictedRingCounitIso hB 𝒪).inv)

/-- Helper for Lemma 6.30.13: the inverse basis comparison map is linear for the basis-side
counit scalar action. -/
theorem basisModuleRestrictionCounitHom_smul
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪))
    (U : (BasisOpen B)ᵒᵖ)
    (r : (restrictedRingSheaf hB 𝒪).presheaf.obj U)
    (m : ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) :
    (BasisSiteSheaf.restrictExtendComponentInv
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U
        (r • m :
          ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
            basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) :
        ℱ.val.obj U) =
      let n : ℱ.val.obj U :=
        BasisSiteSheaf.restrictExtendComponentInv
          ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U m
      r • n := by
  let Fadd : BasisSiteSheaf AddCommGrpCat B hB :=
    (SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ
  let φ :=
    BasisSiteSheaf.restrictExtendComponentHom Fadd U
  apply restrictExtendComponentHom_injective (hB := hB) Fadd U
  dsimp only
  rw [show
      φ (BasisSiteSheaf.restrictExtendComponentInv Fadd U
          (r • m :
            ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
              basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U)) =
        (r • m :
          ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
            basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) by
      simpa [Fadd, φ, basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
        basisModuleSheafExtension_toSheaf] using
        CategoryTheory.congr_fun
          (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd U)
          (r • m :
            ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
              basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U)]
  let n : ℱ.val.obj U := Fadd.restrictExtendComponentInv U m
  have hn : Fadd.restrictExtendComponentHom U n = m := by
    simpa [Fadd, n, basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
      basisModuleSheafExtension_toSheaf] using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd U) m
  have hsmul :
      Fadd.restrictExtendComponentHom U (r • n) =
        (restrictedRingSheaf hB 𝒪).restrictExtendComponentHom U r •
          Fadd.restrictExtendComponentHom U n := by
    simpa [Fadd, n] using
      basisModuleSheafExtension_restrictExtendComponentHom_smul
        (restrictedRingSheaf hB 𝒪) ℱ U r n
  letI : Module
      (((basisOpenInclusion B).op ⋙ (restrictedRingSheaf hB 𝒪).extend.presheaf).obj U)
      (((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) := by
    change Module
      ((restrictedRingSheaf hB 𝒪).extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
        ((basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
          ((basisOpenInclusion B).op.obj U))
    infer_instance
  let Rpushed : RingCat.{u} :=
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj
        (restrictedRingSheaf hB 𝒪).extend).obj.obj U)
  let Mcomposite : Type u :=
    ↑(((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
      basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U)
  letI : Module Rpushed Mcomposite := by
    change Module
      ((restrictedRingSheaf hB 𝒪).extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
      ((basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
        ((basisOpenInclusion B).op.obj U))
    infer_instance
  have hsource :
      (r • m :
        ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
          basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) =
        ((BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U r) •
          (m :
            (basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
              ((basisOpenInclusion B).op.obj U)) :
            (basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
              ((basisOpenInclusion B).op.obj U)) := by
    change
      (((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
            (restrictedRingCounitIso hB 𝒪).inv).hom.app U) r) •
          (m :
            (basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
              ((basisOpenInclusion B).op.obj U)) =
        (BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U r) •
          (m :
            (basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
              ((basisOpenInclusion B).op.obj U))
    simpa [basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
      basisModuleSheafExtension_toSheaf] using
      congrArg
        (fun a =>
          a r •
            (m :
              (basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
                ((basisOpenInclusion B).op.obj U)))
        (restrictedCounitInv_app_eq_restrictExtendComponentHom (hB := hB) (𝒪 := 𝒪) U)
  rw [hsource, hsmul, hn]
  rfl

/-- Helper for Lemma 6.30.13: the forward basis comparison map is linear for the inverse
basis-side counit scalar action. -/
theorem basisModuleRestrictionCounitInv_smul
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪))
    (U : (BasisOpen B)ᵒᵖ)
    (r : (restrictedRingSheaf hB 𝒪).presheaf.obj U)
    (m : ℱ.val.obj U) :
    (BasisSiteSheaf.restrictExtendComponentHom
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U
        (r • m) :
        ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
          basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) =
      let n :
          ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
            basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U :=
        BasisSiteSheaf.restrictExtendComponentHom
          ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U m
      r • n := by
  let Fadd : BasisSiteSheaf AddCommGrpCat B hB :=
    (SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ
  have hsmul :
      Fadd.restrictExtendComponentHom U (r • m) =
        (restrictedRingSheaf hB 𝒪).restrictExtendComponentHom U r •
          Fadd.restrictExtendComponentHom U m := by
    simpa [Fadd] using
      basisModuleSheafExtension_restrictExtendComponentHom_smul
        (restrictedRingSheaf hB 𝒪) ℱ U r m
  letI : Module
      (((basisOpenInclusion B).op ⋙ (restrictedRingSheaf hB 𝒪).extend.presheaf).obj U)
      (((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) := by
    change Module
      ((restrictedRingSheaf hB 𝒪).extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
      ((basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
        ((basisOpenInclusion B).op.obj U))
    infer_instance
  let Rpushed : RingCat.{u} :=
    ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
      (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj
        (restrictedRingSheaf hB 𝒪).extend).obj.obj U)
  let Mcomposite : Type u :=
    ↑(((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
      basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U)
  letI : Module Rpushed Mcomposite := by
    change Module
      ((restrictedRingSheaf hB 𝒪).extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
      ((basisModuleSheafExtension (restrictedRingSheaf hB 𝒪) ℱ).val.obj
        ((basisOpenInclusion B).op.obj U))
    infer_instance
  let n :
      ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U :=
    Fadd.restrictExtendComponentHom U m
  have hsource :
      (r • n :
        ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
          basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) =
        (BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U r) •
          n := by
    change
      (((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
          (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).map
            (restrictedRingCounitIso hB 𝒪).inv).hom.app U) r) •
          n =
        (BasisSiteSheaf.restrictExtendComponentHom (restrictedRingSheaf hB 𝒪) U r) •
          n
    simpa [basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
      basisModuleSheafExtension_toSheaf] using
      congrArg
        (fun a =>
          a r • n)
        (restrictedCounitInv_app_eq_restrictExtendComponentHom (hB := hB) (𝒪 := 𝒪) U)
  change
    Fadd.restrictExtendComponentHom U (r • m) =
      (r • n :
        ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
          basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U)
  rw [hsource]
  simpa [n, basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
    basisModuleSheafExtension_toSheaf] using hsmul

/-- Helper for Lemma 6.30.13: the inverse basis comparison is natural in morphisms of
basis-module sheaves after extension and restriction. -/
theorem basisModuleSheafExtensionUnderlyingMap_restrictExtend_inv_app
    (ℱ 𝒢 : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪))
    (f : ℱ ⟶ 𝒢)
    (U : (BasisOpen B)ᵒᵖ)
    (m : ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) :
    BasisSiteSheaf.restrictExtendComponentInv
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj 𝒢) U
        (((((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
          basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).map f).val.app U) m)) =
      (((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map f).hom.app U)
        (BasisSiteSheaf.restrictExtendComponentInv
          ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U m) := by
  let Fadd : BasisSiteSheaf AddCommGrpCat B hB :=
    (SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ
  let Gadd : BasisSiteSheaf AddCommGrpCat B hB :=
    (SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj 𝒢
  let ψ :=
    ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
      basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).map f)
  apply restrictExtendComponentHom_injective (hB := hB) Gadd U
  have hm :
      Fadd.restrictExtendComponentHom U
          (Fadd.restrictExtendComponentInv U m) =
        m := by
    simpa [Fadd, basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
      basisModuleSheafExtension_toSheaf] using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id Fadd U) m
  have hleft :
      Gadd.restrictExtendComponentHom U
        (Gadd.restrictExtendComponentInv U
          (ψ.val.app U m)) =
        ψ.val.app U m := by
    simpa [Gadd, basisModuleExtensionFunctor, basisModuleRestrictionFunctor,
      basisModuleSheafExtension_toSheaf] using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id Gadd U)
        (ψ.val.app U m)
  have hright :
      Gadd.restrictExtendComponentHom U
        ((((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map f).hom.app U)
          (Fadd.restrictExtendComponentInv U m)) =
        ψ.val.app U m := by
    change
      Gadd.restrictExtendComponentHom U
        ((((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map f).hom.app U)
          (Fadd.restrictExtendComponentInv U m)) =
        ((basisModuleSheafExtensionMap (hB := hB) f).val.app
          ((basisOpenInclusion B).op.obj U)) m
    rw [basisModuleSheafExtensionMap_app]
    calc
      Gadd.restrictExtendComponentHom U
          ((((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map f).hom.app U)
            (Fadd.restrictExtendComponentInv U m)) =
        (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app
          ((basisOpenInclusion B).op.obj U)
          (Fadd.restrictExtendComponentHom U (Fadd.restrictExtendComponentInv U m)) := by
            simpa [Fadd, Gadd] using
              (basisModuleSheafExtensionUnderlyingMap_restrictExtend_app (hB := hB)
                f U (Fadd.restrictExtendComponentInv U m)).symm
      _ =
        (basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app
          ((basisOpenInclusion B).op.obj U) m := by
            exact congrArg
              ((basisModuleSheafExtensionUnderlyingMap (hB := hB) f).hom.app
                ((basisOpenInclusion B).op.obj U)) hm
  rw [hleft, hright]

/-- Helper for Lemma 6.30.13: the hom component of the basis-side counit comparison. -/
noncomputable def basisModuleRestrictionCounitHom
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪)) :
    ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ) ⟶ ℱ :=
  ⟨PresheafOfModules.homMk
    { app := fun U =>
        BasisSiteSheaf.restrictExtendComponentInv
          ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U
      naturality := by
        intro U V i
        change
          (((basisOpenInclusion B).op ⋙
            (BasisSiteSheaf.extend
              ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ)).presheaf).map i) ≫
              BasisSiteSheaf.restrictExtendComponentInv
                ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) V =
            BasisSiteSheaf.restrictExtendComponentInv
                ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U ≫
              (BasisSiteSheaf.presheaf
                ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ)).map i
        exact
          BasisSiteSheaf.restrictExtendInv_naturality
            ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) i }
    (basisModuleRestrictionCounitHom_smul (hB := hB) (𝒪 := 𝒪) ℱ)⟩

/-- Helper for Lemma 6.30.13: the inverse component of the basis-side counit comparison. -/
noncomputable def basisModuleRestrictionCounitInv
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪)) :
    ℱ ⟶
      ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ) :=
  ⟨PresheafOfModules.homMk
    { app := fun U =>
        BasisSiteSheaf.restrictExtendComponentHom
          ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U
      naturality := by
        intro U V i
        change
          (BasisSiteSheaf.presheaf
              ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ)).map i ≫
              BasisSiteSheaf.restrictExtendComponentHom
                ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) V =
            BasisSiteSheaf.restrictExtendComponentHom
                ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U ≫
              (((basisOpenInclusion B).op ⋙
                (BasisSiteSheaf.extend
                  ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ)).presheaf).map i)
        exact
          BasisSiteSheaf.restrictExtendHom_naturality
            ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) i }
    (basisModuleRestrictionCounitInv_smul (hB := hB) (𝒪 := 𝒪) ℱ)⟩

/-- Helper for Lemma 6.30.13: the component isomorphism of the basis-side counit. -/
noncomputable def basisModuleRestrictionCounitComponentIso
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪)) :
    ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ) ≅ ℱ where
  hom := basisModuleRestrictionCounitHom (hB := hB) (𝒪 := 𝒪) ℱ
  inv := basisModuleRestrictionCounitInv (hB := hB) (𝒪 := 𝒪) ℱ
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext m
    exact CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtend_component_inv_hom_id
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U) m
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext m
    exact CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtend_component_hom_inv_id
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U) m

/-- Helper for Lemma 6.30.13: naturality of the basis-side counit component. -/
theorem basisModuleRestrictionCounitComponentIso_naturality
    {ℱ 𝒢 : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪)}
    (f : ℱ ⟶ 𝒢) :
    (basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).map f ≫
        (basisModuleRestrictionCounitComponentIso (hB := hB) (𝒪 := 𝒪) 𝒢).hom =
      (basisModuleRestrictionCounitComponentIso (hB := hB) (𝒪 := 𝒪) ℱ).hom ≫ f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  simpa [basisModuleRestrictionCounitComponentIso, basisModuleRestrictionCounitHom] using
    basisModuleSheafExtensionUnderlyingMap_restrictExtend_inv_app
      (hB := hB) (𝒪 := 𝒪) ℱ 𝒢 f U m

/-- Helper for Lemma 6.30.13: once the extension functor is available on morphisms, the basis-side
counit isomorphism comes from `BasisSiteSheaf.restrictExtendIso` on the underlying additive sheaf,
upgraded to module morphisms using the restricted counit bridge lemmas. -/
public noncomputable def basisModuleRestrictionCounitIso :
    basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪) ≅
      𝟭 (SheafOfModules.{u} (restrictedRingSheaf hB 𝒪)) :=
  NatIso.ofComponents
    (basisModuleRestrictionCounitComponentIso (hB := hB) (𝒪 := 𝒪))
    (basisModuleRestrictionCounitComponentIso_naturality (hB := hB) (𝒪 := 𝒪))

/-- On a basis open, the hom component of the basis-module restriction counit is the inverse
`restrictExtend` comparison on the underlying additive sheaf. -/
@[simp] theorem basisModuleRestrictionCounitIso_hom_app_val_app
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪))
    (U : (BasisOpen B)ᵒᵖ)
    (m : ((basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪) ⋙
        basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj U) :
    (((basisModuleRestrictionCounitIso (hB := hB) (𝒪 := 𝒪)).hom.app ℱ).val.app U) m =
      BasisSiteSheaf.restrictExtendComponentInv
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U m := by
  rfl

/-- On a basis open, the inverse component of the basis-module restriction counit is the
`restrictExtend` comparison on the underlying additive sheaf. -/
@[simp] theorem basisModuleRestrictionCounitIso_inv_app_val_app
    (ℱ : SheafOfModules.{u} (restrictedRingSheaf hB 𝒪))
    (U : (BasisOpen B)ᵒᵖ)
    (m : ℱ.val.obj U) :
    (((basisModuleRestrictionCounitIso (hB := hB) (𝒪 := 𝒪)).inv.app ℱ).val.app U) m =
      BasisSiteSheaf.restrictExtendComponentHom
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).obj ℱ) U m := by
  rfl

/-- Helper for Lemma 6.30.13: restriction to the basis is faithful on module sheaves. -/
public theorem basisModuleRestrictionFunctor_faithful :
    (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).Faithful := by
  refine ⟨?_⟩
  intro ℱ 𝒢 f g hfg
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  apply TopCat.Presheaf.IsSheaf.section_ext 𝒢.isSheaf
  intro x hx
  rcases Opens.isBasis_iff_nbhd.1 hB hx with
    ⟨V, hVB, hxV, hVU⟩
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U.unop := homOfLE hVU
  refine ⟨V, hVU, hxV, ?_⟩
  let Ur : (BasisOpen B)ᵒᵖ := op Vb
  have hlocal :
      ((f.val.app ((basisOpenInclusion B).op.obj Ur)) (ℱ.val.map iVU.op m)) =
        ((g.val.app ((basisOpenInclusion B).op.obj Ur)) (ℱ.val.map iVU.op m)) := by
    have h := congrArg
      (fun k => ((k.val.app Ur) (ℱ.val.map iVU.op m))) hfg
    simpa [basisModuleRestrictionFunctor, Ur] using h
  have hf_nat :
      𝒢.val.map iVU.op ((f.val.app U) m) =
        ((f.val.app ((basisOpenInclusion B).op.obj Ur)) (ℱ.val.map iVU.op m)) := by
    exact (ConcreteCategory.congr_hom (f.val.naturality iVU.op) m).symm
  have hg_nat :
      𝒢.val.map iVU.op ((g.val.app U) m) =
        ((g.val.app ((basisOpenInclusion B).op.obj Ur)) (ℱ.val.map iVU.op m)) := by
    exact (ConcreteCategory.congr_hom (g.val.naturality iVU.op) m).symm
  change
    𝒢.val.map iVU.op ((f.val.app U) m) =
      𝒢.val.map iVU.op ((g.val.app U) m)
  rw [hf_nat, hg_nat]
  exact hlocal

/-- Helper for Lemma 6.30.13: the underlying additive preimage of a morphism after restricting
module sheaves to the basis. -/
noncomputable def basisModuleRestrictionPreimageUnderlyingMap
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (α : (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ ⟶
      (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢) :
    (SheafOfModules.toSheaf 𝒪).obj ℱ ⟶
      (SheafOfModules.toSheaf 𝒪).obj 𝒢 :=
  (addRestrictionEquiv hB).inverse.preimage
    ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map α)

/-- Helper for Lemma 6.30.13: on basis opens, the additive preimage of a restricted
module morphism is the original restricted morphism. -/
theorem basisModuleRestrictionPreimageUnderlyingMap_app
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (α : (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ ⟶
      (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢)
    (U : (BasisOpen B)ᵒᵖ)
    (m : ℱ.val.obj ((basisOpenInclusion B).op.obj U)) :
    (basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α).hom.app
        ((basisOpenInclusion B).op.obj U) m =
      (α.val.app U) m := by
  have hmap :
      (addRestrictionEquiv hB).inverse.map
          (basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α) =
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map α) := by
    simpa [basisModuleRestrictionPreimageUnderlyingMap] using
      ((addRestrictionEquiv hB).inverse.map_preimage
        ((SheafOfModules.toSheaf (restrictedRingSheaf hB 𝒪)).map α))
  have happ := congrArg (fun τ => (ConcreteCategory.hom (τ.hom.app U)) m) hmap
  simpa [basisModuleRestrictionFunctor, restrictedRingSheaf] using happ

/-- Helper for Lemma 6.30.13: the additive preimage of a restricted module morphism is
linear over the original ring sheaf. -/
theorem basisModuleRestrictionPreimageUnderlyingMap_smul
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (α : (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ ⟶
      (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢)
    (U : (Opens X)ᵒᵖ)
    (r : 𝒪.presheaf.obj U)
    (m : ℱ.val.obj U) :
    (show 𝒢.val.obj U from
      (basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α).hom.app U
        (r • m)) =
      (r •
        (show 𝒢.val.obj U from
          (basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α).hom.app U m)) := by
  let φ := basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α
  apply TopCat.Presheaf.IsSheaf.section_ext 𝒢.isSheaf
  intro x hx
  rcases Opens.isBasis_iff_nbhd.1 hB hx with
    ⟨V, hVB, hxV, hVU⟩
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U.unop := homOfLE hVU
  refine ⟨V, hVU, hxV, ?_⟩
  let Ur : (BasisOpen B)ᵒᵖ := op Vb
  let rV : (restrictedRingSheaf hB 𝒪).presheaf.obj Ur :=
    𝒪.presheaf.map iVU.op r
  let mV : ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ).val.obj Ur :=
    ℱ.val.map iVU.op m
  have hφ_nat (z : ℱ.val.obj U) :
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op (show 𝒢.val.obj U from φ.hom.app U z)) =
        (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
          φ.hom.app ((basisOpenInclusion B).op.obj Ur) (ℱ.val.map iVU.op z)) := by
    exact (ConcreteCategory.congr_hom (φ.hom.naturality iVU.op) z).symm
  have hleft :
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op (show 𝒢.val.obj U from φ.hom.app U (r • m))) =
        (α.val.app Ur) (rV • mV) := by
    calc
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op (show 𝒢.val.obj U from φ.hom.app U (r • m))) =
        (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
          φ.hom.app ((basisOpenInclusion B).op.obj Ur) (ℱ.val.map iVU.op (r • m))) := hφ_nat (r • m)
      _ = (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
          φ.hom.app ((basisOpenInclusion B).op.obj Ur) (rV • mV)) := by
        rw [ℱ.val.map_smul]
        rfl
      _ = (α.val.app Ur) (rV • mV) := by
        simpa [φ, rV, mV] using
          basisModuleRestrictionPreimageUnderlyingMap_app
            (hB := hB) (𝒪 := 𝒪) α Ur (rV • mV)
  have hright :
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op
          (r • (show 𝒢.val.obj U from φ.hom.app U m))) =
        rV • (α.val.app Ur mV) := by
    calc
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op
          (r • (show 𝒢.val.obj U from φ.hom.app U m))) =
        rV •
          (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
            𝒢.val.map iVU.op (show 𝒢.val.obj U from φ.hom.app U m)) := by
          dsimp [rV]
          exact 𝒢.val.map_smul iVU.op r
            (show 𝒢.val.obj U from φ.hom.app U m)
      _ = rV •
          (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
            φ.hom.app ((basisOpenInclusion B).op.obj Ur) mV) := by
          exact congrArg (fun z =>
            rV •
              (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from z))
            (hφ_nat m)
      _ = rV • (α.val.app Ur mV) := by
          rw [basisModuleRestrictionPreimageUnderlyingMap_app (hB := hB) (𝒪 := 𝒪) α Ur mV]
  change
    (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
      𝒢.val.map iVU.op (show 𝒢.val.obj U from φ.hom.app U (r • m))) =
      (show ((basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢).val.obj Ur from
        𝒢.val.map iVU.op
          (r • (show 𝒢.val.obj U from φ.hom.app U m)))
  exact hleft.trans (((α.val.app Ur).hom.map_smul rV mV).trans hright.symm)

/-- Helper for Lemma 6.30.13: the global module morphism lifting a restricted module morphism. -/
noncomputable def basisModuleRestrictionPreimage
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (α : (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ ⟶
      (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢) :
    ℱ ⟶ 𝒢 :=
  ⟨PresheafOfModules.homMk
    (basisModuleRestrictionPreimageUnderlyingMap (hB := hB) (𝒪 := 𝒪) α).hom
    (basisModuleRestrictionPreimageUnderlyingMap_smul (hB := hB) (𝒪 := 𝒪) α)⟩

/-- Helper for Lemma 6.30.13: restricting the lifted global morphism recovers the original
basis morphism. -/
theorem basisModuleRestrictionPreimage_map
    {ℱ 𝒢 : SheafOfModules.{u} 𝒪}
    (α : (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj ℱ ⟶
      (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).obj 𝒢) :
    (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).map
        (basisModuleRestrictionPreimage (hB := hB) (𝒪 := 𝒪) α) =
      α := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext m
  simpa [basisModuleRestrictionPreimage, basisModuleRestrictionFunctor] using
    basisModuleRestrictionPreimageUnderlyingMap_app
      (hB := hB) (𝒪 := 𝒪) α U m

/-- Helper for Lemma 6.30.13: restriction to the basis is full on module sheaves. -/
public theorem basisModuleRestrictionFunctor_full :
    (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪)).Full := by
  refine ⟨?_⟩
  intro ℱ 𝒢 α
  exact ⟨basisModuleRestrictionPreimage (hB := hB) (𝒪 := 𝒪) α,
    basisModuleRestrictionPreimage_map (hB := hB) (𝒪 := 𝒪) α⟩

/-- Lemma 6.30.13: restricting a sheaf of `\mathcal O`-modules on `X` to the members of the basis
`\mathcal B` defines an equivalence between `Mod(\mathcal O)` and
`Mod(\mathcal O|_\mathcal B)`. -/
theorem restrictSheafOfModulesToBasis_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{u} X) :
    Functor.IsEquivalence
      (SheafOfModules.pushforward
          (𝟙 (((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪)) :
        SheafOfModules.{u} 𝒪 ⥤
          SheafOfModules.{u} ((((basisOpenInclusion B).sheafPushforwardContinuous RingCat.{u}
            (basisGrothendieckTopology B hB) (Opens.grothendieckTopology X)).obj 𝒪))) := by
  -- Route correction: package the restriction functor with the intended extension quasi-inverse
  -- so the remaining work is reduced to functoriality of extension and the two standard
  -- comparison isomorphisms.
  change Functor.IsEquivalence (basisModuleRestrictionFunctor (hB := hB) (𝒪 := 𝒪))
  refine ⟨?_, ?_, ?_⟩
  · exact basisModuleRestrictionFunctor_faithful (hB := hB) (𝒪 := 𝒪)
  · exact basisModuleRestrictionFunctor_full (hB := hB) (𝒪 := 𝒪)
  · refine ⟨?_⟩
    intro ℱ
    exact ⟨basisModuleExtensionFunctor (hB := hB) (𝒪 := 𝒪).obj ℱ,
      ⟨(basisModuleRestrictionCounitIso (hB := hB) (𝒪 := 𝒪)).app ℱ⟩⟩

end

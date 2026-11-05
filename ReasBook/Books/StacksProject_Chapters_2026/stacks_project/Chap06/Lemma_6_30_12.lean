module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import stacks_project.Chap06.Basis_extension_preserves_stalks
public import stacks_project.Chap06.Lemma_6_30_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open BasisSiteSheaf

noncomputable section

universe u

/-!
Source correction for Stacks Lemma 6.30.12.

The printed proof does not compare two global owners for the extension. It works directly with
families of stalk elements satisfying the local representability condition from Lemma 6.30.6:
given ring-stalk data `(f_x)` and module-stalk data `(m_x)`, define the product family
`(f_x • m_x)` pointwise and check on a basis refinement that it is again locally represented by
ordinary sections on basis opens.

This file now exposes the source-faithful arbitrary-open stalk-family map and the resulting
extensionality statement. The remaining blocker is the reconstruction step: from a basis-stalk
family on an arbitrary open satisfying the local representability condition, rebuild the unique
global section of the extension sheaf.
-/

section

variable {X : TopCat.{u}} {B : Set (Opens X)} {hB : Opens.IsBasis B}

local notation "BasisRingSheaf" => BasisSiteSheaf RingCat B hB

/-- Helper for Lemma 6.30.12: the underlying additive basis sheaf of a sheaf of `𝒪`-modules. -/
public abbrev basisModuleAddSheaf
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) :
    BasisSiteSheaf AddCommGrpCat B hB :=
  ((SheafOfModules.toSheaf 𝒪).obj ℱ)

/-- Helper for Lemma 6.30.12: a section of the extension sheaf on an arbitrary open determines a
family of basis stalk elements by taking its germs and transporting them back along the canonical
stalk comparison isomorphism. -/
public abbrev extendSectionToBasisStalkFamily
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB) (U : Opens X) :
    G.extend.presheaf.obj (op U) → ∀ x : U, G.stalk x.1 :=
  fun s x ↦
    inv (BasisSiteSheaf.stalkComparison G x.1) (G.extend.presheaf.germ U x.1 x.2 s)

/-- Helper for Lemma 6.30.12: a family of basis stalk elements on an arbitrary open is locally
representable if every point admits a basis neighborhood inside the open on which the family is
induced by an honest basis section. We record the witness after applying `stalkComparison`, since
that is the bridge used by the extension sheaf germs. -/
public def IsLocallyRepresentableByBasis
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (U : Opens X) (t : ∀ x : U, G.stalk x.1) : Prop :=
  ∀ x : U,
    ∃ (V : BasisOpen B) (hVU : V.1 ≤ U) (_ : x.1 ∈ V.1) (sV : G.presheaf.obj (op V)),
      ∀ y : V.1,
        BasisSiteSheaf.stalkComparison G y.1 (t ⟨y.1, hVU y.2⟩) =
          G.extend.presheaf.germ V.1 y.1 y.2
            (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)

/-- Helper for Lemma 6.30.12: after reapplying `stalkComparison`, the stalk family extracted from a
global section recovers the original germ of that section. -/
private theorem stalkComparison_extendSectionToBasisStalkFamily
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (U : Opens X) (s : G.extend.presheaf.obj (op U)) (x : U) :
    BasisSiteSheaf.stalkComparison G x.1 (extendSectionToBasisStalkFamily G U s x) =
      G.extend.presheaf.germ U x.1 x.2 s := by
  -- This is the inverse-after-forward cancellation for the stalk comparison isomorphism.
  simp [extendSectionToBasisStalkFamily]

/-- Helper for Lemma 6.30.12: two sections of the additive extension are equal once their induced
basis-stalk families agree pointwise. -/
private theorem extend_sections_ext_by_basis_stalk_family
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB) {U : Opens X}
    {s t : G.extend.presheaf.obj (op U)}
    (hst : extendSectionToBasisStalkFamily G U s = extendSectionToBasisStalkFamily G U t) :
    s = t := by
  -- Compare germs pointwise after transporting back to ordinary stalks via `stalkComparison`.
  apply TopCat.Presheaf.section_ext G.extend U s t
  intro x hx
  have hpoint := congrFun hst ⟨x, hx⟩
  simpa [extendSectionToBasisStalkFamily] using
    congrArg (BasisSiteSheaf.stalkComparison G x) hpoint

/-- Helper for Lemma 6.30.12: the arbitrary-open basis-stalk-family map is injective. -/
public theorem extendSectionToBasisStalkFamily_injective
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB) (U : Opens X) :
    Function.Injective (extendSectionToBasisStalkFamily G U) := by
  intro s t hst
  exact extend_sections_ext_by_basis_stalk_family G hst

/-- Helper for Lemma 6.30.12: every actual section of `G.extend` yields a locally representable
basis-stalk family by restricting to a basis neighborhood and then pulling back along the
comparison isomorphism on that basis open. -/
private theorem extendSectionToBasisStalkFamily_isLocallyRepresentableByBasis
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (U : Opens X) (s : G.extend.presheaf.obj (op U)) :
    IsLocallyRepresentableByBasis G U (extendSectionToBasisStalkFamily G U s) := by
  intro x
  -- Choose a basis neighborhood inside `U`, then use the inverse basis comparison there.
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ :=
    hB.exists_subset_of_mem_open x.2 U.2
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U := homOfLE hVU
  let sV : G.presheaf.obj (op Vb) :=
    BasisSiteSheaf.restrictExtendComponentInv G (op Vb)
      (G.extend.presheaf.map iVU.op s)
  refine ⟨Vb, hVU, hxV, sV, ?_⟩
  intro y
  -- On this basis neighborhood, the restricted extension section has the same germs as `s`.
  have hsV :
      BasisSiteSheaf.restrictExtendComponentHom G (op Vb) sV =
        G.extend.presheaf.map iVU.op s := by
    dsimp [sV]
    simpa using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id G (op Vb))
        (G.extend.presheaf.map iVU.op s)
  calc
    BasisSiteSheaf.stalkComparison G y.1
        (extendSectionToBasisStalkFamily G U s ⟨y.1, hVU y.2⟩) =
      G.extend.presheaf.germ U y.1 (hVU y.2) s := by
        simpa using
          stalkComparison_extendSectionToBasisStalkFamily G U s ⟨y.1, hVU y.2⟩
    _ = G.extend.presheaf.germ V y.1 y.2 (G.extend.presheaf.map iVU.op s) := by
        symm
        simpa [iVU] using G.extend.presheaf.germ_res_apply iVU y.1 y.2 s
    _ = G.extend.presheaf.germ V y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G (op Vb) sV) := by
        rw [hsV]

/-- Helper for Lemma 6.30.12: a locally representable basis-stalk family on an arbitrary open
glues to a unique section of the extension sheaf. -/
public theorem existsUnique_section_of_locally_representable_basis_stalk_family
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (U : Opens X) (t : ∀ x : U, G.stalk x.1)
    (ht : IsLocallyRepresentableByBasis G U t) :
    ∃! s : G.extend.presheaf.obj (op U), extendSectionToBasisStalkFamily G U s = t := by
  classical
  choose V hVU hxV sV hsV using ht
  let W : U → Opens X := fun x ↦ (V x).1
  let iWU : ∀ x : U, W x ⟶ U := fun x ↦ homOfLE (hVU x)
  let sf : ∀ x : U, G.extend.presheaf.obj (op (W x)) := fun x ↦
    BasisSiteSheaf.restrictExtendComponentHom G (op (V x)) (sV x)
  have hcover : U ≤ iSup W := by
    intro x hxU
    exact (le_iSup W ⟨x, hxU⟩) (hxV ⟨x, hxU⟩)
  have hcompat : TopCat.Presheaf.IsCompatible G.extend.presheaf W sf := by
    intro x y
    -- Equality on overlaps is checked on germs, where both local sections realize the same family.
    apply TopCat.Presheaf.section_ext G.extend (W x ⊓ W y)
    intro z hz
    have hzWx : z ∈ W x := (inf_le_left : W x ⊓ W y ≤ W x) hz
    have hzWy : z ∈ W y := (inf_le_right : W x ⊓ W y ≤ W y) hz
    have hxy :
        (⟨z, hVU x hzWx⟩ : U) = ⟨z, hVU y hzWy⟩ := Subtype.ext rfl
    calc
      G.extend.presheaf.germ (W x ⊓ W y) z hz
          (G.extend.presheaf.map (Opens.infLELeft (W x) (W y)).op (sf x)) =
        G.extend.presheaf.germ (W x) z hzWx (sf x) := by
          simpa using
            G.extend.presheaf.germ_res_apply (Opens.infLELeft (W x) (W y)) z hz (sf x)
      _ = BasisSiteSheaf.stalkComparison G z (t ⟨z, hVU x hzWx⟩) := by
          symm
          exact hsV x ⟨z, hzWx⟩
      _ = BasisSiteSheaf.stalkComparison G z (t ⟨z, hVU y hzWy⟩) := by
          cases hxy
          rfl
      _ = G.extend.presheaf.germ (W y) z hzWy (sf y) := by
          exact hsV y ⟨z, hzWy⟩
      _ = G.extend.presheaf.germ (W x ⊓ W y) z hz
          (G.extend.presheaf.map (Opens.infLERight (W x) (W y)).op (sf y)) := by
          symm
          simpa using
            G.extend.presheaf.germ_res_apply (Opens.infLERight (W x) (W y)) z hz (sf y)
  obtain ⟨s, hs, hs_unique⟩ := G.extend.existsUnique_gluing' W U iWU hcover sf hcompat
  have hs_eq : extendSectionToBasisStalkFamily G U s = t := by
    funext x
    -- The glued section has the prescribed germ on the chosen basis neighborhood around `x`.
    have hcompare :
        BasisSiteSheaf.stalkComparison G x.1 (t x) =
          G.extend.presheaf.germ U x.1 x.2 s := by
      calc
        BasisSiteSheaf.stalkComparison G x.1 (t x) =
            G.extend.presheaf.germ (W x) x.1 (hxV x) (sf x) := by
              simpa [W, sf, iWU] using hsV x ⟨x.1, hxV x⟩
        _ = G.extend.presheaf.germ (W x) x.1 (hxV x)
              (G.extend.presheaf.map (iWU x).op s) := by
              rw [← hs x]
        _ = G.extend.presheaf.germ U x.1 x.2 s := by
              simpa [W, iWU] using
                G.extend.presheaf.germ_res_apply (iWU x) x.1 (hxV x) s
    change inv (BasisSiteSheaf.stalkComparison G x.1)
        (G.extend.presheaf.germ U x.1 x.2 s) = t x
    rw [← hcompare]
    simp
  refine ⟨s, hs_eq, ?_⟩
  · intro s' hs'
    exact extendSectionToBasisStalkFamily_injective G U (by rw [hs', hs_eq])

/-- Helper for Lemma 6.30.12: reconstructing the basis-stalk family coming from a basis section
returns the canonical extension section on that basis open. -/
private theorem section_of_locally_representable_basis_stalk_family_eq_restrict_extend
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (V : BasisOpen B) (sV : G.presheaf.obj (op V)) :
    let t := extendSectionToBasisStalkFamily G V.1
      (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)
    ∃! s : G.extend.presheaf.obj (op V.1), extendSectionToBasisStalkFamily G V.1 s = t := by
  let t := extendSectionToBasisStalkFamily G V.1
    (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)
  have ht :
      IsLocallyRepresentableByBasis G V.1 t :=
    extendSectionToBasisStalkFamily_isLocallyRepresentableByBasis G V.1
      (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)
  simpa [t] using
    existsUnique_section_of_locally_representable_basis_stalk_family G V.1 t ht

/-- Helper for Lemma 6.30.12: a basis-open witness for local representability stays valid after
restricting the witnessing section to a smaller basis open. -/
private theorem restrict_local_representability_witness
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    {U : Opens X} {t : ∀ x : U, G.stalk x.1}
    {V W : BasisOpen B}
    (hVU : V.1 ≤ U) (hWV : W.1 ≤ V.1)
    (sV : G.presheaf.obj (op V))
    (hsV : ∀ y : V.1,
      BasisSiteSheaf.stalkComparison G y.1 (t ⟨y.1, hVU y.2⟩) =
        G.extend.presheaf.germ V.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)) :
    ∀ y : W.1,
      BasisSiteSheaf.stalkComparison G y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        G.extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G (op W)
            (G.presheaf.map
              ((ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)).op) sV)) := by
  intro y
  let iWV : W ⟶ V :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)
  have hnat :=
    CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtendHom_naturality G (i := iWV.op)) sV
  -- Naturality identifies the restricted extension section with the extension of the restricted
  -- basis section on the smaller basis open.
  calc
    BasisSiteSheaf.stalkComparison G y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        G.extend.presheaf.germ V.1 y.1 (hWV y.2)
          (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV) := by
          simpa using hsV ⟨y.1, hWV y.2⟩
    _ = G.extend.presheaf.germ W.1 y.1 y.2
          (G.extend.presheaf.map iWV.hom.op
            (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)) := by
          symm
          simpa [iWV] using
            G.extend.presheaf.germ_res_apply iWV.hom y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom G (op V) sV)
    _ = G.extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G (op W)
            (G.presheaf.map iWV.op sV)) := by
          simpa [iWV] using congrArg
            (G.extend.presheaf.germ W.1 y.1 y.2) hnat.symm

/-- Helper for Lemma 6.30.12: basis neighborhoods containing a fixed point form a filtered diagram,
so stalk modules can be constructed as filtered colimits over basis neighborhoods. -/
public instance basisOpenNhds_isFiltered (x : X) :
    IsFiltered ((BasisOpenNhds B x)ᵒᵖ) := by
  refine { toIsFilteredOrEmpty := ?_, nonempty := ?_ }
  · refine
      { cocone_objs := ?_
        cocone_maps := ?_ }
    · intro U V
      -- Refine the two basis neighborhoods to a common basis neighborhood inside their
      -- intersection.
      obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, hWUV⟩ := hB.exists_subset_of_mem_open
        (show x ∈ (U.unop.1.1 ⊓ V.unop.1.1 : Opens X) from ⟨U.unop.2, V.unop.2⟩)
        (U.unop.1.1 ⊓ V.unop.1.1).2
      refine ⟨op ⟨⟨W, hWB⟩, hxW⟩, ?_, ?_, trivial⟩
      · exact Quiver.Hom.op <|
          show (⟨⟨W, hWB⟩, hxW⟩ : BasisOpenNhds B x) ⟶ U.unop from
            ObjectProperty.homMk <| ObjectProperty.homMk <|
              homOfLE (show W ≤ U.unop.1.1 from le_trans hWUV inf_le_left)
      · exact Quiver.Hom.op <|
          show (⟨⟨W, hWB⟩, hxW⟩ : BasisOpenNhds B x) ⟶ V.unop from
            ObjectProperty.homMk <| ObjectProperty.homMk <|
              homOfLE (show W ≤ V.unop.1.1 from le_trans hWUV inf_le_right)
    · intro Y Z f g
      exact ⟨Z, 𝟙 _, by subsingleton⟩
  · -- A basis neighborhood exists by refining the top open around `x`.
    obtain ⟨_, ⟨W, hWB, rfl⟩, hxW, _⟩ := hB.exists_subset_of_mem_open
      (show x ∈ (⊤ : Opens X) by simp) (⊤ : Opens X).2
    exact ⟨op ⟨⟨W, hWB⟩, hxW⟩⟩

/-- Helper for Lemma 6.30.12: the basis stalk of the underlying additive sheaf carries the
canonical module structure over the basis stalk of the ring sheaf, obtained by taking the filtered
colimit of the module structures on basis neighborhoods. -/
public noncomputable instance basis_stalk_module
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) (x : X) :
    Module (𝒪.stalk x) ((basisModuleAddSheaf 𝒪 ℱ).stalk x) := by
  letI : IsFiltered ((BasisOpenNhds B x)ᵒᵖ) := basisOpenNhds_isFiltered (B := B) (hB := hB) x
  letI (i : (BasisOpenNhds B x)ᵒᵖ) :
      Module ((𝒪.stalkDiagram x).obj i) (((basisModuleAddSheaf 𝒪 ℱ).stalkDiagram x).obj i) := by
    -- Each basis neighborhood carries the original module structure from `ℱ`.
    change Module (𝒪.1.obj (op (unop i).obj)) (ℱ.val.obj (op (unop i).obj))
    infer_instance
  -- The basis stalk is the filtered colimit of the module fibers on basis neighborhoods.
  exact Limits.IsColimit.module (𝒪.stalkDiagram x) ((basisModuleAddSheaf 𝒪 ℱ).stalkDiagram x)
    (fun {i j} f r m ↦ by
      -- On each basis neighborhood, semilinearity is exactly the original presheaf module axiom.
      change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r • m) =
        (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r •
          (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m
      exact ℱ.val.map_smul f.unop.hom.op r m)
    (Limits.colimit.isColimit _) (Limits.colimit.isColimit _)

/-- Helper for Lemma 6.30.12: an arbitrary-open section of the extended ring sheaf determines a
family of basis stalk elements by transporting its germs back along the canonical stalk
comparison. -/
public abbrev extendRingSectionToBasisStalkFamily
    (𝒪 : BasisRingSheaf) (U : Opens X) :
    𝒪.extend.presheaf.obj (op U) → ∀ x : U, 𝒪.stalk x.1 :=
  fun r x ↦
    inv (BasisSiteSheaf.stalkComparison 𝒪 x.1) (𝒪.extend.presheaf.germ U x.1 x.2 r)

/-- Helper for Lemma 6.30.12: reapplying the stalk comparison to the extracted ring stalk family
recovers the original germ. -/
private theorem stalkComparison_extendRingSectionToBasisStalkFamily
    (𝒪 : BasisRingSheaf)
    (U : Opens X) (r : 𝒪.extend.presheaf.obj (op U)) (x : U) :
    BasisSiteSheaf.stalkComparison 𝒪 x.1 (extendRingSectionToBasisStalkFamily 𝒪 U r x) =
      𝒪.extend.presheaf.germ U x.1 x.2 r := by
  -- This is the inverse-after-forward cancellation for the ring stalk comparison isomorphism.
  simp [extendRingSectionToBasisStalkFamily]

/-- Helper for Lemma 6.30.12: the stalk comparison sends the basis-open representative of a
section to the corresponding germ of its extension on that basis neighborhood. -/
private theorem stalkComparison_basis_open_eq_germ
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (W : BasisOpen B) (y : W.1) (sW : G.presheaf.obj (op W)) :
    BasisSiteSheaf.stalkComparison G y.1
      (colimit.ι (G.stalkDiagram y.1) (op ⟨W, y.2⟩) sW) =
        G.extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G (op W) sW) := by
  letI : Functor.Final (basisOpenNhdsToOpenNhds B y.1).op :=
    basisOpenNhdsToOpenNhds_final hB y.1
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  have h₁ :
      colimit.ι (G.stalkDiagram y.1) j ≫
          (HasColimit.isoOfNatIso (G.stalkDiagramIso y.1)).hom ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ G.extend.presheaf)).hom =
        (G.stalkDiagramIso y.1).hom.app j ≫
          colimit.ι (G.extendStalkDiagram y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ G.extend.presheaf)).hom := by
    -- First normalize the comparison coming from the diagram isomorphism.
    simpa [Category.assoc] using HasColimit.isoOfNatIso_ι_hom (G.stalkDiagramIso y.1) j
  have h₂base := Functor.Final.ι_colimitIso_hom (basisOpenNhdsToOpenNhds B y.1).op
    ((OpenNhds.inclusion y.1).op ⋙ G.extend.presheaf) j
  have h₂ :
      (G.stalkDiagramIso y.1).hom.app j ≫
          colimit.ι (G.extendStalkDiagram y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ G.extend.presheaf)).hom =
        (G.stalkDiagramIso y.1).hom.app j ≫ G.extend.presheaf.germ W.1 y.1 y.2 := by
    -- Then pass from the basis-neighborhood colimit to the ordinary germ on `W`.
    simpa [j, BasisSiteSheaf.extendStalkDiagram, Category.assoc] using
      congrArg (fun k ↦ (G.stalkDiagramIso y.1).hom.app j ≫ k) h₂base
  have h₃ :
      (G.stalkDiagramIso y.1).hom.app j ≫ G.extend.presheaf.germ W.1 y.1 y.2 =
        G.restrictExtendComponentHom (op W) ≫ G.extend.presheaf.germ W.1 y.1 y.2 := by
    -- On the chosen basis neighborhood, the diagram comparison is literally the restriction map.
    simp [j, BasisSiteSheaf.stalkDiagramIso, BasisSiteSheaf.restrictExtendComponentHom]
  exact CategoryTheory.congr_fun (h₁.trans (h₂.trans h₃)) sW

/-- Helper for Lemma 6.30.12: on a basis open, the extracted module stalk family is exactly the
stalk class of the original basis section. -/
private theorem extendSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (W : BasisOpen B) (sW : G.presheaf.obj (op W)) (y : W.1) :
    extendSectionToBasisStalkFamily G W.1
        (BasisSiteSheaf.restrictExtendComponentHom G (op W) sW) y =
      colimit.ι (G.stalkDiagram y.1) (op ⟨W, y.2⟩) sW := by
  -- Both sides become the same germ after applying the stalk comparison isomorphism.
  simpa [extendSectionToBasisStalkFamily] using
    (congrArg (inv (BasisSiteSheaf.stalkComparison G y.1))
      (stalkComparison_basis_open_eq_germ G W y sW)).symm

/-- Helper for Lemma 6.30.12: on a basis open, the extracted ring stalk family is exactly the
stalk class of the original basis ring section. -/
private theorem extendRingSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι
    (𝒪 : BasisRingSheaf)
    (W : BasisOpen B) (rW : 𝒪.presheaf.obj (op W)) (y : W.1) :
    extendRingSectionToBasisStalkFamily 𝒪 W.1
        (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y =
      colimit.ι (𝒪.stalkDiagram y.1) (op ⟨W, y.2⟩) rW := by
  letI : Functor.Final (basisOpenNhdsToOpenNhds B y.1).op :=
    basisOpenNhdsToOpenNhds_final hB y.1
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  have h₁ :
      colimit.ι (𝒪.stalkDiagram y.1) j ≫
          (HasColimit.isoOfNatIso (𝒪.stalkDiagramIso y.1)).hom ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ 𝒪.extend.presheaf)).hom =
        (𝒪.stalkDiagramIso y.1).hom.app j ≫
          colimit.ι (𝒪.extendStalkDiagram y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ 𝒪.extend.presheaf)).hom := by
    -- Normalize the basis-stalk comparison exactly as in the additive case.
    simpa [Category.assoc] using HasColimit.isoOfNatIso_ι_hom (𝒪.stalkDiagramIso y.1) j
  have h₂base := Functor.Final.ι_colimitIso_hom (basisOpenNhdsToOpenNhds B y.1).op
    ((OpenNhds.inclusion y.1).op ⋙ 𝒪.extend.presheaf) j
  have h₂ :
      (𝒪.stalkDiagramIso y.1).hom.app j ≫
          colimit.ι (𝒪.extendStalkDiagram y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ 𝒪.extend.presheaf)).hom =
        (𝒪.stalkDiagramIso y.1).hom.app j ≫ 𝒪.extend.presheaf.germ W.1 y.1 y.2 := by
    -- Then pass from the basis-neighborhood colimit to the usual germ on `W`.
    simpa [j, BasisSiteSheaf.extendStalkDiagram, Category.assoc] using
      congrArg (fun k ↦ (𝒪.stalkDiagramIso y.1).hom.app j ≫ k) h₂base
  have h₃ :
      (𝒪.stalkDiagramIso y.1).hom.app j ≫ 𝒪.extend.presheaf.germ W.1 y.1 y.2 =
        𝒪.restrictExtendComponentHom (op W) ≫ 𝒪.extend.presheaf.germ W.1 y.1 y.2 := by
    -- On the chosen basis neighborhood, the diagram comparison is the restriction map.
    simp [j, BasisSiteSheaf.stalkDiagramIso, BasisSiteSheaf.restrictExtendComponentHom]
  have hcompare :
      BasisSiteSheaf.stalkComparison 𝒪 y.1
        (colimit.ι (𝒪.stalkDiagram y.1) j rW) =
          𝒪.extend.presheaf.germ W.1 y.1 y.2
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) := by
    exact CategoryTheory.congr_fun (h₁.trans (h₂.trans h₃)) rW
  -- Apply the inverse stalk comparison to the normalized germ equality.
  simpa [j, extendRingSectionToBasisStalkFamily] using
    (congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 y.1)) hcompare).symm

/-- Helper for Lemma 6.30.12: every actual section of `𝒪.extend` admits a basis-open local ring
witness describing its extracted ring stalk family. -/
private theorem exists_basis_ring_witness_of_extend_section
    (𝒪 : BasisRingSheaf)
    (U : Opens X) (r : 𝒪.extend.presheaf.obj (op U)) (x : U) :
    ∃ (V : BasisOpen B) (hVU : V.1 ≤ U) (_ : x.1 ∈ V.1) (rV : 𝒪.presheaf.obj (op V)),
      ∀ y : V.1,
        BasisSiteSheaf.stalkComparison 𝒪 y.1
          (extendRingSectionToBasisStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩) =
            𝒪.extend.presheaf.germ V.1 y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op V) rV) := by
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ :=
    hB.exists_subset_of_mem_open x.2 U.2
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U := homOfLE hVU
  let rV : 𝒪.presheaf.obj (op Vb) :=
    BasisSiteSheaf.restrictExtendComponentInv 𝒪 (op Vb)
      (𝒪.extend.presheaf.map iVU.op r)
  refine ⟨Vb, hVU, hxV, rV, ?_⟩
  intro y
  have hrV :
      BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op Vb) rV =
        𝒪.extend.presheaf.map iVU.op r := by
    dsimp [rV]
    simpa using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id 𝒪 (op Vb))
        (𝒪.extend.presheaf.map iVU.op r)
  -- On the chosen basis neighborhood, the restricted extension section has the same germs as `r`.
  calc
    BasisSiteSheaf.stalkComparison 𝒪 y.1
        (extendRingSectionToBasisStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩) =
      𝒪.extend.presheaf.germ U y.1 (hVU y.2) r := by
        simpa using
          stalkComparison_extendRingSectionToBasisStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩
    _ = 𝒪.extend.presheaf.germ V y.1 y.2 (𝒪.extend.presheaf.map iVU.op r) := by
        symm
        simpa [iVU] using 𝒪.extend.presheaf.germ_res_apply iVU y.1 y.2 r
    _ = 𝒪.extend.presheaf.germ V y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op Vb) rV) := by
        rw [hrV]

/-- Helper for Lemma 6.30.12: on a common basis open, the pointwise product of the extracted ring
and module stalk families is represented by the basis section `rW • mW`. -/
private theorem basis_open_smul_witness
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪)
    (W : BasisOpen B) (rW : 𝒪.presheaf.obj (op W))
    (mW : ℱ.val.obj (op W))
    (y : W.1) :
    BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1
        (extendRingSectionToBasisStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (basisModuleAddSheaf 𝒪 ℱ) (op W) mW) y) =
      (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.germ W.1 y.1 y.2
        (BasisSiteSheaf.restrictExtendComponentHom (basisModuleAddSheaf 𝒪 ℱ)
          (op W) (rW • mW)) := by
  letI : IsFiltered ((BasisOpenNhds B y.1)ᵒᵖ) := basisOpenNhds_isFiltered (B := B) (hB := hB) y.1
  letI (i : (BasisOpenNhds B y.1)ᵒᵖ) :
      Module ((𝒪.stalkDiagram y.1).obj i)
        (((basisModuleAddSheaf 𝒪 ℱ).stalkDiagram y.1).obj i) := by
    change Module (𝒪.1.obj (op (unop i).obj))
      (ℱ.val.obj (op (unop i).obj))
    infer_instance
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  -- Replace both extracted families by the corresponding colimit generators on `W`.
  calc
    BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1
        (extendRingSectionToBasisStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (basisModuleAddSheaf 𝒪 ℱ) (op W) mW) y) =
      BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1
        (colimit.ι ((basisModuleAddSheaf 𝒪 ℱ).stalkDiagram y.1) j (rW • mW)) := by
          rw [extendRingSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι 𝒪 W rW y]
          rw [extendSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι
            (basisModuleAddSheaf 𝒪 ℱ) W mW y]
          -- The filtered-colimit module structure is generated by the literal basis-open formula.
          simpa [j] using congrArg
            (BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1)
            ((Limits.IsColimit.ι_smul (𝒪.stalkDiagram y.1)
              ((basisModuleAddSheaf 𝒪 ℱ).stalkDiagram y.1)
              (fun {i j} f r m ↦ by
                change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r • m) =
                  (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r •
                    (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m
                exact ℱ.val.map_smul f.unop.hom.op r m)
              (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) j rW mW).symm)
    _ = (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom (basisModuleAddSheaf 𝒪 ℱ)
            (op W) (rW • mW)) := by
          simpa [j] using
            stalkComparison_basis_open_eq_germ (basisModuleAddSheaf 𝒪 ℱ) W y (rW • mW)

/-- Helper for Lemma 6.30.12: restricting a ring witness to a smaller basis open preserves the
same local representation statement. -/
private theorem restrict_local_ring_witness
    (𝒪 : BasisRingSheaf)
    {U : Opens X} {t : ∀ x : U, 𝒪.stalk x.1}
    {V W : BasisOpen B}
    (hVU : V.1 ≤ U) (hWV : W.1 ≤ V.1)
    (rV : 𝒪.presheaf.obj (op V))
    (hrV : ∀ y : V.1,
      BasisSiteSheaf.stalkComparison 𝒪 y.1 (t ⟨y.1, hVU y.2⟩) =
        𝒪.extend.presheaf.germ V.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op V) rV)) :
    ∀ y : W.1,
      BasisSiteSheaf.stalkComparison 𝒪 y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        𝒪.extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W)
            (𝒪.presheaf.map
              ((ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)).op) rV)) := by
  intro y
  let iWV : W ⟶ V :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)
  have hnat :=
    CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtendHom_naturality 𝒪 (i := iWV.op)) rV
  -- Naturality identifies the restricted extension section with the extension of the restricted
  -- ring section on the smaller basis open.
  calc
    BasisSiteSheaf.stalkComparison 𝒪 y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        𝒪.extend.presheaf.germ V.1 y.1 (hWV y.2)
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op V) rV) := by
          simpa using hrV ⟨y.1, hWV y.2⟩
    _ = 𝒪.extend.presheaf.germ W.1 y.1 y.2
          (𝒪.extend.presheaf.map iWV.hom.op
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op V) rV)) := by
          symm
          simpa [iWV] using
            𝒪.extend.presheaf.germ_res_apply iWV.hom y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op V) rV)
    _ = 𝒪.extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W)
            (𝒪.presheaf.map iWV.op rV)) := by
          simpa [iWV] using congrArg
            (𝒪.extend.presheaf.germ W.1 y.1 y.2) hnat.symm

/-- Helper for Lemma 6.30.12: the pointwise product of the ring and module stalk families coming
from actual extension sections is again locally representable on a common basis refinement. -/
public theorem pointwise_smul_of_extend_sections_isLocallyRepresentableByBasis
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : 𝒪.extend.presheaf.obj (op U))
    (m : (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U)) :
    IsLocallyRepresentableByBasis (basisModuleAddSheaf 𝒪 ℱ) U
      (fun x ↦ extendRingSectionToBasisStalkFamily 𝒪 U r x •
        extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m x) := by
  intro x
  obtain ⟨Vr, hVrU, hxVr, rVr, hrVr⟩ := exists_basis_ring_witness_of_extend_section 𝒪 U r x
  obtain ⟨Vm, hVmU, hxVm, mVm, hmVm⟩ :=
    extendSectionToBasisStalkFamily_isLocallyRepresentableByBasis
      (basisModuleAddSheaf 𝒪 ℱ) U m x
  obtain ⟨_, ⟨W', hWB, rfl⟩, hxW, hWsub⟩ := hB.exists_subset_of_mem_open
    (show x.1 ∈ (Vr.1 ⊓ Vm.1 : Opens X) from ⟨hxVr, hxVm⟩)
    (Vr.1 ⊓ Vm.1).2
  let W : BasisOpen B := ⟨W', hWB⟩
  have hWVr : W.1 ≤ Vr.1 := le_trans hWsub inf_le_left
  have hWVm : W.1 ≤ Vm.1 := le_trans hWsub inf_le_right
  have hWU : W.1 ≤ U := le_trans hWVr hVrU
  let iWVr : W ⟶ Vr :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWVr)
  let iWVm : W ⟶ Vm :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWVm)
  let rW : 𝒪.presheaf.obj (op W) := 𝒪.presheaf.map iWVr.op rVr
  let mW : ℱ.val.obj (op W) := ℱ.val.map iWVm.op mVm
  refine ⟨W, hWU, hxW, rW • mW, ?_⟩
  intro y
  have hrW := restrict_local_ring_witness 𝒪 hVrU hWVr rVr hrVr y
  have hmW := restrict_local_representability_witness
    (basisModuleAddSheaf 𝒪 ℱ) hVmU hWVm mVm hmVm y
  have hrEq :
      extendRingSectionToBasisStalkFamily 𝒪 U r ⟨y.1, hWU y.2⟩ =
        extendRingSectionToBasisStalkFamily 𝒪 W.1
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y := by
    -- The restricted ring witness on `W` represents the same stalk family as the original one.
    simpa [rW, extendRingSectionToBasisStalkFamily] using
      congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 y.1))
        ((hrW.trans
          (stalkComparison_extendRingSectionToBasisStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y).symm))
  have hmEq :
      extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m ⟨y.1, hWU y.2⟩ =
        extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) W.1
          (BasisSiteSheaf.restrictExtendComponentHom (basisModuleAddSheaf 𝒪 ℱ) (op W) mW) y := by
    -- The same argument identifies the module stalk family with the restricted basis witness.
    simpa [mW, extendSectionToBasisStalkFamily] using
      congrArg (inv (BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1))
        ((hmW.trans
          (stalkComparison_extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom (basisModuleAddSheaf 𝒪 ℱ) (op W) mW) y).symm))
  -- On the common basis refinement, both factors come from honest basis sections, so the local
  -- product is represented by their ordinary product section.
  calc
    BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1
        (extendRingSectionToBasisStalkFamily 𝒪 U r ⟨y.1, hWU y.2⟩ •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m
            ⟨y.1, hWU y.2⟩) =
      BasisSiteSheaf.stalkComparison (basisModuleAddSheaf 𝒪 ℱ) y.1
        (extendRingSectionToBasisStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 (op W) rW) y •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (basisModuleAddSheaf 𝒪 ℱ) (op W) mW) y) := by
          rw [hrEq, hmEq]
    _ = (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom (basisModuleAddSheaf 𝒪 ℱ)
            (op W) (rW • mW)) := by
          simpa [rW, mW] using basis_open_smul_witness 𝒪 ℱ W rW mW y

/-- Helper for Lemma 6.30.12: the section reconstructed from the pointwise product family has that
same product family as its extracted basis-stalk family. -/
private theorem extendSectionToBasisStalkFamily_smul_reconstructed
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : 𝒪.extend.presheaf.obj (op U))
    (m : (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U)) :
    let G : BasisSiteSheaf AddCommGrpCat B hB := basisModuleAddSheaf 𝒪 ℱ
    let t : ∀ x : U, G.stalk x.1 := fun x ↦
      extendRingSectionToBasisStalkFamily 𝒪 U r x • extendSectionToBasisStalkFamily G U m x
    let s : G.extend.presheaf.obj (op U) :=
      Classical.choose <|
        existsUnique_section_of_locally_representable_basis_stalk_family G U t
      (pointwise_smul_of_extend_sections_isLocallyRepresentableByBasis 𝒪 ℱ U r m)
    extendSectionToBasisStalkFamily G U s = t := by
  -- The chosen section is exactly the witness returned by the unique reconstruction theorem.
  simpa using
    (Classical.choose_spec
      (existsUnique_section_of_locally_representable_basis_stalk_family
        (basisModuleAddSheaf 𝒪 ℱ) U
        (fun x ↦ extendRingSectionToBasisStalkFamily 𝒪 U r x •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m x)
        (pointwise_smul_of_extend_sections_isLocallyRepresentableByBasis 𝒪 ℱ U r m))).1

/-- Helper for Lemma 6.30.12: the reconstructed pointwise stalk-family product defines the scalar
action on sections of the additive extension over an arbitrary open. -/
public noncomputable def basisModuleSheafExtension_section_smul
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    𝒪.extend.presheaf.obj (op U) →
      (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U) →
      (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U) :=
  fun r m ↦
    Classical.choose <|
      existsUnique_section_of_locally_representable_basis_stalk_family
        (basisModuleAddSheaf 𝒪 ℱ) U
        (fun x ↦ extendRingSectionToBasisStalkFamily 𝒪 U r x •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m x)
        (pointwise_smul_of_extend_sections_isLocallyRepresentableByBasis 𝒪 ℱ U r m)

/-- Helper for Lemma 6.30.12: extracting basis stalks from the reconstructed scalar product
recovers the pointwise stalk-family product used to define it. -/
public theorem basisModuleSheafExtension_section_smul_family
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : 𝒪.extend.presheaf.obj (op U))
    (m : (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U)) :
    extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U
        (basisModuleSheafExtension_section_smul 𝒪 ℱ U r m) =
      fun x ↦
        extendRingSectionToBasisStalkFamily 𝒪 U r x •
          extendSectionToBasisStalkFamily (basisModuleAddSheaf 𝒪 ℱ) U m x := by
  -- The reconstructed section was chosen precisely so that its extracted family is this product.
  simpa [basisModuleSheafExtension_section_smul] using
    extendSectionToBasisStalkFamily_smul_reconstructed 𝒪 ℱ U r m

/-- Helper for Lemma 6.30.12: restricting an extracted basis-stalk family to a smaller open is
computed by the ordinary restriction on germs. -/
private theorem extendSectionToBasisStalkFamily_map
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    {U V : Opens X} (i : V ⟶ U)
    (s : G.extend.presheaf.obj (op U)) (x : V) :
    extendSectionToBasisStalkFamily G V (G.extend.presheaf.map i.op s) x =
      extendSectionToBasisStalkFamily G U s ⟨x.1, i.le x.2⟩ := by
  -- Both families become the same germ after applying the stalk comparison isomorphism.
  simpa [extendSectionToBasisStalkFamily] using
    congrArg (inv (BasisSiteSheaf.stalkComparison G x.1))
      (by simpa using G.extend.presheaf.germ_res_apply i x.1 x.2 s)

/-- Helper for Lemma 6.30.12: the ring-valued extracted stalk family restricts along germs in the
same way. -/
private theorem extendRingSectionToBasisStalkFamily_map
    (𝒪 : BasisRingSheaf)
    {U V : Opens X} (i : V ⟶ U)
    (r : 𝒪.extend.presheaf.obj (op U)) (x : V) :
    extendRingSectionToBasisStalkFamily 𝒪 V (𝒪.extend.presheaf.map i.op r) x =
      extendRingSectionToBasisStalkFamily 𝒪 U r ⟨x.1, i.le x.2⟩ := by
  -- This is the ring-valued analogue of `extendSectionToBasisStalkFamily_map`.
  simpa [extendRingSectionToBasisStalkFamily] using
    congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 x.1))
      (by simpa using 𝒪.extend.presheaf.germ_res_apply i x.1 x.2 r)

/-- Helper for Lemma 6.30.12: pointwise stalk families carry the natural scalar action induced by
the extracted ring stalk family of a section of `𝒪.extend`. -/
public noncomputable instance basisModuleSheafExtension_stalkFamily_module
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    Module (𝒪.extend.presheaf.obj (op U))
      (∀ x : U, (basisModuleAddSheaf 𝒪 ℱ).stalk x.1) where
  smul r t x := extendRingSectionToBasisStalkFamily 𝒪 U r x • t x
  one_smul := by
    intro t
    -- The unit section acts stalkwise by the unit of each stalk module.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U (1 : 𝒪.extend.presheaf.obj (op U)) x • t x =
      t x
    simp [extendRingSectionToBasisStalkFamily]
  mul_smul := by
    intro r s t
    -- Multiplication of sections is computed pointwise on the extracted ring stalk family.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U (r * s) x • t x =
      extendRingSectionToBasisStalkFamily 𝒪 U r x •
        (extendRingSectionToBasisStalkFamily 𝒪 U s x • t x)
    simp [extendRingSectionToBasisStalkFamily, mul_smul]
  smul_zero := by
    intro r
    -- The pointwise action preserves the zero stalk family.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U r x •
        (0 : (basisModuleAddSheaf 𝒪 ℱ).stalk x.1) =
      0
    simp
  smul_add := by
    intro r t₁ t₂
    -- Distributivity is reduced to the module law in each basis stalk.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U r x • (t₁ x + t₂ x) =
      extendRingSectionToBasisStalkFamily 𝒪 U r x • t₁ x +
        extendRingSectionToBasisStalkFamily 𝒪 U r x • t₂ x
    simp [smul_add]
  zero_smul := by
    intro t
    -- The zero section acts trivially on every extracted basis stalk.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U (0 : 𝒪.extend.presheaf.obj (op U)) x • t x =
      0
    simp [extendRingSectionToBasisStalkFamily]
  add_smul := by
    intro r s t
    -- Addition of sections is computed pointwise on the extracted ring stalk family.
    funext x
    change extendRingSectionToBasisStalkFamily 𝒪 U (r + s) x • t x =
      extendRingSectionToBasisStalkFamily 𝒪 U r x • t x +
        extendRingSectionToBasisStalkFamily 𝒪 U s x • t x
    simp [extendRingSectionToBasisStalkFamily, add_smul]

/-- Helper for Lemma 6.30.12: extracting basis stalk families is an additive map on arbitrary-open
sections of the additive extension. -/
public def extendSectionToBasisStalkFamily_addMonoidHom
    (G : BasisSiteSheaf AddCommGrpCat.{u} B hB)
    (U : Opens X) :
    G.extend.presheaf.obj (op U) →+ ∀ x : U, G.stalk x.1 where
  toFun := extendSectionToBasisStalkFamily G U
  map_zero' := by
    -- Zero sections have zero germs, so the extracted family is pointwise zero.
    funext x
    simp [extendSectionToBasisStalkFamily]
  map_add' s t := by
    -- Additivity is checked pointwise on germs and then transported back to basis stalks.
    funext x
    simp [extendSectionToBasisStalkFamily]

/-- Helper for Lemma 6.30.12: the reconstructed pointwise product equips the extension section
space on an open with a scalar action. -/
public noncomputable instance basisModuleSheafExtension_section_smul_inst
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    SMul (𝒪.extend.presheaf.obj (op U))
      ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U)) where
  smul := basisModuleSheafExtension_section_smul 𝒪 ℱ U

/-- Helper for Lemma 6.30.12: the reconstructed scalar action makes sections of the additive
extension over each open into a module over sections of `𝒪.extend`. -/
public noncomputable instance basisModuleSheafExtension_section_module
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    Module (𝒪.extend.presheaf.obj (op U))
      ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj (op U)) :=
  Function.Injective.module (𝒪.extend.presheaf.obj (op U))
    (extendSectionToBasisStalkFamily_addMonoidHom (basisModuleAddSheaf 𝒪 ℱ) U)
    (extendSectionToBasisStalkFamily_injective (basisModuleAddSheaf 𝒪 ℱ) U)
    (basisModuleSheafExtension_section_smul_family 𝒪 ℱ U)

/-- Helper for Lemma 6.30.12: the objectwise module structure is available uniformly for the
opposite-indexed presheaf objects used by `PresheafOfModules.ofPresheaf`. -/
public noncomputable instance basisModuleSheafExtension_section_module_op
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    (U : (Opens X)ᵒᵖ) :
    Module (𝒪.extend.presheaf.obj U)
      ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj U) := by
  -- This is just the objectwise module structure on the underlying open `U.unop`.
  simpa using
    (basisModuleSheafExtension_section_module (𝒪 := 𝒪) (ℱ := ℱ) (U := U.unop))

/-- Helper for Lemma 6.30.12: restriction maps of the additive extension are semilinear for the
reconstructed section-level scalar action. -/
private theorem basisModuleSheafExtension_presheaf_map_smul
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (r : 𝒪.extend.presheaf.obj U)
    (m : (basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj U) :
    ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.map i) (r • m) =
      ((𝒪.extend.presheaf.map i) r) •
        (((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.map i) m) := by
  let G : BasisSiteSheaf AddCommGrpCat B hB := basisModuleAddSheaf 𝒪 ℱ
  -- Compare the extracted basis-stalk families after restricting from `V.unop` to `U.unop`.
  apply extend_sections_ext_by_basis_stalk_family (G := G)
  funext x
  -- Restrict the left-hand section, expand both scalar products, and compare the resulting
  -- pointwise stalk families.
  calc
    extendSectionToBasisStalkFamily G V.unop (G.extend.presheaf.map i (r • m)) x =
      extendSectionToBasisStalkFamily G U.unop (r • m) ⟨x.1, i.unop.le x.2⟩ := by
        simpa [G] using extendSectionToBasisStalkFamily_map (G := G) i.unop (r • m) x
    _ = extendRingSectionToBasisStalkFamily 𝒪 U.unop r ⟨x.1, i.unop.le x.2⟩ •
          extendSectionToBasisStalkFamily G U.unop m ⟨x.1, i.unop.le x.2⟩ := by
        simpa [G] using congrFun (basisModuleSheafExtension_section_smul_family 𝒪 ℱ U.unop r m) ⟨x.1, i.unop.le x.2⟩
    _ = extendRingSectionToBasisStalkFamily 𝒪 V.unop (𝒪.extend.presheaf.map i r) x •
          extendSectionToBasisStalkFamily G V.unop (G.extend.presheaf.map i m) x := by
        rw [← extendRingSectionToBasisStalkFamily_map (𝒪 := 𝒪) i.unop r x]
        rw [← extendSectionToBasisStalkFamily_map (G := G) i.unop m x]
        have hi : i.unop.op = i := Quiver.Hom.unop_op i
        simpa [hi]
    _ = extendSectionToBasisStalkFamily G V.unop
          (((𝒪.extend.presheaf.map i) r) • ((G.extend.presheaf.map i) m)) x := by
        simpa [G] using
          (congrFun
            (basisModuleSheafExtension_section_smul_family 𝒪 ℱ V.unop
              ((𝒪.extend.presheaf.map i) r) ((G.extend.presheaf.map i) m)) x).symm

public noncomputable def basisModuleSheafExtensionVal
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    PresheafOfModules 𝒪.extend.obj :=
  -- Route correction: define the scalar action on each open by reconstructing the pointwise
  -- stalk family `x ↦ r_x • m_x` from the source-faithful local representability witnesses.
  PresheafOfModules.ofPresheaf
    ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf)
    (by
      intro U V i r m
      exact basisModuleSheafExtension_presheaf_map_smul (𝒪 := 𝒪) (ℱ := ℱ) i r m)

/-- Helper for Lemma 6.30.12: once the source-faithful module structure on the extension presheaf
is constructed, its underlying additive presheaf must satisfy the ordinary sheaf condition. -/
public theorem basisModuleSheafExtensionVal_isSheaf
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (basisModuleSheafExtensionVal 𝒪 ℱ).presheaf := by
  -- The reconstructed module presheaf has exactly the additive extension as underlying presheaf.
  simpa [basisModuleSheafExtensionVal] using
    (BasisSiteSheaf.extend (basisModuleAddSheaf 𝒪 ℱ)).2

/-- Lemma 6.30.12: a sheaf of `𝒪`-modules on the basis site acquires a canonical
`𝒪.extend`-module structure on its extension to `X`. -/
noncomputable def basisModuleSheafExtension
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    SheafOfModules 𝒪.extend where
  val := basisModuleSheafExtensionVal 𝒪 ℱ
  isSheaf := basisModuleSheafExtensionVal_isSheaf 𝒪 ℱ

/-- The underlying additive sheaf of `basisModuleSheafExtension 𝒪 ℱ` is definitionally the
canonical extension of the underlying additive sheaf of `ℱ` from the basis site to `X`. -/
@[simp]
theorem basisModuleSheafExtension_toSheaf
    (𝒪 : BasisRingSheaf)
    (ℱ : SheafOfModules 𝒪) :
    (SheafOfModules.toSheaf 𝒪.extend).obj
        (basisModuleSheafExtension 𝒪 ℱ) =
      BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) := by
  -- Both sheaves have the same underlying additive presheaf, so they are equal by proof
  -- irrelevance in the sheaf predicate.
  apply ObjectProperty.FullSubcategory.ext
  rfl

public instance basisModuleSheafExtension_restrictExtendComponentHom_module
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ) :
    Module (((basisOpenInclusion B).op ⋙ 𝒪.extend.presheaf).obj U)
      (((basisOpenInclusion B).op ⋙
          (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ)).presheaf).obj U) := by
  -- The codomain is the restriction of the extension sheaf, which is the underlying additive
  -- sheaf of `basisModuleSheafExtension 𝒪 ℱ`.
  change Module (𝒪.extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
    ((basisModuleAddSheaf 𝒪 ℱ).extend.presheaf.obj ((basisOpenInclusion B).op.obj U))
  infer_instance

/-- On a basis open, the canonical comparison map from `ℱ` to the restriction of
`basisModuleSheafExtension 𝒪 ℱ` is semilinear for the comparison map from `𝒪` to
`𝒪.extend`. This is the basis-open compatibility clause in Stacks Lemma 6.30.12. -/
theorem basisModuleSheafExtension_restrictExtendComponentHom_smul
    (𝒪 : BasisRingSheaf) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ)
    (r : 𝒪.presheaf.obj U) (m : ℱ.val.obj U) :
    BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U (r • m) =
      𝒪.restrictExtendComponentHom U r •
        BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) U m := by
  -- Route correction: once the reconstruction map from locally representable basis-stalk families
  -- is available, this equality should be proved by comparing the pointwise basis-stalk families
  -- on `U` and then applying `extend_sections_ext_by_basis_stalk_family`.
  let G : BasisSiteSheaf AddCommGrpCat B hB := basisModuleAddSheaf 𝒪 ℱ
  apply extend_sections_ext_by_basis_stalk_family (G := G)
  funext y
  letI : IsFiltered ((BasisOpenNhds B y.1)ᵒᵖ) := basisOpenNhds_isFiltered (B := B) (hB := hB) y.1
  letI (i : (BasisOpenNhds B y.1)ᵒᵖ) :
      Module ((𝒪.stalkDiagram y.1).obj i)
        ((G.stalkDiagram y.1).obj i) := by
    change Module (𝒪.1.obj (op (unop i).obj))
      (ℱ.val.obj (op (unop i).obj))
    infer_instance
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨U.unop, y.2⟩
  -- On the basis open itself, the reconstructed scalar action is the original module action.
  calc
    extendSectionToBasisStalkFamily G ((basisOpenInclusion B).obj U.unop)
        (BasisSiteSheaf.restrictExtendComponentHom G U (r • m)) y =
      colimit.ι (G.stalkDiagram y.1) j (r • m) := by
        simpa [G, j] using
          extendSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι (G := G) U.unop (r • m) y
    _ = colimit.ι (𝒪.stalkDiagram y.1) j r • colimit.ι (G.stalkDiagram y.1) j m := by
      simpa [G, j] using
        Limits.IsColimit.ι_smul (𝒪.stalkDiagram y.1)
          (G.stalkDiagram y.1)
          (fun {i j} f r' m' ↦ by
            change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r' • m') =
              (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r' •
                (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m'
            exact ℱ.val.map_smul f.unop.hom.op r' m')
          (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) j r m
    _ = extendRingSectionToBasisStalkFamily 𝒪 ((basisOpenInclusion B).obj U.unop)
          (𝒪.restrictExtendComponentHom U r) y •
        extendSectionToBasisStalkFamily G ((basisOpenInclusion B).obj U.unop)
          (BasisSiteSheaf.restrictExtendComponentHom G U m) y := by
        have hr :
            colimit.ι (𝒪.stalkDiagram y.1) j r =
              extendRingSectionToBasisStalkFamily 𝒪 ((basisOpenInclusion B).obj U.unop)
                (𝒪.restrictExtendComponentHom U r) y := by
          simpa [j] using
            (extendRingSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι
              (𝒪 := 𝒪) U.unop r y).symm
        have hm :
            colimit.ι (G.stalkDiagram y.1) j m =
              extendSectionToBasisStalkFamily G ((basisOpenInclusion B).obj U.unop)
                (BasisSiteSheaf.restrictExtendComponentHom G U m) y := by
          simpa [G, j] using
            (extendSectionToBasisStalkFamily_restrictExtend_eq_colimit_ι
              (G := G) U.unop m y).symm
        rw [hr, hm]
    _ = extendSectionToBasisStalkFamily G ((basisOpenInclusion B).obj U.unop)
          (𝒪.restrictExtendComponentHom U r •
            BasisSiteSheaf.restrictExtendComponentHom G U m) y := by
        simpa [G] using
          (congrFun
            (basisModuleSheafExtension_section_smul_family 𝒪 ℱ ((basisOpenInclusion B).obj U.unop)
              (𝒪.restrictExtendComponentHom U r)
              (BasisSiteSheaf.restrictExtendComponentHom G U m)) y).symm

end

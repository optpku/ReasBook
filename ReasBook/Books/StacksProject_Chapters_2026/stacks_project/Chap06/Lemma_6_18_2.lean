module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_4_3
public import stacks_project.Chap06.Definition_6_8_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopCat.Presheaf
open TopologicalSpace
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable (ℱ : PAb(X))
variable {𝒢 : Ab(X)}

local notation "J" => Opens.grothendieckTopology X

/- Domain-style sampling for Lemma 6.18.2:
- primary domain: sheafification of abelian presheaves and abelian sheaves on a topological space,
  written `PAb(X)` and `Ab(X)`;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.toSheafify`,
  `CategoryTheory.sheafificationAdjunction`,
  `CategoryTheory.sheafComposeNatIso`,
  `CategoryTheory.sheafifyComposeIso`,
  `CompatibleAddCommGroupStructure.toPAb`,
  `TopCat.Presheaf.isSheaf_iff_isSheaf_comp`;
- best owner abstraction: the fixed set-valued sheafification should stay on the canonical owner
  `((ℱ ⋙ forget AddCommGrpCat.{u}).sheafify : X.Sheaf (Type u))`, equivalently
  `(presheafToSheaf J (Type u)).obj (ℱ ⋙ forget AddCommGrpCat.{u})`; the canonical abelian
  sheafification `(presheafToSheaf J AddCommGrpCat.{u}).obj ℱ` is then the bridge/view comparison
  object, related by `sheafifyComposeIso`;
- primitive data: the fixed set-valued sheafification `ℱ^#`, the canonical abelian sheafification,
  and the units `toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})` and `toSheafify J ℱ`;
- derived API: the transported compatible additive structure on `ℱ^#`, the bundled abelian sheaf
  `setSheafificationAb ℱ : Ab(X)`, the bridge isomorphism to the canonical abelian sheafification,
  and the resulting universal property.

Source/core/bridge triage:
- `source-facing`: the actual fixed set-valued sheafification `ℱ^#`, together with its transported
  compatible abelian-group structure;
- `core/canonical`: the sheafification adjunctions in `Type u` and in `AddCommGrpCat.{u}`;
- `bridge/view`: `sheafifyComposeIso`, which compares `ℱ^#` with the underlying set-valued
  sheafification of the canonical abelian sheafification. -/

/- Lemma 6.18.2: the source-facing `ℱ^#` is the actual set-valued sheafification of the
underlying presheaf of `ℱ`, while the canonical `AddCommGrpCat` sheafification provides the
additive structure and universal property through the standard comparison isomorphisms. -/
recall CategoryTheory.sheafificationAdjunction
recall CategoryTheory.sheafComposeNatIso
recall CategoryTheory.sheafifyComposeIso
recall CategoryTheory.sheafComposeIso_hom_fac

/- The owner equivalence for the canonical adjunction `PAb(X) ⇄ Ab(X)`. -/
#check (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv ℱ 𝒢) :
  ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ ⟶ 𝒢) ≃ (ℱ ⟶ 𝒢.obj))

/- The sheaf-level comparison with the canonical abelian sheafification. -/
#check ((sheafComposeNatIso J (forget AddCommGrpCat.{u})
  (sheafificationAdjunction J AddCommGrpCat.{u})
  (sheafificationAdjunction J (Type u))).app ℱ)

namespace SetSheafification

/- Textbook notation for the fixed set sheafification `ℱ^#`, attached directly to the canonical
owner expression `(presheafToSheaf J (Type u)).obj (ℱ ⋙ forget AddCommGrpCat)` rather than to any
local alias. We spell that owner through `Functor.obj` so the notation expands without projection
syntax. Since the ambient space `X` is recoverable from `ℱ : PAb(X)`, the postfix notation is
inference-stable here. -/
set_option quotPrecheck false in
scoped notation:max F "^#" =>
  Functor.obj (presheafToSheaf J (Type _)) (F ⋙ forget AddCommGrpCat)

end SetSheafification

open scoped SetSheafification

/- The source-facing owner `ℱ^#`. -/
#check (ℱ^# : X.Sheaf (Type u))

/- On underlying presheaves, the bridge/view part of Lemma 6.18.2 is the canonical comparison
`sheafifyComposeIso` specialized to abelian presheaves. -/
#check (sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ :
  (ℱ^#).obj ≅ ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙ forget AddCommGrpCat.{u})

public abbrev setSheafificationComponentEquiv (U : (Opens X)ᵒᵖ) :
    ((ℱ^#).obj).obj U ≃
      (((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙ forget AddCommGrpCat.{u}).obj U :=
  Iso.toEquiv ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).app U)

/-- Lemma 6.18.2, source-facing structure: the exact fixed set-valued sheafification `ℱ^#`
carries a compatible sectionwise abelian-group structure, transported from the canonical
`AddCommGrpCat` sheafification along `sheafifyComposeIso`. -/
noncomputable def setSheafificationCompatibleAddCommGroupStructure :
    CompatibleAddCommGroupStructure
      (ℱ^#).obj :=
  { addCommGroup := fun U ↦
      Equiv.addCommGroup (setSheafificationComponentEquiv ℱ U)
    map_add := by
      intro U V i s t
      let eU := setSheafificationComponentEquiv ℱ U
      let eV := setSheafificationComponentEquiv ℱ V
      let _ : AddCommGroup (((ℱ^#).obj).obj U) := Equiv.addCommGroup eU
      let _ : AddCommGroup (((ℱ^#).obj).obj V) := Equiv.addCommGroup eV
      apply eV.injective
      rw [show eV (((ℱ^#).obj).map i (s + t)) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU (s + t)) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i)
                (s + t)]
      rw [Equiv.add_def eU]
      simp only [Equiv.apply_symm_apply]
      rw [Equiv.add_def eV]
      simp only [Equiv.apply_symm_apply]
      rw [show eV (((ℱ^#).obj).map i s) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU s) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) s]
      rw [show eV (((ℱ^#).obj).map i t) =
          ((((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj ⋙
            forget AddCommGrpCat.{u}).map i) (eU t) by
            simpa using
              congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) t]
      exact (((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj.map i).hom.map_add (eU s) (eU t) }

/-- Lemma 6.18.2, source-facing owner: the fixed sheafification `ℱ^#` bundled as a sheaf of
abelian groups on `X`. -/
noncomputable def setSheafificationAb : Ab(X) where
  obj := (setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb
  property := by
    refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2 ?_
    simpa [(setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb_forget] using
      (ℱ^#).property

/-- Forgetting the abelian-group structure on `setSheafificationAb ℱ` recovers the fixed
set-valued sheafification `ℱ^#`. -/
theorem setSheafificationAb_forget :
    (setSheafificationAb ℱ).obj ⋙ forget AddCommGrpCat.{u} = (ℱ^#).obj :=
  (setSheafificationCompatibleAddCommGroupStructure ℱ).toPAb_forget

public noncomputable def setSheafificationAbComponentAddEquiv (U : (Opens X)ᵒᵖ) :
    ((setSheafificationAb ℱ).obj.obj U) ≃+
      ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj.obj U where
  toEquiv := setSheafificationComponentEquiv ℱ U
  map_add' := by
    intro s t
    let e := setSheafificationComponentEquiv ℱ U
    change e (e.symm (e s + e t)) = e s + e t
    exact e.apply_symm_apply (e s + e t)

public noncomputable def setSheafificationAbPresheafIso :
    (setSheafificationAb ℱ).obj ≅ ((presheafToSheaf J AddCommGrpCat.{u}).obj ℱ).obj :=
  NatIso.ofComponents
    (fun U ↦ (setSheafificationAbComponentAddEquiv ℱ U).toAddCommGrpIso)
    (by
      intro U V i
      apply AddCommGrpCat.ext
      intro s
      simpa using congrFun ((sheafifyComposeIso J (forget AddCommGrpCat.{u}) ℱ).hom.naturality i) s)

/-- The bridge/view between the source-facing abelian sheafification `setSheafificationAb ℱ` and
the canonical abelian sheafification `(presheafToSheaf J AddCommGrpCat).obj ℱ`. -/
noncomputable def setSheafificationAbIsoCanonical :
    setSheafificationAb ℱ ≅ (presheafToSheaf J AddCommGrpCat.{u}).obj ℱ where
  hom := ⟨(setSheafificationAbPresheafIso ℱ).hom⟩
  inv := ⟨(setSheafificationAbPresheafIso ℱ).inv⟩
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (setSheafificationAbPresheafIso ℱ).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (setSheafificationAbPresheafIso ℱ).inv_hom_id

/-- The unit `ℱ ⟶ ℱ^#` as a morphism of abelian presheaves for the exact compatible structure on
`ℱ^#`. -/
noncomputable def toSetSheafificationAb :
    ℱ ⟶ (setSheafificationAb ℱ).obj :=
  toSheafify J ℱ ≫ (setSheafificationAbIsoCanonical ℱ).inv.hom

/-- Composing the source-facing unit with the bridge to the canonical abelian sheafification
recovers the canonical adjunction unit `toSheafify J ℱ`. -/
theorem toSetSheafificationAb_comp_setSheafificationAbIsoCanonical_hom :
    toSetSheafificationAb ℱ ≫ (setSheafificationAbIsoCanonical ℱ).hom.hom = toSheafify J ℱ := by
  exact congrArg
    (fun k ↦ toSheafify J ℱ ≫ k.hom)
    (Iso.inv_hom_id (setSheafificationAbIsoCanonical ℱ))

/-- Forgetting the additive structure on `toSetSheafificationAb ℱ` recovers the actual set-valued
sheafification unit `ℱ ⟶ ℱ^#`. -/
theorem toSetSheafificationAb_forget :
    Functor.whiskerRight (toSetSheafificationAb ℱ) (forget AddCommGrpCat.{u}) ≫
      eqToHom (setSheafificationAb_forget ℱ) =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
  convert (sheafComposeIso_inv_fac J (forget AddCommGrpCat.{u}) ℱ) using 1

/-- Lemma 6.18.2, source-facing map statement: the actual set-valued sheafification unit
`ℱ ⟶ ℱ^#` is additive for the exact compatible abelian-group structure on `ℱ^#`. -/
theorem toSheafify_map_add (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U) :
    by
      let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
      exact
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t := by
  let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
  have hforget := toSetSheafificationAb_forget ℱ
  have hmap := ((toSetSheafificationAb ℱ).app U).hom.map_add s t
  have hs :
      ((toSetSheafificationAb ℱ).app U).hom s =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) s
  have ht :
      ((toSetSheafificationAb ℱ).app U).hom t =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) t
  have hst :
      ((toSetSheafificationAb ℱ).app U).hom (s + t) =
        (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hforget) (s + t)
  simpa [hs, ht, hst] using hmap

private theorem setSheafification_hom_ext {γ δ : (ℱ^#).obj ⟶ (ℱ^#).obj}
    (h :
      toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ γ =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ δ) :
    γ = δ := by
  simpa using (sheafify_hom_ext J γ δ (ℱ^#).property h)

/-- Lemma 6.18.2, universal property on the canonical abelian sheafification: every additive
morphism `η : ℱ ⟶ 𝒢.obj` factors uniquely through the adjunction unit `toSheafify J ℱ`. -/
theorem existsUnique_canonicalSetSheafificationLift {ℱ : PAb(X)} {𝒢 : Ab(X)} (η : ℱ ⟶ 𝒢.obj) :
    ∃! γ : (presheafToSheaf J AddCommGrpCat.{u}).obj ℱ ⟶ 𝒢, toSheafify J ℱ ≫ γ.hom = η := by
  let e := (sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv ℱ 𝒢
  refine ⟨e.symm η, ?_, ?_⟩
  · change e (e.symm η) = η
    exact Equiv.apply_symm_apply e η
  · intro γ hγ
    apply e.injective
    have hγη : e γ = η := by
      simpa [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] using hγ
    rw [hγη]
    exact (Equiv.apply_symm_apply e η).symm

/-- Lemma 6.18.2, source-facing universal property: every additive morphism
`η : ℱ ⟶ 𝒢.obj` factors uniquely through `toSetSheafificationAb ℱ`. -/
theorem existsUnique_setSheafificationLift {ℱ : PAb(X)} {𝒢 : Ab(X)} (η : ℱ ⟶ 𝒢.obj) :
    ∃! γ : setSheafificationAb ℱ ⟶ 𝒢, toSetSheafificationAb ℱ ≫ γ.hom = η := by
  obtain ⟨δ, hδ, hδuniq⟩ := existsUnique_canonicalSetSheafificationLift η
  refine ⟨(setSheafificationAbIsoCanonical ℱ).hom ≫ δ, ?_, ?_⟩
  · change toSetSheafificationAb ℱ ≫ (setSheafificationAbIsoCanonical ℱ).hom.hom ≫ δ.hom = η
    rw [← Category.assoc, toSetSheafificationAb_comp_setSheafificationAbIsoCanonical_hom]
    exact hδ
  · intro γ hγ
    have hγ' : toSheafify J ℱ ≫ ((setSheafificationAbIsoCanonical ℱ).inv ≫ γ).hom = η := by
      change toSheafify J ℱ ≫ (setSheafificationAbIsoCanonical ℱ).inv.hom ≫ γ.hom = η
      simpa [toSetSheafificationAb, Category.assoc] using hγ
    have hcomp : (setSheafificationAbIsoCanonical ℱ).inv ≫ γ = δ := hδuniq _ hγ'
    calc
      γ = (setSheafificationAbIsoCanonical ℱ).hom ≫ ((setSheafificationAbIsoCanonical ℱ).inv ≫ γ) := by
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = (setSheafificationAbIsoCanonical ℱ).hom ≫ δ := by rw [hcomp]

private theorem compatibleAddCommGroupStructure_ext_of_add
    {F : X.Presheaf (Type u)} {h₁ h₂ : CompatibleAddCommGroupStructure F}
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : F.obj U),
      (h₁.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t) =
        (h₂.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t)) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  simp [CompatibleAddCommGroupStructure.toCompatibleAdditionMapStructure,
    CompatibleAddCommGroupStructure.addNatTrans, binaryProductIso_hom_app_prodMk] at hadd
  simp only [CompatibleAddCommGroupStructure.mk.injEq] at ⊢
  funext U
  apply AddCommGroup.ext
  funext s t
  exact hadd U s t

private noncomputable def compatibleAddCommGroupStructureSheaf
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj) : Ab(X) where
  obj := h.toPAb
  property := by
    refine (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2 ?_
    simpa [h.toPAb_forget] using (ℱ^#).property

private theorem compatibleAddCommGroupStructureSheaf_forget
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj) :
    (compatibleAddCommGroupStructureSheaf ℱ h).obj ⋙ forget AddCommGrpCat.{u} = (ℱ^#).obj :=
  h.toPAb_forget

private noncomputable def toCompatibleSetSheafification
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    ℱ ⟶ h.toPAb where
  app U := by
    let _ := h.addCommGroup U
    exact AddCommGrpCat.ofHom <|
      AddMonoidHom.mk' ((toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U) (hadd U)
  naturality := by
    intro U V i
    apply AddCommGrpCat.ext
    intro s
    simpa using congrFun ((toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).naturality i) s

private theorem toCompatibleSetSheafification_forget
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    Functor.whiskerRight (toCompatibleSetSheafification ℱ h hadd) (forget AddCommGrpCat.{u}) ≫
      eqToHom h.toPAb_forget =
        toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
  ext U s
  rfl

private theorem setSheafificationAb_iso_of_toSheafify_map_add
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    ∃! γ : setSheafificationAb ℱ ⟶ compatibleAddCommGroupStructureSheaf ℱ h,
      toSetSheafificationAb ℱ ≫ γ.hom = toCompatibleSetSheafification ℱ h hadd ∧
        Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) =
          eqToHom (setSheafificationAb_forget ℱ) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm := by
  obtain ⟨γ, hγ, hγuniq⟩ :=
    existsUnique_setSheafificationLift
      (show ℱ ⟶ (compatibleAddCommGroupStructureSheaf ℱ h).obj from
        toCompatibleSetSheafification ℱ h hadd)
  have hunderlying_id :
      eqToHom (setSheafificationAb_forget ℱ).symm ≫
          Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) =
        𝟙 (ℱ^#).obj := by
    apply setSheafification_hom_ext ℱ
    calc
      toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫
          eqToHom (setSheafificationAb_forget ℱ).symm ≫
            Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
              eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) =
        Functor.whiskerRight (toSetSheafificationAb ℱ) (forget AddCommGrpCat.{u}) ≫
            Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) ≫
              eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          rw [← toSetSheafificationAb_forget ℱ]
          simp [Category.assoc]
      _ = Functor.whiskerRight (toSetSheafificationAb ℱ ≫ γ.hom) (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          simp [Category.assoc]
      _ = Functor.whiskerRight (toCompatibleSetSheafification ℱ h hadd)
            (forget AddCommGrpCat.{u}) ≫
            eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h) := by
          simpa using congrArg
            (fun k ↦
              Functor.whiskerRight k (forget AddCommGrpCat.{u}) ≫
                eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h))
            hγ
      _ = toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) := by
          exact toCompatibleSetSheafification_forget ℱ h hadd
      _ = toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u}) ≫ 𝟙 (ℱ^#).obj := by simp
  have hunderlying :
      Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}) =
        eqToHom (setSheafificationAb_forget ℱ) ≫
          eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm := by
    have h' := congrArg
      (fun k ↦
        eqToHom (setSheafificationAb_forget ℱ) ≫ k ≫
          eqToHom (compatibleAddCommGroupStructureSheaf_forget ℱ h).symm)
      hunderlying_id
    simpa [Category.assoc] using h'
  refine ⟨γ, ⟨hγ, hunderlying⟩, ?_⟩
  intro γ' hγ'
  exact hγuniq γ' hγ'.1

/-- Lemma 6.18.2, exact-structure uniqueness: if a compatible additive structure on the fixed
set-valued sheafification `ℱ^#` makes the actual sheafification unit additive on every open, then
that structure is exactly the transported structure
`setSheafificationCompatibleAddCommGroupStructure ℱ`. -/
theorem setSheafificationCompatibleAddCommGroupStructure_unique
    (h : CompatibleAddCommGroupStructure (ℱ^#).obj)
    (hadd : ∀ (U : (Opens X)ᵒᵖ) (s t : ℱ.obj U),
      by
        let _ := h.addCommGroup U
        exact
          (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U (s + t) =
            (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U s +
              (toSheafify J (ℱ ⋙ forget AddCommGrpCat.{u})).app U t) :
    h = setSheafificationCompatibleAddCommGroupStructure ℱ := by
  obtain ⟨γ, hγ, _⟩ :=
    setSheafificationAb_iso_of_toSheafify_map_add ℱ h hadd
  apply compatibleAddCommGroupStructure_ext_of_add
  intro U s t
  let _ := h.addCommGroup U
  let _ := (setSheafificationCompatibleAddCommGroupStructure ℱ).addCommGroup U
  letI : (forget AddCommGrpCat.{u}).ReflectsIsomorphisms := by
    infer_instance
  haveI :
      IsIso
        (((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u})).map γ.hom) := by
    change IsIso (Functor.whiskerRight γ.hom (forget AddCommGrpCat.{u}))
    rw [hγ.2]
    infer_instance
  haveI : IsIso (γ.hom) :=
    isIso_of_reflects_iso γ.hom
      ((Functor.whiskeringRight (Opens X)ᵒᵖ AddCommGrpCat.{u} (Type u)).obj
        (forget AddCommGrpCat.{u}))
  let hU := γ.hom.app U
  letI : IsIso hU := NatIso.isIso_app_of_isIso γ.hom U
  let iU := inv hU
  have hU_id (x : ((setSheafificationAb ℱ).obj).obj U) : hU.hom x = x := by
    simpa using congrFun (congrArg (fun k ↦ k.app U) hγ.2) x
  have iU_id (x : ((compatibleAddCommGroupStructureSheaf ℱ h).obj).obj U) : iU.hom x = x := by
    have h₁ : hU.hom (iU.hom x) = iU.hom x := hU_id (iU.hom x)
    have h₂ : hU.hom (iU.hom x) = x := by
      simpa [iU] using IsIso.inv_hom_id_apply hU x
    exact h₁.symm.trans h₂
  have hs : iU.hom s = s := iU_id s
  have ht : iU.hom t = t := iU_id t
  have hsource :
      (iU.hom
        ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))) =
      (h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t) := by
    exact iU_id ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))
  have hadd :
      (iU.hom
        ((h.toCompatibleAdditionMapStructure.add).app U (FunctorToTypes.prodMk s t))) =
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk (iU.hom s) (iU.hom t)) := by
    rw [CompatibleAdditionMapStructure.add_app_eq_add
        (h.toCompatibleAdditionMapStructure) U s t]
    rw [CompatibleAdditionMapStructure.add_app_eq_add
        ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure)
        U (iU.hom s) (iU.hom t)]
    exact iU.hom.map_add s t
  have htarget :
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk (iU.hom s) (iU.hom t)) =
      ((setSheafificationCompatibleAddCommGroupStructure ℱ).toCompatibleAdditionMapStructure.add).app U
        (FunctorToTypes.prodMk s t) := by
    simp [hs, ht]
  exact hsource.symm.trans (hadd.trans htarget)

end

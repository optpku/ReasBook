module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
public import stacks_project.Chap06.Definition_6_26_1
public import stacks_project.Chap06.Lemma_6_31_8
public import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves
public import stacks_project.Chap06.Lemma_6_31_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.12:
- primary domain: extension by zero for sheaves of modules on a ringed space, together with
  fully-faithfulness and essential-image detection by vanishing stalks outside an open subset;
- sampled owner declarations:
  `moduleSheafExtensionByZeroAdjunction`,
  `moduleSheafExtensionByZeroFromOpen`,
  `openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem`,
  `openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isZero_of_not_mem`;
- owner abstraction: the source-facing adjunction owner
  `moduleSheafExtensionByZeroAdjunction`, together with the abelian essential-image criterion from
  `Lemma_6_31_10`;
- primitive data: the ringed space `X`, the open subset `U`, the canonical extension-by-zero
  functor on module sheaves, and the underlying-additive-sheaf functor
  `SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)`;
- derived API: full faithfulness of the module extension-by-zero functor and the module-valued
  zero-stalk essential-image criterion, with the additive criterion used only as an internal
  bridge.

Source/core/bridge triage:
- `source-facing`: the Stacks-project module-sheaf statements in parts (1) and (2);
- `core/canonical`: the explicit `j_! ⊣ j^{-1}` owner from `Lemma_6_31_8` and the abelian owner
  criterion from `Lemma_6_31_10`;
- `bridge/view`: this file’s passage from module-valued stalks to underlying additive stalks via
  `SheafOfModules.toSheaf`.

This file should therefore keep the source-facing module-sheaf statements as the public API: no
new wrapper owner is needed, and the additive-stalk criterion should appear only internally in the
proof of part (2).
-/

section

variable {X : RingedSpace.{u}}

local notation "𝒪X" => RingedSpace.ringCatSheaf X

-- Proof sketch: the explicit extension-by-zero functor agrees with the usual left adjoint to
-- restriction along the open immersion `j : U ↪ X`, and the unit `id ⟶ j⁻¹ j_!` is an
-- isomorphism on module sheaves over `U`; hence `j_!` is fully faithful.
/-- First assertion of Lemma 6.31.12: for a ringed space `(X, \mathcal{O}_X)` and an open
subspace `j : U ↪ X`,
the canonical extension-by-zero functor
`j_! : \textit{Mod}(\mathcal{O}|_U) \to \textit{Mod}(\mathcal{O})`
is fully faithful. -/
instance openSubsetModuleSheafExtensionByZero_fullyFaithful
    (U : Opens X.carrier) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).FullyFaithful := by
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  letI : IsIso h.unit := by
    change IsIso ((openSubspaceModuleSheafExtensionByZero_unitIso (X := X) U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.12: `SheafOfModules.toSheaf` preserves and reflects isomorphisms on the
module counit component, so only the additive comparison remains to be checked. -/
private theorem openSubsetModuleSheafExtensionByZero_counit_isIso_iff_toSheaf_map
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    IsIso ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢) ↔
      IsIso
        ((SheafOfModules.toSheaf 𝒪X).map
          ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)) := by
  constructor
  · intro hCounit
    letI := hCounit
    -- Once the module counit is invertible, any functor preserves that invertibility.
    simpa using
      (Functor.map_isIso (SheafOfModules.toSheaf 𝒪X)
        ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢))
  · intro hCounit
    letI := hCounit
    -- Conversely, `toSheaf` reflects isomorphisms because it is faithful and its composition with
    -- `sheafToPresheaf` is the forgetful functor to additive presheaves.
    exact isIso_of_reflects_iso
      ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)
      (SheafOfModules.toSheaf 𝒪X)

/-- Helper for Lemma 6.31.12: the restriction-side comparison is natural in the module counit. -/
private theorem moduleSheafRestrictionToOpen_toSheafNatIso_naturality_counit
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    let A := (moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢
    let ε := (openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢
    let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
    let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
      ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj A)
    e'.hom ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
        ((SheafOfModules.toSheaf 𝒪X).map ε) =
      (SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).map
        ((moduleSheafRestrictionToOpen U 𝒪X).map ε) ≫
      e.hom := by
  let A := (moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢
  let ε := (openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢
  let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
  let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
    ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj A)
  have hnat := (moduleSheafRestrictionToOpen_toSheafNatIso (X := X) U).hom.naturality ε
  -- The naturality square of the whiskered comparison natural isomorphism is definitionally the
  -- desired square: `toSheafNatIso.hom.app` unfolds to the per-object `toSheafIso` and the
  -- composite-functor `.map` agrees with the iterated `.map` by `Functor.comp_map`.
  exact hnat.symm

/-- Helper for Lemma 6.31.12: the presheaf stalk pullback comparison is natural in the presheaf
argument for sheaves of abelian groups. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Z Y : TopCat.{u}} (f : Z ⟶ Y)
    {ℱ 𝒢 : Y.Presheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : Z) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η) := by
  -- Compare both morphisms after precomposing with every germ, where the pullback-stalk owner is
  -- defined.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro V hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) V (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f 𝒢 x V hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f ℱ x V hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) ((Opens.map f).obj V) x
    hx ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let A :=
    ℱ.germ V (f x) hx ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let B :=
    η.app (Opposite.op V) ≫ 𝒢.germ V (f x) hx ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let C :=
    η.app (Opposite.op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app 𝒢).app
        (Opposite.op V) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η).app
          (Opposite.op ((Opens.map f).obj V)) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
        (Opposite.op V) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ).germ ((Opens.map f).obj V) x hx ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let Z :=
    ℱ.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using h₁
  have hB : B = C := by
    simpa [B, C, Category.assoc] using congrArg
      (fun k ↦ η.app (Opposite.op V) ≫ k)
      h₂𝒢
  have hC : C = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.naturality η)
      (Opposite.op V)
    simpa [C, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj V)
            x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using congrArg
      (fun k ↦
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
            (Opposite.op V) ≫
          k)
      h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using congrArg
      (fun k ↦ k ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η))
      h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.12: the sheaf stalk pullback comparison is natural in the sheaf
argument for sheaves of abelian groups. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Z Y : TopCat.{u}} (f : Z ⟶ Y)
    {ℱ 𝒢 : Y.Sheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : Z) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
  -- Unfold the sheaf-level stalk comparison into the presheaf pullback iso, sheafification unit,
  -- and `pullbackIso.inv`, then move `η` through each factor in turn.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) := by
    -- This is the stalked form of `toSheafify_naturality`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology Z)
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    -- This is the stalked form of naturality for `TopCat.Sheaf.pullbackIso.inv`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} Z).map k)
          (((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv).naturality η))
  have h₁ :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    -- First move `η` through the presheaf-level stalk pullback comparison.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      (presheaf_stalkPullbackIso_hom_naturality f η.hom x)
  have h₂ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) := by
    -- Next move `η` through the sheafification unit.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          k ≫ ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))
      hsheafify
  have h₃ :
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
    -- Finally move `η` through the `pullbackIso.inv` comparison.
    have hpost :
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map σ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map π𝒢))) =
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map πℱ) ≫
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
                  (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)))) := by
      exact congrArg
        (fun k ↦
          (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map τℱ) ≫ k))
        hpullbackIso
    simpa [Category.assoc] using hpost
  exact
    (by
      simpa [σ, τ𝒢, τℱ, π𝒢, πℱ, Category.assoc] using h₁.trans (h₂.trans h₃))

/-- Helper for Lemma 6.31.12: on points of `U`, the underlying-additive stalk map of the module
counit is an isomorphism. -/
private theorem moduleCounit_toSheaf_stalkMap_isIso_of_mem
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) (x : X.carrier) (hx : x ∈ (U : Set X.carrier)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((SheafOfModules.toSheaf 𝒪X).map
          ((openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U).counit.app 𝒢)).hom)) := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  let R := moduleSheafRestrictionToOpen U 𝒪X
  let ε := h.counit.app 𝒢
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((openSubspaceModuleSheafExtensionByZero_unitIso (X := X) U).hom.app (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let unitIso :
      R.obj 𝒢 ≅ R.obj ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢)) :=
    @asIso _ _ _ _ (h.unit.app (R.obj 𝒢)) hunit
  have hright : R.map ε = inv (h.unit.app (R.obj 𝒢)) := by
    have htriangle : h.unit.app (R.obj 𝒢) ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
      simpa [R, ε] using h.right_triangle_components 𝒢
    have := congrArg (fun k ↦ inv (h.unit.app (R.obj 𝒢)) ≫ k) htriangle
    simpa [Category.assoc] using this
  let e := moduleSheafRestrictionToOpen_toSheafIso (X := X) U 𝒢
  let e' := moduleSheafRestrictionToOpen_toSheafIso (X := X) U
    ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))
  have hRmapIso : IsIso (R.map ε) := by
    rw [hright]
    change IsIso unitIso.inv
    infer_instance
  let toSheafRMap :=
    (SheafOfModules.toSheaf
      ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒪X)).map
      (R.map ε)
  letI :
      IsIso
        toSheafRMap := by
    infer_instance
  let toSheafRMapIso := asIso toSheafRMap
  let toSheafRMapPresheafIso :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
      toSheafRMapIso
  let ePresheafIso :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso e
  let ePresheafIso' :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso e'
  let toSheafRMapStalkIso :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso toSheafRMapPresheafIso
  let eStalk := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso ePresheafIso
  let eStalk' := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso ePresheafIso'
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          toSheafRMap.hom) := by
    change IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map toSheafRMapPresheafIso.hom)
    infer_instance
  letI :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e.hom.hom) := by
    change IsIso eStalk.hom
    infer_instance
  letI :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom) := by
    change IsIso eStalk'.hom
    infer_instance
  let pullbackToSheafMap :=
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
      ((SheafOfModules.toSheaf 𝒪X).map ε)
  have hnat := moduleSheafRestrictionToOpen_toSheafNatIso_naturality_counit (U := U) (𝒢 := 𝒢)
  have hnatStalkRaw := congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map k.hom)
      hnat
  have hPullbackMap :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          pullbackToSheafMap.hom) := by
    have hEq :
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          ((moduleSheafRestrictionToOpen_toSheafIso (X := X) U
                ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))).hom.hom ≫
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
              ((SheafOfModules.toSheaf 𝒪X).map ε)).hom)) =
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (toSheafRMap.hom ≫ e.hom.hom)) := by
      simpa only [R, ε] using hnatStalkRaw
    have hCompSplit :
        IsIso
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
                (moduleSheafRestrictionToOpen_toSheafIso (X := X) U
                  ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))).hom.hom) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
                ((SheafOfModules.toSheaf 𝒪X).map ε)).hom))) := by
      have :
          IsIso
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              (toSheafRMap.hom ≫ e.hom.hom)) := by
        rw [Functor.map_comp]
        change IsIso (toSheafRMapStalkIso.hom ≫ eStalk.hom)
        infer_instance
      rw [← Functor.map_comp]
      rw [hEq]
      exact this
    have hCompRaw :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (e'.hom.hom ≫ pullbackToSheafMap.hom)) := by
      rw [Functor.map_comp]
      simpa [e', pullbackToSheafMap] using hCompSplit
    have hComp :
        IsIso
          (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom) ≫
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)) := by
      simpa [e', pullbackToSheafMap, Functor.map_comp] using hCompRaw
    exact
      (isIso_comp_left_iff
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map e'.hom.hom)
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)).1 hComp
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom) := hPullbackMap
  let targetPullbackStalkIso :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((SheafOfModules.toSheaf 𝒪X).obj 𝒢) xU
  let sourcePullbackStalkIso :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((SheafOfModules.toSheaf 𝒪X).obj
        ((openSubsetModuleSheafExtensionByZero U 𝒪X).obj (R.obj 𝒢))) xU
  letI : IsIso targetPullbackStalkIso.hom := by
    infer_instance
  letI : IsIso sourcePullbackStalkIso.hom := by
    infer_instance
  have hpullbackNat :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) ≫
          targetPullbackStalkIso.hom =
        sourcePullbackStalkIso.hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom) := by
    simpa [ε] using sheaf_stalkPullbackIso_hom_naturality
      (f := extensionByZeroOpenSubsetInclusion U)
      (η := (SheafOfModules.toSheaf 𝒪X).map ε)
      (x := xU)
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (extensionByZeroOpenSubsetInclusion U xU)).map
            (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) ≫
          targetPullbackStalkIso.hom) := by
    let sourceCompIso :=
      sourcePullbackStalkIso ≪≫
        @asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map pullbackToSheafMap.hom)
          hPullbackMap
    rw [hpullbackNat]
    change IsIso sourceCompIso.hom
    infer_instance
  have hMap :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom)) :=
    (isIso_comp_right_iff
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (extensionByZeroOpenSubsetInclusion U xU)).map
          (((SheafOfModules.toSheaf 𝒪X).map ε).hom))
      targetPullbackStalkIso.hom).1 hComp
  simpa using hMap

/-- Helper for Lemma 6.31.12: a stalk module is zero exactly when its underlying additive stalk
is zero. -/
private theorem module_stalk_isZero_iff_underlying
    (x : X) (𝒢 : SheafOfModules 𝒪X) :
    IsZero
        (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf x)) ↔
      IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
  let F :=
    forget₂ (ModuleCat ((RingedSpace.ringCatSheaf X).presheaf.stalk x)) AddCommGrpCat
  constructor
  · intro h
    simpa [F] using F.map_isZero h
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    apply F.map_injective
    simpa [F] using h

-- Proof sketch: an extended module has zero stalks outside `U` by the explicit construction;
-- conversely, if a module sheaf on `X` has zero stalks off `U`, then the canonical counit
-- `j_! j⁻¹ 𝒢 ⟶ 𝒢` is an isomorphism on stalks, so `𝒢` belongs to the essential image.
/-- Lemma 6.31.12 (2): a sheaf of `\mathcal{O}_X`-modules on `X` lies in the essential image of
the canonical extension-by-zero functor from `U` if and only if all of its stalks at points of
`X \setminus U` are zero. -/
theorem openSubsetModuleSheafExtensionByZero_essImage_iff_stalk_isZero_of_not_mem
    (U : Opens X.carrier) (𝒢 : SheafOfModules 𝒪X) :
    (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X.carrier) →
        IsZero
          (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk 𝒢.val.presheaf x)) := by
  let h :
      openSubsetModuleSheafExtensionByZero U 𝒪X ⊣ moduleSheafRestrictionToOpen U 𝒪X :=
    openSubsetModuleSheafExtensionByZeroAdjunction (X := X) U
  have hFF : (openSubsetModuleSheafExtensionByZero U 𝒪X).FullyFaithful :=
    openSubsetModuleSheafExtensionByZero_fullyFaithful (X := X) U
  letI : (openSubsetModuleSheafExtensionByZero U 𝒪X).Full := hFF.full
  letI : (openSubsetModuleSheafExtensionByZero U 𝒪X).Faithful := hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢 := by
    -- For a fully faithful left adjoint, the counit detects essential-image membership.
    simpa using
      (h.isIso_counit_app_iff_mem_essImage :
        IsIso (h.counit.app 𝒢) ↔ (openSubsetModuleSheafExtensionByZero U 𝒪X).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    let ε := h.counit.app 𝒢
    let εAdd := (SheafOfModules.toSheaf 𝒪X).map ε
    letI : IsIso ε := hess.mpr h𝒢
    have hToSheaf :
        IsIso εAdd := by
      infer_instance
    letI : IsIso εAdd := hToSheaf
    have hStalkMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom) := by
      exact (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso εAdd).1 hToSheaf x
    let sourceSheaf :=
      (openSubsetModuleSheafExtensionByZero U 𝒪X).obj
        ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢)
    have hSourceZero :
        IsZero
          (TopCat.Presheaf.stalk sourceSheaf.val.presheaf x) := by
      exact
        (module_stalk_isZero_iff_underlying (X := X) x sourceSheaf).1
          (openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
            (X := X) (U := U) ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢) hx)
    have hTargetZero :
        IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
      letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom) := hStalkMap
      exact IsZero.of_iso hSourceZero
        (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom)).symm
    exact (module_stalk_isZero_iff_underlying (X := X) x 𝒢).2 hTargetZero
  · intro hZero
    let ε := h.counit.app 𝒢
    let εAdd := (SheafOfModules.toSheaf 𝒪X).map ε
    have hToSheaf :
        IsIso εAdd := by
      refine (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso εAdd).2 ?_
      intro x
      by_cases hx : x ∈ (U : Set X.carrier)
      · exact moduleCounit_toSheaf_stalkMap_isIso_of_mem (X := X) U 𝒢 x hx
      · let sourceSheaf :=
            (openSubsetModuleSheafExtensionByZero U 𝒪X).obj
              ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢)
        have hSourceZero :
            IsZero (TopCat.Presheaf.stalk sourceSheaf.val.presheaf x) := by
          exact
            (module_stalk_isZero_iff_underlying (X := X) x sourceSheaf).1
              (openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
                (X := X) (U := U) ((moduleSheafRestrictionToOpen U 𝒪X).obj 𝒢) hx)
        have hTargetZero :
            IsZero (TopCat.Presheaf.stalk 𝒢.val.presheaf x) := by
          exact (module_stalk_isZero_iff_underlying (X := X) x 𝒢).1 (hZero x hx)
        exact hSourceZero.isIso hTargetZero
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map εAdd.hom)
    have : IsIso ε := by
      exact isIso_of_reflects_iso ε (SheafOfModules.toSheaf 𝒪X)
    exact hess.mp this

end

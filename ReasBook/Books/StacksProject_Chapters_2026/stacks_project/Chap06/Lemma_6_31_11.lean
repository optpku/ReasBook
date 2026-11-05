module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Extension_by_zero_by_the_initial_object
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 6.31.11:
- primary domain: extension by the initial object for sheaves of algebraic structures along an
  open immersion;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction: the Chapter 6 owner is the open-subset extension-by-initial-object adjunction
  and its stalk description, not a new local wrapper;
- primitive data: the open subset `U`, the sheaf `𝒢`, and the canonical map `initial.to` on the
  stalks;
- derived API: the fully faithful instance and the essential-image criterion.

Source/core/bridge triage:
- `source-facing`: the Stacks-project statements that `j_!` is fully faithful and that its
  essential image is detected by initial stalks outside `U`;
- `core/canonical`: `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction` together with
  the owner-side stalk theorem outside `U`;
- `bridge/view`: this file’s algebraic-structure specialization of those owner declarations.

The public API here should therefore keep only the source-facing fully-faithful and essential-image
statements, while reusing the owner adjunction and stalk theorem directly rather than keeping a
parallel local stalk-initial wrapper.
-/

section

variable {X : TopCat.{v}}

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimits C] [HasLimits C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [hFunLike : ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [hConcrete : ConcreteCategory.{v} C FC]
variable [hPreservesLimits : PreservesLimits (CategoryTheory.forget C)]
variable [hPreservesFilteredColimits : PreservesFilteredColimits (CategoryTheory.forget C)]
variable [hReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms]
variable [hWeakSheafify : CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

include FC CC hFunLike hConcrete hPreservesLimits hPreservesFilteredColimits
  hReflectsIsomorphisms

-- Proof sketch: the restriction functor to the open subspace is the sheaf pushforward along the
-- inclusion-of-opens functor, and `j_!` is its left adjoint. As in the set-valued case, the unit
-- is an isomorphism because on opens lying in `U` the construction agrees with the original sheaf.
/-- Lemma 6.31.11 (1): for a type of algebraic structures with an initial object, extension by the
initial object along the inclusion `j : U ↪ X` is a fully faithful functor on sheaves. -/
instance openSubsetSheafExtensionByInitialObject_fullyFaithful_6_31_11
    (U : Opens X) :
    (((j! U) :
      (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  letI : IsIso h.unit := by
    change IsIso
      ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.11: the presheaf stalk pullback isomorphism is natural in the presheaf
argument. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf C} (η : ℱ ⟶ 𝒢) (x : X) :
    (TopCat.Presheaf.stalkFunctor C (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso C f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso C f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η) := by
  -- Compare both morphisms after precomposing with germs; the pullback stalk isomorphism is built
  -- from those germs and the pullback-pushforward unit.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro V hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := C) V (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := C) f 𝒢 x V hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := C) f ℱ x V hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := C) ((Opens.map f).obj V) x hx
    ((TopCat.Presheaf.pullback C f).map η)
  let A :=
    ℱ.germ V (f x) hx ≫ (TopCat.Presheaf.stalkFunctor C (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom C f 𝒢 x
  let B :=
    η.app (op V) ≫ 𝒢.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom C f 𝒢 x
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫
      ((TopCat.Presheaf.pullback C f).map η).app (op ((Opens.map f).obj V)) ≫
        ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let C₁ :=
    η.app (op V) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app 𝒢).app (op V) ≫
        ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫
      ((TopCat.Presheaf.pullback C f).obj ℱ).germ ((Opens.map f).obj V) x hx ≫
        (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η)
  let Z :=
    ℱ.germ V (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom C f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using
      congrArg (fun k ↦ k ≫ TopCat.Presheaf.stalkPullbackHom C f 𝒢 x) h₁
  have hB : B = C₁ := by
    simpa [B, C₁, Category.assoc] using congrArg (fun k ↦ η.app (op V) ≫ k) h₂𝒢
  have hC : C₁ = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.naturality η) (op V)
    simpa [C₁, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback C f).obj 𝒢).germ ((Opens.map f).obj V) x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using
      congrArg
        (fun k ↦
          ((TopCat.Presheaf.pullbackPushforwardAdjunction C f).unit.app ℱ).app (op V) ≫ k)
        h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Presheaf.pullback C f).map η))
        h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.11: the sheaf stalk pullback comparison is natural in the sheaf
argument. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{v}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Sheaf C} (η : ℱ ⟶ 𝒢) (x : X) :
    ((TopCat.Presheaf.stalkFunctor C (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          (((TopCat.Sheaf.pullback C f).map η).hom)) := by
  -- Unfold the sheaf-level stalk comparison into the presheaf pullback iso, sheafification unit,
  -- and `pullbackIso.inv`, then move `η` through each factor.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback C f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget C X).map
      ((TopCat.Sheaf.pullbackIso C f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget C X).map
      ((TopCat.Sheaf.pullbackIso C f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map σ) := by
    -- This is the stalked form of `toSheafify_naturality`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback C f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          (((TopCat.Sheaf.pullback C f).map η).hom)) := by
    -- This is the stalked form of naturality for `TopCat.Sheaf.pullbackIso.inv`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget C X).map k)
          (((TopCat.Sheaf.pullbackIso C f).inv).naturality η))
  have hstep₁ :
    ((TopCat.Presheaf.stalkFunctor C (f x)).map η.hom) ≫
        (TopCat.Presheaf.stalkPullbackIso C f 𝒢.presheaf x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
        ((TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
    -- First move `η` through the presheaf-level stalk pullback comparison.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map π𝒢))
      (presheaf_stalkPullbackIso_hom_naturality (C := C) f η.hom x)
  have hstep₂ :
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
    -- Next move `η` through the sheafification unit.
    have hstep₂' :
        (((TopCat.Presheaf.stalkFunctor C x).map
              ((TopCat.Presheaf.pullback C f).map η.hom)) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map τ𝒢)) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
          (((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map σ)) ≫
            ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) := by
      exact congrArg
        (fun k ↦ k ≫ ((TopCat.Presheaf.stalkFunctor C x).map π𝒢))
        hsheafify
    simpa [Category.assoc] using congrArg
      (fun k ↦ (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫ k)
      hstep₂'
  have hstep₃ :
      (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor C x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor C x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor C x).map
            (((TopCat.Sheaf.pullback C f).map η).hom)) := by
    -- Finally move `η` through the `pullbackIso.inv` comparison.
    have hpullbackIso' :
        ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
            ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            (((TopCat.Presheaf.stalkFunctor C x).map σ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map π𝒢)) =
          ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
              ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            (((TopCat.Presheaf.stalkFunctor C x).map πℱ) ≫
              ((TopCat.Presheaf.stalkFunctor C x).map
                (((TopCat.Sheaf.pullback C f).map η).hom))) := by
      exact congrArg
        (fun k ↦
          ((TopCat.Presheaf.stalkPullbackIso C f ℱ.presheaf x).hom ≫
              ((TopCat.Presheaf.stalkFunctor C x).map τℱ)) ≫
            k)
        hpullbackIso
    simpa [Category.assoc] using hpullbackIso'
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 6.31.11: on points of `U`, the counit stalk map followed by the stalk
pullback comparison agrees with the explicit stalk identification coming from the unit isomorphism.
-/
private theorem counit_stalk_map_comp_stalkPullbackIso_eq_of_mem
    (U : Opens X) (𝒢 : X.Sheaf C) (x : X) (hx : x ∈ (U : Set X)) :
    let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
    let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
    let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
    let explicit :
        (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU) ≪≫
        ((TopCat.Presheaf.stalkFunctor C xU).mapIso
          ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
            (asIso (h.unit.app (R.obj 𝒢))))).symm
    ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
      explicit.hom := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor C xU).mapIso
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  change ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
    explicit.hom
  -- Route correction: prove the inside-`U` comparison by sheaf-level naturality of
  -- `stalkPullbackIso`, then rewrite `R.map ε` to the inverse unit via the right triangle.
  let e : R.obj 𝒢 ≅ R.obj ((j! U).obj (R.obj 𝒢)) :=
    @asIso _ _ _ _ (h.unit.app (R.obj 𝒢)) hunit
  have hright :
      R.map (h.counit.app 𝒢) = inv (h.unit.app (R.obj 𝒢)) := by
    -- Precompose the right triangle with the inverse unit to isolate `R.map ε`.
    have htriangle :
        h.unit.app (R.obj 𝒢) ≫ R.map (h.counit.app 𝒢) = 𝟙 (R.obj 𝒢) := by
      simpa [R] using h.right_triangle_components 𝒢
    have := congrArg (fun k ↦ inv (h.unit.app (R.obj 𝒢)) ≫ k) htriangle
    simpa [Category.assoc] using this
  have hnat :
      ((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
            xU).hom ≫
          ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) := by
    -- First move the counit across the sheaf stalk pullback comparison.
    simpa [R] using sheaf_stalkPullbackIso_hom_naturality
      (C := C) (f := extensionByZeroOpenSubsetInclusion U) (η := h.counit.app 𝒢) (x := xU)
  rw [hnat]
  have hforget :
      (R.map (h.counit.app 𝒢)).hom =
        (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
          (inv (h.unit.app (R.obj 𝒢))) := by
    -- Rewrite the underlying presheaf map using the right-triangle identity.
    simpa [hright] using congrArg
      (fun k ↦ (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map k) hright
  let stalkUnitIso :
      (R.obj 𝒢).presheaf.stalk xU ≅
        (R.obj ((j! U).obj (R.obj 𝒢))).presheaf.stalk xU :=
    (TopCat.Presheaf.stalkFunctor C xU).mapIso
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso e)
  have hstalk :
      ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) =
        stalkUnitIso.inv := by
    -- Apply the stalk functor to the inverse-unit description of `R.map ε`.
    rw [hforget]
    have hforgetInv :
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom) := by
      exact Functor.map_inv (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) e.hom
    simpa [stalkUnitIso, e] using congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor C xU).map k)
      hforgetInv
  have hcomp :
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        ((TopCat.Presheaf.stalkFunctor C xU).map (R.map (h.counit.app 𝒢)).hom) =
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        stalkUnitIso.inv := by
    -- Replace the stalk map of `R.map ε` by the inverse of the stalked unit.
    simpa using congrArg
      (fun k ↦
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫ k)
      hstalk
  have hexplicit :
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        stalkUnitIso.inv =
      explicit.hom := by
    -- This is exactly the explicit composite defining the inside-`U` stalk isomorphism.
    have hforgetInv :
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom) := by
      exact Functor.map_inv (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) e.hom
    have heinv :
        (TopCat.Presheaf.stalkFunctor C xU).map
            ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.inv) =
          inv
            ((TopCat.Presheaf.stalkFunctor C xU).map
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) := by
      have hstalkInv :
          (TopCat.Presheaf.stalkFunctor C xU).map
              (inv ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) =
            inv
              ((TopCat.Presheaf.stalkFunctor C xU).map
                ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)) := by
        exact Functor.map_inv (TopCat.Presheaf.stalkFunctor C xU)
          ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map e.hom)
      exact (congrArg
        (fun k ↦ (TopCat.Presheaf.stalkFunctor C xU).map k)
        hforgetInv).trans hstalkInv
    simp [explicit, stalkUnitIso, e, Category.assoc]
    have hstalkInv' :
        (TopCat.Presheaf.stalkFunctor C xU).map
            (inv
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) =
          inv
            ((TopCat.Presheaf.stalkFunctor C xU).map
              ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) := by
      exact Functor.map_inv (TopCat.Presheaf.stalkFunctor C xU)
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj 𝒢)))
    exact congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkFunctor C xU).map
            (CategoryTheory.toSheafify
              (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
              ((TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj
                ((TopCat.Sheaf.forget C X).obj ((j! U).obj (R.obj 𝒢))))) ≫
          (TopCat.Presheaf.stalkFunctor C xU).map
            ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).map
              ((TopCat.Sheaf.pullbackIso C (extensionByZeroOpenSubsetInclusion U)).inv.app
                ((j! U).obj (R.obj 𝒢)))) ≫
          k)
      hstalkInv'
  exact hcomp.trans hexplicit

/-- Helper for Lemma 6.31.11: at points of `U`, the counit is stalkwise an isomorphism. -/
private theorem counit_stalk_map_isIso_of_mem
    (U : Opens X) (𝒢 : X.Sheaf C) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor C x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢).hom) := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor C xU).mapIso
        ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    -- The source-faithful step is the explicit inside-`U` stalk comparison from the helper above.
    rw [counit_stalk_map_comp_stalkPullbackIso_eq_of_mem (C := C) U 𝒢 x hx]
    infer_instance
  -- Cancel the pullback stalk comparison to recover the counit stalk map itself.
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor C x).map (h.counit.app 𝒢).hom) ≫
            (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) ≫
          inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

-- Proof sketch: if a sheaf is of the form `j_! ℱ`, then its stalks outside `U` are initial by the
-- extension-by-initial-object construction. Conversely, if the stalks of `𝒢` outside `U` are
-- initial, then the counit map `j_! j^{-1} 𝒢 ⟶ 𝒢` is an isomorphism on every stalk, hence an
-- isomorphism of sheaves, which places `𝒢` in the essential image of `j_!`.
/-- Lemma 6.31.11 (2): a sheaf of algebraic structures on `X` lies in the essential image of
extension by the initial object from `U` if and only if, at every point of `X \ U`, the canonical
map from the initial object of `C` to the stalk is an isomorphism. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf C) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsIso (initial.to (𝒢.presheaf.stalk x)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let hFF :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful :=
    openSubsetSheafExtensionByInitialObject_fullyFaithful_6_31_11 U
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Full :=
    hFF.full
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Faithful :=
    hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢 := by
    simpa using
      (h.isIso_counit_app_iff_mem_essImage : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    letI : IsIso (h.counit.app 𝒢) := hess.mpr h𝒢
    have hε : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := by
      infer_instance
    letI : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := hε
    have hMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      Functor.map_isIso (TopCat.Presheaf.stalkFunctor C x)
        ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))
    letI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      hMap
    have hSource :
        IsInitial
          (((j! U).obj
              ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
        ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
    have hTarget : IsInitial (𝒢.presheaf.stalk x) :=
      IsInitial.ofIso hSource
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) hMap)
    exact isIso_of_isInitial initialIsInitial hTarget (initial.to (𝒢.presheaf.stalk x))
  · intro h𝒢
    let ε := h.counit.app 𝒢
    have : IsIso ε := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      by_cases hx : x ∈ (U : Set X)
      · -- On `U`, the counit is inverse to the unit after transporting through the stalk pullback
        -- comparison.
        exact counit_stalk_map_isIso_of_mem (C := C) U 𝒢 x hx
      · let hSource :
            IsInitial
              (((j! U).obj
                  ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
          OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
            ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
        letI : IsIso (initial.to (𝒢.presheaf.stalk x)) := h𝒢 x hx
        let hTarget : IsInitial (𝒢.presheaf.stalk x) :=
          IsInitial.ofIso initialIsInitial (asIso (initial.to (𝒢.presheaf.stalk x)))
        exact isIso_of_isInitial hSource hTarget ((TopCat.Presheaf.stalkFunctor C x).map ε.hom)
    exact hess.mp this

end

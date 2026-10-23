module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

section

variable {X : TopCat.{u}}

/-
Domain-style sampling for Lemma 6.31.9:
- primary domain: extension by the initial object along an open immersion, specialized to
  set-valued sheaves;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`,
  `TopCat.Presheaf.stalkPullbackIso`;
- `source-facing`: full faithfulness of `j_!` and the empty-stalk characterization of its
  essential image;
- `core/canonical`: the owner adjunction from `Lemma_6_31_7`, together with stalkwise detection
  of isomorphisms;
- `bridge/view`: the `Type`-specific equivalence between “the canonical map from the initial
  object is an isomorphism” and “the target type is empty”.

The proof therefore follows the source route exactly: fully faithfulness comes from the unit
isomorphism, and the essential-image statement comes from checking the counit on stalks. The only
set-specific translation is the initial-object/empty-type bridge.
-/

/-- Helper for Lemma 6.31.9: in `Type`, the canonical map from the initial object is an
isomorphism exactly when the target type is empty. -/
private theorem type_isIso_initial_to_iff_isEmpty (A : Type u) :
    IsIso (initial.to A) ↔ IsEmpty A := by
  constructor
  · intro hA
    exact (Types.initial_iff_empty A).mp
      ⟨IsInitial.ofIso initialIsInitial (asIso (initial.to A))⟩
  · intro hA
    exact
      isIso_of_isInitial initialIsInitial ((Types.initial_iff_empty A).mpr hA).some
        (initial.to A)

/-- Helper for Lemma 6.31.9: the presheaf stalk pullback isomorphism is natural in the presheaf
argument. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf (Type u)} (η : ℱ ⟶ 𝒢) (x : X) :
    (TopCat.Presheaf.stalkFunctor (Type u) (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Presheaf.pullback (Type u) f).map η) := by
  -- Compare both morphisms after precomposing with every germ; the pullback-stalk isomorphism is
  -- built from germs and the pullback-pushforward unit, so the naturality reduces to those APIs.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro U hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := Type u) U (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := Type u) f 𝒢 x U hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := Type u) f ℱ x U hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := Type u) ((Opens.map f).obj U) x hx
    ((TopCat.Presheaf.pullback (Type u) f).map η)
  let A :=
    ℱ.germ U (f x) hx ≫ (TopCat.Presheaf.stalkFunctor (Type u) (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom (Type u) f 𝒢 x
  let B :=
    η.app (op U) ≫ 𝒢.germ U (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom (Type u) f 𝒢 x
  let C :=
    η.app (op U) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app 𝒢).app (op U) ≫
        ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢).germ ((Opens.map f).obj U) x hx
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℱ).app (op U) ≫
      ((TopCat.Presheaf.pullback (Type u) f).map η).app (op ((Opens.map f).obj U)) ≫
        ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢).germ ((Opens.map f).obj U) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℱ).app (op U) ≫
      ((TopCat.Presheaf.pullback (Type u) f).obj ℱ).germ ((Opens.map f).obj U) x hx ≫
        (TopCat.Presheaf.stalkFunctor (Type u) x).map ((TopCat.Presheaf.pullback (Type u) f).map η)
  let Z :=
    ℱ.germ U (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom (Type u) f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor (Type u) x).map ((TopCat.Presheaf.pullback (Type u) f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using
      congrArg (fun k ↦ k ≫ TopCat.Presheaf.stalkPullbackHom (Type u) f 𝒢 x) h₁
  have hB : B = C := by
    simpa [B, C, Category.assoc] using congrArg (fun k ↦ η.app (op U) ≫ k) h₂𝒢
  have hC : C = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.naturality η) (op U)
    simpa [C, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢).germ ((Opens.map f).obj U) x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using
      congrArg
        (fun k ↦
          ((TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app ℱ).app (op U) ≫
            k)
        h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (TopCat.Presheaf.stalkFunctor (Type u) x).map
              ((TopCat.Presheaf.pullback (Type u) f).map η))
        h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.9: the sheaf stalk pullback isomorphism is natural in the sheaf
argument. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Sheaf (Type u)} (η : ℱ ⟶ 𝒢) (x : X) :
    ((TopCat.Presheaf.stalkFunctor (Type u) (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((TopCat.Sheaf.pullback (Type u) f).map η).hom)) := by
  -- Unfold the sheaf-level stalk comparison into the presheaf pullback iso, sheafification unit,
  -- and `pullbackIso.inv`, then move `η` through each factor in turn.
  rw [TopCat.Sheaf.stalkPullbackIso_def, TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom, Category.assoc]
  let σ :=
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback (Type u) f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback (Type u) f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback (Type u) f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget (Type u) X).map ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget (Type u) X).map ((TopCat.Sheaf.pullbackIso (Type u) f).inv.app ℱ)
  have hsheafify :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          ((TopCat.Presheaf.pullback (Type u) f).map η.hom)) ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map τ𝒢) =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map σ) := by
    -- This is the stalked form of `toSheafify_naturality`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor (Type u) x).map k)
      (CategoryTheory.toSheafify_naturality
        (J := Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback (Type u) f).map η.hom))
  have hpullbackIso :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map σ) ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) =
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map πℱ) ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) x).map
          (((TopCat.Sheaf.pullback (Type u) f).map η).hom)) := by
    -- This is the stalked form of naturality for `TopCat.Sheaf.pullbackIso.inv`.
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun k ↦ (TopCat.Presheaf.stalkFunctor (Type u) x).map k)
      (by
        simpa [σ, π𝒢, πℱ] using congrArg
          (fun k ↦ (TopCat.Sheaf.forget (Type u) X).map k)
          (((TopCat.Sheaf.pullbackIso (Type u) f).inv).naturality η))
  have h₁ :
      ((TopCat.Presheaf.stalkFunctor (Type u) (f x)).map η.hom) ≫
          (TopCat.Presheaf.stalkPullbackIso (Type u) f 𝒢.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            ((TopCat.Presheaf.pullback (Type u) f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) := by
    -- First move `η` through the presheaf-level stalk pullback comparison.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        k ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τ𝒢) ≫
            ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢))
      (presheaf_stalkPullbackIso_hom_naturality f η.hom x)
  have h₂ :
      (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            ((TopCat.Presheaf.pullback (Type u) f).map η.hom)) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τ𝒢) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) := by
    -- Next move `η` through the sheafification unit.
    simpa [Category.assoc] using congrArg
      (fun k ↦
        (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          k ≫ ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢))
      hsheafify
  have h₃ :
      (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map σ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢) =
        (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map πℱ) ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            (((TopCat.Sheaf.pullback (Type u) f).map η).hom)) := by
    -- Finally move `η` through the `pullbackIso.inv` comparison.
    have hpost :
        (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor (Type u) x).map σ) ≫
                ((TopCat.Presheaf.stalkFunctor (Type u) x).map π𝒢))) =
          (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫
              (((TopCat.Presheaf.stalkFunctor (Type u) x).map πℱ) ≫
                ((TopCat.Presheaf.stalkFunctor (Type u) x).map
                  (((TopCat.Sheaf.pullback (Type u) f).map η).hom)))) := by
      exact congrArg
        (fun k ↦
          (TopCat.Presheaf.stalkPullbackIso (Type u) f ℱ.presheaf x).hom ≫
            (((TopCat.Presheaf.stalkFunctor (Type u) x).map τℱ) ≫ k))
        hpullbackIso
    simpa [Category.assoc] using hpost
  exact (by simpa [σ, τ𝒢, τℱ, π𝒢, πℱ, Category.assoc] using h₁.trans (h₂.trans h₃))

/-- Lemma 6.31.9 (first clause): extension by the empty set along `j : U ↪ X` is fully faithful
on sheaves of types. -/
instance openSubsetSheafExtensionByInitialObject_fullyFaithful
    (U : Opens X) :
    (((j! U) :
      (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))).FullyFaithful := by
  -- Fully faithfulness is formal from the adjunction once the unit is known to be invertible.
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  letI : IsIso h.unit := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso (C := Type u) U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.9: in the extension-by-empty-set adjunction, pulling back the counit is
an isomorphism because the counit is inverse to the unit by the right triangle identity. -/
private theorem counit_pullback_map_isIso
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) :
    IsIso
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).counit.app
          𝒢)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let R := TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)
  let η := h.unit.app (R.obj 𝒢)
  let ε := h.counit.app 𝒢
  have hη : IsIso η := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso (C := Type u) U).hom.app
      (R.obj 𝒢))
    infer_instance
  have hright : η ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
    simpa [R, η, ε] using h.right_triangle_components_assoc 𝒢 (𝟙 (R.obj 𝒢))
  have hleft : R.map ε ≫ η = 𝟙 (R.obj ((j! U).obj (R.obj 𝒢))) := by
    -- Cancel the unit on the left-hand side after using the right triangle identity.
    apply (CategoryTheory.cancel_epi η).1
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ η) hright
  exact ⟨⟨η, hleft, hright⟩⟩

/-- Helper for Lemma 6.31.9: after applying the stalk functor on the open subspace, the pullback
of the counit composes with the unit to the identity by the adjunction right triangle. -/
private theorem stalk_pullback_counit_comp_unit_eq_id
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) (xU : extensionByZeroOpenSubsetSpace U) :
    ((TopCat.Presheaf.stalkFunctor (Type u) xU).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).unit.app
          ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).hom) ≫
      ((TopCat.Presheaf.stalkFunctor (Type u) xU).map
        (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).map
          ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).counit.app
            𝒢)).hom)) =
      𝟙 _ := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let R := TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)
  let η := h.unit.app (R.obj 𝒢)
  let ε := h.counit.app 𝒢
  have htriangle : η ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
    simpa [R, η, ε] using h.right_triangle_components 𝒢
  -- Map the right triangle through the stalk functor on the open subspace point.
  have hforget :
      ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map η) ≫
          ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map (R.map ε)) =
        𝟙 _ := by
    simpa using congrArg
      (fun k ↦ (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map k) htriangle
  simpa [R, η, ε] using congrArg
    (fun k ↦ (TopCat.Presheaf.stalkFunctor (Type u) xU).map k) hforget

/-- Helper for Lemma 6.31.9: on the inside branch `x ∈ U`, the counit stalk map followed by the
sheaf pullback stalk comparison is the canonical stalk identification from Lemma 6.31.7. -/
private theorem counit_stalk_map_comp_stalkPullbackIso_eq_of_mem
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) (x : X) (hx : x ∈ (U : Set X)) :
    let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
    let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
    let R := TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)
    let explicit :
        (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU) ≪≫
        ((TopCat.Presheaf.stalkFunctor (Type u) xU).mapIso
          ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
            (asIso (h.unit.app (R.obj 𝒢))))).symm
    ((TopCat.Presheaf.stalkFunctor (Type u) x).map (h.counit.app 𝒢).hom) ≫
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
      explicit.hom := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let R := TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso (C := Type u) U).hom.app
      (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor (Type u) xU).mapIso
        ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  change ((TopCat.Presheaf.stalkFunctor (Type u) x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
    explicit.hom
  -- Route correction: the inside-`U` stalk identity is now proved by the sheaf-level naturality
  -- of `stalkPullbackIso` and then the right triangle relation `R.map ε = inv η`.
  let e : R.obj 𝒢 ≅ R.obj ((j! U).obj (R.obj 𝒢)) :=
    (OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso (C := Type u) U).app (R.obj 𝒢)
  let eStalk :
      (((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
          ((j! U).obj (R.obj 𝒢))).presheaf.stalk xU) ≅
        (R.obj 𝒢).presheaf.stalk xU :=
    ((TopCat.Presheaf.stalkFunctor (Type u) xU).mapIso
      ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
        (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hright :
      R.map (h.counit.app 𝒢) = inv (h.unit.app (R.obj 𝒢)) := by
    apply (CategoryTheory.cancel_mono e.hom).1
    simpa [e, R] using h.right_triangle_components 𝒢
  -- First identify the counit composite with the stalk map of `R.map ε`.
  have hnat :
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
            xU).hom ≫
          ((TopCat.Presheaf.stalkFunctor (Type u) xU).map (R.map (h.counit.app 𝒢)).hom) := by
    simpa [R] using sheaf_stalkPullbackIso_hom_naturality
      (f := extensionByZeroOpenSubsetInclusion U) (η := h.counit.app 𝒢) (x := xU)
  rw [hnat]
  -- Then rewrite `R.map ε` using the right triangle, which exactly matches `explicit`.
  have hforget :
      (R.map (h.counit.app 𝒢)).hom =
        (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
          (inv (h.unit.app (R.obj 𝒢))) := by
    simpa [hright] using congrArg
      (fun k ↦ (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map k) hright
  letI :
      IsIso
        ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj 𝒢))) := by
    infer_instance
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor (Type u) xU).map
          ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
            (h.unit.app (R.obj 𝒢)))) := by
    infer_instance
  have hstalk :
      ((TopCat.Presheaf.stalkFunctor (Type u) xU).map (R.map (h.counit.app 𝒢)).hom) =
        eStalk.hom := by
    rw [hforget]
    have hforgetInv :
        (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
            (inv (h.unit.app (R.obj 𝒢))) =
          inv
            ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
              (h.unit.app (R.obj 𝒢))) := by
      exact Functor.map_inv (TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U))
        (h.unit.app (R.obj 𝒢))
    rw [hforgetInv]
    have heStalk :
        eStalk.hom =
          inv
            ((TopCat.Presheaf.stalkFunctor (Type u) xU).map
              ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) := by
      simp [eStalk]
    exact (Functor.map_inv (TopCat.Presheaf.stalkFunctor (Type u) xU)
      ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).map
        (h.unit.app (R.obj 𝒢)))).trans heStalk.symm
  have hcomp :
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        ((TopCat.Presheaf.stalkFunctor (Type u) xU).map (R.map (h.counit.app 𝒢)).hom) =
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫
        eStalk.hom := by
    simpa using congrArg
      (fun k ↦
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU).hom ≫ k)
      hstalk
  exact hcomp.trans (by simp [explicit, eStalk, Category.assoc])

/-- Helper for Lemma 6.31.9: at points of `U`, the counit is stalkwise an isomorphism. -/
private theorem counit_stalk_map_isIso_of_mem
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).counit.app
          𝒢).hom) := by
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let R := TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso (C := Type u) U).hom.app
      (R.obj 𝒢))
    infer_instance
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor (Type u) xU).mapIso
        ((TopCat.Sheaf.forget (Type u) (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor (Type u) x).map
            (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    rw [counit_stalk_map_comp_stalkPullbackIso_eq_of_mem U 𝒢 x hx]
    infer_instance
  -- Cancel the pullback stalk comparison on the right to recover the counit stalk map itself.
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor (Type u) x).map
              (h.counit.app 𝒢).hom) ≫
            (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) ≫
          inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

/-- Helper for Lemma 6.31.9: at points outside `U`, the counit is stalkwise an isomorphism as
soon as the target stalk is empty. -/
private theorem counit_stalk_map_isIso_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) (x : X) (hx : x ∉ (U : Set X))
    (hEmpty : IsEmpty (𝒢.presheaf.stalk x)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U).counit.app
          𝒢).hom) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  -- Outside `U`, the source stalk is initial by the extension-by-empty-set description.
  let hSource :
      IsInitial
        (((j! U).obj
            ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem (C := Type u) U
      ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
  -- The empty-target hypothesis identifies the target stalk with the initial object of `Type`.
  letI : IsIso (initial.to (𝒢.presheaf.stalk x)) :=
    (type_isIso_initial_to_iff_isEmpty _).mpr hEmpty
  let hTarget : IsInitial (𝒢.presheaf.stalk x) :=
    IsInitial.ofIso initialIsInitial (asIso (initial.to (𝒢.presheaf.stalk x)))
  exact
    isIso_of_isInitial hSource hTarget
      ((TopCat.Presheaf.stalkFunctor (Type u) x).map (h.counit.app 𝒢).hom)

-- Proof sketch: fully faithfulness is formal from `j⁻¹ j_! ≅ 𝟭`. For the essential image, use
-- the counit `j_! j⁻¹ 𝒢 ⟶ 𝒢`. On points outside `U`, the source stalk is initial, hence empty; on
-- points inside `U`, the stalk pullback comparison identifies the counit with the inverse of the
-- unit.
/-- Lemma 6.31.9: the functor
`j_! : Sh(U) ⥤ Sh(X)` is fully faithful, and its essential image consists exactly of the sheaves
whose stalks outside `U` are empty. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isEmpty_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf (Type u)) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) → IsEmpty (𝒢.presheaf.stalk x) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction (C := Type u) U
  let hFF :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))).FullyFaithful :=
    openSubsetSheafExtensionByInitialObject_fullyFaithful U
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))).Full :=
    hFF.full
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf (Type u) ⥤ X.Sheaf (Type u))).Faithful :=
    hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢 := by
    simpa using
      (h.isIso_counit_app_iff_mem_essImage : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    letI : IsIso (h.counit.app 𝒢) := hess.mpr h𝒢
    have hForget :
        IsIso ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢)) := by
      infer_instance
    letI : IsIso ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢)) := hForget
    have hMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢))) :=
      Functor.map_isIso (TopCat.Presheaf.stalkFunctor (Type u) x)
        ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢))
    letI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢))) :=
      hMap
    -- Outside `U`, the source stalk is initial, so the target stalk is initial as well.
    have hSource :
        IsInitial
          (((j! U).obj
              ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj
                𝒢)).presheaf.stalk x) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem (C := Type u)
        U ((TopCat.Sheaf.pullback (Type u) (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
    have hTarget : IsInitial (𝒢.presheaf.stalk x) :=
      IsInitial.ofIso hSource
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor (Type u) x).map
            ((TopCat.Sheaf.forget (Type u) X).map (h.counit.app 𝒢))) hMap)
    exact (Types.initial_iff_empty (𝒢.presheaf.stalk x)).mp ⟨hTarget⟩
  · intro h𝒢
    let ε := h.counit.app 𝒢
    have : IsIso ε := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      by_cases hx : x ∈ (U : Set X)
      · -- On `U`, the counit agrees stalkwise with the inverse of the unit.
        exact counit_stalk_map_isIso_of_mem U 𝒢 x hx
      · -- Outside `U`, the source stalk is initial and the target stalk is empty by hypothesis.
        exact counit_stalk_map_isIso_of_not_mem U 𝒢 x hx (h𝒢 x hx)
    exact hess.mp this

end

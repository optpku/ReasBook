module

public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Lemma_6_31_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

/-
Domain-style sampling for Lemma 6.31.10:
- primary domain: extension by zero / by the initial object for sheaves on an open subset, and the
  resulting essential-image criterion in terms of stalks;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- `source-facing`: the abelian reformulation saying the stalks vanish outside `U`;
- `core/canonical`: the extension-by-initial-object functor and its initial-stalk
  essential-image criterion;
- `bridge/view`: the `AddCommGrpCat` specialization converting the owner’s initial-stalk criterion
  into zero stalks via `isIsoZero_iff_source_target_isZero`.

The proof follows the source route: essential-image membership is equivalent to the counit being an
isomorphism for the extension-by-zero adjunction, and that counit is checked stalkwise. Outside
`U`, the source stalk is initial; inside `U`, the remaining comparison is the stalk pullback
naturality bridge for the open immersion.
-/

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable (U : Opens X)

/-- Helper for Lemma 6.31.10: in `AddCommGrpCat`, the unique morphism from the zero object to `A`
is an isomorphism exactly when `A` is a zero object. -/
private theorem addCommGrpCat_isIso_zero_iff_isZero (A : AddCommGrpCat.{u}) :
    IsIso (0 : ⊥_ AddCommGrpCat.{u} ⟶ A) ↔ IsZero A := by
  rw [isIsoZero_iff_source_target_isZero]
  constructor
  · rintro ⟨_, hA⟩
    exact hA
  · intro hA
    exact ⟨initialIsInitial.isZero, hA⟩

/-- Helper for Lemma 6.31.10: the presheaf stalk pullback isomorphism is natural in the presheaf
argument for sheaves of abelian groups. -/
private theorem presheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Presheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
        (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f 𝒢 x).hom =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} f ℱ x).hom ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η) := by
  -- Compare both morphisms after precomposing with every germ, where the owner pullback-stalk
  -- construction is defined.
  apply TopCat.Presheaf.stalk_hom_ext ℱ
  intro U hx
  let h₁ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) U (f x) hx η
  let h₂𝒢 := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f 𝒢 x U hx
  let h₂ℱ := TopCat.Presheaf.germ_stalkPullbackHom (C := AddCommGrpCat.{u}) f ℱ x U hx
  let h₃ := TopCat.Presheaf.stalkFunctor_map_germ (C := AddCommGrpCat.{u}) ((Opens.map f).obj U) x
    hx ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let A :=
    ℱ.germ U (f x) hx ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η ≫
      TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let B :=
    η.app (op U) ≫ 𝒢.germ U (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x
  let C :=
    η.app (op U) ≫
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app 𝒢).app
        (op U) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj U) x hx
  let D :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app (op U) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η).app (op ((Opens.map f).obj U)) ≫
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj U) x hx
  let E :=
    ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app (op U) ≫
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ).germ ((Opens.map f).obj U) x hx ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  let Z :=
    ℱ.germ U (f x) hx ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f ℱ x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η)
  have hA : A = B := by
    simpa [A, B, Category.assoc] using
      congrArg (fun k ↦ k ≫ TopCat.Presheaf.stalkPullbackHom AddCommGrpCat.{u} f 𝒢 x) h₁
  have hB : B = C := by
    simpa [B, C, Category.assoc] using congrArg (fun k ↦ η.app (op U) ≫ k) h₂𝒢
  have hC : C = D := by
    have hNat := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.naturality η)
      (op U)
    simpa [C, D, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢).germ ((Opens.map f).obj U)
            x hx)
        hNat
  have hD : D = E := by
    simpa [D, E, Category.assoc] using
      congrArg
        (fun k ↦
          ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app ℱ).app
              (op U) ≫
            k)
        h₃.symm
  have hE : E = Z := by
    simpa [E, Z, Category.assoc] using
      congrArg
        (fun k ↦
          k ≫
            (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η))
        h₂ℱ.symm
  exact hA.trans (hB.trans (hC.trans (hD.trans hE)))

/-- Helper for Lemma 6.31.10: the extension-by-zero functor is fully faithful because the unit of
the open-subset adjunction is an isomorphism. -/
private noncomputable abbrev extensionByZero_fullyFaithful :
    (((j! U) :
      (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤
        X.Sheaf AddCommGrpCat.{u})).FullyFaithful := by
  -- Fully faithfulness is formal once the adjunction unit is invertible.
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  letI : IsIso h.unit := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

/-- Helper for Lemma 6.31.10: after pulling back along `j : U ↪ X`, the counit is an isomorphism
because the right triangle identity identifies it with the inverse of the unit. -/
private theorem counit_pullback_map_isIso (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    IsIso
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  let η := h.unit.app (R.obj 𝒢)
  let ε := h.counit.app 𝒢
  have hη : IsIso η := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  have hright : η ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
    -- The right triangle identity shows that `R.map ε` is a right inverse to the unit.
    simpa [R, η, ε] using h.right_triangle_components_assoc 𝒢 (𝟙 (R.obj 𝒢))
  have hleft : R.map ε ≫ η = 𝟙 (R.obj ((j! U).obj (R.obj 𝒢))) := by
    -- Cancel the invertible unit on the left to obtain the left inverse as well.
    apply (CategoryTheory.cancel_epi η).1
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ η) hright
  exact ⟨⟨η, hleft, hright⟩⟩

/-- Helper for Lemma 6.31.10: after applying the stalk functor on the open subspace, the pullback
of the counit composes with the unit to the identity by the adjunction right triangle. -/
private theorem stalk_pullback_counit_comp_unit_eq_id
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) (xU : extensionByZeroOpenSubsetSpace U) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).unit.app
          ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            𝒢)).hom) ≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
          ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢)).hom)) =
      𝟙 _ := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  let η := h.unit.app (R.obj 𝒢)
  let ε := h.counit.app 𝒢
  have htriangle : η ≫ R.map ε = 𝟙 (R.obj 𝒢) := by
    simpa [R, η, ε] using h.right_triangle_components 𝒢
  -- Map the right triangle through the stalk functor on the open subspace point.
  have hforget :
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map η) ≫
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
            (R.map ε)) =
        𝟙 _ := by
    simpa using congrArg
      (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map k)
      htriangle
  simpa [R, η, ε] using congrArg
    (fun k ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map k) hforget

/-- Helper for Lemma 6.31.10: the sheaf stalk pullback isomorphism is natural in the sheaf
argument for sheaves of abelian groups. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Sheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : X) :
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
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).map η.hom)
  let τ𝒢 :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj 𝒢.presheaf)
  let τℱ :=
    CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} f).obj ℱ.presheaf)
  let π𝒢 :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map
      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{u} f).inv.app 𝒢)
  let πℱ :=
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map
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
        (J := Opens.grothendieckTopology X)
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
          (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} X).map k)
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

/-- Helper for Lemma 6.31.10: on the inside branch `x ∈ U`, the counit stalk map followed by the
sheaf pullback stalk comparison is the canonical stalk identification from Lemma 6.31.7. -/
private theorem counit_stalk_map_comp_stalkPullbackIso_eq_of_mem
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
    let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
    let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
    let explicit :
        (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
          xU) ≪≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
            (asIso (h.unit.app (R.obj 𝒢))))).symm
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app 𝒢).hom) ≫
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
      explicit.hom := by
  -- Route correction: isolate the inside-`U` composite equality before proving the final
  -- `IsIso` statement. This keeps the transport bookkeeping local to one adapter lemma.
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  letI : IsIso (h.unit.app (R.obj 𝒢)) := hunit
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app 𝒢).hom) ≫
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
    explicit.hom
  -- First package the stalk image of the unit isomorphism on the open subspace.
  let e : R.obj 𝒢 ≅ R.obj ((j! U).obj (R.obj 𝒢)) :=
    (OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).app (R.obj 𝒢)
  let eStalk :
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ((j! U).obj (R.obj 𝒢))).presheaf.stalk xU) ≅
        (R.obj 𝒢).presheaf.stalk xU :=
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
        (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hright :
      R.map (h.counit.app 𝒢) = inv (h.unit.app (R.obj 𝒢)) := by
    -- The right triangle identifies the pulled-back counit with the inverse unit.
    apply (CategoryTheory.cancel_mono e.hom).1
    simpa [e, R] using h.right_triangle_components 𝒢
  -- Move the original counit through the sheaf-level stalk pullback comparison.
  have hnat :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
            ((j! U).obj (R.obj 𝒢)) xU).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (R.map (h.counit.app 𝒢)).hom) := by
    simpa [R] using sheaf_stalkPullbackIso_hom_naturality
      (f := extensionByZeroOpenSubsetInclusion U) (η := h.counit.app 𝒢) (x := xU)
  rw [hnat]
  -- Rewrite the pulled-back counit by the inverse of the unit and map that identity to stalks.
  have hforget :
      (R.map (h.counit.app 𝒢)).hom =
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (inv (h.unit.app (R.obj 𝒢))) := by
    simpa [hright] using congrArg
      (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map k)
      hright
  letI :
      IsIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj 𝒢))) := by
    infer_instance
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
            (h.unit.app (R.obj 𝒢)))) := by
    infer_instance
  have hstalk :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map (R.map (h.counit.app 𝒢)).hom) =
        eStalk.hom := by
    rw [hforget]
    have hforgetInv :
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
            (inv (h.unit.app (R.obj 𝒢))) =
          inv
            ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (h.unit.app (R.obj 𝒢))) := by
      exact Functor.map_inv
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U))
        (h.unit.app (R.obj 𝒢))
    rw [hforgetInv]
    have heStalk :
        eStalk.hom =
          inv
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj 𝒢)))) := by
      simp [eStalk]
    exact
      (Functor.map_inv (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU)
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj 𝒢)))).trans heStalk.symm
  have hcomp :
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj 𝒢)) xU).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          (R.map (h.counit.app 𝒢)).hom) =
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj 𝒢)) xU).hom ≫
        eStalk.hom := by
    simpa using congrArg
      (fun k ↦
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj 𝒢)) xU).hom ≫ k)
      hstalk
  exact hcomp.trans (by simp [explicit, eStalk, Category.assoc])

/-- Helper for Lemma 6.31.10: at points of `U`, the counit should be stalkwise invertible because
the pullback of the counit is inverse to the unit and the stalk pullback comparison is natural. -/
private theorem counit_stalk_map_isIso_of_mem
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢).hom) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj 𝒢)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj 𝒢))
    infer_instance
  let explicit :
      (((j! U).obj (R.obj 𝒢)).presheaf.stalk x) ≅ (R.obj 𝒢).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj 𝒢))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj 𝒢))))).symm
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (h.counit.app 𝒢).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    rw [counit_stalk_map_comp_stalkPullbackIso_eq_of_mem (U := U) 𝒢 x hx]
    infer_instance
  -- Cancel the pullback stalk comparison on the right to recover the counit stalk map itself.
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              (h.counit.app 𝒢).hom) ≫
            (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) ≫
          inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

/-- Helper for Lemma 6.31.10: outside `U`, the source stalk of the counit is initial, so a zero
target stalk forces the counit map on stalks to be an isomorphism. -/
private theorem counit_stalk_map_isIso_of_not_mem
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ (U : Set X))
    (hZero : IsZero (𝒢.presheaf.stalk x)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U).counit.app 𝒢).hom) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  -- Outside `U`, the extension-by-zero stalk is initial by the owner theorem from Lemma 6.31.7.
  let hSource :
      IsInitial
        (((j! U).obj
            ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
              𝒢)).presheaf.stalk x) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
  letI : IsIso (0 : ⊥_ AddCommGrpCat.{u} ⟶ 𝒢.presheaf.stalk x) :=
    (addCommGrpCat_isIso_zero_iff_isZero _).mpr hZero
  let hTarget : IsInitial (𝒢.presheaf.stalk x) :=
    IsInitial.ofIso initialIsInitial (asIso (0 : ⊥_ AddCommGrpCat.{u} ⟶ 𝒢.presheaf.stalk x))
  exact
    isIso_of_isInitial hSource hTarget
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app 𝒢).hom)

-- Proof sketch: fully faithfulness is formal from the unit isomorphism. For the essential image,
-- use the counit `j_! j^{-1} 𝒢 ⟶ 𝒢`. Outside `U`, the source stalk is initial, hence zero after
-- transport; on `U`, the missing Lean-specific ingredient is the stalk pullback naturality bridge.
/-- Lemma 6.31.10: a sheaf of abelian groups on `X` lies in the essential image of extension by
zero from `U` if and only if its stalks vanish at every point of `X \ U`. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_stalk_isZero_of_not_mem
    (𝒢 : X.Sheaf AddCommGrpCat.{u}) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsZero (𝒢.presheaf.stalk x) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let hFF :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤
          X.Sheaf AddCommGrpCat.{u})).FullyFaithful :=
    extensionByZero_fullyFaithful (U := U)
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤
          X.Sheaf AddCommGrpCat.{u})).Full :=
    hFF.full
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u} ⥤
          X.Sheaf AddCommGrpCat.{u})).Faithful :=
    hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢 := by
    -- For a fully faithful left adjoint, essential-image membership is equivalent to the counit
    -- being an isomorphism.
    simpa using
      (h.isIso_counit_app_iff_mem_essImage : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    letI : IsIso (h.counit.app 𝒢) := hess.mpr h𝒢
    have hForget :
        IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢)) := by
      infer_instance
    letI : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢)) := hForget
    have hMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢))) :=
      Functor.map_isIso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢))
    letI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢))) :=
      hMap
    -- Outside `U`, the source stalk is initial, so the target stalk is initial as well.
    have hSource :
        IsInitial
          (((j! U).obj
              ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                𝒢)).presheaf.stalk x) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)
        hx
    have hTarget : IsInitial (𝒢.presheaf.stalk x) :=
      IsInitial.ofIso hSource
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map (h.counit.app 𝒢))) hMap)
    exact
      (addCommGrpCat_isIso_zero_iff_isZero (A := 𝒢.presheaf.stalk x)).mp
        (isIso_of_isInitial initialIsInitial hTarget
          (0 : ⊥_ AddCommGrpCat.{u} ⟶ 𝒢.presheaf.stalk x))
  · intro h𝒢
    let ε := h.counit.app 𝒢
    have hε : IsIso ε := by
      -- The counit is an isomorphism once it is stalkwise invertible.
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      by_cases hx : x ∈ (U : Set X)
      · exact counit_stalk_map_isIso_of_mem (U := U) 𝒢 x hx
      · exact counit_stalk_map_isIso_of_not_mem (U := U) 𝒢 x hx (h𝒢 x hx)
    exact hess.mp hε

end

module

public import Mathlib.CategoryTheory.Sites.CoversTop
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Definition_6_15_1
public import stacks_project.Chap06.Glueing_data_for_sheaves_on_an_open_cover
public import stacks_project.Chap06.Lemma_6_21_6
public import stacks_project.Chap06.Lemma_6_15_2
public import stacks_project.Chap06.Lemma_6_30_3
public import stacks_project.Chap06.Basis_extension_preserves_stalks
public import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}}

local instance : HasLimits (Type w) := inferInstance
local instance : HasColimits (Type w) := inferInstance
local instance : PreservesLimits (forget (Type w)) := inferInstance
local instance : PreservesFilteredColimits (forget (Type w)) :=
  PreservesColimits.preservesFilteredColimits (forget (Type w))
local instance : (forget (Type w)).ReflectsIsomorphisms := inferInstance

@[simp] theorem sheaf_id_hom_app {Y : TopCat.{w}} (G : Y.Sheaf (Type w)) (V) :
    ((𝟙 G : G ⟶ G).hom.app V) = 𝟙 _ := rfl

/-- Helper for Lemma 6.33.3: uniqueness of left adjoints is compatible with replacing the
second factor in a composite adjunction. -/
theorem leftAdjointUniq_comp_second_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ F₁₂' : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₁₂' : F₁₂' ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂')).hom.app X =
      (Adjunction.leftAdjointUniq adj₁₂ adj₁₂').hom.app (F₀₁.obj X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂'.obj (F₀₁.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁.comp adj₁₂')).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        ((adj₁₂.leftAdjointUniq adj₁₂').hom.app (F₀₁.obj X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂') X]
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁₂ adj₁₂' (F₀₁.obj X)
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h.symm

/-- Helper for Lemma 6.33.3: uniqueness of left adjoints is compatible with replacing the
first factor in a composite adjunction. -/
theorem leftAdjointUniq_comp_first_app
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ F₀₁' : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₀₁' : F₀₁' ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂)).hom.app X =
      F₁₂.map ((Adjunction.leftAdjointUniq adj₀₁ adj₀₁').hom.app X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂.obj (F₀₁'.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁'.comp adj₁₂)).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (F₁₂.map ((adj₀₁.leftAdjointUniq adj₀₁').hom.app X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂) X]
  let α := (adj₀₁.leftAdjointUniq adj₀₁').hom.app X
  have h₁ : adj₀₁.unit.app X ≫ G₁₀.map α = adj₀₁'.unit.app X := by
    simpa [α] using Adjunction.unit_leftAdjointUniq_hom_app adj₀₁ adj₀₁' X
  have h₂ :
      α ≫ adj₁₂.unit.app (F₀₁'.obj X) =
        adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α) := by
    simpa [α] using adj₁₂.unit.naturality α
  have hcalc :
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) =
        adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
          G₁₀.map (G₂₁.map (F₁₂.map α)) := by
    calc
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))
          =
        (adj₀₁.unit.app X ≫ G₁₀.map α) ≫
          G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))) h₁.symm
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map (α ≫ adj₁₂.unit.app (F₀₁'.obj X)) := by
            simp [Functor.map_comp, Category.assoc]
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map
            (adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α)) := by
            simpa using congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h₂
      _ =
      adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
        G₁₀.map (G₂₁.map (F₁₂.map α)) := by
          simp [Functor.map_comp]
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp,
    Category.assoc, α] using hcalc

/-- The open subspace attached to an inclusion `W ⊆ U`. -/
abbrev openSubsetHomOfLE {W U : Opens X} (h : W ≤ U) :
    openSubsetSpace W ⟶ openSubsetSpace U :=
  (Opens.toTopCat X).map (homOfLE h)

abbrev openSubsetRestrictionFunctor {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) ⥤ Opens (openSubsetSpace W) :=
  Opens.map (openSubsetHomOfLE h)

/-- Helper for Lemma 6.33.3: the inverse-image functor on opens induced by an inclusion
`W ⊆ U` is continuous for the canonical Grothendieck topologies. -/
theorem openSubsetRestrictionFunctor_isContinuous {W U : Opens X} (h : W ≤ U) :
    (openSubsetRestrictionFunctor h).IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace U))
      (Opens.grothendieckTopology (openSubsetSpace W)) := by
  -- This is the standard continuity instance for inverse image on opens.
  infer_instance

/-- The inclusion `W ↪ U ↪ X` is the inclusion `W ↪ X`. -/
@[simp] theorem openSubsetHomOfLE_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    openSubsetHomOfLE h ≫ openSubsetInclusion U = openSubsetInclusion W :=
  rfl

/-- Helper for Lemma 6.33.3: the open-subspace inclusions induced by nested open subsets compose
as expected. -/
@[simp] theorem openSubsetHomOfLE_comp {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    openSubsetHomOfLE hAB ≫ openSubsetHomOfLE hBC =
      openSubsetHomOfLE (hAB.trans hBC) := by
  -- The induced map on open subspaces is defined from `homOfLE`, so composition is definitional.
  rfl

/-- Helper for Lemma 6.33.3: inverse-image functors on opens induced by nested inclusions
compose to the inverse-image functor of the composite inclusion. -/
theorem openSubsetRestrictionFunctor_comp {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C) :
    openSubsetRestrictionFunctor hBC ⋙ openSubsetRestrictionFunctor hAB =
      openSubsetRestrictionFunctor (hAB.trans hBC) := by
  -- Both functors are `Opens.map` for the same composite open inclusion.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro V W i
  rfl

/-- Helper for Lemma 6.33.3: restricting from `X` to `U` and then internally to `W ⊆ U`
agrees on opens with restricting directly from `X` to `W`. -/
theorem openSubsetRestrictionFunctor_comp_inclusion {W U : Opens X} (h : W ≤ U) :
    (Opens.map (openSubsetInclusion U)) ⋙ openSubsetRestrictionFunctor h =
      Opens.map (openSubsetInclusion W) := by
  -- This is the functor-level version of `openSubsetHomOfLE_comp_inclusion`.
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro V W i
  rfl

/-- Helper for Lemma 6.33.3: the map induced by the identity inclusion of an open subset is the
identity morphism of the corresponding open subspace. -/
@[simp] theorem openSubsetHomOfLE_refl (W : Opens X) :
    openSubsetHomOfLE (show W ≤ W from le_rfl) = 𝟙 _ := by
  -- The identity inclusion induces the identity map on the open subspace.
  rfl

/-- Helper for Lemma 6.33.3: the ambient open `W ⊆ U` viewed as an open of `openSubsetSpace U`. -/
def subspaceOpenOfLE {W U : Opens X} (h : W ≤ U) :
    Opens (openSubsetSpace U) :=
  U.overEquivalence.functor.obj (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.3: an inclusion `A ⊆ B ⊆ U` gives a morphism between the represented
opens of the open subspace `U`. -/
def subspaceOpenHom {A B U : Opens X}
    (hA : A ≤ U) (hB : B ≤ U) (hAB : A ≤ B) :
    subspaceOpenOfLE hA ⟶ subspaceOpenOfLE hB :=
  U.overEquivalence.functor.map
    (Over.homMk (homOfLE hAB) (by
      apply Subsingleton.elim))

@[simp] theorem subspaceOpenHom_refl {W U : Opens X} (hWU : W ≤ U) :
    subspaceOpenHom hWU hWU (show W ≤ W from le_rfl) = 𝟙 _ := by
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.3: the inclusion functor from opens of `openSubsetSpace U` back to
ambient opens of `X`. -/
abbrev subspaceInclusionFunctor (U : Opens X) :
    Opens (openSubsetSpace U) ⥤ Opens X :=
  (Opens.isOpenEmbedding U).functor

/-- Helper for Lemma 6.33.3: the `Over`-equivalence for `U` remembers the ambient open that
produced a given open of `openSubsetSpace U`. -/
theorem overEquivalenceFunctorObjEq
    (U : Opens X) (V : Over U) :
    (subspaceInclusionFunctor U).obj (U.overEquivalence.functor.obj V) = V.left := by
  -- The represented open in the subspace has exactly the ambient points of `V.left`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, (leOfHom V.hom) hx⟩, hx, rfl⟩

/-- Helper for Lemma 6.33.3: viewing `W ⊆ U` as an open of `openSubsetSpace U` and then including
it back into `X` recovers the original ambient open `W`. -/
theorem subspaceOpenOfLEImageEq
    {W U : Opens X} (h : W ≤ U) :
    (subspaceInclusionFunctor U).obj (subspaceOpenOfLE h) = W := by
  -- Specialize the `Over U` comparison to the arrow `W ⟶ U`.
  simpa [subspaceOpenOfLE] using
    overEquivalenceFunctorObjEq U (Over.mk (homOfLE h))

/-- Helper for Lemma 6.33.3: every open of `openSubsetSpace U` is represented by an ambient open
contained in `U`. -/
theorem openSubsetOpenRepresentation
    {U : Opens X} (V : Opens (openSubsetSpace U)) :
    ∃ W : Opens X, ∃ hW : W ≤ U, subspaceOpenOfLE hW = V := by
  let OV : Over U := U.overEquivalence.inverse.obj V
  let hW : OV.left ≤ U := leOfHom OV.hom
  refine ⟨OV.left, hW, ?_⟩
  -- The `Over U ≌ Opens (openSubsetSpace U)` counit identifies `V` with its represented ambient
  -- open.
  have hEq : U.overEquivalence.functor.obj OV = V := by
    ext x
    constructor
    · intro hx
      exact (leOfHom ((U.overEquivalence.counitIso.app V).hom)) hx
    · intro hx
      exact (leOfHom ((U.overEquivalence.counitIso.app V).inv)) hx
  simpa [subspaceOpenOfLE, OV, hW] using hEq

/-- Helper for Lemma 6.33.3: membership in an open of `openSubsetSpace U` is equivalent to
membership of the underlying point in its ambient image in `X`. -/
theorem memSubspaceOpenIff
    {U : Opens X} (A : Opens (openSubsetSpace U)) (x : openSubsetSpace U) :
    x ∈ A ↔ x.1 ∈ (subspaceInclusionFunctor U).obj A := by
  -- The image-open description records exactly the same points as the subspace open itself.
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    cases Subtype.ext hxy
    simpa using hy

/-- Helper for Lemma 6.33.3: membership in the represented open `subspaceOpenOfLE h` is exactly
membership in the ambient open `W`. -/
theorem memSubspaceOpenOfLE_iff
    {W U : Opens X} (h : W ≤ U) (x : openSubsetSpace U) :
    x ∈ subspaceOpenOfLE h ↔ x.1 ∈ W := by
  -- Rewrite membership in the subspace open through its ambient image in `X`.
  simpa [subspaceOpenOfLEImageEq] using
    (memSubspaceOpenIff (subspaceOpenOfLE h) x)

/-- Helper for Lemma 6.33.3: inside `openSubsetSpace D`, the represented open of `A ∩ B`
is the intersection of the represented opens of `A` and `B`. -/
@[simp] theorem subspaceOpenOfLE_inf_eq
    {A B D : Opens X} (hAD : A ≤ D) (hBD : B ≤ D) :
    subspaceOpenOfLE (show A ⊓ B ≤ D from le_trans inf_le_left hAD) =
      subspaceOpenOfLE hAD ⊓ subspaceOpenOfLE hBD := by
  ext x
  constructor
  · intro hx
    have hxAB : x.1 ∈ A ∧ x.1 ∈ B := by
      simpa [subspaceOpenOfLEImageEq] using
        (memSubspaceOpenIff (subspaceOpenOfLE
          (show A ⊓ B ≤ D from le_trans inf_le_left hAD)) x).1 hx
    exact ⟨
      (memSubspaceOpenIff (subspaceOpenOfLE hAD) x).2
        (by simpa [subspaceOpenOfLEImageEq] using hxAB.1),
      (memSubspaceOpenIff (subspaceOpenOfLE hBD) x).2
        (by simpa [subspaceOpenOfLEImageEq] using hxAB.2)⟩
  · rintro ⟨hxA, hxB⟩
    exact
      (memSubspaceOpenIff (subspaceOpenOfLE
        (show A ⊓ B ≤ D from le_trans inf_le_left hAD)) x).2
        (by
          have hxA' : x.1 ∈ A := by
            simpa [subspaceOpenOfLEImageEq] using
              (memSubspaceOpenIff (subspaceOpenOfLE hAD) x).1 hxA
          have hxB' : x.1 ∈ B := by
            simpa [subspaceOpenOfLEImageEq] using
              (memSubspaceOpenIff (subspaceOpenOfLE hBD) x).1 hxB
          simpa [subspaceOpenOfLEImageEq] using And.intro hxA' hxB')

/-- Helper for Lemma 6.33.3: points of `openSubsetSpace W` land in the represented open
`subspaceOpenOfLE h` after applying the inclusion `W ↪ U`. -/
theorem openSubsetHomOfLE_mem_subspaceOpenOfLE
    {W U : Opens X} (h : W ≤ U) (x : openSubsetSpace W) :
    openSubsetHomOfLE h x ∈ subspaceOpenOfLE h := by
  -- The underlying point already lies in `W`, and `memSubspaceOpenOfLE_iff` turns that into the
  -- desired membership statement on `openSubsetSpace U`.
  exact (memSubspaceOpenOfLE_iff h (openSubsetHomOfLE h x)).2 x.property

/-- The map of open subspaces induced by an inclusion `W ⊆ U` is an open embedding. -/
theorem openSubsetHomOfLE_isOpenEmbedding {W U : Opens X} (h : W ≤ U) :
    IsOpenEmbedding (openSubsetHomOfLE h) := by
  exact IsLocalHomeomorph.isOpenEmbedding_of_comp
    U.isOpenEmbedding.isLocalHomeomorph
    (by simpa [Function.comp, openSubsetHomOfLE_comp_inclusion] using W.isOpenEmbedding)
    (by continuity)

/-- Helper for Lemma 6.33.3: restricting an ambient open `A ⊆ B` along the inclusion `B ⊆ C`
produces the subspace open of `C` represented by the same ambient open `A`. -/
theorem openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB)) =
      subspaceOpenOfLE (hAB.trans hBC) := by
  -- Compare both subspace opens through their ambient images in `X`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyA : y.1 ∈ A := by
      simpa [subspaceOpenOfLEImageEq] using
        (memSubspaceOpenIff (subspaceOpenOfLE hAB) y).1 hy
    exact
      (memSubspaceOpenIff (subspaceOpenOfLE (hAB.trans hBC)) (openSubsetHomOfLE hBC y)).2
        (by simpa [subspaceOpenOfLEImageEq, openSubsetHomOfLE] using hyA)
  · intro hx
    have hxA : x.1 ∈ A := by
      simpa [subspaceOpenOfLEImageEq] using
        (memSubspaceOpenIff (subspaceOpenOfLE (hAB.trans hBC)) x).1 hx
    refine ⟨⟨x.1, hAB hxA⟩, ?_, ?_⟩
    · exact (memSubspaceOpenIff (subspaceOpenOfLE hAB) ⟨x.1, hAB hxA⟩).2
        (by simpa [subspaceOpenOfLEImageEq] using hxA)
    · exact Subtype.ext rfl

/-- Helper for Lemma 6.33.3: after identifying the source and target opens via
`openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE`, the open-embedding functor map is the canonical
inclusion between the corresponding represented opens. -/
theorem openSubsetHomOfLEFunctorMapEqSubspaceOpenHom
    {A₁ A₂ B C : Opens X}
    (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B) (h12 : A₁ ≤ A₂) (hBC : B ≤ C) :
    eqToHom
        (by
          simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]) ≫
      (openSubsetHomOfLE_isOpenEmbedding hBC).functor.map
        (subspaceOpenHom hA₁ hA₂ h12) =
      subspaceOpenHom (hA₁.trans hBC) (hA₂.trans hBC) h12 ≫
        eqToHom
          (by
            simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]) := by
  apply Subsingleton.elim

/-- Helper for Lemma 6.33.3: the open-embedding pullback along `B ⊆ C`, evaluated on the
represented open `A ⊆ B`, is the original sheaf evaluated on `A ⊆ C`. -/
noncomputable def openSubsetHomOfLEOpenEmbeddingSectionIso
    {C : Type (w + 1)} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    (ℱ : TopCat.Sheaf C (openSubsetSpace D)) :
    ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).obj ℱ)).1.obj
        (op (subspaceOpenOfLE hAB)) ≅
      ℱ.1.obj (op (subspaceOpenOfLE (hAB.trans hBD))) :=
  eqToIso (by
    change
      ℱ.1.obj
          (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj (subspaceOpenOfLE hAB))) =
        ℱ.1.obj (op (subspaceOpenOfLE (hAB.trans hBD)))
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBD))

/-- Helper for Lemma 6.33.3: equality of sheaf morphisms gives equality on sections over any
chosen open. -/
theorem sheafHomAppCongr
    {C : Type (w + 1)} [Category.{w} C]
    {Y : TopCat.{w}} {ℱ 𝒢 : TopCat.Sheaf C Y} {V : Opens Y} {α β : ℱ ⟶ 𝒢}
    (h : α = β) :
    α.hom.app (op V) = β.hom.app (op V) := by
  cases h
  rfl

/-- Helper for Lemma 6.33.3: the section comparison for an open-subspace inclusion commutes with
restriction from a larger represented open to a smaller one. -/
theorem openSubsetHomOfLEOpenEmbeddingSectionIso_naturality
    {C : Type (w + 1)} [Category.{w} C]
    {A₁ A₂ B D : Opens X} (hA₁ : A₁ ≤ B) (hA₂ : A₂ ≤ B)
    (h12 : A₁ ≤ A₂) (hBD : B ≤ D)
    (ℱ : TopCat.Sheaf C (openSubsetSpace D)) :
    ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).obj ℱ)).1.map
        (subspaceOpenHom hA₁ hA₂ h12).op ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso hA₁ hBD ℱ).hom =
    (openSubsetHomOfLEOpenEmbeddingSectionIso hA₂ hBD ℱ).hom ≫
      ℱ.1.map (subspaceOpenHom (hA₁.trans hBD) (hA₂.trans hBD) h12).op := by
  let p₁ :
      ℱ.1.obj
          (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj
            (subspaceOpenOfLE hA₁))) =
        ℱ.1.obj (op (subspaceOpenOfLE (hA₁.trans hBD))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hA₁ hBD)
  let p₂ :
      ℱ.1.obj
          (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj
            (subspaceOpenOfLE hA₂))) =
        ℱ.1.obj (op (subspaceOpenOfLE (hA₂.trans hBD))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hA₂ hBD)
  have hmap := congrArg (fun k ↦ ℱ.1.map k.op)
    (openSubsetHomOfLEFunctorMapEqSubspaceOpenHom hA₁ hA₂ h12 hBD)
  simpa [openSubsetHomOfLEOpenEmbeddingSectionIso, Topology.IsOpenEmbedding.sheafPullback,
    p₁, p₂, Functor.map_comp, Category.assoc, eqToHom_map] using hmap

/-- Helper for Lemma 6.33.3: the section comparison for an open-subspace inclusion is natural in
the sheaf being restricted. -/
theorem openSubsetHomOfLEOpenEmbeddingSectionIso_map_naturality
    {C : Type (w + 1)} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    {ℱ 𝒢 : TopCat.Sheaf C (openSubsetSpace D)} (η : ℱ ⟶ 𝒢) :
    ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
        (op (subspaceOpenOfLE hAB))) ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).hom =
    (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD ℱ).hom ≫
      η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD))) := by
  let pℱ :
      ℱ.1.obj
          (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj
            (subspaceOpenOfLE hAB))) =
        ℱ.1.obj (op (subspaceOpenOfLE (hAB.trans hBD))) := by
    simpa using congrArg (fun V ↦ ℱ.1.obj (op V))
      (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBD)
  let p𝒢 :
      𝒢.1.obj
          (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj
            (subspaceOpenOfLE hAB))) =
        𝒢.1.obj (op (subspaceOpenOfLE (hAB.trans hBD))) := by
    simpa using congrArg (fun V ↦ 𝒢.1.obj (op V))
      (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBD)
  have hnat :=
    η.hom.naturality
      (eqToHom (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBD).symm).op
  change η.hom.app
        (op ((openSubsetHomOfLE_isOpenEmbedding hBD).functor.obj (subspaceOpenOfLE hAB))) ≫
      eqToHom p𝒢 =
    eqToHom pℱ ≫ η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD)))
  simpa [pℱ, p𝒢, eqToHom_map] using hnat.symm

/-- Helper for Lemma 6.33.3: pulling back a sheaf morphism along an open-subspace inclusion is
the same as conjugating by the section-comparison isomorphisms. -/
theorem openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
    {C : Type (w + 1)} [Category.{w} C]
    {A B D : Opens X} (hAB : A ≤ B) (hBD : B ≤ D)
    {ℱ 𝒢 : TopCat.Sheaf C (openSubsetSpace D)} (η : ℱ ⟶ 𝒢) :
    (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD ℱ).hom ≫
      η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD))) ≫
      (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).inv =
    ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
      (op (subspaceOpenOfLE hAB))) := by
  have hnat :=
    openSubsetHomOfLEOpenEmbeddingSectionIso_map_naturality
      (hAB := hAB) (hBD := hBD) (η := η)
  calc
    (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD ℱ).hom ≫
        η.hom.app (op (subspaceOpenOfLE (hAB.trans hBD))) ≫
        (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).inv
        =
      ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
          (op (subspaceOpenOfLE hAB)) ≫
        (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).hom) ≫
          (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).inv := by
            rw [hnat]
            simp [Category.assoc]
    _ =
      ((((openSubsetHomOfLE_isOpenEmbedding hBD).sheafPullback C).map η).hom.app
        (op (subspaceOpenOfLE hAB))) := by
          rw [Category.assoc,
            (openSubsetHomOfLEOpenEmbeddingSectionIso hAB hBD 𝒢).hom_inv_id]
          exact Category.comp_id _

namespace BasisCover

variable {B : Set (Opens X)} {U₀ : BasisOpen B}

/-- Helper for Lemma 6.33.3: the actual basis open `Uᵢ ∩ Uⱼ`, when that intersection is still in
the chosen basis. -/
abbrev actualIntersection
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) : BasisOpen B :=
  ⟨(𝒰.obj i).obj ⊓ (𝒰.obj j).obj, hInter i j⟩

abbrev actualIntersectionLeft
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actualIntersection 𝒰 hInter i j ⟶ 𝒰.obj i :=
  ⟨homOfLE inf_le_left⟩

abbrev actualIntersectionRight
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (i j : 𝒰.ι) :
    actualIntersection 𝒰 hInter i j ⟶ 𝒰.obj j :=
  ⟨homOfLE inf_le_right⟩

theorem isCompatible_iff_actualIntersections
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max w u} (BasisOpen B))
    (s : FamilyOfElementsOnObjects F 𝒰.obj) :
    s.IsCompatible ↔
      ∀ i j : 𝒰.ι,
        F.map ((actualIntersectionLeft 𝒰 hInter i j).op) (s i) =
          F.map ((actualIntersectionRight 𝒰 hInter i j).op) (s j) := by
  constructor
  · intro hs i j
    exact
      hs (actualIntersection 𝒰 hInter i j) i j
        (actualIntersectionLeft 𝒰 hInter i j)
        (actualIntersectionRight 𝒰 hInter i j)
  · intro hs Z i j f g
    let h : Z ⟶ actualIntersection 𝒰 hInter i j :=
      ⟨homOfLE (fun x hx ↦ ⟨f.hom.le hx, g.hom.le hx⟩)⟩
    have hf : f = h ≫ actualIntersectionLeft 𝒰 hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    have hg : g = h ≫ actualIntersectionRight 𝒰 hInter i j := by
      apply ObjectProperty.hom_ext
      exact Subsingleton.elim _ _
    calc
      F.map f.op (s i)
          = F.map ((actualIntersectionLeft 𝒰 hInter i j).op ≫ h.op) (s i) := by
              simp [hf]
      _ = F.map h.op (F.map ((actualIntersectionLeft 𝒰 hInter i j).op) (s i)) := by
              simp [FunctorToTypes.map_comp_apply]
      _ = F.map h.op (F.map ((actualIntersectionRight 𝒰 hInter i j).op) (s j)) := by
              rw [hs i j]
      _ = F.map ((actualIntersectionRight 𝒰 hInter i j).op ≫ h.op) (s j) := by
              simp [FunctorToTypes.map_comp_apply]
      _ = F.map g.op (s j) := by
              simp [hg, FunctorToTypes.map_comp_apply]

def singletonActualIntersectionCover
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B) :
    BasisIntersectionCover B 𝒰 where
  κ _ _ := PUnit
  obj i j _ := actualIntersection 𝒰 hInter i j
  left i j _ := actualIntersectionLeft 𝒰 hInter i j
  right i j _ := actualIntersectionRight 𝒰 hInter i j
  iUnion_eq i j := by
    ext x
    simp [actualIntersection]

theorem hasSheafCondition_iff_uniqueGluing_actualIntersections
    (𝒰 : BasisCover B U₀)
    (hInter : ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (F : Presheaf.{max w u} (BasisOpen B)) :
    BasisCover.HasSheafCondition F 𝒰 (singletonActualIntersectionCover 𝒰 hInter) ↔
      ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
        s.IsCompatible →
          ∃! t : F.obj (op U₀), ∀ i, F.map ((𝒰.hom i).op) t = s i := by
  constructor
  · intro h s hs
    exact h s (fun i j _ ↦ (isCompatible_iff_actualIntersections 𝒰 hInter F s).1 hs i j)
  · intro h s hs
    exact h s ((isCompatible_iff_actualIntersections 𝒰 hInter F s).2
      (fun i j ↦ hs i j PUnit.unit))

end BasisCover

theorem basisPresheaf_isSheaf_iff_uniqueGluing_on_cofinal_basis_covers_local
    {B : Set (Opens X)} (F : Presheaf.{max w u} (BasisOpen B))
    (Covers : ∀ U : BasisOpen B, Set (BasisCover B U))
    (hInterC :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ Covers U →
        ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ B)
    (hB : Opens.IsBasis B) (hC : BasisCover.IsCofinalSystem Covers) :
    Presheaf.IsSheaf (basisGrothendieckTopology B hB) F ↔
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ Covers U →
        ∀ s : FamilyOfElementsOnObjects F 𝒰.obj,
          s.IsCompatible →
            ∃! t : F.obj (op U), ∀ i, F.map ((𝒰.hom i).op) t = s i := by
  let hInter :
      ∀ ⦃U : BasisOpen B⦄ (𝒰 : BasisCover B U), 𝒰 ∈ Covers U →
        BasisIntersectionCover B 𝒰 :=
    fun {U} 𝒰 h𝒰 ↦
      BasisCover.singletonActualIntersectionCover 𝒰 (hInterC 𝒰 h𝒰)
  constructor
  · intro hSheaf U 𝒰 h𝒰
    exact
      (BasisCover.hasSheafCondition_iff_uniqueGluing_actualIntersections 𝒰
        (hInterC 𝒰 h𝒰) F).1
        ((basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem
          F Covers hInter hB hC).1 hSheaf 𝒰 h𝒰)
  · intro hUnique
    refine (basisPresheaf_isSheaf_iff_hasSheafCondition_on_cofinalSystem
      F Covers hInter hB hC).2 ?_
    intro U 𝒰 h𝒰
    exact
      (BasisCover.hasSheafCondition_iff_uniqueGluing_actualIntersections 𝒰
        (hInterC 𝒰 h𝒰) F).2
        (hUnique 𝒰 h𝒰)

/-- Helper for Lemma 6.33.3: evaluating the pullback of a ring sheaf from `C` to `B` on the
represented open `A ⊆ B` agrees with evaluating the original ring sheaf on the represented open
`A ⊆ C`. -/
noncomputable def openSubsetHomOfLESectionIso
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (𝒪 : TopCat.Sheaf RingCat (openSubsetSpace C)) :
    (((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hBC)).obj 𝒪)).1.obj
        (op (subspaceOpenOfLE hAB)) ≅
      𝒪.1.obj (op (subspaceOpenOfLE (hAB.trans hBC))) :=
  -- First compare the actual pullback with the open-embedding pullback model, then rewrite the
  -- represented test open via `openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE`.
  (((TopCat.Sheaf.forget RingCat (openSubsetSpace B)).mapIso
      (((openSubsetHomOfLE_isOpenEmbedding hBC).sheafPullbackIso RingCat).app 𝒪)).app
      (op (subspaceOpenOfLE hAB))) ≪≫
    eqToIso (by
      change
        𝒪.1.obj
            (op ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB))) =
          𝒪.1.obj (op (subspaceOpenOfLE (hAB.trans hBC)))
      simpa using congrArg (fun V ↦ 𝒪.1.obj (op V))
        (openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBC))

/-- Helper for Lemma 6.33.3: restricting the represented open `A ⊆ B` along `B ⊆ C` and then
including it back into `X` still remembers the ambient open `A`. -/
theorem restrictedRepresentedOpenImageEq
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) :
    (subspaceInclusionFunctor C).obj
        ((openSubsetHomOfLE_isOpenEmbedding hBC).functor.obj (subspaceOpenOfLE hAB)) = A := by
  -- Rewrite the restricted represented open to the direct represented open `A ⊆ C`.
  rw [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE hAB hBC, subspaceOpenOfLEImageEq]

/-- The inclusion `U ∩ V ↪ U` is an open embedding. -/
theorem openSubsetIntersectionLeftInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionLeftInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

/-- The inclusion `U ∩ V ↪ V` is an open embedding. -/
theorem openSubsetIntersectionRightInclusion_isOpenEmbedding (U V : Opens X) :
    IsOpenEmbedding (openSubsetIntersectionRightInclusion U V) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

theorem openSubsetTripleFirstInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleFirstInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

theorem openSubsetTripleSecondInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleSecondInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

theorem openSubsetTripleThirdInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleThirdInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_right

theorem openSubsetTripleToPairLeftInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairLeftInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding inf_le_left

theorem openSubsetTripleToPairCenterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairCenterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding (inf_le_inf inf_le_right le_rfl)

theorem openSubsetTripleToPairOuterInclusion_isOpenEmbedding
    (U V W : Opens X) :
    IsOpenEmbedding (openSubsetTripleToPairOuterInclusion U V W) :=
  openSubsetHomOfLE_isOpenEmbedding
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

/-- Helper for Lemma 6.33.3: `TopCat.Sheaf.pullbackComp` is the left-adjoint comparison
isomorphism for the definitional equality of composite pushforward functors. -/
theorem sheafPullbackComp_def {W Y Z : TopCat.{w}} (f : W ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullbackComp (A := Type w) f g =
      Adjunction.leftAdjointCompIso
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl)) := by
  -- This is the defining comparison between the two left adjoints to the same composite
  -- pushforward functor.
  rfl

/-- Helper for Lemma 6.33.3: the pushforward functors on sheaves satisfy the expected
associativity coherence for composite morphisms of spaces. -/
theorem sheaf_pushforward_assoc {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type w) f)
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl)) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) =
    (Functor.associator
      (TopCat.Sheaf.pushforward (Type w) f)
      (TopCat.Sheaf.pushforward (Type w) g)
      (TopCat.Sheaf.pushforward (Type w) h)).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso
          (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
            TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
        (TopCat.Sheaf.pushforward (Type w) h) ≪≫
      eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl) := by
  -- Both functor-level coherence paths are definitionally the same after evaluation on objects.
  ext ℱ
  rfl

/-- Helper for Lemma 6.33.3: the pullback-composition isomorphisms inherit associativity coherence
from the comparison of left adjoints to the same composite pushforward functor. -/
theorem sheaf_pullback_comp_assoc {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    Functor.isoWhiskerLeft _ (TopCat.Sheaf.pullbackComp (A := Type w) f g) ≪≫
      TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (TopCat.Sheaf.pullbackComp (A := Type w) g h) _ ≪≫
        TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h) := by
  -- Rewrite the pullback comparisons to `leftAdjointCompIso`, where the standard associativity
  -- coherence is already packaged.
  simpa [sheafPullbackComp_def] using
    (Adjunction.leftAdjointCompIso_assoc
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) h)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (g ≫ h))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g))
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type w) (f ≫ g ≫ h))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) g ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙ TopCat.Sheaf.pushforward (Type w) g =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) (f ≫ g) ⋙ TopCat.Sheaf.pushforward (Type w) h =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (eqToIso
        (show TopCat.Sheaf.pushforward (Type w) f ⋙
            TopCat.Sheaf.pushforward (Type w) (g ≫ h) =
          TopCat.Sheaf.pushforward (Type w) (f ≫ g ≫ h) from rfl))
      (sheaf_pushforward_assoc f g h))

/-- Helper for Lemma 6.33.3: the canonical pullback-composition comparisons satisfy the standard
pseudofunctor associativity identity in hom form. -/
theorem sheaf_pullback_pseudofunctor_associativity {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv ≫
        (Functor.isoWhiskerRight
          (TopCat.Sheaf.pullbackComp (A := Type w) g h)
          (TopCat.Sheaf.pullback (Type w) f)).inv ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.isoWhiskerLeft
          (TopCat.Sheaf.pullback (Type w) h)
          (TopCat.Sheaf.pullbackComp (A := Type w) f g)).hom ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom =
      eqToHom (by simp) := by
  -- Package the associativity coherence in the exact hom-shaped form used by endpoint rewrites.
  let e₁ := TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight
    (TopCat.Sheaf.pullbackComp (A := Type w) g h)
    (TopCat.Sheaf.pullback (Type w) f)
  let e₃ := Functor.isoWhiskerLeft
    (TopCat.Sheaf.pullback (Type w) h)
    (TopCat.Sheaf.pullbackComp (A := Type w) f g)
  let e₄ := TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have hcomp : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
    -- This is the hom-component form of `sheaf_pullback_comp_assoc`.
    exact congrArg Iso.hom (sheaf_pullback_comp_assoc f g h)
  rw [hcomp]
  ext X
  simpa using Iso.inv_hom_id_app e₁ X

/-- Helper for Lemma 6.33.3: cancelling the left comparison in pullback-composition coherence
identifies the forward endpoint with the direct restriction map. -/
theorem sheaf_pullback_forward_endpoint {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type w)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
        ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
      (TopCat.Sheaf.pullback (Type w) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
    (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
  have hassoc :
      (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    -- What remains is the forward component of the pullback associativity coherence.
    simpa only [Category.assoc] using
      (congrArg (fun α ↦ α.hom.app F) (sheaf_pullback_comp_assoc f g h)).symm
  have hrewrite :
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).hom.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) := by
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            t)
        hassoc
  have hassoc' :
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          ((TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) =
        ((TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    simp [Category.assoc]
  have hcancel :
      ((TopCat.Sheaf.pullbackComp (A := Type w) f g).inv.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F =
      (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F)
        (Iso.inv_hom_id_app
          (TopCat.Sheaf.pullbackComp (A := Type w) f g)
          ((TopCat.Sheaf.pullback (Type w) h).obj F))
  exact hrewrite.trans (hassoc'.trans hcancel)

/-- Helper for Lemma 6.33.3: cancelling the terminal direct restriction in the inverse
pullback-composition coherence yields the inverse endpoint map. -/
theorem sheaf_pullback_inverse_endpoint {W Y Z T : TopCat.{w}}
    (f : W ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (F : T.Sheaf (Type w)) :
    (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
      (TopCat.Sheaf.pullback (Type w) f).map
        ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
      (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
        ((TopCat.Sheaf.pullback (Type w) h).obj F) =
      (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
  have hcoh :
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F =
        eqToHom (by simp) := by
    -- This is exactly the pseudofunctor associativity identity on pullbacks.
    simpa only [Category.assoc] using
      congrArg (fun α ↦ α.app F) (sheaf_pullback_pseudofunctor_associativity f g h)
  have hid :
      eqToHom (by simp) =
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F := by
    -- The direct comparison composed with its inverse is the identity.
    simpa using
      (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h) F).symm
  have hrewrite :
      (TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
          (TopCat.Sheaf.pullback (Type w) f).map
            ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
            ((TopCat.Sheaf.pullback (Type w) h).obj F) =
        ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    simpa only [Category.assoc] using
      congrArg
        (fun t ↦
          ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F)) ≫
            t)
        (Iso.hom_inv_id_app
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h)
          F).symm
  have hcoh' :
      ((TopCat.Sheaf.pullbackComp (A := Type w) f (g ≫ h)).inv.app F ≫
            (TopCat.Sheaf.pullback (Type w) f).map
              ((TopCat.Sheaf.pullbackComp (A := Type w) g h).inv.app F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) f g).hom.app
              ((TopCat.Sheaf.pullback (Type w) h).obj F) ≫
            (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).hom.app F) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F =
        eqToHom (by simp) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    rw [hcoh]
  have hcancel :
      eqToHom (by simp) ≫
          (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F =
        (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F := by
    simpa [hid, Category.assoc] using
      congrArg
        (fun t ↦ t ≫ (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h).inv.app F)
            (Iso.inv_hom_id_app (TopCat.Sheaf.pullbackComp (A := Type w) (f ≫ g) h) F)
  exact hrewrite.trans (hcoh'.trans hcancel)

end

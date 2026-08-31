module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_43_2
public import stacks_project.Chap07.Lemma_7_21_1
public import stacks_project.Chap07.Lemma_7_21_7
public import stacks_project.Chap07.Lemma_7_27_4
public import stacks_project.Chap07.Lemma_7_29_5
public import stacks_project.Chap07.Lemma_7_30_3
public import stacks_project.Chap07.Lemma_7_30_5
public import stacks_project.Chap07.Lemma_7_30_7

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

universe u v w u₁ v₁

namespace CategoryTheory

open Functor.IsDenseSubsite

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Helper for Lemma 7.43.3: if an object `A` is subterminal, then forgetting the slice structure
over `A` is full. -/
theorem over_forget_full_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    (Over.forget A).Full where
  map_surjective {X Y} f := by
    -- Subterminality forces the compatibility triangle with `A` automatically.
    have hcomm : f ≫ Y.hom = X.hom := hA _ _
    exact ⟨Over.homMk f hcomm, rfl⟩

/-- Helper for Lemma 7.43.3: if forgetting the slice structure over `A` is full, then `A` is
subterminal. -/
theorem isSubterminal_of_over_forget_full
    {A : Sheaf J (Type w)} [hfull : (Over.forget A).Full] :
    IsSubterminal A := by
  intro Z f g
  let X : Over A := Over.mk f
  let Y : Over A := Over.mk g
  let idZ : X.left ⟶ Y.left := by
    change Z ⟶ Z
    exact 𝟙 Z
  obtain ⟨k, hk⟩ := Functor.map_surjective (F := Over.forget A) (X := X) (Y := Y) idZ
  have hk_left : k.left = 𝟙 Z := by
    simpa [idZ] using hk
  -- The defining commutativity of a slice morphism recovers the equality of the two maps to `A`.
  have hw : k.left ≫ Y.hom = X.hom := Over.w k
  simpa [X, Y, hk_left] using hw.symm

/-- Helper for Lemma 7.43.3: an object is subterminal exactly when forgetting its slice structure
is full. -/
theorem isSubterminal_iff_over_forget_full
    {A : Sheaf J (Type w)} :
    IsSubterminal A ↔ (Over.forget A).Full := by
  constructor
  · intro hA
    exact over_forget_full_of_isSubterminal (J := J) hA
  · intro hfull
    letI : (Over.forget A).Full := hfull
    exact isSubterminal_of_over_forget_full (J := J)

/-- Helper for Lemma 7.43.3: if the unit of `Over.forget A ⊣ Over.star A` is invertible on
every slice object, then `A` is subterminal. -/
theorem isSubterminal_of_forgetAdjStar_unit_app_isIso
    {A : Sheaf J (Type w)}
    (hunit : ∀ Y : Over A, IsIso ((Over.forgetAdjStar A).unit.app Y)) :
    IsSubterminal A := by
  -- Componentwise invertibility upgrades the whole unit to an isomorphism, so the left adjoint
  -- `Over.forget A` is fully faithful.
  haveI : ∀ Y : Over A, IsIso ((Over.forgetAdjStar A).unit.app Y) := hunit
  haveI : IsIso (Over.forgetAdjStar A).unit := NatIso.isIso_of_isIso_app _
  let hff : (Over.forget A).FullyFaithful :=
    (Over.forgetAdjStar A).fullyFaithfulLOfIsIsoUnit
  letI : (Over.forget A).Full := hff.full
  -- Fullness of the slice forgetful functor is the earlier subterminality criterion.
  exact isSubterminal_of_over_forget_full (J := J)

/-- Helper for Lemma 7.43.3: if a sheaf `A` is subterminal, then the slice forgetful functor
`Over.forget A` is fully faithful. -/
noncomputable instance over_forget_fullyFaithful_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    (Over.forget A).FullyFaithful := by
  -- Subterminality already supplies fullness, while faithfulness is built into slice forgetting.
  let hfull := over_forget_full_of_isSubterminal (J := J) hA
  letI : (Over.forget A).Full := hfull
  exact .ofFullyFaithful (Over.forget A)

/-- Helper for Lemma 7.43.3: if `A` is subterminal, then the unit map
`Y ⟶ (toOver A).obj Y.left` is an isomorphism for every object `Y` of `Over A`. -/
theorem forgetAdjToOver_unit_app_isIso_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) (Y : Over A) :
    IsIso ((forgetAdjToOver A).unit.app Y) := by
  -- Subterminality identifies the given structure map `Y.left ⟶ A` with the second projection.
  have hproj :
      CartesianMonoidalCategory.fst Y.left A ≫ Y.hom =
        CartesianMonoidalCategory.snd Y.left A := by
    exact hA _ _
  let inv : (toOver A).obj Y.left ⟶ Y :=
    Over.homMk
      (by
        simpa [toOver] using (CartesianMonoidalCategory.fst Y.left A))
      (by simpa [toOver] using hproj)
  -- The inverse is the first projection from the product defining `toOver A`.
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply Over.OverMorphism.ext
    simp [forgetAdjToOver, toOver, inv]
  · apply Over.OverMorphism.ext
    change
      CartesianMonoidalCategory.fst Y.left A ≫
          CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom =
        𝟙 (MonoidalCategoryStruct.tensorObj Y.left A)
    rw [CartesianMonoidalCategory.comp_lift]
    rw [hproj]
    rfl

/-- Helper for Lemma 7.43.3: if `A` is subterminal, then every object of the slice category
`Over A` lies in the essential image of `toOver A`. -/
theorem toOver_essSurj_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) :
    Functor.EssSurj (toOver A) := by
  refine ⟨?_⟩
  intro Y
  -- The previous unit isomorphism provides the required witness in the essential image.
  have hunit : IsIso ((forgetAdjToOver A).unit.app Y) :=
    forgetAdjToOver_unit_app_isIso_of_isSubterminal (J := J) hA Y
  exact ⟨Y.left, ⟨(asIso ((forgetAdjToOver A).unit.app Y)).symm⟩⟩

/-- Helper for Lemma 7.43.3: a sheaf lies in the essential image of `Over.forget A` exactly when
it admits a morphism to `A`. -/
theorem over_forget_essImage_iff_nonempty_hom
    {A X : Sheaf J (Type w)} :
    Functor.essImage (Over.forget A) X ↔ Nonempty (X ⟶ A) := by
  constructor
  · intro hX
    let Y : Over A := hX.witness
    let e : Y.left ≅ X := hX.getIso
    -- Read the slice witness as an actual map `X ⟶ A` by transporting along the image isomorphism.
    exact ⟨e.inv ≫ Y.hom⟩
  · rintro ⟨f⟩
    -- The map `f : X ⟶ A` is itself an object of `Over A`, so `X` is in the essential image.
    simpa using Functor.obj_mem_essImage (Over.forget A) (Over.mk f)

/-- Helper for Lemma 7.43.3: the sheaf `ℱ` itself lies in the essential image of the slice
forgetful functor via the terminal object `𝟙_ℱ : ℱ ⟶ ℱ`. -/
theorem terminal_mem_over_forget_essImage
    {ℱ : Sheaf J (Type w)} :
    Functor.essImage (Over.forget ℱ) ℱ := by
  -- The identity arrow of `ℱ` defines the terminal object of the slice over `ℱ`.
  simpa using Functor.obj_mem_essImage (Over.forget ℱ) (Over.mk (𝟙 ℱ))

/-- Helper for Lemma 7.43.3: every subtopos contains the terminal sheaf of the ambient topos. -/
theorem terminal_mem_essImage_of_isSubtopos
    {E : ObjectProperty (Sheaf J (Type w))} (hE : IsSubtopos J E) :
    E (⊤_ (Sheaf J (Type w))) := by
  rcases hE with ⟨D, hD, K, f, hf, rfl⟩
  letI : Category D := hD
  letI : f.IsEmbedding := hf
  let jstar := CategoryTheory.pushforward f
  let _ : PreservesLimits jstar := f.adjunction.rightAdjoint_preservesLimits
  have hterminal :
      IsTerminal (jstar.obj (⊤_ (Sheaf K (Type w)))) :=
    IsTerminal.isTerminalObj jstar (⊤_ (Sheaf K (Type w))) terminalIsTerminal
  have hmem :
      Functor.essImage jstar (jstar.obj (⊤_ (Sheaf K (Type w)))) :=
    Functor.obj_mem_essImage jstar (⊤_ (Sheaf K (Type w)))
  -- The direct image is a right adjoint, hence sends the source terminal to a terminal object
  -- of the ambient sheaf topos; strict fullness then transports membership to the chosen
  -- terminal sheaf.
  exact Functor.essImage.ofIso (hterminal.uniqueUpToIso terminalIsTerminal) hmem

/-- Helper for Lemma 7.43.3: if `(Over.forget ℱ).essImage` were a subtopos, then `ℱ` would have
a global section. This is the first concrete obstruction to the current owner formulation. -/
theorem global_section_of_isSubtopos_over_forget_essImage
    {ℱ : Sheaf J (Type w)}
    (hsub : IsSubtopos J (Over.forget ℱ).essImage) :
    Nonempty ((⊤_ (Sheaf J (Type w))) ⟶ ℱ) := by
  have hterminal :
      Functor.essImage (Over.forget ℱ) (⊤_ (Sheaf J (Type w))) :=
    terminal_mem_essImage_of_isSubtopos (J := J) hsub
  -- Membership in the slice-forgetful essential image is equivalent to having a map to `ℱ`.
  exact
    (over_forget_essImage_iff_nonempty_hom
      (J := J) (A := ℱ) (X := ⊤_ (Sheaf J (Type w)))).1 hterminal

/-- Helper for Lemma 7.43.3: the current owner `(Over.forget ℱ).essImage` cannot define a
subtopos unless `ℱ` has a global section. This packages the obstruction used in the blocker
diagnosis into contradiction form. -/
theorem not_isSubtopos_over_forget_essImage_of_no_global_section
    {ℱ : Sheaf J (Type w)}
    (hsection : ¬ Nonempty ((⊤_ (Sheaf J (Type w))) ⟶ ℱ)) :
    ¬ IsSubtopos J (Over.forget ℱ).essImage := by
  intro hsub
  -- Any subtopos contains the ambient terminal object, so the previous lemma forces a section.
  exact hsection (global_section_of_isSubtopos_over_forget_essImage (J := J) hsub)

/-- Helper for Lemma 7.43.3: on the representable replacement site, any subtopos witness for the
current owner already forces a global section of the sheafified representable. This isolates the
owner mismatch on the exact representable object used by the source proof. -/
theorem representable_global_section_of_isSubtopos_slice_owner
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C') (U₀ : C')
    (hsub : IsSubtopos J' (Over.forget h[U₀]^#[J']).essImage) :
    Nonempty ((⊤_ (Sheaf J' (Type (max u₁ v₁)))) ⟶ h[U₀]^#[J']) := by
  -- This is the generic global-section obstruction specialized to the representable owner.
  exact global_section_of_isSubtopos_over_forget_essImage (J := J') hsub

/-- Helper for Lemma 7.43.3: if the sheafified representable `h[U₀]^#[J']` has no global
section, then the current owner `(Over.forget h[U₀]^#[J']).essImage` cannot be a subtopos. This
is the contradiction form of the representable-site obstruction used in the blocker report. -/
theorem representable_not_isSubtopos_slice_owner_of_no_global_section
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C') (U₀ : C')
    (hsection : ¬ Nonempty ((⊤_ (Sheaf J' (Type (max u₁ v₁)))) ⟶ h[U₀]^#[J'])) :
    ¬ IsSubtopos J' (Over.forget h[U₀]^#[J']).essImage := by
  -- The representable-site contradiction is exactly the generic contradiction specialized.
  exact not_isSubtopos_over_forget_essImage_of_no_global_section (J := J') hsection

/-- Helper for Lemma 7.43.3: a subterminal sheaf has at most one section on every object of the
base site. -/
theorem subsingleton_sections_of_isSubterminal
    {A : Sheaf J (Type w)} (hA : IsSubterminal A) (U : C) :
    Subsingleton (A.obj.obj (op U)) := by
  -- Pass to the underlying presheaf, where the map to the terminal presheaf is objectwise a
  -- function into the terminal type, hence injective only when the fiber itself is subsingleton.
  let f : A ⟶ Sheaf.terminal J Types.isTerminalPUnit :=
    (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from A
  have hmonoMap : Mono ((sheafToPresheaf J (Type w)).map f) := by
    letI : Mono f := hA.mono_isTerminal_from (Sheaf.isTerminalTerminal J Types.isTerminalPUnit)
    exact (sheafToPresheaf J (Type w)).map_mono f
  let hmonoApp :
      Mono (((sheafToPresheaf J (Type w)).map f).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).1 hmonoMap (op U)
  let hinj :
      Function.Injective (((sheafToPresheaf J (Type w)).map f).app (op U)) :=
    (CategoryTheory.mono_iff_injective _).1 hmonoApp
  refine ⟨?_⟩
  intro s t
  apply hinj
  simp [f, Sheaf.isTerminalTerminal_from_hom, Functor.isTerminalConst_from_app,
    Types.isTerminalPUnit_from_apply]

/-- Helper for Lemma 7.43.3: if `ℱ` is subterminal, then the projection from the category of
elements of `ℱ` to the base site is full. -/
theorem localizationProjection_full_of_isSubterminal
    {ℱ : Sheaf J (Type v)} (hℱ : IsSubterminal ℱ) :
    (localizationProjection ℱ).Full where
  map_surjective {X Y} f := by
    -- The two sections over the source object coincide because every fiber of `ℱ` is
    -- subsingleton.
    have hsec :
        ℱ.obj.map f.op (unop Y).2 = (unop X).2 := by
      let hX := subsingleton_sections_of_isSubterminal (J := J) hℱ ((localizationProjection ℱ).obj X)
      exact hX.elim _ _
    refine ⟨Quiver.Hom.op (CategoryOfElements.homMk (unop Y) (unop X) f.op hsec), ?_⟩
    rfl

/-- Helper for Lemma 7.43.3: the continuous inverse-image functor attached to
`localizationProjection ℱ` preserves finite limits in the original `Type v` universe. -/
theorem localization_sheafPushforwardContinuous_preservesFiniteLimits
    {ℱ : Sheaf J (Type v)} :
    PreservesFiniteLimits
      ((localizationProjection ℱ).sheafPushforwardContinuous
        (Type v) (localizationTopology ℱ) J) := by
  let F :=
    (localizationProjection ℱ).sheafPushforwardContinuous
      (Type v) (localizationTopology ℱ) J
  let G := sheafToPresheaf (localizationTopology ℱ) (Type v)
  have hcomp : PreservesFiniteLimits (F ⋙ G) := by
    let H :=
      sheafToPresheaf J (Type v) ⋙
        (Functor.whiskeringLeft ℱ.obj.Elementsᵒᵖᵒᵖ Cᵒᵖ (Type v)).obj
          (localizationProjection ℱ).op
    have hH : PreservesFiniteLimits H := by
      -- After forgetting to presheaves, the functor is just precomposition with
      -- `localizationProjection ℱ`, and finite limits of presheaves are computed pointwise.
      dsimp [H]
      infer_instance
    -- The continuous pushforward is defined by that presheaf-level precomposition.
    exact
      preservesFiniteLimits_of_natIso
        ((localizationProjection ℱ).sheafPushforwardContinuousCompSheafToPresheafIso
          (Type v) (localizationTopology ℱ) J).symm
  -- The sheaf-to-presheaf functor reflects finite limits, so preservation after forgetting
  -- descends back to sheaves.
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- Helper for Lemma 7.43.3: the canonical morphism from the localization/slice topos at `ℱ`
to the ambient sheaf topos. Its direct image is the localization pushforward along
`localizationProjection ℱ`. -/
noncomputable def localizationMorphismOfTopoiIn
    {ℱ : Sheaf J (Type v)}
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    MorphismOfTopoiIn.{u, max u v, v, v, v} J (localizationTopology ℱ) where
  inverseImageFunctor :=
    letI :
        PreservesFiniteLimits
          ((localizationProjection ℱ).sheafPushforwardContinuous
            (Type v) (localizationTopology ℱ) J) :=
      localization_sheafPushforwardContinuous_preservesFiniteLimits (J := J) (ℱ := ℱ)
    LeftExactFunctor.of
      ((localizationProjection ℱ).sheafPushforwardContinuous
        (Type v) (localizationTopology ℱ) J)
  pushforward :=
    (localizationProjection ℱ).sheafPushforwardCocontinuous
      (Type v) (localizationTopology ℱ) J
  adjunction :=
    (localizationProjection ℱ).sheafAdjunctionCocontinuous
      (Type v) (localizationTopology ℱ) J

/-- Helper for Lemma 7.43.3: if `ℱ` is subterminal, then the canonical localization/slice
morphism at `ℱ` is an embedding of topoi. This is the source meaning of saying that
`Sh(C, J) / ℱ` is a subtopos of `Sh(C, J)`. -/
theorem localization_morphism_isEmbedding_of_isSubterminal
    {ℱ : Sheaf J (Type v)}
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F]
    (hℱ : IsSubterminal ℱ) :
    (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).IsEmbedding := by
  letI : (localizationProjection ℱ).Full :=
    localizationProjection_full_of_isSubterminal (J := J) hℱ
  have hCounitAppIso :
      ∀ X : Sheaf (localizationTopology ℱ) (Type v),
        IsIso
          (((localizationProjection ℱ).sheafAdjunctionCocontinuous
            (Type v) (localizationTopology ℱ) J).counit.app X) := by
    intro X
    -- Fullness of the projection and the built-in faithfulness make the cocontinuous counit
    -- invertible by Lemma 7.21.7.
    exact
      counit_isIso_sheafAdjunctionCocontinuous_of_fullyFaithful
        (localizationTopology ℱ) J (localizationProjection ℱ) X
  letI :
      IsIso
        ((localizationProjection ℱ).sheafAdjunctionCocontinuous
          (Type v) (localizationTopology ℱ) J).counit :=
    NatIso.isIso_of_isIso_app _
  let hff :
      ((localizationProjection ℱ).sheafPushforwardCocontinuous
        (Type v) (localizationTopology ℱ) J).FullyFaithful :=
    ((localizationProjection ℱ).sheafAdjunctionCocontinuous
      (Type v) (localizationTopology ℱ) J).fullyFaithfulROfIsIsoCounit
  -- Repackage full faithfulness of the direct image as the embedding condition for the
  -- corresponding morphism of topoi.
  refine
    { toFull := by
        simpa [localizationMorphismOfTopoiIn, CategoryTheory.pushforward] using hff.full
      toFaithful := by
        simpa [localizationMorphismOfTopoiIn, CategoryTheory.pushforward] using hff.faithful }

/-- Helper for Lemma 7.43.3: if `ℱ` is subterminal, then the localization direct image
associated to the category of elements of `ℱ` presents a subtopos. This is only a consequence of
the canonical embedding statement, not the converse formulation of Lemma 7.43.3. -/
theorem localization_pushforward_isSubtopos_of_isSubterminal
    {ℱ : Sheaf J (Type v)}
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F]
    (hℱ : IsSubterminal ℱ) :
    IsSubtopos.{u, max u v, v, v, v} J
      (Functor.essImage
        ((localizationProjection ℱ).sheafPushforwardCocontinuous
          (Type v) (localizationTopology ℱ) J)) := by
  let i := localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)
  have hi : i.IsEmbedding :=
    localization_morphism_isEmbedding_of_isSubterminal (J := J) hℱ
  letI : i.IsEmbedding := hi
  simpa [i, localizationMorphismOfTopoiIn, CategoryTheory.pushforward] using
    MorphismOfTopoiIn.isSubtopos_essImage (J := J) i

/-- Helper for Lemma 7.43.3: if `X` lies in the essential image of the direct image of an
embedding of topoi, then maps from `X` to the pushed-forward terminal sheaf are unique. -/
theorem hom_subsingleton_to_pushforward_terminal_of_mem_essImage
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (i : MorphismOfTopoiIn J K) [i.IsEmbedding]
    {X : Sheaf J (Type w)} (hX : Functor.essImage (CategoryTheory.pushforward i) X) :
    Subsingleton
      (X ⟶ (CategoryTheory.pushforward i).obj
        (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) := by
  let Y : Sheaf K (Type w) := hX.witness
  let e : (CategoryTheory.pushforward i).obj Y ≅ X := hX.getIso
  have hImage :
      Subsingleton
        ((CategoryTheory.pushforward i).obj Y ⟶ (CategoryTheory.pushforward i).obj
          (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) := by
    refine ⟨?_⟩
    intro f g
    -- Compare the two morphisms after pulling them back through fullness of `i_*`.
    have hpre :
        (CategoryTheory.pushforward i).preimage f =
          (CategoryTheory.pushforward i).preimage g := by
      apply Subsingleton.elim
    simpa using congrArg ((CategoryTheory.pushforward i).map) hpre
  refine ⟨?_⟩
  intro f g
  -- Transport the uniqueness statement along the essential-image isomorphism `e`.
  simpa using (cancel_epi e.hom).1 (Subsingleton.elim (e.hom ≫ f) (e.hom ≫ g))

/-- Helper for Lemma 7.43.3: once the presenting embedding identifies `ℱ` with the pushed-forward
terminal source object, the common essential-image description forces `ℱ` to be subterminal. -/
theorem isSubterminal_of_subtopos_over_forget_essImage_of_iso_terminal
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (i : MorphismOfTopoiIn J K) [i.IsEmbedding]
    {ℱ : Sheaf J (Type w)}
    (hess : Functor.essImage (Over.forget ℱ) =
      Functor.essImage (CategoryTheory.pushforward i))
    (e : (CategoryTheory.pushforward i).obj
      (CategoryTheory.Limits.terminal (Sheaf K (Type w))) ≅ ℱ) :
    IsSubterminal ℱ := by
  intro Z f g
  have hZ : Functor.essImage (CategoryTheory.pushforward i) Z := by
    rw [← hess]
    exact Functor.obj_mem_essImage (Over.forget ℱ) (Over.mk f)
  have hSub :
      Subsingleton
        (Z ⟶ (CategoryTheory.pushforward i).obj
          (CategoryTheory.Limits.terminal (Sheaf K (Type w)))) :=
    hom_subsingleton_to_pushforward_terminal_of_mem_essImage (J := J) i hZ
  -- Compose the two candidate arrows with the comparison to the terminal image.
  exact (cancel_mono e.inv).1 (Subsingleton.elim _ _)

/-- Helper for Lemma 7.43.3: after enlarging the universe once via `AsSmall C`, Lemma `7.29.5`
replaces the sheaf `ℱ` by a representable sheaf on a dense subsite with subcanonical topology and
finite limits. This packages the source proof's first structural reduction. -/
theorem representable_slice_replacement_site
    (ℱ : Sheaf J (Type w)) :
    ∃ (C₀ : Type (max w u v)) (_ : Category C₀) (J₀ : GrothendieckTopology C₀)
      (a : C ⥤ C₀) (_ : a.IsDenseSubsite J J₀)
      (C' : Type (max w u v)) (_ : Category C') (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (v : C₀ ⥤ C') (_ : v.IsDenseSubsite J₀ J')
      (U₀ : C'),
      Nonempty
        (CategoryTheory.yoneda.obj U₀ ≅
          ((sheafEquiv J₀ J' v (Type (max w u v))).functor.obj
            ((sheafEquiv J J₀ a (Type (max w u v))).functor.obj
              ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ))).obj) := by
  -- Enlarge the original site once so the replacement-site theorem applies in the ambient
  -- `Type (max w u v)` universe used by the source proof.
  let C₀ : Type (max w u v) := CategoryTheory.AsSmall.{w} C
  let a : C ⥤ C₀ := CategoryTheory.AsSmall.up
  let e : C ≌ C₀ := CategoryTheory.AsSmall.equiv (C := C)
  let J₀ : GrothendieckTopology C₀ := e.inverse.inducedTopology J
  let _ : a.IsDenseSubsite J J₀ := by
    change e.functor.IsDenseSubsite J J₀
    infer_instance
  -- Apply Lemma `7.29.5` to the singleton family generated by the transported sheaf.
  let F₀ : Sheaf J₀ (Type (max w u v)) :=
    (sheafEquiv J J₀ a (Type (max w u v))).functor.obj
      ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ)
  let F : Unit → Sheaf J₀ (Type (max w u v)) := fun _ ↦ F₀
  rcases exists_representable_family_site_presentation (J := J₀) F with
    ⟨C', hC', J', hsub, hfinite, v, hdense, _, hcover, hsubobj, hfamily⟩
  let _ : Category C' := hC'
  let _ : J'.Subcanonical := hsub
  let _ : HasFiniteLimits C' := hfinite
  let _ : v.IsDenseSubsite J₀ J' := hdense
  -- The singleton family becomes representable on the replacement site, so choose the
  -- representing object and its Yoneda witness.
  have hrepr :
      (((sheafEquiv J₀ J' v (Type (max w u v))).functor.obj F₀).obj).IsRepresentable := by
    simpa [F, F₀] using hfamily ()
  let F' : Sheaf J' (Type (max w u v)) :=
    (sheafEquiv J₀ J' v (Type (max w u v))).functor.obj F₀
  let _ : (F'.obj).IsRepresentable := by
    simpa [F'] using hrepr
  exact
    ⟨C₀, inferInstance, J₀, a, inferInstance, C', hC', J', hsub, hfinite, v, hdense,
      Functor.reprX F'.obj, ⟨Functor.reprW F'.obj⟩⟩

/-- Helper for Lemma 7.43.3: if the representable sheaf `h_{U₀}` is subterminal, then every
hom-set into `U₀` is subsingleton. -/
theorem subsingleton_hom_of_representable_yoneda_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    IsSubterminal (J'.yoneda.obj U₀) → ∀ X : C', Subsingleton (X ⟶ U₀) := by
  intro hsub X
  refine ⟨?_⟩
  intro f g
  -- Apply subterminality to the two Yoneda maps and read the result back through Yoneda.
  have hfg : J'.yoneda.map f = J'.yoneda.map g := hsub _ _
  exact (J'.yoneda).map_injective hfg

/-- Helper for Lemma 7.43.3: if every hom-set into `U₀` is subsingleton, then the representable
sheaf `h_{U₀}` is subterminal. -/
theorem representable_yoneda_isSubterminal_of_subsingleton_hom
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    (∀ X : C', Subsingleton (X ⟶ U₀)) → IsSubterminal (J'.yoneda.obj U₀) := by
  intro hhom Z p q
  -- Equality into a representable sheaf is checked after precomposing with Yoneda generators.
  apply J'.hom_ext_yoneda
  intro X α
  -- In the representable target, both precomposites come from arrows `X ⟶ U₀`, and those are
  -- unique by hypothesis.
  have hpre :
      (J'.yoneda).preimage (α ≫ p) = (J'.yoneda).preimage (α ≫ q) :=
    Subsingleton.elim _ _
  simpa using congrArg (J'.yoneda.map) hpre

/-- Helper for Lemma 7.43.3: on a subcanonical site, the representable sheaf `h_{U₀}` is
subterminal exactly when every hom-set into `U₀` is subsingleton. -/
theorem representable_yoneda_subterminal_iff_subsingleton_hom
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (U₀ : C') :
    IsSubterminal (J'.yoneda.obj U₀) ↔ ∀ X : C', Subsingleton (X ⟶ U₀) := by
  constructor
  · exact subsingleton_hom_of_representable_yoneda_subterminal (J' := J') U₀
  · exact representable_yoneda_isSubterminal_of_subsingleton_hom (J' := J') U₀

/-- Helper for Lemma 7.43.3: an embedding of topoi makes each counit component of the stored
adjunction an isomorphism. -/
theorem morphismCounitApp_isIso_of_isEmbedding
    {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D}
    (i : MorphismOfTopoiIn J K) [i.IsEmbedding] (X : Sheaf K (Type w)) :
    IsIso (i.adjunction.counit.app X) := by
  -- The embedding hypothesis is exactly full faithfulness of the direct image, so the standard
  -- adjunction criterion turns the counit into an isomorphism.
  letI : (CategoryTheory.pushforward i).Full := ‹i.IsEmbedding›.toFull
  letI : (CategoryTheory.pushforward i).Faithful := ‹i.IsEmbedding›.toFaithful
  haveI : IsIso i.adjunction.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful i.adjunction
  infer_instance

/-- Helper for Lemma 7.43.3: if the second projection from `U × U` is an isomorphism, then all
hom-sets into `U` are subsingletons. -/
theorem subsingleton_hom_of_prod_snd_isIso
    {D : Type u₁} [Category.{v₁} D] [HasBinaryProducts D] {U : D}
    (hsnd : IsIso (Limits.prod.snd : U ⨯ U ⟶ U)) :
    ∀ X : D, Subsingleton (X ⟶ U) := by
  intro X
  refine ⟨?_⟩
  intro f g
  letI : IsIso (Limits.prod.snd : U ⨯ U ⟶ U) := hsnd
  have hlift : Limits.prod.lift f g = Limits.prod.lift g g := by
    -- The isomorphic second projection is monic, so two product maps with the same second
    -- component are equal.
    apply (cancel_mono (Limits.prod.snd : U ⨯ U ⟶ U)).1
    rw [Limits.prod.lift_snd, Limits.prod.lift_snd]
  -- Reading the first projection of the equal product maps gives the desired equality.
  calc
    f = Limits.prod.lift f g ≫ Limits.prod.fst := (Limits.prod.lift_fst f g).symm
    _ = Limits.prod.lift g g ≫ Limits.prod.fst := by rw [hlift]
    _ = g := Limits.prod.lift_fst g g

/-- Helper for Lemma 7.43.3: if all maps into `U` are unique, then the self-product projection
`U × U ⟶ U` is an isomorphism. -/
theorem prod_snd_isIso_of_subsingleton_hom
    {D : Type u₁} [Category.{v₁} D] [HasBinaryProducts D] {U : D}
    (hU : ∀ X : D, Subsingleton (X ⟶ U)) :
    IsIso (Limits.prod.snd : U ⨯ U ⟶ U) := by
  let inv : U ⟶ U ⨯ U := Limits.prod.lift (𝟙 U) (𝟙 U)
  -- Use the diagonal as inverse; uniqueness of maps into `U` identifies the two product
  -- coordinates in the nontrivial triangle identity.
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · apply Limits.prod.hom_ext
    · exact Subsingleton.elim _ _
    · simpa [inv] using
        Limits.prod.lift_snd
          (Limits.prod.snd : U ⨯ U ⟶ U)
          (Limits.prod.snd : U ⨯ U ⟶ U)
  · simpa [inv] using
      Limits.prod.lift_snd (𝟙 U) (𝟙 U)

/-- Helper for Lemma 7.43.3: uniqueness of maps into `U` is equivalent to the self-product
projection `U × U ⟶ U` being an isomorphism. -/
theorem prod_snd_isIso_iff_subsingleton_hom
    {D : Type u₁} [Category.{v₁} D] [HasBinaryProducts D] {U : D} :
    IsIso (Limits.prod.snd : U ⨯ U ⟶ U) ↔ ∀ X : D, Subsingleton (X ⟶ U) := by
  constructor
  · intro hsnd
    exact subsingleton_hom_of_prod_snd_isIso (U := U) hsnd
  · intro hU
    exact prod_snd_isIso_of_subsingleton_hom (U := U) hU

/-- Helper for Lemma 7.43.3: on a subcanonical site, an isomorphism of the projection
`U₀ × U₀ ⟶ U₀` makes the sheafified representable at `U₀` subterminal. -/
theorem representableYoneda_isSubterminal_of_prod_snd_isIso
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C')
    (hsnd : IsIso (Limits.prod.snd : U₀ ⨯ U₀ ⟶ U₀)) :
    IsSubterminal (J'.yoneda.obj U₀) := by
  -- Convert the product-projection criterion into hom-subsingletons, then use the representable
  -- Yoneda characterization already established above.
  exact
    (representable_yoneda_subterminal_iff_subsingleton_hom (J' := J') U₀).2
      (subsingleton_hom_of_prod_snd_isIso (U := U₀) hsnd)

/-- Helper for Lemma 7.43.3: on a subcanonical finite-limit site, subterminality of the
sheafified representable is equivalent to the self-product projection being an isomorphism. -/
theorem representable_yoneda_subterminal_iff_prod_snd_isIso
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    IsSubterminal (J'.yoneda.obj U₀) ↔
      IsIso (Limits.prod.snd : U₀ ⨯ U₀ ⟶ U₀) := by
  constructor
  · intro hU₀
    -- Convert representable subterminality to uniqueness of maps into `U₀`, then use the
    -- object-level product criterion.
    exact
      prod_snd_isIso_of_subsingleton_hom (U := U₀)
        ((representable_yoneda_subterminal_iff_subsingleton_hom (J' := J') U₀).1 hU₀)
  · intro hsnd
    -- The reverse implication is the endpoint already used in the main proof.
    exact representableYoneda_isSubterminal_of_prod_snd_isIso (J' := J') U₀ hsnd

/-- Helper for Lemma 7.43.3: a faithful functor reflects subterminal objects. -/
theorem isSubterminal_of_faithful_obj
    {D : Type u₁} [Category.{v₁} D] {E : Type u} [Category.{v} E]
    (F : D ⥤ E) [F.Faithful] {X : D}
    (hFX : IsSubterminal (F.obj X)) :
    IsSubterminal X := by
  intro Z f g
  -- Compare the two arrows after applying the faithful functor.
  exact F.map_injective (hFX (F.map f) (F.map g))

/-- Helper for Lemma 7.43.3: equivalences preserve and reflect subterminal objects. -/
theorem isSubterminal_obj_iff_of_equivalence
    {D : Type u₁} [Category.{v₁} D] {E : Type u} [Category.{v} E]
    (F : D ≌ E) (X : D) :
    IsSubterminal (F.functor.obj X) ↔ IsSubterminal X := by
  constructor
  · intro hFX
    -- Reflection is immediate from faithfulness of the equivalence functor.
    exact isSubterminal_of_faithful_obj (F := F.functor) hFX
  · intro hX Z f g
    -- Apply the inverse functor and compare in the source category through the unit isomorphism.
    apply F.inverse.map_injective
    apply (cancel_mono (F.unitIso.app X).inv).1
    simpa using
      hX
        (F.inverse.map f ≫ (F.unitIso.app X).inv)
        (F.inverse.map g ≫ (F.unitIso.app X).inv)

/-- Helper for Lemma 7.43.3: subterminality is preserved by isomorphism. This is the transport
piece needed to move the representable witness from the replacement site back to the original
sheaf. -/
theorem isSubterminal_iff_of_iso
    {A B : Sheaf J (Type w)} (e : A ≅ B) :
    IsSubterminal A ↔ IsSubterminal B := by
  constructor
  · intro hA Z f g
    -- Postcompose with the inverse isomorphism to compare the two maps inside `A`.
    apply (cancel_mono e.inv).1
    simpa using hA (f ≫ e.inv) (g ≫ e.inv)
  · intro hB Z f g
    -- The same argument in the other direction transports subterminality back across `e`.
    apply (cancel_mono e.hom).1
    simpa using hB (f ≫ e.hom) (g ≫ e.hom)

/-- Helper for Lemma 7.43.3: the replacement-site presentation transports subterminality exactly
between the original sheaf `ℱ` and the representable witness `J'.yoneda.obj U₀`. -/
theorem replacement_site_isSubterminal_iff
    {C₀ : Type (max w u v)} [Category C₀] (J₀ : GrothendieckTopology C₀)
    (a : C ⥤ C₀) [a.IsDenseSubsite J J₀]
    {C' : Type (max w u v)} [Category C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] (v' : C₀ ⥤ C') [v'.IsDenseSubsite J₀ J']
    (ℱ : Sheaf J (Type w)) (U₀ : C')
    (hrepr :
      Nonempty
        (CategoryTheory.yoneda.obj U₀ ≅
          ((sheafEquiv J₀ J' v' (Type (max w u v))).functor.obj
            ((sheafEquiv J J₀ a (Type (max w u v))).functor.obj
              ((sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ))).obj)) :
    IsSubterminal ℱ ↔ IsSubterminal (J'.yoneda.obj U₀) := by
  let ℱulift : Sheaf J (Type (max w u v)) :=
    (sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}).obj ℱ
  let ℱ₀ : Sheaf J₀ (Type (max w u v)) :=
    (sheafEquiv J J₀ a (Type (max w u v))).functor.obj ℱulift
  let ℱ' : Sheaf J' (Type (max w u v)) :=
    (sheafEquiv J₀ J' v' (Type (max w u v))).functor.obj ℱ₀
  rcases hrepr with ⟨e⟩
  let eSheaf : J'.yoneda.obj U₀ ≅ ℱ' :=
    { hom := ⟨e.hom⟩
      inv := ⟨e.inv⟩
      hom_inv_id := by
        ext X x
        -- The sheaf identity is read objectwise from the underlying presheaf identity.
        change (e.hom ≫ e.inv).app X x = x
        simpa using congrFun (NatTrans.congr_app e.hom_inv_id X) x
      inv_hom_id := by
        ext X x
        -- The same objectwise comparison proves the other triangle identity.
        change (e.inv ≫ e.hom).app X x = x
        simpa using congrFun (NatTrans.congr_app e.inv_hom_id X) x }
  constructor
  · intro hℱ
    have hℱulift : IsSubterminal ℱulift := by
      intro Z f g
      ext X x
      -- The source sheaf has singleton fibers, and `ULift` preserves singleton types.
      have hsub :
          Subsingleton (ℱ.obj.obj X) := by
        simpa using subsingleton_sections_of_isSubterminal (J := J) hℱ X.unop
      letI : Subsingleton (ℱulift.obj.obj X) :=
        by
          simpa [ℱulift] using
            (show Subsingleton (ULift.{max w u v, w} (ℱ.obj.obj X)) from inferInstance)
      exact Subsingleton.elim _ _
    have hℱ₀ : IsSubterminal ℱ₀ :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J J₀ a (Type (max w u v))) ℱulift).2 hℱulift
    have hℱ' : IsSubterminal ℱ' :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J₀ J' v' (Type (max w u v))) ℱ₀).2 hℱ₀
    -- Finish by transporting across the representable witness on the replacement site.
    exact (isSubterminal_iff_of_iso (J := J') eSheaf).2 hℱ'
  · intro hU₀
    have hℱ' : IsSubterminal ℱ' :=
      (isSubterminal_iff_of_iso (J := J') eSheaf).1 hU₀
    have hℱ₀ : IsSubterminal ℱ₀ :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J₀ J' v' (Type (max w u v))) ℱ₀).1 hℱ'
    have hℱulift : IsSubterminal ℱulift :=
      (isSubterminal_obj_iff_of_equivalence
        (sheafEquiv J J₀ a (Type (max w u v))) ℱulift).1 hℱ₀
    -- Reflect the remaining transport through the faithful `ULift`-whiskering functor.
    exact isSubterminal_of_faithful_obj
      (F := sheafCompose J CategoryTheory.uliftFunctor.{max w u v, w}) hℱulift

/-- Helper for Lemma 7.43.3: on a representable replacement site, a subterminal representable
sheaf yields an embedding localization morphism of topoi. -/
theorem representable_localization_isEmbedding_of_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C')
    (hsub : IsSubterminal (J'.yoneda.obj U₀)) :
    ((Over.forget U₀).morphismOfTopoiInOfCocontinuous (J'.over U₀) J').IsEmbedding := by
  let hhom : ∀ X : C', Subsingleton (X ⟶ U₀) :=
    (representable_yoneda_subterminal_iff_subsingleton_hom (J' := J') U₀).1 hsub
  let hfull : (Over.forget U₀).Full := overForget_full_of_subsingletonHom U₀ hhom
  letI : (Over.forget U₀).Full := hfull
  have hCounitAppIso :
      ∀ X : Sheaf (J'.over U₀) (Type (max u₁ v₁)),
        IsIso
          (((Over.forget U₀).sheafAdjunctionCocontinuous
            (Type (max u₁ v₁)) (J'.over U₀) J').counit.app X) := by
    intro X
    -- This is exactly Lemma 7.27.4 on the representable replacement site.
    exact
      localization_inverseImage_pushforward_app_isIso_of_subsingletonHom
        (J := J') U₀ hhom X
  haveI :
      IsIso
        ((Over.forget U₀).sheafAdjunctionCocontinuous
          (Type (max u₁ v₁)) (J'.over U₀) J').counit := by
    -- Upgrade the componentwise source-proof isomorphisms to the whole counit transformation.
    exact NatIso.isIso_of_isIso_app _
  let hff :
      ((Over.forget U₀).sheafPushforwardCocontinuous
        (Type (max u₁ v₁)) (J'.over U₀) J').FullyFaithful :=
    ((Over.forget U₀).sheafAdjunctionCocontinuous
      (Type (max u₁ v₁)) (J'.over U₀) J').fullyFaithfulROfIsIsoCounit
  -- Repackage the fully faithful direct image as the source-facing embedding predicate.
  refine
    { toFull := by
        simpa [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using hff.full
      toFaithful := by
        simpa [Functor.morphismOfTopoiInOfCocontinuous_pushforward] using hff.faithful }

/-- Helper for Lemma 7.43.3: the representable-localization comparison is an equivalence, so
precomposing the slice forgetful functor over the sheafified representable `h[U₀]^#[J']` with it
does not change the essential image. -/
theorem representable_comparison_forget_essImage
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    Functor.essImage
        (J'.representableLocalizationComparison U₀ ⋙ Over.forget h[U₀]^#[J']) =
      Functor.essImage (Over.forget h[U₀]^#[J']) := by
  let comparison := J'.representableLocalizationComparison U₀
  haveI : Functor.IsEquivalence comparison :=
    J'.representableLocalizationComparison_isEquivalence U₀
  let e := comparison.asEquivalence
  letI : Functor.EssSurj comparison :=
    { mem_essImage := fun Y ↦ ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩ }
  -- Essential images are invariant under precomposition by an equivalence.
  simpa [comparison] using
    (Functor.essImage_comp_of_essSurj
      (F := comparison) (G := Over.forget h[U₀]^#[J']))

/-- Helper for Lemma 7.43.3: on the representable replacement site, the localized inverse-image
functor agrees with the slice inverse-image functor after the comparison equivalence. This is the
owner-level bridge needed before comparing the two direct-image essential images. -/
noncomputable def representable_comparison_inverseImageIso_star
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    J'.overPullback (Type (max u₁ v₁)) U₀ ⋙ J'.representableLocalizationComparison U₀ ≅
      Over.star h[U₀]^#[J'] :=
  J'.representableLocalizationComparison_inverseImageIso U₀

/-- Helper for Lemma 7.43.3: on the representable replacement site, precomposing the slice-owner
forgetful functor with the comparison equivalence does not change its essential image. This is the
owner equality supplied by Lemma `7.30.5`; it compares the slice owner with the lower-shriek side,
not with the localization direct image `j_{U₀,*}`. -/
theorem representable_localization_lowerShriek_essImage_eq_slice_owner
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C') :
    Functor.essImage
        (J'.representableLocalizationComparison U₀ ⋙ Over.forget h[U₀]^#[J']) =
      Functor.essImage (Over.forget h[U₀]^#[J']) := by
  -- This is exactly the essential-image invariance under the comparison equivalence.
  exact representable_comparison_forget_essImage (J' := J') U₀

/-- Helper for Lemma 7.43.3: on the representable replacement site, a subterminal sheafified
representable already cuts out a subtopos via the localization direct image at `U₀`. -/
theorem representable_localization_pushforward_isSubtopos_of_subterminal
    {C' : Type u₁} [Category.{v₁} C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C'] (U₀ : C')
    (hsub : IsSubterminal (J'.yoneda.obj U₀)) :
    IsSubtopos.{u₁, max u₁ v₁, v₁, v₁, max u₁ v₁}
      J'
      (Functor.essImage
        ((Over.forget U₀).sheafPushforwardCocontinuous
          (Type (max u₁ v₁)) (J'.over U₀) J')) := by
  let i := (Over.forget U₀).morphismOfTopoiInOfCocontinuous (J'.over U₀) J'
  have hi : i.IsEmbedding :=
    representable_localization_isEmbedding_of_subterminal (J' := J') U₀ hsub
  letI : i.IsEmbedding := hi
  -- Route correction: the slice-forgetful owner is the lower-shriek comparison owner, not the
  -- direct image `j_{U₀,*}` used by Lemma 7.43.3.  This helper therefore stays on the direct-image
  -- essential image, where the embedding proof applies directly.
  simpa [i, Functor.morphismOfTopoiInOfCocontinuous_pushforward] using
    MorphismOfTopoiIn.isSubtopos_essImage (J := J') i

/-- Helper for Lemma 7.43.3: a fully faithful right adjoint to `Over.star A` makes the
slice forgetful functor fully faithful by the adjoint-triple criterion. -/
noncomputable def over_forget_fullyFaithful_of_star_rightAdjoint_fullyFaithful
    {E : Type u₁} [Category.{v₁} E] [HasBinaryProducts E] {A : E}
    (R : Over A ⥤ E) (adj : Over.star A ⊣ R) [R.Full] [R.Faithful] :
    (Over.forget A).FullyFaithful :=
  (Adjunction.Triple.fullyFaithfulEquiv
    (t :=
      { adj₁ := Over.forgetAdjStar A
        adj₂ := adj })).symm
    (.ofFullyFaithful R)

/-- Helper for Lemma 7.43.3: the localization adjunction, conjugated by the equivalence between
sheaves on the category of elements and the slice, makes `Over.star ℱ` a left adjoint. -/
noncomputable def localization_overStar_rightAdjunction
    {ℱ : Sheaf J (Type v)}
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    Over.star ℱ ⊣
      (sheafCategoryOfElementsEquivOver ℱ).inverse ⋙
        CategoryTheory.pushforward (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)) :=
  ((localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).adjunction.comp
    (sheafCategoryOfElementsEquivOver ℱ).toAdjunction).ofNatIsoLeft
    (sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ)

/-- Helper for Lemma 7.43.3: if the localization morphism at `ℱ` is an embedding, then `ℱ` is
subterminal. -/
theorem isSubterminal_of_localizationMorphism_isEmbedding
    {ℱ : Sheaf J (Type v)}
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F]
    (hemb : (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).IsEmbedding) :
    IsSubterminal ℱ := by
  let i := localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)
  let E := sheafCategoryOfElementsEquivOver ℱ
  let R : Over ℱ ⥤ Sheaf J (Type v) := E.inverse ⋙ CategoryTheory.pushforward i
  letI : (CategoryTheory.pushforward i).Full := hemb.toFull
  letI : (CategoryTheory.pushforward i).Faithful := hemb.toFaithful
  have hff : (Over.forget ℱ).FullyFaithful := by
    -- Equivalences preserve full faithfulness of the embedded direct image, so the triple helper
    -- applies to the conjugated right adjoint of `Over.star ℱ`.
    exact over_forget_fullyFaithful_of_star_rightAdjoint_fullyFaithful
      (A := ℱ) R (localization_overStar_rightAdjunction (J := J) (ℱ := ℱ))
  letI : (Over.forget ℱ).Full := hff.full
  -- Fullness of the slice forgetful functor is equivalent to subterminality.
  exact isSubterminal_of_over_forget_full (J := J)

/-- Lemma 7.43.3: after replacing a sheaf by a representable sheaf on the
replacement site, the canonical localization embedding hypothesis should force that representing
object to be subterminal. -/
theorem representableReplacement_subterminal_of_localizationEmbedding
    {C₀ : Type (max u v)} [Category C₀] (J₀ : GrothendieckTopology C₀)
    (a : C ⥤ C₀) [a.IsDenseSubsite J J₀]
    {C' : Type (max u v)} [Category C'] (J' : GrothendieckTopology C')
    [J'.Subcanonical] [HasFiniteLimits C']
    (v' : C₀ ⥤ C') [v'.IsDenseSubsite J₀ J']
    (ℱ : Sheaf J (Type v)) (U₀ : C')
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F]
    (hrepr :
      Nonempty
        (CategoryTheory.yoneda.obj U₀ ≅
          ((sheafEquiv J₀ J' v' (Type (max u v))).functor.obj
            ((sheafEquiv J J₀ a (Type (max u v))).functor.obj
              ((sheafCompose J CategoryTheory.uliftFunctor.{max u v, v}).obj ℱ))).obj))
    (hemb : (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).IsEmbedding) :
    IsSubterminal (J'.yoneda.obj U₀) := by
  -- Route correction: avoid the previous representable-counit/product transport and first prove
  -- that the original sheaf is subterminal from the localization embedding.
  have hℱ : IsSubterminal ℱ :=
    isSubterminal_of_localizationMorphism_isEmbedding (J := J) (ℱ := ℱ) hemb
  -- The replacement-site equivalence transports subterminality to the representable witness.
  exact (replacement_site_isSubterminal_iff (J := J) J₀ a J' v' ℱ U₀ hrepr).1 hℱ

/-
Source correction for Lemma 7.43.3: keep the remaining proof on the route used in the text.
After Lemma 7.29.5, work on a subcanonical site with finite limits and a final object `X`, and
replace `ℱ` by a representable sheaf `h_U`. The forward direction should use the source fact that
`U ⟶ X` is mono/subterminal, hence Lemma 7.27.4 gives `j_U^{-1} j_{U,*} = id`, so the slice
localization is a subtopos. The reverse direction should evaluate the embedding condition on
representables: from `j_U^{-1} j_{U,*} h_{Z/U} ≅ h_{Z/U}` at `U` get
`Hom_{C/U}(U ×_X U, Z/U) ≅ Hom_{C/U}(U, Z/U)` for every `Z/U`; Yoneda gives
`U ×_X U ≅ U`, hence `U ⟶ X` is a mono and `h_U` is subterminal.
-/

/- Domain-style sampling for Lemma 7.43.3:
- primary domain: subtopoi of a sheaf topos arising from slice-topos localizations at
  subterminal sheaves;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `IsSubtopos`;
- best owner abstraction: the canonical left-hand owner is `IsSubterminal ℱ`, while
  `Mono (terminal.from ℱ)` is only the bridge/view expressing the same notion as a subobject of
  the terminal sheaf;
- primitive data: the sheaf `ℱ`;
- derived API: the source-facing reformulation in terms of `Mono (terminal.from ℱ)`.

Source/core/bridge triage:
- `source-facing`: the textbook phrasing that `ℱ ⟶ 1` is monic and the slice topos is a subtopos;
- `core/canonical`: `IsSubterminal ℱ` and the embedding condition on the canonical
  localization morphism attached to `localizationProjection ℱ`;
- `bridge/view`: `Mono (terminal.from ℱ)` via the standard subterminal equivalence.

The tempting owner `(Over.forget ℱ).essImage`, and even the bare statement that the localization
direct-image essential image is some subtopos, is not the source statement: those formulations do
not require the canonical slice morphism itself to be an embedding. The source owner is the
embedding predicate on the localization morphism attached to `localizationProjection ℱ`. -/
-- Proof sketch: for the forward implication, the localization
-- `localizationProjection ℱ : ℱ.obj.Elementsᵒᵖ ⥤ C` is the slice-topos morphism from the text,
-- and its direct image is fully faithful when `ℱ` is subterminal. For the reverse implication,
-- reduce to the representable case via Lemma 7.29.5 and use the text's self-pullback/Yoneda
-- argument to show that the representing map is monic.
/-- Helper for Lemma 7.43.3: a sheaf `ℱ` on a site `(𝒞, J)` is subterminal if and only if the canonical
localization/slice morphism `Sh(𝒞, J) / ℱ ⟶ Sh(𝒞, J)` is an embedding of topoi. -/
theorem sheaf_slice_isSubtopos_iff_isSubterminal
    (ℱ : Sheaf J (Type v))
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    IsSubterminal ℱ ↔
      (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).IsEmbedding := by
  constructor
  · intro hℱ
    -- Source route: prove that the direct image of the localization morphism associated to
    -- `localizationProjection ℱ` is fully faithful. In the representable replacement this is
    -- Lemma 7.27.4 applied to the monomorphism `U -> X`.
    exact localization_morphism_isEmbedding_of_isSubterminal (J := J) hℱ
  · intro hℱ
    -- Source route: from the subtopos presentation of `j_{ℱ,*}`, pass to the replacement site
    -- where `ℱ = h_U`; evaluating `j_U^{-1} j_{U,*}` on representables and using Yoneda gives
    -- `U ×_X U ≅ U`, hence `U -> X` is mono and `ℱ` is subterminal.
    rcases representable_slice_replacement_site (J := J) ℱ with
      ⟨C₀, hC₀, J₀, a, hdense, C', hC', J', hsubcan, hfinite, v', hdense', U₀, hrepr⟩
    letI : Category C₀ := hC₀
    letI : a.IsDenseSubsite J J₀ := hdense
    letI : Category C' := hC'
    letI : J'.Subcanonical := hsubcan
    letI : HasFiniteLimits C' := hfinite
    letI : v'.IsDenseSubsite J₀ J' := hdense'
    have hU₀ : IsSubterminal (J'.yoneda.obj U₀) :=
      representableReplacement_subterminal_of_localizationEmbedding
        (J := J) J₀ a J' v' ℱ U₀ hrepr hℱ
    -- The replacement-site equivalence transports the representable subterminality back to
    -- the original sheaf.
    exact
      (replacement_site_isSubterminal_iff
        (J := J) J₀ a J' v' ℱ U₀ hrepr).2 hU₀

/-- Source-facing reformulation of Lemma 7.43.3: a sheaf `ℱ` is a subobject of the terminal sheaf
if and only if the canonical localization/slice morphism at `ℱ` is an embedding. -/
theorem sheaf_slice_isSubtopos_iff_subterminal
    (ℱ : Sheaf J (Type v))
    [∀ F : ℱ.obj.Elementsᵒᵖᵒᵖ ⥤ Type v,
      (localizationProjection ℱ).op.HasPointwiseRightKanExtension F] :
    Mono (terminal.from ℱ) ↔
      (localizationMorphismOfTopoiIn (J := J) (ℱ := ℱ)).IsEmbedding := by
  constructor
  · intro hℱ
    letI : Mono (terminal.from ℱ) := hℱ
    exact (sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).1
      isSubterminal_of_mono_terminal_from
  · intro hℱ
    exact (IsSubterminal.mono_terminal_from
      ((sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).2 hℱ))

end

end CategoryTheory

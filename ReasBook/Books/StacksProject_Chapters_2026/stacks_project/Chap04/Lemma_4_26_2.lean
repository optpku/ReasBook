module

public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Filtered.Grothendieck
public import Mathlib.CategoryTheory.Presentable.Finite
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Cardinal

universe w v v' u u'

namespace CategoryTheory

attribute [local instance] fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {P : ObjectProperty C}

/- Domain-style sampling:
- Primary domain: accessible category theory and filtered-colimit extensions from a small full
  subcategory of finitely presentable objects.
- Core/canonical declarations inspected:
  - `ObjectProperty.IsCardinalFilteredGenerator`
  - `Functor.isFinitelyAccessible_iff_preservesFilteredColimits`
  - `Functor.HasLeftKanExtension`
- Best owner abstraction: the hypothesis that the source subcategory consists of categorically
  compact objects and generates `C` by filtered colimits is already packaged canonically as
  `P.IsCardinalFilteredGenerator ℵ₀`.
- Source/core/bridge triage:
  - `source-facing`: a unique strict extension `F : C ⥤ D` of `F' : P.FullSubcategory ⥤ D`
    preserving filtered colimits;
  - `core/canonical`: the filtered-generator hypothesis `P.IsCardinalFilteredGenerator ℵ₀`;
  - `bridge/view`: Kan-extension machinery is relevant for proofs, but it is not the public owner
    of this statement. -/

namespace ObjectProperty.IsCardinalFilteredGenerator

variable [ObjectProperty.Small.{w} P]

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: a chosen filtered presentation by objects of `P` is final in the
comma category of arrows from `P.ι` into the presented object. -/
lemma presentation_to_costructuredArrow_final
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {J : Type w} [SmallCategory J] [IsFiltered J] {X : C}
    (p : P.ColimitOfShape J X) :
    p.toCostructuredArrow.Final := by
  -- We formalize the textbook compactness argument: every map from an object of `P` into `X`
  -- factors through some stage of the presentation, and two such factorizations agree later on.
  letI : EssentiallySmall.{w} J := by infer_instance
  letI : IsCardinalFiltered J (ℵ₀ : Cardinal.{w}) := by
    rw [isCardinalFiltered_aleph0_iff]
    infer_instance
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨?_, ?_⟩
  · intro f
    letI : IsCardinalPresentable (P.ι.obj f.left) (ℵ₀ : Cardinal.{w}) := by
      simpa using
        (show isCardinalPresentable C (ℵ₀ : Cardinal.{w}) (P.ι.obj f.left) from
          hP.le_isCardinalPresentable _ f.left.property)
    obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit
      (κ := (ℵ₀ : Cardinal.{w})) p.isColimit f.hom
    exact ⟨j, ⟨CostructuredArrow.homMk (ObjectProperty.homMk g) (by simpa [hg])⟩⟩
  · intro d c s s'
    letI : IsCardinalPresentable d.left.obj (ℵ₀ : Cardinal.{w}) := by
      exact hP.le_isCardinalPresentable _ d.left.property
    obtain ⟨k, t, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
      (κ := (ℵ₀ : Cardinal.{w})) p.isColimit s.left.hom s'.left.hom (by
        simpa using s.w.trans s'.w.symm)
    exact ⟨k, t, by
      apply CostructuredArrow.hom_ext
      apply ObjectProperty.hom_ext
      simpa using hk⟩

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the inclusion `P.ι` admits pointwise left Kan extensions because
each comma diagram is controlled by a chosen small filtered presentation. -/
lemma has_pointwise_leftKanExtension_of_filtered_generator_of_size
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D) :
    P.ι.HasPointwiseLeftKanExtension F' := by
  intro X
  -- We choose a small filtered presentation of `X` by objects of `P`.
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  letI : IsFiltered J := by
    rw [← isCardinalFiltered_aleph0_iff]
    infer_instance
  letI : p.toCostructuredArrow.Final := presentation_to_costructuredArrow_final hP p
  -- The lifted presentation already lands in `P.FullSubcategory`, so its image under `F'`
  -- has a colimit; finality transports that colimit to the comma diagram.
  haveI : HasColimit (p.toCostructuredArrow ⋙ CostructuredArrow.proj P.ι X ⋙ F') := by
    simpa using (show HasColimit ((P.lift p.diag p.prop_diag_obj) ⋙ F') by infer_instance)
  exact Functor.Final.hasColimit_of_comp p.toCostructuredArrow

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the inclusion `P.ι` admits pointwise left Kan extensions because
each comma diagram is controlled by a chosen small filtered presentation. -/
lemma has_pointwise_leftKanExtension_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D) :
    P.ι.HasPointwiseLeftKanExtension F' := by
  exact has_pointwise_leftKanExtension_of_filtered_generator_of_size hP F'

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: a restriction isomorphism `P.ι ⋙ G ≅ F'` identifies the
`F'`-diagram coming from a chosen presentation with the corresponding `G`-diagram. -/
noncomputable def presentation_lift_comp_iso_of_extension_iso
    {J : Type w} [SmallCategory J] {X : C}
    (p : P.ColimitOfShape J X) {G : C ⥤ D} {F' : P.FullSubcategory ⥤ D}
    (i : P.ι ⋙ G ≅ F') :
    P.lift p.diag p.prop_diag_obj ⋙ F' ≅ p.diag ⋙ G :=
  -- The restriction isomorphism turns the lifted `F'`-diagram into the original `G`-diagram.
  Functor.isoWhiskerLeft _ i.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (P.liftCompιIso p.diag p.prop_diag_obj) _

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: after transporting a chosen presentation along the restriction
isomorphism `P.ι ⋙ G ≅ F'`, the cocone legs agree with the whiskered extension cocone legs. -/
lemma presentation_lift_comp_iso_of_extension_iso_hom_app_comp_ι
    {J : Type w} [SmallCategory J] {X : C}
    (p : P.ColimitOfShape J X) {G : C ⥤ D} {F' : P.FullSubcategory ⥤ D}
    (i : P.ι ⋙ G ≅ F') (j : J) :
    (presentation_lift_comp_iso_of_extension_iso (p := p) (G := G) (F' := F') i).hom.app j ≫
        G.map (p.ι.app j) =
      i.inv.app { obj := p.diag.obj j, property := p.prop_diag_obj j } ≫ G.map (p.ι.app j) := by
  -- Unfolding the presentation data shows that the extra transport is just the identity.
  dsimp [presentation_lift_comp_iso_of_extension_iso]
  rw [show (P.liftCompιIso p.diag p.prop_diag_obj).hom.app j = 𝟙 _ by rfl]
  simpa using
    (show i.inv.app ((P.lift p.diag p.prop_diag_obj).obj j) ≫ G.map (p.ι.app j) =
        i.inv.app { obj := p.diag.obj j, property := p.prop_diag_obj j } ≫ G.map (p.ι.app j) from
      rfl)

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the canonical pointwise extension evaluated at a chosen filtered
presentation is the colimit of the corresponding stagewise extension diagram. -/
noncomputable def pointwise_extension_obj_iso_of_presentation
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [SmallCategory J] [IsFiltered J] {X : C}
    (p : P.ColimitOfShape J X) :
    (P.ι.pointwiseLeftKanExtension F').obj X ≅
      colimit (p.diag ⋙ P.ι.pointwiseLeftKanExtension F') := by
  let F : C ⥤ D := P.ι.pointwiseLeftKanExtension F'
  let hF := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  letI : IsIso (P.ι.pointwiseLeftKanExtensionUnit F') := hF.isIso_hom
  let i : P.ι ⋙ F ≅ F' := (asIso (P.ι.pointwiseLeftKanExtensionUnit F')).symm
  letI : p.toCostructuredArrow.Final := presentation_to_costructuredArrow_final hP p
  -- We first compute the pointwise Kan extension by the comma-category colimit.
  refine (Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit
    (F := F') (hF X)) ≪≫ ?_
  -- Finality replaces that comma-category colimit with the chosen filtered presentation.
  refine (Functor.Final.colimitIso p.toCostructuredArrow
    (CostructuredArrow.proj P.ι X ⋙ F')).symm ≪≫ ?_
  -- The restriction isomorphism identifies the lifted `F'`-diagram with the stagewise `F`-diagram.
  exact HasColimit.isoOfNatIso
    (presentation_lift_comp_iso_of_extension_iso (p := p) (G := F) (F' := F') i)

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the unit of the canonical pointwise extension is an isomorphism on
the generating subcategory. -/
lemma pointwiseLeftKanExtensionUnit_isIso
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F'] :
    IsIso (P.ι.pointwiseLeftKanExtensionUnit F') := by
  -- The chosen pointwise extension is pointwise left Kan, so the fully faithful unit is invertible.
  exact (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F').isIso_hom

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: any extension that already preserves filtered colimits is itself
pointwise left Kan along `P.ι`, because every comma diagram is computed by a chosen presentation. -/
noncomputable def isPointwiseLeftKanExtension_of_preservesFilteredColimitsOfSize
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {F' : P.FullSubcategory ⥤ D} {G : C ⥤ D}
    (i : P.ι ⋙ G ≅ F')
    [PreservesFilteredColimitsOfSize.{w, w} G] :
    (Functor.LeftExtension.mk G i.symm.hom).IsPointwiseLeftKanExtension := by
  intro X
  classical
  -- We compute the comma colimit for `X` from a chosen `w`-small filtered presentation.
  let J : Type w := Classical.choose (hP.exists_colimitsOfShape X)
  let hJ :
      ∃ (_ : SmallCategory J) (_ : IsCardinalFiltered J (ℵ₀ : Cardinal.{w})),
        P.colimitsOfShape J X :=
    Classical.choose_spec (hP.exists_colimitsOfShape X)
  let _ : SmallCategory J := Classical.choose hJ
  let hJ' :
      ∃ (_ : IsCardinalFiltered J (ℵ₀ : Cardinal.{w})), P.colimitsOfShape J X :=
    Classical.choose_spec hJ
  let _ : IsCardinalFiltered J (ℵ₀ : Cardinal.{w}) := Classical.choose hJ'
  let hJ'' : P.colimitsOfShape J X := Classical.choose_spec hJ'
  letI : IsFiltered J := by
    rw [← isCardinalFiltered_aleph0_iff]
    infer_instance
  let p : P.ColimitOfShape J X := Classical.choice hJ''
  let E : Functor.LeftExtension P.ι F' := Functor.LeftExtension.mk G i.symm.hom
  letI : p.toCostructuredArrow.Final := presentation_to_costructuredArrow_final hP p
  -- The transported image cocone of the chosen presentation already computes the whiskered
  -- comma cocone, because the restriction isomorphism identifies the two diagrams stagewise.
  have hp :
      IsColimit (Cocone.whisker p.toCostructuredArrow (E.coconeAt X)) := by
    have hp₁ :
        IsColimit ((Cocone.precompose
          (presentation_lift_comp_iso_of_extension_iso (p := p) (G := G) (F' := F') i).hom).obj
          (Functor.mapCocone G p.cocone)) := by
      exact (IsColimit.precomposeHomEquiv
        (presentation_lift_comp_iso_of_extension_iso (p := p) (G := G) (F' := F') i)
        (Functor.mapCocone G p.cocone)).2 (isColimitOfPreserves G p.isColimit)
    refine IsColimit.ofIsoColimit hp₁ ?_
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    simpa [E] using
      presentation_lift_comp_iso_of_extension_iso_hom_app_comp_ι
        (p := p) (G := G) (F' := F') i j
  -- Finality transfers this colimit back to the full comma category.
  exact (Functor.Final.isColimitWhiskerEquiv p.toCostructuredArrow (E.coconeAt X)).1 hp

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: every comma category `CostructuredArrow P.ι X` is filtered, because a
chosen filtered presentation of `X` is final in it. -/
lemma costructuredArrow_isFiltered_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    (X : C) :
    IsFiltered (CostructuredArrow P.ι X) := by
  -- We push filteredness across the final functor supplied by a chosen filtered presentation.
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  letI : IsFiltered J := by
    rw [← isCardinalFiltered_aleph0_iff]
    infer_instance
  letI : p.toCostructuredArrow.Final := presentation_to_costructuredArrow_final hP p
  exact IsFiltered.of_final p.toCostructuredArrow

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the comma category `CostructuredArrow P.ι X` is `w`-finally small,
because a chosen `w`-small filtered presentation of `X` is already final in it. -/
lemma costructuredArrow_finallySmall_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    (X : C) :
    _root_.CategoryTheory.FinallySmall.{w} (CostructuredArrow P.ι X) := by
  -- We reuse the chosen presentation from the filtered-generator hypothesis as the small final
  -- model promised by `FinallySmall`.
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  letI : IsFiltered J := by
    rw [← isCardinalFiltered_aleph0_iff]
    infer_instance
  letI : EssentiallySmall.{w} J :=
    essentiallySmall_of_small_of_locallySmall J
  letI : p.toCostructuredArrow.Final := presentation_to_costructuredArrow_final hP p
  exact _root_.CategoryTheory.finallySmall_of_final_of_essentiallySmall.{w}
    p.toCostructuredArrow

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: a functor preserving `v'`-small filtered colimits preserves any
filtered colimit indexed by a `v'`-finally small locally `v'`-small category. -/
lemma preservesColimitsOfShape_of_finallySmall_filtered_shape
    {J : Type*} [Category J] [IsFiltered J] [LocallySmall.{v'} J]
    [_root_.CategoryTheory.FinallySmall.{v'} J]
    (G : C ⥤ D) [PreservesFilteredColimits G] :
    PreservesColimitsOfShape J G := by
  -- The `FinallySmall` API reduces an arbitrary filtered shape to a `v'`-small final model,
  -- so preservation follows from the ambient `PreservesFilteredColimits` hypothesis.
  let _ : _root_.CategoryTheory.FinallySmall.{v'} J := inferInstance
  simpa using CategoryTheory.FinallySmall.preservesColimitsOfShape_of_isFiltered.{v'} (C := J) G

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: a comma category over a constant diagram forgets its indexing object
and becomes the usual costructured-arrow category. This keeps the cocone comparison below as a
composition of concrete functors, instead of hand-writing Grothendieck transport equations. -/
def commaConstToCostructuredArrow
    {J : Type w} [Category.{w} J] (X : C) :
    Comma P.ι ((Functor.const J).obj X) ⥤ CostructuredArrow P.ι X where
  obj Y := CostructuredArrow.mk Y.hom
  map f := CostructuredArrow.homMk f.left (by
    simpa using f.w)
  map_id Y := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the comparison functor from the Grothendieck category of
stagewise arrows `P -> K j` to the comma category `P/colim K`, obtained by composing with the
colimit cocone leg `K j -> colim K`. -/
def grothendieckCostructuredArrowToColimit
    {J : Type w} [Category.{w} J]
    (K : J ⥤ C) (c : Cocone K) :
    Grothendieck (K ⋙ CostructuredArrow.functor P.ι) ⥤ CostructuredArrow P.ι c.pt :=
  CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
    Comma.mapRight P.ι c.ι ⋙
      commaConstToCostructuredArrow (P := P) c.pt

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: every arrow from an object of `P` to a filtered colimit factors
through one stage of the filtered diagram. This is the first half of the finality criterion for
`grothendieckCostructuredArrowToColimit`. -/
lemma grothendieckCostructuredArrowToColimit_exists_factorization
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) {c : Cocone K} (hc : IsColimit c) :
    ∀ d : CostructuredArrow P.ι c.pt,
      ∃ X : Grothendieck (K ⋙ CostructuredArrow.functor P.ι),
        Nonempty (d ⟶ (grothendieckCostructuredArrowToColimit (P := P) K c).obj X) := by
  intro d
  letI : IsCardinalFiltered J (ℵ₀ : Cardinal.{w}) := by
    rw [isCardinalFiltered_aleph0_iff]
    infer_instance
  letI : IsCardinalPresentable d.left.obj (ℵ₀ : Cardinal.{w}) := by
    exact hP.le_isCardinalPresentable _ d.left.property
  letI : IsCardinalPresentable (P.ι.obj d.left) (ℵ₀ : Cardinal.{w}) := by
    change IsCardinalPresentable d.left.obj (ℵ₀ : Cardinal.{w})
    infer_instance
  obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := (ℵ₀ : Cardinal.{w})) hc d.hom
  refine ⟨⟨j, CostructuredArrow.mk g⟩, ⟨CostructuredArrow.homMk (𝟙 d.left) ?_⟩⟩
  simpa [grothendieckCostructuredArrowToColimit, commaConstToCostructuredArrow,
    CostructuredArrow.grothendieckPrecompFunctorToComma, Category.assoc] using hg

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: if two arrows into a stagewise approximation become equal after
passing to the filtered colimit, finite presentability of the source object of `P` makes them equal
after moving to a later stage. This is the compactness equalization step in the Stacks proof. -/
lemma grothendieckCostructuredArrowToColimit_exists_stage_equalization
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) {c : Cocone K} (hc : IsColimit c)
    {d : CostructuredArrow P.ι c.pt}
    {X : Grothendieck (K ⋙ CostructuredArrow.functor P.ι)}
    (s s' : d ⟶ (grothendieckCostructuredArrowToColimit (P := P) K c).obj X) :
    ∃ (j : J) (u : X.base ⟶ j),
      s.left.hom ≫ X.fiber.hom ≫ K.map u = s'.left.hom ≫ X.fiber.hom ≫ K.map u := by
  letI : IsCardinalFiltered J (ℵ₀ : Cardinal.{w}) := by
    rw [isCardinalFiltered_aleph0_iff]
    infer_instance
  letI : IsCardinalPresentable d.left.obj (ℵ₀ : Cardinal.{w}) := by
    exact hP.le_isCardinalPresentable _ d.left.property
  letI : IsCardinalPresentable (P.ι.obj d.left) (ℵ₀ : Cardinal.{w}) := by
    change IsCardinalPresentable d.left.obj (ℵ₀ : Cardinal.{w})
    infer_instance
  have hs : s.left.hom ≫ X.fiber.hom ≫ c.ι.app X.base = d.hom := by
    simpa [grothendieckCostructuredArrowToColimit, commaConstToCostructuredArrow,
      CostructuredArrow.grothendieckPrecompFunctorToComma, Category.assoc] using s.w
  have hs' : s'.left.hom ≫ X.fiber.hom ≫ c.ι.app X.base = d.hom := by
    simpa [grothendieckCostructuredArrowToColimit, commaConstToCostructuredArrow,
      CostructuredArrow.grothendieckPrecompFunctorToComma, Category.assoc] using s'.w
  obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit'
    (κ := (ℵ₀ : Cardinal.{w})) hc (s.left.hom ≫ X.fiber.hom)
      (s'.left.hom ≫ X.fiber.hom) (by
        simpa [Category.assoc] using hs.trans hs'.symm)
  exact ⟨j, u, by simpa [Category.assoc] using hu⟩

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: for a filtered diagram `K`, the Grothendieck category of all
stagewise arrows from objects of `P` into the objects `K j` is filtered. This is the categorical
form of the source text's filtered system of finite-presentable approximations. -/
lemma grothendieck_costructuredArrow_isFiltered_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) :
    IsFiltered (Grothendieck (K ⋙ CostructuredArrow.functor P.ι)) := by
  haveI : ∀ j : J, IsFiltered ((K ⋙ CostructuredArrow.functor P.ι).obj j) := fun j =>
    costructuredArrow_isFiltered_of_filtered_generator (P := P) hP (K.obj j)
  infer_instance

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the stagewise-arrow Grothendieck category is final in
`P/colim K`. This packages the two compactness steps used in the Stacks proof: factor an arrow
through a stage, and equalize two such factorizations after moving farther along the filtered
system. -/
lemma grothendieckCostructuredArrowToColimit_final
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) {c : Cocone K} (hc : IsColimit c) :
    (grothendieckCostructuredArrowToColimit (P := P) K c).Final := by
  haveI : IsFiltered (Grothendieck (K ⋙ CostructuredArrow.functor P.ι)) :=
    grothendieck_costructuredArrow_isFiltered_of_filtered_generator (P := P) hP K
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨grothendieckCostructuredArrowToColimit_exists_factorization
    (P := P) hP K hc, ?_⟩
  intro d X s s'
  obtain ⟨j, u, hu⟩ :=
    grothendieckCostructuredArrowToColimit_exists_stage_equalization
      (P := P) hP K hc s s'
  let A : CostructuredArrow P.ι (K.obj j) :=
    CostructuredArrow.mk (s.left.hom ≫ X.fiber.hom ≫ K.map u)
  let B : CostructuredArrow P.ι (K.obj j) :=
    (CostructuredArrow.map (K.map u)).obj X.fiber
  let a : A ⟶ B := CostructuredArrow.homMk s.left (by
    rfl)
  let b : A ⟶ B := CostructuredArrow.homMk s'.left (by
    simpa [A, B, Category.assoc] using hu.symm)
  haveI : IsFiltered (CostructuredArrow P.ι (K.obj j)) :=
    costructuredArrow_isFiltered_of_filtered_generator (P := P) hP (K.obj j)
  let Q : CostructuredArrow P.ι (K.obj j) := IsFiltered.coeq a b
  let q : B ⟶ Q := IsFiltered.coeqHom a b
  refine ⟨⟨j, Q⟩, ⟨u, q⟩, ?_⟩
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  simpa [grothendieckCostructuredArrowToColimit, commaConstToCostructuredArrow,
    CostructuredArrow.grothendieckPrecompFunctorToComma, A, B, a, b, Category.assoc] using
      congrArg (fun q => q.left.hom) (IsFiltered.coeq_condition a b)

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the canonical pointwise extension evaluated at a stage of a filtered
diagram is the colimit over the corresponding fiber `P/K j`. -/
noncomputable def pointwise_extension_obj_iso_of_stage_comma
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (j : J) :
    (P.ι.pointwiseLeftKanExtension F').obj (K.obj j) ≅
      colimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') := by
  let hF := Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  exact Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit
    (F := F') (hF (K.obj j))

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the Grothendieck fiber diagram over a stage has a colimit, because it
is isomorphic to the usual comma diagram `P/K j` used in the pointwise Kan extension formula. -/
noncomputable instance hasColimit_stage_grothendieck_precomp
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (j : J) :
    HasColimit ((Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
        Comma.fst P.ι K) ⋙ F') := by
  haveI : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
    (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j)
  exact hasColimit_of_iso
    (F := CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
    (G := (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K) ⋙ F')
    (Functor.isoWhiskerRight
      (CostructuredArrow.ιCompGrothendieckPrecompFunctorToCommaCompFst P.ι K j) F')

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the fiber-transition diagram in the Grothendieck construction is
isomorphic to the ordinary comma diagram at the source stage. This is the functorial version of the
stagewise comma computation used by the Grothendieck Fubini API. -/
noncomputable def stage_map_grothendieck_precomp_iso
    (F' : P.FullSubcategory ⥤ D)
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {i j : J} (f : i ⟶ j) :
    CostructuredArrow.proj P.ι (K.obj i) ⋙ F' ≅
      (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
        Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun x => by
    cases x
    simpa [Functor.comp_map, CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left,
      CostructuredArrow.map, Comma.mapRight] using
      F'.congr_map (by
        apply ObjectProperty.hom_ext
        erw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
        simp))

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: every fiber-transition diagram needed for Grothendieck Fubini has a
colimit, transported from the ordinary comma diagram at the source stage. -/
noncomputable instance hasColimit_stage_grothendieck_precomp_map
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {i j : J} (f : i ⟶ j) :
    HasColimit (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
      Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := by
  haveI : HasColimit (CostructuredArrow.proj P.ι (K.obj i) ⋙ F') :=
    (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj i)
  exact hasColimit_of_iso
    (F := CostructuredArrow.proj P.ι (K.obj i) ⋙ F')
    (G := ((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
      Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')
    (stage_map_grothendieck_precomp_iso (P := P) F' K f).symm

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the total Grothendieck stagewise diagram has a colimit. This is the
Fubini step: fiber colimits are supplied by the pointwise Kan formula at each stage, and the base
colimit is filtered. -/
noncomputable instance hasColimit_grothendieck_precomp
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] [IsFiltered J] (K : J ⥤ C) :
    HasColimit (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
      Comma.fst P.ι K ⋙ F') := by
  haveI : ∀ {i j : J} (f : i ⟶ j),
      HasColimit (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
        Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    fun f => hasColimit_stage_grothendieck_precomp_map (P := P) F' K f
  haveI : HasColimitsOfShape J D := inferInstance
  exact Limits.hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit
    (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the stagewise map of the chosen pointwise extension sends each comma
colimit leg to the corresponding leg after applying `CostructuredArrow.map (K.map f)`. -/
lemma pointwise_extension_stage_leg_map
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {i j : J} (f : i ⟶ j)
    (X : CostructuredArrow P.ι (K.obj i)) :
    colimit.ι (CostructuredArrow.proj P.ι (K.obj i) ⋙ F') X ≫
        (P.ι.pointwiseLeftKanExtension F').map (K.map f) =
      colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
        ((CostructuredArrow.map (K.map f)).obj X) := by
  -- This is exactly the explicit `colimit.desc` formula built into `pointwiseLeftKanExtension.map`.
  let c : Cocone (CostructuredArrow.proj P.ι (K.obj i) ⋙ F') :=
    Cocone.mk (colimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F'))
      { app := fun g =>
          colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
            ((CostructuredArrow.map (K.map f)).obj g)
        naturality := fun g₁ g₂ φ => by
          simpa using
            colimit.w (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
              ((CostructuredArrow.map (K.map f)).map φ) }
  simpa [Functor.pointwiseLeftKanExtension_map, c] using
    (colimit.ι_desc (F := CostructuredArrow.proj P.ι (K.obj i) ⋙ F') c X)

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: at each stage `j`, the Grothendieck fiber colimit is identified with
the value of the canonical pointwise extension at `K.obj j`. -/
noncomputable def pointwise_extension_stage_grothendieck_iso
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (j : J)
    (hstage : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (hproj : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')) :
    colimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') ≅
        (P.ι.pointwiseLeftKanExtension F').obj (K.obj j) := by
  -- We compute the stagewise comma colimit and then transport it across the Grothendieck/comma
  -- identification for the fiber over `j`.
  letI : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := hstage
  letI : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') := hproj
  exact
    (@HasColimit.isoOfNatIso _ _ _ _ _ _ hstage hproj
      (Functor.isoWhiskerRight
        (CostructuredArrow.ιCompGrothendieckPrecompFunctorToCommaCompFst P.ι K j) F')) ≪≫
      (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).symm

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the canonical transformation from the Grothendieck diagram to the
fiberwise colimit identifies the `fiberwiseColimit.map` leg with the corresponding stage leg. -/
lemma pointwise_extension_grothendieck_fiber_pre_map
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {i j : J} (f : i ⟶ j)
    (hstage_i : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (hstage_j : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (X : CostructuredArrow P.ι (K.obj i)) :
    colimit.ι
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') X ≫
      (Limits.fiberwiseColimit
          (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')).map f =
    colimit.ι
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')
        (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor.obj X) := by
  -- The Grothendieck naturality square already says that moving along `f` is the stage-`j` leg.
  letI : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := hstage_i
  letI : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := hstage_j
  have hnat :=
    ((Limits.natTransIntoForgetCompFiberwiseColimit
        (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')).naturality
      (Grothendieck.toTransport
        (⟨i, X⟩ : Grothendieck (K ⋙ CostructuredArrow.functor P.ι)) f)).symm
  -- Converting the transported fiber back to `CostructuredArrow.map` makes the stage map
  -- literally the identity on the `P`-object.
  convert hnat using 1
  · change
      colimit.ι
          (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
            CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')
          ((Comma.mapRight P.ι ((Functor.const (Discrete PUnit.{1})).map (K.map f))).obj X) =
        F'.map (𝟙 X.left) ≫
          colimit.ι
            (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
              CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')
            ((Comma.mapRight P.ι ((Functor.const (Discrete PUnit.{1})).map (K.map f))).obj X)
    simp

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the stagewise Grothendieck/comma comparison sends each comma
generator to the canonical pointwise-Kan-extension leg. -/
lemma pointwise_extension_stage_iso_generator_leg
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (j : J)
    (hproj_j : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F'))
    (hstage_j : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (X : CostructuredArrow P.ι (K.obj j)) :
    colimit.ι
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') X ≫
      (pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K j hstage_j hproj_j).hom =
    (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
      (P.ι.pointwiseLeftKanExtension F').map X.hom := by
  -- We first cross the Grothendieck/comma identification, then use the generic pointwise
  -- left-Kan-extension colimit formula on the comma object `X`.
  let hpoint :
      (Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
        (P.ι.pointwiseLeftKanExtensionUnit F')).IsPointwiseLeftKanExtensionAt (K.obj j) :=
    P.ι.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension F' (K.obj j)
  simp only [pointwise_extension_stage_grothendieck_iso, Iso.trans_hom]
  have hw :
      colimit.ι
          (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
            CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') X ≫
        (@HasColimit.isoOfNatIso _ _ _ _ _ _ hstage_j hproj_j
          (Functor.isoWhiskerRight
            (CostructuredArrow.ιCompGrothendieckPrecompFunctorToCommaCompFst P.ι K j) F')).hom =
      colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X := by
    simpa using
      (@HasColimit.isoOfNatIso_ι_hom _ _ _ _ _ _ hstage_j hproj_j
        (w := Functor.isoWhiskerRight
          (CostructuredArrow.ιCompGrothendieckPrecompFunctorToCommaCompFst P.ι K j) F') X)
  rw [← Category.assoc]
  rw [hw]
  letI : P.ι.HasPointwiseLeftKanExtensionAt F' (K.obj j) :=
    hpoint.hasPointwiseLeftKanExtensionAt
  simpa [hpoint, Functor.pointwiseLeftKanExtensionUnit, Functor.pointwiseLeftKanExtension_map,
    Category.assoc] using
    (Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_inv
      (E := Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
        (P.ι.pointwiseLeftKanExtensionUnit F'))
      (h := hpoint) X)

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the stagewise comparison isomorphisms carry the canonical
`fiberwiseColimit.map` leg to the stagewise comma-colimit leg used in
`pointwise_extension_stage_leg_map`. -/
lemma pointwise_extension_grothendieck_fiber_leg_map
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {i j : J} (f : i ⟶ j)
    (hproj_i : HasColimit (CostructuredArrow.proj P.ι (K.obj i) ⋙ F'))
    (hproj_j : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F'))
    (hstage_i : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (hstage_j : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (_hmap : HasColimit (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
      Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'))
    (X : CostructuredArrow P.ι (K.obj i)) :
    colimit.ι
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') X ≫
      (Limits.fiberwiseColimit
          (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')).map f ≫
      (pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K j hstage_j hproj_j).hom =
    colimit.ι
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') X ≫
      (pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K i hstage_i hproj_i).hom ≫
        (P.ι.pointwiseLeftKanExtension F').map (K.map f) := by
  -- We first rewrite the left branch to the stage-`j` Grothendieck generator leg.
  rw [← Category.assoc]
  rw [pointwise_extension_grothendieck_fiber_pre_map
    (P := P) (D := D) F' K f hstage_i hstage_j X]
  trans (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
      (P.ι.pointwiseLeftKanExtension F').map (X.hom ≫ K.map f)
  · -- The stage-`j` comparison is already the canonical comma-colimit formula on the
    -- transported generator `CostructuredArrow.map (K.map f) X`.
    simpa [CostructuredArrow.map, Category.assoc] using
      pointwise_extension_stage_iso_generator_leg
        (P := P) (D := D) F' K j hproj_j hstage_j
        ((CostructuredArrow.map (K.map f)).obj X)
  · -- The stage-`i` comparison gives the same normal form, and functoriality of the
    -- pointwise extension rewrites it to the desired composite.
    rw [← Category.assoc]
    rw [pointwise_extension_stage_iso_generator_leg
      (P := P) (D := D) F' K i hproj_i hstage_i X]
    simpa [Category.assoc] using
      congrArg
        (fun k => (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫ k)
        ((P.ι.pointwiseLeftKanExtension F').map_comp X.hom (K.map f))

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: evaluating the canonical pointwise extension stagewise along a
filtered diagram agrees with taking the fiberwise colimit over the Grothendieck category of pairs
`(j, Pobj ⟶ K.obj j)`. This is the functor-level version of the stagewise comma comparison used in
the Stacks proof. -/
noncomputable def pointwise_extension_iso_fiberwise_grothendieck_precomp
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) :
    K ⋙ P.ι.pointwiseLeftKanExtension F' ≅
      Limits.fiberwiseColimit
        (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := by
  let ecomp :
      ∀ j : J,
        (Limits.fiberwiseColimit
          (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F')).obj j ≅
            (P.ι.pointwiseLeftKanExtension F').obj (K.obj j) := fun j => by
      -- Each stage is identified with the corresponding comma-category colimit.
      let hproj :
          HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
        (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j)
      let hstage :
          HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
            CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
        hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K j
      exact pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K j hstage hproj
  -- We compare each stage by `ecomp` and then verify naturality on individual Grothendieck legs.
  refine Iso.symm <| NatIso.ofComponents ecomp ?_
  intro i j f
  let hproj_i :
      HasColimit (CostructuredArrow.proj P.ι (K.obj i) ⋙ F') :=
    (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj i)
  let hproj_j :
      HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
    (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j)
  let hstage_i :
      HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K i
  let hstage_j :
      HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K j
  let hmap :
      HasColimit (((K ⋙ CostructuredArrow.functor P.ι).map f).toFunctor ⋙
        Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    hasColimit_stage_grothendieck_precomp_map (P := P) (D := D) F' K f
  letI : HasColimit (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) i ⋙
      CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := hstage_i
  -- Naturality is checked legwise on the comma-colimit cocones.
  apply colimit.hom_ext
  intro X
  simpa [ecomp] using
    pointwise_extension_grothendieck_fiber_leg_map
      (P := P) (D := D) F' K f hproj_i hproj_j hstage_i hstage_j hmap X

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: stagewise, the comparison from the pointwise extension to the
Grothendieck fiberwise colimit is the inverse of the stagewise comma-colimit comparison. -/
lemma pointwise_extension_iso_fiberwise_grothendieck_precomp_hom_app
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) (j : J) :
    (pointwise_extension_iso_fiberwise_grothendieck_precomp (P := P) (D := D) F' K).hom.app j =
      (pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K j
        (hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K j)
        ((inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j))).inv := by
  rfl

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the colimit of the Grothendieck diagram of stagewise arrows computes
the value of the canonical pointwise extension at the colimit object of the filtered diagram. -/
noncomputable def grothendieck_precomp_colimit_iso_pointwise_value
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) {c : Cocone K} (hc : IsColimit c) :
    colimit (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
      Comma.fst P.ι K ⋙ F') ≅
        (P.ι.pointwiseLeftKanExtension F').obj c.pt := by
  let Fcolim :
      Grothendieck (K ⋙ CostructuredArrow.functor P.ι) ⥤ CostructuredArrow P.ι c.pt :=
    grothendieckCostructuredArrowToColimit (P := P) K c
  letI : Fcolim.Final := grothendieckCostructuredArrowToColimit_final (P := P) hP K hc
  -- Finality replaces the Grothendieck colimit by the ordinary comma colimit at `c.pt`.
  refine Functor.Final.colimitIso Fcolim (CostructuredArrow.proj P.ι c.pt ⋙ F') ≪≫ ?_
  -- The pointwise Kan-extension formula identifies that comma colimit with the desired value.
  exact
    (Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit
      (F := F') ((Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F') c.pt)).symm

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: after transporting the stage-`j` fiberwise-colimit cocone along the
stage comparison isomorphism, its generator leg is the canonical comma-object map into the target
colimit cocone. -/
lemma pointwise_extension_mapCocone_generator_leg
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {c : Cocone K}
    (j : J) (X : CostructuredArrow P.ι (K.obj j)) :
    colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
        (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv ≫
          ((Cocone.precompose
              (pointwise_extension_iso_fiberwise_grothendieck_precomp
                (P := P) (D := D) F' K).hom).obj
              (Limits.coconeFiberwiseColimitOfCocone
                (((Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
                  (P.ι.pointwiseLeftKanExtensionUnit F')).coconeAt c.pt).whisker
                  (grothendieckCostructuredArrowToColimit (P := P) K c)))).ι.app j =
      (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
        (P.ι.pointwiseLeftKanExtension F').map (X.hom ≫ c.ι.app j) := by
  let wj :
      (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') ≅
        (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
    Functor.isoWhiskerRight
      (CostructuredArrow.ιCompGrothendieckPrecompFunctorToCommaCompFst P.ι K j) F'
  let E : Functor.LeftExtension P.ι F' :=
    Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
      (P.ι.pointwiseLeftKanExtensionUnit F')
  let Fcolim :
      Grothendieck (K ⋙ CostructuredArrow.functor P.ι) ⥤ CostructuredArrow P.ι c.pt :=
    grothendieckCostructuredArrowToColimit (P := P) K c
  let t : Cocone
      (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    (E.coconeAt c.pt).whisker Fcolim
  let s :
      Cocone
        (Limits.fiberwiseColimit
          (CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
            Comma.fst P.ι K ⋙ F')) :=
    Limits.coconeFiberwiseColimitOfCocone t
  -- We first rewrite the transported stage leg as the `w_j`-transported descent from the
  -- Grothendieck fiber over `j`.
  rw [show
      ((Cocone.precompose
          (pointwise_extension_iso_fiberwise_grothendieck_precomp
            (P := P) (D := D) F' K).hom).obj s).ι.app j =
        (pointwise_extension_iso_fiberwise_grothendieck_precomp
          (P := P) (D := D) F' K).hom.app j ≫ s.ι.app j by
      rfl]
  rw [pointwise_extension_iso_fiberwise_grothendieck_precomp_hom_app
    (P := P) (D := D) F' K j]
  let hcomma : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
    (inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j)
  letI : HasColimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') := hcomma
  let hgroth :
      HasColimit
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') :=
    hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K j
  letI :
      HasColimit
        (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
          CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') := hgroth
  let wcolim :
      colimit
          (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
            CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F') ≅
        colimit (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') :=
    @HasColimit.isoOfNatIso _ _ _ _ _ _ hgroth hcomma wj
  have hstageinv :
      (pointwise_extension_stage_grothendieck_iso (P := P) (D := D) F' K j
        (hasColimit_stage_grothendieck_precomp (P := P) (D := D) F' K j)
        ((inferInstance : P.ι.HasPointwiseLeftKanExtension F') (K.obj j))).inv =
        (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).hom ≫
          wcolim.inv := by
    rfl
  -- Unfolding the stage comparison turns the left branch into the `w_j`-transported stage descent.
  rw [hstageinv]
  have hcancel :
      colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
          (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv ≫
            ((pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).hom ≫
              wcolim.inv) ≫ s.ι.app j =
        colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
          wcolim.inv ≫ s.ι.app j := by
    simpa [Category.assoc] using
      congrArg
        (fun k =>
          colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫ k ≫ s.ι.app j)
        ((pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv_hom_id_assoc
          wcolim.inv)
  calc
    colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
        (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv ≫
          ((pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).hom ≫
            wcolim.inv) ≫ s.ι.app j =
      colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
        wcolim.inv ≫ s.ι.app j := hcancel
    _ = (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
        (P.ι.pointwiseLeftKanExtension F').map (X.hom ≫ c.ι.app j) := by
      rw [show s.ι.app j = colimit.desc _
          (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j)) by
          rfl]
      have hdesc :
          wcolim.inv ≫
              colimit.desc
                (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
                  CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
                    Comma.fst P.ι K ⋙ F')
                (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j)) =
            colimit.desc (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
              ((Cocone.precompose wj.inv).obj
                (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j))) := by
        exact @HasColimit.isoOfNatIso_inv_desc _ _ _ _ _ _ hgroth hcomma
          (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j)) wj
      have hdesc_assoc :
          colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫ wcolim.inv ≫
              colimit.desc
                (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j ⋙
                  CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙
                    Comma.fst P.ι K ⋙ F')
                (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j)) =
            colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
              colimit.desc (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
                ((Cocone.precompose wj.inv).obj
                  (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k => colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫ k)
            hdesc
      have hleg :
          colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
              colimit.desc (CostructuredArrow.proj P.ι (K.obj j) ⋙ F')
                ((Cocone.precompose wj.inv).obj
                  (t.whisker (Grothendieck.ι (K ⋙ CostructuredArrow.functor P.ι) j))) =
            (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
              (P.ι.pointwiseLeftKanExtension F').map (X.hom ≫ c.ι.app j) := by
        rw [colimit.ι_desc]
        -- After the transport, the remaining leg is literally the comma-object leg of `E.coconeAt c.pt`.
        simp [wj, t, E, Fcolim, grothendieckCostructuredArrowToColimit,
          commaConstToCostructuredArrow, CostructuredArrow.grothendieckPrecompFunctorToComma]
      exact hdesc_assoc.trans hleg

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the explicit `mapCocone` leg on a comma generator is given by the
canonical unit map followed by the image of the composite into the colimit object. -/
lemma pointwise_extension_mapCocone_target_generator_leg
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {c : Cocone K}
    (j : J) (X : CostructuredArrow P.ι (K.obj j)) :
    colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
        (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv ≫
          ((P.ι.pointwiseLeftKanExtension F').mapCocone c).ι.app j =
      (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
        (P.ι.pointwiseLeftKanExtension F').map (X.hom ≫ c.ι.app j) := by
  let E : Functor.LeftExtension P.ι F' :=
    Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
      (P.ι.pointwiseLeftKanExtensionUnit F')
  let hpoint :
      E.IsPointwiseLeftKanExtensionAt (K.obj j) :=
    Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F' (K.obj j)
  have hι :
      colimit.ι (CostructuredArrow.proj P.ι (K.obj j) ⋙ F') X ≫
          (pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv =
        (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫
          (P.ι.pointwiseLeftKanExtension F').map X.hom := by
    -- This is the standard pointwise left-Kan-extension formula on the comma category `P / K j`.
    simpa [pointwise_extension_obj_iso_of_stage_comma, E, hpoint, Category.assoc] using
      (Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_inv
        (E := E) (h := hpoint) X)
  -- The only remaining step is functoriality of the extension on the composite `X.hom ≫ c.ι.app j`.
  rw [show ((P.ι.pointwiseLeftKanExtension F').mapCocone c).ι.app j =
      (P.ι.pointwiseLeftKanExtension F').map (c.ι.app j) by
      rfl]
  rw [← Category.assoc, hι]
  simpa [Category.assoc] using
    (congrArg
      (fun k => (P.ι.pointwiseLeftKanExtensionUnit F').app X.left ≫ k)
      ((P.ι.pointwiseLeftKanExtension F').map_comp X.hom (c.ι.app j))).symm

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the transported Grothendieck cocone and the explicit
`mapCocone` agree at each stage once both are compared on comma-category generators. -/
lemma pointwise_extension_mapCocone_stage_leg
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] (K : J ⥤ C) {c : Cocone K}
    (j : J) :
    ((Cocone.precompose
        (pointwise_extension_iso_fiberwise_grothendieck_precomp
          (P := P) (D := D) F' K).hom).obj
        (Limits.coconeFiberwiseColimitOfCocone
          (((Functor.LeftExtension.mk (P.ι.pointwiseLeftKanExtension F')
            (P.ι.pointwiseLeftKanExtensionUnit F')).coconeAt c.pt).whisker
            (grothendieckCostructuredArrowToColimit (P := P) K c)))).ι.app j =
      ((P.ι.pointwiseLeftKanExtension F').mapCocone c).ι.app j := by
  -- The comma-category colimit formula detects equality of maps out of `F (K.obj j)`.
  apply (cancel_epi
    ((pointwise_extension_obj_iso_of_stage_comma (P := P) (D := D) F' K j).inv)).1
  apply colimit.hom_ext
  intro X
  -- Both candidate legs reduce to the same canonical comma-generator map.
  exact
    (pointwise_extension_mapCocone_generator_leg (P := P) (D := D) F' K (c := c) j X).trans
      (pointwise_extension_mapCocone_target_generator_leg (P := P) (D := D) F' K (c := c) j X).symm

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the concrete cocone-level preservation statement for the canonical
pointwise extension. This is the exact filtered-colimit comparison in the Stacks proof: rewrite
each `F X` as the colimit over `P/X`, use compactness of objects of `P` to compare the
Grothendieck presentation of a filtered colimit with `P/colim X_i`, then commute the resulting
filtered colimits in `D`. -/
noncomputable def pointwiseLeftKanExtension_mapCocone_isColimit_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimits C] [HasFilteredColimits D]
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F']
    {J : Type w} [Category.{w} J] [IsFiltered J]
    (K : J ⥤ C) {c : Cocone K} (hc : IsColimit c) :
    IsColimit ((P.ι.pointwiseLeftKanExtension F').mapCocone c) := by
  let E : Functor.LeftExtension P.ι F' :=
    Functor.LeftExtension.mk _ (P.ι.pointwiseLeftKanExtensionUnit F')
  let hE : E.IsPointwiseLeftKanExtension :=
    Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension P.ι F'
  let Gk :
      Grothendieck (K ⋙ CostructuredArrow.functor P.ι) ⥤ D :=
    CostructuredArrow.grothendieckPrecompFunctorToComma P.ι K ⋙ Comma.fst P.ι K ⋙ F'
  let e :
      K ⋙ P.ι.pointwiseLeftKanExtension F' ≅ Limits.fiberwiseColimit Gk :=
    pointwise_extension_iso_fiberwise_grothendieck_precomp (P := P) (D := D) F' K
  let Fcolim :
      Grothendieck (K ⋙ CostructuredArrow.functor P.ι) ⥤ CostructuredArrow P.ι c.pt :=
    grothendieckCostructuredArrowToColimit (P := P) K c
  let t : Cocone Gk := (E.coconeAt c.pt).whisker Fcolim
  -- Route correction: earlier attempts tried to enlarge to arbitrary filtered sizes; here we stay
  -- in the `w`-small Grothendieck model supplied by `hP`, exactly as the source proof does.
  letI : Fcolim.Final := grothendieckCostructuredArrowToColimit_final (P := P) hP K hc
  have ht : IsColimit t := by
    -- Finality transports the pointwise comma colimit at `c.pt` to the Grothendieck category of
    -- stagewise arrows landing in the chosen filtered colimit cocone.
    exact (Functor.Final.isColimitWhiskerEquiv Fcolim (E.coconeAt c.pt)).symm (hE c.pt)
  let s : Cocone (Limits.fiberwiseColimit Gk) :=
    Limits.coconeFiberwiseColimitOfCocone t
  have hs : IsColimit s :=
    Limits.isColimitCoconeFiberwiseColimitOfCocone ht
  have hs' : IsColimit ((Cocone.precompose e.hom).obj s) :=
    (IsColimit.precomposeHomEquiv e s).2 hs
  -- We compare the transported cocone with `mapCocone c` on the canonical comma-category legs.
  have hcompare : ((Cocone.precompose e.hom).obj s) ≅
      ((P.ι.pointwiseLeftKanExtension F').mapCocone c) := by
    -- The two cocones have the same point object, so it remains to compare their stage legs.
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    -- The stagewise comparison was reduced above to equality on comma-category generators.
    simpa [e, s, t, E, Gk, Fcolim] using
      pointwise_extension_mapCocone_stage_leg (P := P) (D := D) F' K (c := c) j
  exact IsColimit.ofIsoColimit hs' hcompare

omit [ObjectProperty.Small.{w} P] in
/-- Helper for Lemma 4.26.2: the pointwise left Kan extension along a finite-presentable
filtered generator preserves the same filtered colimits. The class-level statement is just the
packaging of the cocone-level comparison above. -/
lemma pointwiseLeftKanExtension_preservesFilteredColimitsOfSize_of_filtered_generator
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimits C] [HasFilteredColimits D]
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D)
    [P.ι.HasPointwiseLeftKanExtension F'] :
    PreservesFilteredColimitsOfSize.{w, w} (P.ι.pointwiseLeftKanExtension F') where
  preserves_filtered_colimits J _ _ := by
    exact {
      preservesColimit := fun {K} => {
        preserves := fun {c} hc =>
          ⟨pointwiseLeftKanExtension_mapCocone_isColimit_of_filtered_generator
            (P := P) (D := D) hP F' K hc⟩ } }

omit [ObjectProperty.Small.{w} P] in
/-- Lemma 4.26.2: if `P.FullSubcategory` is small, consists of categorically compact objects, and
generates `C` by filtered colimits, then every functor `F' : P.FullSubcategory ⥤ D` admits a
filtered-colimit-preserving extension `F : C ⥤ D` along the inclusion `P.ι`, unique up to
natural isomorphism.  The Stacks text says "unique extension"; in Lean this must not be encoded as
literal equality of functors, since the colimit construction is canonical only up to natural
isomorphism.

The filtered presentations supplied by `hP` are `w`-small, so the Lean statement records
preservation for filtered colimits of that size.  This is the size-explicit version of the Stacks
phrase "commuting with filtered colimits" for this formalization. -/
theorem exists_unique_filtered_colimit_preserving_extension
    (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
    [HasFilteredColimits C] [HasFilteredColimits D]
    [HasFilteredColimitsOfSize.{w, w} D]
    (F' : P.FullSubcategory ⥤ D) :
    ∃ F : C ⥤ D,
      Nonempty (P.ι ⋙ F ≅ F') ∧
        PreservesFilteredColimitsOfSize.{w, w} F ∧
          ∀ G : C ⥤ D,
            Nonempty (P.ι ⋙ G ≅ F') →
              PreservesFilteredColimitsOfSize.{w, w} G →
                Nonempty (F ≅ G) := by
  letI : P.ι.HasPointwiseLeftKanExtension F' :=
    has_pointwise_leftKanExtension_of_filtered_generator hP F'
  let F : C ⥤ D := P.ι.pointwiseLeftKanExtension F'
  have hIsoUnit :
      IsIso (P.ι.pointwiseLeftKanExtensionUnit F') :=
    pointwiseLeftKanExtensionUnit_isIso (P := P) (D := D) F'
  refine ⟨F, ?_, ?_, ?_⟩
  · -- The fully faithful inclusion identifies the constructed extension with the original functor.
    exact ⟨(asIso (P.ι.pointwiseLeftKanExtensionUnit F')).symm⟩
  · -- The pointwise extension is computed by the same `w`-small filtered presentations used in
    -- `hP`, matching the size-explicit preservation statement above.
    exact
      pointwiseLeftKanExtension_preservesFilteredColimitsOfSize_of_filtered_generator
        (P := P) (D := D) hP F'
  · intro G e hG
    -- A competing extension preserving the same `w`-small filtered colimits is pointwise left Kan
    -- along `P.ι`, hence naturally isomorphic to the chosen pointwise extension.
    rcases e with ⟨i⟩
    have hG_pointwise :
        (Functor.LeftExtension.mk G i.inv).IsPointwiseLeftKanExtension :=
      isPointwiseLeftKanExtension_of_preservesFilteredColimitsOfSize
        (P := P) (D := D) hP i
    letI : G.IsLeftKanExtension i.inv := hG_pointwise.isLeftKanExtension
    exact
      ⟨Functor.leftKanExtensionUnique F
        (P.ι.pointwiseLeftKanExtensionUnit F') G i.inv⟩

end ObjectProperty.IsCardinalFilteredGenerator

end CategoryTheory

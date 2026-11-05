module

public import stacks_project.Chap04.Definition_4_22_2
public import stacks_project.Chap04.Lemma_4_22_3
public import stacks_project.Chap04.Remark_4_22_4
public import Mathlib.CategoryTheory.RepresentedBy

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsFiltered I] (M : I ⥤ C)

namespace CategoryTheory.Limits.Cocone

/-- Lemma 4.22.9, condition (2), as an owner-level criterion on a cocone: the Hom-colimit
comparison for `c` is that every induced co-Yoneda test cocone is colimiting. -/
abbrev HasHomColimitComparison (c : CategoryTheory.Limits.Cocone M) :=
  ∀ W : C, IsColimit ((uliftCoyoneda.{uI}.obj (Opposite.op W)).mapCocone c)

end CategoryTheory.Limits.Cocone

private noncomputable def coconeOfRepresentableBy
    {X : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    Cocone M := by
  let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
    RepresentableBy.equivUliftYonedaIso _ _ e
  let hYoneda :
      (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
    ULiftYoneda.fullyFaithful C
  refine
    { pt := X
      ι :=
        { app := fun i ↦ hYoneda.preimage ((colimit.ι (M ⋙ uliftYoneda.{uI}) i) ≫ eIso.inv)
          naturality := ?_ } }
  intro i j f
  apply hYoneda.map_injective
  simp only [Functor.map_comp, hYoneda.map_preimage]
  simpa using congrArg (fun τ ↦ τ ≫ eIso.inv) (colimit.w (M ⋙ uliftYoneda.{uI}) f)

private noncomputable def coconePointIso
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
  (RepresentableBy.equivUliftYonedaIso _ _ e).app (op W) ≪≫
    colimitObjIsoColimitCompEvaluation (M ⋙ uliftYoneda.{uI}) (op W)

omit [IsFiltered I] in
private theorem coconePointIso_hom_ι
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X)
    (j : I) (f : ULift (W ⟶ M.obj j)) :
    let pointIso : ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
      coconePointIso M e
    pointIso.hom
        (((uliftCoyoneda.{uI}.obj (op W)).mapCocone (coconeOfRepresentableBy M e)).ι.app j f) =
      colimit.ι (M ⋙ uliftCoyoneda.{uI}.obj (op W)) j f := by
  let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
    RepresentableBy.equivUliftYonedaIso _ _ e
  let hYoneda :
      (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
    ULiftYoneda.fullyFaithful C
  simp [coconePointIso, coconeOfRepresentableBy]
  simpa using congrArg (fun g ↦ g f)
    (colimitObjIsoColimitCompEvaluation_ι_app_hom (M ⋙ uliftYoneda.{uI}) j (op W))

private noncomputable def homColimitComparisonIsColimit
    {X W : C} (e : (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) :
    IsColimit ((uliftCoyoneda.{uI}.obj (op W)).mapCocone (coconeOfRepresentableBy M e)) := by
  let pointIso : ULift (W ⟶ X) ≅ colimit (M ⋙ uliftCoyoneda.{uI}.obj (op W)) :=
    coconePointIso M e
  refine (colimit.isColimit (M ⋙ uliftCoyoneda.{uI}.obj (op W))).ofIsoColimit <|
    Cocone.ext pointIso.symm <| ?_
  intro j
  ext f
  simpa [pointIso] using
    (congrArg (fun x ↦ pointIso.inv x)
      (coconePointIso_hom_ι M e j f)).symm

private noncomputable def uliftYonedaMapCoconeIsColimit
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    IsColimit (uliftYoneda.mapCocone c) := by
  refine evaluationJointlyReflectsColimits _ ?_
  intro Y
  simpa using h Y.unop

private noncomputable def uliftYonedaIsoOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    uliftYoneda.obj c.pt ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
  (uliftYonedaMapCoconeIsColimit M c h).coconePointUniqueUpToIso
    (colimit.isColimit (M ⋙ uliftYoneda.{uI}))

private noncomputable def representableByOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    (colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy c.pt :=
  (RepresentableBy.equivUliftYonedaIso _ _).symm <|
    uliftYonedaIsoOfCocone_homColimitComparison M c h

private noncomputable def homColimitComparisonIsColimit_of_essentiallyConstant
    {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c) (W : C) :
    IsColimit ((uliftCoyoneda.{uI}.obj (op W)).mapCocone c) :=
  let hc' := hc.mapCocone (uliftCoyoneda.{uI}.obj (op W))
  hc'.isColimit

omit [IsFiltered I] in
private theorem isEssentiallyConstantFilteredCocone_extend
    {c : Cocone M} (hc : IsEssentiallyConstantFilteredCocone c)
    {X : C} (e : c.pt ≅ X) :
    IsEssentiallyConstantFilteredCocone (c.extend e.hom) := by
  rcases hc with ⟨i, σ, hfac⟩
  refine ⟨i, SplitEpi.comp σ ⟨e.inv, by simp⟩, ?_⟩
  · intro j
    rcases hfac j with ⟨k, ik, jk, hjk⟩
    refine ⟨k, ik, jk, ?_⟩
    simpa [Category.assoc] using hjk

private noncomputable def colimitCoconeOfCocone_homColimitComparison
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    ColimitCocone M :=
  ⟨c, isColimitOfReflects (uliftYoneda.{uI})
    (uliftYonedaMapCoconeIsColimit M c h)⟩

/-- Helper for Lemma 4.22.9: if the Hom-colimit comparison for a cocone is colimiting, then the
identity on the cocone point comes from one stage. -/
private theorem exists_section_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) :
    ∃ i : I, ∃ s : c.pt ⟶ M.obj i, s ≫ c.ι.app i = 𝟙 c.pt := by
  -- Evaluate the comparison at the cocone point and lift the identity through the colimit.
  obtain ⟨i, u, hu⟩ :=
    Types.jointly_surjective_of_isColimit (h c.pt) (ULift.up (𝟙 c.pt))
  refine ⟨i, u.down, ?_⟩
  -- Unwinding the co-Yoneda action turns the lifted element into a section of the chosen leg.
  simpa using congrArg ULift.down hu

/-- Helper for Lemma 4.22.9: a cocone satisfying the Hom-colimit comparison is essentially
constant in the sense of Definition 4.22.1. -/
private theorem essentiallyConstantFilteredCocone_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) :
    IsEssentiallyConstantFilteredCocone c := by
  -- Route correction: prove the textbook `(2) ⇒ (1)` directly from a stage retraction and the
  -- filtered-colimit equality criterion, rather than trying to package representability first.
  rw [isEssentiallyConstantFilteredCocone_iff]
  obtain ⟨i, s, hs⟩ := exists_section_of_homColimitComparison M h
  refine ⟨i, s, hs, ?_⟩
  intro j
  -- Compare the classes of `𝟙_{M_j}` and `c.ι.app j ≫ s` in the Hom-colimit for `W = M.obj j`.
  have hEq :
      ((uliftCoyoneda.{uI}.obj (op (M.obj j))).mapCocone c).ι.app i
          (ULift.up (c.ι.app j ≫ s)) =
        ((uliftCoyoneda.{uI}.obj (op (M.obj j))).mapCocone c).ι.app j
          (ULift.up (𝟙 (M.obj j))) := by
    change ULift.up ((c.ι.app j ≫ s) ≫ c.ι.app i) = ULift.up (𝟙 (M.obj j) ≫ c.ι.app j)
    apply congrArg ULift.up
    have hsj : c.ι.app j ≫ s ≫ c.ι.app i = c.ι.app j := by
      simpa using congrArg (fun f ↦ c.ι.app j ≫ f) hs
    simpa [hsj]
  obtain ⟨k, ik, jk, hk⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (F := M ⋙ uliftCoyoneda.{uI}.obj (op (M.obj j))) (h (M.obj j))).mp hEq
  refine ⟨k, ik, jk, ?_⟩
  -- Equality in the filtered colimit provides a common refinement where the desired factorization
  -- identity holds.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc] using (congrArg ULift.down hk).symm

/- Domain-style sampling for Lemma 4.22.9:
- primary domain: filtered diagrams, their formal ind-objects, and representability/corepresenting
  data for the Hom-colimit presheaf.
- inspected owner-level declarations:
  `IsEssentiallyConstantFilteredDiagram`,
  `Cocone`,
  `ColimitCocone`,
  `StructuredArrow`,
  `Cocone.equivStructuredArrow`,
  `Functor.IsRepresentedBy`,
  `Functor.RepresentableBy`,
  `CategoryTheory.indLim_iso_yoneda_equiv_representableBy`.
- best owner abstraction in the target universe-general setting:
  `IsEssentiallyConstantFilteredDiagram M` for the source-facing predicate, and `ColimitCocone M`
  for actual colimit data; the cocone comparison criterion should be stated over `Cocone M`
  rather than a raw natural-transformation sigma package, and the stage-map criterion should be
  stated over `StructuredArrow X M` rather than a raw pair `(i, X ⟶ M.obj i)`; fixed-object
  representability is most canonically phrased through the owner structure
  `Functor.RepresentableBy`, while the stage-map criterion keeps `Functor.IsRepresentedBy` only
  for the specific universal element induced by that stage map.

Primitive-vs-derived split:
- primitive data: a cocone or colimit cocone on `M`, and representability data for the formal
  ind-object `colimit (M ⋙ uliftYoneda.{uI})`.
- derived API: `HasColimit M` together with the chosen `colimit.cocone M`, which should not be
  stored as primitive public data when `ColimitCocone M` is the real owner; raw sigma encodings
  of cocones and stage maps are likewise derived views once `Cocone M` and `StructuredArrow X M`
  are available; chosen universal elements and their pointwise bijectivity formulas are derived
  from `Functor.RepresentableBy`/`Functor.IsRepresentedBy`.

Source/core/bridge triage:
- `source-facing`: the Hom-colimit and stage-map criteria, which match the textbook conditions.
- `core/canonical`: `IsEssentiallyConstantFilteredDiagram M`, `Cocone M`,
  `ColimitCocone M`, and `StructuredArrow X M`.
- `bridge/view`: representability of `colimit (M ⋙ uliftYoneda.{uI})`; for small index
  categories this also compares to `Ind.lim`, but the present file stays universe-general; the
  left-hand owner is `Functor.RepresentableBy`, and the stage-map criterion uses
  `Functor.IsRepresentedBy` only for its specific universal element witness rather than a raw
  duplicated bijectivity package. The private proof layer may use equivalences between
  `Functor.RepresentableBy` data and owner-level packages on `Cocone M`, `ColimitCocone M`, and
  `StructuredArrow X M`, but the public bridge/view layer should expose only proposition-level
  existence criteria unless a canonical witness is available. -/

/-- Lemma 4.22.9, condition (1), expressed through the chapter owner
`IsEssentiallyConstantFilteredDiagram`: a filtered diagram is essentially constant exactly when
its associated ind-object is representable. The textbook Hom-colimit criteria are equivalent
bridge/view formulations of this canonical statement. -/
theorem essentiallyConstant_indObject_characterizations
    :
    (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentable ↔
      IsEssentiallyConstantFilteredDiagram M := by
  constructor
  · intro hM
    -- Choose a representing object and convert it into the cocone supplied by the Yoneda colimit.
    rcases hM.has_representation with ⟨X, ⟨e⟩⟩
    refine ⟨coconeOfRepresentableBy M e, ?_⟩
    -- The source-proof core is that the Hom-colimit comparison forces eventual constancy.
    exact essentiallyConstantFilteredCocone_of_homColimitComparison M
      (fun W ↦ homColimitComparisonIsColimit M e)
  · rintro ⟨c, hc⟩
    -- An essentially constant cocone makes every co-Yoneda comparison cocone colimiting.
    exact
      (representableByOfCocone_homColimitComparison M c
        (fun W ↦ homColimitComparisonIsColimit_of_essentiallyConstant M hc W)).isRepresentable

/-- Helper for Lemma 4.22.9: rebuilding a cocone from the representability datum extracted from a
Hom-colimit comparison cocone recovers the original cocone. -/
private theorem coconeOfRepresentableBy_representableByOfCocone_homColimitComparison_eq
    (c : Cocone M)
    (h : c.HasHomColimitComparison) :
    coconeOfRepresentableBy M (representableByOfCocone_homColimitComparison M c h) = c := by
  -- The recovered representability datum is built from the cocone-point uniqueness iso, so each
  -- recovered leg is exactly the original leg after applying full faithfulness of `uliftYoneda`.
  cases c with
  | mk pt ι =>
      -- Once the cocone point is fixed, it remains to compare the natural-transformation legs.
      simp [coconeOfRepresentableBy, representableByOfCocone_homColimitComparison]
      ext i
      let hYoneda :
          (uliftYoneda.{uI} : C ⥤ Cᵒᵖ ⥤ Type (max uI vC)).FullyFaithful :=
        ULiftYoneda.fullyFaithful C
      apply hYoneda.map_injective
      simpa [hYoneda] using
        (IsColimit.comp_coconePointUniqueUpToIso_inv
          (uliftYonedaMapCoconeIsColimit M { pt := pt, ι := ι } h)
          (colimit.isColimit (M ⋙ uliftYoneda.{uI})) i)

/- Lemma 4.22.9, condition (2), as a direct equivalence of representing data with cocone data:
the ind-object of `M` is represented by `X` exactly when `M` admits a cocone with vertex `X`
whose canonical Hom-colimit comparison cocones are colimiting on all co-Yoneda test functors. -/
private theorem exists_representableByEquivCocone_homColimitComparison
    (X : C) :
    Nonempty
      ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X ≃
        Σ c : { c : Cocone M // c.pt = X }, c.1.HasHomColimitComparison) := by
  classical
  refine ⟨
    { toFun := fun e ↦
        ⟨⟨coconeOfRepresentableBy M e, rfl⟩, fun W ↦ homColimitComparisonIsColimit M e⟩
      invFun := fun c ↦ by
        rcases c with ⟨⟨c, rfl⟩, hc⟩
        exact representableByOfCocone_homColimitComparison M c hc
      left_inv := by
        intro e
        -- Route correction: reduce the roundtrip on representing data to the universal element at
        -- `𝟙 X`, so the remaining comparison is exactly between the two canonical Yoneda isos.
        apply RepresentableBy.ext
        let c0 := coconeOfRepresentableBy M e
        let P := uliftYonedaMapCoconeIsColimit M c0 (fun W ↦ homColimitComparisonIsColimit M e)
        let uIso := uliftYonedaIsoOfCocone_homColimitComparison M c0
          (fun W ↦ homColimitComparisonIsColimit M e)
        let eIso : uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{uI}) :=
          RepresentableBy.equivUliftYonedaIso _ _ e
        have hdesc :
            eIso.hom = P.desc (colimit.cocone (M ⋙ uliftYoneda.{uI})) := by
          apply (P.uniq _ eIso.hom)
          intro j
          ext W x
          simp [c0, coconeOfRepresentableBy, eIso, Category.assoc]
        have hhom : uIso.hom = eIso.hom := by
          have hu :
              uIso.hom = P.desc (colimit.cocone (M ⋙ uliftYoneda.{uI})) := by
            simpa [uIso, uliftYonedaIsoOfCocone_homColimitComparison] using
              (IsColimit.coconePointUniqueUpToIso_hom_desc
                (P := P) (Q := colimit.isColimit (M ⋙ uliftYoneda.{uI}))
                (r := colimit.cocone (M ⋙ uliftYoneda.{uI})))
          exact hu.trans hdesc.symm
        have happ := congrArg (fun η ↦ η.app (op X) (ULift.up (𝟙 X))) hhom
        simpa [representableByOfCocone_homColimitComparison, uIso, eIso] using happ
      right_inv := by
        rintro ⟨⟨c, rfl⟩, hc⟩
        -- Route correction: reduce the cocone roundtrip to equality of cocone legs; the
        -- `HasHomColimitComparison` witness is subsingleton once the cocone is fixed.
        have hcocone :
            coconeOfRepresentableBy M (representableByOfCocone_homColimitComparison M c hc) = c :=
          coconeOfRepresentableBy_representableByOfCocone_homColimitComparison_eq M c hc
        refine Sigma.ext (Subtype.ext hcocone) ?_
        exact Subsingleton.helim
          (congrArg (fun d : Cocone M ↦ d.HasHomColimitComparison) hcocone)
          (fun W ↦ homColimitComparisonIsColimit (M := M) (W := W)
            (representableByOfCocone_homColimitComparison M c hc))
          hc }⟩

/- Lemma 4.22.9, condition (2), as a direct equivalence of representing data with cocone data:
the ind-object of `M` is represented by `X` exactly when `M` admits a cocone with vertex `X`
whose canonical Hom-colimit comparison cocones are colimiting on all co-Yoneda test functors. -/
theorem representableBy_iff_exists_cocone_homColimitComparison
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ c : Cocone M, c.pt = X ∧ Nonempty (c.HasHomColimitComparison) := by
  classical
  rcases exists_representableByEquivCocone_homColimitComparison M X with ⟨e⟩
  constructor
  · rintro ⟨h⟩
    exact ⟨(e h).1.1, (e h).1.2, ⟨(e h).2⟩⟩
  · rintro ⟨c, hcpt, ⟨hc⟩⟩
    exact ⟨e.symm ⟨⟨c, hcpt⟩, hc⟩⟩

variable [IsFiltered I]

theorem representableBy_iff_exists_essentiallyConstant_colimitCocone
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ c : ColimitCocone M,
        c.cocone.pt = X ∧ IsEssentiallyConstantFilteredCocone c.cocone := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Package the condition-(2) cocone as a colimit cocone and reuse the textbook `(2) ⇒ (1)`
    -- argument already formalized above.
    obtain ⟨c, hcpt, ⟨hc⟩⟩ :=
      (representableBy_iff_exists_cocone_homColimitComparison M X).mp ⟨e⟩
    exact ⟨colimitCoconeOfCocone_homColimitComparison M c hc, hcpt,
      essentiallyConstantFilteredCocone_of_homColimitComparison M hc⟩
  · rintro ⟨c, hcpt, hc⟩
    cases hcpt
    -- Forgetting the chosen colimit proof leaves an essentially constant cocone, which already
    -- gives the required representing datum.
    refine ⟨representableByOfCocone_homColimitComparison M c.cocone ?_⟩
    intro W
    exact homColimitComparisonIsColimit_of_essentiallyConstant M hc W

/-- Helper for Lemma 4.22.9: a section of one cocone leg represents the universal element of the
recovered representability datum by the corresponding stage class. -/
private theorem representableByOfCocone_homColimitComparison_homEquiv_id_eq_stageMap
    {c : Cocone M} (h : c.HasHomColimitComparison) {i : I} (s : c.pt ⟶ M.obj i)
    (hs : s ≫ c.ι.app i = 𝟙 c.pt) :
    (representableByOfCocone_homColimitComparison M c h).homEquiv (𝟙 c.pt) =
      ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
  let uIso := uliftYonedaIsoOfCocone_homColimitComparison M c h
  -- Evaluate the cocone-point uniqueness relation on the chosen section to identify the
  -- universal element with its stage representative.
  have hcomp :
      (uIso.hom.app (op c.pt))
          (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
    have hcomp' :=
      congrArg (fun η ↦ η.app (op c.pt) (ULift.up s))
        (IsColimit.comp_coconePointUniqueUpToIso_hom
          (uliftYonedaMapCoconeIsColimit M c h)
          (colimit.isColimit (M ⋙ uliftYoneda.{uI})) i)
    simpa [uIso, uliftYonedaIsoOfCocone_homColimitComparison] using hcomp'
  have hs_app :
      (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) = ULift.up (𝟙 c.pt) := by
    change ULift.up (s ≫ c.ι.app i) = ULift.up (𝟙 c.pt)
    simpa [hs]
  have hstage_id :
      (uIso.hom.app (op c.pt)) (ULift.up (𝟙 c.pt)) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
    have hleft :
        (uIso.hom.app (op c.pt)) (ULift.up (𝟙 c.pt)) =
          (uIso.hom.app (op c.pt))
            (((uliftYoneda.mapCocone c).ι.app i).app (op c.pt) (ULift.up s)) := by
      exact congrArg (fun x ↦ (uIso.hom.app (op c.pt)) x) hs_app.symm
    exact hleft.trans hcomp
  -- Unfold the representability datum to read off its universal element at `𝟙`.
  simpa [representableByOfCocone_homColimitComparison, uIso] using hstage_id

/-- Helper for Lemma 4.22.9: a stage section obtained from the Hom-colimit comparison supplies
the stage-map witness in condition (4). -/
private theorem stageMap_isRepresentedBy_of_homColimitComparison
    {c : Cocone M} (h : c.HasHomColimitComparison) {i : I} (s : c.pt ⟶ M.obj i)
    (hs : s ≫ c.ι.app i = 𝟙 c.pt) :
    (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
      ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) := by
  let R := representableByOfCocone_homColimitComparison M c h
  -- The previous identification lets us reuse the canonical representability witness.
  have hx :
      R.homEquiv (𝟙 c.pt) =
        ((colimit.ι (M ⋙ uliftYoneda.{uI}) i).app (op c.pt) (ULift.up s)) :=
    representableByOfCocone_homColimitComparison_homEquiv_id_eq_stageMap M h s hs
  exact hx ▸ R.isRepresentedBy

/- Lemma 4.22.9, condition (4), as a direct equivalence of representing data with a stage map:
the ind-object of `M` is represented by `X` exactly when some stage map `X ⟶ M.obj i`
determines a universal element in the Hom-colimit presheaf. -/
theorem representableBy_iff_exists_stageMap_homColimitComparison
    (X : C) :
    Nonempty ((colimit (M ⋙ uliftYoneda.{uI})).RepresentableBy X) ↔
      ∃ p : StructuredArrow X M,
        (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app (op X) (ULift.up p.hom)) := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Route correction: use condition (2) to obtain a cocone, extract a section, and then read
    -- the corresponding stage class as the universal element.
    obtain ⟨c, hcpt, ⟨hc⟩⟩ :=
      (representableBy_iff_exists_cocone_homColimitComparison M X).mp ⟨e⟩
    subst hcpt
    obtain ⟨i, s, hs⟩ := exists_section_of_homColimitComparison M hc
    refine ⟨StructuredArrow.mk s, ?_⟩
    simpa using stageMap_isRepresentedBy_of_homColimitComparison M hc s hs
  · rintro ⟨p, hp⟩
    -- Any represented stage class yields a representing object by the canonical mathlib API.
    exact ⟨hp.representableBy⟩

end

module

public import stacks_project.Chap04.Definition_4_22_2
public import stacks_project.Chap04.Lemma_4_22_3
public import stacks_project.Chap04.Remark_4_22_7
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

section

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable (M : I ⥤ C)

/- Domain-style sampling for Lemma 4.22.10:
- primary domain: cofiltered diagrams, their associated pro-objects, and corepresenting data for
  the Hom-colimit functor `X ↦ colim_i Hom(Mᵢ, X)`.
- inspected owner-level declarations:
  `IsEssentiallyConstantCofilteredDiagram`,
  `LimitCone`,
  `Functor.CorepresentableBy`,
  `proSystemHomColimitFunctor`,
  `Limits.colimitObjIsoColimitCompEvaluation`.
- best owner abstraction for the main proposition: `IsEssentiallyConstantCofilteredDiagram M`.
- best owner abstraction for fixed-object corepresenting data:
  `(proSystemHomColimitFunctor M).CorepresentableBy X`.

Primitive-vs-derived split:
- primitive source data: an essentially constant cone on `M`, or equivalently a corepresentation of
  the Hom-colimit functor of `M` by some fixed `X`.
- derived API: the resulting `LimitCone M`, and the Hom-colimit/stage-map comparison packages.
- the private proof layer may compare `Functor.CorepresentableBy` data for
  `proSystemHomColimitFunctor M` directly with the corresponding cone, limit-cone, and
  `CostructuredArrow M X` packages, but the public source-facing bridge statements should expose
  only proposition-level existence criteria unless a canonical witness is available.

Source/core/bridge triage:
- source-facing: the Hom-colimit and stage-map criteria from the textbook.
- core/canonical: `IsEssentiallyConstantCofilteredDiagram M`, `proSystemHomColimitFunctor M`, and
  `LimitCone M`.
- bridge/view: the equivalences below between corepresenting data and the cone/limit-cone/stage-map
  presentations. -/

namespace CategoryTheory.Limits.Cone

/-- Lemma 4.22.10, condition (2), as an owner-level criterion on a cone: the Hom-colimit
comparison for `c` is that every induced Yoneda test cocone on `c.op` is colimiting. -/
def HasHomColimitComparison (c : Cone M) : Prop :=
  ∀ W : C, Nonempty (IsColimit ((uliftYoneda.{uI}.obj W).mapCocone c.op))

end CategoryTheory.Limits.Cone

private noncomputable def stageClass (j : I) :
    (proSystemHomColimitFunctor M).obj (M.obj j) :=
  (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j)).inv <|
    colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j)) (op j) (ULift.up (𝟙 (M.obj j)))

/-- Helper for Lemma 4.22.10: mapping the identity class at stage `j` along a morphism `f`
produces the corresponding class of `f` in the evaluated Hom-colimit. -/
private theorem stageClass_map
    {W : C} (j : I) (f : M.obj j ⟶ W) :
    (proSystemHomColimitFunctor M).map f (stageClass M j) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) (ULift.up f)) := by
  -- Move the functorial action across the evaluation/colimit comparison isomorphism.
  have hmap :=
    CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
      (F := M.op ⋙ uliftCoyoneda.{uI}) (f := f)
  have hmap' := congrFun hmap
    (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j)) (op j) (ULift.up (𝟙 (M.obj j))))
  have hι := congrFun
    (CategoryTheory.Limits.colimit.ι_map
      ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
        ((evaluation C (Type (max uI vC))).map f))
      (op j))
    (ULift.up (𝟙 (M.obj j)))
  have hι' :
      colimMap ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
          ((evaluation C (Type (max uI vC))).map f))
          (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j))
            (op j) (ULift.up (𝟙 (M.obj j)))) =
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) (ULift.up f) := by
    simpa using hι
  simpa [stageClass] using hmap'.trans
    (congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv hι')

/-- Helper for Lemma 4.22.10: mapping a represented stage class along `g` gives the class of the
composite stage map. -/
private theorem stageMap_class_map
    {X W : C} {i : I} (s : M.obj i ⟶ X) (g : X ⟶ W) :
    (proSystemHomColimitFunctor M).map g
      ((colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) X).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s))) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op i) (ULift.up (s ≫ g))) := by
  -- Move the action of `g` across the evaluation/colimit comparison isomorphism.
  have hmap :=
    CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
      (F := M.op ⋙ uliftCoyoneda.{uI}) (f := g)
  have hmap' := congrFun hmap
    (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s))
  have hι := congrFun
    (CategoryTheory.Limits.colimit.ι_map
      ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
        ((evaluation C (Type (max uI vC))).map g))
      (op i))
    (ULift.up s)
  have hι' :
      colimMap ((M.op ⋙ uliftCoyoneda.{uI}).whiskerLeft
          ((evaluation C (Type (max uI vC))).map g))
          (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s)) =
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op i) (ULift.up (s ≫ g)) := by
    simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hι
  simpa using hmap'.trans
    (congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv hι')

private theorem exists_coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    ∃ τ : (Functor.const I).obj X ⟶ M, ∀ j : I, e.homEquiv (τ.app j) = stageClass M j := by
  refine ⟨{ app := fun j ↦ e.homEquiv.symm (stageClass M j), naturality := ?_ }, ?_⟩
  · intro j j' f
    apply e.homEquiv.injective
    -- Both sides are the stage class of `j'`, written once through functoriality.
    have hleft :
        e.homEquiv (((Functor.const I).obj X).map f ≫ e.homEquiv.symm (stageClass M j')) =
          stageClass M j' := by
      simp
    have hcomp :
        e.homEquiv (e.homEquiv.symm (stageClass M j) ≫ M.map f) =
          (proSystemHomColimitFunctor M).map (M.map f) (stageClass M j) := by
      simpa using e.homEquiv_comp (M.map f) (e.homEquiv.symm (stageClass M j))
    have hmap :
        (proSystemHomColimitFunctor M).map (M.map f) (stageClass M j) =
          (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j')).inv
            (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j)
              (ULift.up (M.map f))) := by
      simpa using stageClass_map (M := M) j (M.map f)
    have hw := congrFun (colimit.w (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) f.op)
      (ULift.up (𝟙 (M.obj j')))
    have hw' :
        colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j) (ULift.up (M.map f)) =
          colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j')) (op j')
            (ULift.up (𝟙 (M.obj j'))) := by
      simpa using hw
    exact hleft.trans <| (hcomp.trans <| hmap.trans <|
      congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) (M.obj j')).inv hw').symm
  · intro j
    simp

private noncomputable def coneOfCorepresentableBy
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    (Functor.const I).obj X ⟶ M :=
  Classical.choose (exists_coneOfCorepresentableBy M e)

/-- Helper for Lemma 4.22.10: the chosen cone attached to a corepresentation has the prescribed
stage classes. -/
private theorem coneOfCorepresentableBy_homEquiv
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) (j : I) :
    e.homEquiv ((coneOfCorepresentableBy M e).app j) = stageClass M j := by
  exact Classical.choose_spec (exists_coneOfCorepresentableBy M e) j

private noncomputable def coconePointIso
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    ULift (X ⟶ W) ≅ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) :=
  equivEquivIso <|
    Equiv.ulift.trans <|
      e.homEquiv.trans (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).toEquiv

private theorem coconePointIso_hom_ι
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X)
    (j : I) (f : ULift (M.obj j ⟶ W)) :
    (coconePointIso M e).hom
        (((uliftYoneda.{uI}.obj W).mapCocone
          (Cone.mk X (coneOfCorepresentableBy M e)).op).ι.app (op j) f) =
      colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op j) f := by
  -- Rewrite the chosen cone leg using its defining stage class.
  have hcomp :
      e.homEquiv ((coneOfCorepresentableBy M e).app j ≫ f.down) =
        (proSystemHomColimitFunctor M).map f.down (stageClass M j) := by
    rw [e.homEquiv_comp, coneOfCorepresentableBy_homEquiv]
  -- The evaluated stage class is exactly the image of the chosen element in the colimit.
  have hstage := stageClass_map (M := M) j f.down
  simpa [coconePointIso] using
    congrArg (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
      (hcomp.trans hstage)

/-- Helper for Lemma 4.22.10: if a cone satisfies the Hom-colimit comparison, then the induced
co-Yoneda cocone is colimiting. -/
private noncomputable def uliftCoyonedaMapCoconeIsColimit
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    IsColimit (uliftCoyoneda.mapCocone c.op) := by
  refine evaluationJointlyReflectsColimits _ ?_
  intro Y
  simpa using Classical.choice (h Y)

/-- Helper for Lemma 4.22.10: a cone satisfying the Hom-colimit comparison determines the
canonical co-Yoneda realization of the pro-object. -/
private noncomputable def uliftCoyonedaIsoOfCone_homColimitComparison
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    uliftCoyoneda.obj (op c.pt) ≅ colimit (M.op ⋙ uliftCoyoneda.{uI}) :=
  (uliftCoyonedaMapCoconeIsColimit M c h).coconePointUniqueUpToIso
    (colimit.isColimit (M.op ⋙ uliftCoyoneda.{uI}))

/-- Helper for Lemma 4.22.10: a cone whose Hom-colimit comparisons are colimiting yields a
corepresentation of the pro-Hom functor by its cone point. -/
private noncomputable def corepresentableByOfCone_homColimitComparison
    (c : Cone M)
    (h : c.HasHomColimitComparison) :
    (proSystemHomColimitFunctor M).CorepresentableBy c.pt :=
  (Functor.CorepresentableBy.equivUliftCoyonedaIso _ _).symm <|
    uliftCoyonedaIsoOfCone_homColimitComparison M c h

private noncomputable def homColimitComparisonIsColimit
    {X W : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X) :
    IsColimit ((uliftYoneda.{uI}.obj W).mapCocone
      (Cone.mk X (coneOfCorepresentableBy M e)).op) :=
  (colimit.isColimit (M.op ⋙ uliftYoneda.{uI}.obj W)).ofIsoColimit <|
    Cocone.ext (coconePointIso M e).symm <| by
      intro j
      ext f
      simpa using
        (congrArg (fun x ↦ (coconePointIso M e).inv x) (coconePointIso_hom_ι M e j.unop f)).symm

private theorem exists_corepresentableByOfCone_homColimitComparison
    (c : Cone M) (hc : c.HasHomColimitComparison) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy c.pt) := by
  exact ⟨corepresentableByOfCone_homColimitComparison M c hc⟩

/-- Helper for Lemma 4.22.10: an essentially constant cofiltered cone makes every Yoneda test
cocone colimiting. -/
private noncomputable def homColimitComparisonIsColimit_of_essentiallyConstant
    {c : Cone M} (hc : IsEssentiallyConstantCofilteredCone c) (W : C) :
    IsColimit ((uliftYoneda.{uI}.obj W).mapCocone c.op) :=
  let hc' := (show IsEssentiallyConstantFilteredCocone c.op from hc).mapCocone
    (uliftYoneda.{uI}.obj W)
  hc'.isColimit

-- Proof sketch: this is the dual of Lemma 4.22.9. Pass from the cofiltered diagram to the
-- filtered colimit of the presheaves `Hom(Mᵢ, -)` and identify corepresentability with the
-- chapter owner `IsEssentiallyConstantCofilteredDiagram`.
section

variable [CategoryTheory.IsCofiltered I]

/-- Helper for Lemma 4.22.10: evaluating the Hom-colimit comparison at the cone point produces a
stage retraction to the cone point. -/
private theorem exists_retraction_of_homColimitComparison
    {c : Cone M} (h : c.HasHomColimitComparison) :
    ∃ i : I, ∃ s : M.obj i ⟶ c.pt, c.π.app i ≫ s = 𝟙 c.pt := by
  -- Lift the identity through the colimit presentation at the cone point.
  obtain ⟨i, u, hu⟩ :=
    Types.jointly_surjective_of_isColimit (Classical.choice (h c.pt)) (ULift.up (𝟙 c.pt))
  refine ⟨i.unop, u.down, ?_⟩
  simpa using congrArg ULift.down hu

/-- Helper for Lemma 4.22.10: the Hom-colimit comparison forces the eventual factorization data
of an essentially constant cofiltered cone. -/
private theorem essentiallyConstantCofilteredCone_of_homColimitComparison
    {c : Cone M} (h : c.HasHomColimitComparison) :
    IsEssentiallyConstantCofilteredCone c := by
  -- Route correction: extract a split cone leg first and then use equality in the filtered
  -- colimit over `Iᵒᵖ` to produce the eventual factorization witnesses.
  rw [isEssentiallyConstantCofilteredCone_iff]
  obtain ⟨i, s, hs⟩ := exists_retraction_of_homColimitComparison M h
  refine ⟨i, { retraction := s, id := hs }, ?_⟩
  intro j
  -- Compare the classes of `s ≫ c.π.app j` and `𝟙 (M.obj j)` in the Hom-colimit for `M.obj j`.
  have hEq :
      ((uliftYoneda.{uI}.obj (M.obj j)).mapCocone c.op).ι.app (op i)
          (ULift.up (s ≫ c.π.app j)) =
        ((uliftYoneda.{uI}.obj (M.obj j)).mapCocone c.op).ι.app (op j)
          (ULift.up (𝟙 (M.obj j))) := by
    have hsj : c.π.app i ≫ s ≫ c.π.app j = c.π.app j := by
      simpa using congrArg (fun f ↦ f ≫ c.π.app j) hs
    simpa [FunctorToTypes.map_comp_apply, Category.assoc, hsj]
  obtain ⟨k, ik, jk, hk⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (M.op ⋙ uliftYoneda.{uI}.obj (M.obj j))
      (Classical.choice (h (M.obj j)))).mp hEq
  refine ⟨k.unop, ik.unop, jk.unop, ?_⟩
  -- Equality in the filtered colimit becomes the desired factorization identity after unop.
  simpa [FunctorToTypes.map_comp_apply, Category.assoc] using (congrArg ULift.down hk).symm

/-- Lemma 4.22.10, condition (1), expressed through the chapter owner
`IsEssentiallyConstantCofilteredDiagram`: a cofiltered diagram is essentially constant exactly
when its associated pro-object is corepresentable. The textbook Hom-colimit criteria are
companion bridge/view formulations of this canonical statement. -/
theorem essentiallyConstant_proObject_characterizations
    :
    (proSystemHomColimitFunctor M).IsCorepresentable ↔
      IsEssentiallyConstantCofilteredDiagram M := by
  constructor
  · intro hM
    -- Choose a corepresenting object and recover the cone supplied by the corepresentability
    -- bridge.
    rcases hM.has_corepresentation with ⟨X, ⟨e⟩⟩
    refine ⟨Cone.mk X (coneOfCorepresentableBy M e), ?_⟩
    exact essentiallyConstantCofilteredCone_of_homColimitComparison M
      (fun W ↦ ⟨homColimitComparisonIsColimit M e⟩)
  · rintro ⟨c, hc⟩
    -- An essentially constant cone makes every Yoneda comparison cocone colimiting.
    exact
      (corepresentableByOfCone_homColimitComparison M c
        (fun W ↦ ⟨homColimitComparisonIsColimit_of_essentiallyConstant M hc W⟩)).isCorepresentable

end

-- Proof sketch: dualize the corresponding representability criterion in Lemma 4.22.9. A
-- corepresentation of the formal pro-object by `X` is equivalent to a cone on `M` with vertex
-- `X` whose induced Yoneda test cocones on `c.op` are colimiting for every test object.
private theorem exists_corepresentableByEquivCone_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : Cone M, c.pt = X ∧ c.HasHomColimitComparison := by
  constructor
  · rintro ⟨e⟩
    -- The chosen corepresenting datum supplies the canonical cone with Hom-colimit comparison.
    exact ⟨Cone.mk X (coneOfCorepresentableBy M e), rfl,
      fun W ↦ ⟨homColimitComparisonIsColimit M e⟩⟩
  · rintro ⟨c, hcpt, hc⟩
    -- Conversely, the cone point corepresents the pro-object by the comparison hypothesis.
    cases hcpt
    exact ⟨corepresentableByOfCone_homColimitComparison M c hc⟩

/-- Lemma 4.22.10, condition (2): the pro-object of `M` is corepresented by `X` exactly when `M`
admits a cone with vertex `X` whose canonical Hom-colimit comparison cocones are colimiting on all
test objects `W`. -/
theorem corepresentableBy_iff_exists_cone_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : Cone M, c.pt = X ∧ c.HasHomColimitComparison := by
  simpa using exists_corepresentableByEquivCone_homColimitComparison M X

section

variable [CategoryTheory.IsCofiltered I]

/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
private theorem exists_corepresentableByEquivEssentiallyConstant_limitCone
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  constructor
  · rintro ⟨e⟩
    let c : Cone M := Cone.mk X (coneOfCorepresentableBy M e)
    have hc : IsEssentiallyConstantCofilteredCone c :=
      essentiallyConstantCofilteredCone_of_homColimitComparison M
        (fun W ↦ ⟨homColimitComparisonIsColimit M e⟩)
    -- Package the specific essentially constant cone on `X` as a limit cone.
    exact ⟨cofilteredConeToLimitCone hc, rfl, cofilteredConeToLimitCone_isEssentiallyConstant hc⟩
  · rintro ⟨c, hcpt, hc⟩
    cases hcpt
    -- Forgetting the chosen limit proof leaves an essentially constant cone, which already
    -- corepresents the pro-object.
    exact ⟨corepresentableByOfCone_homColimitComparison M c.cone
      (fun W ↦ ⟨homColimitComparisonIsColimit_of_essentiallyConstant M hc W⟩)⟩

/-- Lemma 4.22.10, condition (3), expressed through the limit-cone owner `LimitCone M`: the
pro-object of `M` is corepresented by `X` exactly when `M` admits an essentially constant
limit cone with vertex `X`. -/
theorem corepresentableBy_iff_exists_essentiallyConstant_limitCone
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ c : LimitCone M, c.cone.pt = X ∧ IsEssentiallyConstantCofilteredCone c.cone := by
  simpa using exists_corepresentableByEquivEssentiallyConstant_limitCone M X

end

/-- Helper for Lemma 4.22.10: a stage retraction of the canonical cone recovers the universal
element of the corepresenting equivalence. -/
private theorem corepresentableBy_homEquiv_id_eq_stageMap
    {X : C} (e : (proSystemHomColimitFunctor M).CorepresentableBy X)
    {i : I} (s : M.obj i ⟶ X)
    (hs : (coneOfCorepresentableBy M e).app i ≫ s = 𝟙 X) :
    e.homEquiv (𝟙 X) =
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) X).inv
        (colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj X) (op i) (ULift.up s)) := by
  -- Rewrite the identity via the chosen cone leg and transport the result through the
  -- corepresenting equivalence.
  have hleft :
      e.homEquiv (𝟙 X) = e.homEquiv ((coneOfCorepresentableBy M e).app i ≫ s) := by
    exact congrArg e.homEquiv hs.symm
  have hcomp :
      e.homEquiv ((coneOfCorepresentableBy M e).app i ≫ s) =
        (proSystemHomColimitFunctor M).map s (stageClass M i) := by
    rw [e.homEquiv_comp, coneOfCorepresentableBy_homEquiv]
  have hstage := stageClass_map (M := M) i s
  exact hleft.trans (hcomp.trans hstage)

-- Proof sketch: dualize the stage-map criterion from Lemma 4.22.9. A distinguished stage map
-- `Mᵢ ⟶ X` determines the forward maps of the corepresenting equivalences
-- `Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for every test object `W`, and conversely those equivalences
-- identify `X` as the corepresenting object.
/-- Lemma 4.22.10, condition (4): the pro-object of `M` is corepresented by `X` exactly when some
stage map `Mᵢ ⟶ X` determines the usual comparison equivalences
`Hom(X, W) ≃ colimⱼ Hom(Mⱼ, W)` for all test objects `W`. -/
private theorem exists_corepresentableByEquivStageMap_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ p : CostructuredArrow M X,
        ∀ W : C,
          Nonempty
            { e : (X ⟶ W) ≃ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) //
                ∀ g : X ⟶ W,
                  e g = colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
                    (ULift.up (p.hom ≫ g)) } := by
  classical
  constructor
  · rintro ⟨e⟩
    -- Represent the universal element at `𝟙 X` by a single stage map.
    obtain ⟨i, u, hu⟩ :=
      Types.jointly_surjective_of_isColimit
        (homColimitComparisonIsColimit (M := M) (e := e) (W := X))
        (ULift.up (𝟙 X))
    have hs : (coneOfCorepresentableBy M e).app i.unop ≫ u.down = 𝟙 X := by
      simpa using congrArg ULift.down hu
    let p : CostructuredArrow M X := CostructuredArrow.mk u.down
    refine ⟨p, ?_⟩
    intro W
    refine ⟨⟨e.homEquiv.trans
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).toEquiv, ?_⟩⟩
    intro g
    -- Every value of the equivalence is obtained by postcomposing the chosen universal element.
    change
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
        (e.homEquiv g) =
      colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
        (ULift.up (p.hom ≫ g))
    rw [e.homEquiv_eq, corepresentableBy_homEquiv_id_eq_stageMap (M := M) e u.down hs]
    simpa using congrArg
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).hom
      (stageMap_class_map (M := M) (s := u.down) g)
  · rintro ⟨p, hp⟩
    refine ⟨
      { homEquiv := fun {W} ↦
          ((Classical.choice (hp W)).1).trans
            (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).symm.toEquiv
        homEquiv_comp := ?_ }⟩
    intro W W' g f
    let eW := Classical.choice (hp W)
    let eW' := Classical.choice (hp W')
    -- Both sides are the same stage class after evaluating the colimit map along `g`.
    change
      (colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W').inv
        (eW'.1 (f ≫ g)) =
      (proSystemHomColimitFunctor M).map g
        ((colimitObjIsoColimitCompEvaluation (M.op ⋙ uliftCoyoneda.{uI}) W).inv (eW.1 f))
    rw [eW'.2, eW.2]
    simpa [Category.assoc] using (stageMap_class_map (M := M) (s := p.hom ≫ f) g).symm

theorem corepresentableBy_iff_exists_stageMap_homColimitComparison
    (X : C) :
    Nonempty ((proSystemHomColimitFunctor M).CorepresentableBy X) ↔
      ∃ p : CostructuredArrow M X,
        ∀ W : C,
          Nonempty
            { e : (X ⟶ W) ≃ colimit (M.op ⋙ uliftYoneda.{uI}.obj W) //
                ∀ g : X ⟶ W,
                  e g = colimit.ι (M.op ⋙ uliftYoneda.{uI}.obj W) (op p.left)
                    (ULift.up (p.hom ≫ g)) } := by
  simpa using exists_corepresentableByEquivStageMap_homColimitComparison M X

end

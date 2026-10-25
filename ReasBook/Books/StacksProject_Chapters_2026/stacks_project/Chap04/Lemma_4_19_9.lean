module

public import stacks_project.Chap04.Lemma_4_19_8
public import Mathlib.Logic.Small.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.FinCategory.Basic
import all Mathlib.Logic.Small.Defs
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ConnectedComponents

universe u v vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I] [Small.{v} I]

private instance connected_component_small (j : ConnectedComponents I) : Small.{v} j.Component :=
  small_of_injective (f := fun X : j.Component => X.obj) (fun X Y h ↦ by
    ext
    exact h)

section SourceFacing

variable [HasSpanCocones I]

/- Domain-style sampling for Lemma 4.19.9:
- source-facing hypotheses: `HasSpanCocones I` and the explicit postcomposition-equalizer
  condition on parallel pairs
- core owner declarations: `connected_components_are_filtered`, `CategoryTheory.decomposedEquiv`,
  `preservesLimitsOfShape_colim_grothendieck`, and mathlib's
  `filtered_colim_preservesFiniteLimits_of_types`
- target layer here: `bridge/view`, namely a `PreservesLimitsOfShape` theorem for connected finite
  shapes obtained from the filtered connected-component owner.
-/

/- Companion recalls: the componentwise filtered owner and the Grothendieck gluing theorem are the
canonical upstream ingredients for this bridge file. -/
recall filtered_colim_preservesFiniteLimits_of_types
recall preservesLimitsOfShape_colim_grothendieck

/-- Helper for Lemma 4.19.9: the colimit of a discrete `Type`-valued diagram is the sigma type of
its components. We package this explicit coproduct functor so the connectedness argument can be
stated directly on sections. -/
private def discrete_sigma_functor (β : Type v) : (Discrete β ⥤ Type v) ⥤ Type v where
  obj X := Σ b : β, X.obj ⟨b⟩
  map τ x := ⟨x.1, τ.app ⟨x.1⟩ x.2⟩

/-- Helper for Lemma 4.19.9: the explicit sigma type carries the canonical cocone on a discrete
diagram of types. -/
private def discrete_sigma_cocone (β : Type v) (X : Discrete β ⥤ Type v) : Cocone X where
  pt := Σ b : β, X.obj ⟨b⟩
  ι := Discrete.natTrans (fun j x ↦ ⟨j.as, x⟩)

/-- Helper for Lemma 4.19.9: the universal map out of the sigma cocone restricts to the prescribed
map on each coproduct injection. -/
private theorem discrete_sigma_cocone_isColimit_fac (β : Type v) (X : Discrete β ⥤ Type v)
    (s : Cocone X) (j : Discrete β) :
    (discrete_sigma_cocone β X).ι.app j ≫ (fun z ↦ s.ι.app ⟨z.1⟩ z.2) = s.ι.app j := by
  -- The desc map simply forgets the sigma tag and applies the corresponding cocone leg.
  ext x
  rfl

/-- Helper for Lemma 4.19.9: a map out of the sigma cocone is determined by its values on the
canonical coproduct injections. -/
private theorem discrete_sigma_cocone_isColimit_uniq (β : Type v) (X : Discrete β ⥤ Type v)
    (s : Cocone X) (m : (discrete_sigma_cocone β X).pt ⟶ s.pt)
    (hm : ∀ j, (discrete_sigma_cocone β X).ι.app j ≫ m = s.ι.app j) :
    m = fun z ↦ s.ι.app ⟨z.1⟩ z.2 := by
  -- Every sigma element lies in one chosen summand, so uniqueness reduces to that summand's leg.
  funext z
  cases z with
  | mk b x =>
      exact congrFun (hm ⟨b⟩) x

/-- Helper for Lemma 4.19.9: the explicit sigma cocone is colimiting because every element already
remembers the unique summand from which it came. -/
private def discrete_sigma_cocone_isColimit (β : Type v) (X : Discrete β ⥤ Type v) :
    IsColimit (discrete_sigma_cocone β X) where
  desc s z := s.ι.app ⟨z.1⟩ z.2
  fac := discrete_sigma_cocone_isColimit_fac β X
  uniq := discrete_sigma_cocone_isColimit_uniq β X

/-- Helper for Lemma 4.19.9: the abstract discrete colimit is canonically identified with the
explicit sigma-type coproduct. -/
private noncomputable def discrete_colimit_sigma_component (β : Type v)
    (X : Discrete β ⥤ Type v) : colimit X ≅ Σ b : β, X.obj ⟨b⟩ :=
  (colimit.isColimit X).coconePointUniqueUpToIso (discrete_sigma_cocone_isColimit β X)

/-- Helper for Lemma 4.19.9: the discrete colimit comparison sends each canonical coproduct
injection to the matching sigma inclusion. -/
private theorem discrete_colimit_sigma_component_hom_ι (β : Type v)
    (X : Discrete β ⥤ Type v) (b : β) :
    colimit.ι X ⟨b⟩ ≫ (discrete_colimit_sigma_component β X).hom = fun x ↦ ⟨b, x⟩ := by
  -- The universal comparison is characterized by its effect on the coproduct injections.
  simpa [discrete_colimit_sigma_component, discrete_sigma_cocone] using
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X)
      (discrete_sigma_cocone_isColimit β X) ⟨b⟩

/-- Helper for Lemma 4.19.9: the discrete colimit-to-sigma comparison is natural in the discrete
diagram. -/
private theorem discrete_colimit_sigma_component_naturality (β : Type v)
    {X Y : Discrete β ⥤ Type v} (τ : X ⟶ Y) :
    colim.map τ ≫ (discrete_colimit_sigma_component β Y).hom =
      (discrete_colimit_sigma_component β X).hom ≫ (discrete_sigma_functor β).map τ := by
  apply colimit.hom_ext
  intro j
  cases j with
  | mk b =>
      -- It is enough to check the square on the canonical coproduct injections.
      funext x
      have hmap :
          ((colimit.ι X ⟨b⟩ ≫ colim.map τ ≫ (discrete_colimit_sigma_component β Y).hom) x) =
            (discrete_colimit_sigma_component β Y).hom (colimit.ι Y ⟨b⟩ (τ.app ⟨b⟩ x)) := by
        simpa [colim] using congrArg ((discrete_colimit_sigma_component β Y).hom)
          (Types.Colimit.ι_map_apply τ ⟨b⟩ x)
      have hX :
          (discrete_colimit_sigma_component β X).hom (colimit.ι X ⟨b⟩ x) = ⟨b, x⟩ :=
        congrFun (discrete_colimit_sigma_component_hom_ι β X b) x
      have hY :
          (discrete_colimit_sigma_component β Y).hom (colimit.ι Y ⟨b⟩ (τ.app ⟨b⟩ x)) =
            ⟨b, τ.app ⟨b⟩ x⟩ :=
        congrFun (discrete_colimit_sigma_component_hom_ι β Y b) (τ.app ⟨b⟩ x)
      -- Both routes send the generator `x` to the same tagged element of the sigma coproduct.
      calc
        ((colimit.ι X ⟨b⟩ ≫ colim.map τ ≫ (discrete_colimit_sigma_component β Y).hom) x)
            = (discrete_colimit_sigma_component β Y).hom (colimit.ι Y ⟨b⟩ (τ.app ⟨b⟩ x)) := hmap
        _ = ⟨b, τ.app ⟨b⟩ x⟩ := by
          simpa using hY
        _ = ((colimit.ι X ⟨b⟩ ≫ (discrete_colimit_sigma_component β X).hom ≫
              (discrete_sigma_functor β).map τ) x) := by
          simpa [discrete_sigma_functor] using
            (congrArg ((discrete_sigma_functor β).map τ) hX).symm

/-- Helper for Lemma 4.19.9: for a discrete index type already living in universe `v`, the
categorical colimit in `Type v` is naturally isomorphic to the explicit sigma-type coproduct. -/
private noncomputable def discrete_colimit_iso_sigma_functor (β : Type v) :
    (colim : (Discrete β ⥤ Type v) ⥤ Type v) ≅ discrete_sigma_functor β :=
  NatIso.ofComponents (discrete_colimit_sigma_component β)
    (discrete_colimit_sigma_component_naturality β)

/-- Helper for Lemma 4.19.9: a section of a sigma-valued diagram determines a functor to the
discrete index category by remembering which summand is chosen at each object. -/
private def sigma_section_index_functor
    {J : Type u} [SmallCategory J] {β : Type v} (K : J ⥤ Discrete β ⥤ Type v)
    (s : (K ⋙ discrete_sigma_functor β).sections) :
    J ⥤ Discrete β where
  obj j := ⟨(s.val j).1⟩
  map {j j'} f := eqToHom <| by
    apply Discrete.ext
    exact congrArg Sigma.fst (s.property f)
  map_id j := by
    simp
  map_comp f g := by
    simp

/-- Helper for Lemma 4.19.9: fix a reference object of the connected index category so that the
common sigma summand of a section can be recorded there. -/
private noncomputable def sigma_section_reference_object
    {J : Type u} [SmallCategory J] [IsConnected J] : J :=
  Classical.choice inferInstance

/-- Helper for Lemma 4.19.9: the reference summand is the first coordinate seen at the chosen
reference object. -/
private noncomputable def sigma_section_reference_index
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) : β :=
  (s.val sigma_section_reference_object).1

/-- Helper for Lemma 4.19.9: every object of a sigma-valued section lies in the reference
summand. -/
private lemma sigma_section_reference_index_eq
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) (j : J) :
    (s.val j).1 = sigma_section_reference_index K s := by
  let F := sigma_section_index_functor K s
  -- Connectedness makes the first-coordinate functor constant on objects.
  exact congrArg Discrete.as
    (CategoryTheory.any_functor_const_on_obj F j sigma_section_reference_object)

/-- Helper for Lemma 4.19.9: on a connected indexing category, a section of a sigma-valued diagram
must stay in a single coproduct summand. -/
private lemma sigma_section_has_constant_index
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) :
    ∃ b : β, ∀ j, (s.val j).1 = b := by
  -- The reference summand is the unique summand used everywhere in the section.
  refine ⟨sigma_section_reference_index K s, ?_⟩
  exact sigma_section_reference_index_eq K s

/-- Helper for Lemma 4.19.9: transport the second coordinate of a sigma-valued section into the
reference summand chosen by connectedness. -/
private noncomputable def sigma_section_reference_component
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) :
    ∀ j, (K.obj j).obj ⟨sigma_section_reference_index K s⟩ :=
  fun j =>
    Eq.ndrec (motive := fun b => (K.obj j).obj ⟨b⟩) (s.val j).2
      (sigma_section_reference_index_eq K s j)

/-- Helper for Lemma 4.19.9: the transported second coordinates still satisfy the section
equations in the fixed reference summand. -/
private theorem sigma_section_transported_component_is_natural
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) :
    ∀ ⦃j j' : J⦄ (f : j ⟶ j'),
      (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨sigma_section_reference_index K s⟩).map f
          (sigma_section_reference_component K s j) =
        sigma_section_reference_component K s j' := by
  intro j j' f
  -- Name the sigma values at `j` and `j'` so the transport equations become ordinary rewrites.
  cases hsj : s.val j with
  | mk bj xj =>
      cases hsj' : s.val j' with
      | mk bj' xj' =>
          have hj : bj = sigma_section_reference_index K s := by
            simpa [hsj] using sigma_section_reference_index_eq K s j
          have hj' : bj' = sigma_section_reference_index K s := by
            simpa [hsj'] using sigma_section_reference_index_eq K s j'
          subst bj
          subst bj'
          have hs : (K.map f).app ⟨sigma_section_reference_index K s⟩ xj = xj' := by
            apply sigma_mk_injective
            simpa [hsj, hsj', discrete_sigma_functor] using s.property f
          have hcomp_j : sigma_section_reference_component K s j = xj := by
            apply eq_of_heq
            dsimp [sigma_section_reference_component]
            exact rec_heq_of_heq (C := fun b => (K.obj j).obj ⟨b⟩)
              (sigma_section_reference_index_eq K s j) ((Sigma.mk.inj_iff.mp hsj).2)
          have hcomp_j' : sigma_section_reference_component K s j' = xj' := by
            apply eq_of_heq
            dsimp [sigma_section_reference_component]
            exact rec_heq_of_heq (C := fun b => (K.obj j').obj ⟨b⟩)
              (sigma_section_reference_index_eq K s j') ((Sigma.mk.inj_iff.mp hsj').2)
          rw [hcomp_j, hcomp_j']
          simpa using hs

/-- Helper for Lemma 4.19.9: the transported second coordinates form a genuine section of the
chosen component diagram. -/
private noncomputable def sigma_section_reference_section
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (s : (K ⋙ discrete_sigma_functor β).sections) :
    (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨sigma_section_reference_index K s⟩).sections :=
  ⟨sigma_section_reference_component K s,
    fun {_ _} f ↦ sigma_section_transported_component_is_natural K s f⟩

/-- Helper for Lemma 4.19.9: package a sigma-valued section as the unique summand together with
its transported componentwise section. -/
private noncomputable def connected_sigma_sections_forward
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    (K ⋙ discrete_sigma_functor β).sections →
      Σ b : β, (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨b⟩).sections :=
  fun s ↦ ⟨sigma_section_reference_index K s, sigma_section_reference_section K s⟩

/-- Helper for Lemma 4.19.9: reinstalling a fixed first coordinate turns a component section back
into a sigma-valued section. -/
private theorem constant_sigma_section_is_natural
    {J : Type u} [SmallCategory J] {β : Type v} (K : J ⥤ Discrete β ⥤ Type v)
    (x : Σ b : β, (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨b⟩).sections) :
    ∀ ⦃j j' : J⦄ (f : j ⟶ j'),
      (K ⋙ discrete_sigma_functor β).map f ⟨x.1, x.2.val j⟩ = ⟨x.1, x.2.val j'⟩ := by
  cases x with
  | mk b t =>
      intro j j' f
      -- The first coordinate is fixed, and the second coordinate follows the given section equation.
      exact Sigma.ext rfl (heq_of_eq (t.property f))

/-- Helper for Lemma 4.19.9: a section in a fixed component gives a sigma-valued section by
attaching the constant summand label. -/
private def connected_sigma_sections_backward
    {J : Type u} [SmallCategory J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    (Σ b : β, (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨b⟩).sections) →
      (K ⋙ discrete_sigma_functor β).sections :=
  fun x ↦
    ⟨fun j ↦ ⟨x.1, x.2.val j⟩,
      fun {_ _} f ↦ constant_sigma_section_is_natural K x f⟩

/-- Helper for Lemma 4.19.9: transporting to the reference component and then reinstating the
constant sigma index recovers the original sigma-valued section. -/
private theorem connected_sigma_sections_left_inv
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    Function.LeftInverse (connected_sigma_sections_backward K) (connected_sigma_sections_forward K) := by
  intro s
  -- Pointwise, connectedness identifies the original summand with the reference summand.
  apply Subtype.ext
  funext j
  cases hsj : s.val j with
  | mk bj xj =>
      have hj : bj = sigma_section_reference_index K s := by
        simpa [hsj] using sigma_section_reference_index_eq K s j
      subst bj
      have hcomp_j : sigma_section_reference_component K s j = xj := by
        apply eq_of_heq
        dsimp [sigma_section_reference_component]
        exact rec_heq_of_heq (C := fun b => (K.obj j).obj ⟨b⟩)
          (sigma_section_reference_index_eq K s j) ((Sigma.mk.inj_iff.mp hsj).2)
      simpa [connected_sigma_sections_backward, connected_sigma_sections_forward,
        sigma_section_reference_section, hcomp_j]

/-- Helper for Lemma 4.19.9: a fixed-component section is unchanged by the forward-backward
conversion. -/
private theorem connected_sigma_sections_right_inv
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    Function.RightInverse (connected_sigma_sections_backward K)
      (connected_sigma_sections_forward K) := by
  intro x
  -- The constructed sigma-valued section is visibly constant in its first coordinate.
  cases x with
  | mk b t =>
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        funext j
        have hj := sigma_section_reference_index_eq K
          (connected_sigma_sections_backward K ⟨b, t⟩) j
        dsimp [connected_sigma_sections_forward, sigma_section_reference_section,
          connected_sigma_sections_backward, sigma_section_reference_component,
          sigma_section_reference_index] at hj ⊢

private noncomputable def connected_sigma_sections_equiv
    {J : Type u} [SmallCategory J] [IsConnected J] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    (K ⋙ discrete_sigma_functor β).sections ≃
      Σ b : β, (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨b⟩).sections :=
  { toFun := connected_sigma_sections_forward K
    invFun := connected_sigma_sections_backward K
    left_inv := connected_sigma_sections_left_inv K
    right_inv := connected_sigma_sections_right_inv K }

/-- Helper for Lemma 4.19.9: the source of the discrete comparison map is the sigma of the limits
of the component diagrams, hence also the sigma of their section sets. -/
private noncomputable def discrete_limit_sigma_sections_equiv
    {J : Type u} [SmallCategory J] [HasLimitsOfShape J (Type v)] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) :
    (Σ b : β, (limit K).obj ⟨b⟩) ≃
      Σ b : β, (K ⋙ (evaluation (Discrete β) (Type v)).obj ⟨b⟩).sections :=
  Equiv.sigmaCongrRight fun b =>
    (limitObjIsoLimitCompEvaluation K ⟨b⟩).toEquiv.trans (Types.limitEquivSections _)

/-- Helper for Lemma 4.19.9: on a chosen summand, the source comparison equivalence is given by
the evaluation-limit comparison followed by the usual section description of limits in `Type`. -/
private theorem discrete_limit_sigma_sections_equiv_apply
    {J : Type u} [SmallCategory J] [HasLimitsOfShape J (Type v)] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (b : β) (x : (limit K).obj ⟨b⟩) :
    discrete_limit_sigma_sections_equiv K ⟨b, x⟩ =
      ⟨b, Types.limitEquivSections _
        ((limitObjIsoLimitCompEvaluation K ⟨b⟩).hom x)⟩ := rfl

/-- Helper for Lemma 4.19.9: under the section identifications on source and target,
`limit.post K (discrete_sigma_functor β)` is the evident sigma of the componentwise comparison
maps. -/
private theorem discrete_sigma_limit_post_components
    {J : Type u} [SmallCategory J] [IsConnected J] [HasLimitsOfShape J (Type v)] {β : Type v}
    (K : J ⥤ Discrete β ⥤ Type v) (z : Σ b : β, (limit K).obj ⟨b⟩) :
    ((Types.limitEquivSections (K ⋙ discrete_sigma_functor β)).trans
      (connected_sigma_sections_equiv K))
      (limit.post K (discrete_sigma_functor β) z) =
    discrete_limit_sigma_sections_equiv K z := by
  rcases z with ⟨b, x⟩
  have hsection :
      Types.limitEquivSections (K ⋙ discrete_sigma_functor β)
          (limit.post K (discrete_sigma_functor β) ⟨b, x⟩) =
        connected_sigma_sections_backward K
          (discrete_limit_sigma_sections_equiv K ⟨b, x⟩) := by
    -- Both sections are computed componentwise from the same family of projections.
    apply Subtype.ext
    funext j
    rw [discrete_limit_sigma_sections_equiv_apply]
    rw [Types.limitEquivSections_apply]
    have hpost := congrFun (limit.post_π K (discrete_sigma_functor β) j) ⟨b, x⟩
    apply Eq.trans (by simpa using hpost)
    simp [connected_sigma_sections_backward, discrete_sigma_functor]
    simpa using
      (congrFun (limitObjIsoLimitCompEvaluation_hom_π K j ⟨b⟩) x).symm
  -- The target equivalence was built from `connected_sigma_sections_backward`, so the comparison
  -- now collapses to the right-inverse identity already proved above.
  calc
    ((Types.limitEquivSections (K ⋙ discrete_sigma_functor β)).trans
        (connected_sigma_sections_equiv K))
        (limit.post K (discrete_sigma_functor β) ⟨b, x⟩)
      = connected_sigma_sections_equiv K
          (connected_sigma_sections_backward K
            (discrete_limit_sigma_sections_equiv K ⟨b, x⟩)) := by
          exact congrArg (connected_sigma_sections_equiv K) hsection
    _ = discrete_limit_sigma_sections_equiv K ⟨b, x⟩ := by
      exact connected_sigma_sections_right_inv K _

/-- Helper for Lemma 4.19.9: discrete coproducts of sets commute with finite connected limits. -/
private theorem discrete_colimit_preserves_connected_limits_of_types
    {J : Type u} [SmallCategory J] [FinCategory J] [IsConnected J] (β : Type v) :
    PreservesLimitsOfShape J (colim : (Discrete β ⥤ Type v) ⥤ Type v) := by
  letI : HasLimitsOfShape J (Type v) := by infer_instance
  letI : PreservesLimitsOfShape J (discrete_sigma_functor β) := by
    constructor
    intro K
    let eSource := discrete_limit_sigma_sections_equiv K
    let eTarget :=
      (Types.limitEquivSections (K ⋙ discrete_sigma_functor β)).trans
        (connected_sigma_sections_equiv K)
    have hbij : Function.Bijective (limit.post K (discrete_sigma_functor β)) := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        -- The explicit sigma-of-sections model turns the comparison into an injective equivalence.
        apply eSource.injective
        calc
          eSource x = eTarget (limit.post K (discrete_sigma_functor β) x) := by
            simpa [eSource, eTarget] using (discrete_sigma_limit_post_components K x).symm
          _ = eTarget (limit.post K (discrete_sigma_functor β) y) := by
            simpa [hxy]
          _ = eSource y := by
            simpa [eSource, eTarget] using discrete_sigma_limit_post_components K y
      · intro y
        -- Surjectivity follows by pulling back along the source equivalence and then comparing.
        refine ⟨eSource.symm (eTarget y), ?_⟩
        apply eTarget.injective
        calc
          eTarget
              (limit.post K (discrete_sigma_functor β) (eSource.symm (eTarget y)))
            = eSource (eSource.symm (eTarget y)) := by
                simpa [eSource, eTarget] using
                  discrete_sigma_limit_post_components K (eSource.symm (eTarget y))
          _ = eTarget y := by
            exact eSource.apply_symm_apply (eTarget y)
    letI : IsIso (limit.post K (discrete_sigma_functor β)) := (isIso_iff_bijective _).2 hbij
    -- Once the comparison map is an isomorphism, preservation of this limit is formal.
    exact (preservesLimit_of_isIso_post (F := K) (G := discrete_sigma_functor β))
  -- Transport the preservation statement from the explicit sigma coproduct back to `colim`.
  exact preservesLimitsOfShape_of_natIso (J := J) (discrete_colimit_iso_sigma_functor β).symm

/-- Helper for Lemma 4.19.9: index the connected components of `I` by the actual quotient type
before shrinking the base to fit the universe required by the Grothendieck gluing theorem. -/
private abbrev component_family_unshrunk : Discrete (ConnectedComponents I) ⥤ Cat :=
  Discrete.functor (fun j : ConnectedComponents I => Cat.of j.Component)

/-- Helper for Lemma 4.19.9: the quotient indexing connected components of `I` is itself
`v`-small because it is a quotient of the `v`-small object type of `I`. -/
private instance connected_components_small : Small.{v} (ConnectedComponents I) := by
  dsimp [ConnectedComponents]
  infer_instance

/-- Helper for Lemma 4.19.9: shrink the discrete base of connected components while keeping the
same fiber categories. -/
private noncomputable abbrev component_family :
    Discrete (Shrink.{v} (ConnectedComponents I)) ⥤ Cat :=
  (Discrete.equivalence (equivShrink.{v} (ConnectedComponents I)).symm).functor ⋙
    component_family_unshrunk (I := I)

/-- Helper for Lemma 4.19.9: the unshrunk component family acts by the identity functor on each
identity morphism of the discrete base, at the level of objects. -/
private theorem component_family_unshrunk_map_id_obj (j : ConnectedComponents I)
    (X : j.Component) :
    ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X = X := by
  simp [component_family_unshrunk]

/-- Helper for Lemma 4.19.9: after collapsing a discrete base morphism to the identity, transport
its fiber morphism back to the actual source object in the connected component. -/
private def component_family_unshrunk_transport_hom (j : ConnectedComponents I)
    {X Y : j.Component}
    (f : ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶ Y) :
    X ⟶ Y :=
  Eq.ndrec (motive := fun X' => X' ⟶ Y) f
    (component_family_unshrunk_map_id_obj (I := I) j X)

/-- Helper for Lemma 4.19.9: transporting the identity fiber morphism along the identity base map
recovers the identity morphism in the component category. -/
private theorem component_family_unshrunk_transport_hom_id (j : ConnectedComponents I)
    (X : j.Component) :
    component_family_unshrunk_transport_hom (I := I) j (eqToHom (by simp :
      ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X = X)) = 𝟙 X := by
  -- The identity functor on the fiber carries no extra transport once the object equality is
  -- reduced.
  unfold component_family_unshrunk_transport_hom
  cases component_family_unshrunk_map_id_obj (I := I) j X
  rfl

/-- Helper for Lemma 4.19.9: transporting the Grothendieck composite over a discrete identity is
the same as composing the transported fiber morphisms in the component category. -/
private theorem component_family_unshrunk_transport_hom_comp (j : ConnectedComponents I)
    {X Y Z : j.Component}
    (f : ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶ Y)
    (g : ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj Y ⟶ Z) :
    component_family_unshrunk_transport_hom (I := I) j
      (eqToHom (by simp) ≫
        (((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.map f) ≫ g) =
      component_family_unshrunk_transport_hom (I := I) j f ≫
        component_family_unshrunk_transport_hom (I := I) j g := by
  -- Once both identity-base functors are reduced to the identity functor on `j.Component`, the
  -- Grothendieck composite is just ordinary composition.
  unfold component_family_unshrunk_transport_hom
  cases component_family_unshrunk_map_id_obj (I := I) j X
  cases component_family_unshrunk_map_id_obj (I := I) j Y
  simpa [component_family_unshrunk] using (Category.id_comp (f ≫ g))

/-- Helper for Lemma 4.19.9: if a genuine component morphism is first viewed over the identity base
map and then transported back, nothing changes. -/
private theorem component_family_unshrunk_transport_hom_from_hom (j : ConnectedComponents I)
    {X Y : j.Component} (f : X ⟶ Y) :
    component_family_unshrunk_transport_hom (I := I) j (eqToHom (by simp) ≫ f) = f := by
  -- The only extra data is the identity on the source object, so transport removes it.
  unfold component_family_unshrunk_transport_hom
  cases component_family_unshrunk_map_id_obj (I := I) j X
  change 𝟙 X ≫ f = f
  simpa using (Category.id_comp f)

/-- Helper for Lemma 4.19.9: transport along the identity base map in the unshrunk component family
is injective on fiber morphisms. -/
private theorem component_family_unshrunk_transport_hom_injective (j : ConnectedComponents I)
    {X Y : j.Component}
    {f g : ((component_family_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶ Y}
    (h : component_family_unshrunk_transport_hom (I := I) j f =
      component_family_unshrunk_transport_hom (I := I) j g) :
    f = g := by
  -- After reducing the identity-base functor to the identity functor, transport is literally the
  -- identity on morphisms.
  unfold component_family_unshrunk_transport_hom at h
  cases component_family_unshrunk_map_id_obj (I := I) j X
  simpa using h

/-- Helper for Lemma 4.19.9: forget the redundant discrete base data in the Grothendieck
construction of the unshrunk component family, keeping only the component index and the fiber
object. -/
private noncomputable def grothendieck_component_family_unshrunk_to_decomposed :
    Grothendieck (component_family_unshrunk (I := I)) ⥤ Decomposed I where
  obj X := ⟨X.base.as, X.fiber⟩
  map := by
    -- A Grothendieck morphism over a discrete base cannot cross components. After collapsing the
    -- base to the identity, only the transported fiber morphism remains.
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨base, fiber⟩
    have h : j = k := Discrete.eq_of_hom base
    cases h
    exact Sigma.SigmaHom.mk (component_family_unshrunk_transport_hom (I := I) j fiber)
  map_id := by
    -- On identities, the transported fiber morphism is exactly the identity in the component.
    rintro ⟨⟨j⟩, X⟩
    refine congrArg Sigma.SigmaHom.mk ?_
    exact component_family_unshrunk_transport_hom_id (I := I) j X
  map_comp := by
    -- Composition is computed inside one connected component once both discrete base morphisms
    -- are collapsed to identities.
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨⟨l⟩, Z⟩ ⟨base_f, fiber_f⟩ ⟨base_g, fiber_g⟩
    have hk : j = k := Discrete.eq_of_hom base_f
    have hl : k = l := Discrete.eq_of_hom base_g
    cases hk
    cases hl
    have hbase_f : base_f = 𝟙 (Discrete.mk j) := Subsingleton.elim _ _
    have hbase_g : base_g = 𝟙 (Discrete.mk j) := Subsingleton.elim _ _
    cases hbase_f
    cases hbase_g
    refine congrArg Sigma.SigmaHom.mk ?_
    exact component_family_unshrunk_transport_hom_comp (I := I) j fiber_f fiber_g

/-- Helper for Lemma 4.19.9: every sigma-category morphism between component objects comes from the
unique Grothendieck morphism over the corresponding identity in the discrete base. -/
private instance grothendieck_component_family_unshrunk_to_decomposed_full :
    (grothendieck_component_family_unshrunk_to_decomposed (I := I)).Full where
  map_surjective := by
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨fiber⟩
    refine ⟨{ base := 𝟙 _, fiber := eqToHom (by simp) ≫ fiber }, ?_⟩
    -- The chosen Grothendieck morphism is the unique morphism over the identity whose transported
    -- fiber is the given sigma-category morphism.
    refine congrArg Sigma.SigmaHom.mk ?_
    exact component_family_unshrunk_transport_hom_from_hom (I := I) j fiber

/-- Helper for Lemma 4.19.9: two Grothendieck morphisms over the discrete component family are
equal as soon as their images in the sigma-category agree. -/
private instance grothendieck_component_family_unshrunk_to_decomposed_faithful :
    (grothendieck_component_family_unshrunk_to_decomposed (I := I)).Faithful where
  map_injective := by
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨base_f, fiber_f⟩ ⟨base_g, fiber_g⟩ h
    have hf : j = k := Discrete.eq_of_hom base_f
    have hg : j = k := Discrete.eq_of_hom base_g
    cases hf
    cases hg
    have hbase : base_f = base_g := Subsingleton.elim _ _
    cases hbase
    have htransport :
        component_family_unshrunk_transport_hom (I := I) j fiber_f =
          component_family_unshrunk_transport_hom (I := I) j fiber_g := by
      injection h
    have hfiber : fiber_f = fiber_g :=
      component_family_unshrunk_transport_hom_injective (I := I) j htransport
    refine Grothendieck.ext _ _ rfl ?_
    · simpa [hfiber] using Category.id_comp fiber_g

/-- Helper for Lemma 4.19.9: every object of the decomposed category is literally represented by an
object of the Grothendieck construction of the unshrunk component family. -/
private instance grothendieck_component_family_unshrunk_to_decomposed_essSurj :
    (grothendieck_component_family_unshrunk_to_decomposed (I := I)).EssSurj where
  mem_essImage := by
    rintro ⟨j, X⟩
    exact ⟨⟨⟨j⟩, X⟩, ⟨Iso.refl _⟩⟩

/-- Helper for Lemma 4.19.9: the forgetful functor from the Grothendieck construction to the
decomposed category is an equivalence. -/
private instance grothendieck_component_family_unshrunk_to_decomposed_isEquivalence :
    (grothendieck_component_family_unshrunk_to_decomposed (I := I)).IsEquivalence where

/-- Helper for Lemma 4.19.9: the Grothendieck construction of the unshrunk discrete component
family is canonically equivalent to the sigma-category of connected components. -/
private noncomputable def grothendieck_component_family_unshrunk_equiv_decomposed :
    Grothendieck (component_family_unshrunk (I := I)) ≌ Decomposed I :=
  (grothendieck_component_family_unshrunk_to_decomposed (I := I)).asEquivalence

/-- Helper for Lemma 4.19.9: after shrinking the discrete base and identifying the resulting
Grothendieck construction with the sigma-category of connected components, the canonical
decomposition equivalence transports us back to `I`. -/
private noncomputable abbrev component_family_grothendieck_equiv :
    Grothendieck (component_family (I := I)) ≌ I :=
  (Grothendieck.preEquivalence (component_family_unshrunk (I := I))
      (Discrete.equivalence (equivShrink.{v} (ConnectedComponents I)).symm)).trans
    ((grothendieck_component_family_unshrunk_equiv_decomposed (I := I)).trans
      (CategoryTheory.decomposedEquiv (J := I)))

/-- Helper for Lemma 4.19.9: replace each connected component category by its actual `v`-small
shrink, while keeping the quotient of connected components itself unshrunk for the moment. -/
private noncomputable abbrev component_family_small_unshrunk :
    Discrete (ConnectedComponents I) ⥤ Cat :=
  Discrete.functor (fun j : ConnectedComponents I => Cat.of (Shrink.{v, uI} j.Component))

/-- Helper for Lemma 4.19.9: shrink the discrete base of connected components and at the same time
keep every connected-component fiber `v`-small. -/
private noncomputable abbrev component_family_small :
    Discrete (Shrink.{v} (ConnectedComponents I)) ⥤ Cat :=
  (Discrete.equivalence (equivShrink.{v} (ConnectedComponents I)).symm).functor ⋙
    component_family_small_unshrunk (I := I)

/-- Helper for Lemma 4.19.9: each shrunk connected component is canonically equivalent to the
original component category. -/
private noncomputable abbrev component_family_small_fiber_equiv
    (j : ConnectedComponents I) : j.Component ≌ Shrink.{v, uI} j.Component :=
  CategoryTheory.Shrink.equivalence.{v} j.Component

/-- Helper for Lemma 4.19.9: the small component family acts by the identity functor on each
identity morphism of the discrete base, at the level of objects. -/
private theorem component_family_small_unshrunk_map_id_obj (j : ConnectedComponents I)
    (X : Shrink.{v, uI} j.Component) :
    ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X = X := by
  simp [component_family_small_unshrunk]

/-- Helper for Lemma 4.19.9: after collapsing a discrete-base identity in the small component
family, transport a fiber morphism back to the original source object. -/
private def component_family_small_unshrunk_transport_hom (j : ConnectedComponents I)
    {X Y : Shrink.{v, uI} j.Component}
    (f : ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶
      Y) :
    X ⟶ Y :=
  Eq.ndrec (motive := fun X' => X' ⟶ Y) f
    (component_family_small_unshrunk_map_id_obj (I := I) j X)

/-- Helper for Lemma 4.19.9: transporting the identity fiber morphism along the identity base map
in the small component family recovers the identity morphism. -/
private theorem component_family_small_unshrunk_transport_hom_id (j : ConnectedComponents I)
    (X : Shrink.{v, uI} j.Component) :
    component_family_small_unshrunk_transport_hom (I := I) j (eqToHom (by simp :
      ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X =
        X)) = 𝟙 X := by
  -- The identity-base functor is the identity on the shrunk fiber once transports are reduced.
  unfold component_family_small_unshrunk_transport_hom
  cases component_family_small_unshrunk_map_id_obj (I := I) j X
  rfl

/-- Helper for Lemma 4.19.9: transporting the Grothendieck composite over a discrete identity in
the small component family is the same as ordinary composition in that shrunk fiber. -/
private theorem component_family_small_unshrunk_transport_hom_comp (j : ConnectedComponents I)
    {X Y Z : Shrink.{v, uI} j.Component}
    (f : ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶
      Y)
    (g : ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj Y ⟶
      Z) :
    component_family_small_unshrunk_transport_hom (I := I) j
      (eqToHom (by simp) ≫
        (((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.map f) ≫
          g) =
      component_family_small_unshrunk_transport_hom (I := I) j f ≫
        component_family_small_unshrunk_transport_hom (I := I) j g := by
  -- Once the identity-base functors are simplified away, the Grothendieck composite is just the
  -- fiberwise composition in the fully shrunk component category.
  unfold component_family_small_unshrunk_transport_hom
  cases component_family_small_unshrunk_map_id_obj (I := I) j X
  cases component_family_small_unshrunk_map_id_obj (I := I) j Y
  simpa [component_family_small_unshrunk] using (Category.id_comp (f ≫ g))

/-- Helper for Lemma 4.19.9: if a shrunk-fiber morphism is first viewed over the identity base map
and then transported back, nothing changes. -/
private theorem component_family_small_unshrunk_transport_hom_from_hom
    (j : ConnectedComponents I) {X Y : Shrink.{v, uI} j.Component} (f : X ⟶ Y) :
    component_family_small_unshrunk_transport_hom (I := I) j (eqToHom (by simp) ≫ f) = f := by
  -- The only extra data is the identity on the source object, which transport removes again.
  unfold component_family_small_unshrunk_transport_hom
  cases component_family_small_unshrunk_map_id_obj (I := I) j X
  change 𝟙 X ≫ f = f
  simpa using (Category.id_comp f)

/-- Helper for Lemma 4.19.9: transport along the identity base map in the small component family
is injective on fiber morphisms. -/
private theorem component_family_small_unshrunk_transport_hom_injective
    (j : ConnectedComponents I) {X Y : Shrink.{v, uI} j.Component}
    {f g :
      ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X ⟶ Y}
    (h : component_family_small_unshrunk_transport_hom (I := I) j f =
      component_family_small_unshrunk_transport_hom (I := I) j g) :
    f = g := by
  -- After reducing the identity-base functor, transport becomes the identity on morphisms.
  unfold component_family_small_unshrunk_transport_hom at h
  cases component_family_small_unshrunk_map_id_obj (I := I) j X
  simpa using h

/-- Helper for Lemma 4.19.9: forget the redundant discrete base data in the Grothendieck
construction of the fully small component family, and identify the shrunk fiber with the original
component. -/
private noncomputable def grothendieck_component_family_small_unshrunk_to_decomposed :
    Grothendieck (component_family_small_unshrunk (I := I)) ⥤ Decomposed I where
  obj X :=
    ⟨X.base.as, (component_family_small_fiber_equiv (I := I) X.base.as).inverse.obj X.fiber⟩
  map := by
    -- A morphism over a discrete base stays in one component, and the fiber part is sent back to
    -- the original component category via the inverse shrink equivalence.
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨base, fiber⟩
    have h : j = k := Discrete.eq_of_hom base
    cases h
    exact Sigma.SigmaHom.mk
      ((component_family_small_fiber_equiv (I := I) j).inverse.map
        (component_family_small_unshrunk_transport_hom (I := I) j fiber))
  map_id := by
    -- After transport along the identity base map, the remaining fiber identity is preserved by
    -- the inverse shrink equivalence.
    rintro ⟨⟨j⟩, X⟩
    let E := (component_family_small_fiber_equiv (I := I) j).inverse
    refine congrArg Sigma.SigmaHom.mk ?_
    calc
      E.map
          (component_family_small_unshrunk_transport_hom (I := I) j
            (eqToHom (by simp :
              ((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.obj X =
                X)))
        =
          E.map (𝟙 X) := by
            exact congrArg E.map
              (component_family_small_unshrunk_transport_hom_id (I := I) j X)
      _ = 𝟙 _ := by
            exact E.map_id X
  map_comp := by
    -- Over a discrete base, composition reduces to fiberwise composition, which the inverse
    -- shrink equivalence carries back to the original component.
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨⟨l⟩, Z⟩ ⟨base_f, fiber_f⟩ ⟨base_g, fiber_g⟩
    have hk : j = k := Discrete.eq_of_hom base_f
    have hl : k = l := Discrete.eq_of_hom base_g
    cases hk
    cases hl
    have hbase_f : base_f = 𝟙 (Discrete.mk j) := Subsingleton.elim _ _
    have hbase_g : base_g = 𝟙 (Discrete.mk j) := Subsingleton.elim _ _
    cases hbase_f
    cases hbase_g
    refine congrArg Sigma.SigmaHom.mk ?_
    calc
      (component_family_small_fiber_equiv (I := I) j).inverse.map
          (component_family_small_unshrunk_transport_hom (I := I) j
            (eqToHom (by simp) ≫
              (((component_family_small_unshrunk (I := I)).map (𝟙 (Discrete.mk j))).toFunctor.map
                  fiber_f) ≫
                fiber_g))
        =
          (component_family_small_fiber_equiv (I := I) j).inverse.map
            (component_family_small_unshrunk_transport_hom (I := I) j fiber_f ≫
              component_family_small_unshrunk_transport_hom (I := I) j fiber_g) := by
            congr 1
            exact component_family_small_unshrunk_transport_hom_comp (I := I) j fiber_f fiber_g
      _ =
          (component_family_small_fiber_equiv (I := I) j).inverse.map
              (component_family_small_unshrunk_transport_hom (I := I) j fiber_f) ≫
            (component_family_small_fiber_equiv (I := I) j).inverse.map
              (component_family_small_unshrunk_transport_hom (I := I) j fiber_g) := by
            simpa using
              Functor.map_comp ((component_family_small_fiber_equiv (I := I) j).inverse)
                (component_family_small_unshrunk_transport_hom (I := I) j fiber_f)
                (component_family_small_unshrunk_transport_hom (I := I) j fiber_g)

/-- Helper for Lemma 4.19.9: every sigma-category morphism between decomposed objects comes from
the unique Grothendieck morphism over the corresponding identity in the fully small component
family. -/
private instance grothendieck_component_family_small_unshrunk_to_decomposed_full :
    (grothendieck_component_family_small_unshrunk_to_decomposed (I := I)).Full where
  map_surjective := by
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨fiber⟩
    let E := (component_family_small_fiber_equiv (I := I) j).inverse
    refine ⟨{ base := 𝟙 _, fiber := eqToHom (by simp) ≫ E.preimage fiber }, ?_⟩
    -- The chosen preimage in the shrunk fiber maps back to the requested component morphism.
    refine congrArg Sigma.SigmaHom.mk ?_
    calc
      E.map
          (component_family_small_unshrunk_transport_hom (I := I) j
            (eqToHom (by simp) ≫ E.preimage fiber))
        = E.map (E.preimage fiber) := by
            congr 1
            exact component_family_small_unshrunk_transport_hom_from_hom (I := I) j
              (E.preimage fiber)
      _ = fiber := by
            simpa [E] using Functor.map_preimage E fiber

/-- Helper for Lemma 4.19.9: two Grothendieck morphisms over the fully small component family are
equal as soon as their images in the decomposed sigma-category agree. -/
private instance grothendieck_component_family_small_unshrunk_to_decomposed_faithful :
    (grothendieck_component_family_small_unshrunk_to_decomposed (I := I)).Faithful where
  map_injective := by
    rintro ⟨⟨j⟩, X⟩ ⟨⟨k⟩, Y⟩ ⟨base_f, fiber_f⟩ ⟨base_g, fiber_g⟩ h
    have hf : j = k := Discrete.eq_of_hom base_f
    have hg : j = k := Discrete.eq_of_hom base_g
    cases hf
    cases hg
    have hbase : base_f = base_g := Subsingleton.elim _ _
    cases hbase
    have htransport :
        (component_family_small_fiber_equiv (I := I) j).inverse.map
            (component_family_small_unshrunk_transport_hom (I := I) j fiber_f) =
          (component_family_small_fiber_equiv (I := I) j).inverse.map
            (component_family_small_unshrunk_transport_hom (I := I) j fiber_g) := by
      injection h
    have hmap :
        component_family_small_unshrunk_transport_hom (I := I) j fiber_f =
          component_family_small_unshrunk_transport_hom (I := I) j fiber_g :=
      ((component_family_small_fiber_equiv (I := I) j).inverse).map_injective htransport
    have hfiber :
        fiber_f = fiber_g :=
      component_family_small_unshrunk_transport_hom_injective (I := I) j hmap
    refine Grothendieck.ext _ _ rfl ?_
    simpa [hfiber] using Category.id_comp fiber_g

/-- Helper for Lemma 4.19.9: every object of the decomposed category is represented by an object
of the Grothendieck construction of the fully small component family. -/
private instance grothendieck_component_family_small_unshrunk_to_decomposed_essSurj :
    (grothendieck_component_family_small_unshrunk_to_decomposed (I := I)).EssSurj where
  mem_essImage := by
    rintro ⟨j, X⟩
    refine ⟨⟨⟨j⟩, (component_family_small_fiber_equiv (I := I) j).functor.obj X⟩, ?_⟩
    let e := ((component_family_small_fiber_equiv (I := I) j).unitIso.app X).symm
    refine ⟨⟨Sigma.SigmaHom.mk e.hom, Sigma.SigmaHom.mk e.inv, ?_, ?_⟩⟩
    · exact congrArg Sigma.SigmaHom.mk e.hom_inv_id
    · exact congrArg Sigma.SigmaHom.mk e.inv_hom_id

/-- Helper for Lemma 4.19.9: the forgetful functor from the fully small Grothendieck construction
to the decomposed category is an equivalence. -/
private instance grothendieck_component_family_small_unshrunk_to_decomposed_isEquivalence :
    (grothendieck_component_family_small_unshrunk_to_decomposed (I := I)).IsEquivalence where

/-- Helper for Lemma 4.19.9: the Grothendieck construction of the fully small discrete component
family is canonically equivalent to the sigma-category of connected components. -/
private noncomputable def grothendieck_component_family_small_unshrunk_equiv_decomposed :
    Grothendieck (component_family_small_unshrunk (I := I)) ≌ Decomposed I :=
  (grothendieck_component_family_small_unshrunk_to_decomposed (I := I)).asEquivalence

/-- Helper for Lemma 4.19.9: after shrinking both the base of connected components and each fiber,
the resulting Grothendieck construction is still canonically equivalent to `I`. -/
private noncomputable abbrev component_family_small_grothendieck_equiv :
    Grothendieck (component_family_small (I := I)) ≌ I :=
  (Grothendieck.preEquivalence (component_family_small_unshrunk (I := I))
      (Discrete.equivalence (equivShrink.{v} (ConnectedComponents I)).symm)).trans
    ((grothendieck_component_family_small_unshrunk_equiv_decomposed (I := I)).trans
      (CategoryTheory.decomposedEquiv (J := I)))

/-- Helper for Lemma 4.19.9: once both the connected-component base and every connected-component
fiber are shrunk to universe `v`, the Grothendieck gluing theorem applies directly to the resulting
small total category. -/
private theorem component_family_small_preserves_connected_limits_of_types
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    [∀ j : ConnectedComponents I, IsFiltered j.Component] :
    PreservesLimitsOfShape J
      (colim : (Grothendieck (component_family_small (I := I)) ⥤ Type v) ⥤ Type v) := by
  -- The discrete base contributes only coproducts, which preserve connected finite limits in
  -- `Type` by the sigma-section calculation proved earlier in this file.
  let _ : PreservesLimitsOfShape J
      (colim : (Discrete (Shrink.{v} (ConnectedComponents I)) ⥤ Type v) ⥤ Type v) :=
    discrete_colimit_preserves_connected_limits_of_types (Shrink.{v} (ConnectedComponents I))
  -- Each fiber is the explicit `Shrink` model of a filtered connected component, so the filtered
  -- colimit theorem applies after transporting filteredness across the equivalence of fibers.
  let _ (j : Discrete (Shrink.{v} (ConnectedComponents I))) :
      PreservesLimitsOfShape J
        (colim : ((component_family_small (I := I)).obj j ⥤ Type v) ⥤ Type v) := by
    let _ : IsFiltered (((equivShrink.{v} (ConnectedComponents I)).symm j.as).Component) :=
      inferInstance
    let _ :
        IsFiltered (Shrink.{v, uI} (((equivShrink.{v} (ConnectedComponents I)).symm j.as).Component)) :=
      IsFiltered.of_equivalence
        (component_family_small_fiber_equiv (I := I)
          ((equivShrink.{v} (ConnectedComponents I)).symm j.as))
    simpa [component_family_small, component_family_small_unshrunk] using
      (inferInstance :
        PreservesLimitsOfShape J
          (colim :
            (Shrink.{v, uI} (((equivShrink.{v} (ConnectedComponents I)).symm j.as).Component) ⥤
              Type v) ⥤ Type v))
  -- With base and fiber preservation available, the Grothendieck gluing theorem supplies the
  -- total-category preservation statement.
  infer_instance

private theorem componentwiseFiltered_preservesFiniteConnectedLimitsOfTypes
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    [∀ j : ConnectedComponents I, IsFiltered j.Component] :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Route correction: instead of transporting through a hand-built fully shrunk total category,
  -- we reuse the already proved fully shrunk Grothendieck model and only simplify the last
  -- transport step using finality of the equivalence functor.
  let e := component_family_small_grothendieck_equiv (I := I)
  -- First obtain preservation on the Grothendieck model coming from the discrete decomposition by
  -- connected components and filtered colimits on each component.
  let _ :
      PreservesLimitsOfShape J
        (colim : (Grothendieck (component_family_small (I := I)) ⥤ Type v) ⥤ Type v) :=
    component_family_small_preserves_connected_limits_of_types (I := I) J
  -- Precomposition along the equivalence functor preserves limits, so the transported colimit
  -- functor is again limit-preserving.
  let _ :
      PreservesLimitsOfShape J
        (((Functor.whiskeringLeft _ _ _).obj e.functor) ⋙
          (colim : (Grothendieck (component_family_small (I := I)) ⥤ Type v) ⥤ Type v)) :=
    inferInstance
  -- Finality of the equivalence functor identifies that transported colimit with the original
  -- colimit over `I`.
  exact preservesLimitsOfShape_of_natIso (J := J) (Functor.Final.colimIso e.functor)

/-- Lemma 4.19.9: assume every span in `I` admits a commuting cocone and every parallel pair in
`I` becomes equal after postcomposition. Then colimits over `I` commute with finite connected
limits in the category of sets. This is the source-faithful statement obtained by combining the
connected-component decomposition from Lemma 4.19.8 with the canonical mathlib result that
filtered colimits in `Type` commute with finite limits. -/
theorem colimit_preserves_finite_connected_limits_of_types
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J]
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Each connected component is filtered by Lemma 4.19.8, so the proof reduces to the
  -- componentwise filtered bridge theorem above.
  let _ (j : ConnectedComponents I) : IsFiltered j.Component :=
    connected_components_are_filtered hMap j
  exact componentwiseFiltered_preservesFiniteConnectedLimitsOfTypes J

-- Proof sketch: specialize the finite-connected-limit statement to the walking cospan.
/-- Under the hypotheses of Lemma 4.19.9, colimits of sets over `I` preserve pullbacks. -/
theorem colimit_preserves_pullbacks_of_types
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Pullbacks are finite connected limits.
  simpa using colimit_preserves_finite_connected_limits_of_types WalkingCospan hMap

-- Proof sketch: specialize the finite-connected-limit statement to the walking parallel pair.
/-- Under the hypotheses of Lemma 4.19.9, colimits of sets over `I` preserve equalizers. -/
theorem colimit_preserves_equalizers_of_types
    (hMap : ∀ ⦃X Y : I⦄ (f g : X ⟶ Y), ∃ (Z : I) (h : Y ⟶ Z), f ≫ h = g ≫ h) :
    PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Equalizers are finite connected limits.
  simpa using colimit_preserves_finite_connected_limits_of_types WalkingParallelPair hMap

end SourceFacing

section FilteredOrEmpty

variable [IsFilteredOrEmpty I]

/-- If `I` is filtered or empty, then it satisfies the source-facing hypotheses used above, so the
finite-connected-limit statement specializes to the traditional filtered-or-empty formulation. -/
theorem filtered_or_empty_colimit_preserves_finite_connected_limits_of_types
    (J : Type u) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- The filtered-or-empty hypothesis supplies the postcomposition equalizer condition needed by
  -- the source-facing theorem.
  let h :
      PreservesLimitsOfShape J (colim : (I ⥤ Type v) ⥤ Type v) :=
    colimit_preserves_finite_connected_limits_of_types J
      (fun {_ _} f g ↦ IsFilteredOrEmpty.cocone_maps f g)
  exact h

/-- Filtered-or-empty colimits of sets preserve fibre products. -/
theorem filtered_or_empty_colimit_preserves_pullbacks_of_types :
    PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Apply the finite-connected-limit theorem to the pullback shape.
  let h :
      PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) :=
    filtered_or_empty_colimit_preserves_finite_connected_limits_of_types WalkingCospan
  exact h

/-- Filtered-or-empty colimits of sets preserve equalizers. -/
theorem filtered_or_empty_colimit_preserves_equalizers_of_types :
    PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) := by
  -- Apply the finite-connected-limit theorem to the equalizer shape.
  let h :
      PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) :=
    filtered_or_empty_colimit_preserves_finite_connected_limits_of_types WalkingParallelPair
  exact h

end FilteredOrEmpty

end CategoryTheory.Limits

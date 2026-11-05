module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.Data.Finite.Card
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

namespace SemiRepresentableFamily.Over

/-- Helper for Lemma 7.39.2: replace an arbitrary finite indexed covering family by the
equivalent `Fin n`-indexed family. This keeps the scheduled request type in the same universe as
the fiber data, rather than one universe higher because of an arbitrary finite index type. -/
noncomputable def finReindex {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W)
    [Finite 𝒰.index] :
    SemiRepresentableFamily.Over.{0} W where
  index := Fin (Nat.card 𝒰.index)
  obj := fun i ↦ 𝒰.obj ((Finite.equivFin 𝒰.index).symm i)

/-- Helper for Lemma 7.39.2: finite reindexing does not change the generated presieve. -/
theorem finReindex_toPresieve {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W)
    [Finite 𝒰.index] :
    (finReindex 𝒰).toPresieve = 𝒰.toPresieve := by
  change Presieve.ofArrows
      (fun i : Fin (Nat.card 𝒰.index) =>
        (𝒰.obj ((Finite.equivFin 𝒰.index).symm i)).left)
      (fun i : Fin (Nat.card 𝒰.index) =>
        (𝒰.obj ((Finite.equivFin 𝒰.index).symm i)).hom) =
    Presieve.ofArrows (fun i : 𝒰.index => (𝒰.obj i).left) fun i => (𝒰.obj i).hom
  simpa using
    (Presieve.ofArrows_comp_eq_of_surjective
      (Y := fun i : 𝒰.index => (𝒰.obj i).left)
      (f := fun i : 𝒰.index => (𝒰.obj i).hom)
      (a := (Finite.equivFin 𝒰.index).symm)
      (Equiv.surjective (Finite.equivFin 𝒰.index).symm))

/-- Helper for Lemma 7.39.2: finite reindexing does not change the generated sieve. -/
theorem finReindex_toSieve {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W)
    [Finite 𝒰.index] :
    (finReindex 𝒰).toSieve = 𝒰.toSieve := by
  simpa [toSieve] using congrArg Sieve.generate (finReindex_toPresieve 𝒰)

end SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.2: equality of two inverse-system raw-fiber generators over
the same object is witnessed after moving to a common later element of the inverse-system fiber. -/
lemma inverseSystem_toPresheafFiber_eq_iff
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    [InitiallySmall ιᵒᵖ] (S : ιᵒᵖ ⥤ C) {F : Cᵒᵖ ⥤ Type (max u v w)}
    (X : C) (x : (fiber.{max u v w} S).obj X) (z₁ z₂ : F.obj (Opposite.op X)) :
    (fiber.{max u v w} S).toPresheafFiber X x F z₁ =
        (fiber.{max u v w} S).toPresheafFiber X x F z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : (fiber.{max u v w} S).obj Y),
        (fiber.{max u v w} S).map f y = x ∧ F.map f.op z₁ = F.map f.op z₂ := by
  constructor
  · intro h
    obtain ⟨j, f, hf⟩ :=
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (ht := CategoryTheory.Limits.colimit.isColimit
          ((CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F))
        (i := Opposite.op ⟨X, x⟩) z₁ z₂).1 h
    exact ⟨j.unop.1, f.unop.val, j.unop.2, f.unop.property, hf⟩
  · rintro ⟨Y, f, y, hy, hEq⟩
    exact
      (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'
        (ht := CategoryTheory.Limits.colimit.isColimit
          ((CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F))
        (i := Opposite.op ⟨X, x⟩) z₁ z₂).2
        ⟨Opposite.op ⟨Y, y⟩,
          Opposite.op (CategoryOfElements.homMk ⟨Y, y⟩ ⟨X, x⟩ f hy), hEq⟩

/-- Helper for Lemma 7.39.2: one finite-cover lifting obligation for the inverse-system fiber of
`S`. -/
structure finite_cover_lift_request (S : ιᵒᵖ ⥤ C) where
  W : C
  n : ℕ
  obj : Fin n → Over W
  h𝒰 : (SemiRepresentableFamily.Over.toSieve
    ({ index := Fin n, obj := obj } : SemiRepresentableFamily.Over.{0} W)) ∈ J W
  f : (fiber.{max u v w} S).obj W

namespace finite_cover_lift_request

/-- The finite covering family represented by a scheduled lifting request. Keeping the stored
index as `Fin n` makes the request type small in the site/fiber universe while preserving the
source-facing `SemiRepresentableFamily.Over` API. -/
def 𝒰 {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S) :
    SemiRepresentableFamily.Over.{0} r.W where
  index := Fin r.n
  obj := r.obj

/-- The represented covering family has finite index set. -/
instance finite_index {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S) :
    Finite r.𝒰.index := by
  dsimp [𝒰]
  infer_instance

end finite_cover_lift_request

attribute [instance] finite_cover_lift_request.finite_index

/-- Helper for Lemma 7.39.2: after replacing arbitrary finite covers by `Fin n`-indexed
presentations, the scheduled request type is small in the universe generated by the site, homs,
and stage index. -/
theorem finite_cover_lift_request_small
    (S : ιᵒᵖ ⥤ C) :
    Small.{max u v w} (finite_cover_lift_request J S) := by
  infer_instance

/-- Helper for Lemma 7.39.2: if the site/fiber universe is small relative to the stage-index
universe, then the scheduled request type is small in the stage universe itself. This isolates the
universe hypothesis needed by a literal `Type w` transfinite schedule. -/
theorem finite_cover_lift_request_small_stage_universe
    (S : ιᵒᵖ ⥤ C) [UnivLE.{max u v w, w}] :
    Small.{w} (finite_cover_lift_request J S) := by
  infer_instance

/-- Helper for Lemma 7.39.2: a small universe model for the source proof's set `E` of
finite-cover lifting requests. -/
abbrev finite_cover_lift_request_schedule
    (S : ιᵒᵖ ⥤ C) : Type (max u v w) :=
  Shrink.{max u v w} (finite_cover_lift_request J S)

/-- Helper for Lemma 7.39.2: decode one entry of the small request schedule as an actual
finite-cover lifting request. -/
noncomputable def finite_cover_lift_request_of_schedule
    (S : ιᵒᵖ ⥤ C) :
    finite_cover_lift_request_schedule (J := J) S → finite_cover_lift_request J S :=
  (equivShrink (finite_cover_lift_request J S)).symm

/-- Helper for Lemma 7.39.2: every finite-cover lifting request appears in the small schedule. -/
theorem finite_cover_lift_request_of_schedule_surjective
    (S : ιᵒᵖ ⥤ C) :
    Function.Surjective (finite_cover_lift_request_of_schedule (J := J) S) := by
  -- This records explicitly that the shrink model loses no source-proof requests.
  intro r
  refine ⟨(equivShrink (finite_cover_lift_request J S)) r, ?_⟩
  simp [finite_cover_lift_request_of_schedule]

/-- Helper for Lemma 7.39.2: a canonical well-ordering relation on the small model of the
source proof's set of finite-cover lifting requests. This is the Lean replacement for the
source phrase "choose a well ordering on `E`". -/
noncomputable def finite_cover_lift_request_wellOrderRel
    (S : ιᵒᵖ ⥤ C) :
    finite_cover_lift_request J S → finite_cover_lift_request J S → Prop :=
  fun r r' =>
    WellOrderingRel
      ((equivShrink (finite_cover_lift_request J S) :
        finite_cover_lift_request J S ≃
          Shrink.{max u v w} (finite_cover_lift_request J S)) r)
      ((equivShrink (finite_cover_lift_request J S) :
        finite_cover_lift_request J S ≃
          Shrink.{max u v w} (finite_cover_lift_request J S)) r')

/-- Helper for Lemma 7.39.2: the canonical request-ordering relation is a well-order. -/
instance finite_cover_lift_request_wellOrderRel_isWellOrder
    (S : ιᵒᵖ ⥤ C) :
    IsWellOrder (finite_cover_lift_request J S)
      (finite_cover_lift_request_wellOrderRel (J := J) S) := by
  -- Pull back Mathlib's global well-order of the small request model along `equivShrink`.
  change IsWellOrder (finite_cover_lift_request J S)
    (((equivShrink (finite_cover_lift_request J S) :
      finite_cover_lift_request J S ≃
        Shrink.{max u v w} (finite_cover_lift_request J S)) ⁻¹'o WellOrderingRel))
  infer_instance

/-- Helper for Lemma 7.39.2: the source proof's well-order can be viewed as a linear order with
well-founded strict order when recursion over scheduled requests is needed. -/
@[reducible] noncomputable def finite_cover_lift_request_linearOrder
    (S : ιᵒᵖ ⥤ C) :
    LinearOrder (finite_cover_lift_request J S) :=
  IsWellOrder.linearOrder (finite_cover_lift_request_wellOrderRel (J := J) S)

/-- Helper for Lemma 7.39.2: the well-ordering relation on requests is well-founded. -/
theorem finite_cover_lift_request_wellFounded
    (S : ιᵒᵖ ⥤ C) :
    WellFounded (finite_cover_lift_request_wellOrderRel (J := J) S) := by
  -- This is the well-foundedness component needed by any transfinite schedule over requests.
  exact (finite_cover_lift_request_wellOrderRel_isWellOrder (J := J) S).wf

variable {J}

/-- Helper for Lemma 7.39.2: a refinement solves a fixed lifting request when the transported
fiber element lifts through one member of the chosen finite covering family. -/
def request_solved {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S)
    {ι' : Type w} [Preorder ι'] (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) : Prop :=
  ∃ i : r.𝒰.index, ∃ y : (fiber.{max u v w} T).obj (r.𝒰.obj i).left,
    (fiber.{max u v w} T).map (r.𝒰.obj i).hom y =
      (refinementFiber j T e).app r.W r.f

/-- Helper for Lemma 7.39.2: transport one finite-cover lifting request along a refinement of
inverse systems. -/
noncomputable def transport_request {S : ιᵒᵖ ⥤ C}
    {ι' : Type w} [Preorder ι'] (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C)
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) (r : finite_cover_lift_request J S) :
    finite_cover_lift_request J T where
  W := r.W
  n := r.n
  obj := r.obj
  h𝒰 := r.h𝒰
  f := (refinementFiber j T e).app r.W r.f

/-- Helper for Lemma 7.39.2: a request is realized on its own stage if its fiber element lifts
through one member of the chosen finite covering family. -/
def request_realized {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S) : Prop :=
  ∃ i : r.𝒰.index, ∃ y : (fiber.{max u v w} S).obj (r.𝒰.obj i).left,
    (fiber.{max u v w} S).map (r.𝒰.obj i).hom y = r.f

/-- Helper for Lemma 7.39.2: solving a request after refinement is the same as realizing its
transported request on the refined stage. -/
@[simp] theorem request_solved_iff_request_realized_transport
    {S : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S)
    {ι' : Type w} [Preorder ι'] (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) :
    request_solved r T j e ↔ request_realized (transport_request (J := J) j T e r) :=
  Iff.rfl

/-- Helper for Lemma 7.39.2: realization of a lifting request persists after further refinement. -/
theorem request_realized_transport
    {S : ιᵒᵖ ⥤ C} {ι' : Type w} [Preorder ι'] (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C)
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) (r : finite_cover_lift_request J S) :
    request_realized (J := J) r →
      request_realized (J := J) (transport_request (J := J) j T e r) := by
  intro hr
  rcases hr with ⟨i, y, hy⟩
  refine ⟨i, (refinementFiber j T e).app _ y, ?_⟩
  -- Naturality transports the local lifting witness to the refined inverse-system fiber.
  have hnat :
      (fiber.{max u v w} T).map (r.𝒰.obj i).hom ((refinementFiber j T e).app _ y) =
        (refinementFiber j T e).app r.W ((fiber.{max u v w} S).map (r.𝒰.obj i).hom y) := by
    simpa using (congrFun ((refinementFiber j T e).naturality (r.𝒰.obj i).hom) y).symm
  exact hnat.trans (congrArg ((refinementFiber j T e).app r.W) hy)

-- Proof sketch: this is exactly the successor step of the source proof. Package one lifting
-- obligation into `finite_cover_lift_request`, then invoke Lemma 7.39.1 on the current stage.
/-- Helper for Lemma 7.39.2: one application of Lemma 7.39.1 extends the current inverse system
so that the images of the chosen sections stay distinct and the chosen lifting request is solved. -/
theorem stage_extend_by_request
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C] (S : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S).presheafFiber).obj ℱ}
    (hss' : s ≠ s')
    (r : finite_cover_lift_request J S) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        request_solved r T j e := by
  -- Apply the single-request refinement lemma to the packaged covering family and fiber element.
  rcases exists_refined_inverse_system_separating_sections_and_lifting_cover
      (J := J) S hss' r.𝒰 r.h𝒰 r.f with
    ⟨ι', hι', hdir, T, j, e, hsep, hsolve⟩
  refine ⟨ι', hι', hdir, T, j, e, hsep, ?_⟩
  -- The conclusion of Lemma 7.39.1 is exactly the `request_solved` predicate by definition.
  simpa [request_solved] using hsolve

/-- Helper for Lemma 7.39.2: compose two refinement order embeddings. -/
def compose_refinement_embedding
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    (j : ι ↪o ι') (k : ι' ↪o ι'') : ι ↪o ι'' where
  toFun := fun i ↦ k (j i)
  inj' := fun _ _ hij ↦ j.injective (k.injective hij)
  map_rel_iff' := by
    intro i i'
    exact k.map_rel_iff.trans j.map_rel_iff

/-- Helper for Lemma 7.39.2: compose the base refinement with a further refinement of the current
stage. -/
noncomputable def compose_refinement_iso
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U) :
    S ≅ ((compose_refinement_embedding j k).toOrderHom.toFunctor).op ⋙ U := by
  -- The new identification is the old one followed by the refinement of the current stage.
  refine e ≪≫ Functor.isoWhiskerLeft _ e' ≪≫ ?_
  simpa [compose_refinement_embedding] using
    (Functor.associator (j.toOrderHom.toFunctor).op (k.toOrderHom.toFunctor).op U)

namespace GrothendieckTopology.Point.ofIsCofiltered

/-- Helper for Lemma 7.39.2: successive refinements induce the same map on inverse-system fibers
as the composed refinement. -/
theorem refinementFiber_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U) :
    refinementFiber (compose_refinement_embedding j k) U (compose_refinement_iso j k e e') =
      refinementFiber j T e ≫ refinementFiber k U e' := by
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨V, f, rfl⟩
  -- Both sides are determined on the canonical fiber generators `fiberMk f`.
  simp [refinementFiber_app_fiberMk, compose_refinement_iso,
    compose_refinement_embedding, Category.assoc]

end GrothendieckTopology.Point.ofIsCofiltered

/-- Helper for Lemma 7.39.2: transporting one request along two successive refinements is the
same as transporting it directly along the composed refinement. -/
theorem transport_request_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U)
    (r : finite_cover_lift_request J S) :
    transport_request (J := J) (compose_refinement_embedding j k) U
        (compose_refinement_iso j k e e') r =
      transport_request (J := J) k U e' (transport_request (J := J) j T e r) := by
  cases r
  -- Only the transported fiber element changes, and `refinementFiber_comp` identifies it.
  simp [transport_request,
    GrothendieckTopology.Point.ofIsCofiltered.refinementFiber_comp]

/-- Helper for Lemma 7.39.2: on a fixed presheaf, the `presheafFiber` map induced by a composite
refinement is the composite of the two induced maps. -/
theorem refinementFiber_presheafFiber_app_comp
    {ι' ι'' : Type w} [Preorder ι'] [Preorder ι'']
    {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}
    (j : ι ↪o ι') (k : ι' ↪o ι'')
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)
    (e' : T ≅ (k.toOrderHom.toFunctor).op ⋙ U)
    (F : Cᵒᵖ ⥤ Type (max u v w)) :
    ((refinementFiber j T e ≫ refinementFiber k U e').presheafFiber).app F =
      ((refinementFiber j T e).presheafFiber ≫ (refinementFiber k U e').presheafFiber).app F := by
  -- Compare both maps on the generators of the source presheaf fiber.
  apply (fiber.{max u v w} S).presheafFiber_hom_ext
  intro X x
  -- Evaluate both sides on one generator and normalize each step with
  -- `toPresheafFiber_presheafFiber_app`.
  calc
    (fiber.{max u v w} S).toPresheafFiber X x F ≫
        ((refinementFiber j T e ≫ refinementFiber k U e').presheafFiber).app F =
      (fiber.{max u v w} U).toPresheafFiber X
        (((refinementFiber j T e ≫ refinementFiber k U e').app X) x) F := by
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber j T e ≫ refinementFiber k U e') (F := F) X x
    _ =
      (fiber.{max u v w} U).toPresheafFiber X
        ((refinementFiber k U e').app X ((refinementFiber j T e).app X x)) F := by
          rfl
    _ =
      (fiber.{max u v w} T).toPresheafFiber X ((refinementFiber j T e).app X x) F ≫
        ((refinementFiber k U e').presheafFiber).app F := by
          symm
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber k U e') (F := F) X ((refinementFiber j T e).app X x)
    _ =
      (fiber.{max u v w} S).toPresheafFiber X x F ≫
        ((refinementFiber j T e).presheafFiber).app F ≫
          ((refinementFiber k U e').presheafFiber).app F := by
          rw [← Category.assoc]
          congr 1
          symm
          simpa using NatTrans.toPresheafFiber_presheafFiber_app
            (η := refinementFiber j T e) (F := F) X x

/-- Helper for Lemma 7.39.2: the induced map on presheaf fibers is unchanged when the refinement
embedding is identified by equality and the refinement iso is identified by the corresponding
heterogeneous equality. This isolates the dependent transport needed by coherent diagrams of
refinement stages. -/
theorem refinementFiber_presheafFiber_app_heq
    {ι' : Type w} [Preorder ι']
    {S : ιᵒᵖ ⥤ C} (T : ι'ᵒᵖ ⥤ C)
    {j₁ j₂ : ι ↪o ι'}
    (hj : j₁ = j₂)
    {e₁ : S ≅ (j₁.toOrderHom.toFunctor).op ⋙ T}
    {e₂ : S ≅ (j₂.toOrderHom.toFunctor).op ⋙ T}
    (he : HEq e₁ e₂)
    (F : Cᵒᵖ ⥤ Type (max u v w)) :
    ((refinementFiber j₁ T e₁).presheafFiber).app F =
      ((refinementFiber j₂ T e₂).presheafFiber).app F := by
  cases hj
  cases he
  rfl


end

end CategoryTheory

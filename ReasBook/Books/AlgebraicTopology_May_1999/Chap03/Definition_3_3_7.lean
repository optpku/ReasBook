/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_2
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The canonical equivalence on stars induced by a covering functor at an object. -/
noncomputable def starEquiv (hp : Functor.IsCovering p) (e : E) :
    Under e ≃ Under (p.obj e) :=
  Equiv.ofBijective ((Under.post p : Under e ⥤ Under (p.obj e)).obj) (hp.star_bijective e)

/-- The lifted star object over a base arrow starting at a chosen point of the fiber. -/
noncomputable def starLift (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) : Under x.1 :=
  (starEquiv hp x.1).symm (x.2.symm ▸ (Under.mk f : Under b))

/-- Helper for Definition 3.3.7: transporting the base arrow into the corresponding under object
over a chosen fiber point yields the expected `Under.mk` term. -/
lemma fiber_transport_under_mk {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    x.2.symm ▸ (Under.mk f : Under b) = Under.mk (eqToHom x.2 ≫ f) := by
  -- Normalize the fiber witness so the transport becomes the identity transport.
  rcases x with ⟨e, h⟩
  subst h
  simp

/-- Helper for Definition 3.3.7: applying `Under.post p` to the chosen lift recovers the transported
base arrow in the target star. -/
lemma starLift_post_eq (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    (Under.post p).obj (starLift hp f x) = x.2.symm ▸ (Under.mk f : Under b) := by
  -- `starLift` was defined by applying the inverse star equivalence to this transported arrow.
  change (starEquiv hp x.1) (starLift hp f x) = x.2.symm ▸ (Under.mk f : Under b)
  rw [starLift]
  exact (starEquiv hp x.1).apply_symm_apply _

/-- The target of the chosen lifted star object lies over the codomain of the base arrow. -/
-- Proof sketch: apply `(starEquiv hp x.1).apply_symm_apply` to the transported object
-- `Under.mk f`, then read off the equality of right endpoints after transporting along `x.2`.
theorem starLift_obj (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) : p.obj (starLift hp f x).right = b' := by
  -- Reduce to the basepoint case so the transport on the under object disappears.
  rcases x with ⟨e, rfl⟩
  have h := starLift_post_eq hp f ⟨e, rfl⟩
  simp [Under.post] at h
  -- The right endpoint of the lifted star object is the codomain of `f`.
  simpa using congrArg Comma.right h

/-- Helper for Definition 3.3.7: the chosen lift of an identity arrow from a basepoint is the
identity star object. -/
lemma starLift_id_eq (hp : Functor.IsCovering p) (e : E) :
    starLift hp (𝟙 (p.obj e)) ⟨e, rfl⟩ = Under.mk (𝟙 e) := by
  -- Compare the two candidates after applying the injective star map.
  apply (hp.star_bijective e).injective
  calc
    (Under.post p).obj (starLift hp (𝟙 (p.obj e)) ⟨e, rfl⟩) =
        Under.mk (𝟙 (p.obj e)) := by
      simpa using starLift_post_eq hp (𝟙 (p.obj e)) ⟨e, rfl⟩
    _ = (Under.post p).obj (Under.mk (𝟙 e)) := by
      simp [Under.post]

/-- Helper for Definition 3.3.7: the image of the chosen lift under `p` is the original base
arrow, with the source and target adjusted by the fiber witnesses. -/
lemma starLift_hom_over (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    p.map (starLift hp f x).hom =
      eqToHom x.2 ≫ f ≫ eqToHom (starLift_obj hp f x).symm := by
  -- Route correction: expose the hom-level content of `starLift_post_eq` before comparing
  -- composite lifts, so the dependent transport is handled by `conj_eqToHom_iff_heq`.
  have h := starLift_post_eq hp f x
  rw [fiber_transport_under_mk] at h
  -- `Under.mk` equality gives the lifted hom as a heterogeneous copy of the base arrow.
  injection h with _ _ hh
  have hh' : p.map (starLift hp f x).hom ≍ f := by
    simpa using hh
  -- Convert the heterogeneous equality into the explicit `eqToHom`-conjugated formula.
  exact (conj_eqToHom_iff_heq _ _ x.2 (starLift_obj hp f x)).2 hh'

/-- Helper for Definition 3.3.7: postcomposing a morphism in an under category with the
`eqToHom` coming from a codomain equality does not change the corresponding under object. -/
lemma under_mk_comp_eqToHom {X Y Z : B} (m : X ⟶ Y) (h : Y = Z) :
    Under.mk (m ≫ eqToHom h) = Under.mk m := by
  -- Collapse the codomain transport by reducing to the reflexive case.
  cases h
  simp

/-- Helper for Definition 3.3.7: lifting a composite from a basepoint lands at the same endpoint
as first lifting the first arrow and then lifting the second from the intermediate endpoint. -/
lemma starLift_comp_endpoint_eq (hp : Functor.IsCovering p) {e : E} {b₂ b₃ : B}
    (f : p.obj e ⟶ b₂) (g : b₂ ⟶ b₃) :
    (starLift hp (f ≫ g) ⟨e, rfl⟩).right =
      (starLift hp g ⟨(starLift hp f ⟨e, rfl⟩).right, starLift_obj hp f ⟨e, rfl⟩⟩).right := by
  let u := starLift hp f ⟨e, rfl⟩
  let v := starLift hp g ⟨u.right, starLift_obj hp f ⟨e, rfl⟩⟩
  let a : p.obj u.right = b₂ := by
    simpa [u] using starLift_obj hp f ⟨e, rfl⟩
  let b : p.obj v.right = b₃ := by
    simpa [u, v] using starLift_obj hp g ⟨u.right, a⟩
  have hu : p.map u.hom = f ≫ eqToHom a.symm := by
    -- Normalize the first chosen lift to the base arrow `f`.
    simpa [u, a] using starLift_hom_over hp f ⟨e, rfl⟩
  have hv : p.map v.hom = eqToHom a ≫ g ≫ eqToHom b.symm := by
    -- Normalize the second chosen lift to the base arrow `g`.
    simpa [u, v, a, b] using starLift_hom_over hp g ⟨u.right, a⟩
  have hmorph : p.map u.hom ≫ p.map v.hom = f ≫ g ≫ eqToHom b.symm := by
    -- Compose the normalized lifts and cancel the middle transport.
    rw [hu]
    calc
      (f ≫ eqToHom a.symm) ≫ p.map v.hom =
          (f ≫ eqToHom a.symm) ≫ (eqToHom a ≫ g ≫ eqToHom b.symm) := by
        exact congrArg (fun k ↦ (f ≫ eqToHom a.symm) ≫ k) hv
      _ = f ≫ g ≫ eqToHom b.symm := by
        simp [Category.assoc]
  have hpost_explicit : (Under.post p).obj (Under.mk (u.hom ≫ v.hom)) = Under.mk (f ≫ g) := by
    -- The explicit composite lift maps to the same transported under object as `f ≫ g`.
    calc
      (Under.post p).obj (Under.mk (u.hom ≫ v.hom)) =
          Under.mk (p.map u.hom ≫ p.map v.hom) := by
        simp [Under.post]
      _ = Under.mk (f ≫ g ≫ eqToHom b.symm) := by
        exact congrArg Under.mk hmorph
      _ = Under.mk (f ≫ g) := by
        simpa [Category.assoc] using under_mk_comp_eqToHom (f ≫ g) b.symm
  have hpost_lift : (Under.post p).obj (starLift hp (f ≫ g) ⟨e, rfl⟩) = Under.mk (f ≫ g) := by
    -- The chosen lift of `f ≫ g` maps to the same under object by construction.
    simpa using starLift_post_eq hp (f ≫ g) ⟨e, rfl⟩
  have hstar : starLift hp (f ≫ g) ⟨e, rfl⟩ = Under.mk (u.hom ≫ v.hom) := by
    -- Injectivity of the star map identifies the chosen composite lift with the explicit one.
    apply (hp.star_bijective e).injective
    exact hpost_lift.trans hpost_explicit.symm
  -- Project the equality of lifts to their endpoints.
  simpa [u, v] using congrArg Comma.right hstar

/-- Definition 3.3.7: the fiber translation functor of a covering functor sends each object to its
fiber and each morphism to the target map of the unique lifted arrow starting at each point of that
fiber. -/
noncomputable def fiberTranslationFunctor (hp : Functor.IsCovering p) : B ⥤ Type u₁ where
  obj b := p.Fiber b
  map f := TypeCat.ofHom fun x ↦ ⟨(starLift hp f x).right, starLift_obj hp f x⟩
  map_id b := by
    ext x
    rcases x with ⟨e, rfl⟩
    -- The identity arrow lifts to the identity at the chosen basepoint.
    apply Subtype.ext
    simpa using congrArg Comma.right (starLift_id_eq hp e)
  map_comp f g := by
    ext x
    rcases x with ⟨e, rfl⟩
    -- Compare the endpoint of the chosen lift of `f ≫ g` with the endpoint of the explicit
    -- composite lift obtained by first lifting `f` and then `g`.
    apply Subtype.ext
    simpa using starLift_comp_endpoint_eq hp f g

/-- Fiber translation along a base morphism sends a point to the endpoint of its lifted arrow. -/
noncomputable abbrev fiberTranslationMap (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    p.Fiber b → p.Fiber b' :=
  ((fiberTranslationFunctor hp).map f).hom

/-- The canonical vertex-group action on a fiber induced by fiber translation. -/
noncomputable abbrev fiberTranslationMulAction (hp : Functor.IsCovering p) (b : B) :
    MulAction (b ⟶ b) (p.Fiber b) :=
  Functor.vertexGroupAction (fiberTranslationFunctor hp) b

namespace fiberTranslationMulAction

/-- The fiber-translation action is pretransitive. -/
abbrev IsPretransitive (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  MulAction.IsPretransitive (b ⟶ b) (p.Fiber b)

/-- The fiber-translation action is transitive. -/
abbrev IsTransitive (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  MulAction.IsTransitive (b ⟶ b) (p.Fiber b)

/-- The fiber-translation action is free. -/
abbrev IsFree (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  IsCancelSMul (b ⟶ b) (p.Fiber b)

end fiberTranslationMulAction

/-- Fiber translation along an identity arrow is the identity map on the fiber. -/
theorem fiberTranslationMap_id (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMap hp (𝟙 b) = id := by
  funext x
  exact congrArg (fun k ↦ k.hom x) ((fiberTranslationFunctor hp).map_id b)

/-- Fiber translation along a composite is the composite of the corresponding fiber maps. -/
theorem fiberTranslationMap_comp (hp : Functor.IsCovering p) {b₁ b₂ b₃ : B} (f : b₁ ⟶ b₂)
    (g : b₂ ⟶ b₃) :
    fiberTranslationMap hp (f ≫ g) =
      fiberTranslationMap hp g ∘ fiberTranslationMap hp f :=
  by
    funext x
    exact congrArg (fun k ↦ k.hom x) ((fiberTranslationFunctor hp).map_comp f g)

/-- The fiber translation functor sends an object of the base groupoid to its fiber. -/
@[simp] theorem fiberTranslationFunctor_obj (hp : Functor.IsCovering p) (b : B) :
    (fiberTranslationFunctor hp).obj b = p.Fiber b := rfl

/-- The fiber translation functor acts on a morphism by fiber translation along that morphism. -/
@[simp] theorem fiberTranslationFunctor_map (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    (fiberTranslationFunctor hp).map f = TypeCat.ofHom (fiberTranslationMap hp f) := rfl

/-- The fiber translation functor applies to a point of the fiber by the corresponding fiber
translation map. -/
@[simp] theorem fiberTranslationFunctor_map_apply (hp : Functor.IsCovering p) {b b' : B}
    (f : b ⟶ b') (x : p.Fiber b) :
    ((fiberTranslationFunctor hp).map f).hom x = fiberTranslationMap hp f x := rfl

end CategoryTheory.Functor.IsCovering

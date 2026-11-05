module

public import stacks_project.Chap07.Lemma_7_38_3.BasicULift

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: the canonical generator of the point fiber of `uliftYoneda.obj U`. -/
noncomputable abbrev point_uliftYoneda_generator
    (q : Point.{w'} J) (U : C) :
    q.fiber.obj U →
      q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) :=
  fun x ↦
    q.toPresheafFiber U x (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U))

/-- Helper for Lemma 7.38.3: the explicit descent map from the fiber of `uliftYoneda.obj U` back
to the point fiber over `U`. -/
lemma point_uliftYoneda_extract_naturality
    (q : Point.{w'} J) (U : C) {X Y : C} (f : X ⟶ Y) (x : q.fiber.obj X) :
    (CategoryTheory.uliftYoneda.{max u v w'}.obj U).map f.op ≫
      (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
        ULift.up (q.fiber.map (ULift.down z) x)) =
    (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op Y) ↦
      ULift.up (q.fiber.map (ULift.down z) (q.fiber.map f x))) := by
  -- The representable transition map acts by precomposition, so both sides are the same by
  -- functoriality of the point fiber.
  funext z
  simp [CategoryTheory.uliftYoneda]

/-- Helper for Lemma 7.38.3: the extractor family satisfies the compatibility hypothesis needed
for `presheafFiberDesc`. -/
lemma point_uliftYoneda_extract_compatible
    (q : Point.{w'} J) (U : C) :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : q.fiber.obj X),
      (CategoryTheory.uliftYoneda.{max u v w'}.obj U).map f.op ≫
        (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
          ULift.up (q.fiber.map (ULift.down z) x)) =
      (fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op Y) ↦
        ULift.up (q.fiber.map (ULift.down z) (q.fiber.map f x))) := by
  intro X Y f x
  exact point_uliftYoneda_extract_naturality (q := q) U f x

/-- Helper for Lemma 7.38.3: the fiber of `uliftYoneda.obj U` at a point maps back to the lifted
fiber over `U`. -/
noncomputable def point_uliftYoneda_extract
    (q : Point.{w'} J) (U : C) :
    q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ⟶
      ULift (q.fiber.obj U) :=
  q.presheafFiberDesc
    (fun X x ↦
      fun z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ↦
        ULift.up (q.fiber.map (ULift.down z) x))
    (point_uliftYoneda_extract_compatible (q := q) U)

/-- Helper for Lemma 7.38.3: the extractor on the fiber of `uliftYoneda.obj U` evaluates a
canonical generator by composing the represented morphism in the point fiber. -/
lemma point_uliftYoneda_extract_toPresheafFiber
    (q : Point.{w'} J) (U X : C) (x : q.fiber.obj X)
    (z : (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X)) :
    point_uliftYoneda_extract (q := q) U
        (q.toPresheafFiber X x (CategoryTheory.uliftYoneda.{max u v w'}.obj U) z) =
      ULift.up (q.fiber.map (ULift.down z) x) := by
  let φ :
      ∀ (X : C) (_ : q.fiber.obj X),
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op X) ⟶
          ULift (q.fiber.obj U) :=
    fun X x z ↦ ULift.up (q.fiber.map (ULift.down z) x)
  -- Evaluate the universal descent map on the canonical colimit generator.
  have h := congr_fun
    (q.toPresheafFiber_presheafFiberDesc φ
      (point_uliftYoneda_extract_compatible (q := q) U) X x) z
  simpa [point_uliftYoneda_extract, φ] using h

/-- Helper for Lemma 7.38.3: the generators coming from `x ∈ u(U)` are already surjective on the
fiber of `uliftYoneda.obj U`. -/
lemma point_uliftYoneda_generator_surjective
    (q : Point.{w'} J) (U : C) :
    Function.Surjective (point_uliftYoneda_generator (q := q) U) := by
  intro p
  refine ⟨ULift.down (point_uliftYoneda_extract (q := q) U p), ?_⟩
  let φ :
      q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ⟶
        q.presheafFiber.obj (CategoryTheory.uliftYoneda.{max u v w'}.obj U) :=
    fun p ↦
      point_uliftYoneda_generator (q := q) U
        (ULift.down (point_uliftYoneda_extract (q := q) U p))
  have hφ : φ = 𝟙 _ := by
    -- The extractor followed by the generator fixes each colimit generator, so it is the identity.
    apply q.presheafFiber_hom_ext
    intro X x
    ext z
    have hz :=
      point_uliftYoneda_extract_toPresheafFiber (q := q) U X x z
    have hw := congr_fun
      (q.toPresheafFiber_w (ULift.down z) x
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U))
    have hw' :
        q.toPresheafFiber X x (CategoryTheory.uliftYoneda.{max u v w'}.obj U) z =
          q.toPresheafFiber U (q.fiber.map (ULift.down z) x)
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U)
            (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
              ULift.up (𝟙 U)) := by
      simpa [CategoryTheory.uliftYoneda] using hw
    simpa [φ, point_uliftYoneda_generator, hz] using hw'.symm
  simpa [φ] using congr_fun hφ p

/-- Helper for Lemma 7.38.3: a point-fiber element determines the corresponding stalk element of
`h_U^#` at the point. -/
noncomputable def point_sheafifiedRepresentable_stalkElem
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) (U : C) (x : q.fiber.obj U) :
    q.sheafFiber.obj (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U) :=
  q.presheafFiber.map
      (CategoryTheory.toSheafify J
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U))
    (point_uliftYoneda_generator (q := q) U x)

/-- Helper for Lemma 7.38.3: every stalk element of `h_U^#` at a point comes from some
`x ∈ u(U)`. -/
lemma point_sheafifiedRepresentable_stalkElem_surjective
    [HasWeakSheafify J (Type (max u v w'))]
    (q : Point.{w'} J) (U : C) :
    Function.Surjective (point_sheafifiedRepresentable_stalkElem (q := q) U) := by
  -- Route correction: instead of forcing a universe-mismatched stalk/fiber isomorphism, use the
  -- explicit `toSheafify` map and the concrete inverse on the `uliftYoneda` fiber.
  let hbij :
      Function.Bijective
        (q.presheafFiber.map
          (CategoryTheory.toSheafify J
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U))) := by
    exact
      (isIso_iff_bijective
        (q.presheafFiber.map
          (CategoryTheory.toSheafify J
            (CategoryTheory.uliftYoneda.{max u v w'}.obj U)))).1 (by infer_instance)
  intro p
  obtain ⟨y, rfl⟩ := hbij.surjective p
  obtain ⟨x, rfl⟩ := point_uliftYoneda_generator_surjective (q := q) U y
  exact ⟨x, rfl⟩

/-- Helper for Lemma 7.38.3: evaluating a morphism out of `h_U^#` on the canonical stalk element
coming from `x` recovers the corresponding germ. -/
lemma sheafifiedRepresentable_stalk_map_apply
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber.map α)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) =
      q.toPresheafFiber U x ℱ.obj
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
  -- Expand the canonical stalk element through `toSheafify`, then use naturality of
  -- `toPresheafFiber` for the adjunct presheaf morphism `uliftYoneda.obj U ⟶ ℱ.obj`.
  simpa [point_sheafifiedRepresentable_stalkElem,
    CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv] using
    (q.toPresheafFiber_naturality_apply
      (CategoryTheory.toSheafify J
        (CategoryTheory.uliftYoneda.{max u v w'}.obj U) ≫ α.hom)
      U x
      (show (CategoryTheory.uliftYoneda.{max u v w'}.obj U).obj (op U) from
        ULift.up (𝟙 U)))

/-- Helper for Lemma 7.38.3: evaluating two morphisms out of `h_U^#` at the canonical stalk
element from `x` agrees exactly when the corresponding germs agree. -/
lemma sheafifiedRepresentable_stalk_map_eq_iff
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α β : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (x : q.fiber.obj U) :
    (q.sheafFiber.map α)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) =
      (q.sheafFiber.map β)
        (point_sheafifiedRepresentable_stalkElem (q := q) U x) ↔
      q.toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
        q.toPresheafFiber U x ℱ.obj
          (J.uliftSheafifiedRepresentableHomEquiv ℱ U β) := by
  -- Rewrite both sides by the explicit stalk-evaluation formula for the canonical generator.
  constructor
  · intro h
    simpa [sheafifiedRepresentable_stalk_map_apply (q := q) U α x,
      sheafifiedRepresentable_stalk_map_apply (q := q) U β x] using h
  · intro h
    simpa [sheafifiedRepresentable_stalk_map_apply (q := q) U α x,
      sheafifiedRepresentable_stalk_map_apply (q := q) U β x] using h

/-- Helper for Lemma 7.38.3: equality of all germs over `U` forces equality of the induced maps on
the stalk of `h_U^#` at the point. -/
lemma sheafifiedRepresentable_stalk_map_ext_of_pointwise_germ_eq
    [HasWeakSheafify J (Type (max u v w'))]
    {ℱ : Sheaf J (Type (max u v w'))} (q : Point.{w'} J) (U : C)
    (α β : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w', u, v} J U ⟶ ℱ)
    (hαβ :
      ∀ x : q.fiber.obj U,
        q.toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) =
          q.toPresheafFiber U x ℱ.obj
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U β)) :
    q.sheafFiber.map α = q.sheafFiber.map β := by
  -- The canonical generators `x ∈ u(U)` are already surjective on the stalk of `h_U^#`, so it
  -- suffices to compare the two stalk maps on those generators.
  ext p
  obtain ⟨x, rfl⟩ := point_sheafifiedRepresentable_stalkElem_surjective (q := q) U p
  exact (sheafifiedRepresentable_stalk_map_eq_iff (q := q) U α β x).2 (hαβ x)

end GrothendieckTopology

end CategoryTheory

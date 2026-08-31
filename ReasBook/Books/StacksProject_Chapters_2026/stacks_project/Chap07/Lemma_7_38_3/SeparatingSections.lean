module

public import stacks_project.Chap07.Lemma_7_38_3.SheafifiedRepresentableStalk

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: conservativity of the small family already gives joint faithfulness
of the corresponding stalk functors on small set-valued sheaves. -/
lemma small_stalkFamily_jointlyFaithful_small_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C] :
    JointlyFaithful
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type w') ⥤ Type w')) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ ψ hφ
  -- Reindex the owner theorem `hp.jointlyFaithful (Type w')` back along `ofObj p`.
  exact (hp.jointlyFaithful (Type w')).map_injective fun Φ ↦ by
    rcases Φ with ⟨q, hq⟩
    rcases (ofObj_iff p q).1 hq with ⟨i, rfl⟩
    exact hφ i

/-- Helper for Lemma 7.38.3: on small set-valued sheaves, equality on every stalk of the family
forces equality of morphisms. -/
lemma sheaf_hom_ext_of_stalkwise_small_type
    {ι : Type w} (p : ι → Point.{w'} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [LocallySmall.{w'} C]
    {ℱ 𝒢 : Sheaf J (Type w')} {φ ψ : ℱ ⟶ 𝒢}
    (hφ : ∀ i, (p i).sheafFiber.map φ = (p i).sheafFiber.map ψ) :
    φ = ψ := by
  -- Apply the small-target joint faithfulness established just above.
  exact (small_stalkFamily_jointlyFaithful_small_type (p := p) hp).map_injective hφ

/-- Helper for Lemma 7.38.3: if the family separates unequal sections, then the associated stalk
functors on sheaves of sets are jointly faithful. -/
lemma stalkFamily_jointlyFaithful_of_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyFaithful
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 φ ψ hφ
  -- Compare morphisms sectionwise; any unequal section values would be separated by some stalk.
  ext U s
  by_contra hs
  obtain ⟨i, x, hx⟩ := hsep U.unop ((φ.hom.app U) s) ((ψ.hom.app U) s) hs
  let a : CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentable.{w',u,v} J U.unop ⟶ ℱ :=
    (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
      J ℱ U.unop).symm s
  have hi :
      ((p i).sheafFiber.map φ)
          (((p i).sheafFiber.map a)
            (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x)) =
        ((p i).sheafFiber.map ψ)
          (((p i).sheafFiber.map a)
            (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x)) := by
    exact congr_fun (hφ i)
      (((p i).sheafFiber.map a)
        (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x))
  have hi' :
      ((p i).sheafFiber.map (a ≫ φ))
          (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x) =
        ((p i).sheafFiber.map (a ≫ ψ))
          (point_sheafifiedRepresentable_stalkElem (q := p i) U.unop x) := by
    simpa [Functor.map_comp, Category.assoc] using hi
  have hcompφ :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ φ) = φ.hom.app U s := by
    have ha :
        CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a = s := by
      simpa [a] using
        (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J ℱ U.unop).apply_symm_apply s
    calc
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ φ) =
        φ.hom.app U
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a) := by
              simpa using
                (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{w',u,v}
                  J a φ)
      _ = φ.hom.app U s := by rw [ha]
  have hcompψ :
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ ψ) = ψ.hom.app U s := by
    have ha :
        CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a = s := by
      simpa [a] using
        (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J ℱ U.unop).apply_symm_apply s
    calc
      CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
          J 𝒢 U.unop (a ≫ ψ) =
        ψ.hom.app U
          (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{w',u,v}
            J ℱ U.unop a) := by
              simpa using
                (CategoryTheory.GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{w',u,v}
                  J a ψ)
      _ = ψ.hom.app U s := by rw [ha]
  exact hx <| by
    simpa [hcompφ, hcompψ] using
      (sheafifiedRepresentable_stalk_map_eq_iff (q := p i) U.unop (a ≫ φ) (a ≫ ψ) x).1 hi'

/-- Helper for Lemma 7.38.3: the section-separation hypothesis upgrades the large stalk family to a
jointly-reflecting family for isomorphisms of set-valued sheaves. -/
lemma stalkFamily_jointlyReflectsIsomorphisms_of_separating_sections_large
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    JointlyReflectIsomorphisms
      (fun i : ι ↦ ((p i).sheafFiber : Sheaf J (Type (max u v w')) ⥤ Type (max u v w'))) := by
  -- Once the large stalk family is jointly faithful, the balanced category of sheaves upgrades
  -- that to joint reflection of isomorphisms.
  exact CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms
    (stalkFamily_jointlyFaithful_of_separating_sections (p := p) hsep)

/-- Helper for Lemma 7.38.3: for type-valued presheaves, equality of two germs in a point fiber
is witnessed after pulling back along some arrow landing at the chosen point element. -/
lemma point_fiber_eq_iff_of_type
    (q : Point.{w'} J) {P : Cᵒᵖ ⥤ Type w''}
    [Limits.HasColimitsOfSize.{w', w'} (Type w'')]
    (X : C) (x : q.fiber.obj X) (z₁ z₂ : P.obj (op X)) :
    q.toPresheafFiber X x P z₁ = q.toPresheafFiber X x P z₂ ↔
      ∃ (Y : C) (f : Y ⟶ X) (y : q.fiber.obj Y), q.fiber.map f y = x ∧
        P.map f.op z₁ = P.map f.op z₂ := by
  constructor
  · intro h
    -- Equality in the filtered colimit comes from some later stage of the category of elements.
    obtain ⟨j, f, hf⟩ :=
      (Limits.Types.FilteredColimit.isColimit_eq_iff'
        (ht := q.isColimitPresheafFiberCocone P) (i := op ⟨X, x⟩) z₁ z₂).1 h
    exact ⟨j.unop.1, f.unop.val, j.unop.2, f.unop.property, hf⟩
  · rintro ⟨Y, f, y, hy, hEq⟩
    -- Conversely, any common refinement in the category of elements identifies the two germs.
    exact (Limits.Types.FilteredColimit.isColimit_eq_iff'
      (ht := q.isColimitPresheafFiberCocone P) (i := op ⟨X, x⟩) z₁ z₂).2
      ⟨op ⟨Y, y⟩, op (CategoryOfElements.homMk ⟨Y, y⟩ ⟨X, x⟩ f hy), hEq⟩

/-- Helper for Lemma 7.38.3: equality of the germs of two sections at a chosen point element
produces a lift of that point element through the equalizer sieve of the two sections. -/
lemma pointwise_germ_eq_gives_equalizer_lift
    (q : Point.{w'} J) {ℱ : Sheaf J (Type (max u v w'))} (U : C)
    (s s' : ℱ.obj.obj (op U)) {x : q.fiber.obj U}
    (hx : q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s') :
    ∃ (Y : C) (g : Y ⟶ U) (_ : Presheaf.equalizerSieve (F := ℱ.obj) s s' g) (y : q.fiber.obj Y),
      q.fiber.map g y = x := by
  -- Read equality in the filtered colimit as equality after pulling back to a common stage.
  obtain ⟨Y, g, y, hy, hEq⟩ :=
    (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').1 hx
  refine ⟨Y, g, hEq, y, hy⟩

/-- Helper for Lemma 7.38.3: equality of two lifted germs is equivalent to equality of the
original germs before applying `ULift`. -/
lemma point_ulift_presheafFiber_eq_iff
    (q : Point.{w'} J) {ℱ : Sheaf J (Type w')} (U : C) (x : q.fiber.obj U)
    (s s' : ℱ.obj.obj (op U)) :
    q.toPresheafFiber U x
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj
        (show
          (((sheafCompose J
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
            from ULift.up.{max u v, w'} s) =
      q.toPresheafFiber U x
        ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj
        (show
          (((sheafCompose J
            (CategoryTheory.uliftFunctor.{max u v, w'} :
              Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
            from ULift.up.{max u v, w'} s') ↔
      q.toPresheafFiber U x ℱ.obj s = q.toPresheafFiber U x ℱ.obj s' := by
  constructor
  · intro h
    -- The lifted equality is witnessed after pullback at some stage; drop `ULift` there.
    obtain ⟨Y, f, y, hy, hEq⟩ :=
      (point_fiber_eq_iff_of_type
        (q := q)
        (P := ((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj)
        U x _ _).1 h
    exact (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').2
      ⟨Y, f, y, hy, by simpa [CategoryTheory.uliftFunctor_map] using hEq⟩
  · intro h
    -- Any witness for the original equality also witnesses the lifted equality after `ULift`.
    obtain ⟨Y, f, y, hy, hEq⟩ :=
      (point_fiber_eq_iff_of_type (q := q) (P := ℱ.obj) U x s s').1 h
    exact (point_fiber_eq_iff_of_type
      (q := q)
      (P := ((sheafCompose J
        (CategoryTheory.uliftFunctor.{max u v, w'} :
          Type w' ⥤ Type (max u v w'))).obj ℱ).obj)
      U x _ _).2
      ⟨Y, f, y, hy, by simpa [CategoryTheory.uliftFunctor_map] using hEq⟩

/-- Helper for Lemma 7.38.3: the large separating-sections hypothesis immediately yields the same
separation property for small type-valued sheaves. -/
lemma small_separating_sections_of_large
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s') :
    ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
      s ≠ s' →
        ∃ i : ι, ∃ x : (p i).fiber.obj U,
          (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s' := by
  intro ℱ U s s' hs
  -- Apply the large hypothesis to the `ULift`-whiskered sheaf and then remove `ULift` from the
  -- resulting germ inequality.
  obtain ⟨i, x, hx⟩ :=
    hsep
      (ℱ := (sheafCompose J
        (CategoryTheory.uliftFunctor.{max u v, w'} :
          Type w' ⥤ Type (max u v w'))).obj ℱ)
      U
      (show
        (((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
          from ULift.up.{max u v, w'} s)
      (show
        (((sheafCompose J
          (CategoryTheory.uliftFunctor.{max u v, w'} :
            Type w' ⥤ Type (max u v w'))).obj ℱ).obj).obj (op U)
          from ULift.up.{max u v, w'} s') <| by
        intro hEq
        exact hs <| by simpa using hEq
  refine ⟨i, x, ?_⟩
  intro hEq
  apply hx
  exact (point_ulift_presheafFiber_eq_iff (q := p i) U x s s').2 hEq

/-- Helper for Lemma 7.38.3: once unequal sections are separated by some germ, stalkwise
isomorphisms force a morphism of small set-valued sheaves to be mono. -/
lemma sheaf_mono_of_stalkwise_isIso_of_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J)
    (hsep :
      ∀ ⦃ℱ : Sheaf J (Type w')⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s')
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    Mono φ := by
  rw [← Sheaf.isLocallyInjective_iff_mono]
  rw [Sheaf.isLocallyInjective_iff_injective]
  intro U s s' hs
  by_contra hss
  obtain ⟨i, x, hx⟩ := hsep U.unop s s' hss
  have hEq :
      ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
        ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s') := by
    -- Naturality converts equality of sections after `φ` into equality of their germs.
    have hLeft :
        ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s) =
          (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s) := by
      simpa using congrFun ((p i).toPresheafFiber_naturality φ.hom U.unop x) s
    have hMid :
        (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s) =
          (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s') := by
      simpa using congrArg ((p i).toPresheafFiber U.unop x 𝒢.obj) hs
    have hRight :
        (p i).toPresheafFiber U.unop x 𝒢.obj ((φ.hom.app U) s') =
          ((p i).sheafFiber.map φ) ((p i).toPresheafFiber U.unop x ℱ.obj s') := by
      symm
      simpa using congrFun ((p i).toPresheafFiber_naturality φ.hom U.unop x) s'
    exact hLeft.trans (hMid.trans hRight)
  have hinj : Function.Injective ((p i).sheafFiber.map φ) := by
    exact (isIso_iff_bijective ((p i).sheafFiber.map φ)).1 (hφ i) |>.injective
  exact hx (hinj hEq)

/-- Helper for Lemma 7.38.3: if all stalk maps of `φ` are isomorphisms, then the same is true for
the stalk maps of the pushout coprojection `pushout.inl φ φ`. -/
lemma sheafFiber_map_pushoutInl_isIso_of_stalkwise_isIso
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢) [HasPushout φ φ]
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    ∀ i : ι, IsIso ((p i).sheafFiber.map (pushout.inl φ φ)) := by
  intro i
  -- Map the actual pushout cocone of `φ` through the stalk functor.
  let _ : PreservesColimit (span φ φ) (p i).sheafFiber := by
    infer_instance
  let hc := isColimitOfHasPushoutOfPreservesColimit ((p i).sheafFiber) φ φ
  -- Since the mapped stalk map is an isomorphism, it is in particular an epimorphism.
  let _ : IsIso ((p i).sheafFiber.map φ) := hφ i
  have hEpi : Epi ((p i).sheafFiber.map φ) := by
    infer_instance
  -- The universal pushout criterion identifies this epi with invertibility of `pushout.inl`.
  exact (epi_iff_isIso_inl hc).1 hEpi

/-- Helper for Lemma 7.38.3: if all stalk maps of `φ` are isomorphisms, then the same is true for
the stalk maps of its pushout codiagonal. -/
lemma stalkwise_isIso_codiagonal_of_stalkwise_isIso
    {ι : Type w} (p : ι → Point.{w'} J)
    {ℱ 𝒢 : Sheaf J (Type w')} (φ : ℱ ⟶ 𝒢) [HasPushout φ φ]
    (hφ : ∀ i : ι, IsIso ((p i).sheafFiber.map φ)) :
    ∀ i : ι, IsIso ((p i).sheafFiber.map (pushout.codiagonal φ)) := by
  intro i
  -- First make the mapped coprojection invertible by the mapped pushout cocone criterion.
  let _ : IsIso ((p i).sheafFiber.map (pushout.inl φ φ)) :=
    sheafFiber_map_pushoutInl_isIso_of_stalkwise_isIso (p := p) (φ := φ) hφ i
  have hcomp :
      (p i).sheafFiber.map (pushout.inl φ φ) ≫
          (p i).sheafFiber.map (pushout.codiagonal φ) =
        𝟙 _ := by
    -- The codiagonal is a right inverse to `pushout.inl`, and this identity survives under any
    -- functor.
    calc
      (p i).sheafFiber.map (pushout.inl φ φ) ≫
          (p i).sheafFiber.map (pushout.codiagonal φ) =
        (p i).sheafFiber.map (pushout.inl φ φ ≫ pushout.codiagonal φ) := by
          rw [Functor.map_comp]
      _ = (p i).sheafFiber.map (𝟙 _) := by
        rw [pushout.inl_codiagonal]
      _ = 𝟙 _ := by
        simp
  have hcod :
      (p i).sheafFiber.map (pushout.codiagonal φ) =
        inv ((p i).sheafFiber.map (pushout.inl φ φ)) := by
    -- An isomorphism is determined by its right inverse, so the mapped codiagonal is the inverse
    -- of the mapped coprojection.
    calc
      (p i).sheafFiber.map (pushout.codiagonal φ) =
          𝟙 _ ≫ (p i).sheafFiber.map (pushout.codiagonal φ) := by
            simp
      _ = inv ((p i).sheafFiber.map (pushout.inl φ φ)) ≫
            ((p i).sheafFiber.map (pushout.inl φ φ) ≫
              (p i).sheafFiber.map (pushout.codiagonal φ)) := by
            simp
      _ = inv ((p i).sheafFiber.map (pushout.inl φ φ)) := by
            simp [hcomp]
  rw [hcod]
  exact inferInstanceAs (IsIso (inv ((p i).sheafFiber.map (pushout.inl φ φ))))

end GrothendieckTopology

end CategoryTheory

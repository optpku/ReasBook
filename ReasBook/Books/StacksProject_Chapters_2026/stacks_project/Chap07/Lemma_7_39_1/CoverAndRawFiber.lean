module

public import stacks_project.Chap07.Lemma_7_39_1.RefinementFiber

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered
open CategoryTheory.SemiRepresentableFamily.Over

variable (J)

/-- Helper for Lemma 7.39.1: pulling back a fixed-target covering family along a stage map again
gives a covering family in the site. -/
theorem pullback_covering_family_mem
    [HasPullbacks C] {U W : C} (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (f : U ⟶ W) :
    Sieve.ofArrows (fun k : 𝒰.index ↦ pullback (𝒰.obj k).hom f)
        (fun k : 𝒰.index ↦
          (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f)) ∈ J U := by
  -- Identify the branch family with the sieve-theoretic pullback of the original covering family.
  rw [Sieve.ofArrows_eq_pullback_of_isPullback
    (f := fun k : 𝒰.index ↦ (𝒰.obj k).hom)
    (g := f)
    (P := fun k : 𝒰.index ↦ pullback (𝒰.obj k).hom f)
    (p₁ := fun k : 𝒰.index ↦
      (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f))
    (p₂ := fun k : 𝒰.index ↦
      (show pullback (𝒰.obj k).hom f ⟶ (𝒰.obj k).left from pullback.fst (𝒰.obj k).hom f))]
  · simpa [SemiRepresentableFamily.Over.toSieve, SemiRepresentableFamily.Over.toPresieve] using
      J.pullback_stable f h𝒰
  · intro k
    -- Each branch square is the canonical pullback square.
    simpa using (IsPullback.of_isLimit (pullbackIsPullback (𝒰.obj k).hom f)).flip

/-- Helper for Lemma 7.39.1: separatedness on the pulled-back covering family makes the stagewise
restriction map into the branch family injective. -/
theorem stage_pullback_cover_restriction_injective
    [HasPullbacks C] {U W : C} (𝒰 : SemiRepresentableFamily.Over W)
    (h𝒰 : 𝒰.toSieve ∈ J W) (ℱ : Sheaf J (Type (max u v w))) (f : U ⟶ W) :
    Function.Injective
      (fun t : ℱ.obj.obj (op U) ↦
        fun k : 𝒰.index ↦
          ℱ.obj.map
            (show (pullback (𝒰.obj k).hom f ⟶ U) from pullback.snd (𝒰.obj k).hom f).op t) := by
  intro s t hst
  -- Use the source proof's local separatedness step on the pullback cover itself.
  have hconst :
      (fun _ : PUnit ↦ s) = (fun _ : PUnit ↦ t) := by
    apply ℱ.property.hom_ext_ofArrows
      (f := fun k : 𝒰.index ↦
        (show pullback (𝒰.obj k).hom f ⟶ U from pullback.snd (𝒰.obj k).hom f))
      (hf := pullback_covering_family_mem (J := J) 𝒰 h𝒰 f)
    intro k
    funext _
    exact congrFun hst k
  exact congrFun hconst PUnit.unit

/-- Helper for Lemma 7.39.1: two distinct points of a finite product already differ on one
coordinate. -/
theorem exists_ne_coordinate_of_ne_fun
    {α : Type*} [Finite α] {β : α → Sort*} {x y : ∀ a, β a}
    (hxy : x ≠ y) :
    ∃ a : α, x a ≠ y a := by
  classical
  -- If every coordinate agreed, function extensionality would force equality.
  by_contra h
  apply hxy
  funext a
  by_contra hne
  exact h ⟨a, hne⟩

/-- Helper for Lemma 7.39.1: an injective map into a finite product sends distinct points to
tuples differing on some coordinate. -/
theorem exists_ne_coordinate_of_injective_map
    {α : Type*} [Finite α] {X : Sort*} {β : α → Sort*}
    (g : X → ∀ a, β a) {x y : X} (hxy : x ≠ y) (hg : Function.Injective g) :
    ∃ a : α, g x a ≠ g y a := by
  -- After applying the injective map, the two product-valued images are still distinct.
  apply exists_ne_coordinate_of_ne_fun
  intro hEq
  apply hxy
  exact hg hEq

/-- Helper for Lemma 7.39.1: once the inverse-system index is nonempty, two elements of the raw
presheaf fiber over `fiber S` admit a common presentation over one object of the category of
elements of `fiber S`. -/
theorem inverse_system_presheafFiber_jointly_surjective₂
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C)
    {F : Cᵒᵖ ⥤ Type (max u v w)}
    (x y : (fiber.{max u v w} S).presheafFiber.obj F) :
    ∃ (X : C) (u : (fiber.{max u v w} S).obj X) (z z' : F.obj (op X)),
      (fiber.{max u v w} S).toPresheafFiber X u F z = x ∧
      (fiber.{max u v w} S).toPresheafFiber X u F z' = y := by
  let _ : Nonempty (ιᵒᵖ) := Opposite.instNonempty
  let _ : IsCofiltered (ιᵒᵖ) := by
    infer_instance
  -- The raw presheaf fiber is a filtered colimit over the category of elements of `fiber S`.
  obtain ⟨⟨X, u⟩, z, z', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit
        ((CategoryTheory.CategoryOfElements.π (fiber.{max u v w} S)).op ⋙ F))
      x y
  exact ⟨X, u, z, z', rfl, rfl⟩

/-- Helper for Lemma 7.39.1: a natural transformation of filtered diagrams in `Type` whose
components are injective induces an injective map on colimits. -/
theorem colimit_map_injective_of_app_injective
    {I : Type w} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ Type (max u v w)} (η : F ⟶ G)
    (hη : ∀ i, Function.Injective (η.app i)) :
    Function.Injective (colim.map η) := by
  intro x y hxy
  obtain ⟨i, x', y', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit F) x y
  have hxy' :
      colimit.ι G i (η.app i x') = colimit.ι G i (η.app i y') := by
    simpa using hxy
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (F := G) (colimit.isColimit G)
      (η.app i x') (η.app i y')).1 hxy'
  have hf' : η.app j (F.map f x') = η.app j (F.map f y') := by
    have hnatx : η.app j (F.map f x') = G.map f (η.app i x') := by
      simpa using congrFun (η.naturality f) x'
    have hnaty : η.app j (F.map f y') = G.map f (η.app i y') := by
      simpa using congrFun (η.naturality f) y'
    exact hnatx.trans (hf.trans hnaty.symm)
  apply Types.colimit_sound' f f
  exact hη j hf'

/-- Helper for Lemma 7.39.1: for a directed inverse system, the raw presheaf fiber is the colimit
of the stagewise section diagram over the index category itself. -/
noncomputable def inverse_system_presheafFiberCocone
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    Cocone (S.op ⋙ F) where
  pt := (fiber.{max u v w} S).presheafFiber.obj F
  ι :=
    { app := fun i ↦
        (fiber.{max u v w} S).toPresheafFiber (S.obj (unop i))
          (fiberMk.{max u v w} (𝟙 (S.obj (unop i)))) F
      naturality := by
        intro i j f
        have hmap :
            (fiber.{max u v w} S).map (S.map f.unop)
                (fiberMk.{max u v w} (𝟙 (S.obj (unop j)))) =
              fiberMk.{max u v w} (𝟙 (S.obj (unop i))) := by
          simp
        simpa [Functor.comp_map, hmap] using
          (fiber.{max u v w} S).toPresheafFiber_w
            (F := F) (S.map f.unop)
            (fiberMk.{max u v w} (𝟙 (S.obj (unop j)))) }

/-- Helper for Lemma 7.39.1: the cocone indexed by the original directed preorder computes the raw
presheaf fiber of the associated inverse-system fiber functor. -/
noncomputable def inverse_system_presheafFiber_isColimit
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (S : ιᵒᵖ ⥤ C) (F : Cᵒᵖ ⥤ Type (max u v w)) :
    IsColimit (inverse_system_presheafFiberCocone (S := S) F) := by
  let _ : Nonempty (ιᵒᵖ) := Opposite.instNonempty
  let _ : IsCofiltered (ιᵒᵖ) := by
    infer_instance
  simpa [inverse_system_presheafFiberCocone, Functor.presheafFiber, Functor.toPresheafFiber] using
    (Functor.Final.isColimitWhiskerEquiv
      (GrothendieckTopology.Point.ofIsCofiltered.functor.{max u v w} (p := S)).op
      (colimit.cocone (((CategoryTheory.CategoryOfElements.π
        (fiber.{max u v w} S)).op) ⋙ F))).2
      (colimit.isColimit (((CategoryTheory.CategoryOfElements.π
        (fiber.{max u v w} S)).op) ⋙ F))

end

end CategoryTheory

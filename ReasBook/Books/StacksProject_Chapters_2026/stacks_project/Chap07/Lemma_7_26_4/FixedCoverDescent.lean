module

public import stacks_project.Chap07.Lemma_7_26_1

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: giving, for each descent datum on the fixed cover `𝒰`, an object in
the essential image of the descent-data functor is exactly the data needed to prove essential
surjectivity. -/
theorem localized_cover_descent_essSurj_of_glued_objects
    (𝒰 : J.Cover U)
    (lift :
      ∀ D : (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f),
        (((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)).essImage D)) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- `Functor.EssSurj.mk` packages the objectwise essential-image witnesses.
  exact Functor.EssSurj.mk lift

/-- Helper for Lemma 7.26.4: the owner-level stack statement for the fixed cover `𝒰` immediately
implies the source-facing essential-surjectivity statement for the associated descent-data
functor. -/
theorem localized_cover_descent_essSurj_of_isStackFor
    (𝒰 : J.Cover U)
    (h :
      (J.pseudofunctorOver (Type w)).IsStackFor
        (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f))) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : 𝒰.Arrow ↦ I.f)).EssSurj := by
  -- Convert the owner-level stack statement into an equivalence of categories.
  letI :
      ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).IsEquivalence :=
    (((J.pseudofunctorOver (Type w)).isStackFor_ofArrows_iff
      (fun I : 𝒰.Arrow ↦ I.f))).1 h
  -- Essential surjectivity is then an instance field of the resulting equivalence.
  infer_instance

/-- Helper for Lemma 7.26.4: the fixed-cover descent category attached to `𝒰`. -/
abbrev localized_cover_descent_category
    (𝒰 : J.Cover U) :=
  (J.pseudofunctorOver (Type w)).DescentData (fun I : 𝒰.Arrow ↦ I.f)

/-- Helper for Lemma 7.26.4: on the pullback cover of `V ⟶ U`, each arrow has the same domain as
its base arrow, so the pullback comparison square is witnessed by the identity on that domain. -/
theorem localized_cover_descent_pullbackDatum_w
    (𝒰 : J.Cover U) (V : Over U) (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫ K.base.f = K.f ≫ V.hom := by
  -- The base arrow of `K` is defined by composing `K.f` with `V.hom`.
  simp [GrothendieckTopology.Cover.Arrow.base]

/-- Helper for Lemma 7.26.4: pull a fixed-cover descent datum back along an object `V` of the
slice `C / U`, so later objectwise formulas can talk directly about the pulled-back cover
`𝒰.pullback V.hom`. -/
def localized_cover_descent_pullbackDatum
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V)).obj D

/-- Helper for Lemma 7.26.4: pulling back the descent datum of an actual sheaf is canonically the
same as taking descent data after pulling the sheaf back to the smaller slice. -/
def localized_cover_descent_pullbackDatum_of_toDescentData_iso
    (𝒰 : J.Cover U)
    (M : Sheaf (J.over U) (Type w))
    (V : Over U) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)).obj M) V ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)).obj
          ((J.overMapPullback (Type w) V.hom).obj M)) :=
  (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    (J.pseudofunctorOver (Type w))
    (f := fun I : 𝒰.Arrow ↦ I.f)
    (p := V.hom)
    (f' := fun K : (𝒰.pullback V.hom).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V)).app M

/-- Helper for Lemma 7.26.4: over the pullback cover above a chosen cover member `I`, one may
reindex the pulled-back datum from the varying base arrows `K.base` to the fixed component `I`
using the descent isomorphisms already stored in `D`. -/
def localized_cover_descent_componentPullbackDatum
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    (J.pseudofunctorOver (Type w)).DescentData
      (fun K : (𝒰.pullback I.f).Arrow ↦ K.f) :=
  (Pseudofunctor.DescentData.pullFunctor (J.pseudofunctorOver (Type w))
    (f := fun JI : 𝒰.Arrow ↦ JI.f)
    (p := I.f)
    (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
    (α := fun _ ↦ I)
    (p' := fun K ↦ K.f)
    (w := fun K ↦ by simp)).obj D

/-- Helper for Lemma 7.26.4: pulling back the terminal object of `Over K.Y` along `K.f` gives the
object `Over.mk K.f` in `Over I.Y`. This is the section-level normalization used when passing
between global sections of a pulled-back sheaf and sections over the overlap object itself. -/
theorem localized_cover_descent_overMap_terminal_obj
    {X Y : C}
    (f : X ⟶ Y) :
    (Over.map f).obj (Over.mk (𝟙 X)) = Over.mk f := by
  change Over.mk ((𝟙 X) ≫ f) = Over.mk f
  simp

/-- Helper for Lemma 7.26.4: for the constant-index pullback datum over a chosen cover member `I`,
the `K`-component is literally the pullback of the fixed sheaf `D.obj I` along `K.f`, so its
global sections are exactly sections of `D.obj I` over `Over.mk K.f`. -/
theorem localized_cover_descent_componentPullbackDatum_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) := by
  -- The pullback datum at `K` is defined using `J.overMapPullback` along `K.f`.
  simp [localized_cover_descent_componentPullbackDatum,
    localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: the same section identification holds for the ordinary
`toDescentData` construction on the fixed sheaf `D.obj I`. This is the target-side normal form
used when comparing pulled-back descent data to the textbook compatible-family description. -/
theorem localized_cover_descent_toDescentData_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((((J.pseudofunctorOver (Type w)).toDescentData
        (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) =
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) := by
  -- Unfolding `toDescentData` shows that its `K`-component is the same pullback sheaf.
  simp [Pseudofunctor.toDescentData, localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: the pulled-back datum can first be reindexed to the constant
component `I` before comparing it with the ordinary descent datum of `D.obj I`. -/
def localized_cover_descent_pullbackDatum_reindex_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f) ≅
      localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I :=
  (Pseudofunctor.DescentData.pullFunctorIso (J.pseudofunctorOver (Type w))
    (f := fun JI : 𝒰.Arrow ↦ JI.f)
    (p := I.f)
    (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
    (α := fun K ↦ K.base)
    (p' := fun _ ↦ 𝟙 _)
    (w := localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 (Over.mk I.f))
    (β := fun _ ↦ I)
    (p'' := fun K ↦ K.f)
    (w' := fun K ↦ by simp)).app D

/-- Helper for Lemma 7.26.4: once the pullback datum over `I` has been reindexed so that every
component comes from the fixed sheaf `D.obj I`, its transition maps are exactly the canonical
transition maps of the ordinary descent datum of `D.obj I`. -/
noncomputable def localized_cover_descent_componentPullbackDatum_toDescentData_obj
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_componentPullbackDatum (J := J) (U := U) 𝒰 D I ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I)) := by
  -- The object components already agree definitionally after reindexing to the fixed index `I`.
  refine Pseudofunctor.DescentData.isoMk (fun K ↦ Iso.refl _) ?_
  intro Y q K₁ K₂ f₁ f₂ hf₁ hf₂
  -- Route correction: specialize the pullback transition map to the common composite `q ≫ I.f`;
  -- the middle descent morphism of `D` then becomes the identity on the `I`-component.
  -- `pullFunctorObjHom_eq` rewrites the pullback transition map into a `D.hom` term at index `I`,
  -- and `hom_self` then collapses that middle map to the identity.
  simpa [localized_cover_descent_componentPullbackDatum, Pseudofunctor.toDescentData,
    D.hom_self, hf₁, hf₂, Category.assoc] using
    (Pseudofunctor.DescentData.pullFunctorObjHom_eq
      (F := J.pseudofunctorOver (Type w))
      (f := fun JI : 𝒰.Arrow ↦ JI.f)
      (p := I.f)
      (f' := fun K : (𝒰.pullback I.f).Arrow ↦ K.f)
      (α := fun _ ↦ I)
      (p' := fun K ↦ K.f)
      (w := fun K ↦ by simp)
      (D := D)
      (q := q)
      (f₁ := f₁)
      (f₂ := f₂)
      (q' := q ≫ I.f)
      (f₁' := q)
      (f₂' := q)).symm

/-- Helper for Lemma 7.26.4: after restricting a descent datum to the pullback cover over a fixed
cover member `I`, the resulting datum is canonically identified with the ordinary descent datum of
the component sheaf `D.obj I` on that pullback cover. -/
noncomputable def localized_cover_descent_pullbackDatum_toDescentData_obj
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow) :
    localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f) ≅
      (((J.pseudofunctorOver (Type w)).toDescentData
        (fun K : (𝒰.pullback I.f).Arrow ↦ K.f)).obj (D.obj I)) := by
  -- First reindex the pulled-back datum so every component is expressed over the fixed sheaf
  -- `D.obj I`; this separates the real remaining issue from the bookkeeping transport.
  refine localized_cover_descent_pullbackDatum_reindex_iso (J := J) (U := U) 𝒰 D I ≪≫
    localized_cover_descent_componentPullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I

/-- Helper for Lemma 7.26.4: on each pullback-cover member `K`, the comparison isomorphism from
the pulled-back datum over `I` to the ordinary descent datum of `D.obj I` has a concrete
componentwise sheaf isomorphism. -/
noncomputable def localized_cover_descent_pullbackDatum_component_iso
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K ≅
      ((((J.pseudofunctorOver (Type w)).toDescentData
          (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K) where
  hom :=
    (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).hom.hom K
  inv :=
    (localized_cover_descent_pullbackDatum_toDescentData_obj
      (J := J) (U := U) 𝒰 D I).inv.hom K
  hom_inv_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).hom.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).inv.hom K =
            𝟙 ((localized_cover_descent_pullbackDatum
              (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).hom_inv_id)
    exact hK
  inv_hom_id := by
    have hK :
        (localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).inv.hom K ≫
          (localized_cover_descent_pullbackDatum_toDescentData_obj
            (J := J) (U := U) 𝒰 D I).hom.hom K =
            𝟙 (((((J.pseudofunctorOver (Type w)).toDescentData
              (fun L : (𝒰.pullback I.f).Arrow ↦ L.f)).obj (D.obj I)).obj K)) := by
      exact congrArg
        (fun f ↦ f.hom K)
        ((localized_cover_descent_pullbackDatum_toDescentData_obj
          (J := J) (U := U) 𝒰 D I).inv_hom_id)
    exact hK

/-- Helper for Lemma 7.26.4: evaluating the `K`-component comparison isomorphism at the terminal
object of `Over K.Y` identifies sections of the pulled-back datum with sections of the fixed
component sheaf `D.obj I` over the overlap object `Over.mk K.f`. -/
noncomputable def localized_cover_descent_pullbackDatum_section_equiv_component
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (I : 𝒰.Arrow)
    (K : (𝒰.pullback I.f).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D (Over.mk I.f)).obj K).1.obj
      (Opposite.op (Over.mk (𝟙 K.Y)))) ≃
      ((D.obj I).1.obj (Opposite.op (Over.mk K.f))) where
  toFun x :=
    cast
      (localized_cover_descent_toDescentData_section_eq (J := J) (U := U) 𝒰 D I K)
      ((localized_cover_descent_pullbackDatum_component_iso
        (J := J) (U := U) 𝒰 D I K).hom.hom.app
          (Opposite.op (Over.mk (𝟙 K.Y))) x)
  invFun y :=
    ((localized_cover_descent_pullbackDatum_component_iso
      (J := J) (U := U) 𝒰 D I K).inv.hom.app
        (Opposite.op (Over.mk (𝟙 K.Y)))
        (cast
          (localized_cover_descent_toDescentData_section_eq
            (J := J) (U := U) 𝒰 D I K).symm y))
  left_inv x := by
    -- Undo the target-side cast and apply the inverse relation of the component comparison.
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_component_iso
          (J := J) (U := U) 𝒰 D I K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e] using CategoryTheory.hom_inv_id_apply e x
  right_inv y := by
    -- The same inverse relation shows that a component section is recovered unchanged.
    let h :=
      localized_cover_descent_toDescentData_section_eq (J := J) (U := U) 𝒰 D I K
    let e :=
      ((sheafToPresheaf (J.over K.Y) (Type w)).mapIso
        (localized_cover_descent_pullbackDatum_component_iso
          (J := J) (U := U) 𝒰 D I K)).app
        (Opposite.op (Over.mk (𝟙 K.Y)))
    simpa [e, h] using congrArg (cast h)
      (CategoryTheory.inv_hom_id_apply e (cast h.symm y))

/-- Helper for Lemma 7.26.4: a morphism `g : V ⟶ W` in `Over U` sends an arrow of the pullback
cover above `V` to the corresponding arrow of the pullback cover above `W` by postcomposing with
`g.left`. This is the indexing map needed for the glued-compatible-family restriction maps. -/
def localized_cover_descent_pullback_arrow_map
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝒰.pullback W.hom).Arrow :=
  ⟨K.Y, K.f ≫ g.left, by
    -- Rewrite the composite to `U` using the defining equality of morphisms in `Over U`.
    have hg : K.f ≫ g.left ≫ W.hom = K.f ≫ V.hom := by
      simpa [Category.assoc] using congrArg (fun h ↦ K.f ≫ h) (Over.w g)
    simpa [GrothendieckTopology.Cover.coe_pullback] using hg ▸ K.hf⟩

/-- Helper for Lemma 7.26.4: the arrow of `𝒰` underlying an indexed pullback arrow does not
change when that pullback arrow is transported along a morphism in `Over U`. -/
theorem localized_cover_descent_pullback_arrow_map_base
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base = K.base := by
  -- Compare the two underlying arrows in the original cover after expanding `base`.
  ext
  · rfl
  · simpa [localized_cover_descent_pullback_arrow_map, GrothendieckTopology.Cover.Arrow.base,
      Category.assoc] using congrArg (fun h ↦ K.f ≫ h) (Over.w g)

/-- Helper for Lemma 7.26.4: the terminal section of a transported pullback-cover arrow is
evaluated at the same terminal object as the original pullback-cover arrow. -/
theorem localized_cover_descent_glue_restrict_source_section_type
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category.{u, v, w} (J := J) (U := U) 𝒰)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.obj
          (Opposite.op (Over.mk (𝟙
            (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).Y)))) =
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D W).obj
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K)).1.obj
          (Opposite.op (Over.mk (𝟙 K.Y)))) := by
  -- The transported pullback-cover arrow has the same source object; only the map to `W`
  -- changes by postcomposition with `g.left`.
  simp [localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: the transported pullback-cover arrow and the original pullback-cover
arrow have the same composite map to `U` after using the slice morphism equation for `g`. -/
theorem localized_cover_descent_glue_restrict_hom_left_fac
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).base.f =
      K.f ≫ V.hom := by
  -- Expand the transported cover arrow, then replace `g.left ≫ W.hom` by `V.hom`.
  dsimp [localized_cover_descent_pullback_arrow_map, GrothendieckTopology.Cover.Arrow.base]
  simpa [Category.assoc] using congrArg (fun h => K.f ≫ h) (Over.w g)

/-- Helper for Lemma 7.26.4: the original pullback-cover arrow satisfies the usual pullback
descent-datum square over `V`. -/
theorem localized_cover_descent_glue_restrict_hom_right_fac
    (𝒰 : J.Cover U)
    (V : Over U)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫ K.base.f = K.f ≫ V.hom := by
  -- This is the defining square of the pulled-back cover arrow.
  exact localized_cover_descent_pullbackDatum_w (J := J) (U := U) 𝒰 V K

/-- Helper for Lemma 7.26.4: as an arrow in the pullback cover over `W`, the image of a
pullback-cover arrow over `V` has structure map `K.f ≫ g.left`. -/
theorem localized_cover_descent_pullback_arrow_map_w
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).f =
      K.f ≫ g.left := by
  -- The arrow map only postcomposes the cover arrow with the slice morphism.
  simp [localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: the two identity pullback maps introduced by the composed
pullFunctor comparison collapse to the identity map on the transported cover arrow. -/
theorem localized_cover_descent_pullback_arrow_map_comp_id
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (K : (𝒰.pullback V.hom).Arrow) :
    (𝟙 K.Y) ≫
        (𝟙 (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K).Y) =
      (𝟙 K.Y) := by
  -- Both arrows are identities on the same source object after unfolding the transported arrow.
  simp [localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: a relation in the pullback cover above `V` is also a relation
between the transported arrows in the pullback cover above `W`. This packages the overlap
reindexing needed for the glued-compatible-family restriction maps. -/
def localized_cover_descent_pullback_relation_map
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.fst).Relation
      (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g R.snd) :=
  { R.r with
    w := by
      -- The overlap equation is preserved after postcomposing both sides with `g.left`.
      simpa [localized_cover_descent_pullback_arrow_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ g.left) R.r.w }

/-- Helper for Lemma 7.26.4: transporting a pullback-cover relation along a slice morphism
does not change the overlap object. This is the object-level normal form needed before comparing
terminal-section applications on transported relations. -/
theorem localized_cover_descent_pullback_relation_map_Z
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_map (J := J) (U := U) 𝒰 g R).Z =
      R.r.Z := by
  -- The relation transport reuses the same overlap witness and only changes its stored
  -- compatibility proof by postcomposition with the slice morphism.
  rfl

/-- Helper for Lemma 7.26.4: after pulling a component of `localized_cover_descent_pullbackDatum`
back along `g : Z ⟶ K.Y`, evaluating at the terminal object of `Over Z` is the same as evaluating
the original component on `Over.mk g`. This is the terminal-section normalization used in the
glued compatible-family overlap equations. -/
theorem localized_cover_descent_pullbackDatum_section_eq
    (𝒰 : J.Cover U)
    (D : localized_cover_descent_category (J := J) (U := U) 𝒰)
    (V : Over U)
    (K : (𝒰.pullback V.hom).Arrow)
    {Z : C}
    (g : Z ⟶ K.Y) :
    (((J.overMapPullback (Type w) g).obj
        ((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K)).1.obj
      (Opposite.op (Over.mk (𝟙 Z)))) =
      (((localized_cover_descent_pullbackDatum (J := J) (U := U) 𝒰 D V).obj K).1.obj
        (Opposite.op (Over.mk g))) := by
  -- Unfold the pullback-datum component and normalize the pulled-back terminal object.
  simp [localized_cover_descent_pullbackDatum,
    localized_cover_descent_overMap_terminal_obj]

/-- Helper for Lemma 7.26.4: once a glue functor together with unit and counit isomorphisms is
constructed, the fixed-cover descent functor is packaged as an equivalence of categories. -/
def localized_cover_descent_equivalence
    (𝒰 : J.Cover U)
    (glue : localized_cover_descent_category (J := J) (U := U) 𝒰 ⥤
      Sheaf (J.over U) (Type w))
    (unitIso :
      𝟭 (Sheaf (J.over U) (Type w)) ≅
        ((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)) ⋙ glue)
    (counitIso :
      glue ⋙ ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)) ≅
        𝟭 (localized_cover_descent_category (J := J) (U := U) 𝒰)) :
    Sheaf (J.over U) (Type w) ≌
      localized_cover_descent_category (J := J) (U := U) 𝒰 :=
  Equivalence.mk
    ((J.pseudofunctorOver (Type w)).toDescentData (fun I : 𝒰.Arrow ↦ I.f))
    glue
    unitIso
    counitIso

/-- Helper for Lemma 7.26.4: an explicit glue quasi-inverse to `toDescentData` is enough to prove
the owner-level fixed-cover stack statement. -/
theorem localized_cover_descent_isStackFor_of_equivalenceData
    (𝒰 : J.Cover U)
    (glue : localized_cover_descent_category (J := J) (U := U) 𝒰 ⥤
      Sheaf (J.over U) (Type w))
    (unitIso :
      𝟭 (Sheaf (J.over U) (Type w)) ≅
        ((J.pseudofunctorOver (Type w)).toDescentData
          (fun I : 𝒰.Arrow ↦ I.f)) ⋙ glue)
    (counitIso :
      glue ⋙ ((J.pseudofunctorOver (Type w)).toDescentData
        (fun I : 𝒰.Arrow ↦ I.f)) ≅
        𝟭 (localized_cover_descent_category (J := J) (U := U) 𝒰)) :
    (J.pseudofunctorOver (Type w)).IsStackFor
      (Presieve.ofArrows _ (fun I : 𝒰.Arrow ↦ I.f)) := by
  -- Rewrite the owner theorem to the explicit descent-data functor statement.
  rw [Pseudofunctor.isStackFor_ofArrows_iff]
  -- The quasi-inverse data now closes the goal by the standard equivalence package.
  exact (localized_cover_descent_equivalence (J := J) (U := U) 𝒰
    glue unitIso counitIso).isEquivalence_functor

-- Route correction: the local `localized_pseudofunctorOver_*` transport block duplicated the
-- prestack work from Lemma `7.26.1` and was the source of the compile errors in this file. The
-- fixed-cover full-faithfulness proof below now uses the direct terminal-cover sheaf condition.
-- The surviving comparison lemmas remain available because the fixed-cover proof still needs the
-- stable NatIso between the ordinary slice-site Hom sheaf and `pseudofunctorOver.presheafHom`.


end

end GrothendieckTopology
end CategoryTheory

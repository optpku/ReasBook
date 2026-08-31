module

public import stacks_project.Chap04.Definition_4_42_3
public import stacks_project.Chap04.Definition_4_40_1
public import stacks_project.Chap04.Lemma_4_35_9
public import stacks_project.Chap04.Lemma_4_35_13
public import stacks_project.Chap04.Lemma_4_35_14

@[expose] public section

/-!
# Support for Lemma 4.42.6: representability over a slice base versus over `C`

The proof of Lemma 4.42.6 compares categories fibred in groupoids over different slice bases
(`Over U`, `Over V`, `Over (U ⨯ V)`). This file provides the *absolutization* bridge that turns a
representability question over a slice base `Over U` into one over the fixed base `C`, where the
ambient two-fibre-product comparison lemmas apply.

Key tools:
* `isRepresentable_of_equivalence_to_over` / `..._iso`: representability of `Z` from an equivalence
  functor `Z.S ⥤ Over W` lying over the base (strictly, resp. up to a natural iso).
* `absolutize`: compose the projection of a slice-based fibred category with `Over.forget U`.
* `absolutize_isRepresentable_of_isRepresentable`: the forward bridge.
-/

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver (ofFunctor)

variable {C : Type (max u v)} [Category.{v} C]

/-- A category fibred in groupoids over a slice base `Over U` is representable provided there is an
equivalence of its total category with a slice `Over W` strictly compatible with the base
projection. -/
theorem isRepresentable_of_equivalence_to_over
    {D : Type (max u v)} [Category.{v} D]
    (Z : FibredInGroupoidsOver D) (W : D)
    (e : Z.S ⥤ Over W) [e.IsEquivalence]
    (hcomm : e ⋙ Over.forget W = Z.p) :
    Z.IsRepresentable := by
  -- The strict compatibility lets us package `e` as a based functor; an equivalence on total
  -- categories is automatically an equivalence over the base.
  rw [FibredInGroupoidsOver.isRepresentable_iff_exists_presentation]
  refine ⟨W, FibredInGroupoidsMor.ofBasedFunctor { toFunctor := e, w := hcomm }, ?_⟩
  apply FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
  exact (inferInstance : e.IsEquivalence)

/-- The strictification of a comparison functor `e : Z.S ⥤ Over W` along a natural isomorphism
`α : e ⋙ Over.forget W ≅ Z.p`: transport each value of `e` to lie strictly over `Z.p`. -/
@[simps]
noncomputable def strictifyToOver
    {D : Type (max u v)} [Category.{v} D]
    (Z : FibredInGroupoidsOver D) (W : D)
    (e : Z.S ⥤ Over W) (α : e ⋙ Over.forget W ≅ Z.p) :
    Z.S ⥤ Over W where
  obj z := Over.mk (α.inv.app z ≫ (e.obj z).hom)
  map {z z'} k := Over.homMk (Z.p.map k) (by
    -- Naturality of `α.inv` together with the slice-triangle for `e.map k`.
    have hw : (e.map k).left ≫ (e.obj z').hom = (e.obj z).hom := Over.w (e.map k)
    have hn : Z.p.map k ≫ α.inv.app z' = α.inv.app z ≫ (e.map k).left := α.inv.naturality k
    simp only [Over.mk_hom]
    calc Z.p.map k ≫ α.inv.app z' ≫ (e.obj z').hom
        = (Z.p.map k ≫ α.inv.app z') ≫ (e.obj z').hom := (Category.assoc _ _ _).symm
      _ = (α.inv.app z ≫ (e.map k).left) ≫ (e.obj z').hom := congrArg (· ≫ (e.obj z').hom) hn
      _ = α.inv.app z ≫ (e.map k).left ≫ (e.obj z').hom := Category.assoc _ _ _
      _ = α.inv.app z ≫ (e.obj z).hom := congrArg (α.inv.app z ≫ ·) hw)

/-- The strictification is naturally isomorphic to the original comparison functor. -/
noncomputable def strictifyToOverIso
    {D : Type (max u v)} [Category.{v} D]
    (Z : FibredInGroupoidsOver D) (W : D)
    (e : Z.S ⥤ Over W) (α : e ⋙ Over.forget W ≅ Z.p) :
    strictifyToOver Z W e α ≅ e :=
  NatIso.ofComponents
    (fun z => Over.isoMk (α.app z).symm (by simp [strictifyToOver]))
    (fun {z z'} k => by
      apply Over.OverMorphism.ext
      have hn : Z.p.map k ≫ α.inv.app z' = α.inv.app z ≫ (e.map k).left := α.inv.naturality k
      simpa [strictifyToOver] using hn)

/-- Variant of `isRepresentable_of_equivalence_to_over` requiring base compatibility only up to a
natural isomorphism. -/
theorem isRepresentable_of_equivalence_to_over_iso
    {D : Type (max u v)} [Category.{v} D]
    (Z : FibredInGroupoidsOver D) (W : D)
    (e : Z.S ⥤ Over W) [e.IsEquivalence]
    (α : e ⋙ Over.forget W ≅ Z.p) :
    Z.IsRepresentable := by
  haveI : (strictifyToOver Z W e α).IsEquivalence :=
    Functor.isEquivalence_of_iso (strictifyToOverIso Z W e α).symm
  exact isRepresentable_of_equivalence_to_over Z W (strictifyToOver Z W e α) rfl

/-- Transport representability along an equivalence of total categories compatible with the base
projection up to natural isomorphism. -/
theorem isRepresentable_of_total_equivalence_over_base_iso
    {P Q : FibredInGroupoidsOver C}
    (e : P.S ⥤ Q.S) [e.IsEquivalence]
    (α : e ⋙ Q.p ≅ P.p)
    (hQ : Q.IsRepresentable) :
    P.IsRepresentable := by
  rw [FibredInGroupoidsOver.isRepresentable_iff_exists_presentation] at hQ
  obtain ⟨W, j, hj⟩ := hQ
  haveI : (FibredInGroupoidsMor.G j).IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase _ hj
  let eTot : P.S ≌ Over W :=
    e.asEquivalence.trans (FibredInGroupoidsMor.G j).asEquivalence
  refine isRepresentable_of_equivalence_to_over_iso P W eTot.functor ?_
  change (e ⋙ FibredInGroupoidsMor.G j) ⋙ Over.forget W ≅ P.p
  exact (Functor.associator e (FibredInGroupoidsMor.G j) (Over.forget W)) ≪≫
    Functor.isoWhiskerLeft e (eqToIso (FibredInGroupoidsMor.comm j)) ≪≫ α

/-- Transport representability from a target CFG along packaged total-category data:
a functor on total categories, an equivalence instance for it, and compatibility with the base
projection.  This keeps later Stacks comparison lemmas from projecting Sigma fields in large goals. -/
theorem isRepresentable_of_total_equivalence_transportData
    {P Q : FibredInGroupoidsOver C}
    (data : Σ' (e : P.S ⥤ Q.S), Σ' (_ : e.IsEquivalence), e ⋙ Q.p ≅ P.p)
    (hQ : Q.IsRepresentable) : P.IsRepresentable := by
  rcases data with ⟨e, he, α⟩
  haveI : e.IsEquivalence := he
  exact isRepresentable_of_total_equivalence_over_base_iso e α hQ

/-- Transport representability from a target CFG along packaged total-category equivalence data:
an equivalence of total categories and compatibility of its forward functor with the base projection. -/
theorem isRepresentable_of_total_equivalenceData
    {P Q : FibredInGroupoidsOver C}
    (data : Σ' (E : P.S ≌ Q.S), E.functor ⋙ Q.p ≅ P.p)
    (hQ : Q.IsRepresentable) : P.IsRepresentable := by
  rcases data with ⟨E, α⟩
  exact isRepresentable_of_total_equivalence_over_base_iso E.functor α hQ

/-- The absolutization over `C` of a category fibred in groupoids over a slice base `Over U`. -/
noncomputable abbrev absolutize {U : C} (Z : FibredInGroupoidsOver (Over U)) :
    FibredInGroupoidsOver C :=
  ofFunctor (Z.p ⋙ Over.forget U)

/-- Two based categories with definitionally equal carrier and category instance are equal as soon
as their projection functors are equal. -/
private theorem basedCategory_eq_of_p_eq {S' : Type*} [Category S']
    (A B : BasedCategory S')
    (hobj : A.obj = B.obj)
    (hcat : HEq A.category B.category)
    (hp : HEq A.p B.p) : A = B := by
  cases A; cases B
  cases hobj; cases hcat; cases hp
  rfl

/-- The absolutization over `C` of the slice base change `sliceTwoFibreProduct F Garg` is equal to
the bicategorical `2`-fibre product `twoFibreProduct Garg F`. -/
theorem absolutize_sliceTwoFibreProduct_eq
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) {U : C}
    (Garg : ofFunctor (Over.forget U) ⟶ Y) :
    (absolutize (FibredInGroupoidsMor.sliceTwoFibreProduct F Garg))
      = (FibredInGroupoidsOver.twoFibreProduct Garg F) := by
  refine ObjectProperty.FullSubcategory.ext ?_
  refine ObjectProperty.FullSubcategory.ext ?_
  refine basedCategory_eq_of_p_eq _ _ rfl (HEq.refl _) ?_
  refine heq_of_eq ?_
  exact FibredInGroupoidsMor.comm
    (FibredInGroupoidsOver.twoFibreProductLeftProjection Garg F)

/-- Representability transport across
`absolutize (sliceTwoFibreProduct F Garg) = twoFibreProduct Garg F`. -/
theorem absolutize_sliceTwoFibreProduct_isRepresentable_of_twoFibreProduct
    {X Y : FibredInGroupoidsOver C} (F : X ⟶ Y) {U : C}
    (Garg : ofFunctor (Over.forget U) ⟶ Y)
    (h : (FibredInGroupoidsOver.twoFibreProduct Garg F).IsRepresentable) :
    (absolutize (FibredInGroupoidsMor.sliceTwoFibreProduct F Garg)).IsRepresentable := by
  rw [absolutize_sliceTwoFibreProduct_eq F Garg]
  exact h

/-- Forward bridge: representability over the slice base `Over U` implies representability of the
absolutization over `C`. -/
theorem absolutize_isRepresentable_of_isRepresentable
    {U : C} (Z : FibredInGroupoidsOver (Over U)) (hZ : Z.IsRepresentable) :
    (absolutize Z).IsRepresentable := by
  obtain ⟨W, ⟨e⟩⟩ := hZ
  have hφ : FibredInGroupoidsMor.IsEquivalenceOverBase e.hom :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  haveI : (FibredInGroupoidsMor.G e.hom).IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase _ hφ
  -- Compose the presentation with the iterated-slice equivalence `(Over U)/W ≌ Over W.left`.
  refine isRepresentable_of_equivalence_to_over (absolutize Z) W.left
    ((FibredInGroupoidsMor.G e.hom).asEquivalence.trans (Over.iteratedSliceEquiv W)).functor ?_
  exact congrArg (· ⋙ Over.forget U) (FibredInGroupoidsMor.comm e.hom)

/-- Slice 2-Yoneda: a functor `Q : Over W₀ ⥤ Over U` compatible over `C` with the slice forgetful
functors (witnessed by `β`) is naturally isomorphic to `Over.map w` for the induced base arrow
`w := (β.app ⊤).inv ≫ (Q.obj ⊤).hom` where `⊤ = Over.mk (𝟙 W₀)`. (The slice projections are
discrete fibrations, so a functor between slices over `C` is determined by a base arrow.) -/
noncomputable def overFunctorIsoMap {W₀ U : C} (Q : Over W₀ ⥤ Over U)
    (β : Q ⋙ Over.forget U ≅ Over.forget W₀) :
    Q ≅ Over.map ((β.app (Over.mk (𝟙 W₀))).inv ≫ (Q.obj (Over.mk (𝟙 W₀))).hom) := by
  refine NatIso.ofComponents (fun g => Over.isoMk (β.app g) ?_) ?_
  · -- Componentwise commutation: read off the slice triangle of `Q.map` on the canonical morphism
    -- to the terminal object `⊤`, then cancel the iso `β.app ⊤`.
    have hnat' : (Q.map (Over.homMk g.hom (by simp) : g ⟶ Over.mk (𝟙 W₀))).left
          ≫ (β.app (Over.mk (𝟙 W₀))).hom = β.hom.app g ≫ g.hom := by
      have := β.hom.naturality (Over.homMk g.hom (by simp) : g ⟶ Over.mk (𝟙 W₀))
      simpa [Functor.comp_map, Over.forget_map] using this
    have hwq := Over.w (Q.map (Over.homMk g.hom (by simp) : g ⟶ Over.mk (𝟙 W₀)))
    have key := (Iso.eq_comp_inv (β.app (Over.mk (𝟙 W₀)))).mpr hnat'
    show (β.app g).hom ≫ (g.hom ≫ _) = (Q.obj g).hom
    rw [← hwq, key]; simp
  · -- Naturality is exactly the naturality of `β`.
    intro g g' k
    apply Over.OverMorphism.ext
    have hnat := β.hom.naturality k
    simp only [Functor.comp_map, Over.forget_map] at hnat
    simpa using hnat

/-- Backward bridge: representability of the absolutization over `C` implies representability over
the slice base `Over U`. -/
theorem isRepresentable_of_absolutize_isRepresentable
    {U : C} (Z : FibredInGroupoidsOver (Over U)) (hAbs : (absolutize Z).IsRepresentable) :
    Z.IsRepresentable := by
  obtain ⟨W₀, ⟨e⟩⟩ := hAbs
  have hφ : FibredInGroupoidsMor.IsEquivalenceOverBase e.hom :=
    FibredInGroupoidsOver.hom_isEquivalenceOverBase e
  haveI : (FibredInGroupoidsMor.G e.hom).IsEquivalence :=
    BasedFunctor.isEquivalence_of_isEquivalenceOverBase _ hφ
  -- The presentation gives an equivalence `ψ : Z.S ≌ Over W₀` over `C`.
  set ψ : Z.S ≌ Over W₀ := (FibredInGroupoidsMor.G e.hom).asEquivalence with hψ
  have hcomm : ψ.functor ⋙ Over.forget W₀ = Z.p ⋙ Over.forget U :=
    FibredInGroupoidsMor.comm e.hom
  -- Transport `Z.p` through `ψ⁻¹` to a functor `Q : Over W₀ ⥤ Over U` over `C`.
  set Q : Over W₀ ⥤ Over U := ψ.inverse ⋙ Z.p with hQ
  have hβeq : Q ⋙ Over.forget U = (ψ.inverse ⋙ ψ.functor) ⋙ Over.forget W₀ := by
    rw [hQ, Functor.assoc, ← hcomm, ← Functor.assoc]
  set β : Q ⋙ Over.forget U ≅ Over.forget W₀ :=
    eqToIso hβeq ≪≫ Functor.isoWhiskerRight ψ.counitIso (Over.forget W₀)
      ≪≫ (Over.forget W₀).leftUnitor with hβ
  -- Slice 2-Yoneda: `Q ≅ Over.map w` for the induced base arrow `w : W₀ ⟶ U`.
  set w : W₀ ⟶ U := (β.app (Over.mk (𝟙 W₀))).inv ≫ (Q.obj (Over.mk (𝟙 W₀))).hom with hw
  have hQmap : Q ≅ Over.map w := overFunctorIsoMap Q β
  set W : Over U := Over.mk w with hWdef
  -- Compose `ψ` with the iterated-slice equivalence into `(Over U)/W` and transport the comparison.
  refine isRepresentable_of_equivalence_to_over_iso Z W
    (ψ.trans (Over.iteratedSliceEquiv W).symm).functor ?_
  exact (Functor.isoWhiskerLeft ψ.functor hQmap.symm) ≪≫ ψ.funInvIdAssoc Z.p

/-- The absolutization bridge: representability over a slice base `Over U` is equivalent to
representability of the absolutization over `C`. -/
theorem isRepresentable_iff_absolutize_isRepresentable
    {U : C} (Z : FibredInGroupoidsOver (Over U)) :
    Z.IsRepresentable ↔ (absolutize Z).IsRepresentable :=
  ⟨absolutize_isRepresentable_of_isRepresentable Z,
    isRepresentable_of_absolutize_isRepresentable Z⟩

end CategoryTheory

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite CategoryOfElements
open CategoryTheory.OverPresheafAux

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type v))

noncomputable section

/- Domain-style sampling for Lemma 7.30.3:
- primary domain: localization of a sheaf topos at an object, presented by the site on the
  category of elements of a set-valued sheaf;
- sampled owner declarations:
  `CategoryOfElements.costructuredArrowYonedaEquivalence`,
  `overEquivPresheafCostructuredArrow`,
  `forgetAdjToOver`,
  `Over.forgetAdjStar`;
- best owner abstraction: the public source-facing owners in this file should be the
  category-of-elements projection/topology together with the slice-topos equivalence
  `sheafCategoryOfElementsEquivOver ℱ`; the presheaf-on-elements description is bridge data, and
  the localization inverse image is canonically owned by `toOver ℱ`, then compared to
  `Over.star ℱ` via uniqueness of right adjoints;
- primitive data: only the sheaf `ℱ`;
- derived API: `localizationProjection`, `localizationTopology`,
  `sheafCategoryOfElementsEquivOver ℱ`, and the comparison between the induced inverse image and
  `Over.star ℱ`.

Source/core/bridge triage:
- `source-facing`: `localizationProjection`, `localizationTopology`,
  `sheafCategoryOfElementsEquivOver ℱ`;
- `core/canonical`: the costructured-arrow/presheaf-over owners
  `CategoryOfElements.costructuredArrowYonedaEquivalence` and
  `overEquivPresheafCostructuredArrow`, plus the slice right-adjoint owners `toOver ℱ` and
  `Over.forgetAdjStar ℱ`;
- `bridge/view`: the internal transport from sheaves on the induced topology to slice objects over
  `ℱ`, and the induced inverse-image comparison isomorphisms.
-/

/-- The projection from the category of elements of a sheaf to the base site. -/
abbrev localizationProjection (ℱ : Sheaf J (Type v)) : ℱ.obj.Elementsᵒᵖ ⥤ C :=
  (π ℱ.obj).leftOp

local notation "Elt" => ℱ.obj.Elementsᵒᵖ
local notation "j" => localizationProjection ℱ

/-- Helper for Lemma 7.30.3: the top sieve is covering for the site of pairs `(U, s)`. -/
theorem localizationTopology_top_mem
    (X : Elt) :
    Sieve.functorPushforward j (⊤ : Sieve X) ∈ J ((localizationProjection ℱ).obj X) := by
  -- By definition, the site of elements declares a sieve covering when its image in `C` covers.
  rw [Sieve.functorPushforward_top]
  exact J.top_mem ((localizationProjection ℱ).obj X)

/-- Helper for Lemma 7.30.3: after pulling a sieve on the category of elements back along a map,
its pushforward along `j` contains the pullback of the original pushed-forward sieve on `C`. -/
theorem localizationTopology_pushforward_pullback_le
    {X Y : Elt} (f : X ⟶ Y) (S : Sieve Y) :
    Sieve.pullback ((localizationProjection ℱ).map f) (Sieve.functorPushforward j S) ≤
      Sieve.functorPushforward j (S.pullback f) := by
  intro W k hk
  rcases hk with ⟨Z, g, i, hg, hki⟩
  have hki' :
      k ≫ (localizationProjection ℱ).map f = i ≫ (localizationProjection ℱ).map g := by
    simpa using hki
  have hg_section :
      (unop Z).2 = ℱ.obj.map ((localizationProjection ℱ).map g).op (unop Y).2 := by
    simpa [localizationProjection] using (CategoryOfElements.map_snd g.unop).symm
  have hf_section :
      ℱ.obj.map ((localizationProjection ℱ).map f).op (unop Y).2 = (unop X).2 := by
    simpa [localizationProjection] using (CategoryOfElements.map_snd f.unop)
  let W' : ℱ.obj.Elements := ⟨op W, ℱ.obj.map k.op (unop X).2⟩
  let hX : op W' ⟶ X := Quiver.Hom.op (CategoryOfElements.homMk (unop X) W' k.op rfl)
  have hZw :
      ℱ.obj.map i.op (unop Z).2 = W'.2 := by
    calc
      ℱ.obj.map i.op (unop Z).2
          = ℱ.obj.map (i ≫ (localizationProjection ℱ).map g).op (unop Y).2 := by
              rw [show (i ≫ (localizationProjection ℱ).map g).op =
                  ((localizationProjection ℱ).map g).op ≫ i.op by rfl]
              rw [FunctorToTypes.map_comp_apply, hg_section]
      _ = ℱ.obj.map (k ≫ (localizationProjection ℱ).map f).op (unop Y).2 := by
            rw [hki']
      _ = ℱ.obj.map k.op (unop X).2 := by
            rw [show (k ≫ (localizationProjection ℱ).map f).op =
                ((localizationProjection ℱ).map f).op ≫ k.op by rfl]
            rw [FunctorToTypes.map_comp_apply, hf_section]
      _ = W'.2 := rfl
  let hZ : op W' ⟶ Z := Quiver.Hom.op (CategoryOfElements.homMk (unop Z) W' i.op hZw)
  have hpull : S.pullback f hX := by
    have hcomp : hX ≫ f = hZ ≫ g := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext ℱ.obj _ _
      simpa [hX, hZ] using congrArg Quiver.Hom.op hki'
    change S (hX ≫ f)
    rw [hcomp]
    exact S.downward_closed hg hZ
  simpa [hX] using
    (Sieve.image_mem_functorPushforward (F := j) (R := S.pullback f) hpull)

/-- Helper for Lemma 7.30.3: pullbacks of covering sieves in the category of elements remain
covering because pushforward along `j` is compatible with pullback up to refinement. -/
theorem localizationTopology_pullback_stable
    {X Y : Elt} {S : Sieve Y} (f : X ⟶ Y)
    (hS : Sieve.functorPushforward j S ∈ J ((localizationProjection ℱ).obj Y)) :
    Sieve.functorPushforward j (S.pullback f) ∈ J ((localizationProjection ℱ).obj X) := by
  -- Every refinement of the pulled-back base cover lifts back to a refinement in the elements site.
  refine J.superset_covering (localizationTopology_pushforward_pullback_le (ℱ := ℱ) f S) ?_
  exact J.pullback_stable ((localizationProjection ℱ).map f) hS

/-- Helper for Lemma 7.30.3: the transitivity axiom for the site of pairs is inherited from the
base site after pushing sieves forward along `j`. -/
theorem localizationTopology_transitive
    {X : Elt} {S R : Sieve X}
    (hS : Sieve.functorPushforward j S ∈ J ((localizationProjection ℱ).obj X))
    (hR : ∀ ⦃Y : Elt⦄ (f : Y ⟶ X), S f →
      Sieve.functorPushforward j (R.pullback f) ∈ J ((localizationProjection ℱ).obj Y)) :
    Sieve.functorPushforward j R ∈ J ((localizationProjection ℱ).obj X) := by
  -- Push the refinement data down to `C` and invoke the transitivity axiom there.
  apply J.transitive hS
  rintro Y _ ⟨Z, g, i, hg, rfl⟩
  have hcover :
      Sieve.pullback i
          (Sieve.pullback ((localizationProjection ℱ).map g) (Sieve.functorPushforward j R)) ∈
        J Y := by
    apply J.pullback_stable i
    refine J.superset_covering (Sieve.functorPushforward_pullback_le (F := j) g R) (hR g hg)
  simpa [Sieve.pullback_comp] using hcover

/-- The Grothendieck topology on the category of elements of `ℱ`: a sieve is covering exactly
when its image sieve on `C` is covering. -/
def localizationTopology (ℱ : Sheaf J (Type v)) : GrothendieckTopology ℱ.obj.Elementsᵒᵖ where
  sieves X S :=
    Sieve.functorPushforward (localizationProjection ℱ) S ∈ J ((localizationProjection ℱ).obj X)
  top_mem' := localizationTopology_top_mem (ℱ := ℱ)
  pullback_stable' _ _ _ f hS := localizationTopology_pullback_stable (ℱ := ℱ) f hS
  transitive' _ _ hS _ hR := localizationTopology_transitive (ℱ := ℱ) hS hR

local notation "Jₑ" => localizationTopology ℱ

/-- Helper for Lemma 7.30.3: covers for `localizationTopology ℱ` are already defined by
pushforward along the projection `j`. -/
theorem localizationProjection_coverPreserving :
    CoverPreserving Jₑ J j where
  cover_preserve {U} {S} hS := by
    simpa [localizationTopology] using hS

/-- Helper for Lemma 7.30.3: every base arrow into `(U, s)` canonically lifts to the category of
elements by restricting the section `s`. -/
theorem localizationProjection_cover_lift
    (X : Elt) (S : Sieve ((localizationProjection ℱ).obj X)) :
    S ≤
      Sieve.functorPushforward (localizationProjection ℱ)
        (S.functorPullback (localizationProjection ℱ)) := by
  intro Y g hg
  let Y' : ℱ.obj.Elements := ⟨op Y, ℱ.obj.map g.op (unop X).2⟩
  let lift : op Y' ⟶ X := Quiver.Hom.op (CategoryOfElements.homMk (unop X) Y' g.op rfl)
  have hpull : S.functorPullback j lift := by
    -- The lifted arrow projects back to the original base arrow `g`.
    change S ((localizationProjection ℱ).map lift)
    simpa [lift] using hg
  exact Sieve.image_mem_functorPushforward (F := j) (R := S.functorPullback j) hpull

-- Proof sketch: equality of base composites gives a common lifted section over the source object,
-- and compatibility there implies compatibility after forgetting back to `C`.
theorem sheafCategoryOfElementsProjection_compatiblePreserving :
    CompatiblePreserving J j := by
  constructor
  intro 𝒢 Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ h
  let X' : Elt := op ⟨op X, ℱ.obj.map f₁.op (unop Y₁).2⟩
  let g₁' : X' ⟶ Y₁ := by
    refine Quiver.Hom.op ?_
    refine CategoryOfElements.homMk (unop Y₁) (unop X') f₁.op ?_
    -- The first lift is built using the defining section of `X'`.
    rfl
  let g₂' : X' ⟶ Y₂ := by
    refine Quiver.Hom.op ?_
    refine CategoryOfElements.homMk (unop Y₂) (unop X') f₂.op ?_
    -- The second lift uses the equality of the two base composites through `Z`.
    calc
      ℱ.obj.map f₂.op (unop Y₂).2
          = ℱ.obj.map (f₂ ≫ (localizationProjection ℱ).map g₂).op (unop Z).2 := by
              rw [← CategoryOfElements.map_snd g₂.unop]
              simp
      _ = ℱ.obj.map (f₁ ≫ (localizationProjection ℱ).map g₁).op (unop Z).2 := by
            simpa using congrArg (fun q ↦ ℱ.obj.map q.op (unop Z).2) h.symm
      _ = ℱ.obj.map f₁.op (unop Y₁).2 := by
            rw [← CategoryOfElements.map_snd g₁.unop]
            simp
  have hcomp : g₁' ≫ g₁ = g₂' ≫ g₂ := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext ℱ.obj _ _
    simpa [g₁', g₂'] using congrArg Quiver.Hom.op h
  -- Apply compatibility on the common lift and then forget back to the base site.
  simpa [g₁', g₂'] using hx g₁' g₂' hg₁ hg₂ hcomp

/-- Lemma 7.30.3 (1): the projection from the category of elements of `ℱ` to `C` is continuous for
the topology on pairs `(U, s)` induced from `J`. -/
instance localizationProjection_isContinuous :
    Functor.IsContinuous (localizationProjection ℱ) (localizationTopology ℱ) J :=
  Functor.isContinuous_of_coverPreserving
    (sheafCategoryOfElementsProjection_compatiblePreserving ℱ)
    (localizationProjection_coverPreserving ℱ)

/-- Lemma 7.30.3 (2): the projection from the category of elements of `ℱ` to `C` is
cocontinuous for the topology on pairs `(U, s)`. -/
instance localizationProjection_isCocontinuous :
    Functor.IsCocontinuous (localizationProjection ℱ) (localizationTopology ℱ) J where
  cover_lift {X} S hS := by
    -- The canonical lift of each base arrow shows that the pulled-back sieve still covers.
    simpa [localizationTopology] using
      (J.superset_covering (localizationProjection_cover_lift (ℱ := ℱ) X S) hS)

-- Proof sketch: identify the opposite of the category of elements with the corresponding
-- costructured-arrow category via Yoneda, and then use the canonical equivalence between
-- presheaves on that costructured-arrow category and presheaves over `ℱ.obj`.
noncomputable abbrev sheafCategoryOfElementsPresheafEquivOverPresheaf :
    Eltᵒᵖ ⥤ Type v ≌ Over ℱ.obj :=
  ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft).trans
    (overEquivPresheafCostructuredArrow ℱ.obj).symm

noncomputable def yonedaCollectionProjIsoToOverLeft
    (P G : Cᵒᵖ ⥤ Type v) :
    yonedaCollectionPresheaf P ((CostructuredArrow.proj yoneda P).op ⋙ G) ≅
      ((toOver P).obj G).left :=
  NatIso.ofComponents
    (fun X ↦ by
      change YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop ≅
        (G.obj X × P.obj X)
      let homX : YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop →
          G.obj X × P.obj X := fun p ↦ ⟨p.snd, p.yonedaEquivFst⟩
      let invX : G.obj X × P.obj X →
          YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop :=
        fun p ↦ YonedaCollection.mk (yonedaEquiv.symm p.2) p.1
      refine { hom := homX, inv := invX, hom_inv_id := ?_, inv_hom_id := ?_ }
      · funext p
        change invX (homX p) = p
        let q : YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop :=
          invX (homX p)
        have h : q.fst = p.fst := by
          simp [q, homX, invX, YonedaCollection.yonedaEquivFst_eq]
        refine YonedaCollection.ext h ?_
        simp [homX, invX]
      · funext p
        change homX (invX p) = p
        rcases p with ⟨g, s⟩
        apply Prod.ext
        · simp [homX, invX]
        · simp [homX, invX, YonedaCollection.yonedaEquivFst_eq])
    (by
      intro X Y f
      ext p
      apply Prod.ext
      · simp
      · simp [YonedaCollection.map₂_yonedaEquivFst])

/-- Helper for Lemma 7.30.3: after identifying `((toOver P).obj G).left.obj X` with
`G.obj X × P.obj X`, the map induced by `η : G ⟶ G'` acts on the `G`-coordinate and leaves the
tautological `P`-coordinate unchanged. -/
theorem yonedaCollectionProjIsoToOverLeft_naturality_components
    {P G G' : Cᵒᵖ ⥤ Type v} (η : G ⟶ G') (X : Cᵒᵖ)
    (x : YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop) :
    (yonedaCollectionProjIsoToOverLeft P G').hom.app X
        (YonedaCollection.map₁
          (Functor.whiskerLeft ((CostructuredArrow.proj yoneda P).op) η) x) =
      (((toOver P).map η).left.app X)
        ((yonedaCollectionProjIsoToOverLeft P G).hom.app X x) := by
  -- Under the product identification, naturality is the componentwise action `(η.app X, id)`.
  apply Prod.ext <;> simp [yonedaCollectionProjIsoToOverLeft, toOver]

/-- Helper for Lemma 7.30.3: the local product identification
`yonedaCollectionProjIsoToOverLeft` is natural in the presheaf variable. -/
theorem yonedaCollectionProjIsoToOverLeft_naturality
    {P G G' : Cᵒᵖ ⥤ Type v} (η : G ⟶ G') :
    yonedaCollectionPresheafMap₁
        (Functor.whiskerLeft ((CostructuredArrow.proj yoneda P).op) η) ≫
      (yonedaCollectionProjIsoToOverLeft P G').hom =
    (yonedaCollectionProjIsoToOverLeft P G).hom ≫
      ((toOver P).map η).left := by
  -- The naturality square is checked pointwise on each object of the base site.
  ext X x
  exact yonedaCollectionProjIsoToOverLeft_naturality_components η X x

instance presheafIsSheaf_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf J : ObjectProperty (Cᵒᵖ ⥤ Type v)) where
  of_iso e hP := (Presheaf.isSheaf_of_iso_iff e).1 hP

abbrev overPresheafHasSheafDomain : ObjectProperty (Over ℱ.obj) :=
  ObjectProperty.inverseImage (Presheaf.IsSheaf J) (Over.forget ℱ.obj)

noncomputable def overPresheafHasSheafDomainEquivOver :
    (overPresheafHasSheafDomain ℱ).FullSubcategory ≌ Over ℱ where
  functor :=
    { obj := fun T ↦
        Over.mk (⟨T.obj.hom⟩ : ⟨T.obj.left, show Presheaf.IsSheaf J T.obj.left from T.property⟩ ⟶ ℱ)
      map := fun f ↦ Over.homMk ⟨f.hom.left⟩ (Sheaf.hom_ext f.hom.w) }
  inverse :=
    { obj := fun η ↦ ⟨Over.mk η.hom.hom, show overPresheafHasSheafDomain ℱ (Over.mk η.hom.hom) from η.left.property⟩
      map := fun f ↦
        ObjectProperty.homMk
          (Over.homMk f.left.hom (congrArg (fun g ↦ g.hom) (Over.w f))) }
  unitIso := NatIso.ofComponents
    (fun T ↦
      ObjectProperty.isoMk (overPresheafHasSheafDomain ℱ)
        (Over.isoMk (Iso.refl _) (by simp)))
    (by
      intro T T' f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      simp)
  counitIso := NatIso.ofComponents
    (fun η ↦ Over.isoMk (Iso.refl _) (by ext X x; rfl))
    (by
      intro η η' f
      apply Over.OverMorphism.ext
      apply Sheaf.hom_ext
      rfl)
  functor_unitIso_comp T := by
    apply Over.OverMorphism.ext
    apply Sheaf.hom_ext
    rfl

/-- Helper for Lemma 7.30.3: for an object `T` over `ℱ.obj`, the inverse presheaf is the
subpresheaf of `jᵒᵖ ⋙ T.left` cut out by the fiber condition over the tautological section. -/
def inverseFiberSubfunctor (T : Over ℱ.obj) :
    Subfunctor ((localizationProjection ℱ).op ⋙ T.left) where
  obj X := { t |
    T.hom.app (op ((localizationProjection ℱ).obj (unop X))) t = (unop (unop X)).2 }
  map := by
    intro X Y f t ht
    -- Restrict the section along `f` and transport the fiber equation by naturality of `T.hom`.
    show
      T.hom.app (op ((localizationProjection ℱ).obj (unop Y)))
          (((localizationProjection ℱ).op ⋙ T.left).map f t) =
        (unop (unop Y)).2
    have hnat := congr_fun (T.hom.naturality (((localizationProjection ℱ).map f.unop).op)) t
    have hnat' :
        T.hom.app (op ((localizationProjection ℱ).obj (unop Y)))
            (((localizationProjection ℱ).op ⋙ T.left).map f t) =
          ℱ.obj.map (((localizationProjection ℱ).map f.unop).op)
            (T.hom.app (op ((localizationProjection ℱ).obj (unop X))) t) := by
      simpa using hnat
    rw [ht] at hnat'
    refine hnat'.trans ?_
    simpa [localizationProjection] using (CategoryOfElements.map_snd f.unop)

/-- Helper for Lemma 7.30.3: the inverse object under the presheaf-over equivalence is naturally
isomorphic to the fiber subpresheaf of `T.left`. -/
noncomputable def inverseObjIsoInverseFiberSubfunctor (T : Over ℱ.obj) :
    ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).inverse.obj T) ≅
      (inverseFiberSubfunctor ℱ T).toFunctor := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    refine
      { hom := ?_
        inv := ?_
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro u
      -- Forgetting an over-arrow gives the underlying section of `T.left`.
      refine ⟨u.val, ?_⟩
      have hval :
          T.hom.app (unop (unop X)).1 u.val =
            yonedaEquiv (yonedaEquiv.symm (unop (unop X)).2) := by
        exact u.app_val
      rw [Equiv.apply_symm_apply] at hval
      exact hval
    · intro u
      -- The fiber equation upgrades a section back to an over-arrow.
      refine ⟨u.1, ⟨?_⟩⟩
      change T.hom.app (unop (unop X)).1 u.1 =
        yonedaEquiv (yonedaEquiv.symm (unop (unop X)).2)
      rw [Equiv.apply_symm_apply]
      exact u.2
    · ext u
      rfl
    · ext u
      rfl
  · intro X Y f
    ext u
    rfl

-- Proof sketch: under the canonical equivalence between the opposite category of elements of `ℱ`
-- and the Yoneda costructured-arrow category, the inverse object is the usual restricted-Yoneda
-- fiber construction attached to `T.hom`; hence the sheaf condition is exactly the one coming from
-- the sheaf domain `T.left`.
theorem sheafCategoryOfElementsInverseObj_isSheaf
    (T : Over ℱ.obj)
    (hT : Presheaf.IsSheaf J T.left) :
    Presheaf.IsSheaf Jₑ
      ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).inverse.obj T) := by
  let e := inverseObjIsoInverseFiberSubfunctor (ℱ := ℱ) T
  apply (Presheaf.isSheaf_of_iso_iff e).2
  have hbase : Presheaf.IsSheaf Jₑ ((localizationProjection ℱ).op ⋙ T.left) :=
    (localizationProjection ℱ).op_comp_isSheaf_of_isSheaf Jₑ J T.left hT
  have hfiber : Presheaf.IsSheaf Jₑ ((localizationProjection ℱ).op ⋙ ℱ.obj) :=
    (localizationProjection ℱ).op_comp_isSheaf_of_isSheaf Jₑ J ℱ.obj ℱ.property
  rw [isSheaf_iff_isSheaf_of_type] at hbase hfiber ⊢
  rw [Subfunctor.isSheaf_iff (inverseFiberSubfunctor ℱ T) hbase]
  intro X t ht
  -- A section belongs to the fiber once its image in `ℱ` agrees locally with the tautological
  -- section, because `ℱ` is separated on the same covering sieve.
  refine ((hfiber ((inverseFiberSubfunctor ℱ T).sieveOfSection t) ht).isSeparatedFor.ext ?_)
  intro Y f hf
  have hnat :
      ((localizationProjection ℱ).op ⋙ ℱ.obj).map f.op
          (T.hom.app (op ((localizationProjection ℱ).obj (unop X))) t) =
        T.hom.app (op ((localizationProjection ℱ).obj Y))
          (((localizationProjection ℱ).op ⋙ T.left).map f.op t) := by
    simpa using
      (congr_fun (T.hom.naturality (((localizationProjection ℱ).map f).op)) t).symm
  have hfiber' :
      T.hom.app (op ((localizationProjection ℱ).obj Y))
          (((localizationProjection ℱ).op ⋙ T.left).map f.op t) =
        (unop Y).2 := by
    simpa [Subfunctor.sieveOfSection, inverseFiberSubfunctor, localizationProjection] using hf
  rw [hnat]
  refine hfiber'.trans ?_
  simpa [localizationProjection] using (CategoryOfElements.map_snd f.unop).symm

/-- Helper for Lemma 7.30.3: equality of the restricted section values determines the underlying
Yoneda arrow uniquely. -/
theorem yoneda_map_symm_eq_of_map_eq
    {X Y : C} (f : Y ⟶ X) {s : ℱ.obj.obj (op X)} {t : yoneda.obj Y ⟶ ℱ.obj}
    (h : ℱ.obj.map f.op s = yonedaEquiv t) :
    yoneda.map f ≫ yonedaEquiv.symm s = t := by
  rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  simpa [yonedaEquiv_symm_app_apply] using h

/-- Helper for Lemma 7.30.3: a Yoneda collection is determined by its tautological section value. -/
theorem yoneda_collection_fst_eq_of_yonedaEquivFst_eq
    {F : (CostructuredArrow yoneda ℱ.obj)ᵒᵖ ⥤ Type v} {X : C}
    (q : YonedaCollection F X) {s : ℱ.obj.obj (op X)}
    (hq : q.yonedaEquivFst = s) :
    q.fst = yonedaEquiv.symm s := by
  -- Applying `yonedaEquiv` to both sides reduces the claim to the given section equality.
  rw [← yonedaEquiv.injective.eq_iff]
  simpa [YonedaCollection.yonedaEquivFst_eq] using hq

/-- Helper for Lemma 7.30.3: the glued base section determines the first coordinate of each local
family member over the base cover. -/
theorem local_family_fst_eq_glued_base
    {P : Eltᵒᵖ ⥤ Type v} {U Y : C} {S : Sieve U}
    (x : Presieve.FamilyOfElements
      (yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) S.arrows)
    {s : ℱ.obj.obj (op U)}
    (hs : ∀ ⦃Z : C⦄ (f : Z ⟶ U) (hf : S.arrows f),
      ℱ.obj.map f.op s = (x f hf).yonedaEquivFst)
    {f : Y ⟶ U} (hf : S.arrows f) :
    (x f hf).fst = yoneda.map f ≫ yonedaEquiv.symm s := by
  -- Convert the glued base equality from section values to Yoneda arrows.
  symm
  exact yoneda_map_symm_eq_of_map_eq (ℱ := ℱ) f (t := (x f hf).fst) (hs f hf)

/-- Helper for Lemma 7.30.3: pulling a local family on the base cover up to the elements-site cover
preserves the tautological first coordinate. -/
theorem pulled_back_local_family_first_coordinate
    {P : Eltᵒᵖ ⥤ Type v} {U : C} {S : Sieve U}
    (x : Presieve.FamilyOfElements
      (yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) S.arrows)
    {s : ℱ.obj.obj (op U)}
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ U) (hf : S.arrows f),
      ℱ.obj.map f.op s = (x f hf).yonedaEquivFst)
    {Y : Elt} (g : Y ⟶ op ⟨op U, s⟩)
    (hg : (Sieve.functorPullback (F := localizationProjection ℱ) (X := op ⟨op U, s⟩) S).arrows g) :
    (x ((localizationProjection ℱ).map g) (by simpa using hg)).yonedaEquivFst = (unop Y).2 := by
  -- The pulled-back section restricts to the tautological section by the glued base equation.
  refine (hs ((localizationProjection ℱ).map g) (by simpa using hg)).symm.trans ?_
  simpa [localizationProjection] using (CategoryOfElements.map_snd g.unop)

/-- Helper for Lemma 7.30.3: restricting a Yoneda collection whose first coordinate matches the
tautological section of `X` produces a Yoneda collection whose first coordinate matches the
tautological section of the source object. -/
theorem mapped_fixed_first_coordinate
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Elt} (g : Y ⟶ X)
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op X))
    (hq : q.yonedaEquivFst = (unop X).2) :
    (((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map g.op q).yonedaEquivFst =
      (unop Y).2 := by
  -- The first coordinate is functorial in the base arrow and then identified with the section of
  -- the source object by `CategoryOfElements.map_snd`.
  have hmap :
      ℱ.obj.map ((localizationProjection ℱ).map g).op (YonedaCollection.yonedaEquivFst q) =
        (unop Y).2 := by
    have hq_map :
        ℱ.obj.map ((localizationProjection ℱ).map g).op (YonedaCollection.yonedaEquivFst q) =
          ℱ.obj.map ((localizationProjection ℱ).map g).op (unop X).2 := by
      exact congrArg (fun t ↦ ℱ.obj.map ((localizationProjection ℱ).map g).op t) hq
    calc
      ℱ.obj.map ((localizationProjection ℱ).map g).op (YonedaCollection.yonedaEquivFst q)
          =
        ℱ.obj.map ((localizationProjection ℱ).map g).op (unop X).2 := hq_map
      _ = (unop Y).2 := by
          simpa [localizationProjection] using (CategoryOfElements.map_snd g.unop)
  simpa [YonedaCollection.map₂_yonedaEquivFst] using hmap

/-- Helper for Lemma 7.30.3: after restricting a compatible family on the pulled-back
elements-site cover along two arrows with the same composite, the resulting Yoneda collections
agree. -/
theorem pulled_back_yoneda_collection_eq_of_compatible
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt} {R : Sieve X}
    (w : Presieve.FamilyOfElements
      ((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) R.arrows)
    (hw : w.Compatible)
    {Y₁ Y₂ Z : Elt} (f₁ : Y₁ ⟶ X) (hf₁ : R.arrows f₁) (f₂ : Y₂ ⟶ X) (hf₂ : R.arrows f₂)
    (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) (h : g₁ ≫ f₁ = g₂ ≫ f₂) :
    let F :=
      (localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ P)
    let p₁ := F.map g₁.op (w f₁ hf₁)
    let p₂ := F.map g₂.op (w f₂ hf₂)
    p₁ = p₂ := by
  -- This is exactly compatibility of `w` after rewriting the ambient functor to the local form.
  simpa using hw g₁ g₂ hf₁ hf₂ h

/-- Helper for Lemma 7.30.3: when a Yoneda collection over the category of elements has first
coordinate equal to the tautological section of `Y`, its second coordinate can be viewed as an
element of `P.obj (op Y)`. -/
theorem second_coordinate_of_fixed_first_index
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y))
    (hsec : q.yonedaEquivFst = (unop Y).2) :
    ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ P).obj (op (CostructuredArrow.mk q.fst)) =
      P.obj (op Y) := by
  -- Replacing the first coordinate by the tautological section identifies the fiber object.
  cases Y using Opposite.rec
  rename_i Y
  cases Y with
  | mk Y sY =>
      dsimp at hsec ⊢
      rw [← hsec]
      rfl

/-- Helper for Lemma 7.30.3: extract the second coordinate of a Yoneda collection whose first
coordinate already matches the tautological section of `Y`. -/
def second_coordinate_of_fixed_first
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y))
    (hsec : q.yonedaEquivFst = (unop Y).2) :
    P.obj (op Y) :=
  cast (second_coordinate_of_fixed_first_index (ℱ := ℱ) (P := P) q hsec) q.snd

/-- Helper for Lemma 7.30.3: equality of sections over a fixed object induces equality of the
corresponding objects in the opposite of the category of elements, after applying `op` twice. -/
theorem elements_op_op_eq_of_section_eq
    {X : Cᵒᵖ} {s t : ℱ.obj.obj X} (h : s = t) :
    op (op ((⟨X, s⟩ : ℱ.obj.Elements))) = op (op ((⟨X, t⟩ : ℱ.obj.Elements))) := by
  -- The category-of-elements object changes only in its section component, so the equality is
  -- induced directly by the given equality of sections.
  apply congrArg op
  apply congrArg op
  refine Functor.Elements.ext _ _ rfl ?_
  simpa using h

/-- Helper for Lemma 7.30.3: removing both `op`s from an equality of opposite elements-site
objects recovers the underlying equality of elements. -/
theorem elements_eq_of_double_op_eq
    {x y : ℱ.obj.Elements} (h : op (op x) = op (op y)) :
    x = y := by
  -- The double-op equality is equivalent to equality in the original category of elements.
  simpa using congrArg unop (congrArg unop h)

/-- Helper for Lemma 7.30.3: equality of two elements over the same base object forces equality of
their section components. -/
theorem section_eq_of_elements_eq_same_base
    {X : Cᵒᵖ} {s t : ℱ.obj.obj X}
    (h : (⟨X, s⟩ : ℱ.obj.Elements) = ⟨X, t⟩) :
    s = t := by
  -- Once the base object is fixed, equality in the category of elements is equality of sections.
  cases h
  rfl

/-- Helper for Lemma 7.30.3: after identifying the target costructured arrow with the literal
section on `Y`, the `fromCostructuredArrow` image of the canonical precomposition morphism is the
literal morphism in the category of elements. -/
theorem fromCostructuredArrow_map_mkPrecomp_cast_eq_literal
    {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (hcostr :
      CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
        CostructuredArrow.mk (yonedaEquiv.symm sY)) :
    (fromCostructuredArrow ℱ.obj).map
        ((eqToHom hcostr.symm ≫
            CostructuredArrow.mkPrecomp (yonedaEquiv.symm sX) g.unop.val.unop).op) =
      CategoryTheory.CategoryOfElements.homMk
        ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (yonedaEquiv.symm sX))))
        ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (yonedaEquiv.symm sY))))
        g.unop.val
        (by simpa using CategoryTheory.CategoryOfElements.map_snd g.unop) := by
  -- The composite in the costructured-arrow category forgets to the same base arrow as `g`.
  apply CategoryTheory.CategoryOfElements.ext ℱ.obj
  -- After unfolding the functor map, both morphisms are literally the same underlying arrow.
  simp [CategoryTheory.CategoryOfElements.fromCostructuredArrow]

/-- Helper for Lemma 7.30.3: the object equalities `pX` and `pY` force the hidden first
coordinates in the transport calculation to be the literal sections `sX` and `sY`, hence the
underlying costructured-arrow object equality is the expected restriction of `sX` along `g`. -/
theorem restricted_costructured_arrow_eq_of_object_equalities
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (pX :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj X sX)))
    (pY :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk
            (YonedaCollection.fst
              (((localizationProjection ℱ).op ⋙
                  yonedaCollectionPresheaf ℱ.obj
                    ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
                g.op q))))) =
        op (op (Functor.elementsMk ℱ.obj Y sY))) :
    CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
      CostructuredArrow.mk (yonedaEquiv.symm sY) := by
  have hsecX :
      YonedaCollection.yonedaEquivFst q = sX := by
    -- The equality `pX` identifies the first coordinate of `q` with the tautological section.
    exact
      section_eq_of_elements_eq_same_base (ℱ := ℱ)
        (X := X) (s := YonedaCollection.yonedaEquivFst q) (t := sX)
        (elements_eq_of_double_op_eq (ℱ := ℱ) pX)
  have hsecY :
      YonedaCollection.yonedaEquivFst
          (((localizationProjection ℱ).op ⋙
              yonedaCollectionPresheaf ℱ.obj
                ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
            g.op q) =
        sY := by
    -- The equality `pY` does the same after restricting along `g`.
    exact
      section_eq_of_elements_eq_same_base (ℱ := ℱ)
        (X := Y)
        (s := YonedaCollection.yonedaEquivFst
          (((localizationProjection ℱ).op ⋙
              yonedaCollectionPresheaf ℱ.obj
                ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
            g.op q))
        (t := sY)
        (elements_eq_of_double_op_eq (ℱ := ℱ) pY)
  have hmapsec :
      ℱ.obj.map g.unop.val.unop.op sX = sY := by
    -- Rewrite the restricted first coordinate to the tautological section on `Y`.
    have hmapq :
        ℱ.obj.map g.unop.val.unop.op (YonedaCollection.yonedaEquivFst q) =
          YonedaCollection.yonedaEquivFst
            (((localizationProjection ℱ).op ⋙
                yonedaCollectionPresheaf ℱ.obj
                  ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
              g.op q) := by
      simpa [YonedaCollection.map₂_yonedaEquivFst]
    simpa [hsecX.symm] using hmapq.trans hsecY
  -- Converting the section equality back through the Yoneda equivalence gives the desired
  -- costructured-arrow equality.
  congr 1
  exact
    yoneda_map_symm_eq_of_map_eq (ℱ := ℱ) g.unop.val.unop
      (s := sX) (t := yonedaEquiv.symm sY) (by simpa using hmapsec)

/-- Helper for Lemma 7.30.3: once the restricted Yoneda collection has been rewritten into the
literal `map₂` form, the remaining second-coordinate comparison is only the outer transport along
the chosen object equalities `pX` and `pY`. -/
theorem congrLeft_map_via_fromCostructuredArrow
    {P : Eltᵒᵖ ⥤ Type v}
    {A B : (CostructuredArrow yoneda ℱ.obj)ᵒᵖ} (m : A ⟶ B) :
    (((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).map m) =
      P.map (((fromCostructuredArrow ℱ.obj).rightOp.op.map m)) := by
  -- The `congrLeft` functor is defined by whiskering with the inverse equivalence, so its map is
  -- definitionally the map of `P` along `fromCostructuredArrow`.
  rfl

/-- Helper for Lemma 7.30.3: unop-ing the hidden morphism in `YonedaCollection.map₂_snd` exposes
the explicit `eqToHom`-then-`mkPrecomp` composite in the costructured-arrow category. -/
theorem expanded_map2_snd_morphism_unop
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (qmap : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap))) :
    (((CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop).op ≫
        eqToHom hm_obj).unop) =
      eqToHom (congrArg unop hm_obj).symm ≫
        CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop := by
  -- Unop reverses the opposite-category composition and turns the final `eqToHom` on objects
  -- into the explicit transport needed for the later `fromCostructuredArrow.map` comparison.
  simpa [unop_comp]

/-- Helper for Lemma 7.30.3: once the restricted Yoneda collection has been rewritten into the
literal `map₂` form, the remaining second-coordinate comparison is only the outer transport along
the chosen object equalities `pX` and `pY`. -/
theorem yoneda_collection_fst_eq_literal_of_object_equality
    {P : Eltᵒᵖ ⥤ Type v} {X : Cᵒᵖ} {sX : ℱ.obj.obj X}
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (pX :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj X sX))) :
    YonedaCollection.fst q = yonedaEquiv.symm sX := by
  -- The object equality `pX` first identifies the underlying section, and Yoneda faithfulness
  -- upgrades that to equality of the first coordinates themselves.
  have hsecX :
      YonedaCollection.yonedaEquivFst q = sX := by
    exact
      section_eq_of_elements_eq_same_base (ℱ := ℱ)
        (X := X) (s := YonedaCollection.yonedaEquivFst q) (t := sX)
        (elements_eq_of_double_op_eq (ℱ := ℱ) pX)
  apply yonedaEquiv.injective
  change YonedaCollection.yonedaEquivFst q = yonedaEquiv (yonedaEquiv.symm sX)
  simpa [YonedaCollection.yonedaEquivFst_eq] using hsecX

/-- Helper for Lemma 7.30.3: rewriting the restricted target object by
`YonedaCollection.map₂_fst` exposes the literal costructured arrow
`yoneda.map g ≫ YonedaCollection.fst q`. -/
theorem restricted_target_object_eq_literal
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (pY :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk
            (YonedaCollection.fst
              (((localizationProjection ℱ).op ⋙
                  yonedaCollectionPresheaf ℱ.obj
                    ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
                g.op q))))) =
        op (op (Functor.elementsMk ℱ.obj Y sY))) :
    ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
        (op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)))) =
      op (op (Functor.elementsMk ℱ.obj Y sY)) := by
  -- Expanding `map₂_fst` removes the remaining opaque target object in the restricted collection.
  simpa [YonedaCollection.map₂_fst] using pY

/-- Helper for Lemma 7.30.3: a cast into an intermediate fiber, followed by the corresponding
`eqToHom` transport and the inverse cast back to the original fiber, is the identity. -/
theorem cast_eqToHom_cast
    {α β γ : Type v} (h₁ : α = β) (h₂ : β = γ) (h₃ : γ = α) (x : α) :
    cast h₃ (eqToHom h₂ (cast h₁ x)) = x := by
  -- All three transports are along equalities of types, so after eliminating those equalities the
  -- claim is definitionally `rfl`.
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- Helper for Lemma 7.30.3: in `Type`, the categorical transport `eqToHom` agrees with the usual
`cast` along the same equality of fibers. -/
theorem eqToHom_eq_cast
    {α β : Type v} (h : α = β) (x : α) :
    eqToHom h x = cast h x := by
  -- Eliminating the type equality reduces both transports to the identity map.
  cases h
  rfl

/-- Helper for Lemma 7.30.3: the hidden target object in `YonedaCollection.map₂_snd` already lies
over the literal section `sY` once the source first coordinate is normalized and the object-level
hidden arrow is compared with the source-proof costructured-arrow equality. -/
theorem hidden_target_fst_eq_literal
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (qmap : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (hfstq : YonedaCollection.fst q = yonedaEquiv.symm sX)
    (hcostr :
      CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
        CostructuredArrow.mk (yonedaEquiv.symm sY))
    (hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap))) :
    YonedaCollection.fst qmap = yonedaEquiv.symm sY := by
  have hm_obj' :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap)) := by
    calc
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX)) =
        op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) := by
          exact congrArg
            (fun f ↦ op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ f))) hfstq.symm
      _ = op (CostructuredArrow.mk (YonedaCollection.fst qmap)) := hm_obj
  -- Replace the hidden target object by the literal costructured-arrow object over `sY`.
  have pY :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) =
        op (op (Functor.elementsMk ℱ.obj Y sY)) := by
    calc
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) =
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX)))) := by
            exact congrArg
              ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj) hm_obj'.symm
      _ =
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (yonedaEquiv.symm sY)))) := by
            rw [hcostr]
      _ = op (op (Functor.elementsMk ℱ.obj Y sY)) := by
            simpa [CategoryOfElements.costructuredArrowYonedaEquivalence] using
              congrArg op
                (congrArg op
                  (CategoryOfElements.fromCostructuredArrow_obj_mk
                    (F := ℱ.obj) (X := unop Y) (f := yonedaEquiv.symm sY)))
  -- The literal object equality is exactly the input expected by the first-coordinate extractor.
  exact yoneda_collection_fst_eq_literal_of_object_equality (ℱ := ℱ) (P := P) qmap pY

/-- Helper for Lemma 7.30.3: unop-ing the hidden target-object equality removes the outer
opposite wrapper and exposes the underlying costructured-arrow equality. -/
theorem hidden_target_object_equality_unop
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (qmap : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap))) :
    CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q) =
      CostructuredArrow.mk (YonedaCollection.fst qmap) := by
  -- Applying `unop` once removes the outer opposite and reveals the raw object equality.
  exact congrArg unop hm_obj

/-- Helper for Lemma 7.30.3: once the restricted Yoneda collection has been rewritten into the
literal `map₂` form, the remaining second-coordinate comparison is only the outer transport along
the chosen object equalities `pX` and `pY`. -/
theorem hidden_m_unop_maps_to_literal_homMk
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (qmap : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (hfstq : YonedaCollection.fst q = yonedaEquiv.symm sX)
    (hfstqmap : YonedaCollection.fst qmap = yonedaEquiv.symm sY)
    (hcostr :
      CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
        CostructuredArrow.mk (yonedaEquiv.symm sY))
    (hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap))) :
    (fromCostructuredArrow ℱ.obj).map
        ((CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop).op ≫
          eqToHom hm_obj) =
      CategoryTheory.CategoryOfElements.homMk
        ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))))
        ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))
        g.unop.val
        (by
          rw [hfstq, hfstqmap]
          simpa using CategoryTheory.CategoryOfElements.map_snd g.unop) := by
  -- Route correction: once `fromCostructuredArrow.map` is unfolded, only the underlying base arrow
  -- survives, so the hidden transport witness is proof-irrelevant.
  apply CategoryTheory.CategoryOfElements.ext ℱ.obj
  simp [CategoryTheory.CategoryOfElements.fromCostructuredArrow]

/-- Helper for Lemma 7.30.3: the literal costructured-arrow object over `s` is sent by
`fromCostructuredArrow.rightOp.op` to the corresponding double-op elements-site object. -/
theorem fromCostructuredArrow_rightOp_op_obj_mk_eq_literal
    {X : Cᵒᵖ} {s : ℱ.obj.obj X} :
    ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
      (op (CostructuredArrow.mk (yonedaEquiv.symm s)))) =
      op (op (Functor.elementsMk ℱ.obj X s)) := by
  -- This is the object-level normalization used when transporting the explicit `homMk` endpoint.
  simpa [Functor.rightOp, CategoryOfElements.costructuredArrowYonedaEquivalence] using
    congrArg op
      (congrArg op
        (CategoryOfElements.fromCostructuredArrow_obj_mk
          (F := ℱ.obj) (X := unop X) (f := yonedaEquiv.symm s)))

/-- Helper for Lemma 7.30.3: the base arrow underlying an equality transport in a category of
elements is exactly the corresponding base `eqToHom`. -/
theorem category_of_elements_eqToHom_val
    {F : C ⥤ Type v} {x y : F.Elements} (h : x = y) :
    ((eqToHom h).val : x.1 ⟶ y.1) = eqToHom (congrArg Sigma.fst h) := by
  -- Eliminating the equality reduces both transports to the identity on the common base object.
  cases h
  rfl

/-- Helper for Lemma 7.30.3: once the restricted Yoneda collection has been rewritten into the
literal `map₂` form, the remaining second-coordinate comparison is only the outer transport along
the chosen object equalities `pX` and `pY`. -/
theorem fromCostructuredArrow_map_explicit_hidden_m_eq_literal
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (pX :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj X sX)))
    (hfstq : YonedaCollection.fst q = yonedaEquiv.symm sX)
    (qmap : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (pY :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) =
        op (op (Functor.elementsMk ℱ.obj Y sY)))
    (hcostr :
      CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
        CostructuredArrow.mk (yonedaEquiv.symm sY))
    (hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap)))
    :
    ((fromCostructuredArrow ℱ.obj).rightOp.op.map
        ((CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop).op ≫
          eqToHom hm_obj)) =
      eqToHom pX ≫ g.op ≫ eqToHom pY.symm := by
  -- Route correction: identify the underlying `CategoryOfElements` arrow first, then reapply
  -- double `op` and use the endpoint transports `pX` and `pY` only at the very end.
  let m :
      op (CostructuredArrow.mk (YonedaCollection.fst q)) ⟶
        op (CostructuredArrow.mk (YonedaCollection.fst qmap)) :=
    (CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop).op ≫
      eqToHom hm_obj
  have hfstqmap :
      YonedaCollection.fst qmap = yonedaEquiv.symm sY := by
    exact hidden_target_fst_eq_literal (ℱ := ℱ) (P := P) g q qmap hfstq hcostr hm_obj
  have hm_unop :
      (fromCostructuredArrow ℱ.obj).map m =
        CategoryTheory.CategoryOfElements.homMk
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))))
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))
          g.unop.val
          (by
            rw [hfstq, hfstqmap]
            simpa using CategoryTheory.CategoryOfElements.map_snd g.unop) := by
    simpa [m] using
      hidden_m_unop_maps_to_literal_homMk
        (ℱ := ℱ) (P := P) g q qmap hfstq hfstqmap hcostr hm_obj
  -- Once the source and target objects are identified with the literal elements-site objects,
  -- the opposite of `hm_unop` is exactly the desired transport-stable comparison.
  have pX_obj :
      (fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))) =
        Functor.elementsMk ℱ.obj X sX := by
    -- Rewrite the hidden source object to the literal costructured-arrow object over `sX`.
    apply elements_eq_of_double_op_eq (ℱ := ℱ)
    calc
      op (op ((fromCostructuredArrow ℱ.obj).obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q))))) =
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) := by
            rfl
      _ =
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (yonedaEquiv.symm sX)))) := by
            exact congrArg ((fromCostructuredArrow ℱ.obj).rightOp.op.obj)
              (congrArg op (congrArg CostructuredArrow.mk hfstq))
      _ = op (op (Functor.elementsMk ℱ.obj X sX)) := by
            exact fromCostructuredArrow_rightOp_op_obj_mk_eq_literal
              (ℱ := ℱ) (X := X) (s := sX)
  have pY_obj :
      (fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))) =
        Functor.elementsMk ℱ.obj Y sY := by
    -- The same object-level rewrite on the target side uses the normalized target first coordinate.
    apply elements_eq_of_double_op_eq (ℱ := ℱ)
    calc
      op (op ((fromCostructuredArrow ℱ.obj).obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))) =
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) := by
            rfl
      _ =
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (yonedaEquiv.symm sY)))) := by
            exact congrArg ((fromCostructuredArrow ℱ.obj).rightOp.op.obj)
              (congrArg op (congrArg CostructuredArrow.mk hfstqmap))
      _ = op (op (Functor.elementsMk ℱ.obj Y sY)) := by
            exact fromCostructuredArrow_rightOp_op_obj_mk_eq_literal
              (ℱ := ℱ) (X := Y) (s := sY)
  have hpX :
      pX =
        (by
          simpa [Functor.rightOp] using congrArg (fun z ↦ op (op z)) pX_obj) := by
    apply Subsingleton.elim
  have hpY :
      pY =
        (by
          simpa [Functor.rightOp] using congrArg (fun z ↦ op (op z)) pY_obj) := by
    apply Subsingleton.elim
  let pX_lit :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj X sX)) := by
    simpa [Functor.rightOp] using congrArg (fun z ↦ op (op z)) pX_obj
  let pY_lit :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) =
        op (op (Functor.elementsMk ℱ.obj Y sY)) := by
    simpa [Functor.rightOp] using congrArg (fun z ↦ op (op z)) pY_obj
  rw [hpX, hpY]
  have hbase :
      CategoryTheory.CategoryOfElements.homMk
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))))
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))
          g.unop.val
          (by
            rw [hfstq, hfstqmap]
            simpa using CategoryTheory.CategoryOfElements.map_snd g.unop) =
        eqToHom pX_obj ≫ g.unop ≫ eqToHom pY_obj.symm := by
    -- The underlying category-of-elements arrow is the literal base arrow `g.unop.val` with the
    -- source and target endpoint transports exposed separately.
    apply CategoryTheory.CategoryOfElements.ext ℱ.obj
    simp [category_of_elements_eqToHom_val, pX_obj, pY_obj]
  have hhomMk :
      (CategoryTheory.CategoryOfElements.homMk
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))))
          ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))
          g.unop.val
          (by
            rw [hfstq, hfstqmap]
            simpa using CategoryTheory.CategoryOfElements.map_snd g.unop)).op.op =
        eqToHom pX_lit ≫
          g.op ≫
          eqToHom pY_lit.symm := by
    -- Passing to the double opposite turns the base equality `hbase` into the target formula.
    simpa [Functor.rightOp, pX_lit, pY_lit] using congrArg (fun k ↦ k.op.op) hbase
  have hm_opop :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.map m) =
        (CategoryTheory.CategoryOfElements.homMk
            ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst q))))
            ((fromCostructuredArrow ℱ.obj).obj (op (CostructuredArrow.mk (YonedaCollection.fst qmap))))
            g.unop.val
            (by
              rw [hfstq, hfstqmap]
              simpa using CategoryTheory.CategoryOfElements.map_snd g.unop)).op.op := by
    simpa [Functor.rightOp, m] using congrArg (fun k ↦ k.op.op) hm_unop
  exact hm_opop.trans hhomMk

/-- Helper for Lemma 7.30.3: once the restricted Yoneda collection has been rewritten into the
literal `map₂` form, the remaining second-coordinate comparison is only the outer transport along
the chosen object equalities `pX` and `pY`. -/
theorem second_coordinate_transport_outer_cast_literal
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Cᵒᵖ} {sX : ℱ.obj.obj X} {sY : ℱ.obj.obj Y}
    (g : op (Functor.elementsMk ℱ.obj Y sY) ⟶ op (Functor.elementsMk ℱ.obj X sX))
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj X sX))))
    (q' : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj
      (op (op (Functor.elementsMk ℱ.obj Y sY))))
    (hq' :
      q' = ((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map g.op q)
    (pX :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj X sX)))
    (pY :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (YonedaCollection.fst q')))) =
        op (op (Functor.elementsMk ℱ.obj Y sY))) :
    cast (congrArg P.obj pY) (YonedaCollection.snd q') =
      P.map g.op (cast (congrArg P.obj pX) (YonedaCollection.snd q)) := by
  -- Route correction: after replacing `q'` by the explicit `map₂` term, the only remaining work
  -- is to rewrite the `fromCostructuredArrow` image of the composite map into the literal
  -- elements-site arrow `g`, and then collapse the three outer transports to `P.map g.op`.
  subst hq'
  have hcostr :
      CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ yonedaEquiv.symm sX) =
        CostructuredArrow.mk (yonedaEquiv.symm sY) :=
    restricted_costructured_arrow_eq_of_object_equalities
      (ℱ := ℱ) (P := P) g q pX pY
  -- TODO for Lemma 7.30.3: the remaining blocker is now isolated to the exact literal
  -- `YonedaCollection.map₂_snd` component term. Use the proved helpers
  -- `yoneda_collection_fst_eq_literal_of_object_equality` and
  -- `restricted_target_object_eq_literal` to rewrite the source and target objects, then compare
  -- the hidden `((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).map`
  -- morphism with `eqToHom (...) ≫ g.op ≫ eqToHom (...)` by unop-ing to
  -- `fromCostructuredArrow_map_mkPrecomp_cast_eq_literal`.
  have hfstq :
      YonedaCollection.fst q = yonedaEquiv.symm sX :=
    yoneda_collection_fst_eq_literal_of_object_equality (ℱ := ℱ) (P := P) q pX
  have pY' :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
          (op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)))) =
        op (op (Functor.elementsMk ℱ.obj Y sY)) :=
    restricted_target_object_eq_literal (ℱ := ℱ) (P := P) g q pY
  let qmap :=
    ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map g.op q
  have hm_obj :
      op (CostructuredArrow.mk (yoneda.map g.unop.val.unop ≫ YonedaCollection.fst q)) =
        op (CostructuredArrow.mk (YonedaCollection.fst qmap)) := by
    simp [qmap, YonedaCollection.map₂_fst]
  let m :=
    (CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop).op ≫
      eqToHom hm_obj
  have hm_unop :
      m.unop =
        eqToHom (congrArg unop hm_obj).symm ≫
          CostructuredArrow.mkPrecomp (YonedaCollection.fst q) g.unop.val.unop :=
    expanded_map2_snd_morphism_unop (ℱ := ℱ) (P := P) g q qmap hm_obj
  have hm :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.map m) =
        eqToHom pX ≫ g.op ≫ eqToHom pY.symm := by
    have pX_from :
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
            (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
          op (op (Functor.elementsMk ℱ.obj X sX)) := by
      simpa using pX
    have pY_from :
        ((fromCostructuredArrow ℱ.obj).rightOp.op.obj
            (op (CostructuredArrow.mk (YonedaCollection.fst qmap)))) =
          op (op (Functor.elementsMk ℱ.obj Y sY)) := by
      simpa [qmap, YonedaCollection.map₂_fst] using pY
    simpa [m] using
      fromCostructuredArrow_map_explicit_hidden_m_eq_literal
        (ℱ := ℱ) (P := P) g q pX_from hfstq qmap pY_from hcostr hm_obj
  -- TODO for Lemma 7.30.3: use `hm` to rewrite `YonedaCollection.map₂_snd` through
  -- `congrLeft_map_via_fromCostructuredArrow`, then normalize the remaining `Type`-valued functor
  -- transports from `eqToHom pX` and `eqToHom pY.symm` down to the literal `P.map g.op` action.
  -- The only remaining work here is this final cast collapse after the arrow-level blocker has
  -- been isolated as `fromCostructuredArrow_map_explicit_hidden_m_eq_literal`.
  change cast (congrArg P.obj pY) (YonedaCollection.snd qmap) =
    P.map g.op (cast (congrArg P.obj pX) (YonedaCollection.snd q))
  rw [show YonedaCollection.snd qmap =
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).map m
        (YonedaCollection.snd q) by
      simp [qmap, m, YonedaCollection.map₂_snd]]
  rw [congrLeft_map_via_fromCostructuredArrow, hm]
  rw [show eqToHom pX ≫ g.op ≫ eqToHom pY.symm =
      (eqToHom pX ≫ g.op) ≫ eqToHom pY.symm by simp [Category.assoc]]
  have hcomp_outer :
      P.map ((eqToHom pX ≫ g.op) ≫ eqToHom pY.symm) (YonedaCollection.snd q) =
        P.map (eqToHom pY.symm) (P.map (eqToHom pX ≫ g.op) (YonedaCollection.snd q)) := by
    simpa using
      (FunctorToTypes.map_comp_apply (F := P) (f := eqToHom pX ≫ g.op)
        (g := eqToHom pY.symm) (a := YonedaCollection.snd q))
  have hcomp_inner :
      P.map (eqToHom pX ≫ g.op) (YonedaCollection.snd q) =
        P.map g.op (P.map (eqToHom pX) (YonedaCollection.snd q)) := by
    simpa using
      (FunctorToTypes.map_comp_apply (F := P) (f := eqToHom pX)
        (g := g.op) (a := YonedaCollection.snd q))
  have hmap_pX :
      P.map g.op (P.map (eqToHom pX) (YonedaCollection.snd q)) =
        P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)) := by
    exact congrArg (fun f ↦ P.map g.op (f (YonedaCollection.snd q))) (eqToHom_map P pX)
  have hmap_pY :
      cast (congrArg P.obj pY)
        (P.map (eqToHom pY.symm)
          (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))) =
        cast (congrArg P.obj pY)
          (eqToHom (congrArg P.obj pY.symm)
            (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))) := by
    exact
      congrArg
        (fun f ↦ cast (congrArg P.obj pY)
          (f (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))))
        (eqToHom_map P pY.symm)
  -- After the hidden arrow is rewritten to the literal `g`, only the outer transport remains.
  calc
    cast (congrArg P.obj pY)
        (P.map ((eqToHom pX ≫ g.op) ≫ eqToHom pY.symm) (YonedaCollection.snd q)) =
      cast (congrArg P.obj pY)
        (P.map (eqToHom pY.symm) (P.map (eqToHom pX ≫ g.op) (YonedaCollection.snd q))) := by
          exact congrArg (fun z ↦ cast (congrArg P.obj pY) z) hcomp_outer
    _ =
      cast (congrArg P.obj pY)
        (P.map (eqToHom pY.symm) (P.map g.op (P.map (eqToHom pX) (YonedaCollection.snd q)))) := by
          exact
            congrArg
              (fun z ↦ cast (congrArg P.obj pY) (P.map (eqToHom pY.symm) z))
              hcomp_inner
    _ =
      cast (congrArg P.obj pY)
        (P.map (eqToHom pY.symm)
          (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))) := by
          exact
            congrArg
              (fun z ↦ cast (congrArg P.obj pY) (P.map (eqToHom pY.symm) z))
              hmap_pX
    _ =
      cast (congrArg P.obj pY)
        (eqToHom (congrArg P.obj pY.symm)
          (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))) := by
          exact hmap_pY
    _ = P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)) := by
          simpa using
            cast_eqToHom_cast rfl (congrArg P.obj pY.symm) (congrArg P.obj pY)
              (P.map g.op (eqToHom (congrArg P.obj pX) (YonedaCollection.snd q)))
    _ = P.map g.op (cast (congrArg P.obj pX) (YonedaCollection.snd q)) := by
          exact congrArg (P.map g.op)
            (eqToHom_eq_cast (h := congrArg P.obj pX) (x := YonedaCollection.snd q))

/-- Helper for Lemma 7.30.3: after restricting a Yoneda collection along an arrow in the category
of elements, reading the second coordinate over the tautological section agrees with applying
`P.map` to the original second coordinate. -/
theorem second_coordinate_transport_map2_literal
    {P : Eltᵒᵖ ⥤ Type v} {X Y : Elt} (g : Y ⟶ X)
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op X))
    (hq : q.yonedaEquivFst = (unop X).2) :
    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P)
        (((localizationProjection ℱ).op ⋙
            yonedaCollectionPresheaf ℱ.obj
              ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map g.op q)
        (mapped_fixed_first_coordinate (ℱ := ℱ) g q hq) =
      P.map g.op (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q hq) := by
  -- Route correction: first turn the first-coordinate equalities into equalities of objects in
  -- the category of elements, so the remaining goal isolates only the final cast normalization.
  cases X using Opposite.rec
  rename_i X
  cases Y using Opposite.rec
  rename_i Y
  cases X with
  | mk X sX =>
      cases Y with
      | mk Y sY =>
          let q' :=
            ((localizationProjection ℱ).op ⋙
                yonedaCollectionPresheaf ℱ.obj
                  ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).map
              g.op q
          have pX :
              ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
                  (op (CostructuredArrow.mk (YonedaCollection.fst q)))) =
                op (op ((⟨X, sX⟩ : ℱ.obj.Elements))) := by
            -- This packages `hq` as an equality of elements-site objects.
            change op (op ((⟨X, YonedaCollection.yonedaEquivFst q⟩ : ℱ.obj.Elements))) =
              op (op ((⟨X, sX⟩ : ℱ.obj.Elements)))
            exact
              elements_op_op_eq_of_section_eq (ℱ := ℱ)
                (X := X) (s := YonedaCollection.yonedaEquivFst q) (t := sX)
                (by simpa [YonedaCollection.yonedaEquivFst_eq] using hq)
          have pY :
              ((costructuredArrowYonedaEquivalence ℱ.obj).op.inverse.obj
                  (op (CostructuredArrow.mk (YonedaCollection.fst q')))) =
                op (op ((⟨Y, sY⟩ : ℱ.obj.Elements))) := by
            -- The restricted collection has the tautological first coordinate on `Y`.
            change op (op ((⟨Y, YonedaCollection.yonedaEquivFst q'⟩ : ℱ.obj.Elements))) =
              op (op ((⟨Y, sY⟩ : ℱ.obj.Elements)))
            exact
              elements_op_op_eq_of_section_eq (ℱ := ℱ)
                (X := Y) (s := YonedaCollection.yonedaEquivFst q') (t := sY)
                (by
                  simpa [q', YonedaCollection.yonedaEquivFst_eq] using
                    mapped_fixed_first_coordinate (ℱ := ℱ) (P := P) g q hq)
          -- The remaining obstruction is now exactly the comparison between the explicit cast
          -- coming from `pX`/`pY` and the literal morphism `g`.
          change cast (congrArg P.obj pY) (YonedaCollection.snd q') =
            P.map g.op (cast (congrArg P.obj pX) (YonedaCollection.snd q))
          -- The inner morphism transport has already been isolated, so only the outer casts remain.
          exact
            second_coordinate_transport_outer_cast_literal (ℱ := ℱ) (P := P) g q q' rfl pX pY

/-- Helper for Lemma 7.30.3: if two Yoneda collections over the same object are equal, then their
transported second coordinates over the tautological section are equal as well. -/
theorem second_coordinate_of_fixed_first_congr
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    {q₁ q₂ : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y)}
    (hq : q₁ = q₂)
    (hsec₁ : q₁.yonedaEquivFst = (unop Y).2)
    (hsec₂ : q₂.yonedaEquivFst = (unop Y).2) :
    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₁ hsec₁ =
      second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₂ hsec₂ := by
  -- After identifying the two collections, the remaining dependence on the section proof is
  -- proposition-valued and hence proof-irrelevant.
  cases hq
  have hproof : hsec₁ = hsec₂ := by
    apply Subsingleton.elim
  cases hproof
  rfl

/-- Helper for Lemma 7.30.3: a compatible family of Yoneda collections on the elements-site cover
whose first coordinate is already the tautological section yields a compatible family of second
coordinates in `P`. -/
theorem compatible_second_coordinates_of_fixed_first_coordinate
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt} {R : Sieve X}
    (w : Presieve.FamilyOfElements
      ((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) R.arrows)
    (hw : w.Compatible)
    (hfst : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X) (hg : R.arrows g), (w g hg).yonedaEquivFst = (unop Y).2)
    (y : Presieve.FamilyOfElements P R.arrows)
    (hy_def : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X) (hg : R.arrows g),
      y g hg = by
        let q := w g hg
        have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
        cases Y using Opposite.rec
        rename_i Y
        cases Y with
        | mk Y sY =>
            dsimp at hsec ⊢
            rw [← hsec]
            simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
              YonedaCollection.yonedaEquivFst_eq] using q.snd) :
    y.Compatible := by
  -- Route correction: compare the whole transported Yoneda collections first and only then
  -- project to the second coordinate after fixing the tautological first coordinate on `R`.
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
  cases Y₁ using Opposite.rec
  rename_i Y₁
  cases Y₂ using Opposite.rec
  rename_i Y₂
  cases Z using Opposite.rec
  rename_i Z
  cases Y₁ with
  | mk Y₁ s₁ =>
      cases Y₂ with
      | mk Y₂ s₂ =>
          cases Z with
          | mk Z sZ =>
              dsimp at *
              let F :=
                (localizationProjection ℱ).op ⋙
                  yonedaCollectionPresheaf ℱ.obj
                    ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ P)
              let p₁ := F.map g₁.op (w f₁ hf₁)
              let p₂ := F.map g₂.op (w f₂ hf₂)
              have hp : p₁ = p₂ := by
                -- Compatibility on `w` gives the equality of the two restricted Yoneda collections.
                simpa [F, p₁, p₂] using
                  pulled_back_yoneda_collection_eq_of_compatible (ℱ := ℱ) w hw f₁ hf₁ f₂ hf₂ g₁ g₂ h
              have hsec₁ : p₁.yonedaEquivFst = sZ := by
                -- The first restricted family already lies over the tautological section of `Z`.
                simpa [F, p₁] using
                  mapped_fixed_first_coordinate (ℱ := ℱ) g₁ (w f₁ hf₁) (hfst f₁ hf₁)
              have hsec₂ : p₂.yonedaEquivFst = sZ := by
                -- The second restricted family lies over the same tautological section.
                simpa [F, p₂] using
                  mapped_fixed_first_coordinate (ℱ := ℱ) g₂ (w f₂ hf₂) (hfst f₂ hf₂)
              have hp_snd :
                  second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₁ hsec₁ =
                    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₂ hsec₂ := by
                -- The two restricted Yoneda collections are equal, so their tautological second
                -- coordinates agree after the same first-coordinate identification.
                exact second_coordinate_of_fixed_first_congr (ℱ := ℱ) (P := P) hp hsec₁ hsec₂
              have hp₁ :
                  second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₁ hsec₁ =
                    P.map g₁.op (y f₁ hf₁) := by
                -- Rewrite the first restricted family to the literal `P.map g₁.op (...)` form.
                rw [hy_def f₁ hf₁]
                simpa [F, p₁] using
                  second_coordinate_transport_map2_literal (ℱ := ℱ) (P := P) g₁ (w f₁ hf₁)
                    (hfst f₁ hf₁)
              have hp₂ :
                  second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₂ hsec₂ =
                    P.map g₂.op (y f₂ hf₂) := by
                -- Rewrite the second restricted family to the literal `P.map g₂.op (...)` form.
                rw [hy_def f₂ hf₂]
                simpa [F, p₂] using
                  second_coordinate_transport_map2_literal (ℱ := ℱ) (P := P) g₂ (w f₂ hf₂)
                    (hfst f₂ hf₂)
              -- Compare the whole restricted Yoneda collections first, then project to second
              -- coordinates only after fixing their common first coordinate.
              calc
                P.map g₁.op (y f₁ hf₁) =
                    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₁ hsec₁ := by
                      symm
                      exact hp₁
                _ = second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) p₂ hsec₂ := hp_snd
                _ = P.map g₂.op (y f₂ hf₂) := hp₂

/-- Helper for Lemma 7.30.3: the cast-free local second-coordinate family on the pulled-back
elements-site cover is compatible as soon as the original Yoneda-collection family is compatible.
-/
theorem explicit_second_coordinate_family_compatible
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt} {R : Sieve X}
    (w : Presieve.FamilyOfElements
      ((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) R.arrows)
    (hw : w.Compatible)
    (hfst : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X) (hg : R.arrows g), (w g hg).yonedaEquivFst = (unop Y).2) :
    let y : R.arrows.FamilyOfElements P := fun Y g hg => by
      let q := w g hg
      have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
      cases Y using Opposite.rec
      rename_i Y
      cases Y with
      | mk Y sY =>
          dsimp at hsec ⊢
          rw [← hsec]
          simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
            YonedaCollection.yonedaEquivFst_eq] using q.snd
    y.Compatible := by
  let y : R.arrows.FamilyOfElements P := fun Y g hg => by
    let q := w g hg
    have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
    cases Y using Opposite.rec
    rename_i Y
    cases Y with
    | mk Y sY =>
        dsimp at hsec ⊢
        rw [← hsec]
        simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
          YonedaCollection.yonedaEquivFst_eq] using q.snd
  -- The explicit family is exactly the one handled by the general fixed-first-coordinate
  -- compatibility lemma, so the proof is just that lemma with the defining formula for `y`.
  have hy_def : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X) (hg : R.arrows g),
      y g hg = by
        let q := w g hg
        have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
        cases Y using Opposite.rec
        rename_i Y
        cases Y with
        | mk Y sY =>
            dsimp at hsec ⊢
            rw [← hsec]
            simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
              YonedaCollection.yonedaEquivFst_eq] using q.snd := by
    intro Y g hg
    rfl
  exact
    compatible_second_coordinates_of_fixed_first_coordinate
      (ℱ := ℱ) (P := P) w hw hfst y hy_def

/-- Helper for Lemma 7.30.3: the canonical glued pair has the expected first coordinate after
restriction along a base arrow. -/
theorem canonical_lift_map₂_fst
    {P : Eltᵒᵖ ⥤ Type v} {U Y : C} {s : ℱ.obj.obj (op U)}
    (f : Y ⟶ U)
    {t' :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).obj
        (op (CostructuredArrow.mk (yonedaEquiv.symm s)))}
    {q : YonedaCollection
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P) Y}
    (hs : ℱ.obj.map f.op s = q.yonedaEquivFst) :
    (YonedaCollection.map₂
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P) f
        (YonedaCollection.mk (yonedaEquiv.symm s) t')).fst =
      q.fst := by
  -- The first coordinate is exactly the Yoneda arrow determined by the glued base section.
  simpa using yoneda_map_symm_eq_of_map_eq (ℱ := ℱ) f (t := q.fst) hs

/-- Helper for Lemma 7.30.3: the canonical glued Yoneda collection over `(U, s)` lies over the
tautological section `s`. -/
theorem canonical_glued_collection_yonedaEquivFst
    {P : Eltᵒᵖ ⥤ Type v} {U : C} {s : ℱ.obj.obj (op U)}
    {t' :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).obj
        (op (CostructuredArrow.mk (yonedaEquiv.symm s)))} :
    (YonedaCollection.mk (yonedaEquiv.symm s) t').yonedaEquivFst = s := by
  -- The first component of `YonedaCollection.mk` is definitionally the chosen section.
  simp [YonedaCollection.yonedaEquivFst_eq]

/-- Helper for Lemma 7.30.3: reinterpreting a section of `P` over an elements-site object as a
section over the corresponding costructured arrow is the explicit definitional cast. -/
theorem canonical_glued_section_eq_cast
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt} (t : P.obj (op X)) :
    (show
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).obj
            (op (CostructuredArrow.mk (yonedaEquiv.symm (unop X).2))) from
          by
            simpa using t) =
      cast (by simp) t := by
  -- The equivalence identifies the fiber object over `X` with `P.obj (op X)` definitionally.
  rfl

/-- Helper for Lemma 7.30.3: the explicit category-of-elements identity arrow becomes the literal
identity after one passage to the opposite category. -/
theorem elements_op_identity_literal
    (Xelt : ℱ.obj.Elements) :
    Quiver.Hom.op (𝟙 Xelt) = (𝟙 (Opposite.op Xelt) : Opposite.op Xelt ⟶ Opposite.op Xelt) := by
  -- Both sides are definitionally the identity morphism in the opposite of the category of
  -- elements.
  rfl

/-- Helper for Lemma 7.30.3: if two elements become equal after transport to a common fiber, then
transporting one directly to the other fiber recovers the raw equality. -/
theorem eqToHom_of_cast_eq
    {α β γ : Type v} {x : α} {y : β}
    (h₁ : α = γ) (h₂ : β = γ)
    (h : cast h₁ x = cast h₂ y) :
    eqToHom (h₂.trans h₁.symm) y = x := by
  -- Once the common-fiber equalities are eliminated, the statement is exactly `h.symm`.
  cases h₁
  cases h₂
  simpa using h.symm

/-- Helper for Lemma 7.30.3: the tautological second coordinate of the canonical glued collection
recovers the original section of `P`. -/
theorem canonical_glued_second_coordinate_eq_raw
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt}
    {t : P.obj (op X)}
    {t' :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).obj
        (op (CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)))}
    (ht' : t' = cast (by simp) t) :
    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P)
      (YonedaCollection.mk (yonedaEquiv.symm (unop X).2) t')
      (by
        simpa using
          (canonical_glued_collection_yonedaEquivFst (ℱ := ℱ) (P := P)
            (s := (unop X).2) (t' := t'))) = t := by
  -- Route correction: once `t'` is the explicit cast of `t`, the canonical glued collection has
  -- the tautological first coordinate, so the remaining transport is the identity after unpacking
  -- the element-site object `X`.
  subst ht'
  cases X using Opposite.rec
  rename_i X
  cases X with
  | mk U s =>
      -- After expanding the `mk` second component, the only map left is an `eqToHom`, so the
      -- remaining transport is computed by `eqToHom_map`.
      rw [second_coordinate_of_fixed_first, YonedaCollection.mk_snd, eqToHom_map]
      exact cast_eqToHom_cast _ _ _ t

/-- Helper for Lemma 7.30.3: after rewriting both first coordinates to the tautological section on
the same elements-site object, equality of extracted second coordinates is exactly the raw
second-component equality needed by `YonedaCollection.ext`. -/
theorem common_fiber_cast_cancel
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    {q₁ q₂ : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y)}
    (hsec₁ : q₁.yonedaEquivFst = (unop Y).2)
    (hsec₂ : q₂.yonedaEquivFst = (unop Y).2)
    (hfst : q₁.fst = q₂.fst)
    (hsecond :
      second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₁ hsec₁ =
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₂ hsec₂) :
    ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).map
        (eqToHom (by rw [hfst])) (YonedaCollection.snd q₂) =
      YonedaCollection.snd q₁ := by
  -- Once `Y = op ⟨op U, s⟩` is unpacked, the transport in `second_coordinate_of_fixed_first`
  -- is exactly the same `eqToHom` transport appearing in `YonedaCollection.ext`.
  cases Y using Opposite.rec
  rename_i Y
  cases Y with
  | mk U s =>
      rw [eqToHom_map]
      exact eqToHom_of_cast_eq _ _
        (by
          simpa [second_coordinate_of_fixed_first, second_coordinate_of_fixed_first_index,
            YonedaCollection.yonedaEquivFst_eq, hsec₁, hsec₂, hfst] using hsecond)

/-- Helper for Lemma 7.30.3: two Yoneda collections over the same elements-site object are equal
once they have the same tautological first coordinate and the same second coordinate in that
common fiber. -/
theorem yoneda_collection_ext_second_of_common_section
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    {q₁ q₂ : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y)}
    (hsec₁ : q₁.yonedaEquivFst = (unop Y).2)
    (hsec₂ : q₂.yonedaEquivFst = (unop Y).2)
    (hsecond :
      second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₁ hsec₁ =
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q₂ hsec₂) :
    q₁ = q₂ := by
  -- Route correction: the common tautological section determines the first coordinate, and after
  -- unpacking `Y` the second-coordinate comparison is exactly the raw sigma equality.
  have hfst :
      q₁.fst = q₂.fst :=
    (yoneda_collection_fst_eq_of_yonedaEquivFst_eq (ℱ := ℱ) q₁ hsec₁).trans
      (yoneda_collection_fst_eq_of_yonedaEquivFst_eq (ℱ := ℱ) q₂ hsec₂).symm
  cases Y using Opposite.rec
  rename_i Y
  cases Y with
  | mk U s =>
      refine YonedaCollection.ext hfst ?_
      exact common_fiber_cast_cancel (ℱ := ℱ) (P := P) hsec₁ hsec₂ hfst hsecond

/-- Helper for Lemma 7.30.3: changing only the proof witness for the same fixed first coordinate
does not change the extracted second coordinate. -/
theorem second_coordinate_of_fixed_first_proof_irrel
    {P : Eltᵒᵖ ⥤ Type v} {Y : Elt}
    (q : ((localizationProjection ℱ).op ⋙
      yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op Y))
    {hsec₁ hsec₂ : q.yonedaEquivFst = (unop Y).2} :
    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q hsec₁ =
      second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) q hsec₂ := by
  -- The dependence on the section witness is proposition-valued, so the two extractions agree.
  have hproof : hsec₁ = hsec₂ := by
    apply Subsingleton.elim
  cases hproof
  rfl

/-- Helper for Lemma 7.30.3: on the pulled-back cover, the abstract extracted second coordinate
agrees with the explicit local fiber formula used in the compatibility argument. -/
theorem pulled_back_second_coordinate_eq_explicit
    {P : Eltᵒᵖ ⥤ Type v} {X : Elt} {R : Sieve X}
    (w : Presieve.FamilyOfElements
      ((localizationProjection ℱ).op ⋙
        yonedaCollectionPresheaf ℱ.obj
          ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) R.arrows)
    (hfst : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X) (hg : R.arrows g), (w g hg).yonedaEquivFst = (unop Y).2)
    {Y : Elt} (g : Y ⟶ X) (hg : R.arrows g) :
    second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) (w g hg) (hfst g hg) =
      (by
        let q := w g hg
        have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
        cases Y using Opposite.rec
        rename_i Y
        cases Y with
        | mk Y sY =>
            dsimp at hsec ⊢
            rw [← hsec]
            simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
              YonedaCollection.yonedaEquivFst_eq] using q.snd) := by
  -- Unpack the source object of the pulled-back arrow once so the dependent cast becomes the
  -- literal fiberwise formula used elsewhere in the sheaf proof.
  unfold second_coordinate_of_fixed_first
  cases Y using Opposite.rec
  rename_i Y
  cases Y with
  | mk Y sY =>
      dsimp
      rfl

/-- Helper for Lemma 7.30.3: any amalgamation of the local family has the same first coordinate as
the section glued in `ℱ`. -/
theorem amalgamation_first_coordinate_eq
    {P : Eltᵒᵖ ⥤ Type v} {U : C} {S : Sieve U}
    (x : Presieve.FamilyOfElements
      (yonedaCollectionPresheaf ℱ.obj
        ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)) S.arrows)
    (hsheafF : Presieve.IsSheafFor ℱ.obj S.arrows)
    (s : ℱ.obj.obj (op U))
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ U) (hf : S.arrows f),
      ℱ.obj.map f.op s = (x f hf).yonedaEquivFst)
    (z : (yonedaCollectionPresheaf ℱ.obj
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)).obj (op U))
    (hz : x.IsAmalgamation z) :
    z.yonedaEquivFst = s := by
  -- Separatedness on `ℱ` determines the first coordinate once all restrictions agree with `x`.
  apply hsheafF.isSeparatedFor.ext
  intro Y f hf
  calc
    ℱ.obj.map f.op z.yonedaEquivFst = (x f hf).yonedaEquivFst := by
      simpa using congrArg YonedaCollection.yonedaEquivFst (hz f hf)
    _ = ℱ.obj.map f.op s := by
      symm
      exact hs f hf

theorem sheafCategoryOfElementsFunctorObj_isSheaf
    (P : Eltᵒᵖ ⥤ Type v)
    (hP : Presheaf.IsSheaf Jₑ P) :
    Presheaf.IsSheaf J
      ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P).left := by
  -- Route correction: glue the first coordinates in `ℱ`, then pull the cover back to the elements
  -- site and prepare the second-coordinate family on that pulled-back cover.
  let Q :=
    yonedaCollectionPresheaf ℱ.obj
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P)
  change Presheaf.IsSheaf J Q
  rw [isSheaf_iff_isSheaf_of_type]
  intro U S hS
  intro x hx
  let x₁ : S.arrows.FamilyOfElements ℱ.obj := fun Y f hf ↦ (x f hf).yonedaEquivFst
  have hx₁ : x₁.Compatible := by
    -- Compatibility of the local Yoneda collections gives compatibility of their first coordinates.
    rw [Presieve.compatible_iff_sieveCompatible] at hx ⊢
    intro Y Z f g hf
    simpa [x₁, Q] using congrArg YonedaCollection.yonedaEquivFst (hx f g hf)
  let hℱ : Presieve.IsSheaf J ℱ.obj := (isSheaf_iff_isSheaf_of_type J ℱ.obj).1 ℱ.property
  let hℱS := hℱ S hS
  let s := hℱS.amalgamate x₁ hx₁
  have hs : ∀ ⦃Y : C⦄ (f : Y ⟶ U) (hf : S.arrows f),
      ℱ.obj.map f.op s = (x f hf).yonedaEquivFst := by
    -- The glued section in `ℱ` matches the first coordinate of each local datum.
    intro Y f hf
    exact hℱS.valid_glue hx₁ f hf
  let X₀ : Elt := op ⟨op U, s⟩
  let R : Sieve X₀ := Sieve.functorPullback (F := localizationProjection ℱ) (X := X₀) S
  have hR : R ∈ Jₑ X₀ := by
    -- The pulled-back sieve covers in the elements site because its pushforward refines `S`.
    simpa [R, localizationTopology] using
      (J.superset_covering (localizationProjection_cover_lift (ℱ := ℱ) X₀ S) hS)
  let w : R.arrows.FamilyOfElements (((localizationProjection ℱ).op) ⋙ Q) :=
    fun Y g hg ↦ x ((localizationProjection ℱ).map g) (by simpa [R] using hg)
  have hw : w.Compatible := by
    -- Pulling the family back along the projection preserves compatibility.
    rw [Presieve.compatible_iff_sieveCompatible] at hx ⊢
    intro Y Z f g hf
    simpa [w, R, Q, Functor.comp_map] using
      hx ((localizationProjection ℱ).map f) ((localizationProjection ℱ).map g) (by simpa [R] using hf)
  have hfst : ∀ ⦃Y : Elt⦄ (g : Y ⟶ X₀) (hg : R.arrows g), (w g hg).yonedaEquivFst = (unop Y).2 := by
    -- Each pulled-back local datum already lies over the tautological section of its source.
    intro Y g hg
    simpa [w, R] using
      pulled_back_local_family_first_coordinate (ℱ := ℱ) (P := P) x (s := s) hs g hg
  let y : R.arrows.FamilyOfElements P :=
    fun Y g hg => by
      let q := w g hg
      have hsec : q.yonedaEquivFst = (unop Y).2 := hfst g hg
      cases Y using Opposite.rec
      rename_i Y
      cases Y with
      | mk Y sY =>
          dsimp at hsec ⊢
          rw [← hsec]
          simpa [sheafCategoryOfElementsPresheafEquivOverPresheaf,
            YonedaCollection.yonedaEquivFst_eq] using q.snd
  have hy : y.Compatible := by
    -- The pulled-back family already has tautological first coordinate, so the explicit
    -- fiberwise second-coordinate formula is compatible on the pulled-back cover.
    simpa [y] using
      explicit_second_coordinate_family_compatible (ℱ := ℱ) (P := P) w hw hfst
  let hPR := (isSheaf_iff_isSheaf_of_type Jₑ P).1 hP R hR
  let t : P.obj (op X₀) := hPR.amalgamate y hy
  have ht : y.IsAmalgamation t := by
    -- The glued section in `P` restricts back to the explicit family by the sheaf axiom on `R`.
    exact hPR.isAmalgamation hy
  let t' :
      ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft.functor.obj P).obj
        (op (CostructuredArrow.mk (yonedaEquiv.symm s))) := by
    simpa [X₀] using t
  have ht' : t' = cast (by simp [X₀]) t := by
    -- The canonical identification of the fiber over `(U, s)` is the explicit cast used by
    -- `YonedaCollection.mk`.
    simpa [t', X₀] using canonical_glued_section_eq_cast (ℱ := ℱ) (P := P) (X := X₀) t
  let z : Q.obj (op U) := YonedaCollection.mk (yonedaEquiv.symm s) t'
  let z₀ : (((localizationProjection ℱ).op ⋙ Q).obj (op X₀)) := by
    simpa [Q, X₀, localizationProjection] using z
  have hz_sec : z.yonedaEquivFst = s := by
    -- The canonical glued collection over `(U, s)` has the prescribed first coordinate.
    simpa [z] using
      canonical_glued_collection_yonedaEquivFst (ℱ := ℱ) (P := P) (s := s)
        (t' := t')
  have hz₀_sec : z₀.yonedaEquivFst = (unop X₀).2 := by
    simpa [z₀, X₀] using hz_sec
  have hz_second :
      second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z₀ hz₀_sec = t := by
    -- Its tautological second coordinate is exactly the glued section `t`.
    simpa [z₀, z] using
      canonical_glued_second_coordinate_eq_raw (ℱ := ℱ) (P := P) (X := X₀)
        (t := t) (t' := t') ht'
  refine ⟨z, ?_, ?_⟩
  · intro Y f hf
    let Y₀ : Elt := op ⟨op Y, ℱ.obj.map f.op s⟩
    let g : Y₀ ⟶ X₀ :=
      Quiver.Hom.op (CategoryOfElements.homMk (unop X₀) (unop Y₀) f.op rfl)
    have hg : R.arrows g := by
      -- This is the canonical lifted arrow of `f` to the elements-site pullback cover.
      simpa [R, g, localizationProjection]
        using hf
    have hf' : S.arrows ((localizationProjection ℱ).map g) := by
      simpa [R] using hg
    have hfg : (localizationProjection ℱ).map g = f := by
      simp [g, localizationProjection]
    let xg : Q.obj (op Y) := x ((localizationProjection ℱ).map g) hf'
    let xg₀ : (((localizationProjection ℱ).op ⋙ Q).obj (op Y₀)) := by
      simpa [Q, Y₀, localizationProjection] using xg
    have hxg_eq : xg = x f hf := by
      dsimp [xg]
      cases hfg
      have hhf : hf' = hf := by
        apply Subsingleton.elim
      cases hhf
      rfl
    have hz_map_sec :
        (Q.map f.op z).yonedaEquivFst = (unop Y₀).2 := by
      -- Restricting `z` along `f` lands over the tautological pulled-back section.
      simpa [Q, z, Y₀, YonedaCollection.map₂_yonedaEquivFst]
        using congrArg (fun t ↦ ℱ.obj.map f.op t) hz_sec
    let zg₀ : (((localizationProjection ℱ).op ⋙ Q).obj (op Y₀)) :=
      ((localizationProjection ℱ).op ⋙ Q).map g.op z₀
    have hzg₀_sec : zg₀.yonedaEquivFst = (unop Y₀).2 := by
      simpa [zg₀, z₀, Q, g, Y₀, localizationProjection] using hz_map_sec
    have hx_sec :
        (x f hf).yonedaEquivFst = (unop Y₀).2 := by
      -- The local datum `x f hf` has the same first coordinate by construction of `s`.
      simpa [Y₀] using (hs f hf).symm
    have hxg₀_sec : xg₀.yonedaEquivFst = (unop Y₀).2 := by
      simpa [xg₀, xg, Y₀] using hfst g hg
    have hz_map_second :
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) zg₀ hzg₀_sec = y g hg := by
      -- The second coordinate of the canonical glued pair restricts to the glued family `y`.
      calc
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) zg₀ hzg₀_sec =
            P.map g.op (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z₀
              hz₀_sec) := by
                simpa [zg₀] using
                  second_coordinate_transport_map2_literal (ℱ := ℱ) (P := P) g z₀ hz₀_sec
        _ = P.map g.op t := by rw [hz_second]
        _ = y g hg := ht g hg
    have hx_second :
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) xg₀ hxg₀_sec =
          y g hg := by
      have hw_eq : w g hg = xg₀ := by
        -- The pulled-back family `w` is literally the original family evaluated at the base arrow
        -- underlying `g`.
        rfl
      -- Rewriting through `w g hg` identifies the abstract fixed-second-coordinate extractor with
      -- the explicit family `y`.
      calc
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) xg₀ hxg₀_sec =
            second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) (w g hg) (hfst g hg) := by
              exact second_coordinate_of_fixed_first_congr (ℱ := ℱ) (P := P)
                hw_eq.symm hxg₀_sec (hfst g hg)
        _ = y g hg := pulled_back_second_coordinate_eq_explicit (ℱ := ℱ) (P := P) w hfst g hg
    -- Equality of first and second coordinates over the common section gives the local restriction.
    have hmap_eq_xg :
        Q.map f.op z = xg := by
      have hcomp :
          zg₀ = xg₀ :=
        yoneda_collection_ext_second_of_common_section (ℱ := ℱ) (P := P)
          (Y := Y₀) hzg₀_sec hxg₀_sec (hz_map_second.trans hx_second.symm)
      simpa [zg₀, z₀, xg₀, Q, g, Y₀, localizationProjection] using hcomp
    exact hmap_eq_xg.trans hxg_eq
  · intro z' hz'
    let z'₀ : (((localizationProjection ℱ).op ⋙ Q).obj (op X₀)) := by
      simpa [Q, X₀, localizationProjection] using z'
    have hz'_sec : z'.yonedaEquivFst = s := by
      -- Any amalgamation has the same first coordinate as the glued section in `ℱ`.
      exact amalgamation_first_coordinate_eq (ℱ := ℱ) (P := P) x hℱS s hs z' hz'
    have hz'₀_sec : z'₀.yonedaEquivFst = (unop X₀).2 := by
      simpa [z'₀, X₀] using hz'_sec
    have hz'_second_local :
        ∀ ⦃Y₁ : Elt⦄ (g : Y₁ ⟶ X₀) (hg : R.arrows g),
          P.map g.op
              (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z'₀ hz'₀_sec) =
            y g hg := by
      intro Y₁ g hg
      have hz'_map_eq :
          ((localizationProjection ℱ).op ⋙ Q).map g.op z'₀ = w g hg := by
        -- Since `z'` amalgamates `x`, its restriction along the lifted arrow is the pulled-back
        -- local datum `w g hg`.
        simpa [z'₀, w, R] using hz' ((localizationProjection ℱ).map g) (by simpa [R] using hg)
      have hz'_map_sec :
          ((((localizationProjection ℱ).op ⋙ Q).map g.op z'₀).yonedaEquivFst) = (unop Y₁).2 := by
        -- Restricting `z'` along `g` preserves the tautological first coordinate of `Y₁`.
        simpa [Q] using
          mapped_fixed_first_coordinate (ℱ := ℱ) (P := P) g z'₀ hz'₀_sec
      have hz'_map_second :
          second_coordinate_of_fixed_first (ℱ := ℱ) (P := P)
              (((localizationProjection ℱ).op ⋙ Q).map g.op z'₀) hz'_map_sec =
            P.map g.op
              (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z'₀ hz'₀_sec) := by
        -- The restriction formula for second coordinates is the same one used in the existence
        -- branch, now applied to `z'`.
        simpa [Q] using
          second_coordinate_transport_map2_literal (ℱ := ℱ) (P := P) g z'₀ hz'₀_sec
      have hw_second :
          second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) (w g hg) (hfst g hg) =
            y g hg := by
        -- The explicit pulled-back family `y` was defined from `w` by reading this same fixed
        -- second coordinate.
        exact pulled_back_second_coordinate_eq_explicit (ℱ := ℱ) (P := P) w hfst g hg
      calc
        P.map g.op
            (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z'₀ hz'₀_sec) =
          second_coordinate_of_fixed_first (ℱ := ℱ) (P := P)
              (((localizationProjection ℱ).op ⋙ Q).map g.op z'₀) hz'_map_sec := by
                symm
                exact hz'_map_second
        _ = second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) (w g hg) (hfst g hg) := by
              exact second_coordinate_of_fixed_first_congr (ℱ := ℱ) (P := P) hz'_map_eq
                hz'_map_sec (hfst g hg)
        _ = y g hg := hw_second
    have hz'_second :
        second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z'₀ hz'₀_sec = t := by
      -- The pulled-back restrictions of `z'` and `t` agree on the covering sieve `R`, so
      -- separatedness of `P` on `R` identifies their global second coordinates.
      apply hPR.isSeparatedFor.ext
      intro Y₁ g hg
      calc
        P.map g.op
            (second_coordinate_of_fixed_first (ℱ := ℱ) (P := P) z'₀ hz'₀_sec) = y g hg :=
              hz'_second_local g hg
        _ = P.map g.op t := by symm; exact ht g hg
    -- Matching first coordinates and matching tautological second coordinates determine `z'`.
    have hcomp :
        z'₀ = z₀ :=
      yoneda_collection_ext_second_of_common_section (ℱ := ℱ) (P := P)
        (Y := X₀) hz'₀_sec hz₀_sec
        (hz'_second.trans hz_second.symm)
    simpa [z'₀, z₀, Q, X₀, localizationProjection] using hcomp

theorem sheafCategoryOfElementsPresheafEquivOverPresheaf_obj_isSheaf_iff
    (P : Eltᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf J
        ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P).left ↔
      Presheaf.IsSheaf Jₑ P := by
  constructor
  · intro hP
    let e := (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).unitIso.app P
    exact
      (Presheaf.isSheaf_of_iso_iff e).2
        (sheafCategoryOfElementsInverseObj_isSheaf ℱ
          ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P) hP)
  · intro hP
    exact sheafCategoryOfElementsFunctorObj_isSheaf ℱ P hP

theorem sheafCategoryOfElementsPresheafEquivOverPresheaf_inverseImage :
    (overPresheafHasSheafDomain ℱ).inverseImage
        (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor =
      Presheaf.IsSheaf Jₑ := by
  ext P
  simpa [overPresheafHasSheafDomain, ObjectProperty.prop_inverseImage_iff] using
    sheafCategoryOfElementsPresheafEquivOverPresheaf_obj_isSheaf_iff ℱ P

/-- Lemma 7.30.3 (3): there is an equivalence between sheaves on the site of elements of `ℱ` and
objects of `Sh(C, J)` over `ℱ`. -/
noncomputable def sheafCategoryOfElementsEquivOver :
    Sheaf Jₑ (Type v) ≌ Over ℱ :=
  (Equivalence.congrFullSubcategory
      (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ)
      (sheafCategoryOfElementsPresheafEquivOverPresheaf_inverseImage ℱ)).trans
    (overPresheafHasSheafDomainEquivOver ℱ)

/-- Helper for Lemma 7.30.3: after unfolding the inverse side of
`sheafCategoryOfElementsEquivOver ℱ`, the displayed triple wrapper of
`overEquivPresheafCostructuredArrow.inverse.map` is exactly the literal
`YonedaCollection.map₁` for `η.hom`. -/
theorem overEquiv_inverse_wrapper_component_eq_map1
    {G G' : Sheaf J (Type v)} (η : G ⟶ G') (X : Cᵒᵖ)
    (x : (((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
      (sheafCategoryOfElementsEquivOver ℱ).functor).obj G).left.obj.obj X) :
    (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
            ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
              (localizationProjection ℱ).op G'.obj).hom).left.app
      X
      (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
              (Functor.whiskerLeft
                ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ (localizationProjection ℱ).op)
                η.hom)).left.app
        X
        (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
                ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
                    (localizationProjection ℱ).op G.obj).inv).left.app
            X x))) =
      YonedaCollection.map₁
        (Functor.whiskerLeft ((CostructuredArrow.proj yoneda ℱ.obj).op) η.hom) x := by
  -- The inverse functor on presheaves-over-`ℱ.obj` acts on the left component by
  -- `YonedaCollection.map₁`, and the associator corrections reduce to the literal whiskered map.
  change
      YonedaCollection.map₁
          ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
            (localizationProjection ℱ).op G'.obj).hom
          (YonedaCollection.map₁
            (Functor.whiskerLeft
              ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ (localizationProjection ℱ).op)
              η.hom)
            (YonedaCollection.map₁
              ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
                (localizationProjection ℱ).op G.obj).inv x)) =
        YonedaCollection.map₁
          (Functor.whiskerLeft ((CostructuredArrow.proj yoneda ℱ.obj).op) η.hom) x
  have hassoc_inv :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
          (localizationProjection ℱ).op G.obj).inv = 𝟙 _ := by
    ext Y y
    rfl
  have hassoc_hom :
      ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
          (localizationProjection ℱ).op G'.obj).hom = 𝟙 _ := by
    ext Y y
    rfl
  rw [hassoc_inv, hassoc_hom]
  have hid_inner :
      YonedaCollection.map₁ (𝟙 ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
            (localizationProjection ℱ).op ⋙ G.obj)) x = x := by
    exact
      congrFun
        (YonedaCollection.map₁_id
          (F := (fromCostructuredArrow ℱ.obj).rightOp.op ⋙
            (localizationProjection ℱ).op ⋙ G.obj)
          (X := X.unop))
        x
  have hmid :
      YonedaCollection.map₁
          (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
              (localizationProjection ℱ).op).whiskerLeft η.hom)
          (YonedaCollection.map₁
            (𝟙 ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
                (localizationProjection ℱ).op ⋙ G.obj)) x) =
        YonedaCollection.map₁
          (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
              (localizationProjection ℱ).op).whiskerLeft η.hom) x := by
    exact
      congrArg
        (YonedaCollection.map₁
          (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
              (localizationProjection ℱ).op).whiskerLeft η.hom))
        hid_inner
  rw [hmid]
  have hid_outer :
      YonedaCollection.map₁
          (𝟙 (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
                (localizationProjection ℱ).op) ⋙ G'.obj))
          (YonedaCollection.map₁
            (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
                (localizationProjection ℱ).op).whiskerLeft η.hom) x) =
        YonedaCollection.map₁
          (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
              (localizationProjection ℱ).op).whiskerLeft η.hom) x := by
    exact
      congrFun
        (YonedaCollection.map₁_id
          (F := ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
            (localizationProjection ℱ).op) ⋙ G'.obj)
          (X := X.unop))
        (YonedaCollection.map₁
          (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙
              (localizationProjection ℱ).op).whiskerLeft η.hom) x)
  refine hid_outer.trans ?_
  have hproj :
      ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ (π ℱ.obj).leftOp.op) =
        (CostructuredArrow.proj yoneda ℱ.obj).op := by
    rfl
  have hwhisker :
      (((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ (π ℱ.obj).leftOp.op).whiskerLeft η.hom) =
        ((CostructuredArrow.proj yoneda ℱ.obj).op.whiskerLeft η.hom) := by
    cases hproj
    rfl
  rw [hwhisker]
  rfl

/-- Helper for Lemma 7.30.3: the remaining inverse-image comparison is the explicit componentwise
normalization of the `overEquivPresheafCostructuredArrow.inverse.map` wrapper around
`yonedaCollectionProjIsoToOverLeft`. -/
theorem inverse_map_toOverCompYoneda_component_normalize
    {G G' : Sheaf J (Type v)} (η : G ⟶ G') (X : Cᵒᵖ)
    (x : (((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
      (sheafCategoryOfElementsEquivOver ℱ).functor).obj G).left.obj.obj X) :
    (yonedaCollectionProjIsoToOverLeft ℱ.obj G'.obj).hom.app X
        (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
                ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
                  (localizationProjection ℱ).op G'.obj).hom).left.app
          X
          (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
                  (Functor.whiskerLeft
                    ((fromCostructuredArrow ℱ.obj).rightOp.op ⋙ (localizationProjection ℱ).op)
                    η.hom)).left.app
            X
          (((overEquivPresheafCostructuredArrow ℱ.obj).inverse.map
                  ((fromCostructuredArrow ℱ.obj).rightOp.op.associator
                      (localizationProjection ℱ).op G.obj).inv).left.app
              X x))) =
      (η.hom.app X ((yonedaCollectionProjIsoToOverLeft ℱ.obj G.obj).hom.app X x).1,
        ((yonedaCollectionProjIsoToOverLeft ℱ.obj G.obj).hom.app X x).2) := by
  -- Route correction: after unfolding the induced inverse image into the explicit
  -- `overEquivPresheafCostructuredArrow.inverse` composite, the whole wrapper is exactly the
  -- naturality map on `YonedaCollection`, so the result is the componentwise naturality statement.
  rw [overEquiv_inverse_wrapper_component_eq_map1 (ℱ := ℱ) η X x]
  exact
    yonedaCollectionProjIsoToOverLeft_naturality_components
      (P := ℱ.obj) (η := η.hom) X x

-- Internal comparison with the abstract slice inverse-image `toOver ℱ`; the public compatibility
-- statement below composes this with the canonical identification `toOver ℱ ≅ Over.star ℱ`.
noncomputable def sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoToOver :
    ((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
        (sheafCategoryOfElementsEquivOver ℱ).functor) ≅
      toOver ℱ :=
  NatIso.ofComponents
    (fun G ↦ by
      simpa [Functor.sheafPushforwardContinuous, ObjectProperty.lift,
          sheafCategoryOfElementsEquivOver, overPresheafHasSheafDomainEquivOver,
          sheafCategoryOfElementsPresheafEquivOverPresheaf] using
        (by
          refine Over.isoMk
            (ObjectProperty.isoMk (Presheaf.IsSheaf J)
              (by
                simpa [toOver] using
                  (((yonedaCollectionFunctor ℱ.obj).mapIso
                      (Functor.isoWhiskerRight
                        (Iso.refl ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj)) ≪≫
                    yonedaCollectionProjIsoToOverLeft ℱ.obj G.obj)))
            (by
              apply Sheaf.hom_ext
              ext X x
              change SemiCartesianMonoidalCategory.snd (G.obj.obj X) (ℱ.obj.obj X)
                ((YonedaCollection.map₁
                      (Functor.whiskerRight
                        (𝟙 ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj) x).snd,
                    (YonedaCollection.map₁
                      (Functor.whiskerRight
                        (𝟙 ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj) x).yonedaEquivFst) =
                ((yonedaCollectionPresheafToA
                    ((CostructuredArrow.proj yoneda ℱ.obj).op ⋙ G.obj)).app
                  X) x
              simp [yonedaCollectionPresheafToA, SemiCartesianMonoidalCategory.snd])))
    (by
      intro G G' η
      -- The comparison is objectwise identity on the underlying pair `(section, value)`.
      apply Over.OverMorphism.ext
      apply Sheaf.hom_ext
      ext X x
      -- The remaining comparison is exactly the componentwise normalization isolated above.
      simpa [Functor.sheafPushforwardContinuous, ObjectProperty.lift,
        sheafCategoryOfElementsEquivOver, overPresheafHasSheafDomainEquivOver,
        sheafCategoryOfElementsPresheafEquivOverPresheaf,
        yonedaCollectionProjIsoToOverLeft_naturality] using
        inverse_map_toOverCompYoneda_component_normalize (ℱ := ℱ) η X x)

/-- Lemma 7.30.3 (compatibility): under `sheafCategoryOfElementsEquivOver`, the sheaf functor
induced by the projection from the category of elements of `ℱ` is canonically isomorphic to the
localization inverse-image functor `Over.star ℱ`. Equivalently, this equivalence identifies the
morphism of topoi induced by `π_ℱ` with the localization morphism at `ℱ`. -/
noncomputable def sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar :
    ((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
        (sheafCategoryOfElementsEquivOver ℱ).functor) ≅
      Over.star ℱ :=
  sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoToOver ℱ ≪≫
    ((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm

-- Proof sketch: the comparison is the application of the natural isomorphism
-- `sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ` to `G`.
/-- The comparison morphism from the image of `G` under
`(sheafCategoryOfElementsEquivOver ℱ).functor` to the slice inverse image `Over.star ℱ` is an
isomorphism. -/
theorem sheafCategoryOfElementsEquivOver_functor_obj_inverseImage_hom_isIso
    (G : Sheaf J (Type v)) :
    IsIso ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).hom.app G) :=
  inferInstance

end

end CategoryTheory

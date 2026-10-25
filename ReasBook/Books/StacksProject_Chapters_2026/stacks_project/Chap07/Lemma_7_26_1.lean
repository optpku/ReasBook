module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v w

noncomputable section

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {U : C} {ℱ 𝒢 : Sheaf J (Type w)}

abbrev localizedSheafHomPresheaf
    (J : GrothendieckTopology C) (U : C) (ℱ 𝒢 : Sheaf J (Type w)) :
    (Over U)ᵒᵖ ⥤ Type (max u v w) :=
  (CategoryTheory.sheafHom (J := J.over U) (ℱ.over U) (𝒢.over U)).1

/- Domain-style sampling for Lemma 7.26.1:
- primary domain: descent of morphisms for set-valued sheaves on localized sites;
- sampled owner API:
  `Pseudofunctor.presheafHomObjHomEquiv`,
  `Pseudofunctor.DescentData.subtypeCompatibleHomEquiv`,
  `Pseudofunctor.bijective_toDescentData_map_iff`,
  `CategoryTheory.Pseudofunctor.sheafHom`,
  `Functor.sheafPushforwardContinuousComp'`;
- source-facing layer: explicit local morphisms on a fixed cover and their overlap compatibility;
- core/canonical owner: the descent-data functor
  `((J.pseudofunctorOver (Type w)).toDescentData (fun I : 𝒰.Arrow ↦ I.f))` on the sheaf
  pseudofunctor over slice sites;
- bridge/view: the textbook local family `φ I : ℱ.over I.Y ⟶ 𝒢.over I.Y` is the image of the
  canonical compatible family for the sheaf-Hom presheaf, transported through
  `Functor.sheafPushforwardContinuousComp'`.

Primitive data are the cover `𝒰 : J.Cover U` and the local morphisms on its members. The
comparison isomorphism between iterated localization and direct localization is already owned by
`Functor.sheafPushforwardContinuousComp'`, and the compatible-family owner already lives in the
descent-data API. The public surface here should therefore center the canonical descent-data map on
Homs and keep the overlap-equality formulation only as a source-facing companion.
-/

/-- Helper for Lemma 7.26.1: after transporting sheaves on the iterated slice `(C/U)/(T/U)`
across the canonical equivalence with `C/T`, one recovers the direct localization functor along
`T ⟶ U`. -/
def iteratedSlicePullbackIsoOverMapPullback
    (T : Over U) (ℱ : Sheaf J (Type w)) :
    (T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
      (((J.over U).overPullback (Type w) T).obj (ℱ.over U)) ≅
    (J.overMapPullback (Type w) T.hom).obj (ℱ.over U) := by
  -- Compare the two sheaves on `C/T` at the presheaf level using the equality
  -- `iteratedSliceBackward ⋙ forget = Over.map T.hom`.
  refine (fullyFaithfulSheafToPresheaf (J.over T.left) (Type w)).preimageIso ?_
  simpa [GrothendieckTopology.overPullback, GrothendieckTopology.overMapPullback,
    Equivalence.sheafCongr, Equivalence.sheafCongr.functor] using
    (Functor.isoWhiskerRight
      (eqToIso (congrArg Functor.op (Over.iteratedSliceBackward_forget T)))
      ((ℱ.over U).obj))

/-- Helper for Lemma 7.26.1: transporting a morphism between the iterated localizations on
`((C/U)/(T/U))` across the canonical slice equivalence gives a morphism on `C/T`. -/
def iteratedSliceSheafCongrHomEquiv
    (T : Over U) :
    (((J.over U).overPullback (Type w) T).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) T).obj (𝒢.over U)) ≃
    ((T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
        (((J.over U).overPullback (Type w) T).obj (ℱ.over U)) ⟶
      (T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor.obj
        (((J.over U).overPullback (Type w) T).obj (𝒢.over U))) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((T.iteratedSliceEquiv.sheafCongr ((J.over U).over T) (J.over T.left) (Type w)).functor)).homEquiv

/-- Helper for Lemma 7.26.1: the ordinary Hom sheaf on `C/U` evaluated at a cover arrow gives the
localized morphisms on that slice member. -/
def localizedSheafHomEquiv (𝒰 : J.Cover U) (I : 𝒰.Arrow) :
    (localizedSheafHomPresheaf J U ℱ 𝒢).obj
      (Opposite.op (Over.mk I.f)) ≃
      (ℱ.over I.Y ⟶ 𝒢.over I.Y) := by
  -- Route correction: use the ordinary slice-site Hom owner and transport only the objectwise
  -- iterated-slice comparison, rather than building a global NatIso of Hom-presheaves.
  change (((J.over U).overPullback (Type w) (Over.mk I.f)).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) (Over.mk I.f)).obj (𝒢.over U)) ≃
      (ℱ.over I.Y ⟶ 𝒢.over I.Y)
  exact (iteratedSliceSheafCongrHomEquiv (J := J) (ℱ := ℱ) (𝒢 := 𝒢) (T := Over.mk I.f)).trans
    (Iso.homCongr
      (iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk I.f) (ℱ := ℱ))
      (iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk I.f) (ℱ := 𝒢)))

/-- Helper for Lemma 7.26.1: the value of the ordinary Hom sheaf on `C/U` at the terminal object
recovers morphisms on the whole localized site `C/U`. -/
def localizedSheafHomAtBaseEquiv :
    (localizedSheafHomPresheaf J U ℱ 𝒢).obj
      (Opposite.op (Over.mk (𝟙 U))) ≃
      (ℱ.over U ⟶ 𝒢.over U) := by
  change (((J.over U).overPullback (Type w) (Over.mk (𝟙 U))).obj (ℱ.over U) ⟶
      ((J.over U).overPullback (Type w) (Over.mk (𝟙 U))).obj (𝒢.over U)) ≃
      (ℱ.over U ⟶ 𝒢.over U)
  -- The terminal object in `Over U` reduces the direct pullback back to `C/U`.
  refine (iteratedSliceSheafCongrHomEquiv (J := J) (ℱ := ℱ) (𝒢 := 𝒢)
      (T := Over.mk (𝟙 U))).trans ?_
  -- The remaining comparison is the identity pullback on `C/U`.
  simpa using
    (Iso.homCongr
      ((iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk (𝟙 U))
        (ℱ := ℱ)).trans ((J.overMapPullbackId (Type w) U).app (ℱ.over U)))
      ((iteratedSlicePullbackIsoOverMapPullback (J := J) (T := Over.mk (𝟙 U))
        (ℱ := 𝒢)).trans ((J.overMapPullbackId (Type w) U).app (𝒢.over U))))

/-- Helper for Lemma 7.26.1: the cover arrows in `Over U` generate exactly the pullback of the
original covering sieve to the terminal object `U/U`. -/
theorem cover_arrows_sieve_over_terminal
    (𝒰 : J.Cover U) :
    Sieve.overEquiv (Over.mk (𝟙 U))
      (Sieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) =
      (𝒰 : Sieve U) := by
  -- The generated sieve in the slice site consists exactly of morphisms factoring through one of
  -- the chosen cover members.
  ext Z g
  rw [Sieve.overEquiv_iff, Sieve.mem_ofArrows_iff]
  constructor
  · rintro ⟨I, h, _⟩
    have hw : h.left ≫ I.f = g := by
      simpa using Over.w h
    exact hw ▸ (𝒰 : Sieve U).downward_closed I.hf h.left
  · intro hg
    let a : Over.mk (g ≫ (Over.mk (𝟙 U)).hom) ⟶ Over.mk g := Over.homMk (𝟙 Z) (by simp)
    refine ⟨⟨Z, g, hg⟩, a, ?_⟩
    ext
    simp [a]

/-- The restriction of a morphism on the localized site `C/U` to a chosen member of a cover of
`U`, read through the ordinary slice-site Hom sheaf and then transported across the canonical
slice-site pullback isomorphism. -/
def restrict_sheaf_hom_to_cover_arrow
    (𝒰 : J.Cover U) (ψ : ℱ.over U ⟶ 𝒢.over U) (I : 𝒰.Arrow) :
    ℱ.over I.Y ⟶ 𝒢.over I.Y :=
  localizedSheafHomEquiv 𝒰 I <|
    (localizedSheafHomPresheaf J U ℱ 𝒢).map
      (Over.homMk I.f).op ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ)

/-- A family of local morphisms on the members of a cover of `U` is compatible on overlaps when
the induced family of sections of the ordinary localized Hom sheaf on `C / U` is compatible. -/
def LocalizedSheafHomCompatible
    (𝒰 : J.Cover U) (φ : ∀ I : 𝒰.Arrow, ℱ.over I.Y ⟶ 𝒢.over I.Y) : Prop :=
  Presieve.Arrows.Compatible
    (localizedSheafHomPresheaf J U ℱ 𝒢)
    (fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
    (fun I : 𝒰.Arrow ↦ (localizedSheafHomEquiv 𝒰 I).symm (φ I))

section

variable (𝒰 : J.Cover U)

theorem localizedSheafHom_isSheafFor_cover :
    ∀ {ℱ 𝒢 : Sheaf (J.over U) (Type w)},
    Presieve.IsSheafFor
      ((CategoryTheory.sheafHom (J := J.over U) ℱ 𝒢).1)
      (Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) := by
  intro ℱ 𝒢
  -- The ordinary internal Hom on the slice site is already a sheaf; we only identify the cover
  -- arrows with the covering sieve of `U/U`.
  rw [Presieve.isSheafFor_iff_generate]
  refine Presheaf.IsSheaf.isSheafFor
    ((CategoryTheory.sheafHom (J := J.over U) ℱ 𝒢).2) _ ?_
  rw [J.mem_over_iff, cover_arrows_sieve_over_terminal (J := J) (U := U) 𝒰]
  exact 𝒰.condition

theorem coverwise_compatible_sheaf_hom_of_global
    (𝒰 : J.Cover U) (ψ : ℱ.over U ⟶ 𝒢.over U) :
    LocalizedSheafHomCompatible 𝒰
      (fun I ↦ restrict_sheaf_hom_to_cover_arrow 𝒰 ψ I) := by
  -- The local restrictions are literally the compatible family cut out from the section at `U/U`.
  unfold LocalizedSheafHomCompatible restrict_sheaf_hom_to_cover_arrow
  simpa using
    (Presieve.Arrows.toCompatible
      (localizedSheafHomPresheaf J U ℱ 𝒢)
      (fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)
      ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ)).property

/-- Lemma 7.26.1, source-facing form: a coverwise family of local morphisms satisfying
`LocalizedSheafHomCompatible` glues uniquely to a morphism on `ℱ|_{C/U}`. -/
theorem exists_unique_localized_hom_of_coverwise_compatible
    (𝒰 : J.Cover U)
    (φ : ∀ I : 𝒰.Arrow, ℱ.over I.Y ⟶ 𝒢.over I.Y)
    (hφ : LocalizedSheafHomCompatible 𝒰 φ) :
    ∃! ψ : ℱ.over U ⟶ 𝒢.over U, ∀ I : 𝒰.Arrow,
      restrict_sheaf_hom_to_cover_arrow 𝒰 ψ I = φ I := by
  let P := localizedSheafHomPresheaf J U ℱ 𝒢
  let π := fun I : 𝒰.Arrow ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f
  -- The cover sheaf condition gives a bijection between global sections and compatible families.
  let hbij :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P π).mp
      (localizedSheafHom_isSheafFor_cover (𝒰 := 𝒰) (ℱ := ℱ.over U) (𝒢 := 𝒢.over U))
  let x : Subtype (Presieve.Arrows.Compatible P π) :=
    by
      refine ⟨fun I ↦ (localizedSheafHomEquiv 𝒰 I).symm (φ I), ?_⟩
      simpa [P, π] using hφ
  obtain ⟨s, hs⟩ := hbij.surjective x
  refine ⟨(localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢) s), ?_, ?_⟩
  · intro I
    -- The glued section restricts to the prescribed local morphism on each cover member.
    rw [restrict_sheaf_hom_to_cover_arrow]
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    change P.map (π I).op
        ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm
          ((localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)) s)) = x.1 I
    rw [Equiv.symm_apply_apply]
    simpa using congrFun (congrArg Subtype.val hs) I
  · intro ψ hψ
    -- Uniqueness comes from injectivity of the global-section-to-compatible-family map.
    let sψ :=
      (localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm ψ
    have hψ' :
        Presieve.Arrows.toCompatible P π
            sψ = x := by
      apply Subtype.ext
      funext I
      rw [show x.1 I = (localizedSheafHomEquiv 𝒰 I).symm (φ I) by rfl]
      apply (localizedSheafHomEquiv 𝒰 I).injective
      simpa [sψ, restrict_sheaf_hom_to_cover_arrow, P, π] using hψ I
    apply (localizedSheafHomAtBaseEquiv (J := J) (U := U) (ℱ := ℱ) (𝒢 := 𝒢)).symm.injective
    simpa [sψ] using
      (hbij.injective (hψ'.trans hs.symm) : sψ = s)

/-- Lemma 7.26.1, owner-level form: for a fixed cover `𝒰` of `U`, the ordinary Hom sheaf on
`C/U` satisfies the sheaf condition for the presieve generated by the cover arrows. -/
theorem localizedSheafPseudofunctorOver_isPrestackFor_cover
    (𝒰 : J.Cover U) :
    Presieve.IsSheafFor
      (localizedSheafHomPresheaf J U ℱ 𝒢)
      (Presieve.ofArrows (fun I : 𝒰.Arrow ↦ Over.mk I.f)
        (fun I ↦ show Over.mk I.f ⟶ Over.mk (𝟙 U) from Over.homMk I.f)) := by
  -- This is exactly the coverwise sheaf condition proved for the ordinary slice-site Hom owner.
  simpa [localizedSheafHomPresheaf] using
    (localizedSheafHom_isSheafFor_cover (J := J) (U := U) (𝒰 := 𝒰)
      (ℱ := ℱ.over U) (𝒢 := 𝒢.over U))

end

end

end GrothendieckTopology
end CategoryTheory

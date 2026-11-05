module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom
@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-
Domain-style sampling for Lemma 4.2.18:
- `Functor.EssSurj` is the owner abstraction for chosen objectwise preimages up to isomorphism.
- `Functor.essImage.liftFunctor` / `Functor.essImage.liftFunctorCompIso` provide the canonical
  essential-image lift.
- `Functor.fullyFaithfulCancelRight` is the canonical uniqueness tool for lifts through a fully
  faithful functor.
- `Functor.IsEquivalence` is the owner predicate for equivalences of categories.

Primitive-vs-derived split:
- primitive source-facing data: a chosen object assignment `jObj : B → A` and isomorphisms
  `i X : X ≅ F.obj (jObj X)`.
- derived API: the induced lift functor, the canonical `EssSurj` witness, and hence
  `IsEquivalence` when `F` is also full and faithful.
-/

/- Source/core/bridge triage for Lemma 4.2.18:
- `source-facing`: `fully_faithful_objwise_iso_existsUnique_lift`.
- `core/canonical`: `Functor.EssSurj` and `Functor.IsEquivalence`.
- `bridge/view`: `essSurj_of_objwise_iso` and the resulting equivalence criterion below.

The source-facing theorem keeps an explicit lift construction because the textbook data prescribes
the object assignment `jObj` on the nose. Mathlib's owner-level `essImage.liftFunctor` only
produces a chosen preimage object from essential-image membership, so it does not preserve that
specified object assignment definitionally. -/

variable (F : A ⥤ B)

/-- Lemma 4.2.18 (1): the chosen object assignment and isomorphisms determine a unique extension
functor. -/
theorem fully_faithful_objwise_iso_existsUnique_lift
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    ∃! j : B ⥤ A,
      ∃ hjObj : ∀ X : B, j.obj X = jObj X,
        ∃ α : 𝟭 B ≅ j ⋙ F,
          ∀ X : B,
            α.hom.app X =
              (i X).hom ≫
                eqToHom
                  (show F.obj (jObj X) = (j ⋙ F).obj X from by
                    simpa using congrArg (fun Z ↦ F.obj Z) (hjObj X).symm) := by
  let j : B ⥤ A :=
    { obj := jObj
      map := fun f ↦ F.preimage ((i _).inv ≫ f ≫ (i _).hom)
      map_id := by
        intro X
        apply F.map_injective
        simp
      map_comp := by
        intro X Y Z f g
        apply F.map_injective
        simp [Category.assoc] }
  let α : 𝟭 B ≅ j ⋙ F :=
    NatIso.ofComponents i <| by
      intro X Y f
      change f ≫ (i Y).hom = (i X).hom ≫ F.map (F.preimage ((i X).inv ≫ f ≫ (i Y).hom))
      simp
  have hj : ∀ X : B, j.obj X = jObj X := fun _ ↦ rfl
  have hα :
      ∀ X : B,
        α.hom.app X =
          (i X).hom ≫
            eqToHom
              (show F.obj (jObj X) = (j ⋙ F).obj X from by
                simpa using congrArg (fun Z ↦ F.obj Z) (hj X).symm) := by
    intro X
    simp [α, j]
  refine ⟨j, ?_, ?_⟩
  · exact ⟨hj, α, hα⟩
  · intro j' hj'
    rcases hj' with ⟨hjObj, α', hα'⟩
    let compIso : j' ⋙ F ≅ j ⋙ F := α'.symm ≪≫ α
    let e : j' ≅ j := fullyFaithfulCancelRight F compIso
    refine ext_of_iso e (fun X ↦ (hjObj X).trans (hj X).symm) ?_
    intro X
    let hobjX : j'.obj X = j.obj X := (hjObj X).trans (hj X).symm
    change F.preimage (compIso.hom.app X) = eqToHom hobjX
    apply F.map_injective
    let p : (j' ⋙ F).obj X = F.obj (jObj X) := by
      simpa using congrArg (fun Z ↦ F.obj Z) (hjObj X)
    have h1 : α'.inv.app X ≫ (i X).hom = eqToHom p := by
      apply (cancel_mono (eqToHom p.symm)).1
      simpa [p, hα' X, Category.assoc] using α'.inv_hom_id_app X
    have h2 : F.map (eqToHom hobjX) = eqToHom p := by
      simp [eqToHom_map]
    have hcomp : compIso.hom.app X = α'.inv.app X ≫ (i X).hom := by
      simp [compIso, α]
    exact (F.map_preimage _).trans (hcomp.trans (h1.trans (by simpa using h2.symm)))

/-- Chosen objectwise preimages exhibit `F` as essentially
surjective. -/
theorem essSurj_of_objwise_iso
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    F.EssSurj :=
  ⟨fun X ↦ ⟨jObj X, ⟨(i X).symm⟩⟩⟩

/-- Lemma 4.2.18 (2): chosen objectwise preimages under a fully faithful functor make the functor an
equivalence. -/
theorem fully_faithful_isEquivalence_of_objwise_iso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) : F.IsEquivalence := by
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := F.essSurj_of_objwise_iso jObj i }

end Functor
end CategoryTheory

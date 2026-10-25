module

public import stacks_project.Chap04.Definition_4_35_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open FibredInGroupoidsMor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X₁ X₂ X₃ X₄ : FibredInGroupoidsOver C}

/- Domain-style sampling for Lemma 4.35.11:
- primary domain: bicategorical hom-categories of categories fibred in groupoids over a fixed
  base, with equivalences expressed on explicit morphisms over the base;
- inspected owner-level declarations:
  `FibredInGroupoidsOver C`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `Bicategory.precomp`,
  `Bicategory.postcomp`,
  `Bicategory.associatorNatIsoRight`,
  `Bicategory.associatorNatIsoLeft`;
- best owner abstraction: the owner homs `X₁ ⟶ X₂` and `X₃ ⟶ X₄` in
  `FibredInGroupoidsOver C`, together with the owner predicate `IsEquivalenceOverBase`; the
  packaged bicategorical equivalence `X ≌ Y` is derived;
- primitive data: morphisms `φ : X₁ ⟶ X₂`, `ψ : X₃ ⟶ X₄` and proofs
  `IsEquivalenceOverBase φ`,
  `IsEquivalenceOverBase ψ`;
- derived API: the internal bicategorical equivalences built from those data, and the induced
  equivalences on hom-categories via `precomp`, `postcomp`, and their composite.

Source/core/bridge triage:
- `source-facing`: the explicit over-base morphisms `φ`, `ψ` and the induced end functor on the
  hom-categories;
- `core/canonical`: bicategorical hom-categories, `precomp`, `postcomp`, and `Functor.IsEquivalence`;
- `bridge/view`: `FibredInGroupoidsMor.exists_equivalence` and
  `FibredInGroupoidsOver.hom_isEquivalenceOverBase`. -/

namespace Bicategory

variable {B : Type u} [Bicategory B]
variable {a b c d : B}

/-- In any bicategory, whiskering on the right by an equivalence induces an equivalence on the
corresponding hom-category. -/
theorem precomp_isEquivalence (c : B) (e : a ≌ b) :
    Functor.IsEquivalence (precomp c e.hom) :=
  -- The quasi-inverse is given by whiskering with the inverse 1-morphism.
  Functor.IsEquivalence.mk'
    (precomp c e.inv)
    -- The counit is assembled from the bicategorical counit and the unitor/associator coherence.
    ((leftUnitorNatIso b c).symm ≪≫
      Functor.mapIso (precomposing b b c) e.counit.symm ≪≫
      associatorNatIsoRight e.inv e.hom c)
    -- The unit is the dual coherence built from the bicategorical unit of `e`.
    ((associatorNatIsoRight e.hom e.inv c).symm ≪≫
      Functor.mapIso (precomposing a a c) e.unit.symm ≪≫
      leftUnitorNatIso a c)

/-- In any bicategory, whiskering on the left by an equivalence induces an equivalence on the
corresponding hom-category. -/
theorem postcomp_isEquivalence (a : B) (e : c ≌ d) :
    Functor.IsEquivalence (postcomp a e.hom) :=
  -- The quasi-inverse is given by whiskering with the inverse 1-morphism.
  Functor.IsEquivalence.mk'
    (postcomp a e.inv)
    -- The counit uses the unit of `e` transported across the right unitor and associator.
    ((rightUnitorNatIso a c).symm ≪≫
      Functor.mapIso (postcomposing a c c) e.unit ≪≫
      (associatorNatIsoLeft a e.hom e.inv).symm)
    -- The unit uses the counit of `e` in the dual coherence pattern.
    (associatorNatIsoLeft a e.inv e.hom ≪≫
      Functor.mapIso (postcomposing a d d) e.counit ≪≫
      rightUnitorNatIso a d)

end Bicategory

/-- Lemma 4.35.11: if `𝒮₁`, `𝒮₂`, `𝒮₃`, and `𝒮₄` are categories fibred in groupoids over `C`,
and `φ : 𝒮₁ ⟶ 𝒮₂`, `ψ : 𝒮₃ ⟶ 𝒮₄` are equivalences over the base, then precomposition by `φ`
and postcomposition by `ψ` induce an equivalence
`Mor_{Cat/C}(𝒮₂, 𝒮₃) → Mor_{Cat/C}(𝒮₁, 𝒮₄)`. Via Definition 4.35.6, these hom-categories are
canonically `X₂ ⟶ X₃` and `X₁ ⟶ X₄`. -/
theorem prePostcomposeFunctorOfOverBaseEquivalences_isEquivalence
    (φ : X₁ ⟶ X₂) (ψ : X₃ ⟶ X₄)
    (hφ : IsEquivalenceOverBase φ) (hψ : IsEquivalenceOverBase ψ) :
    Functor.IsEquivalence (postcomp X₂ ψ ⋙ precomp X₄ φ) := by
  -- Replace the explicit over-base equivalences by packaged bicategorical equivalences.
  rcases exists_equivalence φ hφ with ⟨eφ, rfl⟩
  rcases exists_equivalence ψ hψ with ⟨eψ, rfl⟩
  -- Each whiskering functor is an equivalence on the corresponding hom-category.
  letI : Functor.IsEquivalence (postcomp X₂ eψ.hom) :=
    Bicategory.postcomp_isEquivalence X₂ eψ
  letI : Functor.IsEquivalence (precomp X₄ eφ.hom) :=
    Bicategory.precomp_isEquivalence X₄ eφ
  -- The target functor is the composite of those two equivalences.
  infer_instance

end CategoryTheory

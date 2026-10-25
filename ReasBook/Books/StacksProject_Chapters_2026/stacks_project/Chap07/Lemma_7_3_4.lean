module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open CategoryTheory.Subfunctor

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
variable {ℱ 𝒢 : Presheaf C} (φ : ℱ ⟶ 𝒢)

/- Domain-style sampling for Lemma 7.3.4:
- primary domain: images of morphisms of set-valued presheaves and their epi/mono factorizations;
- sampled owner declarations:
  `Presheaf`,
  `Subfunctor.range`,
  `Subfunctor.toRange`,
  `Subfunctor.toRange_ι`,
  `Subfunctor.range_eq_top`;
- best owner abstraction: the chapter owner `Presheaf C`, together with the range subpresheaf
  `Subfunctor.range φ`, whose inclusion is the canonical mono part of the image factorization of
  `φ`;
- primitive data: the morphism `φ`;
- derived API: factorization through the range via `toRange φ`, its epi instance, and the
  uniqueness criterion below identifying any epi factorization through a subpresheaf with
  `range φ`.

Source/core/bridge triage:
- `source-facing`: the unique subpresheaf of the target through which `φ` factors by an
  epimorphism;
- `core/canonical`: the chapter presheaf owner `Presheaf C` and the canonical range subpresheaf
  `Subfunctor.range φ`;
- `bridge/view`: the proof below identifies any epi factorization through a subpresheaf with the
  canonical range subpresheaf, but this bridge is internal to the source-facing uniqueness
  statement rather than a second public owner.
-/
/-- Lemma 7.3.4: a morphism of presheaves of sets factors through a unique subpresheaf of the
target such that the induced map to that subpresheaf is an epimorphism. -/
theorem existsUnique_subfunctor_factorization_epi :
    ∃! G' : Subfunctor 𝒢,
      ∃ α : ℱ ⟶ G'.toFunctor, Epi α ∧ α ≫ G'.ι = φ := by
  -- The source proof chooses the image subpresheaf, which is `range φ` in the canonical API.
  refine ⟨range φ, ?_, ?_⟩
  -- The canonical map into the range provides the required epi factorization.
  · exact ⟨toRange φ, inferInstance, toRange_ι φ⟩
  -- Any other epi factorization through a subpresheaf has the same range, hence the same subpresheaf.
  · intro G' hG'
    rcases hG' with ⟨α, hα_epi, hα⟩
    letI : Epi α := hα_epi
    calc
      G' = range (α ≫ G'.ι) := by
        symm
        rw [range_comp, range_eq_top, image_top, range_ι]
      _ = range φ := by simp [hα]

end
end Presheaf
end CategoryTheory

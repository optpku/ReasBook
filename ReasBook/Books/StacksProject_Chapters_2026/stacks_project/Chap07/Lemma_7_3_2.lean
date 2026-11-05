module

public import Mathlib.CategoryTheory.NatIso
import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_3_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe w v u

namespace CategoryTheory
namespace Presheaf

/-
Domain-style sampling for Lemma 7.3.2:
- primary domain: monomorphisms, epimorphisms, and isomorphisms of set-valued presheaves;
- inspected owner declarations:
  `CategoryTheory.Presheaf.mono_iff_injective`,
  `CategoryTheory.Presheaf.epi_iff_surjective`,
  `CategoryTheory.isIso_iff_mono_and_epi`;
- best owner abstraction: the categorical predicates `Mono`, `Epi`, and `IsIso` for morphisms of
  presheaves, with the sectionwise injective/surjective criteria as derived bridge API;
- primitive data: a morphism `φ : ℱ ⟶ 𝒢`;
- derived API: the objectwise injective and surjective reformulations.

Source/core/bridge triage:
- `source-facing`: the Stacks sectionwise injective, surjective, and bijective clauses for a
  morphism of presheaves of sets;
- `core/canonical`: `Mono φ`, `Epi φ`, and `IsIso φ`;
- `bridge/view`: `mono_iff_injective`, `epi_iff_surjective`, and the companion theorem below
  combining them with `isIso_iff_mono_and_epi`. -/

section

variable {C : Type u} [Category.{v} C]
variable {ℱ 𝒢 : Presheaf C} (φ : ℱ ⟶ 𝒢)

/- Lemma 7.3.2 (1): the injective maps of presheaves of sets are exactly the monomorphisms.
This is the exact canonical theorem already recorded in Definition 7.3.1. -/
recall mono_iff_injective

/- Lemma 7.3.2 (2): the surjective maps of presheaves of sets are exactly the epimorphisms.
This is the exact canonical theorem already recorded in Definition 7.3.1. -/
recall epi_iff_surjective

/-
Lemma 7.3.2 (3): the canonical owner theorem for "isomorphism iff injective and surjective" is
`CategoryTheory.isIso_iff_mono_and_epi`.
-/
recall isIso_iff_mono_and_epi

/-- Lemma 7.3.2 (3), companion bridge: a morphism of presheaves of sets is an isomorphism if and
only if it is injective and surjective in the sense of Definition 7.3.1. -/
theorem isIso_iff_injective_and_surjective :
    IsIso φ ↔
      (∀ U : C, Function.Injective (φ.app (op U))) ∧
        ∀ U : C, Function.Surjective (φ.app (op U)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  constructor
  · intro hφ
    constructor
    · intro U
      exact ((CategoryTheory.isIso_iff_bijective (φ.app (op U))).1 (hφ (op U))).1
    · intro U
      exact ((CategoryTheory.isIso_iff_bijective (φ.app (op U))).1 (hφ (op U))).2
  · intro hφ U
    exact (CategoryTheory.isIso_iff_bijective (φ.app U)).2
      ⟨hφ.1 U.unop, hφ.2 U.unop⟩

end

end Presheaf
end CategoryTheory

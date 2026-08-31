module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_3_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Presheaf

/- Source/core/bridge triage for Definition 7.3.1:
- source-facing layer: the objectwise injective/surjective clauses on sections over every object
  of `C`;
- core/canonical owners: the chapter presheaf owner `_root_.CategoryTheory.Presheaf C` together
  with the categorical predicates `Mono φ` and `Epi φ`;
- bridge/view API: `NatTrans.mono_iff_mono_app`, `NatTrans.epi_iff_epi_app`,
  `CategoryTheory.mono_iff_injective`, and `CategoryTheory.epi_iff_surjective`;
- primitive data: the morphism `φ : F ⟶ G`;
- derived API: the objectwise function criteria recorded by the companion bridge theorems below.
-/

section

variable {F G : Presheaf C} (φ : F ⟶ G)

/- Definition 7.3.1 (injective clause), owner recall: for a morphism of set-valued presheaves,
the canonical owner notion is `Mono φ`. The textbook sectionwise formulation is the companion
bridge theorem below. -/
recall Mono

/- Definition 7.3.1 (surjective clause), owner recall: for a morphism of set-valued presheaves,
the canonical owner notion is `Epi φ`. The textbook sectionwise formulation is the companion
bridge theorem below. -/
recall Epi

-- Proof sketch: monomorphisms in a functor category are objectwise monomorphisms, and
-- monomorphisms in `Type` are exactly injective functions.
/-- Companion bridge: a morphism of presheaves of sets is a monomorphism exactly when it is
injective on sections over every object of `C`. -/
theorem mono_iff_injective :
    Mono φ ↔ ∀ U : C, Function.Injective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.mono_iff_injective _).1
      ((NatTrans.mono_iff_mono_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.mono_iff_mono_app φ).2 fun U ↦
      (CategoryTheory.mono_iff_injective _).2 (hφ U.unop)

-- Proof sketch: epimorphisms in a functor category are objectwise epimorphisms, and
-- epimorphisms in `Type` are exactly surjective functions.
/-- Companion bridge: a morphism of presheaves of sets is an epimorphism exactly when it is
surjective on sections over every object of `C`. -/
theorem epi_iff_surjective :
    Epi φ ↔ ∀ U : C, Function.Surjective (φ.app (op U)) := by
  constructor
  · intro hφ U
    exact (CategoryTheory.epi_iff_surjective _).1
      ((NatTrans.epi_iff_epi_app φ).1 hφ (op U))
  · intro hφ
    exact (NatTrans.epi_iff_epi_app φ).2 fun U ↦
      (CategoryTheory.epi_iff_surjective _).2 (hφ U.unop)

end
end Presheaf

end CategoryTheory

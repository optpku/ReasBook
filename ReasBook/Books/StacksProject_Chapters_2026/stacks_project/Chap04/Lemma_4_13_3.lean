module

public import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/-
Domain-style sampling for Lemma 4.13.3:
- primary domain: characterizations of monomorphisms and epimorphisms by canonical pullback and
  pushout squares in `CategoryTheory`;
- inspected owner declarations:
  `Mono`,
  `Epi`,
  `mono_iff_isPullback`,
  `epi_iff_isPushout`;
- best owner abstraction: the canonical owner theorems `mono_iff_isPullback` and
  `epi_iff_isPushout`;
- primitive-vs-derived split:
  primitive data: only the morphism `f : X ⟶ Y` together with the standard owner predicates
    `Mono f` and `Epi f`;
  derived API: the corresponding cartesian and cocartesian square formulations
    `IsPullback (𝟙 X) (𝟙 X) f f` and `IsPushout f f (𝟙 Y) (𝟙 Y)`. -/

/- Source/core/bridge triage for Lemma 4.13.3:
- source-facing: the textbook equivalences expressing mono and epi morphisms through the obvious
  pullback and pushout squares;
- core/canonical: the mathlib owner theorems `mono_iff_isPullback` and `epi_iff_isPushout`;
- bridge/view: the earlier source-facing square notions `IsPullback` and `IsPushout` recalled in
  Definitions 4.6.2 and 4.9.2. -/

/- Lemma 4.13.3 (1): a morphism `f : X ⟶ Y` is a monomorphism if and only if the canonical square
with both horizontal arrows `𝟙 X` and both vertical arrows `f` is a pullback. This is exactly the
canonical mathlib theorem `CategoryTheory.mono_iff_isPullback`. -/
recall mono_iff_isPullback (f : X ⟶ Y) :
  Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f

/- Lemma 4.13.3 (2): a morphism `f : X ⟶ Y` is an epimorphism if and only if the canonical square
with both horizontal arrows `f` and both vertical arrows `𝟙 Y` is a pushout. This is exactly the
canonical mathlib theorem `CategoryTheory.epi_iff_isPushout`. -/
recall epi_iff_isPushout (f : X ⟶ Y) :
  Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y)

end CategoryTheory

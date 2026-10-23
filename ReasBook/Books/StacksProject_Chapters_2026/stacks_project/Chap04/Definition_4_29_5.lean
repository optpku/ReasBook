module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u₁ u₂

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {A : Type u₁} [Category.{v} A]

/- Domain-style sampling for Definition 4.29.5:
- `LocallyDiscrete.mkPseudofunctor` is the canonical constructor from the textbook object map,
  morphism map, and invertible unit/composition comparison data.
- `Functor.toPseudofunctor'` is the canonical bridge from an ordinary functor into a strict
  `2`-category to the corresponding weak functor.
- `PullbackChoice.fiberPseudofunctor` is the chapter's downstream project use of that same owner
  abstraction `LocallyDiscrete _ ⥤ᵖ _`.
- `Functor.IsSplitFibredCategory` later reuses `Functor.toPseudofunctor'` rather than introducing
  a parallel weak-functor wrapper.

Primitive-vs-derived split:
- primitive data: a weak functor is a pseudofunctor `LocallyDiscrete A ⥤ᵖ C`; its primitive fields
  are the object map, `1`-morphism map, `mapId`, `mapComp`, and the three coherence axioms.
- derived API: `LocallyDiscrete.mkPseudofunctor` packages the textbook data into that owner, while
  `Functor.toPseudofunctor'` is the additional bridge that requires strictness of the target. -/

/- Source/core/bridge triage for Definition 4.29.5:
- `source-facing`: the textbook notions of ordinary and weak functors from `A` to the strict
  `2`-category `C`.
- `core/canonical`: ordinary functors `A ⥤ C` and pseudofunctors `LocallyDiscrete A ⥤ᵖ C`.
- `bridge/view`: `LocallyDiscrete.mkPseudofunctor` and, under the extra strictness hypothesis,
  `Functor.toPseudofunctor'`. -/

section Core

variable {C : Type u₂} [Category.{v} C] [Bicategory.{w, v} C]

/- Definition 4.29.5 (1): a functor from an ordinary category `A` into a strict `2`-category `C`
is just an ordinary functor into the underlying category of `C`, i.e. an element of `A ⥤ C`. -/
#check (A ⥤ C)

/- Definition 4.29.5 (2): the canonical Lean notion of a weak functor from an ordinary category
`A` to a strict `2`-category `C` is a pseudofunctor `LocallyDiscrete A ⥤ᵖ C`. -/
#check (LocallyDiscrete A ⥤ᵖ C)

/- The textbook object map, morphism map, invertible unit and composition `2`-morphisms, and
coherence axioms are assembled by the existing constructor `LocallyDiscrete.mkPseudofunctor`. Its
field `mapId` uses mathlib's standard pseudofunctor orientation `φ (𝟙 a) ≅ 𝟙 (φ a)`, so the
Stacks-project unit comparison `αₐ : 𝟙 (φ a) ⟶ φ (𝟙 a)` is the inverse isomorphism. No parallel
local wrapper API is needed: the source-facing coherence equalities are already exactly the
constructor arguments of `LocallyDiscrete.mkPseudofunctor`. -/
recall LocallyDiscrete.mkPseudofunctor

end Core

section StrictBridge

variable {C : Type u₂} [Bicategory.{w, v} C] [Strict C]

/- Under the strictness hypothesis from the source text, any ordinary functor into `C`
canonically promotes to the corresponding weak functor from `LocallyDiscrete A`. This is a
derived bridge, not the owner of the notion. -/
recall Functor.toPseudofunctor'

end StrictBridge

end CategoryTheory

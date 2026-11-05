module

import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C)

/-
Companion recall: the canonical functor from `C` to the localization of `W` is `W.Q`.
-/
recall Q

/-
Companion recall: if `s : X ⟶ Y` lies in `W`, then its image under `W.Q` is canonically an
isomorphism, namely `Localization.isoOfHom W.Q W s hs`.
-/
recall isoOfHom

/-
Companion recall: the strict universal property of the canonical localization functor is packaged
by `Localization.strictUniversalPropertyFixedTargetQ`.
-/
recall strictUniversalPropertyFixedTargetQ

/- Domain-style sampling in the localization owner API:
- inspected owner predicate: `Functor.IsLocalization`
- inspected canonical localization functor: `MorphismProperty.Q`
- inspected owner instance for `W.Q`: `Functor.q_isLocalization`
- inspected bridge package: `Localization.strictUniversalPropertyFixedTargetQ`

Primitive data: the morphism property `W`.
Derived API: the localization functor `W.Q`, the strict universal property, the inverted
isomorphisms `Localization.isoOfHom`, and the owner-level instance `Functor.q_isLocalization`.

Source/core/bridge triage:
- `source-facing`: the chapter’s canonical localization functor attached to the chosen
  multiplicative system;
- `core/canonical`: the owner predicate `Functor.IsLocalization`;
- `bridge/view`: the strict universal property
  `Localization.strictUniversalPropertyFixedTargetQ`, from which the owner instance is built.

Lemma 4.27.16 is a `core/canonical` recall item: the source statement is the owner fact that the
canonical localization functor `W.Q` localizes `C` at `W`. The chapter’s surrounding
right-fraction hypotheses are redundant for this owner fact, so the main entry stays at the
assumption-free canonical recall rather than reintroducing a source-local wrapper theorem.
-/
/- Lemma 4.27.16: the canonical localization functor `W.Q` is a localization of `C` at the
morphism property `W`. -/
recall Functor.q_isLocalization : W.Q.IsLocalization W

end CategoryTheory

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

namespace Group

/-!
Primary domain: finitely presented group properties and Markov properties from decision-problem
theory.

Layer triage:
- `source-facing`: a property `P` of finitely presented groups, assumed invariant under
  isomorphism, together with the two textbook clauses that characterize when `P` is a Markov
  property.
- `core/canonical`: `Group.IsMarkovProperty` is the chapter owner for this abstract group-level
  notion, `IsFinitelyPresented` is mathlib's owner predicate for finite presentability,
  multiplicative equivalences `G ≃* H` are the canonical group isomorphisms, and monoid
  homomorphisms with `Function.Injective` are the source-faithful embedding data.
- `bridge/view`: the textbook phrase “`G₂` cannot be embedded in any finitely presented group with
  `P`” is expressed directly by the nonexistence of an injective homomorphism `G₂ →* H` into such
  a group `H`.

Domain sampling:
1. `Group.HasSolvableWordProblem` in Theorem `4-4-8` is the chapter's abstract group-level owner
   pattern for decision-theoretic properties, so this definition should also live in `namespace
   Group`.
2. `IsFinitelyPresented` is mathlib's owner predicate for finite presentability.
3. `IsFinitelyPresented.equiv` transports finite presentability across a group isomorphism, so the
   invariance hypothesis should be stated using `G ≃* H`.
4. The surrounding chapter states embeddings source-faithfully as homomorphisms together with
   `Function.Injective`, rather than introducing a separate wrapper object.

Primitive vs. derived:
- ambient input: only the group property `P`;
- primitive class data: preservation of `P` along multiplicative equivalences out of a finitely
  presented group, plus the two existence clauses from the textbook definition;
- derived public API: the symmetric `iff` form of invariance under finitely presented
  isomorphisms.
-/

/-- Definition 4-4-1: a property `P` of finitely presented groups is a Markov property when it is
invariant under isomorphism of finitely presented groups, some finitely presented group has `P`,
and some finitely presented group embeds in no finitely presented group having `P`. -/
class IsMarkovProperty (P : (G : Type u) → [Group G] → Prop) : Prop where
  /-- The property is preserved along multiplicative equivalences out of a finitely presented
  group. -/
  of_mulEquiv {G H : Type u} [Group G] [Group H]
      (e : G ≃* H) (_ : IsFinitelyPresented G) :
      P G → P H
  /-- Some finitely presented group satisfies the property. -/
  exists_with_property :
    ∃ (G₁ : Type u) (_ : Group G₁) (_ : IsFinitelyPresented G₁), P G₁
  /-- Some finitely presented group cannot embed in any finitely presented group satisfying the
  property. -/
  exists_embedding_obstruction :
    ∃ (G₂ : Type u) (_ : Group G₂) (_ : IsFinitelyPresented G₂),
      ∀ {H : Type u} [Group H] (_ : IsFinitelyPresented H) (_ : P H) (f : G₂ →* H),
        ¬ Function.Injective f

namespace IsMarkovProperty

variable {P : (G : Type u) → [Group G] → Prop} [IsMarkovProperty P]

/-- A Markov property is invariant under multiplicative equivalence between finitely presented
groups. -/
theorem iff_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsFinitelyPresented G) :
    P G ↔ P H := by
  constructor
  · exact IsMarkovProperty.of_mulEquiv e hG
  · exact IsMarkovProperty.of_mulEquiv e.symm (IsFinitelyPresented.equiv e hG)

end IsMarkovProperty

end Group

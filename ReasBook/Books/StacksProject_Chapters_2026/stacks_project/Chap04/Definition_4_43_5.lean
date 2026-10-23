module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain sampling:
- Primary domain: rigid monoidal category theory.
- Core/canonical declarations inspected:
  - `ExactPairing`
  - `HasLeftDual`
  - `HasRightDual`
  - `ExactPairing.coevaluation`
  - `ExactPairing.evaluation`
- Owner abstraction: `ExactPairing Y X`.
- Layer triage:
  - `source-facing`: the fixed-pair left-duality datum exhibiting `Y` as a left dual of `X`;
  - `core/canonical`: `ExactPairing Y X`;
  - `bridge/view`: `HasLeftDual X` and `HasRightDual Y` package only the existence of some chosen
    dual object, so they are downstream owner abstractions for later existence-style statements,
    not the main owner for this fixed-pair definition.
- Primitive vs. derived:
  - primitive data: the coevaluation, evaluation, and triangle identities stored by
    `ExactPairing`;
  - derived API: the accessors `η_`, `ε_`, the owner-level existence classes `HasLeftDual X` and
    `HasRightDual Y`, and the later hom-equivalence/adjunction constructions.
-/

/- Definition 4.43.5: the textbook datum of a left dual `Y` of `X` is exactly the canonical
mathlib owner `ExactPairing Y X`, whose primitive fields are the coevaluation,
evaluation, and the two triangle identities. -/
recall ExactPairing

end CategoryTheory

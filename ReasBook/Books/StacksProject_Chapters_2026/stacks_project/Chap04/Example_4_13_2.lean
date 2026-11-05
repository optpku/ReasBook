module

public import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Example 4.13.2:
- primary domain: monomorphisms and epimorphisms in the category of sets.
- inspected owner declarations:
  `CategoryTheory.Mono`,
  `CategoryTheory.Epi`,
  `CategoryTheory.mono_iff_injective`,
  `CategoryTheory.epi_iff_surjective`.
- owner abstraction: the categorical classes `Mono` and `Epi`, with the canonical `Type`
  characterizations supplied by `mono_iff_injective` and `epi_iff_surjective`.
- primitive data: the monomorphism/epimorphism structures themselves.
- derived API: the injectivity/surjectivity reformulations specific to `Type`.
- triage: this example is a `bridge/view` recall of the canonical `Type`-level characterizations,
  so the right public surface is direct recall of the upstream theorems rather than any local
  restatement or wrapper. -/

/- Example 4.13.2 (monomorphism clause): in the category of sets, a morphism is a monomorphism
exactly when its underlying function is injective. This is the canonical theorem
`CategoryTheory.mono_iff_injective`. -/
recall mono_iff_injective

/- Example 4.13.2 (epimorphism clause): in the category of sets, a morphism is an epimorphism
exactly when its underlying function is surjective. This is the canonical theorem
`CategoryTheory.epi_iff_surjective`. -/
recall epi_iff_surjective

end CategoryTheory

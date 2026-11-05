module

public import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 7.47.5:
- primary domain: sieve pullbacks and membership in a sieve;
- sampled owner API:
  `Sieve.pullback`,
  `Sieve.pullback_eq_top_of_mem`,
  `Sieve.mem_iff_pullback_eq_top`,
  `GrothendieckTopology.pullback_stable`;
- source/core/bridge triage:
  `source-facing`: a morphism belonging to a sieve makes the pullback sieve maximal;
  `core/canonical`: the owner construction `Sieve.pullback`;
  `bridge/view`: the equivalent reformulation
  `Sieve.mem_iff_pullback_eq_top`.

Primitive data are only a sieve `S` and a morphism `f`. The maximal-pullback criterion is already
the canonical theorem API for `Sieve.pullback`, so the correct refinement is direct recall of the
owner theorem and its converse, not a parallel local wrapper.
-/

/- Lemma 7.47.5: if a morphism `f : V ⟶ U` belongs to a sieve `S` on `U`, then the pullback sieve
`S.pullback f` on `V` is maximal, equivalently it is the top sieve `⊤`, i.e. the whole
representable presheaf `h_V`. -/
recall Sieve.pullback_eq_top_of_mem

/- Companion recall: membership of `f` in `S` is equivalent to the pullback sieve `S.pullback f`
being maximal. -/
recall Sieve.mem_iff_pullback_eq_top

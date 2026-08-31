module

public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 4.17.2:
- primary domain: final functors and colimit comparison along whiskering.
- sampled owner declarations:
  `Functor.Final.colimit_pre_isIso`,
  `Functor.Final.hasColimit_comp_iff`,
  `Functor.Final.colimitIso`,
  `Functor.Final.hasColimit_of_comp`.
- best owner abstraction: `Functor.Final`.
- primitive-vs-derived split:
  primitive source data: finality of `H : I ⥤ J`;
  derived API: the comparison morphism `colimit.pre M H`, its `IsIso` instance, and the induced
    colimit-existence equivalence for `H ⋙ M`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement about the canonical comparison morphism and colimit
  existence along a final functor;
- `core/canonical`: `Functor.Final`;
- `bridge/view`: the two direct owner recalls below. -/

/- Lemma 4.17.2: if `H : I ⥤ J` is final and `M : J ⥤ C` has a colimit, then the canonical
comparison morphism `colimit.pre M H : colimit (H ⋙ M) ⟶ colimit M` is an isomorphism. This is
exactly the canonical instance `Functor.Final.colimit_pre_isIso`. -/
recall Functor.Final.colimit_pre_isIso

/- Companion to Lemma 4.17.2: for a final functor `H : I ⥤ J`, the composite diagram `H ⋙ M`
has a colimit if and only if `M` does. This is exactly the canonical theorem
`Functor.Final.hasColimit_comp_iff`. -/
recall Functor.Final.hasColimit_comp_iff

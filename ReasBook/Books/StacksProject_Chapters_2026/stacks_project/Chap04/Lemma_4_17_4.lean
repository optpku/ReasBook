module

public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe vI vJ vC uI uJ uC

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/- Domain-style sampling for Lemma 4.17.4:
- primary domain: limit comparison along initial functors in `CategoryTheory.Limits`;
- sampled owner API:
  `Functor.Initial.limitIso`,
  `Functor.Initial.hasLimit_comp_iff`,
  `Functor.Initial.hasLimit_of_comp`,
  `Functor.Final.colimitIso`;
- best owner abstraction: `Functor.Initial`;
- primitive-vs-derived split:
  primitive data: a functor `H : I ⥤ J` equipped with `H.Initial`;
  derived API: transfer of limit existence along `H` and the canonical comparison isomorphism on
    limits;
- layer triage:
  - `core/canonical`: `Functor.Initial`;
  - derived owner API: `Functor.Initial.hasLimit_of_comp`,
    `Functor.Initial.hasLimit_comp_iff`, and `Functor.Initial.limitIso`;
  - this item needs no separate `source-facing` wrapper, because Lemma 4.17.4 is exactly the
    canonical owner theorem. -/

/- Lemma 4.17.4: if `H : I ⥤ J` is initial and `M : J ⥤ C` has a limit, then the induced map
on limits is a canonical isomorphism. This is exactly the owner theorem
`Functor.Initial.limitIso`. -/
recall Initial.limitIso

end Functor
end CategoryTheory

module

public import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling for Definition 4.2.5:
- primary domain: categorical groupoids;
- sampled owner-level declarations:
  `CategoryTheory.Groupoid`,
  `CategoryTheory.IsGroupoid`,
  `CategoryTheory.Groupoid.ofIsGroupoid`;
- best owner abstraction: the source notion is already owned canonically by `Groupoid` for bundled
  data and `IsGroupoid` for the Prop-valued condition on an existing category;
- primitive owner data: `Groupoid.inv` in the bundled owner and `IsGroupoid.all_isIso` in the
  Prop-valued owner;
- derived API: `Groupoid.ofIsGroupoid` promotes the Prop-valued owner back to bundled data when a
  downstream construction needs bundled inverses.

Source/core/bridge triage:
- `source-facing`: the textbook wording that a groupoid is a category in which every morphism is an
  isomorphism;
- `core/canonical`: `Groupoid` and `IsGroupoid`;
- `bridge/view`: `Groupoid.ofIsGroupoid`, used when a downstream construction needs bundled
  inverses from the Prop-valued owner. -/

/- Definition 4.2.5: a groupoid is a category in which every morphism is an isomorphism; this is
the defining content bundled by the canonical mathlib class `Groupoid`. -/
recall Groupoid

/- Companion recall: for an already given category structure, the condition that every morphism is
an isomorphism is the canonical Prop-valued class `IsGroupoid C`. -/
recall IsGroupoid

end CategoryTheory

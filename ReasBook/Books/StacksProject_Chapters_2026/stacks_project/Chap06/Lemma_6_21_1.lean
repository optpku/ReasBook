module

public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 6.21.1:
- primary domain: sheaf pushforward along a continuous map of topological spaces;
- sampled owner declarations:
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`,
  `TopCat.Sheaf.pushforward`,
  `TopCat.Sheaf.pushforwardForgetIso`,
  `TopCat.Presheaf.pushforward`;
- owner abstraction: the canonical owner is the sheaf-level theorem
  `TopCat.Sheaf.pushforward_sheaf_of_sheaf`;
- primitive data: a continuous map `f : X ⟶ Y` and a sheaf condition on the underlying presheaf;
- derived API: the sheaf pushforward functor and its forgetful comparison to presheaf pushforward.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that the direct image of a sheaf of sets is again a
  sheaf of sets;
- `core/canonical`: `TopCat.Sheaf.pushforward_sheaf_of_sheaf`;
- `bridge/view`: the functor-level owner `TopCat.Sheaf.pushforward`, whose object part uses the
  recalled theorem.

The numbered item is only the `C := Type u` specialization of the canonical owner theorem, so the
refined file should recall that theorem directly rather than introduce a local wrapper or restate
the sheaf data as primitive structure. -/

namespace TopCat.Sheaf

/- Lemma 6.21.1: for a continuous map `f : X ⟶ Y`, the direct image of a sheaf of sets on `X`
is again a sheaf of sets on `Y`. In Lean this is the `C := Type u` specialization of the canonical
mathlib theorem `TopCat.Sheaf.pushforward_sheaf_of_sheaf`. -/
recall pushforward_sheaf_of_sheaf

end TopCat.Sheaf

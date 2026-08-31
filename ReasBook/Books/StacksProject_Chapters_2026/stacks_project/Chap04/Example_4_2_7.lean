module

public import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory

/- Example 4.2.7: a set `C` gives the discrete groupoid `Discrete C` via the canonical instance
`instGroupoidDiscrete`. Distinct objects have no morphisms between them, and every endomorphism is
the identity. -/
recall instGroupoidDiscrete

/- Domain-style sampling for Example 4.2.7:
- primary domain: discrete categories and groupoids;
- sampled owner-level declarations: `instGroupoidDiscrete`, `Discrete.isDiscrete`,
  `obj_ext_of_isDiscrete`, `Discrete.instSubsingletonDiscreteHom`;
- best owner abstraction: `IsDiscrete (Discrete C)`;
- primitive owner data: `IsDiscrete.eq_of_hom` and the induced subsingleton hom-spaces;
- derived consequences in the source text: distinct objects admit no morphisms, and every
  endomorphism is the identity. These are better used directly from the owner API than via local
  duplicate theorem names.

Source/core/bridge triage:
- `source-facing`: the example-level recall that `Discrete C` is a groupoid with discrete homs;
- `core/canonical`: `instGroupoidDiscrete`, `Discrete.isDiscrete`, `obj_ext_of_isDiscrete`,
  `Discrete.instSubsingletonDiscreteHom`;
- `bridge/view`: none. -/
recall Discrete.isDiscrete

/- Any morphism in `Discrete C` forces equality of its source and target via the owner bridge
`obj_ext_of_isDiscrete`, specialized by `Discrete.isDiscrete`. -/
recall obj_ext_of_isDiscrete

/- Every hom-space in `Discrete C` is a subsingleton, so in particular every endomorphism is the
identity. -/
recall Discrete.instSubsingletonDiscreteHom

end CategoryTheory

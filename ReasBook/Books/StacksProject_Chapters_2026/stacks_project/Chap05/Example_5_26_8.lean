module

public import Mathlib.Topology.ExtremallyDisconnected

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/- Domain-style sampling for Example 5.26.8:
- primary domain: Stone-Cech compactification of discrete spaces inside compact Hausdorff
  projectivity and extremal disconnectedness;
- inspected owner declarations:
  `StoneCech.projective`,
  `CompactT2.Projective.extremallyDisconnected`,
  `CompactT2.projective_iff_extremallyDisconnected`;
- best owner abstraction: `StoneCech.projective`, with extremal disconnectedness as derived API;
- primitive-vs-derived split: the discrete topology on `X` is the only input needed to invoke the
  canonical owner theorem `StoneCech.projective`, while the conclusion
  `ExtremallyDisconnected (StoneCech X)` is derived via the canonical bridge
  `CompactT2.Projective.extremallyDisconnected`.

Layer triage:
- `source-facing`: the textbook example that the Stone-Cech compactification of a discrete space is
  extremally disconnected;
- `core/canonical`: the owner theorem `StoneCech.projective`;
- `bridge/view`: the specialization `StoneCech.extremallyDisconnected` below.

The source item is not a new owner and should not introduce an ad hoc global wrapper instance.
The natural public surface is the owner-prefixed theorem obtained by applying the canonical bridge
from projectivity to extremal disconnectedness.
-/

namespace StoneCech

-- Proof sketch: apply the canonical projectivity theorem for the Stone-Cech compactification of a
-- discrete space, then pass to the derived extremal-disconnectedness API.
/-- Example 5.26.8: the Stone-Cech compactification of a discrete space is extremally
disconnected. -/
theorem extremallyDisconnected : ExtremallyDisconnected (StoneCech X) :=
  CompactT2.Projective.extremallyDisconnected projective

end StoneCech

end

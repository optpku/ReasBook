module

public import stacks_project.Chap06.Definition_6_7_4
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Example 6.17.4:
- primary domain: set-valued sheaves on a topological space, specifically the comparison between
  the canonical constant sheaf and the source-facing sheaf of locally constant functions;
- sampled owner API:
  `CategoryTheory.constantSheaf`,
  `locallyConstantSheaf`,
  `constantSheafToLocallyConstantSheaf`,
  `constantSheafToLocallyConstantSheaf_isIso`;
- source/core/bridge triage:
  `source-facing`: the sheaf of locally constant `A`-valued functions on `X`;
  `core/canonical`: `CategoryTheory.constantSheaf`;
  `bridge/view`: `constantSheafToLocallyConstantSheaf`, while the isomorphism fact for that
  comparison belongs to the derived API.

The owner abstraction for this example is therefore the project-level bridge
`constantSheafToLocallyConstantSheaf`, not a new `Iso` wrapper around it. Primitive data are only
the space `X`, the value type `A`, and the source-facing sheaf `locallyConstantSheaf X A`; the
`IsIso` fact for the comparison morphism belongs to derived API.
-/

/- Example 6.17.4: the canonical comparison from the constant sheaf with value `A` to the
source-facing sheaf of locally constant `A`-valued functions is the upstream bridge
`constantSheafToLocallyConstantSheaf`, and its invertibility is the companion theorem
`constantSheafToLocallyConstantSheaf_isIso`. -/
recall constantSheafToLocallyConstantSheaf

recall constantSheafToLocallyConstantSheaf_isIso

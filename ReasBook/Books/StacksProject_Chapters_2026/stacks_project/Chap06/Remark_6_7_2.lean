module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits Opposite TopCat

universe u v

/- Domain-style sampling for Remark 6.7.2:
- primary domain: sheaves on a topological space, evaluated on the empty open and on disjoint
  unions of opens;
- sampled owner API:
  `TopCat.Sheaf.isTerminalOfEmpty`,
  `TopCat.Sheaf.isProductOfDisjoint`,
  `Types.isTerminalEquivUnique`,
  `IsTerminal`;
- owner abstraction: the core/canonical owner for the empty-open clause is the terminal-object
  statement `TopCat.Sheaf.isTerminalOfEmpty`;
- primitive data: only the sheaf `F`;
- derived API: the `Type`-valued singleton-section reformulation, obtained from
  `Types.isTerminalEquivUnique`.

Source/core/bridge triage:
- `source-facing`: the remark that a sheaf has a final object of sections over the empty open, and
  that disjoint unions of opens give binary products of sections;
- `core/canonical`: `TopCat.Sheaf.isTerminalOfEmpty` and `TopCat.Sheaf.isProductOfDisjoint`;
- `bridge/view`: the `Unique` instance below, which is the `Type`-specialization of terminality.

The file already uses the canonical sheaf owners directly, so the only local declaration kept here
is the derived singleton-section instance rather than a parallel wrapper theorem. -/

/- Remark 6.7.2: for any sheaf on a topological space, the sections over the empty open are a
final object in the target category. -/
recall TopCat.Sheaf.isTerminalOfEmpty

/- In particular, for a sheaf of types or sets, the sections over the empty open form a singleton
type. -/
noncomputable instance {X : TopCat.{u}} (F : X.Sheaf (Type v)) :
    Unique (F.obj.obj (op ⊥)) :=
  Types.isTerminalEquivUnique _ F.isTerminalOfEmpty

/- Companion recall: if `U` and `V` are disjoint opens, then the sheaf condition identifies the
sections on `U ⊔ V` as the binary product of the sections on `U` and on `V`. -/
recall TopCat.Sheaf.isProductOfDisjoint

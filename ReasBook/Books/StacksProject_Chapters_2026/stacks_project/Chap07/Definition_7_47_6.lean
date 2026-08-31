module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.47.6:
- primary domain: Grothendieck topologies on a category, expressed by covering sieves and their
  axioms;
- sampled canonical declarations:
  `CategoryTheory.GrothendieckTopology`,
  `GrothendieckTopology.top_mem`,
  `GrothendieckTopology.pullback_stable`,
  `GrothendieckTopology.transitive`;
- best owner abstraction:
  the notion is owned directly by the mathlib structure `GrothendieckTopology C`;
- source/core/bridge triage:
  `source-facing`: a topology on `C` given by covering sieves that contain the maximal sieve, are
  stable under pullback, and satisfy transitivity;
  `core/canonical`: `GrothendieckTopology C`;
  `bridge/view`: the derived owner API `top_mem`, `pullback_stable`, and `transitive`.

Primitive data are exactly the covering sieves together with these axioms. The axiom accessors are
derived API from the canonical owner, so any local structure restating those fields would be
duplicate wheel packaging and should be deleted rather than preserved.
-/

/- Definition 7.47.6: a topology on a category `C` is the canonical mathlib structure
`CategoryTheory.GrothendieckTopology`, namely a rule assigning to each object `U` a set `J(U)` of
sieves on `U` such that covering sieves are stable under pullback, satisfy the usual transitivity
axiom, and contain the maximal sieve. -/
recall GrothendieckTopology

end

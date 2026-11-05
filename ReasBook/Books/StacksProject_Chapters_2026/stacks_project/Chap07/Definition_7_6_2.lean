module

public import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.6.2:
- primary domain: sites presented by set-sized covering families on a category;
- sampled owner API:
  `Precoverage`,
  `Pretopology`,
  `Pretopology.toPrecoverage`,
  `Pretopology.toGrothendieck`,
  `Precoverage.toPretopology`;
- best owner abstraction: `Pretopology C`;
- primitive data: the covering presieves of a chosen precoverage;
- derived API: the three site axioms and the associated Grothendieck topology.

Source/core/bridge triage:
- `source-facing`: the Stacks Project notion of a site given by set-sized covering families;
- `core/canonical`: mathlib's `Pretopology C`, whose docstring explicitly records that Stacks
  calls a category with a pretopology a site;
- `bridge/view`: the underlying `Precoverage` and the generated Grothendieck topology.

The file therefore recalls the canonical owner `Pretopology` directly rather than introducing a
parallel local `Site` wrapper or a conjunction of the three axioms. -/

section

variable [HasPullbacks C]

/- Definition 7.6.2: a site is a category equipped with covering families with fixed target,
containing singleton isomorphism covers, closed under composition of covering families, and stable
under base change. In mathlib this is the canonical owner `Pretopology C`. -/
recall Pretopology

section

variable (J : Pretopology C)

/- Companion check: the raw set of covering families underlying a pretopology is its inherited
`Precoverage`. -/
#check (J.toPrecoverage)

/- Companion check: the pretopology site generates its associated Grothendieck topology. -/
#check (J.toGrothendieck)

end

section

variable (J : Precoverage C)
variable [J.HasIsos] [J.IsStableUnderBaseChange] [J.IsStableUnderComposition]

/- Bridge recall: a raw precoverage satisfying the three owner-level axioms upgrades to the
canonical pretopology owner. -/
recall Precoverage.toPretopology

end

end

end CategoryTheory

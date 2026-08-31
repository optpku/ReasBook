module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/- Domain-style sampling for Definition 7.11.1:
- primary domain: injective and surjective morphisms of set-valued sheaves on a Grothendieck
  site, expressed through the canonical sheaf-local owner predicates;
- sampled canonical declarations:
  `CategoryTheory.Sheaf.IsLocallyInjective`,
  `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`,
  `CategoryTheory.Sheaf.IsLocallySurjective`,
  `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`;
- best owner abstraction: for the sheaf-level source notion, the owner predicates are
  `CategoryTheory.Sheaf.IsLocallyInjective` and `CategoryTheory.Sheaf.IsLocallySurjective`;
- primitive data: a morphism of sheaves of sets;
- derived API: the objectwise injectivity criterion on sections and later categorical
  characterizations such as `Mono`/`Epi`.

Source/core/bridge triage:
- `source-facing`: the Stacks predicates that a morphism of sheaves of sets is injective
  objectwise on sections and surjective locally on the site;
- `core/canonical`: the owner predicates `CategoryTheory.Sheaf.IsLocallyInjective` and
  `CategoryTheory.Sheaf.IsLocallySurjective`;
- `bridge/view`: the companion theorem
  `CategoryTheory.Sheaf.isLocallyInjective_iff_injective`, which rewrites the local injectivity
  owner in the textbook objectwise form; for later chapter lemmas, the surjectivity owner also
  has the categorical bridge `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`.

No extra chapter-local definition is warranted here: the source notions are already owned by the
sheaf namespace, and this file should stay at the canonical recall layer. -/

/- Definition 7.11.1 (1): for a morphism of sheaves of sets, the canonical injectivity owner is
`Sheaf.IsLocallyInjective`; for sheaves this agrees with the textbook objectwise injectivity
condition recorded in the companion theorem below. -/
recall IsLocallyInjective

/- Definition 7.11.1 (1), canonical objectwise form: the exact mathlib companion theorem says
that a morphism of sheaves is locally injective exactly when each component map on the
underlying presheaf is injective. -/
recall isLocallyInjective_iff_injective

/- Definition 7.11.1 (2): a morphism of sheaves of sets is surjective when every section of the
target is locally in the image; this is the canonical notion
`Sheaf.IsLocallySurjective`. -/
recall IsLocallySurjective

end Sheaf

end CategoryTheory

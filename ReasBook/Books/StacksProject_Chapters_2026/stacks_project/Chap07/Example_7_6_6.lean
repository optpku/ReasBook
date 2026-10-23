module

public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category A]

/- Domain-style sampling for Example 7.6.6:
- primary domain: chaotic Grothendieck topologies and the associated sheaf categories;
- sampled canonical declarations:
  `GrothendieckTopology.trivial`,
  `GrothendieckTopology.trivial_eq_bot`,
  `sheafBotEquivalence`,
  `Pretopology.trivial`;
- best owner abstraction:
  the source-facing chaotic site is owned canonically at the topology layer by
  `GrothendieckTopology.trivial C`, while `Pretopology.trivial` is only the stronger pullback-based
  presentation available when pullbacks exist;
- source/core/bridge triage:
  `source-facing`: the chaotic topology on `C` and its sheaf category;
  `core/canonical`: `GrothendieckTopology.trivial` together with `sheafBotEquivalence`;
  `bridge/view`: `GrothendieckTopology.trivial_eq_bot`, which identifies the source-facing chaotic
    topology with the bottom topology used by `sheafBotEquivalence`.

Primitive data are only the category `C` and the target category `A`. The induced sheaf category
equivalence is derived from the canonical topology owner, so the local `Coverage` presentation is
duplicate wheel data and should be deleted rather than preserved as a parallel owner.
-/

/- Example 7.6.6: the chaotic site on `C` is the canonical trivial Grothendieck topology. -/
recall GrothendieckTopology.trivial

/- Example 7.6.6: sheaves on the chaotic topology on `C` with values in `A` are canonically
equivalent to `A`-valued presheaves on `C`. This is the bottom-topology equivalence specialized
along `GrothendieckTopology.trivial_eq_bot`. -/
#check
  (show Sheaf (GrothendieckTopology.trivial C) A ≌ Cᵒᵖ ⥤ A from by
    simpa [GrothendieckTopology.trivial_eq_bot] using (sheafBotEquivalence A))

end CategoryTheory

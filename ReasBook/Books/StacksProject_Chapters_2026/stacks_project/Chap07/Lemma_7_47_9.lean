module

public import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C]
variable (Js : Set (GrothendieckTopology C))

/- Domain-style sampling for Lemma 7.47.9:
- primary domain: the complete lattice of Grothendieck topologies on a fixed category;
- sampled canonical declarations:
  `GrothendieckTopology.instCompleteLattice`,
  `GrothendieckTopology.mem_sInf`,
  `GrothendieckTopology.isGLB_sInf`,
  `isLUB_sSup`;
- layer triage for this item:
  `source-facing`: arbitrary intersections of Grothendieck topologies and the least topology finer
  than a given family;
  `core/canonical`: `GrothendieckTopology C` with its upstream `CompleteLattice` instance;
  `bridge/view`: the pointwise covering-sieve characterization of `sInf` given by
  `GrothendieckTopology.mem_sInf`.

Primitive data are only the category `C` and the set `Js`. The infimum and supremum constructions
are already packaged by the canonical complete-lattice owner, so this file should recall that owner
directly and keep only the source-facing infimum API as companions.
-/

/- Lemma 7.47.9: Grothendieck topologies on `C` form a complete lattice, so arbitrary infima and
suprema exist. -/
recall GrothendieckTopology.instCompleteLattice : CompleteLattice (GrothendieckTopology C)

/- Companion recall for Lemma 7.47.9 (1): for a set `Js` of Grothendieck topologies on a category
`C`, the pointwise intersection rule `J(U) = ⋂_{J ∈ Js} J(U)` is again a Grothendieck topology. In
mathlib this is the infimum topology `sInf Js`, and `GrothendieckTopology.mem_sInf` states exactly
that a sieve is covering for `sInf Js` if and only if it is covering for every `J ∈ Js`. -/
recall GrothendieckTopology.mem_sInf {U : C} (S : Sieve U) :
  S ∈ (sInf Js) U ↔ ∀ J ∈ Js, S ∈ J U

/- Companion recall for Lemma 7.47.9 (2): the intersection topology `sInf Js` is the greatest
lower bound of `Js`, which is the complete-lattice formulation of the source's closure under
arbitrary intersections. Suprema continue to come from the recalled complete-lattice owner. -/
recall GrothendieckTopology.isGLB_sInf (s : Set (GrothendieckTopology C)) : IsGLB s (sInf s)

end

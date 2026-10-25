module

public import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Domain-style sampling for Lemma 7.13.2:
- primary domain: continuous functors of Grothendieck sites and inverse-image preservation of
  sheaves of sets;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.op_comp_isSheaf_of_types`,
  `Functor.op_comp_isSheaf`,
  `Functor.sheafPushforwardContinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project statement that the inverse-image presheaf of a sheaf of
  sets along a continuous functor is again a sheaf;
  `core/canonical`: the continuity owner `Functor.IsContinuous` together with the theorem
  `Functor.op_comp_isSheaf_of_types`;
  `bridge/view`: `Functor.op_comp_isSheaf` and `Functor.sheafPushforwardContinuous`, which
  package the same preservation result for arbitrary target categories and as a functor on
  sheaves.

Primitive data are only the functor of sites, the two Grothendieck topologies, the continuity
instance, and the input sheaf. The resulting sheaf condition on `u.op ⋙ ℱ.obj` is derived API
from the canonical owner theorem, so this file should recall that theorem directly rather than
reintroducing a parallel local wrapper. -/

/- Lemma 7.13.2: if `u : C ⥤ D` is a continuous functor of sites and `ℱ` is a sheaf of sets on
`(D, K)`, then the inverse-image presheaf `u.op ⋙ ℱ.obj` on `(C, J)` is again a sheaf. This is
exactly the canonical site-theoretic owner
`Functor.op_comp_isSheaf_of_types`. -/
recall Functor.op_comp_isSheaf_of_types

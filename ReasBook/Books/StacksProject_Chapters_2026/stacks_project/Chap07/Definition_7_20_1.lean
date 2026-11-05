module

public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 7.20.1:
- primary domain: Grothendieck topologies and cocontinuous functors between sites;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `CategoryTheory.Functor.cover_lift`,
  `CategoryTheory.isCocontinuous_comp`,
  `CategoryTheory.ran_isSheaf_of_isCocontinuous`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project definition that pullbacks of covering sieves along a
  functor are covering;
  `core/canonical`: `CategoryTheory.Functor.IsCocontinuous`;
  `bridge/view`: the covering-family refinement reading of `Functor.cover_lift`.

This file is targeting the `core/canonical` layer: the source notion is already owned upstream by
`Functor.IsCocontinuous`, so the correct refinement is direct recall of that owner rather than a
parallel local wrapper restating its field.

Primitive data are only the functor and the two Grothendieck topologies. The sieve pullback
condition is already the owner field `cover_lift`, so the family-based textbook phrasing belongs
in explanatory text rather than a parallel local declaration.
-/

/- Definition 7.20.1: the Stacks Project notion of a cocontinuous functor of sites is the
canonical class `Functor.IsCocontinuous`. Its defining field says that every
covering sieve on `u(U)` pulls back to a covering sieve on `U`; equivalently, every covering
family on `u(U)` admits a covering-family refinement after pullback along `u`, as in the
textbook formulation. -/
recall CategoryTheory.Functor.IsCocontinuous

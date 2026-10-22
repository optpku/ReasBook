/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u}
variable (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

/-!
Primary domain: one-relator groups and virtual torsion-freeness.

Layer triage:
- `source-facing`: a one-relator group `G = (X; r)` and the textbook conclusion that `G` has a
  torsion-free normal subgroup of finite index.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `FiniteIndexNormalSubgroup` for normal finite-index subgroups, and `IsMulTorsionFree` for
  torsion-freeness of the subgroup carrier.
- `bridge/view`: the source phrase “`G` has a torsion-free normal subgroup of finite index” is the
  bundled owner-level witness `N : FiniteIndexNormalSubgroup Q` together with the torsion-free
  property of `N.toSubgroup`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the established project owner for one-relator groups in
   this chapter, used throughout nearby files such as Propositions `2-5-17`, `2-5-21`, and
   `2-5-29`.
2. `FiniteIndexNormalSubgroup` from mathlib is the canonical owner abstraction for normal
   subgroups of finite index; earlier project items already use it directly, for example
   Proposition `1-4-9`.
3. `IsMulTorsionFree` is mathlib's canonical torsion-free predicate, and
   `isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower` from Proposition
   `2-5-17` shows the same one-relator domain already records torsion statements at that owner
   level.
4. `exists_torsionFree_finiteIndexNormalSubgroup_of_isFGroup` from Proposition `3-7-13` uses the
   same bundled conclusion shape in the broader F-group setting, confirming that the finite-index
   normal subgroup witness is derived API rather than primitive presentation data.

Primitive vs. derived:
the primitive public data are only the relator `r` and the canonical one-relator owner `Q`; the
finite-index normal subgroup witness is the derived conclusion, so no parallel presentation wrapper
or extra packaging belongs in the public API.
-/

-- Proof sketch: apply the classical finite-cover theorem for one-relator groups. In Magnus's
-- theory one constructs a finite-index normal subgroup whose associated covering complex has free
-- fundamental group, hence is torsion-free by Proposition `1-2-18`.
/-- Proposition 2-5-20: every one-relator group `G = (X; r)` has a torsion-free normal subgroup
of finite index. In the canonical owner form `Q = PresentedGroup (Set.singleton r)`, this is
expressed by a bundled finite-index normal subgroup whose underlying subgroup is torsion free. -/
theorem exists_torsionFree_finiteIndexNormalSubgroup_of_oneRelator
    : ∃ N : FiniteIndexNormalSubgroup Q, IsMulTorsionFree N.toSubgroup := sorry

end

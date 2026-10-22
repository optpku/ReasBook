/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

/-!
Primary domain: planar Cayley complexes and the structure of abelian subgroups in planar groups.

Layer triage:
- `source-facing`: a planar Cayley complex `C(X; R)` realizing the planar group
  `PresentedGroup R`, together with an abelian subgroup of that presented group.
- `core/canonical`: `PresentedGroup R` is the chapter owner for the ambient group,
  `CayleyComplex.Coordinates` is the owner for the chosen Cayley-complex realization,
  `C.EmbedsInPlane` is the chapter owner for planarity of that realization, `Subgroup G` is the
  owner for a subgroup, `IsMulCommutative H` is the canonical abelianity predicate on the subgroup
  type, and `IsCyclic` together with `Multiplicative (FreeAbelianGroup (Fin 2))` give the two
  classification alternatives.
- `bridge/view`: the textbook phrase “planar group” is rendered through a chosen planar Cayley
  presentation, matching the existing chapter interface for planarity.

Domain sampling:
1. `CayleyComplex.Coordinates.PresentationCoordinates C R` from Proposition `3-4-1` is the owner
   abstraction for an actual Cayley complex over the presented group.
2. `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` is the chapter owner for the planar
   hypothesis.
3. Nearby Proposition `2-5-23` uses `Nonempty (H ≃* Multiplicative (FreeAbelianGroup (Fin 2)))`
   as the established encoding of “free abelian of rank `2`”.
4. `IsCyclic` and `IsMulCommutative` are the canonical mathlib predicates for the cyclic and
   abelian branches of the subgroup classification.

Primitive vs. derived:
- primitive data: the planar Cayley presentation `(X; R, C, coords, hplanar)` and the chosen
  subgroup `H`;
- derived API: the subgroup classification conclusion. No extra wrapper structure for “planar
  group” is introduced, since the chapter already expresses planarity through the existence of a
  planar Cayley presentation.
-/

namespace CayleyComplex.Coordinates

section

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

local notation "PG" => PresentedGroup R
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 3-7-10: every abelian subgroup of a presented group admitting a planar Cayley
realization is either cyclic or free abelian of rank `2`. The source continues with a
classification of the planar groups containing a rank-two free abelian subgroup; that
exceptional-family list is not present in the current excerpt, so only the visible subgroup
dichotomy is formalized here. -/
-- Proof sketch: use the planar Cayley-complex realization to place the ambient presented group in
-- the Chapter III planar setting. The geometric restrictions on commuting deck transformations
-- force any abelian subgroup to act either through a single translation direction, giving a cyclic
-- subgroup, or through a lattice action on the plane, giving the standard free abelian group of
-- rank `2`.
theorem abelian_subgroup_of_planar_presentedGroup_isCyclic_or_freeAbelian_rank_two
    (coords : PresentationCoordinates C R)
    (hplanar : C.EmbedsInPlane)
    (H : Subgroup PG) (hab : IsMulCommutative H) :
    IsCyclic H ∨ Nonempty (H ≃* RankTwoFreeAbelian) := sorry

end

end CayleyComplex.Coordinates

/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_13
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_4
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_10

universe u v

set_option autoImplicit false

noncomputable section

open FGroupPresentation
open CayleyComplex.Coordinates

/-!
Primary domain: planar groups, abelian subgroups, and Euclidean `F`-group presentations.

Layer triage:
- `source-facing`: a group `G` equipped with a planar Cayley presentation, together with an abelian
  subgroup `H ≤ G` or, for the Euclidean classification clause, the existence of a rank-two free
  abelian subgroup of `G`.
- `core/canonical`: `PresentedGroup R` for the chosen presentation, `CayleyComplex.Coordinates`
  for the actual Cayley complex, `TwoComplex.EmbedsInPlane` for planarity,
  `IsMulCommutative`/`IsCyclic` for subgroup structure, `Multiplicative (FreeAbelianGroup (Fin 2))`
  for the rank-two free abelian group, and `FGroupPresentation.orientableStandardRelators` /
  `FGroupPresentation.nonorientableStandardRelators` for the seven standard presentations named in
  the proposition.
- `bridge/view`: a multiplicative equivalence `PresentedGroup R ≃* G` transports the canonical
  presented-group statement to an abstract planar group.

Domain sampling:
1. `PresentedGroup R` is the project owner abstraction for groups given by generators and
   relators.
2. `CayleyComplex.Coordinates.PresentationCoordinates C R` together with `C.EmbedsInPlane` is
   the chapter owner for a planar Cayley-complex realization of a group.
3. `IsCyclic`, `IsMulCommutative`, and `Multiplicative (FreeAbelianGroup (Fin 2))` are the
   standard mathlib-facing abstractions for the subgroup dichotomy in the proposition.
4. Proposition `3-5-4` supplies the canonical standard-presentation layer for all seven Euclidean
   cases, while its torsion-free `p = 0` equivalences to the Chapter `2` surface-group owners are
   bridge lemmas rather than the main classification surface here.

Primitive vs. derived:
- primitive public data: the planar Cayley presentation of `G`, the subgroup `H`, and the
  abelianity or rank-two free-abelian hypotheses on `H`;
- derived conclusions: the cyclic/rank-two dichotomy for `H`, and the restriction of the ambient
  planar group to the seven Euclidean standard presentations.
-/

section

variable {G : Type u} [Group G]
variable {X : Type v} {R : Set (FreeGroup X)} {C : TwoComplex}

local notation "PG" => PresentedGroup R
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 3-7-11: every abelian subgroup of a planar group is either cyclic or free abelian
of rank `2`. -/
-- Proof sketch: use the planar presentation to reduce to the Section `5` classification of planar
-- groups into `F`-groups and free products of cyclic groups. Abelian subgroups of the free-product
-- branch are cyclic, while abelian subgroups of the `F`-group branch are analyzed through the
-- standard presentation: torsion cases are cyclic by the self-normalizing root argument, and the
-- torsion-free case reduces via the `p = 0` bridge to the Chapter `2` one-relator classification,
-- leaving only the cyclic and rank-two free abelian possibilities.
theorem abelian_subgroup_of_planar_group_isCyclic_or_freeAbelian_rank_two
    (coords : PresentationCoordinates C R)
    (e : PG ≃* G) (hplanar : C.EmbedsInPlane)
    (H : Subgroup G) (hab : IsMulCommutative H) :
    IsCyclic H ∨ Nonempty (H ≃* RankTwoFreeAbelian) := by
  let H' : Subgroup PG := H.comap (e : PG →* G)
  let eH : H' ≃* H :=
    (MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm' e H)).trans
      (e.symm.subgroupMap H).symm
  have hab' : IsMulCommutative H' := by
    letI : IsMulCommutative H := hab
    refine IsMulCommutative.of_comm fun a b ↦ ?_
    apply eH.injective
    simpa using mul_comm' (eH a) (eH b)
  have hH' :
      IsCyclic H' ∨ Nonempty (H' ≃* RankTwoFreeAbelian) :=
    abelian_subgroup_of_planar_presentedGroup_isCyclic_or_freeAbelian_rank_two
      coords hplanar H' hab'
  rcases hH' with hcyc | hfree
  · exact Or.inl ((MulEquiv.isCyclic eH).mp hcyc)
  · rcases hfree with ⟨efree⟩
    exact Or.inr ⟨eH.symm.trans efree⟩

/-- A planar group containing a rank-two free abelian subgroup has one of the seven Euclidean
standard presentations from the textbook list. -/
-- Proof sketch: the preceding dichotomy forces the subgroup to lie in the rank-two free abelian
-- branch. The planar presentation therefore falls in the `F`-group case, and the Euclidean
-- classification of `F`-groups with abelian subgroup `ℤ²` reduces the ambient presentation to one
-- of the seven standard Euclidean presentations: the torsion-free orientable or nonorientable
-- cases, or one of the five exceptional nonorientable standard presentations with
-- torsion signatures `(2,2)`, `(2,2,2,2)`, `(2,3,6)`, `(2,4,4)`, or `(3,3,3)`.
theorem planar_group_with_rank_two_freeAbelian_subgroup_has_standard_euclidean_presentation
    (coords : PresentationCoordinates C R)
    (e : PG ≃* G) (hplanar : C.EmbedsInPlane)
    (hH : ∃ H : Subgroup G, Nonempty (H ≃* RankTwoFreeAbelian)) :
    Nonempty (PresentedGroup (orientableStandardRelators 0 1 (fun i ↦ nomatch i)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 0 2 (fun i ↦ nomatch i)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 2 1 (fun _ ↦ 2)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 4 0 (fun _ ↦ 2)) ≃* G) ∨
      Nonempty
        (PresentedGroup
          (nonorientableStandardRelators 3 0
            (fun i ↦
              match i.1 with
              | 0 => 2
              | 1 => 3
              | _ => 6)) ≃* G) ∨
      Nonempty
        (PresentedGroup
          (nonorientableStandardRelators 3 0
            (fun i ↦
              match i.1 with
              | 0 => 2
              | _ => 4)) ≃* G) ∨
      Nonempty (PresentedGroup (nonorientableStandardRelators 3 0 (fun _ ↦ 3)) ≃* G) := sorry

end

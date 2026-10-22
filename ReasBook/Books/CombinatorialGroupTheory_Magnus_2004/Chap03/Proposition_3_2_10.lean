/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_6
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.SingleObj Quiver
open IsFreeGroupoid
open IsFreeGroupoid.SpanningTree

noncomputable section

local instance root_loopGroup_isFree {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    IsFreeGroup (End (show G from Quiver.root T)) := by
  simpa using IsFreeGroupoid.SpanningTree.endIsFree T

-- Layer triage:
-- `source-facing`: a finite connected `1`-complex `C`, a base vertex `v : C`, and the rank claim
-- for the fundamental group `π(C, v)`, expressed using the canonical connectedness predicate on
-- the symmetrified quiver and the owner-level notion `OneComplex.GeometricEdge`.
-- `core/canonical`: `OneComplex.fundamentalGroup` is the owner abstraction for `π(C, v)`.
-- `IsFreeGroupoid.SpanningTree.endIsFree`, `Quiver.geodesicSubtree`, and
-- `FreeGroupBasis.cardinal_eq` are the canonical free-groupoid/tree-counting tools behind the
-- proof.
-- `bridge/view`: the spanning-tree complement theorem for a free groupoid loop group is the
-- internal comparison statement from which the source-facing `OneComplex` theorem is derived.
-- Domain sampling:
-- 1. `OneComplex.fundamentalGroup` is the chapter owner for the fundamental group `π(C, v)`.
-- 2. `Quiver.IsStronglyConnected (Quiver.Symmetrify C)` is the intrinsic connectedness owner for
--    the underlying `1`-complex, replacing the bridge-level rooted-connectedness hypothesis.
-- 3. `OneComplex.GeometricEdge` is the owner abstraction for unoriented edges of a `1`-complex.
-- 4. `IsFreeGroupoid.SpanningTree.endIsFree` is the owner theorem giving freeness of the root
--    loop group of a spanning tree in a free groupoid.
-- 5. `Quiver.geodesicSubtree` is the canonical rooted spanning tree attached to a connected quiver.
-- 6. `FreeGroupBasis` is mathlib's canonical structure for “free on a specified generating type”.
-- 7. `IsFreeGroup.Generators` is the canonical generator type used to speak about the rank of a
--    free group via `Nat.card`.
-- 8. `FreeGroupBasis.cardinal_eq` is the standard bridge equating the cardinalities of two bases.

open scoped Classical in
/-- The complement of a spanning tree indexes a free basis of the root loop group. -/
-- Proof sketch: unpack the universal-property construction implicit in
-- `IsFreeGroupoid.SpanningTree.endIsFree`; the non-tree generating edges are exactly the free
-- generators produced by the Nielsen-Schreier spanning-tree argument.
private def root_loopGroup_basis_of_arborescence {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    FreeGroupBasis (((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _))
      (End (show G from Quiver.root T)) :=
  FreeGroupBasis.ofUniqueLift ((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)
    (fun e ↦ loopOfHom T (of e.val.hom))
    (by
      intro X _ f
      let f' : Labelling (IsFreeGroupoid.Generators G) X := fun a b e ↦
        if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine ⟨F'.mapEnd _, ?_, ?_⟩
      · suffices ∀ {x y} (q : x ⟶ y), F'.map (loopOfHom T q) = (F'.map q : X) by
          rintro ⟨⟨a, b, e⟩, h⟩
          change F'.map (loopOfHom T (of e)) = f ⟨⟨a, b, e⟩, h⟩
          rw [this, hF']
          exact dif_neg h
        intro x y q
        suffices ∀ {a} (p : Path (root T) a), F'.map (homOfPath T p) = 1 by
          simp only [this, treeHom, comp_as_mul, inv_as_inv, loopOfHom, inv_one, mul_one,
            one_mul, Functor.map_inv, Functor.map_comp]
        intro a p
        induction p with
        | nil =>
            change F'.map (𝟙 (show G from Quiver.root T)) = 1
            rw [F'.map_id, id_as_one]
        | cons p e ih =>
            rw [homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
            rcases e with ⟨e | e, eT⟩
            · rw [hF']
              exact dif_pos (Or.inl eT)
            · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
              exact dif_pos (Or.inr eT)
      · intro E hE
        ext x
        suffices (functorOfMonoidHom T E).map x = F'.map x by
          erw [Functor.mapEnd_apply]
          change E (loopOfHom T x) = F'.map x at this
          change
            E
                (treeHom T (show G from Quiver.root T) ≫ x ≫
                  inv (treeHom T (show G from Quiver.root T))) =
              F'.map x at this
          have hroot : treeHom T (show G from Quiver.root T) = 𝟙 _ := by
            change treeHom T (show G from Quiver.root T) = 𝟙 _
            exact treeHom_root T
          have hx :
              treeHom T (show G from Quiver.root T) ≫ x ≫
                inv (treeHom T (show G from Quiver.root T)) =
              x := by
            rw [hroot]
            calc
              𝟙 _ ≫ x ≫ inv (𝟙 _) = x ≫ inv (𝟙 _) := by
                simp
              _ = x ≫ 𝟙 _ := by rw [IsIso.inv_id]
              _ = x := by simp
          have hxE :
              E
                  (treeHom T (show G from Quiver.root T) ≫ x ≫
                    inv (treeHom T (show G from Quiver.root T))) =
                E x := by
            simpa using congrArg E hx
          exact hxE.symm.trans this
        congr
        apply uF'
        intro a b e
        change E (loopOfHom T (of e)) = dite _ _ _
        split_ifs with h
        · rw [loopOfHom_eq_id T e h, ← End.one_def]
          simpa using E.map_one
        · exact hE ⟨⟨a, b, e⟩, h⟩)

/-- Companion bridge theorem: in a free groupoid with a chosen spanning tree, the root loop group
has rank equal to the number of generating edges outside the tree. -/
private theorem root_loopGroup_rank_eq_card_spanningTree_complement
    {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
    (T : WideSubquiver (Symmetrify <| IsFreeGroupoid.Generators G)) [Arborescence T] :
    Nat.card (IsFreeGroup.Generators (End (show G from Quiver.root T))) =
      Nat.card (((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)) := by
  have hcard :=
    (root_loopGroup_basis_of_arborescence T).cardinal_eq
      (IsFreeGroup.basis (End (show G from Quiver.root T)))
  simpa [Nat.card, Cardinal.toNat_lift] using congrArg Cardinal.toNat hcard.symm

namespace OneComplex

attribute [local instance] fundamentalGroup_isFree

/-- Proposition 3-2-10: if `C` is a connected `1`-complex with finitely many oriented edges and
`v` is a base vertex, then the fundamental group `π(C, v)` has rank `γ₁ - γ₀ + 1`.

Here `γ₁` is expressed canonically as `Nat.card (GeometricEdge C)` and `γ₀` as `Nat.card C`.
The intrinsic owner hypothesis
`hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C)` replaces the bridge-level
rooted-connectedness assumption, while still providing the rooted connectivity needed internally
for the spanning-tree argument. Edge finiteness together with connectedness forces the vertex type
to be finite, so no separate vertex-finiteness binder belongs in the source-facing statement. -/
theorem fundamentalGroup_rank_eq_card_geometricEdges_sub_card_vertices_add_one
    (C : OneComplex.{u, v}) [Finite C.Edge]
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C)) (v : C) :
    Nat.card (IsFreeGroup.Generators (π(C, v))) =
      Nat.card (GeometricEdge C) - Nat.card C + 1 := by
  sorry

end OneComplex

/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open scoped FundamentalGroupoid

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- The canonical functor from the one-object category `π₁(X,x)` to the fundamental groupoid
`Π(X)` sends the unique object to the basepoint `x`. -/
-- Proof sketch: the object part of `SingleObj.functor` is definitionally the chosen object
-- `FundamentalGroupoid.mk x`.
theorem fundamental_group_inclusion_obj (x : X) :
    (SingleObj.functor (MonoidHom.id (FundamentalGroup X x))).obj
        (SingleObj.star (FundamentalGroup X x)) =
      FundamentalGroupoid.mk x := rfl

/-- Helper for Proposition 2.5.7: equality of fundamental-groupoid objects induced by equality of
points in the space. -/
lemma fundamental_groupoid_mk_eq {X : Type u} {x y : X} (h : x = y) :
    FundamentalGroupoid.mk x = FundamentalGroupoid.mk y := by
  -- Object equality in the fundamental groupoid is induced directly from equality in the space.
  cases h
  rfl

/-- Helper for Proposition 2.5.7: choose an isomorphism from the basepoint object to any object of
`Π(X)`, using the identity when the target object is the basepoint itself. -/
noncomputable def basepoint_path_iso (x y : X) [PathConnectedSpace X] :
    FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
  letI : DecidableEq X := Classical.decEq X
  if h : y = x then
    eqToIso (fundamental_groupoid_mk_eq h.symm)
  else
    (Groupoid.isoEquivHom _ _).symm (FundamentalGroupoid.fromPath ⟦PathConnectedSpace.somePath x y⟧)

/-- Helper for Proposition 2.5.7: the chosen isomorphism at the basepoint is literally the identity
isomorphism. -/
lemma basepoint_path_iso_self (x : X) [PathConnectedSpace X] :
    basepoint_path_iso x x = Iso.refl (FundamentalGroupoid.mk x) := by
  -- The special case in `basepoint_path_iso` forces the self-isomorphism to be reflexive.
  simp [basepoint_path_iso]

/-- Helper for Proposition 2.5.7: transport every morphism of `Π(X)` back to a loop at the chosen
basepoint `x`. -/
def fundamental_groupoid_to_single_obj (x : X) [PathConnectedSpace X] :
    FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x) where
  obj _ := SingleObj.star (FundamentalGroup X x)
  map {y z} f :=
    FundamentalGroup.fromArrow ((basepoint_path_iso x y.as).hom ≫ f ≫ (basepoint_path_iso x z.as).inv)
  map_id y := by
    -- The chosen isomorphism cancels its inverse on identity morphisms.
    change ((basepoint_path_iso x y.as).hom ≫ 𝟙 y ≫ (basepoint_path_iso x y.as).inv :
        FundamentalGroup X x) = 1
    simp
  map_comp {X} {Y} {Z} f g := by
    -- Insert the middle identity through the chosen basepoint isomorphism and reassociate.
    change ((basepoint_path_iso x X.as).hom ≫ (f ≫ g) ≫ (basepoint_path_iso x Z.as).inv :
        FundamentalGroup _ x) =
      (((basepoint_path_iso x X.as).hom ≫ f ≫ (basepoint_path_iso x Y.as).inv : FundamentalGroup _ x) ≫
        ((basepoint_path_iso x Y.as).hom ≫ g ≫ (basepoint_path_iso x Z.as).inv : FundamentalGroup _ x))
    calc
      (basepoint_path_iso x X.as).hom ≫ (f ≫ g) ≫ (basepoint_path_iso x Z.as).inv
          = (basepoint_path_iso x X.as).hom ≫ f ≫
              ((basepoint_path_iso x Y.as).inv ≫ (basepoint_path_iso x Y.as).hom) ≫ g ≫
                (basepoint_path_iso x Z.as).inv := by
                simp [Category.assoc]
      _ = (((basepoint_path_iso x X.as).hom ≫ f ≫ (basepoint_path_iso x Y.as).inv : FundamentalGroup _ x) ≫
            ((basepoint_path_iso x Y.as).hom ≫ g ≫ (basepoint_path_iso x Z.as).inv : FundamentalGroup _ x)) := by
            simp [Category.assoc]

/-- Helper for Proposition 2.5.7: the chosen basepoint isomorphisms form the counit exhibiting
essential surjectivity of the inclusion functor. -/
def fundamental_group_inclusion_counit_iso (x : X) [PathConnectedSpace X] :
    fundamental_groupoid_to_single_obj x ⋙
        CategoryTheory.SingleObj.functor (MonoidHom.id (FundamentalGroup X x)) ≅
      𝟭 (FundamentalGroupoid X) := by
  refine NatIso.ofComponents (fun y ↦ basepoint_path_iso x y.as) ?_
  intro y z f
  -- Naturality is exactly cancellation of the chosen isomorphism at the target object.
  change (((basepoint_path_iso x y.as).hom ≫ f ≫ (basepoint_path_iso x z.as).inv : FundamentalGroup X x) ≫
      (basepoint_path_iso x z.as).hom) = (basepoint_path_iso x y.as).hom ≫ f
  simp [Category.assoc]

/-- Helper for Proposition 2.5.7: the composite of the inclusion with the quasi-inverse is the
identity on the one-object category because the chosen isomorphism at `x` is reflexive. -/
def fundamental_group_inclusion_unit_iso (x : X) [PathConnectedSpace X] :
    𝟭 (SingleObj (FundamentalGroup X x)) ≅
      CategoryTheory.SingleObj.functor (MonoidHom.id (FundamentalGroup X x)) ⋙
        fundamental_groupoid_to_single_obj x := by
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro _ _ a
  -- Route correction: forcing the chosen self-isomorphism to be `Iso.refl` removes all conjugation.
  change a ≫ 𝟙 _ = 𝟙 _ ≫
      FundamentalGroup.fromArrow ((basepoint_path_iso x x).hom ≫ (MonoidHom.id (FundamentalGroup X x)) a ≫
        (basepoint_path_iso x x).inv)
  simp [basepoint_path_iso_self]

/-- Proposition 2.5.7: if `X` is path connected, then for each basepoint `x`, the inclusion of
`π₁(X,x)` viewed as a one-object category into the fundamental groupoid `Π(X)` is an equivalence
of categories. -/
-- Proof sketch: regard `π₁(X,x)` as the full subgroupoid of `Π(X)` on the object `x`; a path from
-- `x` to any point yields an isomorphism in `Π(X)`, so path connectedness makes this inclusion
-- essentially surjective, and fullness and faithfulness are built into the one-object inclusion.
theorem fundamental_group_inclusion_is_equivalence (x : X) [PathConnectedSpace X] :
    Functor.IsEquivalence (SingleObj.functor (MonoidHom.id (FundamentalGroup X x))) := by
  -- The source proof identifies `π₁(X,x)` with a one-object skeleton of `Π(X)`.
  exact Functor.IsEquivalence.mk' (fundamental_groupoid_to_single_obj x)
    (fundamental_group_inclusion_unit_iso x) (fundamental_group_inclusion_counit_iso x)

/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_7
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open QuotientGroup

variable (G : Type u) [Group G]

/-- The orbit category maps canonically to bundled `G`-actions by sending `H` to the quotient
action on `G ⧸ H`. -/
private def orbitCategoryToAction : O(G) ⥤ Action (Type u) G where
  obj H := Action.ofMulAction G (G ⧸ H)
  map {H K} f :=
    { hom := TypeCat.ofHom f.toFun
      comm := fun g ↦ by
        ext x
        simpa [Action.ofMulAction_apply] using f.map_smul' g x }
  map_id H := by
    apply Action.hom_ext
    rfl
  map_comp f g := by
    apply Action.hom_ext
    rfl

/-- The canonical functor from the orbit category to bundled transitive `G`-sets. -/
abbrev orbitCategoryToTransitiveGSet :
    O(G) ⥤ ObjectProperty.FullSubcategory
      (fun A : Action (Type u) G ↦ MulAction.IsTransitive G (ToType A)) :=
  ObjectProperty.lift
    (fun A : Action (Type u) G ↦ MulAction.IsTransitive G (ToType A))
    (orbitCategoryToAction G)
    (fun H ↦ orbitCategory_obj_isTransitive G H)

/-- Helper for Remark 3.6.7: an equivariant map between quotient actions is already a morphism in
the orbit category. -/
private def action_hom_to_orbit_morphism {H K : O(G)}
    (φ : Action.ofMulAction G (G ⧸ H) ⟶ Action.ofMulAction G (G ⧸ K)) : H ⟶ K where
  toFun x := φ.hom x
  map_smul' g x := by
    -- The orbit-category morphism condition is exactly equivariance of the underlying function.
    have h := congrArg (fun k ↦ k x) (φ.comm g)
    simpa [Action.ofMulAction_apply] using h

/-- Helper for Remark 3.6.7: a transitive bundled `G`-action is isomorphic to the quotient by the
stabilizer of any chosen point. -/
private noncomputable def quotient_stabilizer_action_iso
    {A : Action (Type u) G} (a : ToType A) [MulAction.IsPretransitive G (ToType A)] :
    Action.ofMulAction G (G ⧸ MulAction.stabilizer G a) ≅ A := by
  -- Lemma 3.4.3 gives the underlying equivariant bijection `G / G_a ≃ A`.
  refine Action.mkIso
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := ToType A) a).toIso ?_
  intro g
  ext x
  -- The equivariance statement becomes the commutativity condition for `Action.mkIso`.
  simpa using
    quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := ToType A) a g x

/-- Helper for Remark 3.6.7: every bundled transitive `G`-set is represented by some quotient
`G ⧸ H` in the orbit category. -/
private theorem transitive_action_iso_quotient_stabilizer
    (A : ObjectProperty.FullSubcategory
      (fun X : Action (Type u) G ↦ MulAction.IsTransitive G (ToType X))) :
    ∃ H : O(G), Nonempty ((orbitCategoryToTransitiveGSet G).obj H ≅ A) := by
  rcases A.2 with ⟨ha, hpre⟩
  rcases ha with ⟨a⟩
  let H : O(G) := ⟨MulAction.stabilizer G a⟩
  let _ : MulAction.IsPretransitive G (ToType A.1) := hpre
  refine ⟨H, ⟨?_⟩⟩
  -- Lift the quotient-stabilizer isomorphism into the full subcategory of transitive actions.
  refine ObjectProperty.isoMk _ ?_
  simpa [orbitCategoryToTransitiveGSet, orbitCategoryToAction, H] using
    (quotient_stabilizer_action_iso (G := G) (A := A.1) a)

/-- Remark 3.6.7: the orbit category `O(G)` is equivalent to the full subcategory of transitive
`G`-sets. A skeleton of that category arises only after choosing one subgroup from each conjugacy
class, whereas `O(G)` itself keeps every quotient `G ⧸ H`. -/
-- Proof sketch: every object of `O(G)` is already a transitive quotient `G ⧸ H`, so the displayed
-- functor lands in the full subcategory of transitive `G`-sets. Essential surjectivity is the
-- quotient-stabilizer description of transitive actions, and full faithfulness identifies maps of
-- transitive `G`-sets with equivariant maps between the corresponding quotients.
theorem orbitCategoryToTransitiveGSet_isEquivalence :
    Functor.IsEquivalence (orbitCategoryToTransitiveGSet G) := by
  let _ : (orbitCategoryToAction G).Faithful :=
    { map_injective := by
        intro H K f g hfg
        -- Faithfulness reduces to equality of the underlying equivariant functions.
        apply MulActionHom.ext
        intro x
        exact congrArg (fun k ↦ k.hom.hom x) hfg }
  let _ : (orbitCategoryToAction G).Full :=
    { map_surjective := by
        intro H K φ
        -- Fullness uses the adapter turning an `Action` morphism back into an orbit morphism.
        refine ⟨action_hom_to_orbit_morphism (G := G) φ, ?_⟩
        apply Action.hom_ext
        ext x
        rfl }
  let _ : (orbitCategoryToTransitiveGSet G).EssSurj :=
    { mem_essImage := by
        intro A
        -- Choose a point in the transitive action and identify it with the corresponding quotient.
        rcases transitive_action_iso_quotient_stabilizer (G := G) A with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- The lifted functor is therefore faithful, full, and essentially surjective.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

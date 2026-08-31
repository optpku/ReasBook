module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

/- Domain-style sampling for Lemma 4.28.2:
- primary domain: coherence for vertical and horizontal composition of natural transformations in
  the functor bicategory.
- inspected owner declarations: `Category.assoc`, `Category.id_comp`, `Category.comp_id`,
  `NatTrans.hcomp`, `Functor.id_hcomp`, `Functor.hcomp_id`, `Functor.associator`,
  `Functor.whiskerRight_left`, and `NatTrans.exchange`.
- best owner abstraction: the canonical functor-category / whiskering API centered on
  `NatTrans.hcomp` together with `Functor.associator`.
- primitive-vs-derived split:
  primitive owner data: vertical composition, horizontal composition, the associator, and identity
  transformations.
  derived API kept here: only the source-facing associativity square, since the unit and
  interchange laws already exist upstream with their final owner interfaces. -/

/- Source/core/bridge triage for Lemma 4.28.2:
- source-facing: the textbook associativity, unitality, and interchange laws for `⋆` and `∘`.
- core/canonical: `Category.assoc`, `Category.id_comp`, `Category.comp_id`, `NatTrans.hcomp`,
  `Functor.id_hcomp`, `Functor.hcomp_id`, `Functor.associator`, and `NatTrans.exchange`.
- bridge/view: `horizontalComposition_assoc`, whose `CommSq` statement is the source-facing
  square version of the canonical associator/whiskering coherence law. -/

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

/-
Lemma 4.28.2 (1), vertical part: associativity of vertical composition is the canonical
associativity axiom in the functor category `A ⥤ B`.
-/
recall Category.assoc

/-
Lemma 4.28.2 (2): the identity transformations `𝟙 F` are left units for vertical composition;
this is the canonical axiom in the functor category `A ⥤ B`.
-/
recall Category.id_comp

/-
Lemma 4.28.2 (2): the identity transformations `𝟙 F` are right units for vertical composition;
this is the canonical axiom in the functor category `A ⥤ B`.
-/
recall Category.comp_id

/-- Helper for Lemma 4.28.2: the canonical associator square for horizontal composition of
natural transformations commutes. -/
lemma horizontalComposition_assoc_square {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (t : F ⟶ F') (s : G ⟶ G') (r : H ⟶ H') :
    CommSq (F.associator G H).hom (((t ◫ s) ◫ r)) (t ◫ (s ◫ r))
      (F'.associator G' H').hom := by
  -- Reduce the square to componentwise equality of the four-fold composite.
  refine ⟨?_⟩
  ext X
  -- Both sides simplify to the same morphism after expanding horizontal composition.
  simp [NatTrans.hcomp, Category.assoc]

/-- Lemma 4.28.2 (1), horizontal part: the canonical associator for functor composition makes the
square comparing the two horizontal composites of `t`, `s`, and `r` commute. -/
theorem horizontalComposition_assoc {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (t : F ⟶ F') (s : G ⟶ G') (r : H ⟶ H') :
    CommSq (F.associator G H).hom (((t ◫ s) ◫ r)) (t ◫ (s ◫ r))
      (F'.associator G' H').hom := by
  -- Reuse the dedicated associativity square proved componentwise above.
  exact horizontalComposition_assoc_square t s r

/-
Lemma 4.28.2 (3), left-unit part: the identity transformation of the identity functor is a
left unit for horizontal composition. This is exactly the owner theorem `Functor.id_hcomp`.
-/
recall Functor.id_hcomp

/-
Lemma 4.28.2 (3), right-unit part: the identity transformation of the identity functor is a
right unit for horizontal composition. This is exactly the owner theorem `Functor.hcomp_id`.
-/
recall Functor.hcomp_id

/-
Lemma 4.28.2 (4): vertical composition is compatible with horizontal composition through the
interchange law. In the textbook notation this is
`(s' ∘ s) ⋆ (t' ∘ t) = (s' ⋆ t') ∘ (s ⋆ t)`. This is the canonical theorem
`CategoryTheory.NatTrans.exchange`.
-/
recall NatTrans.exchange

end CategoryTheory

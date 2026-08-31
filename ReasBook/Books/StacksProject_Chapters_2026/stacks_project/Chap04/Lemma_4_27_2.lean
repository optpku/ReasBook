module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.LeftFraction
open MorphismProperty.LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Z : C}

/- Domain-style sampling for Lemma 4.27.2:
- primary domain: left-fraction localizations and their canonical equivalence relation;
- source-facing content: the equivalence relation on left fractions and the fact that composition
  of represented morphisms depends only on equivalence classes;
- core/canonical owner abstraction: `MorphismProperty.LeftFractionRel` together with the induced
  morphism
  `LeftFraction.Localization.homMk : W.LeftFraction X Y → (Q W).obj X ⟶ (Q W).obj Y`
  in `W.Localization`;
- upstream owner facts inspected before refining:
  `MorphismProperty.equivalenceLeftFractionRel`,
  `LeftFraction.map_eq_iff`,
  `LeftFraction.Localization.homMk_eq_of_leftFractionRel`,
  `Category.assoc`.

Primitive data: a pair of left fractions and proofs that they are related by `LeftFractionRel`.
Derived API: the induced localization morphism `homMk` and equality of such morphisms coming from
`homMk_eq_of_leftFractionRel`. The source-facing well-definedness statement should therefore use
`homMk` rather than repeat the generic map expression through `W.Q`.

Source/core/bridge triage:
- `source-facing`: `leftFractionComp_wellDefined`;
- `core/canonical`: `LeftFractionRel`, `equivalenceLeftFractionRel`, and `homMk`;
- `bridge/view`: the passage from equivalence-class representatives to equality after composition.
-/

/- Canonical recall: for a left multiplicative system `W`, the relation on left fractions is the
canonical relation `LeftFractionRel`, and its equivalence-relation statement is exactly
`equivalenceLeftFractionRel`. -/
recall equivalenceLeftFractionRel

-- Proof sketch: convert both relation hypotheses to equalities of the induced localization
-- morphisms via the owner theorem `LeftFraction.Localization.homMk_eq_of_leftFractionRel`,
-- then use congruence of composition.
/-- Lemma 4.27.2: composition of left fractions is well defined on equivalence classes. -/
theorem leftFractionComp_wellDefined
    (z₁ z₁' : W.LeftFraction X Y) (z₂ z₂' : W.LeftFraction Y Z)
    (h₁ : LeftFractionRel z₁ z₁') (h₂ : LeftFractionRel z₂ z₂') :
    homMk z₁ ≫ homMk z₂ = homMk z₁' ≫ homMk z₂' := by
  -- Translate the source-level relation on the first representative into equality in the
  -- localization.
  have hhom₁ : homMk z₁ = homMk z₁' := homMk_eq_of_leftFractionRel z₁ z₁' h₁
  -- Do the same for the second representative so the target equality becomes a formal rewrite.
  have hhom₂ : homMk z₂ = homMk z₂' := homMk_eq_of_leftFractionRel z₂ z₂' h₂
  -- Once both factors agree in the localization, composition agrees by congruence.
  calc
    homMk z₁ ≫ homMk z₂ = homMk z₁' ≫ homMk z₂ := by rw [hhom₁]
    _ = homMk z₁' ≫ homMk z₂' := by rw [hhom₂]

/- Canonical recall: composition in the left-fraction localization is associative; this is the
canonical associativity axiom `CategoryTheory.Category.assoc` in `W.Localization`. -/
recall Category.assoc

/- Canonical recall: the identity morphism is a left unit for composition in `W.Localization`;
this is the canonical axiom `CategoryTheory.Category.id_comp`. -/
recall Category.id_comp

/- Canonical recall: the identity morphism is a right unit for composition in `W.Localization`;
this is the canonical axiom `CategoryTheory.Category.comp_id`. -/
recall Category.comp_id

end CategoryTheory

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {X Y Z : C}

/- Domain-style sampling for Lemma 4.27.11:
- source-facing content: the equivalence relation on right fractions and the fact that composition
  of represented morphisms depends only on equivalence classes
- core/canonical owner abstraction: `MorphismProperty.RightFractionRel` together with the induced
  morphism `RightFraction.map : W.RightFraction X Y → W.Q.obj X ⟶ W.Q.obj Y`
- upstream owner facts inspected before refining:
  `MorphismProperty.equivalenceRightFractionRel`,
  `RightFraction.map_eq_iff`,
  `Category.assoc`

Primitive data: a pair of right fractions and proofs that they are related by
`RightFractionRel`.
Derived API: the induced localization morphism `RightFraction.map` and equality of such morphisms
coming from `RightFraction.map_eq_iff`. Unlike the concrete left-fraction model, the right-fraction
side has no separate localization owner like `homMk`, so the source-facing well-definedness
statement should use `RightFraction.map` itself directly, without introducing a parallel local
wrapper.

Source/core/bridge triage:
- `source-facing`: `rightFractionComp_wellDefined`;
- `core/canonical`: `RightFractionRel`, `equivalenceRightFractionRel`, and `RightFraction.map`;
- `bridge/view`: the passage from equivalence-class representatives to equality after composition.
-/

/- Lemma 4.27.11(1): the canonical relation `RightFractionRel` on right fractions is the mathlib
relation `CategoryTheory.MorphismProperty.RightFractionRel`, and its equivalence-relation
statement is exactly `CategoryTheory.MorphismProperty.equivalenceRightFractionRel`. -/
recall MorphismProperty.equivalenceRightFractionRel

-- Proof sketch: rewrite both hypotheses with the canonical theorem
-- `MorphismProperty.RightFraction.map_eq_iff`, replace the two pairs of maps by equal morphisms
-- in `W.Localization`, and then use congruence of composition.
/-- Lemma 4.27.11, well-definedness clause: composition of represented right fractions depends only
on their equivalence classes. -/
theorem rightFractionComp_wellDefined
    (φ φ' : W.RightFraction X Y) (ψ ψ' : W.RightFraction Y Z)
    (hφ : RightFractionRel φ φ') (hψ : RightFractionRel ψ ψ') :
    φ.map W.Q (Localization.inverts _ _) ≫ ψ.map W.Q (Localization.inverts _ _) =
      φ'.map W.Q (Localization.inverts _ _) ≫ ψ'.map W.Q (Localization.inverts _ _) := by
  simpa using congrArg₂ (· ≫ ·) (map_eq_iff W.Q W φ φ' |>.2 hφ) (map_eq_iff W.Q W ψ ψ' |>.2 hψ)

/- Lemma 4.27.11(3): composition in the right-fraction localization is associative; this is the
canonical associativity axiom `CategoryTheory.Category.assoc` in `W.Localization`. -/
recall Category.assoc

/- Lemma 4.27.11(3): the identity morphism is a left unit for composition in
`W.Localization`; this is the canonical axiom `CategoryTheory.Category.id_comp`. -/
recall Category.id_comp

/- Lemma 4.27.11(3): the identity morphism is a right unit for composition in
`W.Localization`; this is the canonical axiom `CategoryTheory.Category.comp_id`. -/
recall Category.comp_id

end CategoryTheory

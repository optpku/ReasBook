module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

open LeftFraction
open LeftFraction.Localization

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]

/- Domain-style sampling for Definition 4.27.4:
- primary domain: left-fraction localizations of categories with a left calculus of fractions
- upstream owner declarations inspected:
  `LeftFraction.Localization.homMk`,
  `LeftFraction.Localization.Q_map_comp_Qinv`,
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `LeftFraction.Localization.Qinv`
- best owner abstraction: `LeftFraction.Localization.homMk : W.LeftFraction X Y → (Q W).obj X ⟶
  (Q W).obj Y`

Primitive data: a left fraction `mk f s hs`.
Derived API: the source-facing notation `s⁻¹ f`, expanding directly to the canonical owner
`homMk (mk f s hs)`. The bridge to the composite `Q(f) ≫ Qinv(s)` is already owned upstream by
`LeftFraction.Localization.Q_map_comp_Qinv`, so this file reuses that theorem directly and keeps
only the source-facing notation surface.

Source/core/bridge triage:
- `source-facing`: the textbook fraction notation `s⁻¹ f`;
- `core/canonical`: the owner morphism `homMk (mk f s hs)` in `LeftFraction.Localization W`;
- `bridge/view`: the owner theorem `Q_map_comp_Qinv`, reused directly below. -/

/-- Definition 4.27.4: for a left multiplicative system `W`, a morphism `f : X ⟶ Y'`, and a
denominator `s : Y ⟶ Y'` in `W`, `left_fraction_hom W f s hs` is the morphism
`s⁻¹ f : (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y`
in the left-fraction localization represented by the roof `(f, s)`. -/
noncomputable abbrev left_fraction_hom {X Y Y' : C} (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    (LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y :=
  homMk (mk f s hs)

namespace LeftFractionNotation

scoped notation:80 s "⁻¹ " f:81 => left_fraction_hom _ f s ‹_›

end LeftFractionNotation

open scoped LeftFractionNotation

/-- The textbook fraction `s⁻¹ f` agrees with the canonical composite `Q(f) ≫ Qinv(s)` in the
left-fraction localization. -/
-- Proof sketch: unfold `left_fraction_hom` and apply the owner theorem
-- `LeftFraction.Localization.Q_map_comp_Qinv`.
theorem left_fraction_hom_eq_Q_map_comp_Qinv {X Y Y' : C}
    (f : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_hom W f s hs =
      (LeftFraction.Localization.Q W).map f ≫ Qinv s hs := by
  -- Unfold the source-facing roof notation to the canonical localization morphism.
  simpa [left_fraction_hom] using
    (LeftFraction.Localization.Q_map_comp_Qinv (W := W) f s hs).symm

end MorphismProperty
end CategoryTheory

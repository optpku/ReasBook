module

public import stacks_project.Chap04.Lemma_4_27_5
@[expose] public section

open CategoryTheory
open MorphismProperty
open MorphismProperty.RightFraction
open Opposite
open Localization

universe u v w w'

namespace CategoryTheory
namespace Localization

variable {C : Type u} {D : Type w'} [Category.{v} C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasRightCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.13:
- primary domain: localization by a right calculus of fractions;
- inspected owner declarations:
  `RightFraction.map`,
  `Localization.exists_leftFraction_finite`,
  `LeftFraction.unop`,
  `RightFraction.op_map`;
- best owner abstraction: `MorphismProperty.RightFraction` together with the canonical map
  `RightFraction.map`, which is the owner-level realization of a roof in the localization;
- primitive data: a common denominator `s : X' ⟶ X` in `W` and numerators `f i : X' ⟶ Y i`;
- derived API: the represented morphisms in the localization, obtained here by transporting the
  finite left-fraction theorem across the opposite-category bridge `LeftFraction.unop`.

Source/core/bridge triage:
- `source-facing`: `exists_rightFraction_finite`;
- `core/canonical`: the owner-level right-fraction localization API above;
- `bridge/view`: passage to the opposite category, followed by the canonical owner bridge
  `LeftFraction.unop`, where the finite common-denominator statement is already canonical as
  `exists_leftFraction_finite`. -/

-- Proof sketch: apply the finite left-fraction theorem in the opposite category, then unop the
-- resulting common denominator and numerators.
omit [W.HasRightCalculusOfFractions] in
/-- Helper for Lemma 4.27.13: mapping the `unop` of an opposite-category left fraction is
compatible with taking opposites of the original left-fraction map. -/
lemma right_fraction_map_opposite_bridge {X Y : Cᵒᵖ} (φ : W.op.LeftFraction X Y) :
    (φ.unop.map L (inverts L W)).op = φ.map L.op (inverts L.op W.op) := by
  -- This is the canonical `op`/`unop` transport for fraction representatives.
  simpa using φ.unop.op_map L (inverts L W)

/-- Lemma 4.27.13: a finite family of morphisms in a localization with common source admits
representatives by right fractions with a single common denominator in `W`. -/
theorem exists_rightFraction_finite {ι : Type w} [Finite ι] {X : C} {Y : ι → C}
    (g : ∀ i, L.obj X ⟶ L.obj (Y i)) :
    ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
      ∀ i, g i = (RightFraction.mk s hs (f i)).map L (inverts L W) := by
  -- Move to the opposite category, where the statement is exactly the finite left-fraction lemma.
  obtain ⟨X'op, s, hs, f, hf⟩ := exists_leftFraction_finite L.op W.op fun i ↦ (g i).op
  refine ⟨unop X'op, s.unop, hs, fun i ↦ (f i).unop, ?_⟩
  intro i
  -- Compare the transported right fraction with the left fraction found on the opposite side.
  have hφ :
      ((RightFraction.mk s.unop hs (f i).unop).map L (inverts L W)).op =
        (LeftFraction.mk (f i) s hs).map L.op (inverts L.op W.op) :=
    right_fraction_map_opposite_bridge (L := L) (W := W) (LeftFraction.mk (f i) s hs)
  -- Injectivity of `op` transfers the opposite-side equality back to the original localization.
  exact Quiver.Hom.op_inj <| (hf i).trans hφ.symm

end Localization
end CategoryTheory

module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.List.TFAE

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open MorphismProperty
open MorphismProperty.RightFraction
open Localization

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
variable {X X' Y : C}

/- Domain-style sampling for Lemma 4.27.14:
- primary domain: localization by a right calculus of fractions, with right fractions as the
  concrete presentation of morphisms;
- core/canonical owner APIs sampled upstream:
  `RightFraction.map`,
  `RightFraction.map_eq_iff`,
  `MorphismProperty.map_eq_iff_precomp`,
  `RightFraction.map_ofHom`;
- source-facing content here: the fixed-denominator comparison criterion for two right fractions,
  together with its `TFAE` companion;
- primitive data: a morphism property `S`, a common denominator `s : X' ⟶ X` with `hs : S s`, and
  numerators `f g : X' ⟶ Y`;
- derived API: the represented morphisms in `S.Localization` and the two equivalent
  precomposition criteria.

The owner abstraction is the localization morphism represented by `RightFraction.map`, together
with the canonical equality criteria `RightFraction.map_eq_iff` and `map_eq_iff_precomp`. The
source-facing fixed-denominator criterion should therefore be public, while the auxiliary variant
with composite denominator in `S` is best derived first at the primitive owner relation
`RightFractionRel`, and only then passed to the localization-equality layer and the companion
`TFAE`.
-/
private theorem same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    RightFractionRel (RightFraction.mk s hs f) (RightFraction.mk s hs g) ↔
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) := by
  constructor
  · rintro ⟨Z, t₁, t₂, hst, hfg, ht⟩
    let hS : S.HasRightCalculusOfFractions := inferInstance
    obtain ⟨X'', a, ha, hta⟩ := hS.ext t₁ t₂ s hs hst
    refine ⟨X'', a ≫ t₁, ?_, ?_⟩
    · calc
        (a ≫ t₁) ≫ f = a ≫ (t₁ ≫ f) := by simp [Category.assoc]
        _ = a ≫ (t₂ ≫ g) := by
              simpa [Category.assoc] using congrArg (fun k ↦ a ≫ k) hfg
        _ = (a ≫ t₂) ≫ g := by simp [Category.assoc]
        _ = (a ≫ t₁) ≫ g := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ g) hta.symm
    · simpa [Category.assoc] using S.comp_mem _ _ ha ht

  · rintro ⟨X'', a, hag, has⟩
    exact ⟨X'', a, a, rfl, hag, has⟩

-- Proof sketch: cancel the common inverted denominator `(S.Q).map s` and apply the canonical
-- localization criterion `MorphismProperty.map_eq_iff_precomp` to the equality
-- `(S.Q).map f = (S.Q).map g`.
/-- Lemma 4.27.14 (1): for two right fractions with common denominator `s`, equality of the
induced morphisms in the localization is equivalent to the existence of a further denominator in
`S` equalizing the numerators. -/
theorem right_fraction_hom_eq_iff_exists_precomp
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map S.Q (inverts _ _) =
        (RightFraction.mk s hs g).map S.Q (inverts _ _) ↔
      ∃ (X'' : C) (t : X'' ⟶ X'), S t ∧ t ≫ f = t ≫ g := by
  constructor
  · intro h
    have hfg : S.Q.map f = S.Q.map g := by
      simpa [RightFraction.map] using congrArg ((S.Q.map s) ≫ ·) h
    simpa using (map_eq_iff_precomp S.Q S f g).mp hfg
  · rintro ⟨X'', t, ht, htg⟩
    rw [map_eq_iff S.Q S]
    exact (same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S S f g s hs).2
      ⟨X'', t, htg, S.comp_mem _ _ ht hs⟩

/-- Lemma 4.27.14 (2): for two right fractions with common denominator `s`, equality of the
induced morphisms in the localization is equivalent to the existence of a morphism whose
precomposition equalizes the numerators and whose composite with `s` lies in `S`. -/
theorem right_fraction_hom_eq_iff_exists_precomp_composite_in_S
    (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s) :
    (RightFraction.mk s hs f).map S.Q (inverts _ _) =
        (RightFraction.mk s hs g).map S.Q (inverts _ _) ↔
      ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) := by
  rw [map_eq_iff S.Q S]
  exact same_denominator_rightFractionRel_iff_exists_precomp_composite_in_S S f g s hs

end CategoryTheory

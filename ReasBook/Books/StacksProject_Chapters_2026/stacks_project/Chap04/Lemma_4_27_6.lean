module

import Mathlib.Tactic.TFAE
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap04.Definition_4_27_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

open LeftFraction
open LeftFraction.Localization
open scoped CategoryTheory.MorphismProperty.LeftFractionNotation

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C}

local notation "Q" => LeftFraction.Localization.Q

/-
Domain-style sampling for Lemma 4.27.6:
- primary domain: left-fraction localizations and equality criteria for roofs with fixed
  denominator;
- inspected owner declarations:
  `LeftFraction.Localization.homMk_eq_iff_leftFractionRel`,
  `LeftFraction.Localization.Q_map_comp_Qinv`,
  `MorphismProperty.LeftFractionRel`,
  `MorphismProperty.map_eq_iff_postcomp`;
- best owner abstraction: the localization functor `Q W`, with the represented morphism `s⁻¹ f`
  viewed through the owner morphism `homMk (mk f s hs)` and the canonical comparison
  `Q_map_comp_Qinv`;
- primitive data: numerators `f`, `g` and a common denominator `s` with `W s`;
- derived API: the fixed-denominator equality criterion below, together with the canonical
  postcomposition criterion extracted by `map_eq_iff_postcomp`.

Source/core/bridge triage:
- `source-facing`: `left_fraction_hom_eq_iff_exists_postcomp`;
- `core/canonical`: the owner-level localization API above;
- `bridge/view`: the relation witness for the fixed-denominator fractions
  `mk f s hs` and `mk g s hs`, used to discharge condition `(3)` of the TFAE statement. -/

/-- A morphism of `W` with source `Y'` that equalizes the numerators `f` and `g` by
postcomposition. -/
def left_fraction_has_postcomp_eq
    (f g : X ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t

/-- A postcomposition equalizer for `f` and `g` whose composite with the denominator `s`
lies in `W`. -/
def left_fraction_has_postcomp_comp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') :
    Prop :=
  ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a)

/-- Helper for Lemma 4.27.6: canceling a common denominator reduces equality of two roofs to
 equality of the localized numerator maps. -/
lemma left_fraction_hom_eq_iff_Q_map_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_hom W f s hs = left_fraction_hom W g s hs ↔
      (Q W).map f = (Q W).map g := by
  constructor
  · intro h
    -- Rewrite both roofs as `Q.map _ ≫ Qinv s` and cancel the common inverse denominator.
    have hroof : (Q W).map f ≫ Qinv s hs = (Q W).map g ≫ Qinv s hs := by
      simpa [left_fraction_hom_eq_Q_map_comp_Qinv (W := W) f s hs,
        left_fraction_hom_eq_Q_map_comp_Qinv (W := W) g s hs] using h
    exact (cancel_mono (Qinv s hs)).1 hroof
  · intro h
    -- Reinsert the common inverse denominator to recover equality of the roofs.
    calc
      s⁻¹ f = (Q W).map f ≫ Qinv s hs := left_fraction_hom_eq_Q_map_comp_Qinv (W := W) f s hs
      _ = (Q W).map g ≫ Qinv s hs := by
        simpa using congrArg (fun k ↦ k ≫ Qinv s hs) h
      _ = s⁻¹ g := (left_fraction_hom_eq_Q_map_comp_Qinv (W := W) g s hs).symm

/-- Helper for Lemma 4.27.6: a common postcomposition equalizer whose composite with the
 denominator lies in `W` identifies the corresponding fixed-denominator roofs. -/
lemma left_fraction_hom_eq_of_has_postcomp_comp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_has_postcomp_comp_eq W f g s →
      left_fraction_hom W f s hs = left_fraction_hom W g s hs := by
  rintro ⟨Y'', a, hfg, hsa⟩
  -- The owner relation is witnessed by the same refinement `a` on both roofs.
  have hmk : homMk (mk f s hs) = homMk (mk g s hs) := by
    rw [homMk_eq_iff_leftFractionRel]
    exact ⟨Y'', a, a, rfl, hfg, hsa⟩
  simpa [left_fraction_hom] using hmk

/-- Equality of left fractions with fixed denominator is equivalent to postcomposition
equalization in `W`. -/
-- Proof sketch: rewrite `s⁻¹ f = s⁻¹ g` using `Q_map_comp_Qinv`, then apply the canonical
-- localization criterion `map_eq_iff_postcomp`.
theorem left_fraction_hom_eq_iff_has_postcomp_eq
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    left_fraction_hom W f s hs = left_fraction_hom W g s hs ↔
      left_fraction_has_postcomp_eq W f g := by
  constructor
  · intro h
    -- Cancel the common denominator and apply the localization criterion for map equality.
    obtain ⟨Y'', t, ht, hfg⟩ := (map_eq_iff_postcomp (L := Q W) (W := W) f g).1
      ((left_fraction_hom_eq_iff_Q_map_eq (W := W) f g s hs).1 h)
    exact ⟨Y'', t, ht, hfg⟩
  · rintro ⟨Y'', t, ht, hfg⟩
    -- A postcomposition witness in `W` gives equality of the localized numerators.
    exact (left_fraction_hom_eq_iff_Q_map_eq (W := W) f g s hs).2 <|
      (map_eq_iff_postcomp (L := Q W) (W := W) f g).2 ⟨Y'', t, ht, hfg⟩

/-- Lemma 4.27.6: for two left fractions with common denominator `s`, the following are
equivalent:

1. the induced morphisms in the localization are equal;
2. the numerators become equal after postcomposition with a morphism of `W`;
3. the numerators become equal after postcomposition with a morphism whose composite with `s`
   lies in `W`. -/
-- Proof sketch: use `left_fraction_hom_eq_iff_has_postcomp_eq` for `(1) ↔ (2)`, and compare
-- clauses `(2)` and `(3)` by composing with `s` and by invoking the fixed-denominator relation
-- criterion `homMk_eq_iff_leftFractionRel`.
theorem left_fraction_hom_tfae
    (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s) :
    [ left_fraction_hom W f s hs = left_fraction_hom W g s hs,
      left_fraction_has_postcomp_eq W f g,
      left_fraction_has_postcomp_comp_eq W f g s ].TFAE := by
  -- First identify equality of roofs with equality after postcomposition by a morphism in `W`.
  tfae_have 1 ↔ 2 := by
    simpa using left_fraction_hom_eq_iff_has_postcomp_eq (W := W) f g s hs
  -- Next any witness in `W` also gives a witness whose composite with `s` still lies in `W`.
  tfae_have 2 → 3 := by
    rintro ⟨Y'', t, ht, hfg⟩
    exact ⟨Y'', t, hfg, W.comp_mem _ _ hs ht⟩
  -- Finally a refinement equalizing the numerators yields equality of the original roofs.
  tfae_have 3 → 1 := by
    exact left_fraction_hom_eq_of_has_postcomp_comp_eq (W := W) f g s hs
  -- These three implications assemble the desired equivalence of conditions.
  tfae_finish

end MorphismProperty
end CategoryTheory

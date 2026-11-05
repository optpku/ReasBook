module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section

open CategoryTheory
open MorphismProperty

universe u v w w'

namespace CategoryTheory
namespace Localization

variable {C : Type u} {D : Type w'} [Category.{v} C] [Category D]
variable (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
variable [W.HasLeftCalculusOfFractions]

/- Domain-style sampling for Lemma 4.27.5:
- primary domain: localization by a left calculus of fractions;
- inspected owner declarations:
  `Localization.exists_leftFraction`,
  `MorphismProperty.RightFraction.leftFraction`,
  `MorphismProperty.RightFraction.leftFraction_fac`,
  `MorphismProperty.LeftFraction.map_eq_iff`,
  `Localization.exists_leftFraction₂`;
- best owner abstraction: `MorphismProperty.LeftFraction` as the canonical representation of a
  localized morphism by a roof;
- primitive data: a finite family `g i : L.obj (X i) ⟶ L.obj Y`;
- derived API: existence of representatives with one common denominator.

Source/core/bridge triage:
- `source-facing`: `exists_leftFraction_finite`;
- `core/canonical`: the owner-level left-fraction localization API above;
- `bridge/view`: the operational `Finset`-indexed common-denominator statement
  used internally to derive the finite theorem. -/

/-- Helper for Lemma 4.27.5: postcomposing a left-fraction representative to a common
refinement of its denominator does not change the represented localized morphism. -/
private lemma leftFraction_map_postcomp_eq {X Y Z : C} (φ : W.LeftFraction X Y)
    (t : φ.Y' ⟶ Z) (ht : W (φ.s ≫ t)) :
    φ.map L (inverts L W) =
      (LeftFraction.mk (φ.f ≫ t) (φ.s ≫ t) ht).map L (inverts L W) := by
  -- Compare the two roofs using the obvious common refinement through `Z`.
  exact (MorphismProperty.LeftFraction.map_eq_iff (L := L) (W := W) _ _).2 <| by
    refine ⟨Z, t, 𝟙 Z, ?_, ?_, ht⟩
    · simp
    · simp

/-- Helper for Lemma 4.27.5: an Ore-square equality lets one replace the denominator of a
left-fraction representative by an equal common refinement. -/
private lemma leftFraction_map_eq_of_ore_refinement {X Y Z Z' : C} (φ : W.LeftFraction X Y)
    (a : φ.Y' ⟶ Z') (b : Z ⟶ Z') {s₁ : Y ⟶ Z} (ht : W (s₁ ≫ b))
    (h : φ.s ≫ a = s₁ ≫ b) :
    φ.map L (inverts L W) =
      (LeftFraction.mk (φ.f ≫ a) (s₁ ≫ b) ht).map L (inverts L W) := by
  -- Use the Ore-square identity as the comparison witness between the two roofs.
  exact (MorphismProperty.LeftFraction.map_eq_iff (L := L) (W := W) _ _).2 <| by
    refine ⟨Z', a, 𝟙 Z', ?_, ?_, ?_⟩
    · simpa using h
    · simp
    · rw [h]
      exact ht

/-- Helper for Lemma 4.27.5: for a finite subfamily of morphisms in a
localization with common target, one can choose left-fraction representatives with a single common
denominator in `W`. -/
private theorem exists_leftFraction_finset {ι : Type w} {X : ι → C} (s : Finset ι) {Z : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Z) :
    ∃ (Z' : C) (t : Z ⟶ Z') (ht : W t) (f : ∀ i, i ∈ s → (X i ⟶ Z')),
      ∀ i (hi : i ∈ s), g i = (LeftFraction.mk (f i hi) t ht).map L (inverts L W) := by
  classical
  -- Induct on the finite family, maintaining a single denominator for the treated indices.
  induction s using Finset.induction with
  | empty =>
      refine ⟨Z, 𝟙 Z, W.id_mem Z, fun i hi ↦ False.elim <| Finset.notMem_empty i hi, ?_⟩
      intro i hi
      exact False.elim <| Finset.notMem_empty i hi
  | @insert a s ha ih =>
      -- First keep a common denominator for the old subfamily.
      obtain ⟨Z₁, s₁, hs₁, f₁, hf₁⟩ := ih
      -- Then choose one left-fraction representative for the new morphism.
      obtain ⟨φ₀, hφ₀⟩ := exists_leftFraction L W (g a)
      -- The Ore square refines the two competing denominators to a common one.
      let α : W.LeftFraction φ₀.Y' Z₁ := (RightFraction.mk φ₀.s φ₀.hs s₁).leftFraction
      have hα : φ₀.s ≫ α.f = s₁ ≫ α.s := by
        simpa [α] using
          (RightFraction.leftFraction_fac (RightFraction.mk φ₀.s φ₀.hs s₁)).symm
      let t : Z ⟶ α.Y' := s₁ ≫ α.s
      have ht : W t := W.comp_mem _ _ hs₁ α.hs
      let f : ∀ i, i ∈ insert a s → (X i ⟶ α.Y') := fun i hi ↦
        if h : i = a then
          h.symm.rec (φ₀.f ≫ α.f)
        else
          f₁ i ((Finset.mem_insert.1 hi).resolve_left h) ≫ α.s
      refine ⟨α.Y', t, ht, f, ?_⟩
      intro i hi
      by_cases h : i = a
      · subst h
        rw [hφ₀]
        -- The new index is handled directly by the Ore square.
        simpa [t, f, α] using
          leftFraction_map_eq_of_ore_refinement (L := L) (W := W)
            (φ := φ₀) (a := α.f) (b := α.s) (s₁ := s₁) (ht := ht) hα
      · have hi' : i ∈ s := (Finset.mem_insert.1 hi).resolve_left h
        rw [hf₁ i hi']
        -- Old indices are postcomposed into the refined common denominator.
        simpa [t, f, h] using
          (leftFraction_map_postcomp_eq (L := L) (W := W)
            (φ := LeftFraction.mk (f₁ i hi') s₁ hs₁) (t := α.s) (Z := α.Y') ht)

-- Proof sketch: choose a left-fraction representative for each `g i`. Then induct on the finite
-- index type, using the left Ore condition to replace two denominators by a common refinement in
-- `W`, and compose the previously chosen numerators with the comparison maps into that refinement.
/-- Lemma 4.27.5: a finite family of morphisms in a localization with common target admits
representatives by left fractions with a single common denominator in `W`. -/
theorem exists_leftFraction_finite {ι : Type w} [Finite ι] {X : ι → C} {Y : C}
    (g : ∀ i, L.obj (X i) ⟶ L.obj Y) :
    ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
      ∀ i, g i = (LeftFraction.mk (f i) s hs).map L (inverts L W) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Apply the finite-set statement to the whole index type.
  obtain ⟨Y', s, hs, f, hf⟩ := exists_leftFraction_finset L W Finset.univ g
  refine ⟨Y', s, hs, fun i ↦ f i (Finset.mem_univ i), ?_⟩
  intro i
  exact hf i (Finset.mem_univ i)

end Localization
end CategoryTheory

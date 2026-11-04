/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Slice
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_15.Clutter

public section

namespace SteinerTripleSystem

universe u

variable {α : Type u}

/-- A Steiner triple system on the finite ground set `E` is a family `S` of triples in `E` such
that every `2`-element subset of `E` lies in exactly one member of `S`. -/
structure IsOn (E : Finset α) (S : Set (Finset α)) : Prop where
  /-- Every triple in the family is contained in the ground set. -/
  subset_ground : ∀ s ∈ S, s ⊆ E
  /-- Every member of the family has cardinality `3`. -/
  sized : S.Sized 3
  /-- Every `2`-element subset of the ground set lies in exactly one triple of the family. -/
  pair_cover : ∀ p, p ∈ E.powersetCard 2 → ∃! s, s ∈ S ∧ p ⊆ s

/-- Build a Steiner triple system witness from ground containment, `3`-uniformity, and exact pair
coverage. -/
def IsOn.ofSubsetGroundSizedAndPairCover
    {E : Finset α} {S : Set (Finset α)}
    (h_subset_ground : ∀ s ∈ S, s ⊆ E)
    (h_sized : S.Sized 3)
    (h_pair_cover : ∀ p, p ∈ E.powersetCard 2 → ∃! s, s ∈ S ∧ p ⊆ s) :
    IsOn E S :=
  ⟨h_subset_ground, h_sized, h_pair_cover⟩

/-- Unfolding specification for `IsOn`. -/
theorem isOn_iff
    {E : Finset α} {S : Set (Finset α)} :
    IsOn E S ↔
      (∀ s ∈ S, s ⊆ E) ∧
        S.Sized 3 ∧
          ∀ p, p ∈ E.powersetCard 2 → ∃! s, s ∈ S ∧ p ⊆ s := by
  constructor
  · intro h
    -- Expose the three defining fields as the stated conjunction.
    exact ⟨h.subset_ground, h.sized, h.pair_cover⟩
  · rintro ⟨h_subset_ground, h_sized, h_pair_cover⟩
    -- Repackage the explicit containment, size, and pair-cover conditions.
    exact IsOn.ofSubsetGroundSizedAndPairCover h_subset_ground h_sized h_pair_cover

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_6_definition_2_26/SteinerTripleSystem.lean

A Steiner triple system family on `E` is a clutter on the same ground set. -/
theorem isClutterOn
    {E : Finset α} {S : Set (Finset α)}
    (h : IsOn E S) :
    Clutter.IsClutterOn E S := by
  -- Uniform cardinality makes the family an antichain under inclusion.
  refine Clutter.IsClutterOn.ofSubsetGroundAndAntichain h.subset_ground ?_
  -- Apply the canonical sized-family antichain theorem.
  exact h.sized.isAntichain

#print axioms isClutterOn

end SteinerTripleSystem

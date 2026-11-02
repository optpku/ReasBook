module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Antichain

public section

namespace Clutter

universe u

variable {α : Type u}

/-- A clutter on the finite ground set `E` is a family of finite subsets of `E` that is an
antichain under inclusion. -/
structure IsClutterOn (E : Finset α) (S : Set (Finset α)) : Prop where
  /-- Every member of the clutter is contained in the ground set. -/
  subset_ground : ∀ s ∈ S, s ⊆ E
  /-- Distinct members of the clutter are incomparable under inclusion. -/
  antichain : IsAntichain (· ⊆ ·) S

/-- Build a clutter-on-ground-set witness from its ground-set and antichain properties. -/
def IsClutterOn.ofSubsetGroundAndAntichain
    {E : Finset α} {S : Set (Finset α)}
    (h_ground : ∀ s ∈ S, s ⊆ E)
    (h_antichain : IsAntichain (· ⊆ ·) S) :
    IsClutterOn E S :=
  ⟨h_ground, h_antichain⟩

/-- Unfolding specification for `IsClutterOn`. -/
theorem isClutterOn_iff
    {E : Finset α} {S : Set (Finset α)} :
    IsClutterOn E S ↔
      (∀ s ∈ S, s ⊆ E) ∧ IsAntichain (· ⊆ ·) S := by
  constructor
  · intro hS
    -- Unpack the structure fields into the two explicit properties.
    exact ⟨hS.subset_ground, hS.antichain⟩
  · rintro ⟨h_ground, h_antichain⟩
    -- Repackage the explicit properties into the structure.
    exact IsClutterOn.ofSubsetGroundAndAntichain h_ground h_antichain

end Clutter

module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.SDiff
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_15.Clutter

public section

open Clutter

/-- Definition 2.15. A finite family `S : Finset (Finset (Fin n))` is a clutter when for any
two distinct members `Si, Sj ∈ S`, both `Si \ Sj` and `Sj \ Si` are nonempty. -/
class IsClutter {n : ℕ} (S : Finset (Finset (Fin n))) : Prop where
  /-- Distinct members of a clutter are incomparable under inclusion. -/
  antichain : IsAntichain (· ⊆ ·) (S : Set (Finset (Fin n)))

namespace IsClutter

/-- Build a clutter from the corresponding antichain condition. -/
theorem ofAntichain
    {n : ℕ} {S : Finset (Finset (Fin n))}
    (hS : IsAntichain (· ⊆ ·) (S : Set (Finset (Fin n)))) :
    IsClutter S :=
  ⟨hS⟩

/-- A clutter on `Fin n` is a clutter on the finite ground set `Finset.univ`. -/
theorem toIsClutterOn
    {n : ℕ} {S : Finset (Finset (Fin n))}
    (hS : IsClutter S) :
    IsClutterOn Finset.univ (S : Set (Finset (Fin n))) :=
  IsClutterOn.ofSubsetGroundAndAntichain
    (fun U _ ↦ Finset.subset_univ U)
    hS.antichain

end IsClutter

/-- The empty family of subsets of `Fin n` is a clutter. -/
instance instIsClutterEmpty {n : ℕ} : IsClutter (∅ : Finset (Finset (Fin n))) :=
  IsClutter.ofAntichain <| by
    simpa only [Finset.coe_empty] using
      (IsAntichain.empty : IsAntichain (· ⊆ ·) (∅ : Set (Finset (Fin n))))

/-- A family is a clutter exactly when it is an antichain under inclusion. -/
theorem isClutter_iff_antichain
    {n : ℕ} (S : Finset (Finset (Fin n))) :
    IsClutter S ↔ IsAntichain (· ⊆ ·) (S : Set (Finset (Fin n))) := by
  exact ⟨fun hS ↦ hS.antichain, IsClutter.ofAntichain⟩

/-- A clutter on `Fin n` is exactly a clutter on the ground set `Finset.univ`. -/
theorem isClutter_iff_isClutterOn_univ
    {n : ℕ} (S : Finset (Finset (Fin n))) :
    IsClutter S ↔ IsClutterOn Finset.univ (S : Set (Finset (Fin n))) := by
  exact ⟨IsClutter.toIsClutterOn, fun hS ↦ IsClutter.ofAntichain hS.antichain⟩

/-- A family is a clutter exactly when distinct members have nonempty set differences in both
directions, expressed as a pairwise condition on the family. -/
theorem isClutter_iff_pairwise_sdiff_nonempty
    {n : ℕ} (S : Finset (Finset (Fin n))) :
    IsClutter S ↔
      (S : Set (Finset (Fin n))).Pairwise
        (fun Si Sj ↦ (Si \ Sj).Nonempty ∧ (Sj \ Si).Nonempty) := by
  rw [isClutter_iff_antichain]
  constructor
  · intro hS Si hSi Sj hSj hne
    exact ⟨Finset.sdiff_nonempty.mpr (hS hSi hSj hne),
      Finset.sdiff_nonempty.mpr (hS hSj hSi hne.symm)⟩
  · intro hS Si hSi Sj hSj hne hsubset
    exact (Finset.sdiff_nonempty.mp (hS hSi hSj hne).1) hsubset

/-- A family is a clutter exactly when distinct members have nonempty set differences in both
directions. -/
theorem isClutter_iff {n : ℕ} (S : Finset (Finset (Fin n))) :
    IsClutter S ↔
      (∀ ⦃Si⦄, Si ∈ S → ∀ ⦃Sj⦄, Sj ∈ S → Si ≠ Sj →
        (Si \ Sj).Nonempty ∧ (Sj \ Si).Nonempty) := by
  simpa [Set.Pairwise] using isClutter_iff_pairwise_sdiff_nonempty S

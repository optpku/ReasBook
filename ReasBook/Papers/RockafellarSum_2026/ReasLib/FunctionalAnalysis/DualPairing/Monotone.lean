/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.DualPairing

/-!
# Monotone polars for dual pairings

This module defines monotonicity, monotone polars, and their maximality
characterizations for a continuous dual pairing.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- A set is monotone with respect to a dual pairing when the pairing's quadratic form
is nonnegative on the difference of every two points of the set. -/
def IsMonotone (P : DualPairing X Xstar) (S : Set (X × Xstar)) : Prop :=
  ∀ z ∈ S, ∀ w ∈ S, 0 ≤ P.quadratic (z - w)

/-- Every subset of a monotone set is monotone. -/
theorem IsMonotone.mono (P : DualPairing X Xstar) {S T : Set (X × Xstar)}
    (hTS : T ⊆ S) (hS : P.IsMonotone S) : P.IsMonotone T := by
  intro z hz w hw
  -- Transport both points through the inclusion, then use monotonicity on `S`.
  exact hS z (hTS hz) w (hTS hw)

/-- The points monotonically related to every point of a set with respect to the
quadratic form of a dual pairing. -/
def monotonePolar (P : DualPairing X Xstar) (S : Set (X × Xstar)) : Set (X × Xstar) :=
  {z | ∀ s ∈ S, 0 ≤ P.quadratic (z - s)}

/-- Membership in the monotone polar is the pointwise nonnegativity condition. -/
theorem mem_monotonePolar (P : DualPairing X Xstar) (S : Set (X × Xstar))
    (z : X × Xstar) :
    z ∈ P.monotonePolar S ↔ ∀ s ∈ S, 0 ≤ P.quadratic (z - s) := by
  -- Membership in the defining set comprehension is precisely the stated condition.
  rfl

/-- Taking the monotone polar reverses set inclusion. -/
theorem monotonePolar_antitone (P : DualPairing X Xstar) : Antitone P.monotonePolar := by
  intro S T hST z hz
  -- Expose the pointwise conditions defining both polar memberships.
  rw [mem_monotonePolar] at hz ⊢
  intro s hs
  -- Test `hz` at the image of `hs` under the inclusion `S ⊆ T`.
  exact hz s (hST hs)

/-- A set is monotone if and only if it is contained in its monotone polar. -/
theorem isMonotone_iff_subset_polar (P : DualPairing X Xstar) (S : Set (X × Xstar)) :
    P.IsMonotone S ↔ S ⊆ P.monotonePolar S := by
  constructor
  · intro hS z hz
    -- Polar membership asks for monotonicity between `z` and every point of `S`.
    rw [mem_monotonePolar]
    intro s hs
    exact hS z hz s hs
  · intro hS z hz w hw
    -- Use the assumed inclusion to place `z` in the polar, then test it at `w`.
    have hzPolar : z ∈ P.monotonePolar S := hS hz
    rw [mem_monotonePolar] at hzPolar
    exact hzPolar w hw

/-- A monotone set is maximal among monotone sets if and only if it equals its
monotone polar. -/
theorem maximalMonotone_iff_polar_eq (P : DualPairing X Xstar) (S : Set (X × Xstar))
    (hS : P.IsMonotone S) : Maximal (P.IsMonotone) S ↔ P.monotonePolar S = S := by
  constructor
  · intro hMax
    apply Set.Subset.antisymm
    · intro z hz
      rw [mem_monotonePolar] at hz
      -- Adjoining a point of the polar preserves monotonicity.
      have hInsert : P.IsMonotone (insert z S) := by
        intro a ha b hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · simp
          · exact hz b hb
        · rcases hb with rfl | hb
          · rw [P.quadratic.map_sub]
            exact hz a ha
          · exact hS a ha b hb
      -- Maximality forces the adjoined polar point back into `S`.
      exact hMax.2 hInsert (Set.subset_insert z S) (Set.mem_insert z S)
    · exact (isMonotone_iff_subset_polar P S).mp hS
  · intro hPolar
    refine ⟨hS, ?_⟩
    intro T hT hST
    -- Every monotone extension is contained in the polar, hence in `S`.
    rw [← hPolar]
    intro z hz s hs
    exact hT z hz s (hST hs)

end DualPairing

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.DualPairing

/-!
# Origin exclusion for a monotone graph

This module records the negative-quadratic-pairing obstruction to containing
the origin in a monotone graph.
-/

public section

namespace C0Seq

/-- A monotone subset of `C0Seq × L1Seq` containing a point with negative quadratic
pairing does not contain the origin. -/
theorem zero_not_mem_of_quadraticPairing_neg
    {S : Set (C0Seq × L1Seq)} {z : C0Seq × L1Seq}
    (hz : z ∈ S) (hz_neg : quadraticPairing z < 0)
    (hS : coordinateDualPairing.IsMonotone S) :
    (0, 0) ∉ S := by
  rcases z with ⟨x, a⟩
  change (x, a) ∈ S at hz
  change quadraticPairing (x, a) < 0 at hz_neg
  intro hzero
  have hzpolar : (x, a) ∈ coordinateDualPairing.monotonePolar S :=
    (DualPairing.isMonotone_iff_subset_polar coordinateDualPairing S).mp hS hz
  have hnonneg :=
    (DualPairing.mem_monotonePolar coordinateDualPairing S (x, a)).mp hzpolar
      (0, 0) hzero
  have hnonneg' : 0 ≤ quadraticPairing (x, a) := by
    have hzsub : (x, a) - (0, 0) = (x, a) := by
      ext <;> simp
    rw [hzsub] at hnonneg
    simpa using hnonneg
  exact (not_lt_of_ge hnonneg' hz_neg)

end C0Seq

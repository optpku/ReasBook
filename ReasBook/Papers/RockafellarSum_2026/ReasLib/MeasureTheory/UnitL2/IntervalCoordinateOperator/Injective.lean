/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Jump
public import RockafellarSum_2026.ReasLib.MeasureTheory.Measure.Lebesgue.Conull

/-!
# Injectivity of interval-coordinate synthesis

This module proves that the interval-coordinate operator has trivial kernel by
isolating jumps of a pointwise representative.
-/

public section

namespace L1Seq

/-- Every coordinate of a summable sequence in the kernel of the interval-coordinate
operator vanishes. -/
private lemma apply_eq_zero_of_intervalCoordinateOperator_eq_zero (a : L1Seq)
    (ha : intervalCoordinateOperator a = 0) (n₀ : ℕ) : a n₀ = 0 := by
  classical
  -- Pass from equality in `UnitL2` to a pointwise-zero representative on a conull set.
  obtain ⟨E, hE, hConull, hZero⟩ := pointwiseRepresentative_exists_conull_zero a ha
  by_contra hn₀
  have hPositive : 0 < |a n₀| := abs_pos.mpr hn₀
  -- Choose a finite core whose complementary absolute sum is smaller than the
  -- coefficient that will be recovered from the isolated jump.
  obtain ⟨J, hn₀J, hTail⟩ := exists_finset_tail_lt a n₀ |a n₀| hPositive
  let F : Finset ℝ := (J.erase n₀).image rationalTime
  have hCentralNotMem : rationalTime n₀ ∉ F := by
    intro hCentral
    obtain ⟨n, hnErase, hnTime⟩ := Finset.mem_image.mp hCentral
    have hnNe : n ≠ n₀ := (Finset.mem_erase.mp hnErase).1
    exact hnNe (rationalTime_injective hnTime)
  have hFSubset : (F : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨n, _, hnTime⟩ := Finset.mem_image.mp ht
    rw [← hnTime]
    exact rationalTime_mem_Ioo n
  let E' : Set ℝ := E \ (F : Set ℝ)
  have hE'Subset : E' ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro s hs
    exact hE hs.1
  have hE'Conull : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E') = 0 := by
    -- Deleting finitely many breakpoints preserves relative conullness.
    unfold E'
    rw [Set.sdiff_sdiff_eq_sdiff_union hFSubset]
    exact MeasureTheory.measure_union_null hConull
      (F.measure_zero MeasureTheory.volume)
  -- Select zero points on both sides while avoiding every other breakpoint in `J`.
  obtain ⟨sLeft, hsLeft, sRight, hsRight, hAvoidOpen⟩ :=
    Real.exists_conull_points_around_avoiding_finset hE'Subset hE'Conull
      (rationalTime_mem_Ioo n₀) F hCentralNotMem |a n₀| hPositive
  have hLeft : sLeft ∈ Set.Ioo (0 : ℝ) (rationalTime n₀) :=
    ⟨(hE'Subset hsLeft.1).1, hsLeft.2.2⟩
  have hRight : sRight ∈ Set.Ioo (rationalTime n₀) 1 :=
    ⟨hsRight.2.1, (hE'Subset hsRight.1).2⟩
  have hAvoidClosed :
      ∀ n ∈ J, n ≠ n₀ → rationalTime n ∉ Set.Ioc sLeft sRight := by
    intro n hnJ hnNe hnClosed
    have hnF : rationalTime n ∈ F := by
      exact Finset.mem_image.mpr ⟨n, Finset.mem_erase.mpr ⟨hnNe, hnJ⟩, rfl⟩
    by_cases hnRight : rationalTime n = sRight
    · exact hsRight.1.2 (hnRight ▸ hnF)
    · exact hAvoidOpen (rationalTime n) hnF
        ⟨hnClosed.1, lt_of_le_of_ne hnClosed.2 hnRight⟩
  have hStrict := abs_apply_lt_of_pointwiseRepresentative_eq_zero
    a n₀ J sLeft sRight |a n₀| hn₀J hLeft hRight hAvoidClosed hTail
      (hZero sLeft hsLeft.1.1) (hZero sRight hsRight.1.1)
  -- The jump estimate now contradicts irreflexivity of strict order.
  exact (lt_irrefl |a n₀|) hStrict

/-- The interval-coordinate operator from real summable sequences to `UnitL2` is injective. -/
public theorem intervalCoordinateOperator_injective :
    Function.Injective intervalCoordinateOperator := by
  intro a b hab
  -- Reduce injectivity to coordinatewise vanishing of the difference in the kernel.
  have hKernel : intervalCoordinateOperator (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  ext n
  have hCoordinate := apply_eq_zero_of_intervalCoordinateOperator_eq_zero (a - b) hKernel n
  simpa only [lp.coeFn_sub, Pi.sub_apply, sub_eq_zero] using hCoordinate

end L1Seq

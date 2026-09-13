/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Conull point selection on real intervals

This module selects points on both sides of a center while avoiding a finite
set and a null relative complement.
-/

namespace Real

/-- For `Real.exists_conull_points_around_avoiding_finset`, a positive open interval
contained in an ambient set meets any subset with null relative complement there. -/
private lemma nonempty_inter_Ioo_of_volume_sdiff_eq_zero {E A : Set ℝ} {a b : ℝ}
    (hnull : MeasureTheory.volume (A \ E) = 0) (hab : a < b)
    (hsub : Set.Ioo a b ⊆ A) : (E ∩ Set.Ioo a b).Nonempty := by
  -- Restrict the null relative complement from the ambient set to the interval.
  have hinterNull : MeasureTheory.volume (Set.Ioo a b \ E) = 0 :=
    MeasureTheory.measure_mono_null (Set.sdiff_subset_sdiff_left hsub) hnull
  have hmeasure : MeasureTheory.volume (Set.Ioo a b ∩ E) =
      MeasureTheory.volume (Set.Ioo a b) :=
    MeasureTheory.measure_inter_conull' hinterNull
  -- Positive interval length makes the intersection measure nonzero.
  have hintervalNe : MeasureTheory.volume (Set.Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  have hinterNe : MeasureTheory.volume (Set.Ioo a b ∩ E) ≠ 0 := by
    intro hinterZero
    apply hintervalNe
    rw [← hmeasure, hinterZero]
  obtain ⟨x, hxIoo, hxE⟩ := MeasureTheory.nonempty_of_measure_ne_zero hinterNe
  exact ⟨x, hxE, hxIoo⟩

/-- For `Real.exists_conull_points_around_avoiding_finset`, every open neighborhood of a
point contains an open interval around it that avoids a finite set missing the point. -/
private lemma exists_Ioo_subset_avoiding_finset {U : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U) (F : Finset ℝ) (htF : t ∉ F) :
    ∃ l u, t ∈ Set.Ioo l u ∧ Set.Ioo l u ⊆ U \ (F : Set ℝ) := by
  -- Remove the closed finite set while retaining an open neighborhood of the point.
  have hopen : IsOpen (U \ (F : Set ℝ)) := hU.sdiff F.isClosed
  have htDiff : t ∈ U \ (F : Set ℝ) := ⟨ht, htF⟩
  exact mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds htDiff)

/-- If `E` is contained in the open unit interval and has null relative complement, then
arbitrarily close points of `E` can be chosen on both sides of an interior point so that
the open interval between them avoids any prescribed finite set not containing that point. -/
public theorem exists_conull_points_around_avoiding_finset {E : Set ℝ}
    (_hE : E ⊆ Set.Ioo (0 : ℝ) 1)
    (hconull : MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E) = 0)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 1) (F : Finset ℝ) (htF : t ∉ F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ sLeft ∈ E ∩ Set.Ioo (t - ε) t,
      ∃ sRight ∈ E ∩ Set.Ioo t (t + ε),
        ∀ x ∈ F, x ∉ Set.Ioo sLeft sRight := by
  -- Choose one interval controlling proximity, the unit interval, and finite-set avoidance.
  have hopen : IsOpen (Set.Ioo (t - ε) (t + ε) ∩ Set.Ioo (0 : ℝ) 1) :=
    isOpen_Ioo.inter isOpen_Ioo
  have htOpen : t ∈ Set.Ioo (t - ε) (t + ε) ∩ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · constructor
      · linarith
      · linarith
    · exact ht
  obtain ⟨l, u, hltu, hsub⟩ :=
    exists_Ioo_subset_avoiding_finset hopen htOpen F htF
  have hleftSub : Set.Ioo l t ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact (hsub ⟨hx.1, lt_trans hx.2 hltu.2⟩).1.2
  have hrightSub : Set.Ioo t u ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    exact (hsub ⟨lt_trans hltu.1 hx.1, hx.2⟩).1.2
  -- The null-complement hypothesis supplies an `E`-point in each half-interval.
  obtain ⟨sLeft, hsLeftE, hsLeftIoo⟩ :=
    nonempty_inter_Ioo_of_volume_sdiff_eq_zero hconull hltu.1 hleftSub
  obtain ⟨sRight, hsRightE, hsRightIoo⟩ :=
    nonempty_inter_Ioo_of_volume_sdiff_eq_zero hconull hltu.2 hrightSub
  have hsLeftWindow : sLeft ∈ Set.Ioo (t - ε) (t + ε) :=
    (hsub ⟨hsLeftIoo.1, lt_trans hsLeftIoo.2 hltu.2⟩).1.1
  have hsRightWindow : sRight ∈ Set.Ioo (t - ε) (t + ε) :=
    (hsub ⟨lt_trans hltu.1 hsRightIoo.1, hsRightIoo.2⟩).1.1
  refine ⟨sLeft, ⟨hsLeftE, hsLeftWindow.1, hsLeftIoo.2⟩, sRight, ?_, ?_⟩
  · exact ⟨hsRightE, hsRightIoo.1, hsRightWindow.2⟩
  · intro x hxF hxBetween
    -- Any point between the two witnesses lies in the finite-set-free control interval.
    have hxControl : x ∈ Set.Ioo l u :=
      ⟨lt_trans hsLeftIoo.1 hxBetween.1, lt_trans hxBetween.2 hsRightIoo.2⟩
    exact (hsub hxControl).2 hxF

end Real

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Pointwise interval-coordinate representatives

This module defines the scalar pointwise representative of interval-coordinate
synthesis and its evaluation API.
-/

noncomputable section

namespace L1Seq

/-- The scalar function obtained by summing the rational interval indicators with
coefficients from a real summable sequence. -/
public noncomputable def pointwiseRepresentative (a : L1Seq) (s : ℝ) : ℝ :=
  ∑' n : ℕ,
    a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) s

/-- Evaluation of the pointwise representative is its defining scalar series. -/
public theorem pointwiseRepresentative_apply (a : L1Seq) (s : ℝ) :
    pointwiseRepresentative a s =
      ∑' n : ℕ,
        a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) s := by
  -- The displayed series is exactly the body of the representative definition.
  rfl

/-- The absolute values of the rational interval-indicator summands are summable at
every real point. -/
public theorem summable_abs_pointwiseRepresentative (a : L1Seq) (s : ℝ) :
    Summable (fun n : ℕ ↦
      |a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) s|) := by
  -- The `ℓ¹` hypothesis supplies the summable coordinatewise majorant.
  have hAbs : Summable (fun n : ℕ ↦ |a n|) := by
    have hOne : 0 < (1 : ENNReal).toReal := by
      norm_num
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      a.2.summable hOne
  -- Every indicator factor is zero or one, so each summand is bounded by that majorant.
  refine hAbs.of_norm_bounded (fun n ↦ ?_)
  by_cases hs : s ∈ Set.Ioo (0 : ℝ) (rationalTime n)
  · simp only [Set.indicator_of_mem hs, mul_one, Real.norm_eq_abs, abs_abs, le_refl]
  · simp only [Set.indicator_of_notMem hs, mul_zero, abs_zero, Real.norm_eq_abs,
      abs_nonneg]

/-- The pointwise representative agrees almost everywhere on the unit interval with
the interval-coordinate operator. -/
public theorem pointwiseRepresentative_ae_eq (a : L1Seq) :
    (fun s : ℝ ↦ pointwiseRepresentative a s) =ᵐ[
      MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun s : ℝ ↦ intervalCoordinateOperator a s) := by
  -- Norm summability gives the non-top extended-norm sum required by `Lp.coeFn_tsum`.
  have hEnorm :
      (∑' n : ℕ, ‖a n • UnitL2.rationalIntervalVec n‖ₑ) ≠ (⊤ : ENNReal) :=
    tsum_enorm_ne_top_iff_summable_norm.2
      (summable_norm_smul_rationalIntervalVec a)
  have hTsum :
      (fun s : ℝ ↦ (∑' n : ℕ, a n • UnitL2.rationalIntervalVec n) s) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
          (fun s : ℝ ↦ ∑' n : ℕ, (a n • UnitL2.rationalIntervalVec n) s) :=
    MeasureTheory.Lp.coeFn_tsum hEnorm
  -- Scalar multiplication and each interval-vector representative agree pointwise a.e.
  have hTerm (n : ℕ) :
      (fun s : ℝ ↦ (a n • UnitL2.rationalIntervalVec n) s) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
          (fun s : ℝ ↦
            a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
              (fun _ ↦ (1 : ℝ)) s) := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul (a n) (UnitL2.rationalIntervalVec n),
      UnitL2.rationalIntervalVec_apply_ae n] with s hSmul hVec
    calc
      (a n • UnitL2.rationalIntervalVec n) s = a n * UnitL2.rationalIntervalVec n s := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hSmul
      _ = a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
          (fun _ ↦ (1 : ℝ)) s := congrArg (a n * ·) hVec
  have hAll :
      ∀ᵐ s : ℝ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
        ∀ n : ℕ,
          (a n • UnitL2.rationalIntervalVec n) s =
            a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
              (fun _ ↦ (1 : ℝ)) s :=
    MeasureTheory.ae_all_iff.2 hTerm
  -- On the common conull set, compare the two scalar series term by term.
  filter_upwards [hAll, hTsum] with s hs hsum
  calc
    pointwiseRepresentative a s =
        ∑' n : ℕ, a n * (Set.Ioo (0 : ℝ) (rationalTime n)).indicator
          (fun _ ↦ (1 : ℝ)) s := pointwiseRepresentative_apply a s
    _ = ∑' n : ℕ, (a n • UnitL2.rationalIntervalVec n) s :=
      tsum_congr (fun n ↦ (hs n).symm)
    _ = (∑' n : ℕ, a n • UnitL2.rationalIntervalVec n) s := hsum.symm
    _ = intervalCoordinateOperator a s :=
      congrArg (fun f : UnitL2 ↦ f s) (intervalCoordinateOperator_apply a).symm

/-- If the interval-coordinate operator vanishes, its pointwise representative
vanishes on a conull subset of the open unit interval. -/
public theorem pointwiseRepresentative_exists_conull_zero (a : L1Seq)
    (ha : intervalCoordinateOperator a = 0) :
    ∃ E : Set ℝ,
      E ⊆ Set.Ioo (0 : ℝ) 1 ∧
        MeasureTheory.volume (Set.Ioo (0 : ℝ) 1 \ E) = 0 ∧
          ∀ s ∈ E, pointwiseRepresentative a s = 0 := by
  -- Replace the operator by zero in its representative and combine the two a.e. identities.
  have hOperatorZero :
      (fun s : ℝ ↦ intervalCoordinateOperator a s) =ᵐ[
        MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun _ ↦ (0 : ℝ)) := by
    rw [ha]
    exact MeasureTheory.Lp.coeFn_zero ℝ 2
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1))
  have hVanishing :
      ∀ᵐ s : ℝ ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
        pointwiseRepresentative a s = 0 :=
    (pointwiseRepresentative_ae_eq a).trans hOperatorZero
  have hAmbient :
      ∀ᵐ s : ℝ ∂MeasureTheory.volume,
        s ∈ Set.Ioc (0 : ℝ) 1 → pointwiseRepresentative a s = 0 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).1 hVanishing
  -- Intersect the ambient conull equality set with the open unit interval.
  refine ⟨{s : ℝ | s ∈ Set.Ioo (0 : ℝ) 1 ∧ pointwiseRepresentative a s = 0}, ?_, ?_, ?_⟩
  · intro s hs
    exact hs.1
  · apply MeasureTheory.measure_mono_null ?_ (MeasureTheory.ae_iff.1 hAmbient)
    intro s hs
    change ¬(s ∈ Set.Ioc (0 : ℝ) 1 → pointwiseRepresentative a s = 0)
    intro hPoint
    apply hs.2
    exact ⟨hs.1, hPoint ⟨hs.1.1, hs.1.2.le⟩⟩
  · intro s hs
    exact hs.2

end L1Seq

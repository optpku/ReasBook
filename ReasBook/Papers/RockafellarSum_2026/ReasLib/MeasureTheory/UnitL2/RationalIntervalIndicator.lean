/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalIndicator
public import RockafellarSum_2026.ReasLib.Order.RationalTime

/-!
# Rational interval indicators

This module defines the interval-indicator sequence indexed by the fixed
rational-time enumeration.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace UnitL2

/-- The interval-indicator vector at the `n`th time in the fixed rational enumeration. -/
noncomputable def rationalIntervalVec (n : ℕ) : UnitL2 :=
  intervalVec
    ⟨rationalTime n, (rationalTime_mem_Ioo n).1.le, (rationalTime_mem_Ioo n).2.le⟩

/-- The function represented by `rationalIntervalVec n` is almost everywhere the indicator
of `Set.Ioo 0 (rationalTime n)` on the unit interval. -/
theorem rationalIntervalVec_apply_ae (n : ℕ) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      rationalIntervalVec n x =
        (Set.Ioo (0 : ℝ) (rationalTime n)).indicator (fun _ ↦ (1 : ℝ)) x := by
  -- Expose the packaged rational endpoint, then reuse the general representative theorem.
  unfold rationalIntervalVec
  exact intervalVec_apply_ae _

end UnitL2

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Real `L2` on the unit interval

This module fixes the unit-interval `L2` model and its canonical representative
and inner-product API.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/-- The real `L²` space on the unit interval, represented using Lebesgue measure on `ℝ`
restricted to `Set.Ioc 0 1`. -/
abbrev UnitL2 : Type :=
  MeasureTheory.Lp ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))

namespace UnitL2

/-- The canonical real-linear inclusion of `UnitL2` into its `AEEqFun` representation. -/
def toAEEqFun : UnitL2 →ₗ[ℝ] (ℝ →ₘ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ℝ) :=
  Submodule.subtype
    (MeasureTheory.Lp.LpSubmodule ℝ ℝ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- Evaluating the `AEEqFun` view of an element of `UnitL2` agrees with its inherited
function coercion. -/
theorem toAEEqFun_apply (f : UnitL2) (x : ℝ) : toAEEqFun f x = f x := by
  -- The subtype inclusion and the inherited function coercion expose the same representative.
  rfl

/-- Two elements of `UnitL2` are equal exactly when their canonical `AEEqFun` views are
equal. -/
theorem ext_iff (f g : UnitL2) : f = g ↔ toAEEqFun f = toAEEqFun g := by
  constructor
  · intro h
    -- Equality in `UnitL2` is preserved by its canonical inclusion.
    exact congrArg toAEEqFun h
  · intro h
    -- Equality of the included values identifies the elements of the subtype.
    exact Subtype.ext h

end UnitL2

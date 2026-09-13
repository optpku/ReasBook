/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates
public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2.IntervalCoordinateOperator.Injective

/-!
# Lorentz-coordinate kernel

This module proves that vanishing negative Lorentz coordinates recover the
underlying parametrization parameters.
-/

public section

namespace Lorentz

/-- Vanishing of the negative coordinate of `parametrizedPoint d a t` recovers the
parameters `a = 0` and `t = 0`. -/
theorem parameters_eq_zero_of_negativeCoordinate_eq_zero (d : C0Seq) (hd : d ≠ 0)
    (a : L1Seq) (t : ℝ)
    (hN : negativeCoordinate d hd (parametrizedPoint d a t) = 0) :
    a = 0 ∧ t = 0 := by
  -- Expose the two components of the negative coordinate.
  rw [negativeCoordinate_apply] at hN
  have hfst : L1Seq.intervalCoordinateOperator a = 0 := by
    have hProjection := congrArg HilbertProd2.fst hN
    simpa [HilbertProd2.fst, HilbertProd2.mk] using hProjection
  -- Injectivity of the interval-coordinate operator recovers the sequence parameter.
  have hinterval : L1Seq.intervalCoordinateOperator a =
      L1Seq.intervalCoordinateOperator 0 := by
    simpa using hfst
  have ha : a = 0 := L1Seq.intervalCoordinateOperator_injective hinterval
  subst a
  -- The remaining scalar component is `t / 2`, so it determines `t`.
  have hsnd := congrArg HilbertProd2.snd hN
  have hsnd' : t / 2 = 0 := by
    simpa [HilbertProd2.snd, HilbertProd2.mk] using hsnd
  constructor
  · trivial
  · linarith

/-- If the negative coordinate of a point in `parametrizedSubspace d` vanishes,
then the point itself is zero. -/
theorem eq_zero_of_negativeCoordinate_eq_zero (d : C0Seq) (hd : d ≠ 0)
    (z : parametrizedSubspace d) (hN : negativeCoordinate d hd z = 0) :
    z = 0 := by
  -- Represent the subspace point by its sequence and scalar parameters.
  obtain ⟨a, t, hz⟩ := (mem_parametrizedSubspace d z.1).mp z.property
  have hpoint : z = parametrizedPoint d a t := by
    apply Subtype.ext
    rw [parametrizedPoint_apply, parametrization_apply]
    exact hz
  -- Vanishing of the negative coordinate forces both parameters to vanish.
  rw [hpoint]
  obtain ⟨ha, ht⟩ := parameters_eq_zero_of_negativeCoordinate_eq_zero d hd a t
    (hpoint ▸ hN)
  subst a
  subst t
  -- The canonical point with zero parameters is the zero subspace element.
  apply Subtype.ext
  rw [parametrizedPoint_apply, parametrization_apply]
  simp

end Lorentz

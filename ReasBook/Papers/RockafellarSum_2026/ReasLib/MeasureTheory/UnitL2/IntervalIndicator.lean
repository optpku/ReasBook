/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.MeasureTheory.UnitL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.UnitInterval

/-!
# Interval indicator vectors

This module defines the `UnitL2` representatives of interval indicators and
their basic almost-everywhere identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnitL2

/-- The `UnitL2` vector represented by the indicator of the open interval `(0, t)`. -/
noncomputable def intervalVec (t : unitInterval) : UnitL2 :=
  MeasureTheory.indicatorConstLp 2 measurableSet_Ioo
    (MeasureTheory.measure_ne_top
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) t))
    (1 : ℝ)

/-- The function represented by `intervalVec t` is almost everywhere the indicator of
`Set.Ioo 0 t` for Lebesgue measure restricted to `Set.Ioc 0 1`. -/
theorem intervalVec_apply_ae (t : unitInterval) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      intervalVec t x = (Set.Ioo (0 : ℝ) t).indicator (fun _ ↦ (1 : ℝ)) x := by
  -- Unfold the wrapper and use the canonical representative of `indicatorConstLp`.
  unfold intervalVec
  filter_upwards [MeasureTheory.indicatorConstLp_coeFn (c := (1 : ℝ))] with x hx
  exact hx

/-- The inner product of two interval-indicator vectors is the minimum of their endpoints. -/
theorem inner_intervalVec (s t : unitInterval) :
    ⟪intervalVec s, intervalVec t⟫_ℝ = min s t := by
  -- The overlap of the two indicator supports stays inside the restricted unit interval.
  have hoverlap :
      Set.Ioo (0 : ℝ) (s : ℝ) ∩ Set.Ioo (0 : ℝ) (t : ℝ) ⊆ Set.Ioc 0 1 := by
    intro x hx
    exact ⟨hx.1.1, hx.1.2.le.trans (unitInterval.le_one s)⟩
  -- Hence restriction does not change the measure of the overlap.
  have hrestrict :
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).real
          (Set.Ioo (0 : ℝ) (s : ℝ) ∩ Set.Ioo (0 : ℝ) (t : ℝ)) =
        volume.real (Set.Ioo (0 : ℝ) (s : ℝ) ∩ Set.Ioo (0 : ℝ) (t : ℝ)) := by
    exact congrArg ENNReal.toReal (Measure.restrict_eq_self volume hoverlap)
  -- The canonical `L2` formula reduces the inner product to the overlap length.
  have hmin_nonneg : (0 : ℝ) ≤ min (s : ℝ) (t : ℝ) :=
    le_min (unitInterval.nonneg s) (unitInterval.nonneg t)
  unfold intervalVec
  rw [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, hrestrict,
    Set.Ioo_inter_Ioo]
  simp only [sup_idem]
  rw [Real.volume_real_Ioo_of_le hmin_nonneg, sub_zero]
  -- Coercion from the ordered subtype preserves the minimum of the endpoints.
  simp

/-- The inner product of interval-indicator vectors with endpoints strictly between zero
and one is the minimum of those endpoints. -/
theorem inner_intervalVec_of_mem_Ioo (s t : unitInterval)
    (_hs : (s : ℝ) ∈ Set.Ioo 0 1) (_ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    ⟪intervalVec s, intervalVec t⟫_ℝ = min (s : ℝ) (t : ℝ) := by
  -- The unrestricted Gram identity already gives the formula at these endpoints.
  exact inner_intervalVec s t

/-- The squared norm of an interval-indicator vector is its endpoint. -/
theorem norm_sq_intervalVec (t : unitInterval) :
    ‖intervalVec t‖ ^ 2 = t := by
  -- View the squared norm as a diagonal inner product and use the overlap formula.
  rw [← real_inner_self_eq_norm_sq, inner_intervalVec, min_self]

/-- The norm of an interval-indicator vector whose endpoint lies strictly between zero
and one is the square root of its endpoint. -/
theorem norm_intervalVec_of_mem_Ioo (t : unitInterval) (_ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    ‖intervalVec t‖ = Real.sqrt (t : ℝ) := by
  -- Recover the nonnegative norm by taking square roots of the squared-norm identity.
  calc
    ‖intervalVec t‖ = Real.sqrt (‖intervalVec t‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg (intervalVec t))).symm
    _ = Real.sqrt (t : ℝ) := congrArg Real.sqrt (norm_sq_intervalVec t)

/-- The norm of an interval-indicator vector whose endpoint lies strictly between zero
and one is at most one. -/
theorem norm_intervalVec_le_one_of_mem_Ioo (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    ‖intervalVec t‖ ≤ 1 := by
  -- Rewrite the norm, then use the upper endpoint bound from membership in `(0, 1)`.
  rw [norm_intervalVec_of_mem_Ioo t ht]
  exact Real.sqrt_le_one.mpr ht.2.le

/-- The squared distance between two interval-indicator vectors is the absolute
difference of their endpoints. -/
theorem norm_sub_intervalVec_sq (s t : unitInterval) :
    ‖intervalVec s - intervalVec t‖ ^ 2 = |(s : ℝ) - (t : ℝ)| := by
  -- Expand the squared distance and replace every inner-product term by its endpoint formula.
  rw [norm_sub_sq_real, norm_sq_intervalVec, inner_intervalVec, norm_sq_intervalVec]
  -- The two endpoint orders determine both the minimum and the sign of their difference.
  rcases le_total s t with hst | hts
  · have hsub : (s : ℝ) - (t : ℝ) ≤ 0 := sub_nonpos.mpr hst
    rw [min_eq_left hst, abs_of_nonpos hsub]
    ring
  · have hsub : 0 ≤ (s : ℝ) - (t : ℝ) := sub_nonneg.mpr hts
    rw [min_eq_right hts, abs_of_nonneg hsub]
    ring

/-- The distance between two interval-indicator vectors is the square root of the
absolute difference of their endpoints. -/
theorem norm_sub_intervalVec (s t : unitInterval) :
    ‖intervalVec s - intervalVec t‖ = Real.sqrt |(s : ℝ) - (t : ℝ)| := by
  -- Substitute the squared-distance identity under the square root.
  rw [← norm_sub_intervalVec_sq]
  -- The norm is nonnegative, so taking the square root of its square recovers it.
  exact (Real.sqrt_sq (norm_nonneg (intervalVec s - intervalVec t))).symm

/-- The distance between interval-indicator vectors with endpoints strictly between zero
and one is the square root of the absolute difference of those endpoints. -/
theorem norm_sub_intervalVec_of_mem_Ioo (s t : unitInterval)
    (_hs : (s : ℝ) ∈ Set.Ioo 0 1) (_ht : (t : ℝ) ∈ Set.Ioo 0 1) :
    ‖intervalVec s - intervalVec t‖ = Real.sqrt |(s : ℝ) - (t : ℝ)| := by
  -- The unrestricted distance identity specializes directly to these endpoints.
  exact norm_sub_intervalVec s t

end UnitL2

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngleLift
import ReasLib.Topology.Circle.AngleLift
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Comparing endpoint polar and gradient angle lifts

This file identifies the difference between the real lifts of endpoint polar and
gradient angles with the physical oriented angle from the gradient direction to the
radial direction.  The branch-selection argument is delegated to the generic API for
sequences of `Real.Angle` values.
-/

public section

noncomputable section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-- The generic canonical lift of the endpoint polar-angle sequence agrees pointwise
with the orbit's endpoint polar-angle lift. -/
private theorem liftSequence_endpointPolarAngle (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    Real.Angle.liftSequence (orbit.endpointPolarAngle C) n =
      orbit.endpointPolarAngleLift C n := by
  induction n with
  | zero =>
      rw [Real.Angle.liftSequence_zero, endpointPolarAngleLift_zero]
  | succ n ih =>
      rw [Real.Angle.liftSequence_succ, endpointPolarAngleLift_succ, ih]

/-- The generic canonical lift of the endpoint gradient-angle sequence agrees pointwise
with the orbit's endpoint gradient-angle lift. -/
private theorem liftSequence_endpointGradientAngle (orbit : DFP.TwoPhaseOrbit) (n : ℕ) :
    Real.Angle.liftSequence orbit.endpointGradientAngle n =
      orbit.endpointGradientAngleLift n := by
  induction n with
  | zero =>
      rw [Real.Angle.liftSequence_zero, endpointGradientAngleLift_zero]
  | succ n ih =>
      rw [Real.Angle.liftSequence_succ, endpointGradientAngleLift_succ, ih]

/-- The quotient-valued endpoint polar angle minus the gradient angle is the physical
oriented angle from the endpoint gradient to the radial displacement. -/
theorem endpointPolarAngle_sub_gradientAngle
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (hgradient : orbit.endpointGradient k ≠ 0) (hradial : orbit.endpoint k - C ≠ 0) :
    orbit.endpointPolarAngle C k - orbit.endpointGradientAngle k =
      EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C) := by
  have hbasis : EuclideanSpace.basisFun (Fin 2) ℝ 0 ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    norm_num [EuclideanSpace.basisFun_apply] at hcoordinate
  rw [endpointPolarAngle_def, endpointGradientAngle_def]
  exact EuclideanPlane.orientation.oangle_sub_left hbasis hgradient hradial

/-- Coercing the difference of the endpoint polar and gradient lifts gives the physical
polar-to-gradient correction angle. -/
theorem polarGradientLiftDifference_coe
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (hgradient : orbit.endpointGradient k ≠ 0) (hradial : orbit.endpoint k - C ≠ 0) :
    ((orbit.endpointPolarAngleLift C k - orbit.endpointGradientAngleLift k : ℝ) :
        Real.Angle) =
      EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C) := by
  change (orbit.endpointPolarAngleLift C k : Real.Angle) -
      (orbit.endpointGradientAngleLift k : Real.Angle) = _
  rw [endpointPolarAngleLift_coe, endpointGradientAngleLift_coe]
  exact endpointPolarAngle_sub_gradientAngle orbit C k hgradient hradial

/-- If the initial endpoint polar and gradient representatives are both in a common
quarter-turn chart, their lifted difference is the principal representative of the
physical correction angle. -/
theorem polarGradientLiftDifference_zero_of_small
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hgradient : orbit.endpointGradient 0 ≠ 0) (hradial : orbit.endpoint 0 - C ≠ 0)
    (hpolar : |(orbit.endpointPolarAngle C 0).toReal| < Real.pi / 4)
    (hgradientAngle : |(orbit.endpointGradientAngle 0).toReal| < Real.pi / 4) :
    orbit.endpointPolarAngleLift C 0 - orbit.endpointGradientAngleLift 0 =
      (EuclideanPlane.orientation.oangle (orbit.endpointGradient 0)
        (orbit.endpoint 0 - C)).toReal := by
  have hcoe := polarGradientLiftDifference_coe orbit C 0 hgradient hradial
  rw [endpointPolarAngleLift_zero, endpointGradientAngleLift_zero] at hcoe ⊢
  have htriangle := abs_sub (orbit.endpointPolarAngle C 0).toReal
    (orbit.endpointGradientAngle 0).toReal
  have habs :
      |(orbit.endpointPolarAngle C 0).toReal -
          (orbit.endpointGradientAngle 0).toReal| < Real.pi := by
    linarith [Real.pi_pos]
  have hprincipal :
      (orbit.endpointPolarAngle C 0).toReal -
          (orbit.endpointGradientAngle 0).toReal ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hbounds := abs_lt.mp habs
    exact ⟨hbounds.1, hbounds.2.le⟩
  have hreal := congrArg Real.Angle.toReal hcoe
  have hprincipalReal :
      ((((orbit.endpointPolarAngle C 0).toReal -
          (orbit.endpointGradientAngle 0).toReal : ℝ) : Real.Angle).toReal) =
        (orbit.endpointPolarAngle C 0).toReal -
          (orbit.endpointGradientAngle 0).toReal :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hprincipal
  rw [hprincipalReal] at hreal
  exact hreal

/-- Small consecutive polar and gradient increments select a single real branch on
which the difference of their lifts equals the physical correction angle at every
endpoint. -/
theorem polarGradientLiftDifference_eq_correction_of_small
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hgradientNe : ∀ k : ℕ, orbit.endpointGradient k ≠ 0)
    (hradialNe : ∀ k : ℕ, orbit.endpoint k - C ≠ 0)
    (hbase : orbit.endpointPolarAngleLift C 0 - orbit.endpointGradientAngleLift 0 =
      (EuclideanPlane.orientation.oangle (orbit.endpointGradient 0)
        (orbit.endpoint 0 - C)).toReal)
    (hpolarGap : ∀ k : ℕ,
      |(orbit.endpointPolarAngle C (k + 1) -
        orbit.endpointPolarAngle C k).toReal| < Real.pi / 4)
    (hgradientGap : ∀ k : ℕ,
      |(orbit.endpointGradientAngle (k + 1) -
        orbit.endpointGradientAngle k).toReal| < Real.pi / 4)
    (hcorrection : ∀ k : ℕ,
      |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal| < Real.pi / 4) :
    ∀ k : ℕ,
      orbit.endpointPolarAngleLift C k - orbit.endpointGradientAngleLift k =
        (EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
          (orbit.endpoint k - C)).toReal := by
  have hzero :
      Real.Angle.liftSequence (orbit.endpointPolarAngle C) 0 -
          Real.Angle.liftSequence orbit.endpointGradientAngle 0 =
        (orbit.endpointPolarAngle C 0 - orbit.endpointGradientAngle 0).toReal := by
    rw [liftSequence_endpointPolarAngle, liftSequence_endpointGradientAngle]
    have hangle := congrArg Real.Angle.toReal
      (endpointPolarAngle_sub_gradientAngle orbit C 0
        (hgradientNe 0) (hradialNe 0))
    exact hbase.trans hangle.symm
  have hprincipal : ∀ k : ℕ,
      (orbit.endpointPolarAngle C k - orbit.endpointGradientAngle k).toReal +
          (orbit.endpointPolarAngle C (k + 1) -
            orbit.endpointPolarAngle C k).toReal -
          (orbit.endpointGradientAngle (k + 1) -
            orbit.endpointGradientAngle k).toReal ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro k
    have hangle := congrArg Real.Angle.toReal
      (endpointPolarAngle_sub_gradientAngle orbit C k
        (hgradientNe k) (hradialNe k))
    rw [hangle]
    have hfirst := abs_add_le
      (EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal
    have hsecond := abs_sub
      ((EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
        (orbit.endpoint k - C)).toReal +
        (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal)
      (orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal
    have habs :
        |(EuclideanPlane.orientation.oangle (orbit.endpointGradient k)
              (orbit.endpoint k - C)).toReal +
            (orbit.endpointPolarAngle C (k + 1) -
              orbit.endpointPolarAngle C k).toReal -
            (orbit.endpointGradientAngle (k + 1) -
              orbit.endpointGradientAngle k).toReal| < Real.pi := by
      linarith [hcorrection k, hpolarGap k, hgradientGap k, Real.pi_pos]
    have hbounds := abs_lt.mp habs
    exact ⟨hbounds.1, hbounds.2.le⟩
  have hbranch := Real.Angle.liftSequence_sub_eq_toReal_sub_of_mem_Ioc
    (orbit.endpointPolarAngle C) orbit.endpointGradientAngle hzero hprincipal
  intro k
  have hk := hbranch k
  rw [liftSequence_endpointPolarAngle, liftSequence_endpointGradientAngle] at hk
  have hangle := congrArg Real.Angle.toReal
    (endpointPolarAngle_sub_gradientAngle orbit C k
      (hgradientNe k) (hradialNe k))
  exact hk.trans hangle

end DFP.TwoPhaseOrbit

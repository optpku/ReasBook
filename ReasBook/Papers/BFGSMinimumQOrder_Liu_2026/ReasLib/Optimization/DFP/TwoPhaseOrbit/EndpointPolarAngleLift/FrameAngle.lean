module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle
public import ReasLib.Topology.Circle.AngleLift
import Mathlib.Tactic.Linarith

/-!
# Even endpoint-polar lifts relative to the accumulated frame angle

This file specializes the principal-branch theorem for canonical angle lifts to the
even endpoint subsequence of a two-phase DFP orbit.  Orbit geometry supplies only the
quotient relation and local smallness; the branch induction itself lives in
`Real.Angle.liftSequence_even_sub_eq_toReal_of_coe_of_mem_Ioc`.
-/

public section

noncomputable section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-- The recursively unwrapped endpoint-polar angle is the canonical lift of the
quotient-valued endpoint-polar angle sequence. -/
theorem endpointPolarAngleLift_eq_liftSequence
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) :
    orbit.endpointPolarAngleLift C =
      Real.Angle.liftSequence (orbit.endpointPolarAngle C) := by
  funext k
  induction k with
  | zero =>
      rw [endpointPolarAngleLift_zero, Real.Angle.liftSequence_zero]
  | succ k ih =>
      rw [endpointPolarAngleLift_succ, Real.Angle.liftSequence_succ, ih]

/-- A principal-interval branch-selection principle for the even endpoint-polar lift
relative to the accumulated frame angle. -/
theorem endpointPolarAngleLift_even_eq_frameAngle_add_correction_of_mem_Ioc
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hbase : orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
      (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
        (orbit.endpoint 0 - C)).toReal)
    (hquot : ∀ j : ℕ,
      ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
          Real.Angle) =
        EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - C))
    (hprincipal : ∀ j : ℕ,
      (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - C)).toReal +
          (orbit.endpointPolarAngle C (2 * j + 1) -
            orbit.endpointPolarAngle C (2 * j)).toReal +
          (orbit.endpointPolarAngle C ((2 * j + 1) + 1) -
            orbit.endpointPolarAngle C (2 * j + 1)).toReal -
          (orbit.frameAngle (j + 1) - orbit.frameAngle j) ∈
            Set.Ioc (-Real.pi) Real.pi) :
    ∀ j : ℕ,
      orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j =
        (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - C)).toReal := by
  rw [endpointPolarAngleLift_eq_liftSequence orbit C] at hbase hquot ⊢
  exact Real.Angle.liftSequence_even_sub_eq_toReal_of_coe_of_mem_Ioc
    (orbit.endpointPolarAngle C) orbit.frameAngle
    (fun j ↦ EuclideanPlane.orientation.oangle (orbit.state j).lowVector
      (orbit.endpoint (2 * j) - C)) hbase hquot hprincipal

/-- If the correction, both intervening polar gaps, and the frame increment are each
smaller than `π / 8`, the even endpoint-polar lift selects the physical correction
branch relative to the accumulated frame angle. -/
theorem endpointPolarAngleLift_even_eq_frameAngle_add_correction_of_small
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hbase : orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
      (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
        (orbit.endpoint 0 - C)).toReal)
    (hquot : ∀ j : ℕ,
      ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
          Real.Angle) =
        EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - C))
    (hgap : ∀ k : ℕ,
      |(orbit.endpointPolarAngle C (k + 1) -
        orbit.endpointPolarAngle C k).toReal| < Real.pi / 8)
    (hframe : ∀ j : ℕ,
      |orbit.frameAngle (j + 1) - orbit.frameAngle j| < Real.pi / 8)
    (hcorr : ∀ j : ℕ,
      |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.endpoint (2 * j) - C)).toReal| < Real.pi / 8) :
    ∀ j : ℕ,
      orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j =
        (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - C)).toReal := by
  apply endpointPolarAngleLift_even_eq_frameAngle_add_correction_of_mem_Ioc
    orbit C hbase hquot
  intro j
  rcases abs_lt.mp (hcorr j) with ⟨haLower, haUpper⟩
  rcases abs_lt.mp (hgap (2 * j)) with ⟨hbLower, hbUpper⟩
  rcases abs_lt.mp (hgap (2 * j + 1)) with ⟨hcLower, hcUpper⟩
  rcases abs_lt.mp (hframe j) with ⟨hdLower, hdUpper⟩
  constructor <;> linarith [Real.pi_pos]

end DFP.TwoPhaseOrbit

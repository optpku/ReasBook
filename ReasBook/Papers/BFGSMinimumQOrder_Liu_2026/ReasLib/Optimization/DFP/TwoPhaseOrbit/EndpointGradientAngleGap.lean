module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import ReasLib.Geometry.Euclidean.Plane.FrameOrientedAngle
import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
import all ReasLib.Optimization.DFP.TwoPhaseOrbit
import Mathlib.Tactic.FinCases

/-!
# Endpoint gradient-angle gaps

This file identifies the two physical endpoint gradient-angle increments in one exact
two-phase orbit cycle with the corresponding normalized observable angles.
-/

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoPhaseOrbit

/-- Within an exact cycle, the gradient angle from the even endpoint to the following
odd endpoint is the first normalized endpoint-angle observable. -/
theorem endpointGradientAngle_odd_sub_even
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ)
    (hstate : State.PhaseValidity (orbit.state j))
    (heven : orbit.endpointGradient (2 * j) ≠ 0)
    (hodd : orbit.endpointGradient (2 * j + 1) ≠ 0) :
    orbit.endpointGradientAngle (2 * j + 1) -
        orbit.endpointGradientAngle (2 * j) =
      (DFP.TwoLeg.observableMap
        (orbit.state j).coordinates).firstEndpointAngleIncrement := by
  have hbasis : EuclideanSpace.basisFun (Fin 2) ℝ 0 ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    norm_num [EuclideanSpace.basisFun_apply] at hcoordinate
  rw [endpointGradientAngle_def, endpointGradientAngle_def,
    EuclideanPlane.orientation.oangle_sub_left hbasis heven hodd]
  rw [endpointGradient_even, endpointGradient_odd, State.gradient_def,
    State.middleGradient_def]
  have hcancel :
      EuclideanPlane.orientation.oangle
          ((orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ
              ![(1 : ℝ), (orbit.state j).p * (orbit.state j).ε ^ 2]))
          ((orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ
              DFP.FirstLeg.outputGradient (orbit.state j).ε
                (orbit.state j).p (orbit.state j).h)) =
        EuclideanPlane.orientation.oangle
          (!₂[(1 : ℝ), (orbit.state j).p * (orbit.state j).ε ^ 2] :
            EuclideanSpace ℝ (Fin 2))
          (!₂[DFP.FirstLeg.outputGradient (orbit.state j).ε
              (orbit.state j).p (orbit.state j).h 0,
            DFP.FirstLeg.outputGradient (orbit.state j).ε
              (orbit.state j).p (orbit.state j).h 1] :
            EuclideanSpace ℝ (Fin 2)) := by
    rw [EuclideanPlane.orientation.oangle_smul_left_of_pos _ _ hstate.amplitude_pos,
      EuclideanPlane.orientation.oangle_smul_right_of_pos _ _ hstate.amplitude_pos]
    exact EuclideanPlane.oangle_specialOrthogonal_mulVec
      (orbit.state j).frame hstate.frame_specialOrthogonal
      1 ((orbit.state j).p * (orbit.state j).ε ^ 2)
      (DFP.FirstLeg.outputGradient (orbit.state j).ε
        (orbit.state j).p (orbit.state j).h 0)
      (DFP.FirstLeg.outputGradient (orbit.state j).ε
        (orbit.state j).p (orbit.state j).h 1)
  have hobservable := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_endpointAngleIncrements
      (orbit.state j).ε (orbit.state j).p (orbit.state j).h)
  simpa only [State.coordinates_def] using hcancel.trans hobservable.symm

/-- Within an exact cycle, the gradient angle from its odd endpoint to the next even
endpoint is the second normalized endpoint-angle observable. -/
theorem endpointGradientAngle_nextEven_sub_odd
    (orbit : DFP.TwoPhaseOrbit) (j : ℕ)
    (hstate : State.PhaseValidity (orbit.state j))
    (hodd : orbit.endpointGradient (2 * j + 1) ≠ 0)
    (hnextEven : orbit.endpointGradient (2 * j + 2) ≠ 0) :
    orbit.endpointGradientAngle (2 * j + 2) -
        orbit.endpointGradientAngle (2 * j + 1) =
      (DFP.TwoLeg.observableMap
        (orbit.state j).coordinates).secondEndpointAngleIncrement := by
  have hbasis : EuclideanSpace.basisFun (Fin 2) ℝ 0 ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    norm_num [EuclideanSpace.basisFun_apply] at hcoordinate
  rw [endpointGradientAngle_def, endpointGradientAngle_def,
    EuclideanPlane.orientation.oangle_sub_left hbasis hodd hnextEven]
  have hnextIndex : 2 * j + 2 = 2 * (j + 1) := by
    simp [Nat.mul_add]
  rw [hnextIndex, endpointGradient_even, endpointGradient_odd]
  have hnextState : orbit.state (j + 1) = (orbit.state j).next :=
    orbit.state_succ j
  have hexact :=
    (State.secondPhaseExact_of_phaseValidity (orbit.state j) hstate).gradient
  have houtput : (State.secondStep (orbit.state j) hstate).nextGradient =
      (orbit.state j).amplitude • DFP.SecondLeg.outputGradient
        (orbit.state j).ε (orbit.state j).p (orbit.state j).h := by
    simpa only using congrArg Prod.snd
      (State.secondStep_output (orbit.state j) hstate)
  have hnextGradient : (orbit.state (j + 1)).gradient =
      (orbit.state j).amplitude • WithLp.toLp 2
        ((orbit.state j).frame *ᵥ
          (DFP.FirstLeg.frame (orbit.state j).ε
            (orbit.state j).p (orbit.state j).h *ᵥ
            DFP.SecondLeg.outputGradient (orbit.state j).ε
              (orbit.state j).p (orbit.state j).h)) := by
    rw [hnextState, hexact, houtput, State.middleFrame_def,
      Matrix.mulVec_smul, WithLp.toLp_smul, Matrix.mulVec_mulVec]
  rw [hnextGradient, State.middleGradient_def]
  let v₂ : Fin 2 → ℝ := DFP.FirstLeg.frame (orbit.state j).ε
    (orbit.state j).p (orbit.state j).h *ᵥ
    DFP.SecondLeg.outputGradient (orbit.state j).ε
      (orbit.state j).p (orbit.state j).h
  have hcancel :
      EuclideanPlane.orientation.oangle
          ((orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ
              DFP.FirstLeg.outputGradient (orbit.state j).ε
                (orbit.state j).p (orbit.state j).h))
          ((orbit.state j).amplitude • WithLp.toLp 2
            ((orbit.state j).frame *ᵥ v₂)) =
        EuclideanPlane.orientation.oangle
          (!₂[DFP.FirstLeg.outputGradient (orbit.state j).ε
              (orbit.state j).p (orbit.state j).h 0,
            DFP.FirstLeg.outputGradient (orbit.state j).ε
              (orbit.state j).p (orbit.state j).h 1] :
            EuclideanSpace ℝ (Fin 2))
          (!₂[v₂ 0, v₂ 1] : EuclideanSpace ℝ (Fin 2)) := by
    rw [EuclideanPlane.orientation.oangle_smul_left_of_pos _ _ hstate.amplitude_pos,
      EuclideanPlane.orientation.oangle_smul_right_of_pos _ _ hstate.amplitude_pos]
    exact EuclideanPlane.oangle_specialOrthogonal_mulVec
      (orbit.state j).frame hstate.frame_specialOrthogonal
      (DFP.FirstLeg.outputGradient (orbit.state j).ε
        (orbit.state j).p (orbit.state j).h 0)
      (DFP.FirstLeg.outputGradient (orbit.state j).ε
        (orbit.state j).p (orbit.state j).h 1)
      (v₂ 0) (v₂ 1)
  have hfirstVector :
      DFP.FirstLeg.outputGradient (orbit.state j).ε
          (orbit.state j).p (orbit.state j).h =
        ![DFP.FirstLeg.outputGradient (orbit.state j).ε
            (orbit.state j).p (orbit.state j).h 0,
          DFP.FirstLeg.outputGradient (orbit.state j).ε
            (orbit.state j).p (orbit.state j).h 1] := by
    funext i
    fin_cases i
    · rfl
    · rfl
  have hsecondVector :
      DFP.FirstLeg.frame (orbit.state j).ε
          (orbit.state j).p (orbit.state j).h *ᵥ
          DFP.SecondLeg.outputGradient (orbit.state j).ε
            (orbit.state j).p (orbit.state j).h =
        ![v₂ 0, v₂ 1] := by
    change v₂ = _
    funext i
    fin_cases i
    · rfl
    · rfl
  have hobservable := congrArg Prod.snd
    (DFP.TwoLeg.observableMap_endpointAngleIncrements
      (orbit.state j).ε (orbit.state j).p (orbit.state j).h)
  rw [hfirstVector, hsecondVector] at hobservable
  simpa only [State.coordinates_def] using hcancel.trans hobservable.symm

end DFP.TwoPhaseOrbit

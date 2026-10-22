/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.QuadraticBridge
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.StepNorm
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.PredictedDecrease
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.CorrectionRatio
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.StepRatio

/-!
# Uniform step-descent estimates on invariant slow curves

This umbrella exposes the bundled `DFP.TwoLeg.SlowCurve` API together with the
unbundled compatibility statements used by existing consumers.
-/

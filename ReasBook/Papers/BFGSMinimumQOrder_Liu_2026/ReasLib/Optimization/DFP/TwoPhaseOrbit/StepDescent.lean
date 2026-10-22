/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseOrbit/StepDescent.lean
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

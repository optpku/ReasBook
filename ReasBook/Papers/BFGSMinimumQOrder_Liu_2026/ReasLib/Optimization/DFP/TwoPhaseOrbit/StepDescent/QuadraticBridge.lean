/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Optimization/DFP/TwoPhaseOrbit/StepDescent/QuadraticBridge.lean
-/

module

public import ReasLib.Analysis.Normed.QuadraticBounds
public import ReasLib.Optimization.DFP.AbstractSecantStep.PhaseBounds

/-!
# Step-descent quadratic bridges

This compatibility umbrella re-exports the generic norm-interval estimates and
the phase-controlled abstract secant-step bounds from their canonical owners.
-/

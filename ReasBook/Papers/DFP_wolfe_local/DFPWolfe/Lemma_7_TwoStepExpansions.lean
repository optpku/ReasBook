/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDrift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleRemainder

/-!
# Lemma 7: two-step expansions

Paper label: `lem:two-step-expansions` in `main-new.tex`.

On the invariant center manifold, the amplitude ratio is
`1 - (13 / 2)εⱼ⁴ + O(εⱼ⁶)` and the frame rotation is
`-3εⱼ² + O(εⱼ⁴)`. With `Cₖ = xₖ - gₖ`, the full-cycle center drift is
`-(116 / 5)Gⱼεⱼ⁶e₂ⱼ + O(Gⱼεⱼ⁷)` and the half-cycle displacement is
`O(Gⱼεⱼ³)`. The consecutive gradient polar-angle increments are
`-2εⱼ² + o(εⱼ²)` and `-εⱼ² + o(εⱼ²)`.

The checks retain every component, in the order of the paper's equations.
The amplitude check uses the sixth-order remainder proved in `AmplitudeJet`.
The other proofs are in the corresponding imported orbit modules.
-/

-- `eq:G-map`: the full O(ε⁶) amplitude remainder.
#check DFP.TwoLeg.slowCurveAmplitudeDrift

-- `eq:phi-map`, `eq:C-map`, and `eq:C-half`.
#check DFP.TwoPhaseOrbit.slowCurveFrameRotation
#check DFP.TwoPhaseOrbit.slowCurveFullCenterDrift
#check DFP.TwoPhaseOrbit.slowCurveHalfCenterDisplacement

-- `eq:half-angles`: a vanishing modulus for both within-cycle remainders.
#check DFP.TwoPhaseOrbit.slowCurveEndpointAngleRemainderModulus

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ScalarAsymptotics

/-!
# Lemma 8: scalar asymptotics and limiting circle

Paper label: `lem:scalar-asymptotics` in `main-new.tex`.

There are limits `G∞ > 0` and `C∞` with
`εⱼ ∼ ((9 / 2)j)^(-1 / 3)` and `Gⱼ - G∞ ∼ (13 / 3)G∞εⱼ`.
Both center subsequences approach `C∞` with error `O(εⱼ³)`, the unwrapped
frame angle tends to negative infinity, and the complete endpoint cluster set
equals the circle of center `C∞` and radius `G∞`.

`ScalarAsymptotics` packages these conclusions. The second check points
directly to the circle equality proved in `EndpointClusterSet`.
-/

#check DFP.TwoPhaseOrbit.slowCurveScalarAsymptotics
#check DFP.TwoPhaseOrbit.slowCurveEndpointClusterSet_eq_limitCircle

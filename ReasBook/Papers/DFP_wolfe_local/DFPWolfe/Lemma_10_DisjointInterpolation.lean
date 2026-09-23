/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Interpolation.SmoothExtension
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Interpolation.HessianBound
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.Interpolation
public import ReasLib.Optimization.DFP.PlanarConvergence

/-!
# Lemma 10: disjoint interpolation

Paper label: `lem:disjoint-interpolation` in `main-new.tex`.

The endpoint-bump correction Ψ, extended by zero on the limiting circle, is
`C²` with a globally one-half Hölder Hessian. It satisfies `Ψ(xₖ) = 0`,
`∇Ψ(xₖ) = aₖ`, and a uniform Hessian norm bound `K ε₀`.

The checks locate smoothness and zero-extension in `SmoothExtension`, the
endpoint values and gradients in `EndpointBump.Interpolation`, the uniform
bound in `HessianBound`, and Hölder regularity in `PlanarConvergence`.
The component statements expose the small-scale, invariant-curve, and
disjoint-support hypotheses assembled by the counterexample construction.
-/

-- Smoothness and zero-extension on the limiting circle.
#check contDiff_two_slowCurveBumpCorrection
#check slowCurveBumpCorrection_eqOn_zero

-- `eq:interpolation-jets` and `eq:interpolation-hessian-bound`.
#check DFP.TwoPhaseOrbit.bumpCorrection_endpoint
#check DFP.TwoPhaseOrbit.bumpCorrection_gradient_endpoint
#check slowCurveBumpCorrectionHessianBound

-- Global one-half Hölder Hessian regularity.
#check DFP.PlanarConvergence.bumpCorrectionHessianHolder

/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.Theorem_1_StrongWolfeCounterexample
public import DFPWolfe.Corollary_2_IdentityInitialization
public import DFPWolfe.Theorem_3_PlanarConvergence
public import DFPWolfe.Proposition_4_OneStepMap
public import DFPWolfe.Lemma_5_LocalInvariantGraph
public import DFPWolfe.Lemma_6_CenterManifold
public import DFPWolfe.Lemma_7_TwoStepExpansions
public import DFPWolfe.Lemma_8_ScalarAsymptotics
public import DFPWolfe.Lemma_9_UniformSeparation
public import DFPWolfe.Lemma_10_DisjointInterpolation
public import DFPWolfe.Lemma_11_PlanarSecantDegeneration

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Interpolation.IsolationBalls
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Interpolation.ObjectiveBounds
public import ReasLib.Optimization.DFP.WolfeCounterexample.CommonScale
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Interpolation.UniformBounds

/-!
# Paper results

The public entry point for the eleven numbered results in `main-new.tex`.
Each result has a correspondingly numbered file in `DFPWolfe`, with its LaTeX
label, mathematical summary, and checks of the existing proof declarations.
See `DFPWolfe/README.md` for the file and declaration index.

The remaining imports preserve the supporting interpolation and orbit API.
The navigation files do not duplicate declarations or proofs.
-/

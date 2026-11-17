/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.Latest.Theorem_1_StrongWolfeCounterexample
public import DFPWolfe.Latest.Corollary_2_IdentityInitialization
public import DFPWolfe.Latest.Theorem_3_PlanarConvergence
public import DFPWolfe.Latest.Lemma_4_PolarContinuation
public import DFPWolfe.Latest.Lemma_5_PolarGeometry
public import DFPWolfe.Latest.Lemma_6_PolarInterpolation
public import DFPWolfe.Latest.Lemma_7_PlanarSecantDegeneration
public import DFPWolfe.Latest.Sequences
public import DFPWolfe.Latest.Lemma_PolarDirectionUpdate
public import DFPWolfe.Latest.Lemma_PolarEndpointWolfe
public import DFPWolfe.Latest.Proposition_PolarRealization
public import DFPWolfe.Latest.Lemma_PolarLimitingCycle
public import DFPWolfe.Latest.Lemma_PolarParameterChoice
public import DFPWolfe.Latest.Lemma_PolarCycleEstimates

/-!
# DFP counterexample — the general polar construction

This entry follows `20251117-DFP/arXiv.tex`: Theorem 10, Corollary 11,
Lemma 12 and Theorem 13; the preliminary results are Lemmas 1–9, together with the unnumbered comparisons on the
same actual Wolfe orbit. Both Wolfe parameters
and the Hessian Hölder exponent
range over their full admissible intervals. The quantitative identity
normalization and all-dimensional extension retain the prescribed source data.

The earlier center-manifold and fixed-exponent polar constructions remain
available through `DFPWolfe.Paper` and `DFPWolfe.V21.Paper`; the preserved
`DFPWolfe.Latest.Proposition_8_CenterManifold` module is historical and is not
part of this manuscript entry. The current manuscript has thirteen theorem-like results under its shared counter. See `DFPWolfe/Latest/README.md` for the exact correspondence.
-/

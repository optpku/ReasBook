/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.V21.PolarData_Recurrence
public import DFPWolfe.V21.NormalizedMap_Dynamics
public import DFPWolfe.V21.LimitingTwoCycle
public import DFPWolfe.V21.Main
public import DFPWolfe.V21.IdentityInitialization
public import DFPWolfe.V21.PlanarConvergence
public import DFPWolfe.V21.PolarConstruction
public import DFPWolfe.V21.SecantDegeneration
public import DFPWolfe.V21.CenterManifold
public import DFPWolfe.V21.SequenceProperties
public import DFPWolfe.V21.CenterInterpolation
public import DFPWolfe.V21.FullTurn
public import DFPWolfe.V21.IdentityQuantitative

/-!
# DFP counterexample: the v21 paper

The source-facing entries follow the v21 manuscript numbering: Theorem 1
and its near-identity refinement, Corollary 2, Theorem 3, Lemmas 4–7,
and the independent center-manifold Proposition 8.
The counterexample uses the prescribed polar recurrence and explicit cutoff
interpolation; the original center-manifold proof remains available through
`DFPWolfe.Paper`.

Each imported source entry states the original result and records its LaTeX
label. Supporting proofs live in `ReasLib.Optimization.DFP.Polar`, while the
general previous-secant degeneration and planar convergence arguments retain
their broader mathematical hypotheses.

The Section 6 graph uses uniform C⁸ bounds for the actual graph-transform
iterates and Arzelà–Ascoli to obtain C⁷ regularity. Its recurrence, cancellation,
limiting scales and full circle cluster set are exported separately from the
polar counterexample. The unnumbered sequence comparisons hold on the same
canonical Wolfe witness as the polar theorem.

The conditional Section 6 interpolation retains the manuscript's explicit
disjoint-ball premise and eventual radius orders. It preserves the complete
original cutoff sum and its exact endpoint jets. The polar complete-turn
expansion is attached to the same Wolfe witness, and the identity-initialization
entry also exports the source's precise eigenvalue bounds and gradient liminf.
-/

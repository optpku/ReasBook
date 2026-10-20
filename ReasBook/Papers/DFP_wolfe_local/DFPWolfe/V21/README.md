# v21 paper correspondence

The v21 submission proves the counterexample by a prescribed polar recurrence
and explicit cutoff interpolation. Import `DFPWolfe.V21.Paper` for this route.
The repository root `DFPWolfe` also retains the original center-manifold proof
through `DFPWolfe.Paper`; its numbering is listed in the [original index](../README.md).

| v21 result | Source label | Public file and declaration |
| --- | --- | --- |
| Theorem 1: strong Wolfe counterexample in every dimension `n≥2` | `thm:main` | [Main](Main.lean): `DFPWolfe.V21.main` |
| Corollary 2: identity initialization and a centered elliptical accumulation set | `cor:identity-initialization` | [IdentityInitialization](IdentityInitialization.lean): `DFPWolfe.V21.identityInitializationExplicit` |
| Corollary 2 proof: precise eigenvalue bounds and gradient liminf | `cor:identity-initialization` | [IdentityQuantitative](IdentityQuantitative.lean): `DFPWolfe.V21.identityInitializationQuantitative` |
| Theorem 3: planar convergence with locally Lipschitz Hessian | `thm:planar-convergence` | [PlanarConvergence](PlanarConvergence.lean): `DFPWolfe.V21.planarConvergenceCases` |
| Lemma 4: continuation and invariant tube | `lem:polar-continuation` | [PolarConstruction](PolarConstruction.lean): `DFPWolfe.V21.polarContinuation` |
| Lemma 5: polar geometry and uniform separation | `lem:polar-geometry` | [PolarConstruction](PolarConstruction.lean): `DFPWolfe.V21.polarGeometry` |
| Complete-turn distance expansion on the same Wolfe witness | Paragraph following `lem:polar-geometry` | [FullTurn](FullTurn.lean): `DFPWolfe.V21.planarCounterexampleFamilyWithFullTurn` |
| Lemma 6: explicit disjoint interpolation | `lem:polar-interpolation` | [PolarConstruction](PolarConstruction.lean): `DFPWolfe.V21.polarInterpolation` |
| Lemma 7: degeneration of general planar secant sequences | `lem:planar-degeneration` | [SecantDegeneration](SecantDegeneration.lean): `DFPWolfe.V21.planarDegeneration` |
| Proposition 8: the independent center-manifold recurrence | `cm-center-proposition` | [CenterManifold](CenterManifold.lean): `DFPWolfe.V21.CenterManifold.centerProposition` |
| Section 6.3: cancellation, limiting scales and the full circle | `cm-center-cancellation`, `cm-limiting-scales` | [CenterManifold](CenterManifold.lean): `DFPWolfe.V21.CenterManifold.centerManifoldAsymptotics` |
| Section 6.3: conditional interpolation of the actual trajectory | `cm-limiting-scales` | [CenterInterpolation](CenterInterpolation.lean): `DFPWolfe.V21.CenterInterpolation.centerManifoldConditionalInterpolation` |
| Sequence comparisons and polar degeneration rates on the same Wolfe witness | `sec:known-results`, `eq:planar-scalar-definition` | [SequenceProperties](SequenceProperties.lean): `DFPWolfe.V21.planarCounterexampleFamilyWithSequenceProperties` |

Theorem 1 uses the original polar data throughout. Its proved properties include
gradient norms tending exactly to one, globally half-Hölder Hessian continuity,
failure of every larger Hölder exponent on the initial level set, arbitrarily
small Hessian deviation from identity, the unique origin minimizer, and the full
unit-circle accumulation set in an embedded plane. The source identities retain
the actual objective, points, step lengths, gradients and inverse Hessians.
`not_globalWeakWolfeConvergenceAt` and `not_levelSetGlobalWeakWolfeConvergenceAt`
state the negative answer using this new witness.

Corollary 2 applies the positive square root of the initial matrix, retaining the
same Wolfe parameters and step lengths. Its conclusion is a positive gradient
liminf; the transformation gives example-dependent Hessian bounds. The quantitative
entry proves the precise planar constants `λmin(H₀)/2`, `3λmax(H₀)/2`, and
`liminf ‖g̃ₖ‖ ≥ √λmin(H₀)` for the same normalized iteration. The identity-block
extension retains the stated minimum and maximum with one. Theorem 3
covers an arbitrary initial positive definite matrix, the full weak Wolfe range,
stationary termination represented by constant continuation, and infinite-orbit
convergence. Strong Wolfe and C³ consequences are also exported. Lemma 7 assumes
the previous secant equation and positive definite search matrices, without a
DFP update or Hessian Lipschitz assumption.

Proposition 8 uses the actual zero-start graph-transform iterates, uniform C⁸
derivative bounds and Arzelà–Ascoli to construct the C⁷ graph. Its literal initial
data generate the infinite positive definite recurrence and the stated inverse
cubic scale asymptotic. Section 6.3 retains the source cancellation and positive
product arguments, with the full quadratic amplitude remainder, cubic center
tails, positive gradient limit and exact circle cluster set. Its conditional
interpolation entry uses that same graph, trajectory and limits, retaining the
source's positive radii, eventual quadratic radius orders and disjoint open balls.
It proves C² regularity, globally half-Hölder Hessians, exact endpoint jets and the
eventual per-bump derivative bounds for the full original cutoff sum. Finite early
bumps are restored without adding a global margin assumption. Section 6 does not
assert a complete hatted Wolfe counterexample.

The sequence comparisons are proved for the same canonical Wolfe witness as
the polar counterexample, with its source identities retained. They include
gradient-norm oscillation, divergent total step length, nonzero endpoint
directional derivatives, the original curvature and free-coefficient rates,
Xu's scalar asymptotics, and nonconvergence to any point. Parameter neighborhoods
are intersected before selecting the cycle parameter, and comparison constants
are fixed before the accuracy and later starting index. The complete-turn entry
also intersects the complete-turn neighborhood before that selection, so its
`3(D₀+D₁)/(N(N+1)) + O(N⁻³)` distance estimate holds on the same canonical
Wolfe witness together with all the sequence comparisons.

Core proofs are in [the polar library](../../ReasLib/Optimization/DFP/Polar/).
The main results and their public entries have passed individual Lean checks
and axiom audits using only `propext`, `Classical.choice`, and `Quot.sound`.

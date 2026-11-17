# Latest manuscript: general polar construction

Import `DFPWolfe.Latest.Paper` for `20251117-DFP/arXiv.tex` (SHA256
`2a22ecf8e12959dd584a11732ba1836319eb16dd583059c283e4513b3dbbbdca`). The
manuscript uses one shared amsthm counter, so its 13 theorem-like results are
numbered in source order: Lemmas 1–2, Proposition 3, Lemmas 4–9, Theorem 10,
Corollary 11, Lemma 12, and Theorem 13.

## Paper correspondence

| Manuscript result | LaTeX label | Navigation | Main declaration |
| --- | --- | --- | --- |
| Lemma 1 | `lem:polar-direction-update` | [direction update](Lemma_PolarDirectionUpdate.lean) | `Parameters.matrix_step` |
| Lemma 2 | `lem:polar-endpoint-wolfe` | [endpoint Wolfe](Lemma_PolarEndpointWolfe.lean) | `WolfeRatios.sourceStrongWolfe_of_phaseMargins` |
| Proposition 3 | `prop:polar-realization` | [realization](Proposition_PolarRealization.lean) | `PlanarCounterexample.existsSourceCertificate` |
| Lemma 4 | `lem:polar-limiting-cycle` | [limiting cycle](Lemma_PolarLimitingCycle.lean) | `cycleMatchingEven`, `cycleMatchingOdd` |
| Lemma 5 | `lem:polar-parameter-choice` | [parameter choice](Lemma_PolarParameterChoice.lean) | `strictWolfeBaseExists` |
| Lemma 6 | `lem:polar-cycle-estimates` | [cycle estimates](Lemma_PolarCycleEstimates.lean) | `Continuation.existsTrajectoryBounds` |
| Lemma 7 | `lem:polar-continuation` | [continuation](Lemma_4_PolarContinuation.lean) | `Continuation.existsContinuationEstimates` |
| Lemma 8 | `lem:polar-geometry` | [geometry](Lemma_5_PolarGeometry.lean) | `ActualGeometry.existsSourceGeometry` |
| Lemma 9 | `lem:polar-interpolation` | [interpolation](Lemma_6_PolarInterpolation.lean) | `Objective.existsSourceObjectiveData` |
| Theorem 10 | `thm:main` | [main theorem](Theorem_1_StrongWolfeCounterexample.lean) | `Latest.main` |
| Corollary 11 | `cor:identity-initialization` | [identity initialization](Corollary_2_IdentityInitialization.lean) | `Latest.identityInitialization` |
| Lemma 12 | `lem:planar-degeneration` | [secant degeneration](Lemma_7_PlanarSecantDegeneration.lean) | `Latest.planarDegeneration` |
| Theorem 13 | `thm:planar-convergence` | [planar convergence](Theorem_3_PlanarConvergence.lean) | `Latest.planarConvergenceCases` |

The six construction interfaces are included in the same shared counter; they
are not unnumbered. `Sequences.lean` retains the same actual Wolfe witness for
the manuscript's later sequence comparisons. The earlier center-manifold route
and the October 2026 fixed-exponent polar route remain available through
`DFPWolfe.Paper` and `DFPWolfe.V21.Paper`.

The current audit manifest contains 32 declarations. The source tree contains
no proof placeholders or custom axioms; audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

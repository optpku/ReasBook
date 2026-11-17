# Latest manuscript: correctness and correspondence review

Reviewed manuscript: `20251117-DFP/arXiv.tex`, SHA256
`2a22ecf8e12959dd584a11732ba1836319eb16dd583059c283e4513b3dbbbdca`.
The four amsthm environments share one counter. Therefore the frontend and
Lean navigation must use Lemmas 1–2, Proposition 3, Lemmas 4–9, Theorem 10,
Corollary 11, Lemma 12, and Theorem 13.

| Manuscript result | Lean declaration | Verification scope |
| --- | --- | --- |
| Lemma 1 | `Parameters.matrix_step` | Exact polar matrix-step identity. |
| Lemma 2 | `WolfeRatios.sourceStrongWolfe_of_phaseMargins` | Endpoint Wolfe inequalities for both phases. |
| Proposition 3 | `PlanarCounterexample.existsSourceCertificate` | Realization of the prescribed orbit as a DFP certificate. |
| Lemma 4 | `cycleMatchingEven`, `cycleMatchingOdd` | Limiting two-cycle matching. |
| Lemma 5 | `strictWolfeBaseExists` | Admissible parameter selection. |
| Lemma 6 | `Continuation.existsTrajectoryBounds` | Fast and slow cycle estimates. |
| Lemma 7 | `Continuation.existsContinuationEstimates` | Infinite continuation and feasibility. |
| Lemma 8 | `ActualGeometry.existsSourceGeometry` | Separation, radii, steps and cluster geometry. |
| Lemma 9 | `Objective.existsSourceObjectiveData` | Explicit cutoff interpolation and Hölder bounds. |
| Theorem 10 | `Latest.main` | General strong-Wolfe counterexample for every admissible pair, exponent and dimension. |
| Corollary 11 | `Latest.identityInitialization` | Identity initialization after planar square-root normalization and extension. |
| Lemma 12 | `Latest.planarDegeneration` | General planar secant degeneration under weak Wolfe hypotheses. |
| Theorem 13 | `Latest.planarConvergenceCases` | Planar convergence or finite stationary termination with locally Lipschitz Hessian. |

`Sequences.lean` packages the unnumbered comparisons after the numbered
results on the same actual witness: gradient oscillation, nonsummable step
lengths, Xu phase comparison, endpoint derivatives, curvature and determinant
limits, and the free-coefficient asymptotics.

The older center-manifold section is historical and remains exported by
`DFPWolfe.Paper` and `DFPWolfe.V21.Paper`; it is not part of this latest entry.

# The multiplier step size in classical two-block ADMM: convergence and counterexamples

This catalog folder links to the Lean formalization on the `v4.32.0` version
branch. The source update follows the revised 2026 manuscript.

- **Paper authors:** Benqi Liu, Qiming Dai, and Zaiwen Wen
- **Year:** 2026
- **Formalization contributor:** Qiming Dai ([@newbiedqm](https://github.com/newbiedqm))
- **Project ID:** `glowinski_admm_counterexample`
- **Lean/mathlib:** `v4.32.0` (`leanprover/lean4:v4.32.0`)
- **License:** Apache License, Version 2.0
- **Paper:** [arXiv:2611.09169](https://arxiv.org/abs/2611.09169) (`math.OC`, v1, 2026)

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#papers).
The paper authors listed above are bibliographic authors; per-file Lean code
authorship is recorded separately in the version-branch source headers.

**[Open the source on `v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/)**

[Paper.lean](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/Paper.lean) ·
[Source README](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/README.md)

## Coverage

The updated formalization covers all twelve numbered mathematical results of
the revised manuscript: Theorems 2.1 and 2.2, Corollary 2.3, Lemmas 3.1, 3.2,
4.1, 5.1, 5.2, and C.1, and Propositions 4.2, 4.3, and 5.3. It also verifies
the supporting certificates in Appendices A and B and both refined endpoint
certificates in Appendices C.2 and C.3.

For finite-dimensional problems with closed proper convex objectives and a
KKT triple, the strengthened convergence theorem applies to every well-defined
exact two-block ADMM trajectory with arbitrary initial state and positive penalty,
for `0 < gamma <= L`, where `L = 1.886882470025`. Its conclusions include the
separate constraint-image limits, vanishing residuals and second-block image
increments, optimal objective values, and convergence of the multiplier to an
optimal multiplier. Injectivity of both constraint maps additionally gives
primal-dual KKT convergence.

The unit-circle convergence criterion and exact rational certificates prove
`L < Gamma* < U`, with `U = 1.886882643762680` and
`U - L = 1.7373768e-7`. The retained counterexamples include fixed-polytope
periodic orbits, strictification, smooth strongly convex realization, and finite
convex piecewise-quadratic objectives with periodic or geometrically growing
trajectories. The upper endpoint uses the additional 1024-phase construction.

The exact value of `Gamma*` and convergence at `gamma = Gamma*` remain open in
the manuscript. Bibliographic discussion and presentation material are outside
the formal theorem assertions. The manuscript PDF, TeX, and bibliography are
kept outside this source contribution.

## Source statistics and validation

The [version-branch source README](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/glowinski_admm_counterexample/README.md)
records the updated source statistics, exact validation commands, declaration
counts, and proof completion. The updated source contains proved interfaces
for all twelve numbered results and the two unnumbered endpoint certificates.
The original JSON interfaces remain available as compatibility entry points;
they include overlapping items and definitions and are not distinct theorem
counts. The local integration build checked 1,434 Lean files; its axiom audit
covered 65,285 compiled project declarations, with no proof placeholders or
project-defined axioms.

## Published reading resources

[Docs](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/glowinski_admm_counterexample/Paper.html) ·
[Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/glowinski_admm_counterexample/paper/) ·
[Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/glowinski_admm_counterexample/) ·
[Reviewer](https://reasbook.reaslab.io/review/books/glowinski_admm_counterexample/)

These published resources describe the earlier merged source, including its
11 numbered manuscript results. Documentation for the revised twelve-result
source is pending a maintainer release after the source update is merged. The
existing resource links are retained for reading the earlier formalization;
they do not claim that the strengthened results are already published there.

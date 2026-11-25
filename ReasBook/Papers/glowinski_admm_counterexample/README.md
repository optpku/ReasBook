# The multiplier step size in classical two-block ADMM: convergence and counterexamples

- **Paper authors:** Benqi Liu, Qiming Dai, and Zaiwen Wen.
- **Year:** 2026.
- **Paper:** [arXiv:2611.09169](https://arxiv.org/abs/2611.09169).
- **Lean contributor:** Qiming Dai ([@newbiedqm](https://github.com/newbiedqm)).
- **Project ID:** `glowinski_admm_counterexample`.
- **Branch/toolchain:** `v4.32.0` / `leanprover/lean4:v4.32.0`.
- **Mathlib:** `v4.32.0`, pinned by the repository's `lake-manifest.json`.

## Coverage

The updated development proves all twelve numbered results of the manuscript
and the supporting certificate obligations in Appendices A, B, C.2 and C.3.
The main convergence theorem covers every finite-dimensional closed proper
convex problem with a KKT triple, every positive penalty, and every well-defined
exact trajectory with arbitrary initialization and minimizer choices, for
`0 < gamma <= L`. It includes separate constraint-image limits, residual and
objective limits, an optimal multiplier limit, and full primal-dual KKT
convergence when both matrix maps are injective.

Here `L = 1.886882470025` and `U = 1.886882643762680`. The strict enclosure
`L < Gamma* < U` and exact width `U - L = 1.7373768e-7` are proved. The
unit-circle criterion uses the actual 256-lag rational certificate, including
strict continuation at the same positive margin. The upper bound uses the
actual 1024-phase Fourier counterexample and its strict supports.

| Paper result | Content | Lean entry |
| --- | --- | --- |
| 2.1 | Convergence for the full updated factor range | [GlowinskiADMM/UpdatedResults.lean](GlowinskiADMM/UpdatedResults.lean) |
| 2.2 | Periodic and geometrically growing counterexamples | [GlowinskiADMM/theorem_2_1_4.lean](GlowinskiADMM/theorem_2_1_4.lean) |
| 2.3 | Strict uniform convergence endpoint bounds | [GlowinskiADMM/UpdatedResults.lean](GlowinskiADMM/UpdatedResults.lean) |
| 3.1 | Reduction to constraint images | [GlowinskiADMM/lemma_3_1_2.lean](GlowinskiADMM/lemma_3_1_2.lean) |
| 3.2 | Finite-memory interval certificate | [GlowinskiADMM/lemma_3_2_reduced.lean](GlowinskiADMM/lemma_3_2_reduced.lean) |
| 4.1 | Projection cycles | [GlowinskiADMM/lemma_4_1_2.lean](GlowinskiADMM/lemma_4_1_2.lean) |
| 4.2 | Cyclic reduction | [GlowinskiADMM/proposition_4_1_3.lean](GlowinskiADMM/proposition_4_1_3.lean) |
| 4.3 | A fixed pair of polytopes | [GlowinskiADMM/proposition_4_1_6.lean](GlowinskiADMM/proposition_4_1_6.lean) |
| 5.1 | Strictification in both blocks | [GlowinskiADMM/lemma_5_1_1.lean](GlowinskiADMM/lemma_5_1_1.lean) |
| 5.2 | Smooth strongly convex realization | [GlowinskiADMM/lemma_5_1_4.lean](GlowinskiADMM/lemma_5_1_4.lean) |
| 5.3 | Piecewise-quadratic realization and growth | [GlowinskiADMM/finite_objectives_and_growth.lean](GlowinskiADMM/finite_objectives_and_growth.lean) |
| C.1 | Convergence from the unit-circle criterion | [GlowinskiADMM/UnitCircleConvergence.lean](GlowinskiADMM/UnitCircleConvergence.lean) |

Appendix C.2 is `ADMM.UpdatedTargets.lowerCircleCertificate` in
[RefinedLowerCertificate.lean](GlowinskiADMM/RefinedLowerCertificate.lean).
Appendix C.3 is `ADMM.UpdatedTargets.refinedUpperBound` in
[UpdatedAssembly.lean](GlowinskiADMM/UpdatedAssembly.lean).
The original period-48 counterexamples, strictification, smooth strongly convex
realization, and piecewise-quadratic growth results are retained.

The exact value of `Gamma*` and convergence at that exact endpoint remain open
in the paper. Bibliographic discussion and external software performance claims
are outside the formal theorem statements. Manuscript PDF/TeX files are not
included; the arXiv link provides the paper.

## Entry points and layout

[Paper.lean](Paper.lean) imports the complete updated public surface.
[UpdatedResults.lean](GlowinskiADMM/UpdatedResults.lean) contains unconditional
`mainConvergence`, `refinedLowerBound`, and `endpointBounds`.
[UpdatedTargets.lean](GlowinskiADMM/UpdatedTargets.lean) defines their full
propositions; the implementations supply actual closed proofs.
[lemma_3_2_reduced.lean](GlowinskiADMM/lemma_3_2_reduced.lean) supplies the direct
arbitrary reduced-trajectory interface for Lemma 3.2.

All module paths are project-prefixed, for example
`glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence`, so they
coexist with DFP's separate `ReasLib` module root. Mathematical declaration
names remain in the `ADMM` and `ConsensusADMM` namespaces. Relocation preserves the public
theorem statements, exact numeric data, and existing author/license notices.
Six start-endpoint coefficient checks reuse the already certified Chebyshev
cache, preserving the original equalities while reducing compilation cost.

Qiming Dai ([@newbiedqm](https://github.com/newbiedqm)) confirmed Lean
code authorship for all 938 files added in this update. The 496 existing
author notices are preserved from the maintainer-reviewed
[PR #100](https://github.com/optpku/ReasBook/pull/100). Exact certificate inputs originate from
[bqliu815/ADMM-Multiplier-Step-Size](https://github.com/bqliu815/ADMM-Multiplier-Step-Size/tree/dbc85ba3e257a389e95106c2b3c50431ce1ef9d1),
commit `dbc85ba3e257a389e95106c2b3c50431ce1ef9d1`. These rational data are
explicit Lean definitions with kernel-checked source and positivity identities.

## Statistics and proof status

- **Lean source:** 1,434 `.lean` files, 208,720 physical lines,
  174,487 nonblank lines, including `Paper.lean`.
- **Source declaration heads:** 56,670; theorem/lemma heads: 42,535; other heads: 14,135.
- **Numbered manuscript results:** 12 / 12; Appendices C.2/C.3: 2 / 2.
- **Remaining placeholders:** `sorry`: 0; `admit`: 0.
- **Project-defined axioms:** 0.

Declaration counts are source-level heads after removing nested comments and
string literals. They exclude imported Mathlib and compiler-generated auxiliary
declarations; numeric certificate helpers are included. Source counts and
manuscript-result counts measure different things.

## Build and validation

From the repository's Lean project directory:

```bash
cd ReasBook
lake build glowinski_admm_counterexample
lake env lean Papers/glowinski_admm_counterexample/Paper.lean
```

The author-header checker from current `main` checked all 1,434 files with zero
invalid headers. The dedicated library build and direct `Paper.lean` check passed.
Six exact claim types were checked as closed theorems, and a transitive
axiom audit covered 65,285 compiled project declarations. Its only dependencies
are `propext`, `Classical.choice`, and `Quot.sound`. The check is scoped to
this paper library.

## Reading resources

[Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/glowinski_admm_counterexample/Paper.html) |
[Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/glowinski_admm_counterexample/paper/) |
[Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/glowinski_admm_counterexample/) |
[arXiv](https://arxiv.org/abs/2611.09169)

The published reading resources currently describe the earlier source release.
Updated API documentation, Verso pages, and the theorem map are regenerated
for this source change and require a new verified release before the published
links describe this revision. Source and catalog changes are prepared on
separate version and main branches.

The [numbered theorem map data](theorem-map/data.json) groups the actual
compiled declarations into 14 manuscript nodes, including
Appendices C.2/C.3, with 20 dependencies. Its
[witness paths](theorem-map/edge-witnesses.json) preserve the compiled
statement/proof dependency evidence. API Docs and Verso were regenerated
locally for 1,418 reachable modules and
18 selected reading modules, respectively.

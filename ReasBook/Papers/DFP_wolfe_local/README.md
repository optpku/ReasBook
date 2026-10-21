# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

[Reviewer: deployed center-manifold snapshot](https://reasbook.reaslab.io/review/books/dfp_wolfe_local/)

This is a catalog link folder on `main`. The `v4.32.0` source preserves two
complete proof routes: the original center-manifold construction and the v21
prescribed polar construction.

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1); the polar proof follows the October 9, 2026 v21 submission.
- **Contributor:** Zichen Wang ([@imathwy](https://github.com/imathwy))
- **License:** Apache License, Version 2.0

**[Open the source on `v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/)**

[API documentation](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/docs/) ·
[Verso reading pages](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/pages/) ·
[Original dependency map](https://optpku.github.io/ReasBook/theorem-maps/papers/dfp_wolfe_local/) ·
[v21 dependency map](https://optpku.github.io/ReasBook/theorem-maps/papers/dfp_wolfe_local/v21/)

## Proof versions

| Version | Source | Coverage |
| --- | --- | --- |
| Original center-manifold construction | [Original entry](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe/Paper.lean) | Complete counterexample, identity initialization, sharp Hölder regularity and planar convergence. |
| October 9, 2026 v21 polar construction | [v21 entry](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe/V21/Paper.lean) · [Correspondence](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe/V21/) | Complete numbered results 1–8, quantitative identity initialization, same-witness sequence comparisons and complete-turn geometry. |

The v21 counterexample retains the source polar recurrence and explicit cutoff
interpolation. Its independent Proposition 8 follows graph-transform iterate
bounds and Arzelà–Ascoli. The separate Section 6 interpolation retains the
manuscript's disjoint-open-ball premise and eventual support-radius orders;
it does not assert a hatted Wolfe counterexample.

The [v21 graph source](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/theorem-map/v21/)
has an eight-node paper-numbered view and a detailed compiled-declaration view.
Numbered nodes quote the exact manuscript statement above the corresponding
Lean code; all projected edges retain compiled witness paths and immutable
GitHub source links. The original proof's graph and quoted statements remain
available separately.

The combined source has 502 Lean files, 144,521 physical lines and 5,550
declaration heads, with no `sorry`, `admit` or custom axioms. The final v21 audit
checked 182 kernel axiom reports using only `propext`, `Classical.choice` and
`Quot.sound`. Comparator has not been rerun for this route.

The Docs source plan covers 498 reachable modules. The 21-route Verso manifest
preserves all original reading URLs and adds the complete v21 results. Docs,
Verso and both dependency maps are published in
[site-20261020T152000Z-64fdfbc54b6b](https://github.com/optpku/ReasBook/releases/tag/reasbook-site-20261020T152000Z-64fdfbc54b6b).
Both maps provide paper-numbered and Lean-declaration views. The published
resources use the immutable source snapshot
[`5f2648b6`](https://github.com/optpku/ReasBook/commit/5f2648b67408c025ff266d7263a3693e67ce4435).

# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

**Published reading (v4.32.0):** [Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/papers/dfp_wolfe_local/) · [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/DFP_wolfe_local/Paper.html) · [Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/dfp_wolfe_local/)

**Project-level formalization contributors:** Zichen Wang.

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#papers); it is separate from the original reference authors and per-file Lean authorship.

[Center-manifold statements](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/DFPWolfe/Paper.html) · [v21 statements](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/DFPWolfe/V21/Paper.html) · [v21 theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/dfp_wolfe_local/v21/?view=paper)

[Reviewer: deployed center-manifold snapshot](https://reasbook.reaslab.io/review/books/dfp_wolfe_local/)

This is a catalog link folder on `main`. The `v4.32.0` source preserves two
complete proof routes: the original center-manifold construction and the v21
prescribed polar construction.

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1); the polar proof follows the October 9, 2026 v21 submission.
- **Contributor:** Zichen Wang ([@imathwy](https://github.com/imathwy))
- **License:** Apache License, Version 2.0

**[Open the source on `v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/)**

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
[site-20261105T034713Z-fe8615a941bf](https://github.com/optpku/ReasBook/releases/tag/reasbook-site-20261105T034713Z-fe8615a941bf).
Both maps provide paper-numbered and Lean-declaration views. The published
resources use the immutable source snapshot
[`dac77d53`](https://github.com/optpku/ReasBook/commit/dac77d532d2d28352c5a2af2f9a3a3a1256be1a6).

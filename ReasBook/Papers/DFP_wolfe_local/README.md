# A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions

This is a catalog link folder on `main`. The `v4.32.0` source preserves the
completed center-manifold proof and the separate v21 polar foundations.

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Paper:** [arXiv HTML](https://arxiv.org/html/2608.21708v1)
- **Contributor:** Zichen Wang ([@imathwy](https://github.com/imathwy))
- **License:** Apache License, Version 2.0

**[Open the source on `v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/)**

[API documentation](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/docs/) ·
[Verso reading pages](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/pages/) ·
[Theorem dependency map](https://optpku.github.io/ReasBook/theorem-maps/papers/dfp_wolfe_local/)

The API documentation covers both proof versions. The guide presents the main
results and eleven source-backed reading sections, including planar convergence, sharp Hölder regularity, and
general secant degeneration. The dependency map offers paper-numbered and Lean
declaration views. Each numbered result displays the original paper statement
above its corresponding Lean declarations and proofs, with links to their
source locations. The three additional reading sections cover the v21 polar foundations.

## Proof versions

| Version | Source | Coverage |
| --- | --- | --- |
| Center-manifold construction | [Original entry](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe.lean) | Complete counterexample, identity initialization, sharp Hölder regularity and planar convergence. |
| October 9, 2026 v21 polar construction | [Independent entry](https://github.com/optpku/ReasBook/blob/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe/V21.lean) · [Correspondence](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/DFPWolfe/V21/) | Verified polar recurrence, normalized-map regularity and limiting two-cycle. The full v21 counterexample proof remains in progress. |

PR [#71](https://github.com/optpku/ReasBook/pull/71) added the v21 foundations while
retaining the original proof. The [v21 graph source](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/theorem-map/v21/)
contains 154 compiled public theorems/lemmas and 321 dependency edges, with a
three-node source-section overview and corresponding Lean code.

The combined Docs closure contains 460 modules. The 11 Verso reading routes
retain the original eight sections and add three independent v21 sections.
The [v21 dependency map](https://optpku.github.io/ReasBook/theorem-maps/papers/dfp_wolfe_local/v21/)
provides a separate view of the polar foundations; the original map continues
to describe the completed center-manifold proof.

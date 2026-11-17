# DFP Wolfe formalization

**Published reading (v4.32.0):** [Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/papers/dfp_wolfe_local/) · [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/DFP_wolfe_local/Paper.html) · [Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/dfp_wolfe_local/)

This ReasBook entry preserves three source routes under the same Lean project:
the original center-manifold construction, the October 2026 fixed-exponent v21
snapshot, and the current `20251117-DFP/arXiv.tex` general polar construction.

| Route | Entry | Paper-facing resource |
| --- | --- | --- |
| Original center-manifold | [`DFPWolfe.Paper`](DFPWolfe/Paper.lean) | [Original theorem map](theorem-map/index.html?view=paper) |
| October 2026 v21 snapshot | [`DFPWolfe.V21.Paper`](DFPWolfe/V21/Paper.lean) | [Historical v21 map](theorem-map/v21/index.html?view=paper) |
| 20251117 latest polar proof | [`DFPWolfe.Latest.Paper`](DFPWolfe/Latest/Paper.lean) | [Latest theorem DAG](theorem-map/latest/index.html?view=paper) |

The latest manuscript uses the shared amsthm counter in source order. Its
paper-numbered results are:

- Lemmas 1–2: polar direction update and endpoint Wolfe ratios;
- Proposition 3: polar DFP realization;
- Lemmas 4–9: limiting cycle, parameter choice, cycle estimates, continuation,
  geometry, and interpolation;
- Theorem 10: the general strong-Wolfe counterexample;
- Corollary 11: identity initialization;
- Lemma 12: planar secant degeneration;
- Theorem 13: planar convergence.

The latest DAG has 13 nodes and 15 reviewed paper-order edges. It is generated
from manuscript SHA256
`2a22ecf8e12959dd584a11732ba1836319eb16dd583059c283e4513b3dbbbdca`; its Lean
source links use immutable source commit
[`97fe7b8f`](https://github.com/imathwy/DFP_wolfe_local/commit/97fe7b8f1a2fa524f9ce5588a4190603db93946c).
The original and October 2026 v21 maps remain unchanged.

- **Authors:** Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan
- **Contributor:** Zichen Wang ([@imathwy](https://github.com/imathwy))
- **License:** Apache License, Version 2.0

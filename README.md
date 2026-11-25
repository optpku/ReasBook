# ReasBook — Lean/mathlib v4.32.0

**Toolchain:** `leanprover/lean4:v4.32.0`
**Mathlib:** `v4.32.0`

[Published reading catalog](https://optpku.github.io/ReasBook/) · [Cross-version source catalog](https://github.com/optpku/ReasBook/) · [Reading and review](https://reasbook.reaslab.io/review/)

This branch contains 1 book projects and 3 paper projects using Lean/mathlib `v4.32.0`. The reading links below refer to the [published site snapshot](https://github.com/optpku/ReasBook/releases/tag/reasbook-site-20261105T034713Z-fe8615a941bf); their versions are shown explicitly. Source links stay on this branch.

## Books

| Project and reference | Formalization contributors | Published reading |
| --- | --- | --- |
| **[Computational Methods for Inverse Problems](./ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/)**<br><sub>Curtis R. Vogel (2002)</sub> | Yifan Bai, Wanli Ma, Zichen Wang | Source only; not included in the published site. |

## Papers

| Project and reference | Formalization contributors | Published reading |
| --- | --- | --- |
| **[A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions](./ReasBook/Papers/DFP_wolfe_local/)**<br><sub>Benqi Liu, Zichen Wang, Zaiwen Wen, Liwei Zhang, and Yaxiang Yuan</sub> | Zichen Wang | `v4.32.0`<br>[Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/papers/dfp_wolfe_local/) &#124; [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/DFP_wolfe_local/Paper.html) &#124; [Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/dfp_wolfe_local/) |
| **[Technical note: a counterexample to the Rockafellar sum conjecture on c₀](./ReasBook/Papers/RockafellarSum_2026/)**<br><sub>Junyu Zhang, Jinbiao Chen, Zichen Wang, Benqi Liu, and Zaiwen Wen (2026)</sub> | Zichen Wang | `v4.32.0`<br>[Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/papers/rockafellarsum_2026/) &#124; [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/RockafellarSum_2026/Paper.html) |
| **[The multiplier step size of two-block ADMM: convergence and counterexamples](./ReasBook/Papers/glowinski_admm_counterexample/)**<br><sub>2026</sub> | Qiming Dai | `v4.32.0`<br>[Verso](https://optpku.github.io/ReasBook/versions/v4.32.0/papers/glowinski_admm_counterexample/) &#124; [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.0/docs/ReasBook/glowinski_admm_counterexample/Paper.html) &#124; [Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.0/theorem-maps/papers/glowinski_admm_counterexample/) |

Contributor names are project-level credits; project READMEs retain roster sources and any upstream roles. Original book and paper authors are listed separately.

## Build

Use the committed `ReasBook/lean-toolchain` and `ReasBook/lake-manifest.json` dependency pins. Follow the [build SDK guide](https://github.com/optpku/ReasBook/blob/main/sdk/build/README.md) for the corresponding version. Published documentation records its own source snapshot; its publication does not certify every historical source file or an aggregate branch build.

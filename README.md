# ReasBook — Lean/mathlib v4.30.0

**Toolchain:** `leanprover/lean4:v4.30.0`
**Mathlib:** v4.30.0
**Status:** Active
**Last build:** pending

This branch aggregates books and papers that use exactly Lean/mathlib `v4.30.0`.
Dependency locks, shared declarations, and namespaces must stay compatible within the branch.

- Manifest: [`ReasBook/lake-manifest.json`](ReasBook/lake-manifest.json)
- Aggregate entry: [`ReasBook/ReasBook.lean`](ReasBook/ReasBook.lean)

## Books

| Book | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| A Concise Course in Algebraic Topology — J. Peter May (1999) | — | [doc](https://optpku.github.io/ReasBook/docs/Books/AlgebraicTopology_May_1999/Book.html) | [source](./ReasBook/Books/AlgebraicTopology_May_1999/) | [verso](https://optpku.github.io/ReasBook/books/algebraictopology_may_1999/) |
| Analysis II — Terence Tao (4th ed., 2022) | Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang | [doc](https://optpku.github.io/ReasBook/docs/Books/Analysis2_Tao_2022/Book.html) | [source](./ReasBook/Books/Analysis2_Tao_2022/) | [verso](https://optpku.github.io/ReasBook/books/analysis2_tao_2022/) |
| Combinatorial Group Theory — Magnus, Karrass, Solitar (2004) | — | [doc](https://optpku.github.io/ReasBook/docs/Books/CombinatorialGroupTheory_Magnus_2004/Book.html) | [source](./ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | [verso](https://optpku.github.io/ReasBook/books/combinatorialgrouptheory_magnus_2004/) |
| Convex Analysis and Monotone Operator Theory in Hilbert Spaces — Bauschke, Combettes (2nd ed., 2017) | — | [doc](https://optpku.github.io/ReasBook/docs/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html) | [source](./ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | [verso](https://optpku.github.io/ReasBook/books/convexanalysismonotoneoperators_bauschkecombettes_2017/) |
| First-Order Methods in Optimization — Amir Beck (2017) | — | [doc](https://optpku.github.io/ReasBook/docs/Books/FirstOrderMethodsOptimization_Beck_2017/Book.html) | [source](./ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | [verso](https://optpku.github.io/ReasBook/books/firstordermethodsoptimization_beck_2017/) |
| Introduction to Real Analysis, Volume I — Jiri Lebl (v6.2, 2025) | Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) | [source](./ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | [verso](https://optpku.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/) |
| Optimization Theory and Methods: Nonlinear Programming — Wenyu Sun, Ya-xiang Yuan (2006) | Chenyi Li, Wanli Ma, Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Books/OptimizationTheoryAndMethods_SunYuan_2006/Book.html) | [source](./ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/) | — |
| Lectures on Riemann Surfaces — Otto Forster (1981) | — | [doc](https://optpku.github.io/ReasBook/docs/Books/RiemannSurfaces_Forster_1981/Book.html) | [source](./ReasBook/Books/RiemannSurfaces_Forster_1981/) | [verso](https://optpku.github.io/ReasBook/books/riemannsurfaces_forster_1981/) |

## Papers

| Paper | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| Smooth Minimization of Non-Smooth Functions — Yurii Nesterov (2004) | Wanli Ma, Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Paper.html) | [source](./ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | [verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/) |
| On Some Local Rings — Mohamad Maassarani (2025) | Liang Xiao, Haochen Ju, Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) | [source](./ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | [verso](https://optpku.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/) |

## Build

```bash
cd ReasBook
lake update
lake build
```

Full Lean build and web build run on the self-hosted runner; locally, `./build.sh` / `./build-web.sh`
replicate the same phases (see `scripts/`).

# ReasBook

**English** | [简体中文](README.zh-CN.md)

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks
and research papers. It preserves the structure of the original references
while producing machine-checkable statements and proofs. Browse the generated
[documentation and project catalog](https://optpku.github.io/ReasBook/) to
explore the current collection.

Many ReasBook projects are initialized with
[M2F](https://github.com/optsuite/M2F.git) and then checked and refined in
Lean. You can also try [Quokka](https://quokka.reaslab.io/), the public
automated formalization system for turning long-form mathematical literature
into compilable Lean 4 projects.

## Toolchain Branches

| Branch | Lean/mathlib | Registry status | Books/Papers |
| --- | --- | --- | ---: |
| `v4.32.0` | `v4.32.0` | Empty | 1 / 0 |
| `v4.32.2` | `v4.32.2` | Active | 0 / 1 |
| `v4.30.0` | `v4.30.0` | Active | 10 / 2 |
| `v4.26.0` | `v4.26.0` | Active | 4 / 2 |

`main` is the cross-version catalog. Source code stays on the registered
version branches; the lightweight link folders below make each entry
discoverable from this branch.

Registry status: `Empty` (not included in active releases) · `Active`
(accepting PRs and included in release planning) · `Frozen` (kept, no new
books) · `Archived` (historical only). Counts describe source directories and
therefore may be nonzero on an `Empty` branch.

## Main-branch Link Folders

Each directory in these indexes is a landing page for one book or paper. Open a
directory and follow its prominent source link to the exact version branch and
project folder.

- [Books](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/)
- [Papers](https://github.com/optpku/ReasBook/tree/main/ReasBook/Papers/)
- [Theorem dependency maps](https://optpku.github.io/ReasBook/theorem-maps/)
  (the current Pages deployment contains TR-LALM)

## Architecture

ReasBook separates versioned mathematical sources from cross-version tooling
and generated output:

| Path | Responsibility |
| --- | --- |
| `ReasBook/` | Lean sources on their matching version branches |
| `ReasBookWeb/` | Verso site shell and catalog generation |
| `apps/reasbook-reviewer/` | Public reading, source/docs/graph inspection and authenticated review comments |
| `sdk/` | Reusable build, Verso, theorem-graph, comparator, and deployment APIs |
| `scripts/` | Thin repository-specific build and Pages adapters |
| `config/` | Toolchain registry, canonical versions, release profiles, and schemas |

Generated sites, Lake artifacts, logs, and release state live outside the
checkout under the configured cache root. Git history contains source and
configuration, not generated sites. The immutable release and rollback model
is recorded in [ADR-0001](docs/decisions/0001-static-release-pipeline.md).

## Quick Start

Use the [project catalog](https://optpku.github.io/ReasBook/) or the tables
below to choose a formalization. Each entry records its exact version branch,
source directory, and available documentation. Follow the matching branch link
when you need to inspect or check the Lean source.

For local development, documentation generation, comparison, and static-site
deployment, use the focused SDK guide for the relevant capability:

| Capability | Guide |
| --- | --- |
| Lean build and reachable project documentation | [Build SDK](sdk/build/README.md) |
| Verso site and literate pages | [Verso SDK](sdk/verso/README.md) · [upstream Verso](https://github.com/leanprover/verso) |
| Theorem dependency maps | [Theorem graph SDK](sdk/theorem_graph/README.md) |
| Challenge/Solution comparison | [Comparator SDK](sdk/comparator/README.md) · [upstream Comparator](https://github.com/leanprover/comparator) |
| Multi-stage deployment and release assembly | [Deploy SDK](sdk/deploy/README.md) |

See the relevant SDK guide for operational commands. The homepage focuses on
the project catalog.

## Run the reading and review platform

[ReasBook Reviewer](apps/reasbook-reviewer/README.md) is part of this repository.
It serves books and papers from the existing SDK cache and supports signed-in
review comments. From the repository root, with Python 3.11+:

```bash
python3.11 -m venv apps/reasbook-reviewer/.venv
apps/reasbook-reviewer/.venv/bin/python -m pip install -r apps/reasbook-reviewer/requirements.txt
export REASBOOK_CACHE_ROOT=/srv/reasbook-cache
apps/reasbook-reviewer/start_server.sh
```

Point `REASBOOK_CACHE_ROOT` at the cache you already built; no Lean compilation
runs at server startup. Open <http://127.0.0.1:8876/ReasBook/>. An empty cache
shows pending indexes; sign-in is optional for reading and required for posting.
The [deployment guide](apps/reasbook-reviewer/README.md#container-deployment)
covers Docker Compose, persistent comment storage and ReasLab authentication.
GitHub Pages remains the static publication target; public comments require the
reviewer backend.

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Great Bay University
- Huawei
- iQuest Research
- Sino-Russian Mathematics Center
- National Natural Science Foundation of China

## Books

Titles open their catalog pages; version links open the Lean source directly.

| Formalization | Source | Contributors | Resources |
| --- | :---: | --- | --- |
| **[A Concise Course in Algebraic Topology](ReasBook/Books/AlgebraicTopology_May_1999/)**<br><sub>J. Peter May (1999)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | Ze Yuan, Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/AlgebraicTopology_May_1999/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/algebraictopology_may_1999/pages/) |
| **[Analysis II](ReasBook/Books/Analysis2_Tao_2022/)**<br><sub>Terence Tao (4th ed., 2022)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | <details><summary>9 contributors</summary><sub>Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/analysis2_tao_2022/pages/) |
| **[Combinatorial Group Theory](ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/)**<br><sub>Magnus, Karrass, and Solitar (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/combinatorialgrouptheory_magnus_2004/pages/) |
| **[Convex Analysis](ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)**<br><sub>R. Tyrrell Rockafellar (1970)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | <details><summary>21 contributors</summary><sub>Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/convexanalysis_rockafellar_1970/pages/) |
| **[Convex Analysis and Monotone Operator Theory in Hilbert Spaces](ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/)**<br><sub>Bauschke and Combettes (2nd ed., 2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | Yifan Bai, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/convexanalysismonotoneoperators_bauschkecombettes_2017/pages/) |
| **[First-Order Methods in Optimization](ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/)**<br><sub>Amir Beck (2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | Shu Miao, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/firstordermethodsoptimization_beck_2017/pages/) |
| **[Integer Programming](ReasBook/Books/IntegerProgramming_Conforti_2014/)**<br><sub>Conforti, Cornuejols, and Zambelli (2014)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | <details><summary>38 contributors</summary><sub>Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html) &#124; Verso not published |
| **[Introduction to Real Analysis, Volume I](ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)**<br><sub>Jiri Lebl (v6.2, 2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/introductiontorealanalysisvolumei_jirilebl_2025/pages/) |
| **[Introductory Lectures on Convex Optimization](ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/) | Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/introductorylecturesonconvexoptimization_nesterov_2004/pages/) |
| **[Optimization Theory and Methods: Nonlinear Programming](ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/)**<br><sub>Wenyu Sun and Ya-xiang Yuan (2006)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/) | Chenyi Li, Wanli Ma, Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/optimizationtheoryandmethods_sunyuan_2006/pages/) |
| **[Probability Theory: A Comprehensive Course](ReasBook/Books/ProbabilityTheory_Klenke_2020/)**<br><sub>Achim Klenke (3rd ed., 2020)</sub> | [`v4.29.0`](https://github.com/optpku/ReasBook/tree/v4.29.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | Xuanzhi Ren, Zichen Wang | Source only (excluded from the current release profile) |
| **[Lectures on Riemann Surfaces](ReasBook/Books/RiemannSurfaces_Forster_1981/)**<br><sub>Otto Forster (1981)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/RiemannSurfaces_Forster_1981/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/riemannsurfaces_forster_1981/pages/) |
| **[Computational Methods for Inverse Problems](ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/)**<br><sub>Curtis R. Vogel (2002)</sub> | Not assigned to an active release branch | Yifan Bai, Wanli Ma, Zichen Wang | Source only (excluded from the current release profile) |

## Papers

Titles open their catalog pages; version links open the Lean source directly.

| Formalization | Source | Contributors | Resources |
| --- | :---: | --- | --- |
| **[A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates](ReasBook/Papers/TR_LALM_theory/)**<br><sub>Benqi Liu, Kangkang Deng, Zichen Wang, and Zaiwen Wen</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/TR_LALM_theory/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/tr_lalm_theory/pages/) &#124; [Theorem map](https://optpku.github.io/ReasBook/theorem-maps/papers/tr_lalm_theory/) |
| **[Smooth Minimization of Non-Smooth Functions](ReasBook/Papers/SmoothMinimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | Wanli Ma, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/smoothminimization_nesterov_2004/pages/) |
| **[On Some Local Rings](ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)**<br><sub>Mohamad Maassarani (2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/onsomelocalrings_maassaran_2025/pages/) |

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for the human-facing contribution
procedure. Agent-assisted contributions can follow the
[ReasBook contributing skill](CONTRIBUTING/SKILL.md), which encodes the branch,
metadata, validation, and pull-request rules.

- Book and paper code lives on the registered version branch matching its Lean/mathlib toolchain; only registered stable `vX.Y.Z` versions are accepted.
- **Book and paper code is not merged to `main`.** `main` remains the cross-version catalog, while its link folders point to the corresponding version branches.
- PR base, PR title version, `ReasBook/lean-toolchain`, and book metadata (when applicable) must all match.

## Lean Projects

<table>
<thead>
<tr>
<th scope="col">Category</th>
<th scope="col">Project</th>
<th scope="col">Description</th>
</tr>
</thead>
<tbody>
<tr>
<td scope="rowgroup">Formalization platform</td>
<td><a href="https://reaslab.io">ReasLab</a></td>
<td>An online Lean formalization platform for collaborative theorem development and verification.</td>
</tr>
<tr>
<td rowspan="2" scope="rowgroup">Formalization project</td>
<td><a href="https://github.com/optsuite/optlib">Optlib</a></td>
<td>A Lean4 library for mathematical optimization, covering convex analysis, optimality conditions, and algorithm convergence.</td>
</tr>
<tr>
<td><a href="https://github.com/optpku/ReasBook">ReasBook</a></td>
<td>A Lean4 project for textbook and paper formalization, including both theorem proving and computational problems.</td>
</tr>
<tr>
<td rowspan="2" scope="rowgroup">Benchmark</td>
<td><a href="https://github.com/optsuite/AMBER">AMBER</a></td>
<td>A Lean4 benchmark for construction and verification in applied mathematics formalization, covering both theorem-proving and computational problems.</td>
</tr>
<tr>
<td><a href="https://github.com/optpku/CAM-Bench">CAM-Bench</a></td>
<td>A Lean4 benchmark for formal theorem proving in computational and applied mathematics.</td>
</tr>
<tr>
<td rowspan="3" scope="rowgroup">Autoformalization and theorem proving</td>
<td><a href="https://github.com/optsuite/M2F">M2F</a></td>
<td>A toolkit for converting natural-language mathematical textbooks into formalization-ready Lean projects.</td>
</tr>
<tr>
<td><a href="https://github.com/chenyili0818/SITA">SITA</a></td>
<td>A structure-to-instance autoformalization framework for generating Lean definitions/theorems with verification feedback.</td>
</tr>
<tr>
<td><a href="https://github.com/optsuite/lean-tools-mcp">lean-tools-mcp</a></td>
<td>A Lean MCP server with higher parallel throughput and lower memory usage for heavy imports (especially Mathlib).</td>
</tr>
</tbody>
</table>

## Publications

### Mathematical Formalization

- Wanli Ma, Zichen Wang,  Zaiwen Wen, *A Unified Framework for Formalizing Matrix Decomposition Proofs*. [(Paper)](https://arxiv.org/abs/2607.05874)
- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automated Theorem Proving

- Wentao Long, Yunfei Zhang, Chenyi Li, Zaiwen Wen, *MECA: A Mechanism-Centered Agent for Constructing Well-Specified and Valuable Mathematical Conjectures*. [(Paper)](https://arxiv.org/abs/2607.27709)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*, ICML 2026. [(Paper)](https://arxiv.org/abs/2604.23712)
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(Paper)](https://arxiv.org/abs/2602.17016)
- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)

### Theorem-Proof Checking

- Ziyu Wang, Qiming Dai, Yishan Wu, Zaiwen Wen. *FaithSieve: Fine-Grained Evaluation of Math Proofs with Faithful Formal Evidence*.
- Ziyu Wang, Qiming Dai, Chenyi Li, Zaiwen Wen, *Beyond Formal Correctness: Structure-Aware Evaluation of Informal–Formal Proof Correspondence*

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*. [(Paper)](https://arxiv.org/abs/2602.01291)
- Wentao Long, Yunfei Zhang, Chenyi Li, Li Zhou, Chumin Sun, Zaiwen Wen. *CAM-Bench: A Benchmark for Computational and Applied Mathematics in Lean*. [(Paper)](https://arxiv.org/abs/2605.17255)

## Contributors

- Chenyi Li, School of Mathematical Sciences, Peking University, China (`lichenyi@stu.pku.edu.cn`)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, China (`wlma@pku.edu.cn`)
- Zichen Wang, School of Mathematical Sciences, Peking University, China (`zichenwang25@stu.pku.edu.cn`)
- Ziyu Wang, School of Mathematical Sciences, Peking University, China (`wangziyu-edu@stu.pku.edu.cn`)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, China (`wenzw@pku.edu.cn`)
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Yantao Li, Wentao Long, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Feiming Wang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwu Wu, Mingyue Xu, Lurong Yang, Yunfei Zhang, Jian Yu, Changyun Zou

## Citation

If you use ReasBook, please cite both the M2F paper and the repository:

M2F paper:

```bibtex
@misc{wang2026m2f,
  author        = {Zichen Wang and Wanli Ma and Zhenyu Ming and Gong Zhang and
                   Kun Yuan and Zaiwen Wen},
  title         = {{M2F}: Automated Formalization of Mathematical Literature at Scale},
  year          = {2026},
  eprint        = {2602.17016},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  doi           = {10.48550/arXiv.2602.17016},
  url           = {https://arxiv.org/abs/2602.17016}
}
```

ReasBook software:

```bibtex
@software{reasbook2026,
  author  = {{ReasBook Contributors}},
  title   = {{ReasBook}: Formalizations of Mathematical Textbooks and
             Research Papers in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/optpku/ReasBook},
  license = {Apache-2.0}
}
```

When referring to a particular formalization, also cite the original book or
paper and record the ReasBook project directory, version branch, and full
commit SHA. For example: `v4.30.0`, `ReasBook/Books/<project>/`, and the output
of `git rev-parse HEAD`. This repository also provides
[`CITATION.cff`](CITATION.cff) for citation tools and GitHub's citation
interface.

## License

ReasBook uses the [Apache License 2.0](LICENSE), matching mathlib. Unless an
individual file carries a different notice, this license covers ReasBook
content on every official branch and in all copies and forks derived from this
repository. Fork-specific additions and third-party dependencies remain subject
to their respective license notices.

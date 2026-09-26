# ReasBook

[English](README.md) | **简体中文**

**ReasBook** 是一个使用 Lean 4 对数学教材和研究论文进行形式化的项目。它在保留原始文献结构的同时，生成可由机器检查的命题与证明。你可以浏览已生成的[文档与项目目录](https://optpku.github.io/ReasBook/)，了解当前收录的形式化项目。

许多 ReasBook 项目由 [M2F](https://github.com/optsuite/M2F) 初始化，随后在 Lean 中进行检查和完善。M2F 是数学文献自动形式化的算法框架；[Quokka](https://quokka.reaslab.io/) 是 M2F 的工程实现和公开在线服务，托管于 ReasLab，通过网页提供将数学文献转化为 Lean 4 项目的功能。Quokka 的源代码将在后续开源。

## 工具链分支

| 分支 | Lean/mathlib | 注册状态 | 书籍/论文 |
| --- | --- | --- | ---: |
| `v4.32.0` | `v4.32.0` | 空 | 1 / 2 |
| `v4.32.2` | `v4.32.2` | 活跃 | 0 / 2 |
| `v4.30.0` | `v4.30.0` | 活跃 | 9 / 2 |
| `v4.26.0` | `v4.26.0` | 活跃 | 4 / 2 |

`main` 是跨版本目录。源代码保留在已注册的版本分支上；下方的轻量链接目录使每个条目都可以从 `main` 分支找到。

注册状态包括：`空`（不纳入活跃发布）、`活跃`（接受 PR 并纳入发布计划）、`冻结`（保留但不再接收新书）和 `归档`（仅保留历史记录）。数量统计的是源代码目录，因此 `空` 分支上的数量也可能不为零。

## main 分支索引目录

这些索引中的每个目录都是一本书或一篇论文的入口页。打开目录后，可以通过醒目的源代码链接进入精确的版本分支和项目目录。

- [书籍](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/)
- [论文](https://github.com/optpku/ReasBook/tree/main/ReasBook/Papers/)
- [定理依赖图](https://optpku.github.io/ReasBook/theorem-maps/)（当前 Pages 部署包含 TR-LALM）

## 架构

ReasBook 将带版本的数学源代码、跨版本工具和生成产物分开管理：

| 路径 | 职责 |
| --- | --- |
| `ReasBook/` | 位于对应版本分支上的 Lean 源代码 |
| `ReasBookWeb/` | Verso 站点外壳和目录生成 |
| `apps/reasbook-reviewer/` | 公开阅读、源码/文档/依赖图查看与登录后评论评审 |
| `sdk/` | 可复用的构建、Verso、定理图、比较器和部署 API |
| `scripts/` | 仓库专用的轻量构建与 Pages 适配器 |
| `config/` | 工具链注册表、canonical 版本、发布配置和 schema |

生成的站点、Lake 产物、日志和发布状态均位于检出目录之外的指定缓存根目录中。Git 历史只保存源代码和配置，不保存生成站点。不可变发布与回滚模型记录在 [ADR-0001](docs/decisions/0001-static-release-pipeline.md) 中。

## 快速开始

你可以使用[项目目录](https://optpku.github.io/ReasBook/)，或浏览下方表格选择一个形式化项目。每个条目都记录了精确的版本分支、源代码目录和可用文档；需要检查 Lean 源码时，请进入相匹配的版本分支。

### 使用 Git 只下载一本书

Lean 源码位于版本分支。先在下方书籍表格中找到目标书籍，并从源代码链接确认
版本分支和目录。Git 2.25 或更高版本可通过 sparse checkout 只下载该书内容，
无需取得其他书籍的文件。下面的命令以 `v4.30.0` 分支的 **Analysis II** 为例：

```bash
git clone --filter=blob:none --sparse --depth 1 --branch v4.30.0 --single-branch https://github.com/optpku/ReasBook.git ReasBook-Analysis2
cd ReasBook-Analysis2
git sparse-checkout set ReasBook/Books/Analysis2_Tao_2022
git branch --show-current
git sparse-checkout list
```

最后两条命令应分别显示 `v4.30.0` 和
`ReasBook/Books/Analysis2_Tao_2022`。之后在该克隆目录运行
`git pull --ff-only`，即可获取这个版本分支的后续提交。下载其他书籍时，请把
分支和目录替换成相应源代码链接中的准确值；路径区分大小写。下载论文的步骤
相同，只需使用对应的 `ReasBook/Papers/<目录>` 路径。

本地开发、文档生成、比较和静态站点部署请使用对应能力的 SDK 指南：

| 能力 | 指南 |
| --- | --- |
| Lean 构建与可达项目文档 | [Build SDK](sdk/build/README.md) |
| Verso 站点与 literate 页面 | [Verso SDK](sdk/verso/README.md) · [Verso 上游仓库](https://github.com/leanprover/verso) |
| 定理依赖图 | [Theorem graph SDK](sdk/theorem_graph/README.md) |
| Challenge/Solution 比较 | [Comparator SDK](sdk/comparator/README.md) · [Comparator 上游仓库](https://github.com/leanprover/comparator) |
| 多阶段部署与发布组装 | [Deploy SDK](sdk/deploy/README.md) |

各项操作命令请参阅对应能力的 SDK 指南，主页集中展示项目目录。

## 部署阅读与评审平台

[ReasBook Reviewer](apps/reasbook-reviewer/README.md) 是本仓库的一部分，复用
SDK 已生成的书籍、论文和证据缓存，并支持登录后发表评论和评审意见。
在仓库根目录使用 Python 3.11+：

```bash
python3.11 -m venv apps/reasbook-reviewer/.venv
apps/reasbook-reviewer/.venv/bin/python -m pip install -r apps/reasbook-reviewer/requirements.txt
export REASBOOK_CACHE_ROOT=/srv/reasbook-cache
apps/reasbook-reviewer/start_server.sh
```

将 `REASBOOK_CACHE_ROOT` 指向已经构建好的缓存目录即可复用产物，启动服务器不会
执行 Lean 编译。打开 <http://127.0.0.1:8876/ReasBook/>；空缓存会显示索引待生成，
阅读无需登录，发表评论需要认证。[部署指南](apps/reasbook-reviewer/README.md#container-deployment)
包含 Docker Compose、评论数据库持久化和 ReasLab 登录配置。
GitHub Pages 继续发布静态站点，公众评论需要运行 reviewer 后端。

## 赞助单位

- 北京大学北京国际数学研究中心
- 大湾区大学
- 华为
- iQuest Research
- 中俄数学中心
- 国家自然科学基金委员会

## 书籍

点击标题可打开目录页；点击版本可直接打开 Lean 源代码。

| 形式化项目 | 源代码 | 贡献者 | 资源 |
| --- | :---: | --- | --- |
| **[A Concise Course in Algebraic Topology](ReasBook/Books/AlgebraicTopology_May_1999/)**<br><sub>J. Peter May (1999)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | Ze Yuan, Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/AlgebraicTopology_May_1999/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/algebraictopology_may_1999/pages/) |
| **[Analysis II](ReasBook/Books/Analysis2_Tao_2022/)**<br><sub>Terence Tao（第 4 版，2022）</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | <details><summary>9 位贡献者</summary><sub>Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/analysis2_tao_2022/pages/) |
| **[Combinatorial Group Theory](ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/)**<br><sub>Magnus、Karrass 与 Solitar (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/combinatorialgrouptheory_magnus_2004/pages/) |
| **[Convex Analysis](ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)**<br><sub>R. Tyrrell Rockafellar (1970)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | <details><summary>21 位贡献者</summary><sub>Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/convexanalysis_rockafellar_1970/pages/) |
| **[Convex Analysis and Monotone Operator Theory in Hilbert Spaces](ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/)**<br><sub>Bauschke 与 Combettes（第 2 版，2017）</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | Yifan Bai, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/convexanalysismonotoneoperators_bauschkecombettes_2017/pages/) |
| **[First-Order Methods in Optimization](ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/)**<br><sub>Amir Beck (2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | Shu Miao, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/firstordermethodsoptimization_beck_2017/pages/) |
| **[Integer Programming](ReasBook/Books/IntegerProgramming_Conforti_2014/)**<br><sub>Conforti、Cornuejols 与 Zambelli (2014)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | <details><summary>38 位贡献者</summary><sub>Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html) &#124; 尚未发布 Verso |
| **[Introduction to Real Analysis, Volume I](ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)**<br><sub>Jiri Lebl（v6.2，2025）</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/introductiontorealanalysisvolumei_jirilebl_2025/pages/) |
| **[Introductory Lectures on Convex Optimization](ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/) | Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/introductorylecturesonconvexoptimization_nesterov_2004/pages/) |
| **[Optimization Theory and Methods: Nonlinear Programming](ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/)**<br><sub>Wenyu Sun 与 Ya-xiang Yuan (2006)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/) | Chenyi Li, Wanli Ma, Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/optimizationtheoryandmethods_sunyuan_2006/pages/) |
| **[Probability Theory: A Comprehensive Course](ReasBook/Books/ProbabilityTheory_Klenke_2020/)**<br><sub>Achim Klenke（第 3 版，2020）</sub> | [`v4.29.0`](https://github.com/optpku/ReasBook/tree/v4.29.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | Xuanzhi Ren, Zichen Wang | 仅源代码（不包含在当前发布配置中） |
| **[Lectures on Riemann Surfaces](ReasBook/Books/RiemannSurfaces_Forster_1981/)**<br><sub>Otto Forster (1981)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/RiemannSurfaces_Forster_1981/Book.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/riemannsurfaces_forster_1981/pages/) |
| **[Computational Methods for Inverse Problems](ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/)**<br><sub>Curtis R. Vogel (2002)</sub> | 未分配到活跃发布分支 | Yifan Bai, Wanli Ma, Zichen Wang | 仅源代码（不包含在当前发布配置中） |

## 论文

点击标题可打开目录页；点击版本可直接打开 Lean 源代码。

### 我们解决的开放问题

以下论文给出了本团队对既有开放研究问题的解答。

| 形式化项目 | 源代码 | 贡献者 | 资源 |
| --- | :---: | --- | --- |
| **[A Counterexample to Global Convergence of Classical DFP Under the Standard Strong Wolfe Conditions](ReasBook/Papers/DFP_wolfe_local/)**<br><sub>Benqi Liu、Zichen Wang、Zaiwen Wen、Liwei Zhang 与 Yaxiang Yuan</sub> | [`v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/DFP_wolfe_local/) | Zichen Wang | [Docs](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/docs/) &#124; [Verso](https://optpku.github.io/ReasBook/sites/dfp_wolfe_local/pages/) &#124; [定理依赖图](https://optpku.github.io/ReasBook/theorem-maps/papers/dfp_wolfe_local/) &#124; [arXiv](https://arxiv.org/html/2608.21708v1) |
| **[A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates](ReasBook/Papers/TR_LALM_theory/)**<br><sub>Benqi Liu、Kangkang Deng、Zichen Wang 与 Zaiwen Wen</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/TR_LALM_theory/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/tr_lalm_theory/pages/) &#124; [定理图](https://optpku.github.io/ReasBook/theorem-maps/papers/tr_lalm_theory/) |
| **[The Minimum Q-Order of BFGS with Exact Line Search Is One](ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/)**<br><sub>Benqi Liu、Chenyi Li 与 Zaiwen Wen (2026)</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/) | Chenyi Li | 仅源代码（文档待发布） |
| **[Technical note: a counterexample to the Rockafellar sum conjecture on c₀](ReasBook/Papers/RockafellarSum_2026/)**<br><sub>Junyu Zhang, Jinbiao Chen, Zichen Wang, Benqi Liu, and Zaiwen Wen (2026)</sub> | [`v4.32.0`](https://github.com/optpku/ReasBook/tree/v4.32.0/ReasBook/Papers/RockafellarSum_2026/) | Zichen Wang | 仅源代码（文档待发布） |

### 其他已形式化论文

| 形式化项目 | 源代码 | 贡献者 | 资源 |
| --- | :---: | --- | --- |
| **[Smooth Minimization of Non-Smooth Functions](ReasBook/Papers/SmoothMinimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | Wanli Ma, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/smoothminimization_nesterov_2004/pages/) |
| **[On Some Local Rings](ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)**<br><sub>Mohamad Maassarani (2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) &#124; [Verso](https://optpku.github.io/ReasBook/sites/onsomelocalrings_maassaran_2025/pages/) |

## 贡献指南

人类贡献流程见 [CONTRIBUTING.md](CONTRIBUTING.md)。使用 coding agent 时，可遵循 [ReasBook contributing skill](CONTRIBUTING/SKILL.md)；其中记录了分支、元数据、验证和 pull request 规则。

- 书籍和论文代码位于与其 Lean/mathlib 工具链相匹配的已注册版本分支；仅接受已注册的稳定 `vX.Y.Z` 版本。
- **书籍和论文代码不合并到 `main`。** `main` 始终作为跨版本目录，其中的链接目录指向对应版本分支。
- PR 的目标分支、PR 标题中的版本、`ReasBook/lean-toolchain` 和书籍元数据（如适用）必须完全一致。

## Lean 项目

<table>
<thead>
<tr>
<th scope="col">类别</th>
<th scope="col">项目</th>
<th scope="col">简介</th>
</tr>
</thead>
<tbody>
<tr>
<td scope="rowgroup">形式化平台</td>
<td><a href="https://reaslab.io">ReasLab</a></td>
<td>用于协作式定理开发和验证的在线 Lean 形式化平台。</td>
</tr>
<tr>
<td rowspan="2" scope="rowgroup">形式化项目</td>
<td><a href="https://github.com/optsuite/optlib">Optlib</a></td>
<td>面向数学优化的 Lean 4 库，涵盖凸分析、最优性条件和算法收敛性。</td>
</tr>
<tr>
<td><a href="https://github.com/optpku/ReasBook">ReasBook</a></td>
<td>面向教材和论文形式化的 Lean 4 项目，同时覆盖定理证明和计算问题。</td>
</tr>
<tr>
<td rowspan="2" scope="rowgroup">基准测试</td>
<td><a href="https://github.com/optsuite/AMBER">AMBER</a></td>
<td>面向应用数学形式化中构造与验证任务的 Lean 4 基准，同时覆盖定理证明和计算问题。</td>
</tr>
<tr>
<td><a href="https://github.com/optpku/CAM-Bench">CAM-Bench</a></td>
<td>面向计算与应用数学形式化定理证明的 Lean 4 基准。</td>
</tr>
<tr>
<td rowspan="3" scope="rowgroup">自动形式化与定理证明</td>
<td><a href="https://github.com/optsuite/M2F">M2F</a></td>
<td>将自然语言数学教材转换为可进行形式化的 Lean 项目的工具包。</td>
</tr>
<tr>
<td><a href="https://github.com/chenyili0818/SITA">SITA</a></td>
<td>一种结构到实例的自动形式化框架，利用验证反馈生成 Lean 定义和定理。</td>
</tr>
<tr>
<td><a href="https://github.com/optsuite/lean-tools-mcp">lean-tools-mcp</a></td>
<td>Lean MCP 服务器，在重型 import（尤其是 Mathlib）场景中提供更高并行吞吐和更低内存占用。</td>
</tr>
</tbody>
</table>

## 研究成果

### 数学形式化

- Wanli Ma, Zichen Wang, Zaiwen Wen, *A Unified Framework for Formalizing Matrix Decomposition Proofs*. [(论文)](https://arxiv.org/abs/2607.05874)
- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(论文)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(论文)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(论文)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(论文)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### 自动形式化与自动定理证明

- Wentao Long, Yunfei Zhang, Chenyi Li, Zaiwen Wen, *MECA: A Mechanism-Centered Agent for Constructing Well-Specified and Valuable Mathematical Conjectures*. [(论文)](https://arxiv.org/abs/2607.27709)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*, ICML 2026. [(论文)](https://arxiv.org/abs/2604.23712)
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(论文)](https://arxiv.org/abs/2602.17016)
- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(论文)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(论文)](https://arxiv.org/abs/2511.10356)

### 定理证明检查

- Ziyu Wang, Qiming Dai, Yishan Wu, Zaiwen Wen. *FaithSieve: Fine-Grained Evaluation of Math Proofs with Faithful Formal Evidence*.
- Ziyu Wang, Qiming Dai, Chenyi Li, Zaiwen Wen, *Beyond Formal Correctness: Structure-Aware Evaluation of Informal–Formal Proof Correspondence*

### 前提选择

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(论文)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### 基准测试

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*. [(论文)](https://arxiv.org/abs/2602.01291)
- Wentao Long, Yunfei Zhang, Chenyi Li, Li Zhou, Chumin Sun, Zaiwen Wen. *CAM-Bench: A Benchmark for Computational and Applied Mathematics in Lean*. [(论文)](https://arxiv.org/abs/2605.17255)

## 贡献者

- Chenyi Li，北京大学数学科学学院，中国（`lichenyi@stu.pku.edu.cn`）
- Wanli Ma，北京大学北京国际数学研究中心，中国（`wlma@pku.edu.cn`）
- Zichen Wang，北京大学数学科学学院，中国（`zichenwang25@stu.pku.edu.cn`）
- Ziyu Wang，北京大学数学科学学院，中国（`wangziyu-edu@stu.pku.edu.cn`）
- Zaiwen Wen，北京大学北京国际数学研究中心，中国（`wenzw@pku.edu.cn`）
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Yantao Li, Wentao Long, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Feiming Wang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwu Wu, Mingyue Xu, Lurong Yang, Yunfei Zhang, Jian Yu, Changyun Zou

## 引用

如果你使用 ReasBook，请同时引用 M2F 论文和本仓库。

M2F 论文：

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

ReasBook 软件：

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

引用某个具体形式化项目时，还应引用原始书籍或论文，并记录 ReasBook 项目目录、版本分支和完整 commit SHA。例如：`v4.30.0`、`ReasBook/Books/<project>/`，以及 `git rev-parse HEAD` 的输出。本仓库还提供 [`CITATION.cff`](CITATION.cff)，供引用工具和 GitHub 引用界面使用。

## 许可证

ReasBook 使用与 mathlib 一致的 [Apache License 2.0](LICENSE)。除非单个文件另有声明，该许可证适用于 ReasBook 在所有官方分支上的内容，以及由本仓库派生的所有副本和 fork。各 fork 的新增内容和第三方依赖仍受其各自许可证声明约束。

# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome collaboration from researchers, students, and practitioners.

ReasBook is generated using the tool: [M2F](https://github.com/optsuite/M2F.git).

## Current Coverage

> Note: `Documentation` is currently maintained and validated for Tao's *Analysis II*.
> For other books, full aggregation in `Documentation` may temporarily cause naming conflicts.

### Books
- [Terence Tao, *Analysis II*, 4th ed., Hindustan Book Agency / Springer, Singapore, 2022, ISBN 978-981-19-7284-3.](./ReasBook/Books/Analysis2_Tao_2022/)
  - Contributors: Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Books/Analysis2_Tao_2022/Book.html) | [Lean source](./ReasBook/Books/Analysis2_Tao_2022/Chapters/) | [Verso](https://optpku.github.io/ReasBook/books/analysis2_tao_2022/)
- [R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, Princeton, 1970, ISBN 0-691-08069-0.](./ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)
  - Contributors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwan Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Book.html) | [Lean source](./ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/) | [Verso](https://optpku.github.io/ReasBook/books/convexanalysis_rockafellar_1970/)
- [Jiri Lebl, *Introduction to Real Analysis, Volume I*, version 6.2, May 23, 2025, (TBD: publisher/city), (TBD: ISBN).](./ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)
  - Contributors: Zichen Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) | [Lean source](./ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/) | [Verso](https://optpku.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/)
- [Michele Conforti, Gerard Cornuejols, Giacomo Zambelli, *Integer Programming*, Graduate Texts in Mathematics 271, Springer, 2014, ISBN 978-3-319-11007-3.](./ReasBook/Books/IntegerProgramming_Conforti_2014/)
  - Contributors: Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Books/IntegerProgramming_Conforti_2014/Book.html) | [Lean source](./ReasBook/Books/IntegerProgramming_Conforti_2014/Chapters/) | [Verso](https://optpku.github.io/ReasBook/books/integerprogramming_conforti_2014/)

### Papers
- [Yurii Nesterov, "Smooth minimization of non-smooth functions," *Mathematical Programming*, Ser. A 103, 127-152, 2005, DOI: 10.1007/s10107-004-0552-5.](./ReasBook/Papers/SmoothMinimization_Nesterov_2004/)
  - Contributors: Wanli Ma, Zichen Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Paper.html) | [Lean source](./ReasBook/Papers/SmoothMinimization_Nesterov_2004/Sections/) | [Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/)
- [Mohamad Maassarani, "On Some Local Rings," arXiv:2512.19197v1 [math.AC], 2025.](./ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)
  - Contributors: Liang Xiao, Haochen Ju, Zichen Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) | [Lean source](./ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Sections/) | [Verso](https://optpku.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/)

## Repository Layout

The repository keeps a shared Lean source tree (`ReasBook/`) and a single Verso website project (`ReasBookWeb/`):

```text
ReasBook/
├── ReasBook/                         # Main Lean project (books + papers)
│   ├── Books/
│   ├── Papers/
│   ├── ReasBook.lean
│   ├── LiterateExtract.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── ReasBookWeb/                      # Verso website project
│   ├── ReasBookSite/
│   ├── static_files/
│   ├── scripts/gen_sections.py
│   ├── ReasBookSite.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── .github/workflows/deploy_pages.yml
├── build.sh
├── build-web.sh
├── serve.py
└── scripts/cleanup-generated.sh
```

## Naming Convention

Top-level content directories use:

`<Title>_<AuthorLastName>_<Year>`

Examples:

- `ConvexAnalysis_Rockafellar_1970`
- `SmoothMinimization_Nesterov_2004`
- `OnSomeLocalRings_Maassaran_2025`

## Build

### Fast preview (Verso-only, recommended)

From the repository root:

```bash
BUILD_DOCS=0 ./build.sh
./scripts/build_reasbook_web.sh
python3 serve.py 18000
```

Open:

- `http://127.0.0.1:18000/ReasBook/`

### Full build (complete pipeline)

```bash
./build-web.sh
python3 serve.py 18000
```

This path is much slower than the fast preview mode.

If generated artifacts were previously committed, untrack them (without deleting local files):

```bash
./scripts/cleanup-generated.sh
```

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Sino-Russian Mathematics Center
- Great Bay University
- National Natural Science Foundation of China

## Lean Projects

### Formalization Platform

- [ReasLab](https://prove.reaslab.io)
  - An online Lean formalization platform for collaborative theorem development and verification.

### Formalization Projects

- [Optlib](https://github.com/optsuite/optlib)
  - A Lean4 library for mathematical optimization, covering convex analysis, optimality conditions, and algorithm convergence.
- [ReasBook](https://github.com/optsuite/ReasBook)
  - A Lean4 project for textbook and paper formalization, including both theorem proving and computational problems.

### Benchmark

- [AMBER](https://github.com/optsuite/AMBER)
  - A Lean4 benchmark for applied mathematics formalization including proving and computational problems.

### Autoformalization and Theorem Proving Systems

- [M2F](https://github.com/optsuite/M2F)
  - A toolkit for converting natural-language mathematical textbooks into formalization-ready Lean projects.

- [SITA](https://github.com/chenyili0818/SITA)
  - A structure-to-instance autoformalization framework for generating Lean definitions/theorems with verification feedback.

## Publications

### Formalization of Optimization

- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automated Theorem Proving

- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*.
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(Paper)](https://arxiv.org/abs/2602.17016)

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*. [(Paper)](https://arxiv.org/abs/2602.01291)

## Contributors

- Chenyi Li, School of Mathematical Sciences, Peking University, China (`lichenyi@stu.pku.edu.cn`)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, China (`wlma@pku.edu.cn`)
- Zichen Wang, School of Mathematical Sciences, Peking University, China (`zichenwang25@stu.pku.edu.cn`)
- Ziyu Wang, School of Mathematical Sciences, Peking University, China (`wangziyu-edu@stu.pku.edu.cn`)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, China (`wenzw@pku.edu.cn`)
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwan Wu, Mingyue Xu, Yunfei Zhang, Changyun Zou

## License

Released under the Apache 2.0 license. See `LICENSE` for details.

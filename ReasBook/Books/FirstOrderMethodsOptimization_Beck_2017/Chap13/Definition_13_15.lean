/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 13.15 is `source-facing`: it fixes the constrained problem `(13.42)` together with
its canonical optimizer set notation `X^*` used later in Chapter 13. Domain sampling in the
constrained-optimization layer identifies:

- `constrained_problem_objective` from Chapter 3 as the owner of the extended-real constrained
  objective;
- `constrained_problem_solutions` from Chapter 8 as the owner of the feasible minimizer set;
- `mem_constrained_problem_solutions_iff` as the companion characterization of that set by
  feasibility plus `IsMinOn`.

Primitive data are only the original objective `f` and the feasible set `C`. The objective and
optimizer set are therefore derived by direct reuse of those upstream owners, so this item should
surface them directly rather than keep any local wrapper or repackage the solution-set data. -/

/- Definition 13.15: the constrained problem `min_{x ∈ C} f(x)` is represented by the Chapter 3
owner `constrained_problem_objective`, specialized to the given objective `f` and feasible set
`C`. -/
recall constrained_problem_objective

/- Definition 13.15: the associated optimal set `X^*` is the Chapter 8 owner
`constrained_problem_solutions`, specialized to the same data `(f, C)`. -/
recall constrained_problem_solutions

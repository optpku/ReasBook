/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → ℝ) (Lf : NNReal)

/- Definition 10.61 is recall-only. The non-Euclidean gradient method keeps the same source-facing
whole-space minimization setup as Definition 10.4.1; the only change is that the ambient norm on
`E` need not be Euclidean.

Domain sampling identifies the existing owners already used in the chapter:
- `unconstrained_problem_solutions` from Chapter 8 for the unconstrained minimization problem;
- `mem_unconstrained_problem_solutions_iff` for its companion minimizer characterization;
- `is_l_smooth_on` from Chapter 5 for the `L_f`-smoothness assumption;
- `is_l_smooth_on_iff` for the derivative-Lipschitz characterization of that assumption.

The primitive data here are only the objective `f` and the smoothness parameter `Lf`; the
problem and smoothness clauses are derived by direct reuse of the existing owners, so this file
should not keep a separate wrapper around the generic smoothness predicate alone. -/

/- Definition 10.61: the unconstrained problem `min {f(x) | x ∈ E}` is the Chapter 8 owner
`unconstrained_problem_solutions f`. -/
#check unconstrained_problem_solutions f

/- Definition 10.61: the standing non-Euclidean smoothness assumption is the whole-space
specialization `is_l_smooth_on f Set.univ Lf` of the Chapter 5 owner predicate. -/
#check is_l_smooth_on f Set.univ Lf

end

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

/- Definition 10.4.1 is a recall-only `source-facing` item in the smooth whole-space
minimization domain: it introduces no new owner abstraction beyond the Chapter 8 unconstrained
minimization owner and the Chapter 5 smoothness owner.

Domain sampling:
- `unconstrained_problem_solutions` is the source-facing owner for minimizing `f` on the ambient
  space `E`;
- `mem_unconstrained_problem_solutions_iff` is the companion characterization by `IsMinOn f
  Set.univ x`;
- `is_l_smooth_on` is the Chapter 5 owner for the `L_f`-smoothness clause;
- `is_l_smooth_on_iff` is the derivative-Lipschitz companion API for that smoothness owner.

The primitive data are only the objective `f : E → ℝ` and the smoothness parameter `L_f`. The
source-facing whole-space problem and smoothness clause are therefore the canonical specializations
`unconstrained_problem_solutions f` and `is_l_smooth_on f Set.univ Lf`, derived directly from the
existing owners rather than from a parallel local wrapper. -/

set_option linter.hashCommand false

/- Definition 10.4.1: the unconstrained minimization problem
`min {f(x) | x ∈ E}` is the Chapter 8 owner specialized to `f`. -/
#check unconstrained_problem_solutions f

/- Definition 10.4.1: the standing smoothness assumption is the Chapter 5 owner `is_l_smooth_on`,
specialized to the whole space `Set.univ`. -/
#check is_l_smooth_on f Set.univ Lf

end

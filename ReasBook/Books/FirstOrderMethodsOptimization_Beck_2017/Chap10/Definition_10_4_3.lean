/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {ι : Type u} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

variable (f : E → ℝ) (lam : ℝ) (Lf : NNReal)

/- Definition 10.4.3 is `source-facing`: it considers the Euclidean `ℓ¹`-regularized composite
problem
`min_x {f x + λ ‖x‖₁}`
under the standing assumptions `0 < λ` and global `L_f`-smoothness of `f`.

Domain sampling:
- `EuclideanSpace.l1Norm` and the notation `‖x‖₁` from Chapter 6 are the project owner for the
  Euclidean `ℓ¹` norm on finite products;
- `unconstrained_problem_solutions` from Chapter 8 is the source-facing owner for whole-space
  minimization;
- `composite_model_objective` is the Chapter 10 owner for objectives of the form `f + g`;
- `is_l_smooth_on` is the Chapter 5 owner for the smoothness clause.

Primitive data here are therefore the whole-space minimization owner
`unconstrained_problem_solutions` applied to the Chapter 10 composite objective
`composite_model_objective f (fun x ↦ lam * ‖x‖₁)`, together with the explicit source
assumptions `0 < lam` and `is_l_smooth_on f Set.univ Lf`. There is no additional owner-level
wrapper to introduce. -/

set_option linter.hashCommand false

/- Definition 10.4.3: the Euclidean `ℓ¹`-regularized problem is the unconstrained minimization
problem for the Chapter 10 composite objective `x ↦ f x + λ ‖x‖₁`. -/
#check (unconstrained_problem_solutions
  (composite_model_objective f (fun x : E ↦ lam * EuclideanSpace.l1Norm x)) : Set E)

/- Definition 10.4.3: the regularization parameter satisfies the standing positivity condition
`0 < λ`. -/
#check 0 < lam

/- Definition 10.4.3: the smooth term `f` satisfies the whole-space `L_f`-smoothness condition. -/
#check is_l_smooth_on f Set.univ Lf

end

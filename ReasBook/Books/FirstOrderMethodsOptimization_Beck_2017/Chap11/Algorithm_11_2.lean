/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 11.2 is a `bridge/view` in the Chapter 11 proximal-gradient domain.

Domain sampling identifies the relevant owner layer as:
- `is_proximal_gradient_trajectory_with_stepsizes` from Definition 10.8, the chapter's
  `source-facing` proximal-gradient trajectory stated in the textbook stepsize language;
- `is_proximal_gradient_trajectory_with_stepsizes_step`, the canonical one-step accessor for the
  primitive textbook differentiability and prox-update data;
- `is_proximal_gradient_trajectory_with_stepsizes_mem_prox` and
  `proximal_gradient_step_eq_stepsize_form` from Definition 10.8 as the direct bridge/view API.

Primitive data here remain only the smooth term `f`, the nonsmooth term `g`, the iterate sequence
`x^k`, and the positive stepsizes `t_k`. The Chapter 11 displayed update
`x^(k+1) ∈ prox_{t_k g}(x^k - t_k ∇ f(x^k))` is therefore derived API from the existing Chapter 10
stepsize owner, not a second owner. -/

/- Algorithm 11.2: the textbook proximal-gradient recursion with positive stepsizes is already the
existing Chapter 10 owner `is_proximal_gradient_trajectory_with_stepsizes`. -/
recall is_proximal_gradient_trajectory_with_stepsizes
recall is_proximal_gradient_trajectory_with_stepsizes_step
recall proximal_gradient_step_eq_stepsize_form
recall is_proximal_gradient_trajectory_with_stepsizes_mem_prox

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.62 is recall-only in the chapter's first-order iterative API. Domain sampling in
the same owner family points to the existing Chapter 8 declarations

- `gradient_method` as the recursive sequence owner;
- `gradient_method_zero` and `gradient_method_succ` as the derived base-step and one-step API;
- `subgradient_method` as the nearby same-shape first-order method owner confirming the chapter's
  recursion-first design.

The primitive data are exactly the objective `f`, the stepsize sequence `t`, and the initial
point `x0`. The update formula and its stepwise expansion are derived from the owner via the
existing zero/succ theorems, so this file should not introduce a parallel local wrapper, alias,
or restated recursion. -/

/- Definition 10.62: given an initial point `x0` and stepsizes `t_k`, the gradient method for a
differentiable objective `f` is the recursive sequence satisfying
`x^(k+1) = x^k - t_k • ∇ f(x^k)`. -/
recall gradient_method

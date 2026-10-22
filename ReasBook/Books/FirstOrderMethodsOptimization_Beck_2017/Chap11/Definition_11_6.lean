/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 11.6 is a `source-facing` recall in the Chapter 11 block proximal-gradient layer.

Domain sampling identifies the owner stack as follows:
- `prox[...]` together with `prox_eq_singleton_of_proper_closed_convex` is the
  `core/canonical` proximal owner;
- `block_partial_prox_grad_point` from Definition 11.4 is the Chapter 11 `source-facing` owner for
  the one-block proximal-gradient point `T_M^i(x)`, written in Lean on the theorem surface as
  `(T[M; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i`.

The primitive data here are only the block penalties `g_i`, the chosen block partial gradient
map, the positive stepsize `M`, the base point `x`, and the block index `i`. The redundant local
wrapper with an ambient `f` and `x : interior (effective_domain f)` did not define new
mathematics, so this file reuses the existing owner directly instead of keeping a parallel
chosen-witness definition. -/

/- Definition 11.6: the one-block proximal-gradient point is the existing Chapter 11 owner
`block_partial_prox_grad_point`, written on the theorem surface as
`(T[M; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i`, the unique point of
`prox[((1 / M) • g_i)] (x_i - (1 / M) • block_gradient_i(x))`. -/
recall block_partial_prox_grad_point

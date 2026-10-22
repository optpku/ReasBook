/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

/- Definition 13.16 is recall-only in the block conditional-gradient setup.

Domain sampling identifies the existing owner abstractions already fixed upstream:
- `PiLp.separableSum` from Chapter 6 for the block-separable term `x ↦ ∑ i, g_i (x_i)`;
- `composite_model_objective` from Chapter 10 for the objective `F = f + g`;
- the Chapter 11 source-facing block insertion notation `𝒰[i]`, implemented by `PiLp.single 2 i`;
- the Chapter 11 bridge `block_partial_gradient`, with
  `gradient_eq_block_partial_gradient` expressing `∇ f(x) = (∇[i] f x)_i`.

The primitive data remain only the smooth term, the block penalties, and the ambient product
space `PiLp 2 E`. This item should therefore reuse those owners directly rather than keep a
parallel Chapter 13 wrapper layer. -/

/- Definition 13.16: on the canonical block product `PiLp 2 E`, the block composite objective is
the Chapter 10 owner `composite_model_objective f (PiLp.separableSum g)`, the insertion map `𝒰ᵢ` is
the Chapter 11 notation for `PiLp.single 2 i`, and the block partial gradient `∇ᵢ f` is the
Chapter 11 bridge to the ambient gradient. -/
recall PiLp.separableSum
recall composite_model_objective
recall PiLp.single
recall block_partial_gradient
recall gradient_eq_block_partial_gradient

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 11.2 is a `bridge/view` recall in the proximal-gradient chapter.

Domain sampling shows that the correct owner abstraction is already present upstream:
- Definition 10.2's `composite_model_objective`, the chapter owner for the source-facing
  composite objective `F(x) = f(x) + g(x)`;
- Definition 10.66, which already reuses the same owner in a later proximal-gradient setting with
  no new owner-level data;
- Definition 11.3, where the genuinely new Chapter 11 content first appears as the block-product
  specialization of that same owner.

The primitive data remain only the two summands `f` and `g`; Chapter 11.2 adds no new canonical
object beyond the existing pointwise-sum objective. This file should therefore recall
`composite_model_objective` directly rather than keep a second wrapper or alias specialized to the
proximal-gradient section. -/

/- Definition 11.2: the proximal gradient model
`min_{x ∈ E} f(x) + g(x)` is the same composite objective owner
`composite_model_objective` used earlier for the pointwise sum `F(x) = f(x) + g(x)`. -/
recall composite_model_objective

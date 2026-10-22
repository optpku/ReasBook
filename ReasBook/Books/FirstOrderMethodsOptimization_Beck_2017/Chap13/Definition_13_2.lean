/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 13.2 is a `bridge/view` recall in the generalized conditional-gradient chapter.

Domain sampling identifies the existing owner abstraction upstream:
- `composite_model_objective` from Chapter 10 for the source-facing composite objective
  `F(x) = f(x) + g(x)`;
- recall-only specializations in Definitions 10.66 and 11.2, which already reuse that same owner
  without introducing a parallel Chapter-local wrapper.

The primitive data remain only the two summands `f` and `g`, so this file should expose direct
reuse of the Chapter 10 owner rather than a second alias for the same pointwise sum. -/

/- Definition 13.2: the composite problem
`min {F(x) ≡ f(x) + g(x)}`
is the same pointwise-sum objective owner `composite_model_objective` introduced earlier. -/
recall composite_model_objective

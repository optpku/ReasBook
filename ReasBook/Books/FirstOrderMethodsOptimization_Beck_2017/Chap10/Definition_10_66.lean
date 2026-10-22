/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.66 is recall-only in the non-Euclidean proximal-gradient section.

Domain sampling shows that the correct owner abstraction is already present upstream:
- Definition 10.2's `composite_model_objective`, the Chapter 10 owner for the source-facing
  composite objective `F(x) = f(x) + g(x)`;
- later recall-only reuse such as Definition 11.2, which keeps the same owner for the same
  objective in a new algorithmic setting;
- downstream results such as Remark 10.20, which already use `composite_model_objective` on the
  theorem surface.

The primitive data remain only the two summands `f` and `g`; the statement that the ambient norm
on `E` need not be Euclidean is setup, not new owner-level mathematical content. So this file
should reuse the existing `core/canonical` declaration `composite_model_objective` directly,
rather than introducing a second local wrapper or alias. -/

/- Definition 10.66: the composite optimization model
`min_{x ∈ E} {F(x) ≡ f(x) + g(x)}` in a normed space whose norm is not assumed Euclidean is the
same Chapter 10 objective owner `composite_model_objective`. -/
recall composite_model_objective

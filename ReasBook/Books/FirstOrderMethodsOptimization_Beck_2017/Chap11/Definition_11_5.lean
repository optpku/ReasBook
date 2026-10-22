/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 11.5 is recall-only in the Chapter 11 proximal-gradient toolbox.

Domain sampling identifies the Chapter 10 proximal-gradient stack as:
- `source-facing`: `prox_gradient_mapping`, the real-valued smooth-term surface `G[L; f, g]`;
- `core/canonical`: `gradient_mapping`, the residual owner on
  `interior (effective_domain f.toEReal)`;
- `bridge/view`: `prox_grad_operator`, the owner of the auxiliary notation `T_L^{f,g}`.

This item therefore introduces no new owner-level data, wrapper, or chapter-local surrogate. -/

/- Definition 11.5: the Chapter 11 gradient mapping is the previously defined Chapter 10
proximal-gradient mapping `prox_gradient_mapping`, whose core owner is `gradient_mapping` with
residual formula `G_L^{f,g}(x) = L • (x - T_L^{f,g}(x))`. The auxiliary update
`T_L^{f,g}` is already owned upstream by `prox_grad_operator`. -/
recall gradient_mapping
recall prox_gradient_mapping

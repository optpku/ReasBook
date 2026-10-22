/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 12.0.3 is a `core/canonical` recall in one-variable calculus. Domain sampling:
- `exists_hasDerivAt_eq_slope` is the `HasDerivAt` owner form of Lagrange's theorem;
- `exists_deriv_eq_slope` is the canonical `deriv` owner matching the textbook statement;
- `exists_deriv_eq_slope'` is the same theorem in `slope` notation;
- `exists_deriv_eq_zero` is the nearby Rolle specialization.

The Chapter 12 item adds no new source-facing data or bridge construction, so the correct public
surface is the direct recall of `exists_deriv_eq_slope`. -/
recall exists_deriv_eq_slope

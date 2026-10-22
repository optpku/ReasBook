/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 10.55 is a `bridge/view` item. The S-FISTA objective
`H(x) = f(x) + h(x) + g(x)` introduces no new owner-level data beyond the Chapter 10 pointwise-sum
objective `composite_model_objective`; it is just that owner used twice. The primitive data are
the three summand functions, while the explicit three-term evaluation and minimization formulas are
definitional consequences of that nested owner. A separate local wrapper API is therefore
redundant. -/

section

variable {E : Type u} {α : Type v} [Add α]
variable (f h g : E → α)

@[inherit_doc composite_model_objective] notation "H[" f ", " h ", " g "]" =>
  composite_model_objective (composite_model_objective f h) g

/- Definition 10.55: the S-FISTA optimization model with objective
`H(x) = f(x) + h(x) + g(x)` is the Chapter 10 composite-model owner used twice, written on the
source-facing theorem surface as `H[f, h, g]`. -/
#check H[f, h, g]

end

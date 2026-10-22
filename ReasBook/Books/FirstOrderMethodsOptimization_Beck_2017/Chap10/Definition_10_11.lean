/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- Definition 10.11 lies in the Chapter 10 stepsize-rule domain.

Domain sampling against the nearby project API identifies:
- `PosReal` from Definition 6.7 as the canonical owner for positive scalar parameters;
- `Function.const` as the canonical owner for a constant sequence;
- `uses_proximal_gradient_Lf_stepsize_rule` from Remark 10.19 as a neighboring source-facing
  constant-rule owner, showing that the primitive mathematical data are the admissible parameter
  while the schedule itself is derived from the constant-map abstraction.

Triage:
- `source-facing`: the admissible parameter `barL ∈ (L_f / 2, ∞)`;
- `core/canonical`: the constant map `Function.const`;
- `bridge/view`: using an admissible parameter as the constant value of that map.

Primitive data are therefore only the admissible parameter. The constant strategy should be
recalled through the canonical constant-map owner rather than by maintaining a second exact-copy
local definition. -/

/-- An admissible constant parameter for the nonconvex proximal-gradient constant stepsize
strategy is a positive value `barL` satisfying `L_f / 2 < barL`. -/
abbrev ProximalGradientConstantStepsizeParameter (Lf : NNReal) :=
  { barL : PosReal // (Lf : ℝ) / 2 < (barL : ℝ) }

namespace ProximalGradientConstantStepsizeParameter

theorem lower_bound {Lf : NNReal} (barL : ProximalGradientConstantStepsizeParameter Lf) :
    (Lf : ℝ) / 2 < (barL : ℝ) :=
  barL.2

end ProximalGradientConstantStepsizeParameter

variable {Lf : NNReal}

/- Definition 10.11: for an admissible parameter `barL ∈ (L_f / 2, ∞)`, the constant stepsize
strategy is the canonical constant map on `ℕ` with value `barL`. -/
#check (Function.const ℕ : PosReal → ℕ → PosReal)

end

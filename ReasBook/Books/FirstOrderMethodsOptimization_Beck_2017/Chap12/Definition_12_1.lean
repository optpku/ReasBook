/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Set

variable {E : Type u} {Y : Type v}

/- Definition 12.1 has two layers:
- `bridge/view`: the primal objective `x ↦ f x + g (A x)` is the Chapter 10 owner
  `composite_model_objective` specialized to the pair of summands `f` and `g ∘ A`;
- `source-facing`: the associated primal optimal value.

Domain sampling in the surrounding project gives:
- `source-facing`: the primal model `x ↦ f x + g (A x)`;
- `core/canonical`: `composite_model_objective` from Definition 10.2;
- `bridge/view`: precomposition of the second term along `A`, namely `g ∘ A`.

The primitive data are therefore only `f`, `g`, and `A`; no new Chapter 12 owner object is needed.
The only genuinely new declaration in this file is the source-facing optimal value attached to the
canonical objective `composite_model_objective f (g ∘ A)`. -/

/- Definition 12.1: the primal objective for the dual-based proximal-gradient model is the
Chapter 10 composite objective specialized to `f` and `g ∘ A`. -/
recall composite_model_objective
recall composite_model_objective_apply

/-- The optimal value `f_opt` of the dual-based primal model is the infimum of the range of the
primal objective `x ↦ f x + g (A x)`. -/
noncomputable def dual_based_proximal_gradient_primal_optimal_value
    (f : E → EReal) (g : Y → EReal) (A : E → Y) : EReal :=
  sInf (range (composite_model_objective f (g ∘ A)))

-- Proof sketch: unfold `dual_based_proximal_gradient_primal_optimal_value`; the statement is the
-- defining `sInf` formula for the primal optimal value.
/-- Expanding the primal optimal value gives the infimum of the attained objective values. -/
@[simp] theorem dual_based_proximal_gradient_primal_optimal_value_eq_sInf
    (f : E → EReal) (g : Y → EReal) (A : E → Y) :
    dual_based_proximal_gradient_primal_optimal_value f g A =
      sInf (range (composite_model_objective f (g ∘ A))) := rfl

end

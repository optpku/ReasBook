/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/- `prompt_add/` is absent in this workspace, so the owner choice is sampled directly from the
nearby optimization files.

This item is `source-facing`: the textbook introduces the linear-composite minimization model
`min_x {f₁(x) + f₂(Ax)}` together with the standing assumptions that `f₁` and `f₂` are proper,
closed, and convex.

Domain sampling shows that the best owner abstraction is already upstream:
- `core/canonical`: `composite_model_objective` from Chapter 10 for two-term objectives;
- `core/canonical`: `IsADMMConvexObjectivePair` from Chapter 15 Definition 15.1 for the proper/
  closed/convex pair assumptions;
- `bridge/view`: `IsADPMMProblem` from Chapter 15 Definition 15.4, which already extends that
  same Chapter 15 owner rather than rebuilding a second regularity package;
- `bridge/view`: the source formula is the specialization
  `composite_model_objective f₁ (f₂ ∘ A)`.

Primitive data are therefore just the objective terms `f₁`, `f₂`, and the linear map `A`. The
objective itself should reuse the Chapter 10 owner directly rather than duplicating it under a
second local name, and the standing regularity assumptions should reuse the existing Chapter 15
owner rather than minting a parallel local class. -/

/- Definition 15.6: the linear-composite objective `x ↦ f₁(x) + f₂(Ax)` is the Chapter 10
composite objective specialized to `g := f₂ ∘ A`. -/
recall composite_model_objective
recall composite_model_objective_apply

/-- Evaluating the Chapter 10 composite owner at the linear-composite specialization recovers the
textbook formula `f₁(x) + f₂(Ax)`. -/
@[simp] theorem composite_model_objective_comp_apply
    (f₁ : X → EReal) (f₂ : Y → EReal) (A : X →ₗ[ℝ] Y) (x : X) :
    composite_model_objective f₁ (f₂ ∘ A) x = f₁ x + f₂ (A x) :=
  rfl

end

section

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]
variable [TopologicalSpace Y] [AddCommMonoid Y] [Module ℝ Y]

/- The proper/closed/convex standing assumptions in Definition 15.6 are already the Chapter 15
owner `IsADMMConvexObjectivePair`; the linear-composite file adds no second regularity owner. -/
recall IsADMMConvexObjectivePair

end

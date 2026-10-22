/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {α : Type v} [Add α]

/- Definition 10.2 is `source-facing`: the textbook introduces the composite optimization model
through its objective `F(x) = f(x) + g(x)`. The `core/canonical` owner of that mathematics is the
ordinary pointwise addition on the function space `E → α`, so this file should expose only a thin
source-facing name together with atomic bridges back to the canonical additive API. -/

/-- Definition 10.2: the composite model objective is the pointwise sum `F(x) = f(x) + g(x)`
whose minimization over `E` is the composite optimization problem. -/
abbrev composite_model_objective (f g : E → α) : E → α := f + g

-- Proof sketch: `composite_model_objective` is definitionally the canonical pointwise sum `f + g`.
/-- The source-facing Chapter 10 objective is exactly the canonical pointwise sum `f + g`. -/
theorem composite_model_objective_eq_add (f g : E → α) :
    composite_model_objective f g = f + g := rfl

-- Proof sketch: evaluate the canonical pointwise sum `(f + g)` at `x`.
/-- Evaluating the composite model objective at `x` gives the sum `f x + g x`. -/
@[simp] theorem composite_model_objective_apply (f g : E → α) (x : E) :
    composite_model_objective f g x = f x + g x := rfl

end

section

variable {E : Type u} {α : Type v} [Add α] [Preorder α]

-- Proof sketch: `composite_model_objective f g` is definitionally the canonical pointwise sum
-- `f + g`.
/-- On any domain `s`, minimizing the composite model objective is exactly minimizing the
canonical pointwise sum `f + g` on `s`; the textbook `Set.univ` case is the specialization
`s = Set.univ`. -/
theorem isMinOn_composite_model_objective_iff
    {f g : E → α} {s : Set E} {x : E} :
    IsMinOn (composite_model_objective f g) s x ↔
      IsMinOn (f + g) s x := Iff.rfl

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 8.7 is `source-facing`: the textbook introduces a deterministic rule that chooses,
for each feasible point `x ∈ C`, one member of the owner set `subdifferential f x = ∂ f(x)`.
This is genuine data, not merely an existence claim, so the public API is a function on `C`
equipped with the pointwise membership property, without any existential wrapper or separate choice
operator. -/

/-- Definition 8.7: a subgradient selection for `f` on `C` is a deterministic rule assigning to
each `x ∈ C` a chosen subgradient `f'(x) ∈ ∂ f(x)`, that is, a function `C → E*` whose value at
every feasible point belongs to the subdifferential of `f` at that point. -/
structure SubgradientSelection (f : E → EReal) (C : Set E) where
  toFun : C → Module.Dual ℝ E
  mem_subdifferential : ∀ x : C, toFun x ∈ subdifferential f x.1

/-- A subgradient selection is canonically used as the underlying function `C → E*`. -/
instance {f : E → EReal} {C : Set E} :
    CoeFun (SubgradientSelection f C) (fun _ ↦ ↥C → Module.Dual ℝ E) where
  coe s := s.toFun

end

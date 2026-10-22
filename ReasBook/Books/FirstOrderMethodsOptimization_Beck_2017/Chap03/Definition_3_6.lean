/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.6 is `source-facing` in the chapter subgradient API. The primitive owner object is
the pointwise set `subdifferential f x`; Definition 3.5 already identifies "subdifferentiable at
`x`" with the canonical proposition `(subdifferential f x).Nonempty`. This file therefore keeps
only the textbook point-domain `dom(∂ f)` together with the atomic membership and domain
consequence lemmas derived from that owner set. -/

/-- Definition 3.6: the domain of the subdifferential `dom(∂ f)` is the set of points where the
extended-real-valued function `f` is subdifferentiable, equivalently where `∂ f(x)` is nonempty. -/
def subdifferential_domain (f : E → EReal) : Set E :=
  {x | (subdifferential f x).Nonempty}

-- Proof sketch: unfold `subdifferential_domain`.
/-- Membership in `dom(∂ f)` means that the subdifferential at the point is nonempty. -/
@[simp] theorem mem_subdifferential_domain {f : E → EReal} {x : E} :
    x ∈ subdifferential_domain f ↔ (subdifferential f x).Nonempty :=
  Iff.rfl

-- Proof sketch: if `x ∉ effective_domain f`, then Definition 3.2 gives
-- `subdifferential f x = ∅`, so `x` cannot belong to `subdifferential_domain f`.
/-- Every point in the domain of the subdifferential belongs to the effective domain. -/
theorem subdifferential_domain_subset_effective_domain {f : E → EReal} :
    subdifferential_domain f ⊆ effective_domain f := by
  intro x hx
  rw [mem_subdifferential_domain] at hx
  by_contra hx_dom
  simp [subdifferential_eq_empty_of_not_mem_effective_domain hx_dom] at hx

end

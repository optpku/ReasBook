/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter Metric
open scoped Topology

variable {E : Type u}

/-- A proper extended-real-valued function never takes the value `-∞` and has nonempty effective
domain. -/
class IsProperExtendedRealFunction (f : E → EReal) : Prop where
  ne_bot : ∀ x, f x ≠ ⊥
  effective_domain_nonempty : (effective_domain f).Nonempty

section

variable [NormedAddCommGroup E]

/-- Definition 2.5: a proper extended-real-valued function is coercive when its values tend to
`∞` along the filter `‖x‖ → ∞`. -/
class IsCoerciveExtendedRealFunction (f : E → EReal) : Prop
    extends IsProperExtendedRealFunction f where
  tendsto_top : Tendsto f (comap norm atTop) (𝓝 (⊤ : EReal))

section

variable [ProperSpace E] {f : E → EReal}

-- Proof sketch: use the coercive field `hf.tendsto_top`, rewrite `comap norm atTop` as
-- `cobounded E` via `comap_norm_atTop`, then identify `cobounded E` with `cocompact E` on a
-- proper space.
/-- On a proper normed group, a coercive extended-real-valued function tends to `∞` along the
cocompact filter. -/
theorem IsCoerciveExtendedRealFunction.tendsto_top_cocompact
    (hf : IsCoerciveExtendedRealFunction f) : Tendsto f (cocompact E) (𝓝 (⊤ : EReal)) := by
  simpa [comap_norm_atTop', cobounded_eq_cocompact] using hf.tendsto_top

/-- On a proper normed group, coercivity supplies the cocompact `Fact` needed for downstream
minimization arguments. -/
instance instFactTendstoTopCocompact [hf : IsCoerciveExtendedRealFunction f] :
    Fact (Tendsto f (cocompact E) (𝓝 (⊤ : EReal))) where
  out := hf.tendsto_top_cocompact

end

end

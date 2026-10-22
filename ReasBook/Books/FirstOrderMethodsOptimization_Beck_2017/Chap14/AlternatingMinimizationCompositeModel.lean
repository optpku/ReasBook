/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, NormedSpace ℝ (Ei i)]

/-- The standing composite-model assumptions for Algorithm 14.3: each block term `g_i` is proper,
closed, convex, and continuous on its effective domain; the smooth term `f` never takes the value
`-∞`, is closed with convex effective domain, is differentiable on
`interior (effective_domain f)`, and the effective domain of the block-separable regularizer
`separableSum g` lies in `interior (effective_domain f)`. -/
class IsAlternatingMinimizationCompositeModel
    (f : ((i : Fin p) → Ei i) → EReal)
    (g : (i : Fin p) → Ei i → EReal) : Prop where
  g_proper (i : Fin p) : IsProperExtendedRealFunction (g i)
  g_closed (i : Fin p) : LowerSemicontinuous (g i)
  g_convex (i : Fin p) : is_convex_function (g i)
  g_continuousOn_effective_domain (i : Fin p) :
    ContinuousOn (g i) (effective_domain (g i))
  f_ne_bot (x : (i : Fin p) → Ei i) : f x ≠ ⊥
  f_closed : LowerSemicontinuous f
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  f_toReal_differentiableOn_interior_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (interior (effective_domain f))
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain (separableSum g) ⊆ interior (effective_domain f)

namespace IsAlternatingMinimizationCompositeModel

variable {f : ((i : Fin p) → Ei i) → EReal}
variable {g : (i : Fin p) → Ei i → EReal}

/-- The blockwise properness assumptions and the domain-compatibility clause force
`effective_domain f` to be nonempty. -/
theorem f_effective_domain_nonempty
    (h : IsAlternatingMinimizationCompositeModel f g) :
    (effective_domain f).Nonempty := by
  rcases (separableSum_proper g h.g_proper).effective_domain_nonempty with ⟨x, hx⟩
  exact ⟨x, interior_subset (h.g_effective_domain_subset_interior_f_effective_domain hx)⟩

/-- Assumption 14.6 canonically implies that the smooth term `f` is proper. -/
theorem f_proper
    (h : IsAlternatingMinimizationCompositeModel f g) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := h.f_effective_domain_nonempty

/-- Under Assumption 14.6, the smooth term `f` is proper. -/
instance instIsProperExtendedRealFunctionOfIsAlternatingMinimizationCompositeModel
    (h : IsAlternatingMinimizationCompositeModel f g) :
    IsProperExtendedRealFunction f :=
  h.f_proper

end IsAlternatingMinimizationCompositeModel

end

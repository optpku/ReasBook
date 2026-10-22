/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [TopologicalSpace E]

section

-- Proof sketch: if `a ≠ ⊤` and `f x ≤ a`, then automatically `f x < ⊤`, so every `Iic a`
-- sublevel set lies in the effective domain.
omit [TopologicalSpace E] in
/-- Any `Iic a` sublevel set with `a ≠ ⊤` is contained in the effective domain. -/
theorem preimage_Iic_subset_effective_domain {f : E → EReal} {a : EReal} (ha : a ≠ ⊤) :
    f ⁻¹' Set.Iic a ⊆ effective_domain f := by
  intro x hx
  rw [mem_effective_domain]
  exact lt_of_le_of_lt hx (lt_top_iff_ne_top.mpr ha)

-- Proof sketch: prove lower semicontinuity pointwise. On the closed effective domain, continuity
-- gives lower semicontinuity within the domain. Outside the domain the function is identically
-- `⊤` on an open neighborhood, because the complement of a closed effective domain is open.
-- Combine these two cases to obtain lower semicontinuity everywhere.
/-- Theorem 2.3: if an extended-real-valued function is continuous on its effective domain and that
domain is closed, then the function is closed, equivalently lower semicontinuous. -/
theorem lowerSemicontinuous_of_continuousOn_effective_domain (f : E → EReal)
    (h_cont : ContinuousOn f (effective_domain f))
    (h_closed : IsClosed (effective_domain f)) :
    LowerSemicontinuous f := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun a ↦ ?_
  by_cases ha : a = ⊤
  · simp [ha]
  · obtain ⟨v, hv_closed, hv_eq⟩ :=
      lowerSemicontinuousOn_iff_preimage_Iic.1
        h_cont.lowerSemicontinuousOn a
    have h_eq : f ⁻¹' Set.Iic a = effective_domain f ∩ v := by
      calc
        f ⁻¹' Set.Iic a = effective_domain f ∩ (f ⁻¹' Set.Iic a) := by
          symm
          exact Set.inter_eq_right.mpr (preimage_Iic_subset_effective_domain ha)
        _ = effective_domain f ∩ v := hv_eq
    rw [h_eq]
    exact h_closed.inter hv_closed

end

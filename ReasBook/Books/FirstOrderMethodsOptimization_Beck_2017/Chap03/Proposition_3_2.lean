/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: unfold `subdifferential`, `extendedIndicator`, and `normal_cone`. If `x ∈ S`, then
-- `extendedIndicator S x = 0`, and the subgradient inequality is equivalent to
-- `g (z - x) ≤ 0` for every `z ∈ S`. If `x ∉ S`, then `x ∉ effective_domain (extendedIndicator S)`,
-- so `subdifferential (extendedIndicator S) x = ∅`, and `normal_cone S x` is also empty by
-- definition.
/-- Proposition 3.2: the subdifferential of the indicator function `δ_S` coincides with the normal
cone of `S` at every point. In this bridge formulation, the textbook nonemptiness hypothesis on
`S` is redundant because both sides are empty outside `S`. -/
theorem subdifferential_extended_indicator_eq_normal_cone (S : Set E) (x : E) :
    subdifferential (extendedIndicator S) x = normal_cone S x := by
  by_cases hx : x ∈ S
  · ext g
    rw [mem_subdifferential, mem_normal_cone S hx]
    constructor
    · intro hg z hz
      have hsub : (g (z - x) : EReal) ≤ 0 := by
        simpa [extendedIndicator, hx, hz] using hg.2 z
      exact_mod_cast hsub
    · intro hg
      refine ⟨by simpa using hx, ?_⟩
      intro z
      by_cases hz : z ∈ S
      · have hsub : (g (z - x) : EReal) ≤ 0 := by
          exact_mod_cast hg z hz
        simpa [extendedIndicator, hx, hz] using hsub
      · simp [extendedIndicator, hx, hz]
  · rw [subdifferential_eq_empty_of_not_mem_effective_domain, normal_cone_eq_empty_of_not_mem S hx]
    simpa using hx

end

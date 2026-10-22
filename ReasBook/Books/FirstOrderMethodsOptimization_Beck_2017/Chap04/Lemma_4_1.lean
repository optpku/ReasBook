/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: for fixed `x` and any dual vector `y`, the defining supremum formula for
-- `conjugate_function f y` gives `y x - f x ≤ conjugate_function f y`. Rearranging yields
-- `y x - conjugate_function f y ≤ f x`, and taking the supremum over `y` gives
-- `biconjugate_function f x ≤ f x`.
/-- Lemma 4.1: the biconjugate of an extended-real-valued function is pointwise bounded above by
the original function. -/
theorem biconjugate_function_apply_le (f : E → EReal) (x : E) :
    biconjugate_function f x ≤ f x := by
  cases hfx : f x with
  | bot =>
      rw [biconjugate_function_apply]
      refine sSup_le fun z hz ↦ ?_
      rcases hz with ⟨y, rfl⟩
      have hx_top : (⊤ : EReal) ∈ Set.range fun z : E ↦ (y z : EReal) - f z := by
        refine ⟨x, ?_⟩
        simp [hfx, EReal.sub_bot (EReal.coe_ne_bot (y x))]
      have hy_top : conjugate_function f y = ⊤ := by
        rw [conjugate_function_apply]
        exact top_unique <| le_sSup hx_top
      simp [hy_top]
  | coe r =>
      rw [biconjugate_function_apply]
      refine sSup_le fun z hz ↦ ?_
      rcases hz with ⟨y, rfl⟩
      change (y x : EReal) - conjugate_function f y ≤ (r : EReal)
      rw [conjugate_function_apply]
      have hxy :
          (y x : EReal) - (r : EReal) ≤
            sSup (Set.range fun z : E ↦ (y z : EReal) - f z) := by
        refine le_sSup ?_
        refine ⟨x, ?_⟩
        simp [hfx]
      have hy_le :
          (y x : EReal) ≤
            sSup (Set.range fun z : E ↦ (y z : EReal) - f z) + (r : EReal) :=
        (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot r)) (.inl (EReal.coe_ne_top r))).1 hxy
      exact EReal.sub_le_of_le_add' hy_le
  | top =>
      simp

end

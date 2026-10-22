/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Proposition 4.2 is `source-facing` in the chapter conjugacy API. The `core/canonical` owners
for properness and Fenchel conjugation are already Chapter 2's
`IsProperExtendedRealFunction` and Definition 4.1's `conjugate_function`, so this file keeps only
the source-facing inequality and reuses those owners directly. -/
recall IsProperExtendedRealFunction
recall conjugate_function
recall conjugate_function_apply

-- Proof sketch: evaluate the defining supremum of `conjugate_function f y` at `x`, then rearrange
-- the resulting inequality in `EReal`.
/-- Proposition 4.2: Fenchel's inequality. For a proper extended-real-valued function `f`, the sum
of `f x` and its conjugate at `y` dominates the dual pairing `⟨y, x⟩`, written here as `y x`. -/
theorem fenchel_inequality (f : E → EReal) (x : E) (y : Module.Dual ℝ E)
    (hproper : IsProperExtendedRealFunction f) :
    f x + conjugate_function f y ≥ (y x : EReal) := by
  have hx :
      (y x : EReal) - f x ≤ conjugate_function f y := by
    rw [conjugate_function_apply]
    exact le_sSup (Set.mem_range_self x)
  rcases hproper.effective_domain_nonempty with ⟨z, hz⟩
  lift f z to ℝ using ⟨hz.ne, hproper.ne_bot z⟩ with fz hfz
  have hconj_ne_bot : conjugate_function f y ≠ ⊥ := by
    have hz' :
        ((y z : EReal) - f z) ≤ conjugate_function f y := by
      rw [conjugate_function_apply]
      exact le_sSup (Set.mem_range_self z)
    have hterm_ne_bot : ((y z : EReal) - f z) ≠ ⊥ := by
      rw [← hfz]
      simpa [EReal.coe_sub] using EReal.coe_ne_bot (y z - fz)
    exact bot_lt_iff_ne_bot.mp <| (bot_lt_iff_ne_bot.mpr hterm_ne_bot).trans_le hz'
  have hyx :
      (y x : EReal) ≤ conjugate_function f y + f x :=
    (EReal.sub_le_iff_le_add (.inl (hproper.ne_bot x)) (.inr hconj_ne_bot)).mp hx
  simpa [add_comm] using hyx

end

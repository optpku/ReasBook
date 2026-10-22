/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 5.10 is `source-facing`: it lowers the strong-convexity modulus for the Chapter 5
owner `is_strongly_convex_function`. The canonical core owner remains
`StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)` from `Definition_5_16`, so the
proof should bridge through that owner and reuse mathlib's `StrongConvexOn.mono` instead of
duplicating the owner API locally. -/

/-- Proposition 5.10: if an extended-real-valued function is `σ₁`-strongly convex, then it is
also `σ₂`-strongly convex for every smaller positive modulus `σ₂ < σ₁`. -/
theorem is_strongly_convex_function.mono
    {f : E → EReal} {σ₁ σ₂ : ℝ} (hf : is_strongly_convex_function f σ₁)
    (hσ₂ : 0 < σ₂) (hσ₂σ₁ : σ₂ < σ₁) :
    is_strongly_convex_function f σ₂ := by
  rcases is_strongly_convex_function_iff_strongConvexOn_toReal.mp hf with
    ⟨_, hf_ne_bot, hf_strong⟩
  exact
    is_strongly_convex_function_iff_strongConvexOn_toReal.mpr
      ⟨hσ₂, hf_ne_bot, hf_strong.mono hσ₂σ₁.le⟩

end

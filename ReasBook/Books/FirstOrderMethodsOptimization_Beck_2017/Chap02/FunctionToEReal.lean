/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7

universe u

namespace Function

section

variable {E : Type u}

/-- The canonical extended-real-valued lift of a real-valued potential. -/
abbrev toEReal (ω : E → ℝ) : E → EReal :=
  Real.toEReal ∘ ω

/-- Evaluating the canonical extended-real-valued lift of a real-valued potential. -/
@[simp] theorem toEReal_apply (ω : E → ℝ) (x : E) :
    ω.toEReal x = ω x :=
  rfl

end

section

variable {E : Type u} [Nonempty E]

/-- A real-valued function, viewed in `EReal`, is proper. -/
theorem toEReal_isProper (ω : E → ℝ) :
    IsProperExtendedRealFunction ω.toEReal := by
  refine ⟨?_, ?_⟩
  · intro x
    simp [Function.toEReal]
  · let x : E := Classical.choice inferInstance
    exact ⟨x, by simp [effective_domain, Function.toEReal]⟩

end

section

variable {E : Type u} [TopologicalSpace E]

/-- Continuity of a real-valued function implies lower semicontinuity of its canonical
`EReal` coercion. -/
theorem toEReal_lowerSemicontinuous_of_continuous
    {ω : E → ℝ} (hω : Continuous ω) :
    LowerSemicontinuous ω.toEReal := by
  simpa [Function.toEReal] using
    (continuous_coe_real_ereal.comp hω).lowerSemicontinuous

end

section

variable {E : Type u} [PseudoMetricSpace E]

/-- A Lipschitz real-valued function remains lower semicontinuous after coercion to `EReal`. -/
theorem toEReal_lowerSemicontinuous_of_lipschitz
    {ω : E → ℝ} {L : NNReal} (hω : LipschitzWith L ω) :
    LowerSemicontinuous ω.toEReal :=
  toEReal_lowerSemicontinuous_of_continuous hω.continuous

end

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

/-- A convex real-valued function remains convex after coercion to `EReal`. -/
theorem toEReal_isConvexFunction
    {ω : E → ℝ} (hω : ConvexOn ℝ Set.univ ω) :
    is_convex_function ω.toEReal := by
  have hne_bot :
      ∀ x ∈ effective_domain ω.toEReal, ω.toEReal x ≠ ⊥ := by
    intro x hx
    simp [Function.toEReal]
  refine (is_convex_function_iff_convexOn_toReal hne_bot).2 ?_
  simpa [effective_domain, Function.toEReal] using hω

end

end Function

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.1 is the `source-facing` primitive predicate for Chapter 3 subdifferential
theory. The owner set-valued abstraction appears next as `subdifferential`; any finite-valued or
topologized forms should remain derived bridge/view API rather than parallel primitive data. -/

/-- Definition 3.1: a vector `g ∈ E* = Module.Dual ℝ E` is a subgradient of
`f : E → EReal` at `x` when `x` lies in the effective domain of `f` and the
subgradient inequality `f y ≥ f x + g (y - x)` holds for every `y`. -/
def is_subgradient_at (f : E → EReal) (x : E) (g : Module.Dual ℝ E) : Prop :=
  x ∈ effective_domain f ∧ ∀ y : E, f y ≥ f x + (g (y - x) : EReal)

-- Proof sketch: one implication is immediate by restriction. For the converse, if `y` is outside
-- the effective domain then `¬ f y < ⊤`, hence `⊤ ≤ f y`; together with `f y ≤ ⊤` this gives
-- `f y = ⊤`, so the inequality is automatic there.
/-- The subgradient inequality may be checked only on the effective domain, since outside that set
`f y = ⊤` and the inequality is automatic. -/
theorem is_subgradient_at_iff_forall_mem_effective_domain
    (f : E → EReal) (x : E) (g : Module.Dual ℝ E) :
    is_subgradient_at f x g ↔
      x ∈ effective_domain f ∧
        ∀ y ∈ effective_domain f, f y ≥ f x + (g (y - x) : EReal) := by
  constructor
  · rintro ⟨hx, hg⟩
    exact ⟨hx, fun y hy ↦ hg y⟩
  · rintro ⟨hx, hg⟩
    refine ⟨hx, fun y ↦ ?_⟩
    by_cases hy : y ∈ effective_domain f
    · exact hg y hy
    · have hy' : ¬ f y < ⊤ := by
        simpa [effective_domain] using hy
      have hfy_top : f y = ⊤ := le_antisymm le_top (not_lt.mp hy')
      simp [hfy_top]

/-- For a real-valued function, every point lies in the effective domain and the chapter
subgradient predicate reduces to the usual affine lower-support inequality. -/
theorem is_subgradient_at_coe_iff (f : E → ℝ) (x : E) (g : Module.Dual ℝ E) :
    is_subgradient_at (fun y ↦ (f y : EReal)) x g ↔ ∀ y : E, f y ≥ f x + g (y - x) := by
  constructor
  · intro hg y
    have h₀ : (f x : EReal) + (g (y - x) : EReal) ≤ (f y : EReal) := by
      simpa only [ge_iff_le] using hg.2 y
    have h : (((f x + g (y - x) : ℝ) : EReal) ≤ (f y : EReal)) := by
      simpa only [EReal.coe_add] using h₀
    exact EReal.coe_le_coe_iff.mp h
  · intro hg
    refine ⟨by simp [effective_domain], fun y ↦ ?_⟩
    have h₀ : f x + g (y - x) ≤ f y := by
      simpa only [ge_iff_le] using hg y
    have h : (((f x + g (y - x) : ℝ) : EReal) ≤ (f y : EReal)) :=
      EReal.coe_le_coe h₀
    simpa only [ge_iff_le, EReal.coe_add] using h

end

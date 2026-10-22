/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable (C : Set E)

/- Definition 1.11: a subset of a real vector space is convex in the textbook sense precisely when
it satisfies the canonical mathlib predicate `Convex ℝ C`. -/
#check Convex ℝ C

-- Proof sketch: rewrite the claim using `convex_iff_add_mem`; specialize the two coefficients to
-- `t` and `1 - t`, and use the interval hypothesis `t ∈ [0,1]` to obtain the required
-- nonnegativity assumptions.
/-- A subset of a real vector space is convex exactly when it contains every combination
`t • x + (1 - t) • y` of its points with `t ∈ [0,1]`. -/
theorem convex_iff_smul_add_sub_mem :
    Convex ℝ C ↔
      ∀ ⦃x y : E⦄, x ∈ C → y ∈ C → ∀ ⦃t : ℝ⦄, t ∈ Set.Icc (0 : ℝ) 1 →
        t • x + (1 - t) • y ∈ C := by
  constructor
  · intro h
    exact fun {x} {y} hx hy {t} ht ↦
      (convex_iff_add_mem.1 h) hx hy ht.1 (sub_nonneg.2 ht.2) (by ring)
  · intro h
    refine convex_iff_add_mem.2 ?_
    intro x hx y hy a b ha hb hab
    have ha1 : a ≤ (1 : ℝ) := by linarith
    have hb' : b = 1 - a := by linarith
    simpa [hb'] using h hx hy ⟨ha, ha1⟩

end

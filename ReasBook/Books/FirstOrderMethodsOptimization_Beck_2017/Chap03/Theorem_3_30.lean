/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Theorem 3.30 is a `source-facing` Fermat criterion for the chapter owner notion
`subdifferential`. Its primitive data are already owned upstream:
`effective_domain` comes from Chapter 2, while
`subdifferential` is the derived set of `is_subgradient_at` from Definitions 3.1 and 3.2.
This file therefore reuses that owner API directly instead of introducing a parallel local copy.
-/

-- Proof sketch: if `x` minimizes `f` on all of `E`, a point of `effective_domain f` supplies
-- some `y` with `f y < ⊤`, hence also `f x < ⊤`; then the subgradient inequality for the zero
-- functional is
-- exactly the global minimality inequality. Conversely, if `0 ∈ ∂ f(x)`, unfold
-- `subdifferential`; the zero functional kills `y - x`, leaving `f x ≤ f y` for every `y`.
/-- Theorem 3.30: Fermat's optimality condition for the chapter's extended-real subdifferential.
If the effective domain of an extended-real-valued function is nonempty, then a point is a global
minimizer exactly when the zero dual vector belongs to its subdifferential. -/
theorem isMinOn_univ_iff_zero_mem_subdifferential
    {f : E → EReal} (hdom : (effective_domain f).Nonempty) {x : E} :
    IsMinOn f Set.univ x ↔ 0 ∈ subdifferential f x := by
  rw [isMinOn_univ_iff, mem_subdifferential, is_subgradient_at]
  constructor
  · intro hx
    rcases hdom with ⟨y, hy⟩
    refine ⟨lt_of_le_of_lt (hx y) hy, ?_⟩
    intro z
    simpa using hx z
  · rintro ⟨_, hx⟩ y
    simpa using hx y

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The real-valued strong-dual formulation is a `bridge/view` corollary of the source-facing
owner theorem above. The primitive data still belongs to `subdifferential`; `subdifferentialAt`
is only the canonical real-valued view used later in the chapter. -/

/-- Theorem 3.30 in the real-valued strong-dual view: a point globally minimizes `f`
exactly when the zero continuous linear functional belongs to `subdifferentialAt f x`. -/
theorem isMinOn_univ_iff_zero_mem_subdifferentialAt
    {f : E → ℝ} {x : E} :
    IsMinOn f Set.univ x ↔ (0 : StrongDual ℝ E) ∈ subdifferentialAt f x := by
  have hdom : (effective_domain fun y ↦ (f y : EReal)).Nonempty := ⟨x, by simp [effective_domain]⟩
  have hferm :
      IsMinOn (fun y ↦ (f y : EReal)) Set.univ x ↔
        (0 : Module.Dual ℝ E) ∈ subdifferential (fun y ↦ (f y : EReal)) x :=
    isMinOn_univ_iff_zero_mem_subdifferential hdom
  simp [isMinOn_univ_iff, subdifferentialAt, mem_subdifferential,
    is_subgradient_at_coe_iff] at hferm ⊢

end

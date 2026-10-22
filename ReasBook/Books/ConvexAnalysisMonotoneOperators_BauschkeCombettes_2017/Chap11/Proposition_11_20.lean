/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace ERealFunction

variable {H : Type u} [SeminormedAddCommGroup H]

-- Proof sketch: choose a real level `ξ` so that the minimizing-sequence values eventually satisfy
-- `f (x n) ≤ ξ`; Proposition 11.12 makes `lowerLevelSet f ξ` bounded, hence the tail of the
-- sequence is bounded, and adjoining finitely many initial terms preserves boundedness.
/-- Proposition 11.20: every minimizing sequence of a coercive extended-real-valued function is
bounded. -/
theorem isBounded_range_of_isMinimizingSequence_of_coercive
    {f : H → EReal} (hf : Coercive f) {x : ℕ → H} (hx : IsMinimizingSequence f x) :
    Bornology.IsBounded (Set.range x) := by
  let ξ : ℝ := (f (x 0)).toReal + 1
  have hx0_lt_ξ : f (x 0) < (ξ : EReal) := by
    by_cases hx0_bot : f (x 0) = ⊥
    · simpa [ξ, hx0_bot] using EReal.bot_lt_coe ((f (x 0)).toReal + 1)
    · rw [← EReal.coe_toReal (ne_of_lt (hx.lt_top 0)) hx0_bot]
      exact_mod_cast show (f (x 0)).toReal < (f (x 0)).toReal + 1 by linarith
  have hsInf_lt_ξ : sInf (Set.range f) < (ξ : EReal) := by
    exact lt_of_le_of_lt (sInf_le (Set.mem_range_self (x 0))) hx0_lt_ξ
  have hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ) :=
    (coercive_iff_bounded_lowerLevelSet f).1 hf ξ
  have htail : ∀ᶠ n in atTop, x n ∈ lowerLevelSet f ξ := by
    have hle : ∀ᶠ n in atTop, f (x n) ≤ (ξ : EReal) :=
      hx.tendsto.eventually (Iic_mem_nhds hsInf_lt_ξ)
    simpa [lowerLevelSet, Function.comp] using hle
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s₀ : Set H := x '' {n : ℕ | n < N}
  have hs₀_finite : s₀.Finite := by
    classical
    simpa [s₀] using (Set.finite_lt_nat N).image x
  have hrange_subset : Set.range x ⊆ s₀ ∪ lowerLevelSet f ξ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr (hN n (Nat.le_of_not_lt hn))
  exact (hs₀_finite.isBounded.union hlevel_bounded).subset hrange_subset

end ERealFunction

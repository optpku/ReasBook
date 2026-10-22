/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped InnerProductSpace

/-
Fact 2.11: the canonical Cauchy--Schwarz inequality in a real or complex inner product space is
`norm_inner_le_norm`.
-/
recall norm_inner_le_norm
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) :
    ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖

private theorem eq_zero_or_exists_smul_iff_not_linearIndependent_pair
    {𝕜 : Type u} {E : Type v} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (x y : E) :
    (x = 0 ∨ ∃ c : 𝕜, y = c • x) ↔ ¬ LinearIndependent 𝕜 ![x, y] := by
  constructor
  · intro hxy hlin
    rcases hxy with rfl | ⟨c, rfl⟩
    · exact (hlin.ne_zero 0) rfl
    · by_cases hx : x = 0
      · exact (hlin.ne_zero 0) hx
      · rw [LinearIndependent.pair_iff' hx] at hlin
        exact hlin c rfl
  · intro hdep
    by_cases hx : x = 0
    · exact Or.inl hx
    · rw [LinearIndependent.pair_iff' hx, not_forall] at hdep
      rcases hdep with ⟨c, hc⟩
      exact Or.inr ⟨c, (not_ne_iff.mp hc).symm⟩

/-- Fact 2.11: equality in the Cauchy--Schwarz inequality holds exactly when the pair `x, y` is
linearly dependent. Together with `norm_inner_le_norm`, this is the textbook fact. -/
theorem cauchy_schwarz_and_eq_iff_linearly_dependent_pair
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (x y : E) :
    ‖inner 𝕜 x y‖ = ‖x‖ * ‖y‖ ↔ ¬ LinearIndependent 𝕜 ![x, y] := by
  calc
    ‖inner 𝕜 x y‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ c : 𝕜, y = c • x := by
      simpa using (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ ¬ LinearIndependent 𝕜 ![x, y] :=
      eq_zero_or_exists_smul_iff_not_linearIndependent_pair x y

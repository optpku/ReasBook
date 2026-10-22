/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

-- Proof sketch: use nonnegativity to get the uniform lower bound `0 ≤ a n / n`,
-- apply mathlib's owner theorem `Subadditive.tendsto_lim`, and unfold `Subadditive.lim`.
/-- Exercise 20.6.2: if a real sequence is nonnegative and subadditive, then the normalized
sequence `a n / n` converges to the infimum of its values over the positive indices. -/
theorem subadditive_nonnegative_tendsto_div_eq_sInf
    {a : ℕ → ℝ} (ha_nonneg : ∀ n : ℕ, 0 ≤ a n) (hsub : Subadditive a) :
    Tendsto (fun n : ℕ ↦ a n / n) atTop
      (nhds (sInf ((fun n : ℕ ↦ a n / n) '' Set.Ici 1))) := by
  have hbdd : BddBelow (Set.range fun n : ℕ ↦ a n / n) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (ha_nonneg n) (Nat.cast_nonneg n)
  simpa [Subadditive.lim] using hsub.tendsto_lim hbdd

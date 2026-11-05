/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22

open scoped Matrix

/-- Exercise 3.13. The nonemptiness hypothesis in Theorem 3.22 cannot be dropped: for the empty
polyhedron cut out by `0 *ᵥ x ≤ -1`, the inequality `x₀ ≤ 0` is vacuously valid, but there is no
nonnegative row multiplier representation of its left-hand side. -/
theorem empty_polyhedron_counterexample_to_valid_inequality_row_multiplier_characterization :
    let A : Matrix (Fin 1) (Fin 1) ℝ := 0
    let b : Fin 1 → ℝ := fun _ ↦ (-1 : ℝ)
    let c : Fin 1 → ℝ := fun _ ↦ (1 : ℝ)
    is_valid_inequality (polyhedron_le_set A b) c 0 ∧
      ¬ (polyhedron_le_set A b).Nonempty ∧
      ¬ ∃ u : Fin 1 → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b ≤ 0 := by
  dsimp [is_valid_inequality]
  have h_empty :
      ¬ (polyhedron_le_set (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ ↦ (-1 : ℝ))).Nonempty := by
    rintro ⟨x, hx⟩
    have hx0 : (0 : ℝ) ≤ -1 := by
      simpa [polyhedron_le_set] using hx 0
    linarith
  refine ⟨?_, h_empty, ?_⟩
  · intro x hx
    exact False.elim (h_empty ⟨x, hx⟩)
  · rintro ⟨u, hu_nonneg, hu_row, hu_eval⟩
    have hcoord : (0 : ℝ) = 1 := by
      simpa using congrFun hu_row 0
    linarith

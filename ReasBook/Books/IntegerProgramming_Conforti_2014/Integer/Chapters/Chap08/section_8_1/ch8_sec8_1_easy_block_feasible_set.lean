/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1

open scoped Matrix

section EasyBlockFeasibleSet

variable {m n : ℕ}

/-- The easy-block set `Q = {x ∈ ℝ^n_+ | A₂ *ᵥ x ≤ b²}` used in Section 8.1. -/
abbrev easy_block_feasible_set
    (A₂ : Matrix (Fin m) (Fin n) ℝ)
    (b₂ : Fin m → ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A₂ b₂ ∩ Set.Ici (0 : Fin n → ℝ)

/-- Membership in `easy_block_feasible_set A₂ b₂` means satisfying the easy-block inequalities
`A₂ *ᵥ x ≤ b²` together with nonnegativity. -/
theorem mem_easy_block_feasible_set_iff
    {A₂ : Matrix (Fin m) (Fin n) ℝ}
    {b₂ : Fin m → ℝ}
    {x : Fin n → ℝ} :
    x ∈ easy_block_feasible_set A₂ b₂ ↔ A₂ *ᵥ x ≤ b₂ ∧ 0 ≤ x := by
  rw [easy_block_feasible_set, Set.mem_inter_iff, mem_polyhedron_le_set_iff]
  rfl

end EasyBlockFeasibleSet

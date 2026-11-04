/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_1.ch3_sec3_1_theorem_3_1

open scoped BigOperators Matrix

-- Declarations for this item will be appended below by the statement pipeline.

/-- The matrix `A^3` for the three-variable system in the Fourier-elimination example. -/
def example_3_3_A3 : Matrix (Fin 7) (Fin (2 + 1)) ℚ :=
  !![(-1 : ℚ), 0, 0;
    0, -1, 0;
    0, 0, -1;
    -1, -1, 0;
    -1, 0, -1;
    0, -1, -1;
    1, 1, 1]

/-- The right-hand side `b^3` for the three-variable system in the Fourier-elimination example. -/
def example_3_3_b3 : Fin 7 → ℚ :=
  ![(-1 : ℚ), -1, -1, -3, -3, -3, 6]

/-- The matrix `A^2` obtained after eliminating `x_3` in the Fourier-elimination example. -/
def example_3_3_A2 : Matrix (Fin 6) (Fin (1 + 1)) ℚ :=
  !![(-1 : ℚ), 0;
    0, -1;
    -1, -1;
    1, 1;
    0, 1;
    1, 0]

/-- The right-hand side `b^2` obtained after eliminating `x_3` in the Fourier-elimination
example. -/
def example_3_3_b2 : Fin 6 → ℚ :=
  ![(-1 : ℚ), -1, -3, 5, 3, 3]

/-- The backward-substitution point selected in the Fourier-elimination example. -/
def example_3_3_solution : Fin 3 → ℚ :=
  ![(3 : ℚ), 1, 2]

/-- Helper for Example 3.3: the original three-variable matrix system is exactly the displayed list
of seven scalar inequalities. -/
lemma example_3_3_A3_mulVec_le_b3_iff {x1 x2 x3 : ℚ} :
    example_3_3_A3 *ᵥ ![x1, x2, x3] ≤ example_3_3_b3 ↔
      1 ≤ x1 ∧ 1 ≤ x2 ∧ 1 ≤ x3 ∧ 3 ≤ x2 + x1 ∧ 3 ≤ x3 + x1 ∧
        3 ≤ x3 + x2 ∧ x1 + (x2 + x3) ≤ 6 := by
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1' := hx 1
    have hx2' := hx 2
    have hx3' := hx 3
    have hx4' := hx 4
    have hx5' := hx 5
    have hx6 := hx 6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [example_3_3_A3, example_3_3_b3] using hx0
    · simpa [example_3_3_A3, example_3_3_b3] using hx1'
    · simpa [example_3_3_A3, example_3_3_b3] using hx2'
    · simpa [example_3_3_A3, example_3_3_b3] using hx3'
    · simpa [example_3_3_A3, example_3_3_b3] using hx4'
    · simpa [example_3_3_A3, example_3_3_b3] using hx5'
    · simpa [example_3_3_A3, example_3_3_b3] using hx6
  · rintro ⟨hx1, hx2, hx3, hx12, hx13, hx23, hsum⟩
    intro i
    fin_cases i
    · simpa [example_3_3_A3, example_3_3_b3] using hx1
    · simpa [example_3_3_A3, example_3_3_b3] using hx2
    · simpa [example_3_3_A3, example_3_3_b3] using hx3
    · simpa [example_3_3_A3, example_3_3_b3] using hx12
    · simpa [example_3_3_A3, example_3_3_b3] using hx13
    · simpa [example_3_3_A3, example_3_3_b3] using hx23
    · simpa [example_3_3_A3, example_3_3_b3] using hsum

/-- Helper for Example 3.3: the displayed two-variable matrix system is exactly the listed six
scalar inequalities. -/
lemma example_3_3_A2_mulVec_le_b2_iff {x1 x2 : ℚ} :
    example_3_3_A2 *ᵥ ![x1, x2] ≤ example_3_3_b2 ↔
      1 ≤ x1 ∧ 1 ≤ x2 ∧ 3 ≤ x2 + x1 ∧ x1 + x2 ≤ 5 ∧ x2 ≤ 3 ∧ x1 ≤ 3 := by
  constructor
  · intro hx
    have hx0 := hx 0
    have hx1' := hx 1
    have hx2' := hx 2
    have hx3' := hx 3
    have hx4' := hx 4
    have hx5' := hx 5
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [example_3_3_A2, example_3_3_b2] using hx0
    · simpa [example_3_3_A2, example_3_3_b2] using hx1'
    · simpa [example_3_3_A2, example_3_3_b2] using hx2'
    · simpa [example_3_3_A2, example_3_3_b2] using hx3'
    · simpa [example_3_3_A2, example_3_3_b2] using hx4'
    · simpa [example_3_3_A2, example_3_3_b2] using hx5'
  · rintro ⟨hx1, hx2, hx12, hsum, hx2_upper, hx1_upper⟩
    intro i
    fin_cases i
    · simpa [example_3_3_A2, example_3_3_b2] using hx1
    · simpa [example_3_3_A2, example_3_3_b2] using hx2
    · simpa [example_3_3_A2, example_3_3_b2] using hx12
    · simpa [example_3_3_A2, example_3_3_b2] using hsum
    · simpa [example_3_3_A2, example_3_3_b2] using hx2_upper
    · simpa [example_3_3_A2, example_3_3_b2] using hx1_upper

/-- The displayed matrix system `A^2 x ≤ b^2` is exactly the canonical Fourier-Motzkin step for
`A^3 x ≤ b^3`, written in the textbook row order. -/
lemma example_3_3_A2_mulVec_le_b2_iff_fourier_step {x1 x2 : ℚ} :
    example_3_3_A2 *ᵥ ![x1, x2] ≤ example_3_3_b2 ↔
      satisfies_fourier_motzkin_step example_3_3_A3 example_3_3_b3 ![x1, x2] := by
  constructor
  · rw [example_3_3_A2_mulVec_le_b2_iff]
    rintro ⟨hx1, hx2, hx12, hsum, hx2_upper, hx1_upper⟩
    refine (satisfies_fourier_motzkin_step_iff example_3_3_A3 example_3_3_b3 ![x1, x2]).2
      ⟨?_, ?_⟩
    · intro i k hi hk
      fin_cases i <;> fin_cases k <;>
        simp [example_3_3_A3, example_3_3_b3] at hi hk ⊢ <;>
        linarith [hx1, hx2, hx12, hsum, hx2_upper, hx1_upper]
    · intro i hi
      fin_cases i <;>
        simp [example_3_3_A3, example_3_3_b3] at hi ⊢ <;>
        linarith [hx1, hx2, hx12]
  · intro hx
    have h := (satisfies_fourier_motzkin_step_iff example_3_3_A3 example_3_3_b3 ![x1, x2]).1 hx
    refine (example_3_3_A2_mulVec_le_b2_iff).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [example_3_3_A3, example_3_3_b3] using h.2 0 (by decide)
    · simpa [example_3_3_A3, example_3_3_b3] using h.2 1 (by decide)
    · simpa [example_3_3_A3, example_3_3_b3] using h.2 3 (by decide)
    · have hsum : 1 + (x1 + x2) ≤ 6 := by
        simpa [example_3_3_A3, example_3_3_b3] using h.1 6 2 (by decide) (by decide)
      linarith
    · have hx2_upper : 3 + x2 ≤ 6 := by
        simpa [example_3_3_A3, example_3_3_b3] using h.1 6 4 (by decide) (by decide)
      linarith
    · have hx1_upper : 3 + x1 ≤ 6 := by
        simpa [example_3_3_A3, example_3_3_b3] using h.1 6 5 (by decide) (by decide)
      linarith

lemma example_3_3_snoc₂ (x1 x2 x3 : ℚ) : Fin.snoc ![x1, x2] x3 = ![x1, x2, x3] := by
  ext i
  fin_cases i <;> rfl

lemma example_3_3_snoc₁ (x1 x2 : ℚ) : Fin.snoc ![x1] x2 = ![x1, x2] := by
  ext i
  fin_cases i <;> rfl

/-- The canonical Fourier-Motzkin step for the displayed two-variable system reduces to the
interval condition `1 ≤ x_1 ≤ 3`. -/
lemma example_3_3_fourier_step_A2_iff {x1 : ℚ} :
    satisfies_fourier_motzkin_step example_3_3_A2 example_3_3_b2 ![x1] ↔ 1 ≤ x1 ∧ x1 ≤ 3 := by
  rw [satisfies_fourier_motzkin_step_iff]
  constructor
  · rintro ⟨_, hzero⟩
    have h0 : 1 ≤ x1 := by
      simpa [example_3_3_A2, example_3_3_b2] using hzero 0 (by decide)
    have h5 : x1 ≤ 3 := by
      simpa [example_3_3_A2, example_3_3_b2] using hzero 5 (by decide)
    exact ⟨h0, h5⟩
  · rintro ⟨hx1_lower, hx1_upper⟩
    refine ⟨?_, ?_⟩
    · intro i k hi hk
      fin_cases i <;> fin_cases k <;>
        simp [example_3_3_A2, example_3_3_b2] at hi hk ⊢ <;> linarith
    · intro i hi
      fin_cases i <;>
        simp [example_3_3_A2, example_3_3_b2] at hi ⊢ <;> linarith

/-- Eliminating `x_3` from the original system in the Fourier-elimination example yields the
displayed two-variable system `A^2 x ≤ b^2`. -/
theorem example_3_3_eliminate_x3 {x1 x2 : ℚ} :
    example_3_3_A2 *ᵥ ![x1, x2] ≤ example_3_3_b2 ↔
      ∃ x3 : ℚ, example_3_3_A3 *ᵥ ![x1, x2, x3] ≤ example_3_3_b3 := by
  rw [example_3_3_A2_mulVec_le_b2_iff_fourier_step]
  simpa [example_3_3_snoc₂] using
    (fourier_motzkin_step_iff_exists_last_coordinate example_3_3_A3 example_3_3_b3 ![x1, x2])

/-- Eliminating `x_2` from the displayed two-variable system leaves the interval
`1 ≤ x_1 ≤ 3`. -/
theorem example_3_3_eliminate_x2 {x1 : ℚ} :
    1 ≤ x1 ∧ x1 ≤ 3 ↔ ∃ x2 : ℚ, example_3_3_A2 *ᵥ ![x1, x2] ≤ example_3_3_b2 := by
  rw [← example_3_3_fourier_step_A2_iff]
  simpa [example_3_3_snoc₁] using
    (fourier_motzkin_step_iff_exists_last_coordinate example_3_3_A2 example_3_3_b2 ![x1])

/-- Substituting `x_1 = 3` into the displayed two-variable system yields the interval
`1 ≤ x_2 ≤ 2`. -/
theorem example_3_3_substitute_x1 (x2 : ℚ) :
    example_3_3_A2 *ᵥ ![(3 : ℚ), x2] ≤ example_3_3_b2 ↔ 1 ≤ x2 ∧ x2 ≤ 2 := by
  constructor
  · intro hx2
    rw [example_3_3_A2_mulVec_le_b2_iff] at hx2
    rcases hx2 with ⟨_, hx2_lower, _, hsum, _, _⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hx2_lower, hx2_upper⟩
    rw [example_3_3_A2_mulVec_le_b2_iff]
    refine ⟨by norm_num, ?_, ?_, ?_, ?_, by norm_num⟩
    · linarith
    · linarith
    · linarith
    · linarith

/-- Substituting `x_1 = 3` and `x_2 = 1` into the original system forces `x_3 = 2`. -/
theorem example_3_3_substitute_x1_x2 (x3 : ℚ) :
    example_3_3_A3 *ᵥ ![(3 : ℚ), 1, x3] ≤ example_3_3_b3 ↔ x3 = 2 := by
  constructor
  · intro hx3
    rw [example_3_3_A3_mulVec_le_b3_iff] at hx3
    rcases hx3 with ⟨_, _, _, _, _, hx3_lower, hsum⟩
    linarith
  · intro hx3
    subst hx3
    rw [example_3_3_A3_mulVec_le_b3_iff]
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num⟩

/-- Example 3.3. The system obtained by backward substitution from the Fourier-elimination
steps has the feasible solution `x = (3, 1, 2)`. -/
theorem example_3_3_solution_feasible :
    example_3_3_A3 *ᵥ example_3_3_solution ≤ example_3_3_b3 := by
  simpa [example_3_3_solution] using (example_3_3_substitute_x1_x2 (2 : ℚ)).2 rfl

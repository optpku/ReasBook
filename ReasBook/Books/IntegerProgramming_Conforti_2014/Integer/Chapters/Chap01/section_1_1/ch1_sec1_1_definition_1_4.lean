import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.LinearRelaxation
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Objective

open scoped Matrix

section Definition14

variable {m n p : ℕ}

/-- Definition 1.4 (2). Given a linear objective `mixed_linear_objective c h` and a relaxation
set `P'`, the corresponding linear programming relaxation is formalized by the attained objective
values on `P'`. -/
def linear_programming_relaxation_objective_values
    (P' : Set (MixedRealPoint n p))
    (c : Fin n → ℝ)
    (h : Fin p → ℝ) : Set ℝ :=
  mixed_linear_objective c h '' P'

/-- Membership in `linear_programming_relaxation_objective_values P' c h` means that the value is
attained by some point of `P'`. -/
theorem mem_linear_programming_relaxation_objective_values_iff
    {P' : Set (MixedRealPoint n p)}
    {c : Fin n → ℝ}
    {h : Fin p → ℝ}
    {r : ℝ} :
    r ∈ linear_programming_relaxation_objective_values P' c h ↔
      ∃ xy ∈ P', mixed_linear_objective c h xy = r := by
  rw [linear_programming_relaxation_objective_values, Set.mem_image]

end Definition14

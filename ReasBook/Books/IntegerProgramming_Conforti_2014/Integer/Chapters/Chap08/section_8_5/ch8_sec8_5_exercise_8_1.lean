import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_1.ch8_sec8_1_proposition_8_1

section Exercise81

variable {m₁ n : ℕ}

/-- Exercise 8.1. A branch-and-bound node with feasible region `Q` may be fathomed using a
nonnegative Lagrangian bound `z_LR(λ)` in place of the usual LP bound once the incumbent value
already dominates that Lagrangian upper bound. -/
def branch_and_bound_lagrangian_fathoms_node
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (incumbent : ℝ) : Prop :=
  lagrangian_relaxation_value A₁ b₁ c Q lam ≤ (incumbent : EReal)

/-- If the incumbent dominates the chosen nonnegative Lagrangian bound at a node, then it also
dominates the true integer-program value of that node, so fathoming is sound. -/
theorem branch_and_bound_lagrangian_fathoms_node_spec
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (c : Fin n → ℝ)
    (Q : Set (Fin n → ℝ))
    (lam : Fin m₁ → ℝ)
    (incumbent : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hfathom : branch_and_bound_lagrangian_fathoms_node A₁ b₁ c Q lam incumbent) :
    integer_program_value A₁ b₁ c Q ≤ (incumbent : EReal) :=
  le_trans (lagrangian_relaxation_value_ge_integer_program_value A₁ b₁ c Q lam hlam) hfathom

end Exercise81

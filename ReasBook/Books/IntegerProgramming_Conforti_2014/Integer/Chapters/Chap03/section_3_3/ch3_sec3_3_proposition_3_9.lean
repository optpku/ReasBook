import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_theorem_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

/-- The dual feasible region is nonempty exactly when every primal recession direction has
nonpositive objective slope. This is Theorem 3.5 applied to `Aᵀ`. -/
lemma dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    Set.Nonempty (dual_feasible_region A c) ↔
      ∀ y : Fin n → ℝ, A *ᵥ y ≤ 0 → c ⬝ᵥ y ≤ 0 := by
  simpa [dual_feasible_region, Matrix.mulVec_transpose, Matrix.vecMul_transpose, dotProduct_comm]
    using feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers Aᵀ c

/-- A feasible point together with a recession direction of positive objective slope forces the
primal objective set to be unbounded above. -/
lemma primal_objective_values_not_bddAbove_of_improving_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    {y : Fin n → ℝ}
    (hyA : A *ᵥ y ≤ 0)
    (hyc : 0 < c ⬝ᵥ y) :
    ¬ BddAbove (primal_objective_values A b c) := by
  rcases hP with ⟨x₀, hx₀⟩
  have hx₀_feas := (mem_primal_feasible_region_iff A b x₀).mp hx₀
  intro hbounded
  rcases hbounded with ⟨M, hM⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (M - c ⬝ᵥ x₀) / (c ⬝ᵥ y) < N := by
    exact exists_nat_gt ((M - c ⬝ᵥ x₀) / (c ⬝ᵥ y))
  have hNmul : M - c ⬝ᵥ x₀ < (N : ℝ) * (c ⬝ᵥ y) := by
    exact (div_lt_iff₀ hyc).mp hN
  have hN' : M < c ⬝ᵥ x₀ + (N : ℝ) * (c ⬝ᵥ y) := by
    linarith
  let xN : Fin n → ℝ := x₀ + (N : ℝ) • y
  have hxN : xN ∈ primal_feasible_region A b := by
    rw [mem_primal_feasible_region_iff]
    intro i
    have hyi : (N : ℝ) * (A *ᵥ y) i ≤ 0 := by
      have hNnonneg : 0 ≤ (N : ℝ) := by
        exact_mod_cast Nat.zero_le N
      exact mul_nonpos_of_nonneg_of_nonpos hNnonneg (hyA i)
    calc
      (A *ᵥ xN) i = (A *ᵥ x₀) i + (N : ℝ) * (A *ᵥ y) i := by
        simp [xN, Matrix.mulVec_add, Matrix.mulVec_smul]
      _ ≤ b i + 0 := by
        nlinarith [hx₀_feas i, hyi]
      _ = b i := by
        ring
  have hxN_value : M < c ⬝ᵥ xN := by
    calc
      M < c ⬝ᵥ x₀ + (N : ℝ) * (c ⬝ᵥ y) := hN'
      _ = c ⬝ᵥ xN := by
        simp [xN, dotProduct_add, dotProduct_smul]
  exact (not_lt_of_ge (hM ⟨xN, hxN, rfl⟩)) hxN_value

/-- Proposition 3.9 (1). Let `P = {x | A *ᵥ x ≤ b}` and
`D = {u | u ᵥ* A = c ∧ 0 ≤ u}`, and assume `P` is nonempty. Then the primal objective
`{c ⬝ᵥ x | x ∈ P}` is unbounded above if and only if `D` is empty. -/
theorem primal_objective_unbounded_iff_dual_feasible_region_empty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b)) :
    ¬ BddAbove (primal_objective_values A b c) ↔
      dual_feasible_region A c = (∅ : Set (Fin m → ℝ)) := by
  classical
  constructor
  · intro hunbounded
    by_contra hD
    have hDnonempty : Set.Nonempty (dual_feasible_region A c) := by
      rw [← Set.not_nonempty_iff_eq_empty] at hD
      exact not_not.mp hD
    exact hunbounded (primal_objective_values_bddAbove_of_dual_nonempty A b c hDnonempty)
  · intro hD
    have hDempty : ¬ Set.Nonempty (dual_feasible_region A c) := by
      rwa [Set.not_nonempty_iff_eq_empty]
    have hnotforall :
        ¬ ∀ y : Fin n → ℝ, A *ᵥ y ≤ 0 → c ⬝ᵥ y ≤ 0 := by
      intro hforall
      exact hDempty
        ((dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 hforall)
    rcases not_forall.mp hnotforall with ⟨y, hy⟩
    rcases Classical.not_imp.mp hy with ⟨hyA, hyc⟩
    exact primal_objective_values_not_bddAbove_of_improving_direction A b c hP hyA
      (lt_of_not_ge hyc)

/-- Proposition 3.9 (2). Let `P = {x | A *ᵥ x ≤ b}` and
`D = {u | u ᵥ* A = c ∧ 0 ≤ u}`, and assume `P` is nonempty. Then the primal objective
`{c ⬝ᵥ x | x ∈ P}` is unbounded above if and only if there exists a vector `y` such that
`A *ᵥ y ≤ 0` and `c ⬝ᵥ y > 0`. -/
theorem primal_objective_unbounded_iff_exists_improving_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b)) :
    ¬ BddAbove (primal_objective_values A b c) ↔
      ∃ y : Fin n → ℝ, A *ᵥ y ≤ 0 ∧ c ⬝ᵥ y > 0 := by
  classical
  constructor
  · intro hunbounded
    by_contra hdir
    have hforall : ∀ y : Fin n → ℝ, A *ᵥ y ≤ 0 → c ⬝ᵥ y ≤ 0 := by
      intro y hyA
      by_contra hyc
      exact hdir ⟨y, hyA, lt_of_not_ge hyc⟩
    have hD : Set.Nonempty (dual_feasible_region A c) :=
      (dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 hforall
    exact hunbounded (primal_objective_values_bddAbove_of_dual_nonempty A b c hD)
  · rintro ⟨y, hyA, hyc⟩
    exact primal_objective_values_not_bddAbove_of_improving_direction A b c hP hyA hyc

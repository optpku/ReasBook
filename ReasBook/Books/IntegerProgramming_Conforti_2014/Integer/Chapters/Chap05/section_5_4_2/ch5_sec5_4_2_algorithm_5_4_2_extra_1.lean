import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators Matrix

section Algorithm542Extra1

variable {n p : ℕ} (hp : p ≤ n)
variable (StageRow RestrictedRow : ℕ → Type)

/-- A linear inequality `α x ≤ β` that can be appended to a stage relaxation as a cut. -/
structure lift_project_cut (n : ℕ) where
  coeff : Fin n → ℝ
  rhs : ℝ

namespace lift_project_cut

/-- The point `x` satisfies the lift-and-project cut `α x ≤ β`. -/
def Satisfied {n : ℕ} (cut : lift_project_cut n) (x : Fin n → ℝ) : Prop :=
  (∑ i, cut.coeff i * x i) ≤ cut.rhs

end lift_project_cut

/-- An auxiliary LP solution records the pair `(u¹, u²)` used to derive a `j`-cut from the
restricted system `A^{k,j-1} x ≤ b^{k,j-1}`. -/
structure lift_project_auxiliary_solution (Row : Type) where
  u1 : Row → ℝ
  u2 : Row → ℝ

/-- The first `p` coordinates of `x` satisfy the binary constraints of the mixed `0,1` problem. -/
def has_binary_prefix (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin p, x (Fin.castLE hp i) = 0 ∨ x (Fin.castLE hp i) = 1

/-- The binary-block coordinate indexed by `j` is fractional. -/
def is_fractional_binary_index (x : Fin n → ℝ) (j : Fin p) : Prop :=
  0 < x (Fin.castLE hp j) ∧ x (Fin.castLE hp j) < 1

/-- The index `j` is the largest binary-block index with fractional value. -/
def is_largest_fractional_binary_index (x : Fin n → ℝ) (j : Fin p) : Prop :=
  is_fractional_binary_index hp x j ∧
    ∀ i : Fin p, j < i → ¬ is_fractional_binary_index hp x i

/-- A stage-indexed execution of Algorithm 5.4.2-extra-1 records the current relaxation
`Aᵏ x ≤ bᵏ`, the restricted system `A^{k,j-1} x ≤ b^{k,j-1}`, the selected binary index `j`,
the auxiliary solution `(u¹, u²)`, and the generated `j`-cut at each stage. -/
structure specialized_lift_project_execution
    (n p : ℕ) (StageRow RestrictedRow : ℕ → Type) where
  stage_matrix : ∀ k, Matrix (StageRow k) (Fin n) ℝ
  stage_rhs : ∀ k, StageRow k → ℝ
  basic_solution : ℕ → Fin n → ℝ
  selected_index : ℕ → Fin p
  restricted_matrix : ∀ k, Matrix (RestrictedRow k) (Fin n) ℝ
  restricted_rhs : ∀ k, RestrictedRow k → ℝ
  auxiliary_solution : ∀ k, lift_project_auxiliary_solution (RestrictedRow k)
  generated_cut : ℕ → lift_project_cut n

namespace specialized_lift_project_execution

section

variable {StageRow RestrictedRow : ℕ → Type}

variable (execution : specialized_lift_project_execution n p StageRow RestrictedRow)
variable (c : Fin n → ℝ)
variable
    (is_optimal_basic_solution_of_stage :
      ∀ k, (Fin n → ℝ) → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        (Fin n → ℝ) → Prop)
    (is_optimal_original_solution : (Fin n → ℝ) → Prop)
    (is_restricted_system :
      ∀ k, Fin p → Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) →
        Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) → Prop)
    (is_optimal_basic_solution_of_auxiliary_lp :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → Prop)
    (is_j_cut_of_auxiliary_solution :
      ∀ k, Fin p → Matrix (RestrictedRow k) (Fin n) ℝ → (RestrictedRow k → ℝ) →
        lift_project_auxiliary_solution (RestrictedRow k) → lift_project_cut n → Prop)
    (next_stage_adds_cut :
      ∀ k, Matrix (StageRow k) (Fin n) ℝ → (StageRow k → ℝ) → lift_project_cut n →
        Matrix (StageRow (k + 1)) (Fin n) ℝ → (StageRow (k + 1) → ℝ) → Prop)

/-- The selected binary index viewed as optional, with `none` exactly at terminal stages where the
current basic solution already satisfies the binary restrictions. -/
noncomputable def selectedIndexOption (k : ℕ) : Option (Fin p) :=
  open Classical in
  if has_binary_prefix hp (execution.basic_solution k) then
    none
  else
    some (execution.selected_index k)

/-- The optional selected-index view is `none` exactly at stages where the current basic solution
satisfies the binary restrictions on the first `p` coordinates. -/
theorem selectedIndexOption_eq_none_iff (k : ℕ) :
    execution.selectedIndexOption hp k = none ↔
      has_binary_prefix hp (execution.basic_solution k) := by
  -- Split on the textbook stopping test so each branch unfolds the `if` in `selectedIndexOption`.
  by_cases hk : has_binary_prefix hp (execution.basic_solution k)
  · simp [selectedIndexOption, hk]
  · simp [selectedIndexOption, hk]

/-- The optional selected-index view is `some j` exactly at nonterminal stages, in which case the
stored selected index is exposed. -/
theorem selectedIndexOption_eq_some_selectedIndex_iff (k : ℕ) :
    execution.selectedIndexOption hp k = some (execution.selected_index k) ↔
      ¬ has_binary_prefix hp (execution.basic_solution k) := by
  -- The same stop/nonstop case split converts the optional view into the branch predicate.
  by_cases hk : has_binary_prefix hp (execution.basic_solution k)
  · simp [selectedIndexOption, hk]
  · simp [selectedIndexOption, hk]

/-- The stage-`k` clause of Algorithm 5.4.2-extra-1 for the recorded relaxation `Aᵏ x ≤ bᵏ`,
the restricted system `A^{k,j-1} x ≤ b^{k,j-1}`, the selected binary index `j`, the auxiliary
solution `(u¹, u²)`, and the generated `j`-cut. -/
def StagewiseClause (k : ℕ) : Prop :=
  is_optimal_basic_solution_of_stage k c (execution.stage_matrix k) (execution.stage_rhs k)
      (execution.basic_solution k) ∧
    (has_binary_prefix hp (execution.basic_solution k) →
      is_optimal_original_solution (execution.basic_solution k)) ∧
    (¬ has_binary_prefix hp (execution.basic_solution k) →
      is_largest_fractional_binary_index hp
          (execution.basic_solution k) (execution.selected_index k) ∧
        is_restricted_system k (execution.selected_index k)
          (execution.stage_matrix k) (execution.stage_rhs k)
          (execution.restricted_matrix k) (execution.restricted_rhs k) ∧
        is_optimal_basic_solution_of_auxiliary_lp k (execution.selected_index k)
          (execution.restricted_matrix k) (execution.restricted_rhs k)
          (execution.auxiliary_solution k) ∧
        is_j_cut_of_auxiliary_solution k (execution.selected_index k)
          (execution.restricted_matrix k) (execution.restricted_rhs k)
          (execution.auxiliary_solution k) (execution.generated_cut k) ∧
        next_stage_adds_cut k (execution.stage_matrix k) (execution.stage_rhs k)
          (execution.generated_cut k) (execution.stage_matrix (k + 1))
          (execution.stage_rhs (k + 1)))

/-- Algorithm 5.4.2-extra-1: a stage-indexed execution satisfies the textbook stagewise clause
at every stage. -/
@[mk_iff isAlgorithm_iff]
class IsAlgorithm : Prop where
  stagewise : ∀ k,
    execution.StagewiseClause hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut k

variable [h :
  execution.IsAlgorithm hp c is_optimal_basic_solution_of_stage
    is_optimal_original_solution is_restricted_system
    is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
    next_stage_adds_cut]

/-- An execution of Algorithm 5.4.2-extra-1 satisfies the stagewise clause at every stage. -/
theorem stagewise (k : ℕ) :
    execution.StagewiseClause hp c is_optimal_basic_solution_of_stage
      is_optimal_original_solution is_restricted_system
      is_optimal_basic_solution_of_auxiliary_lp is_j_cut_of_auxiliary_solution
      next_stage_adds_cut k := by
  -- Expose the packaged stagewise clause by projecting the single field of `IsAlgorithm`.
  exact h.stagewise k

end

end specialized_lift_project_execution

end Algorithm542Extra1

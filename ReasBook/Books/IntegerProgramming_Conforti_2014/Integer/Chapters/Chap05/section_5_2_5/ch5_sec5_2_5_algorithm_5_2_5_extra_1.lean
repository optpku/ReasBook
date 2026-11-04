/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Rat
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_5.ch5_sec5_2_5_theorem_5_19

open IsLocalization

-- Semantic recall note: this file reuses the Chapter 5 lexicographic owner vocabulary from
-- Theorem 5.19 and adds only the finer source-facing stage-by-stage execution interface.

-- Declarations for this item will be appended below by the statement pipeline.

section Algorithm525Extra1

variable {n : ℕ}

/-- An affine inequality in `k` variables, written `a · x ≤ β`. -/
structure affine_cut (k : ℕ) where
  coeff : Fin k → ℚ
  rhs : ℚ

namespace affine_cut

/-- The coefficients of the original decision variables `x̄₁, ..., x̄ₙ` inside a stage cut whose
coordinates are ordered as `x̄₀, x̄₁, ..., x̄ₙ` followed by the previously introduced cut
variables. -/
def decisionCoeff {n t : ℕ} (cut : affine_cut (n + t + 1)) : Fin n → ℚ :=
  fun j ↦
    cut.coeff
      ⟨j.1.succ, by
        exact Nat.lt_succ_iff.mpr
          (le_trans (Nat.succ_le_of_lt j.isLt) (Nat.le_add_right n t))⟩

/-- The original decision-variable columns that contribute nontrivially to the Gomory fractional
cut obtained from the recorded stage cut. -/
def decisionColumns {n t : ℕ} (cut : affine_cut (n + t + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ Int.fract (cut.decisionCoeff j) ≠ 0

end affine_cut

/-- A stage-`t` basic solution for Gomory's lexicographic method records `x̄₀`, the original
variables `x̄₁, ..., x̄ₙ`, and the `t` additional variables introduced by previously added cuts. -/
structure gomory_lex_stage_solution (n t : ℕ) where
  objective_value : ℚ
  decision_value : Fin n → ℚ
  cut_value : Fin t → ℚ

namespace gomory_lex_stage_solution

/-- The coordinate `x̄_h` for `h ∈ {0, ..., n}`, with `h = 0` corresponding to `x̄₀`. -/
def prefix_value {n t : ℕ} (xbar : gomory_lex_stage_solution n t) : Fin (n + 1) → ℚ :=
  Fin.cases xbar.objective_value xbar.decision_value

end gomory_lex_stage_solution

/-- A rational number is integral exactly when its real image lies in the integer-coordinate subset
used by the Chapter 5 lexicographic owner. -/
theorem rat_cast_mem_intCast_range_iff (q : ℚ) :
    ((q : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ)) ↔ IsInteger ℤ q := by
  rw [Rat.isLocalizationIsInteger_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by exact_mod_cast hz⟩

/-- The original decision variables `x̄₁, ..., x̄ₙ` are integral. -/
def has_integral_decision_part {n t : ℕ} (xbar : gomory_lex_stage_solution n t) : Prop :=
  ∀ i : Fin n, IsInteger ℤ (xbar.decision_value i)

/-- The index `h` is the smallest index in `{0, ..., n}` whose corresponding prefix coordinate of
the basic solution is fractional. -/
def is_smallest_fractional_prefix_index
    {n t : ℕ} (xbar : gomory_lex_stage_solution n t) (h : Fin (n + 1)) : Prop :=
  ¬ IsInteger ℤ (xbar.prefix_value h) ∧
    ∀ j : Fin (n + 1), j < h → IsInteger ℤ (xbar.prefix_value j)

/-- The smallest fractional prefix index, when it exists, is unique. -/
theorem eq_of_is_smallest_fractional_prefix_index
    {n t : ℕ}
    {xbar : gomory_lex_stage_solution n t}
    {h k : Fin (n + 1)}
    (hh : is_smallest_fractional_prefix_index xbar h)
    (hk : is_smallest_fractional_prefix_index xbar k) :
    h = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hh.1 (hk.2 h hlt)
  · exact hk.1 (hh.2 k hgt)

/-- Helper for Algorithm 5.2.5-extra-1: if every prefix coordinate `x̄₀, …, x̄ₙ` is integral,
then the original decision variables are integral as well. -/
theorem has_integral_decision_part_of_prefix_integral
    {n t : ℕ}
    {xbar : gomory_lex_stage_solution n t}
    (hall : ∀ i : Fin (n + 1), IsInteger ℤ (xbar.prefix_value i)) :
    has_integral_decision_part xbar := by
  -- The decision coordinates are exactly the nonzero prefix coordinates.
  intro i
  simpa [gomory_lex_stage_solution.prefix_value] using hall i.succ

/-- A stage-indexed execution of Gomory's lexicographic cutting plane method records the chosen
lexicographically optimal bases, the selected fractional row index, and the cut added at each
nonterminal stage. The associated basic solution is the canonical one attached to the recorded
basis via `basic_solution_of`. -/
structure gomory_lexicographic_execution
    (n : ℕ) (Basis : ℕ → Type) where
  basis : ∀ t, Basis t
  fractional_index : ℕ → Fin (n + 1)
  generated_cut : ∀ t, affine_cut (n + t + 1)

namespace gomory_lexicographic_execution

/-- The basic solution attached to the recorded stage-`t` basis. -/
abbrev stage_solution
    {n : ℕ} {Basis : ℕ → Type}
    (execution : gomory_lexicographic_execution n Basis)
    (basic_solution_of : ∀ t, Basis t → gomory_lex_stage_solution n t)
    (t : ℕ) : gomory_lex_stage_solution n t :=
  basic_solution_of t (execution.basis t)

section

variable {Basis : ℕ → Type}
variable (execution : gomory_lexicographic_execution n Basis)
variable (stage_has_solution : ℕ → Prop)
variable (is_lexicographically_optimal_basis : ∀ t, Basis t → Prop)
variable (basic_solution_of : ∀ t, Basis t → gomory_lex_stage_solution n t)
variable (original_problem_infeasible : Prop)
variable (is_optimal_original_solution : (Fin n → ℚ) → Prop)
variable (is_cut_generated_from_tableau_row :
  ∀ {t}, Basis t → Fin (n + 1) → affine_cut (n + t + 1) → Prop)
variable (next_stage_adds_cut : ∀ t, affine_cut (n + t + 1) → Prop)

/-- The stagewise clause from Algorithm 5.2.5-extra-1 at stage `t`. -/
def StagewiseClause (t : ℕ) : Prop :=
  (¬ stage_has_solution t → original_problem_infeasible) ∧
    (stage_has_solution t →
      is_lexicographically_optimal_basis t (execution.basis t) ∧
        (has_integral_decision_part (execution.stage_solution basic_solution_of t) →
          is_optimal_original_solution
            (execution.stage_solution basic_solution_of t).decision_value) ∧
          (¬ has_integral_decision_part (execution.stage_solution basic_solution_of t) →
            is_smallest_fractional_prefix_index
                (execution.stage_solution basic_solution_of t)
                (execution.fractional_index t) ∧
              is_cut_generated_from_tableau_row
                (execution.basis t) (execution.fractional_index t)
                (execution.generated_cut t) ∧
                next_stage_adds_cut t (execution.generated_cut t)))

/-- A stage-indexed execution refines a Chapter 5 lexicographic
cutting-plane method when the owner iterate is the real-valued prefix of each stage solution, the
canonical method cut data is the original-variable part of the recorded generated cut, and the
remaining recorded data satisfy the textbook stagewise clause. -/
@[mk_iff refines_iff]
class Refines (method : GomoryLexicographicCuttingPlaneMethod n) : Prop where
  /-- The Chapter 5 iterate is the real-valued prefix of the stage solution attached to the
  recorded stage basis. -/
  iterates_eq :
    ∀ t,
      method.iterates t =
        fun h ↦ ((execution.stage_solution basic_solution_of t).prefix_value h : ℝ)
  /-- The Chapter 5 cut columns are the original-variable columns with nonzero fractional
  coefficient in the recorded stage cut. -/
  cutColumns_eq :
    ∀ t, method.cutColumns t = (execution.generated_cut t).decisionColumns
  /-- The Chapter 5 cut coefficients are the original-variable coefficients of the recorded stage
  cut. -/
  cutCoeff_eq :
    ∀ t, method.cutCoeff t = (execution.generated_cut t).decisionCoeff
  /-- The Chapter 5 cut right-hand side is the right-hand side of the recorded stage cut. -/
  cutRhs_eq :
    ∀ t, method.cutRhs t = (execution.generated_cut t).rhs
  /-- Whenever the execution records that the next stage is obtained by adjoining its generated
  cut, the Chapter 5 relaxation step is exactly the cut induced by the original-variable part of
  that recorded cut. -/
  next_stage_eq :
    ∀ t,
      next_stage_adds_cut t (execution.generated_cut t) →
        method.relaxation (t + 1) =
          method.relaxation t ∩
            gomory_fractional_cut
              (execution.generated_cut t).decisionColumns
              (execution.generated_cut t).decisionCoeff
              (execution.generated_cut t).rhs
  /-- The stagewise clause of Algorithm 5.2.5-extra-1 holds at every stage. -/
  stagewise : ∀ t,
    execution.StagewiseClause stage_has_solution is_lexicographically_optimal_basis
      basic_solution_of original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut t

variable {method : GomoryLexicographicCuttingPlaneMethod n}

/-- In a refining execution, the Chapter 5 iterate is the real-valued prefix of the recorded
stage solution. -/
theorem iterates_eq
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    (t : ℕ) :
    method.iterates t =
      fun h ↦ ((execution.stage_solution basic_solution_of t).prefix_value h : ℝ) :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.iterates_eq t

/-- In a refining execution, the Chapter 5 cut columns are exactly the original-variable columns
of the recorded stage cut with nonzero fractional coefficient. -/
theorem cutColumns_eq
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    (t : ℕ) :
    method.cutColumns t = (execution.generated_cut t).decisionColumns :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.cutColumns_eq t

/-- In a refining execution, the Chapter 5 cut coefficients are the original-variable
coefficients of the recorded stage cut. -/
theorem cutCoeff_eq
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    (t : ℕ) :
    method.cutCoeff t = (execution.generated_cut t).decisionCoeff :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.cutCoeff_eq t

/-- In a refining execution, the Chapter 5 cut right-hand side is the recorded stage cut
right-hand side. -/
theorem cutRhs_eq
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    (t : ℕ) :
    method.cutRhs t = (execution.generated_cut t).rhs :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.cutRhs_eq t

/-- In a refining execution, any recorded next-stage cut addition agrees with the canonical
Chapter 5 relaxation step determined by the original-variable part of the recorded stage cut. -/
theorem next_stage_eq
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    {t : ℕ}
    (hnext : next_stage_adds_cut t (execution.generated_cut t)) :
    method.relaxation (t + 1) =
      method.relaxation t ∩
        gomory_fractional_cut
          (execution.generated_cut t).decisionColumns
          (execution.generated_cut t).decisionCoeff
          (execution.generated_cut t).rhs :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.next_stage_eq t hnext

/-- In a refining execution, the textbook stagewise clause holds at every stage. -/
theorem stagewise
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    (t : ℕ) :
    execution.StagewiseClause stage_has_solution is_lexicographically_optimal_basis
      basic_solution_of original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut t :=
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  hrefines.stagewise t

/-- In a refining execution, every recorded nonterminal stage identifies the canonical Chapter 5
relaxation step using the method's own cut fields. -/
theorem relaxation_step_eq_of_stage_has_solution_of_nonintegral_decision_part
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    {t : ℕ}
    (ht : stage_has_solution t)
    (hnonint : ¬ has_integral_decision_part (execution.stage_solution basic_solution_of t)) :
    method.relaxation (t + 1) =
      method.relaxation t ∩
        gomory_fractional_cut (method.cutColumns t) (method.cutCoeff t) (method.cutRhs t) := by
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  have hnext :
      next_stage_adds_cut t (execution.generated_cut t) :=
    ((hrefines.stagewise t).2 ht).2.2 hnonint |>.2.2
  rw [hrefines.cutColumns_eq t, hrefines.cutCoeff_eq t, hrefines.cutRhs_eq t]
  exact hrefines.next_stage_eq t hnext

/-- Algorithm 5.2.5-extra-1: in a refining execution, every solved stage with nonintegral decision
part selects exactly the recorded smallest fractional prefix index. -/
theorem selectedRow_eq_some_fractional_index_of_stage_has_solution_of_nonintegral_decision_part
    [execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
      original_problem_infeasible is_optimal_original_solution
      is_cut_generated_from_tableau_row next_stage_adds_cut method]
    {t : ℕ}
    (ht : stage_has_solution t)
    (hnonint : ¬ has_integral_decision_part (execution.stage_solution basic_solution_of t)) :
    method.selectedRow t = some (execution.fractional_index t) := by
  let xbar := execution.stage_solution basic_solution_of t
  -- Read the owner iterate in the same coordinates as the recorded stage solution.
  let hrefines :
      execution.Refines stage_has_solution is_lexicographically_optimal_basis basic_solution_of
        original_problem_infeasible is_optimal_original_solution
        is_cut_generated_from_tableau_row next_stage_adds_cut method := inferInstance
  have hiter :
      method.iterates t = fun i ↦ (xbar.prefix_value i : ℝ) := by
    simpa [xbar] using hrefines.iterates_eq t
  cases hrow : method.selectedRow t with
  | none =>
      -- If no row is selected, every owner coordinate is integral, hence every prefix coordinate
      -- of the recorded stage solution is integral as well.
      have hall : ∀ i : Fin (n + 1), IsInteger ℤ (xbar.prefix_value i) := by
        intro i
        have hi :
            method.iterates t i ∈ Set.range (Int.cast : ℤ → ℝ) :=
          (method.selectedRow_none_iff t).1 hrow i
        have hi' : ((xbar.prefix_value i : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ)) := by
          simpa [hiter] using hi
        exact (rat_cast_mem_intCast_range_iff (xbar.prefix_value i)).1 hi'
      -- Prefix integrality contradicts the assumed nonintegral decision part.
      exact (hnonint (has_integral_decision_part_of_prefix_integral hall)).elim
  | some k =>
      -- A selected owner row is exactly a smallest fractional prefix coordinate after transport
      -- along the iterate comparison.
      have hk : is_smallest_fractional_prefix_index xbar k := by
        refine ⟨?_, ?_⟩
        · intro hk_int
          have hk' : ((xbar.prefix_value k : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ)) :=
            (rat_cast_mem_intCast_range_iff (xbar.prefix_value k)).2 hk_int
          have hk'' : method.iterates t k ∈ Set.range (Int.cast : ℤ → ℝ) := by
            simpa [hiter] using hk'
          exact (method.selectedRow_spec hrow).2 hk''
        · intro j hj
          have hj' :
              method.iterates t j ∈ Set.range (Int.cast : ℤ → ℝ) :=
            (method.selectedRow_spec hrow).1 j hj
          have hj'' : ((xbar.prefix_value j : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ)) := by
            simpa [hiter] using hj'
          exact (rat_cast_mem_intCast_range_iff (xbar.prefix_value j)).1 hj''
      have hsmallest :
          is_smallest_fractional_prefix_index xbar (execution.fractional_index t) :=
        ((hrefines.stagewise t).2 ht).2.2 hnonint |>.1
      have hk_eq : k = execution.fractional_index t :=
        eq_of_is_smallest_fractional_prefix_index hk hsmallest
      subst k
      rfl

end

end gomory_lexicographic_execution

end Algorithm525Extra1

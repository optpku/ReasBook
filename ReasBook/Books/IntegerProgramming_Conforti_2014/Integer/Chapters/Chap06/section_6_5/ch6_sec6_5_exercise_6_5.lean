/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

open scoped BigOperators Matrix

namespace Exercise65Core

variable {I N : Type}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the mixed-integer tableau
lattice consists of points with integral coordinates on the left summand. -/
def tableau_mixed_integer_lattice : Set (Sum I N → ℝ) :=
  {x | ∀ i : I, ∃ z : ℤ, x (Sum.inl i) = (z : ℝ)}

section Tableau

variable [Fintype N]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the rational tableau
relaxation records its row equations and nonnegative nonbasic coordinates. -/
abbrev rationalTableauCornerRelaxation
    (abar : I → N → ℚ)
    (bbar : I → ℚ) : Set (Sum I N → ℝ) :=
  {x |
    (∀ i : I,
      x (Sum.inl i) = (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j)) ∧
      ∀ j : N, 0 ≤ x (Sum.inr j)}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: membership in the rational
tableau relaxation exposes its row equations and nonnegativity conditions. -/
@[simp] theorem mem_rationalTableauCornerRelaxation_iff
    (abar : I → N → ℚ)
    (bbar : I → ℚ)
    (x : Sum I N → ℝ) :
    x ∈ rationalTableauCornerRelaxation abar bbar ↔
      (∀ i : I,
        x (Sum.inl i) = (bbar i : ℝ) - ∑ j : N, (abar i j : ℝ) * x (Sum.inr j)) ∧
        ∀ j : N, 0 ≤ x (Sum.inr j) := by
  -- The local tableau set was defined directly by these two conditions.
  exact Iff.rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the tableau apex has the
right-hand side on basic coordinates and zero on nonbasic coordinates. -/
def tableauCornerBasePoint
    (bbar : I → ℚ) : Sum I N → ℝ :=
  Sum.elim (fun i ↦ (bbar i : ℝ)) (fun _ ↦ 0)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the tableau apex satisfies
every row equation and every nonbasic nonnegativity constraint. -/
theorem tableauCornerBasePoint_mem_rationalTableauCornerRelaxation
    (abar : I → N → ℚ)
    (bbar : I → ℚ) :
    tableauCornerBasePoint bbar ∈ rationalTableauCornerRelaxation abar bbar := by
  -- Zero nonbasic coordinates make the row sums vanish and satisfy nonnegativity.
  refine (mem_rationalTableauCornerRelaxation_iff abar bbar _).2 ⟨?_, ?_⟩
  · intro i
    simp [tableauCornerBasePoint]
  · intro j
    simp [tableauCornerBasePoint]

end Tableau

end Exercise65Core

open Exercise65Core

-- This exercise uses the small local tableau interface above and adds the exercise-specific
-- data: integrality of the nonbasic block and the reduced-cost objective. Keeping that interface
-- local avoids importing unrelated later infrastructure through the Chapter 6.1 owner module.
-- Domain sampling for this file:
-- * primary domain: tableau relaxations and attained objective-value sets
-- * core/canonical owners reused directly:
--   `rationalTableauCornerRelaxation`, `tableau_mixed_integer_lattice`, `IsGreatest`
-- * objective-value owner precedent inspected:
--   `primal_objective_values`, `sdp_primal_objective_values`

section Exercise65

variable {B N : Type} [Fintype N]

/-- The feasible region of the pure Gomory relaxation: the Chapter 6.1 tableau relaxation together
with integrality of the nonbasic block. -/
def pure_gomory_relaxation_feasible_region
    (abar : B → N → ℚ)
    (bbar : B → ℚ) : Set (Sum B N → ℝ) :=
  {x |
    x ∈ rationalTableauCornerRelaxation abar bbar ∧
      ∀ j : N, ∃ z : ℤ, x (Sum.inr j) = (z : ℝ)}

/-- The source-facing feasible region coincides with the Chapter 6.1 tableau relaxation together
with the mixed-integer lattice condition on the nonbasic block after swapping summands. -/
theorem pure_gomory_relaxation_feasible_region.eq_inter_swap_mixed_integer_lattice
    (abar : B → N → ℚ)
    (bbar : B → ℚ) :
    pure_gomory_relaxation_feasible_region abar bbar =
      rationalTableauCornerRelaxation abar bbar ∩
        {x | x ∘ Sum.swap ∈ tableau_mixed_integer_lattice} := by
  ext x
  constructor
  · rintro ⟨hxRelax, hxNonbasic⟩
    refine ⟨hxRelax, ?_⟩
    simpa [Function.comp, tableau_mixed_integer_lattice] using hxNonbasic
  · rintro ⟨hxRelax, hxSwap⟩
    refine ⟨hxRelax, ?_⟩
    simpa [Function.comp, tableau_mixed_integer_lattice] using hxSwap

/-- Membership in `pure_gomory_relaxation_feasible_region abar bbar` means belonging to the
tableau relaxation and having integral nonbasic coordinates. -/
@[simp] theorem mem_pure_gomory_relaxation_feasible_region_iff
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (x : Sum B N → ℝ) :
    x ∈ pure_gomory_relaxation_feasible_region abar bbar ↔
      x ∈ rationalTableauCornerRelaxation abar bbar ∧
        ∀ j : N, ∃ z : ℤ, x (Sum.inr j) = (z : ℝ) :=
  Iff.rfl

/-- The transformed objective value of a point in the Gomory relaxation, with the constant term
omitted so that only the reduced-cost contribution `-∑ j ∈ N, c̄_j x_j` remains. -/
noncomputable def pure_gomory_relaxation_objective
    (reducedCosts : N → ℚ)
    (x : Sum B N → ℝ) : ℝ :=
  -∑ j : N, (reducedCosts j : ℝ) * x (Sum.inr j)

/-- The transformed objective values attained on the pure Gomory relaxation feasible region. -/
noncomputable def pure_gomory_relaxation_objective_values
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    : Set ℝ :=
  pure_gomory_relaxation_objective reducedCosts '' pure_gomory_relaxation_feasible_region abar bbar

/-- Membership in `pure_gomory_relaxation_objective_values abar bbar reducedCosts` means that some
pure-Gomory-feasible point attains the value `r`. -/
theorem mem_pure_gomory_relaxation_objective_values_iff
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (r : ℝ) :
    r ∈ pure_gomory_relaxation_objective_values abar bbar reducedCosts ↔
      ∃ x : Sum B N → ℝ,
        x ∈ pure_gomory_relaxation_feasible_region abar bbar ∧
          pure_gomory_relaxation_objective reducedCosts x = r :=
  Iff.rfl

/-- The tableau coefficients `Ā = A_B⁻¹ A_N` attached to the integer basis block `A_B`. -/
noncomputable def pure_gomory_basis_abar
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (AN : Matrix B N ℤ) : B → N → ℚ :=
  fun i j ↦
    (((AB.map (Int.castRingHom ℚ))⁻¹ * (AN.map (Int.castRingHom ℚ))) i j)

/-- The transformed right-hand side `b̄ = A_B⁻¹ b` attached to the integer basis block `A_B`. -/
noncomputable def pure_gomory_basis_bbar
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (b : B → ℤ) : B → ℚ :=
  fun i ↦
    (((AB.map (Int.castRingHom ℚ))⁻¹).mulVec (fun k ↦ (b k : ℚ)) i)

/-- The reduced costs `c̄_N = c_B A_B⁻¹ A_N - c_N` attached to the integer basis block `A_B`. -/
noncomputable def pure_gomory_basis_reduced_costs
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (AN : Matrix B N ℤ)
    (cB : B → ℤ)
    (cN : N → ℤ) : N → ℚ :=
  fun j ↦
    (((fun i ↦ (cB i : ℚ)) ᵥ*
          (((AB.map (Int.castRingHom ℚ))⁻¹) * (AN.map (Int.castRingHom ℚ)))) j -
      (cN j : ℚ))

/-- A point of the pure Gomory relaxation is optimal when it is feasible and attains the greatest
transformed objective value. -/
class pure_gomory_relaxation_optimal_solution
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (x : Sum B N → ℝ) : Prop where
  feasible : x ∈ pure_gomory_relaxation_feasible_region abar bbar
  isGreatest :
    IsGreatest
      (pure_gomory_relaxation_objective_values abar bbar reducedCosts)
      (pure_gomory_relaxation_objective reducedCosts x)

/-- An optimal pure Gomory solution attains one of the recorded transformed objective values. -/
theorem pure_gomory_relaxation_optimal_solution.objective_mem
    {abar : B → N → ℚ}
    {bbar : B → ℚ}
    {reducedCosts : N → ℚ}
    {x : Sum B N → ℝ}
    (hx : pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x) :
    pure_gomory_relaxation_objective reducedCosts x ∈
      pure_gomory_relaxation_objective_values abar bbar reducedCosts :=
  hx.isGreatest.1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the tableau apex is feasible
for the pure Gomory relaxation. -/
theorem tableauCornerBasePoint_mem_pure_gomory_relaxation_feasible_region
    (abar : B → N → ℚ)
    (bbar : B → ℚ) :
    tableauCornerBasePoint bbar ∈ pure_gomory_relaxation_feasible_region abar bbar := by
  -- Reuse feasibility of the tableau apex and witness integrality of every zero coordinate.
  refine (mem_pure_gomory_relaxation_feasible_region_iff abar bbar _).2 ⟨?_, ?_⟩
  · exact tableauCornerBasePoint_mem_rationalTableauCornerRelaxation abar bbar
  · intro j
    refine ⟨0, ?_⟩
    simp [tableauCornerBasePoint]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: strict positivity of all
reduced costs forces every nonbasic coordinate of an optimal solution to vanish. -/
theorem pure_gomory_relaxation_optimal_solution.nonbasic_eq_zero_of_strict
    {abar : B → N → ℚ}
    {bbar : B → ℚ}
    {reducedCosts : N → ℚ}
    {x : Sum B N → ℝ}
    (hx : pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x)
    (hstrict : ∀ j : N, 0 < reducedCosts j) :
    ∀ j : N, x (Sum.inr j) = 0 := by
  classical
  -- The feasible apex supplies the zero objective value against which optimality is compared.
  have hapexFeasible :
      tableauCornerBasePoint bbar ∈ pure_gomory_relaxation_feasible_region abar bbar :=
    tableauCornerBasePoint_mem_pure_gomory_relaxation_feasible_region abar bbar
  have hapexObjective :
      pure_gomory_relaxation_objective reducedCosts (tableauCornerBasePoint bbar) = 0 := by
    simp [pure_gomory_relaxation_objective, tableauCornerBasePoint]
  have hzeroMem :
      (0 : ℝ) ∈ pure_gomory_relaxation_objective_values abar bbar reducedCosts := by
    refine (mem_pure_gomory_relaxation_objective_values_iff abar bbar reducedCosts 0).2 ?_
    exact ⟨tableauCornerBasePoint bbar, hapexFeasible, hapexObjective⟩
  have hobjectiveNonnegative : 0 ≤ pure_gomory_relaxation_objective reducedCosts x :=
    hx.isGreatest.2 hzeroMem
  -- Feasibility and strict reduced-cost positivity make every term in the objective sum nonnegative.
  have hnonbasicNonnegative : ∀ j : N, 0 ≤ x (Sum.inr j) :=
    ((mem_rationalTableauCornerRelaxation_iff abar bbar x).1
      ((mem_pure_gomory_relaxation_feasible_region_iff abar bbar x).1 hx.feasible).1).2
  have hcostPositive : ∀ j : N, (0 : ℝ) < (reducedCosts j : ℝ) := by
    intro j
    exact_mod_cast hstrict j
  have htermNonnegative :
      ∀ j : N, 0 ≤ (reducedCosts j : ℝ) * x (Sum.inr j) := by
    intro j
    exact mul_nonneg (hcostPositive j).le (hnonbasicNonnegative j)
  have hsumNonnegative :
      0 ≤ ∑ j : N, (reducedCosts j : ℝ) * x (Sum.inr j) :=
    Finset.sum_nonneg fun j _ ↦ htermNonnegative j
  have hsumNonpositive :
      ∑ j : N, (reducedCosts j : ℝ) * x (Sum.inr j) ≤ 0 := by
    simpa [pure_gomory_relaxation_objective, neg_nonneg] using hobjectiveNonnegative
  have hsumZero :
      ∑ j : N, (reducedCosts j : ℝ) * x (Sum.inr j) = 0 :=
    le_antisymm hsumNonpositive hsumNonnegative
  -- A finite sum of nonnegative terms is zero only coordinatewise; cancel each positive cost.
  intro j
  have htermZero : (reducedCosts j : ℝ) * x (Sum.inr j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ ↦ htermNonnegative k)).1 hsumZero j (Finset.mem_univ j)
  exact (mul_eq_zero.mp htermZero).resolve_left (ne_of_gt (hcostPositive j))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean`: the determinant row bound
makes all basic coordinates of every strict-reduced-cost optimum nonnegative. -/
theorem pure_gomory_relaxation_optimal_solution.basic_coordinates_nonnegative_of_row_bound
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (hdet : AB.det ≠ 0)
    (rowMax : B → ℚ)
    (hrowMax :
      ∀ i : B,
        IsGreatest
          (Set.insert 0 (Set.range (abar i)))
          (rowMax i))
    (hstrictReducedCosts : ∀ j : N, 0 < reducedCosts j)
    (hbound :
      ∀ i : B,
        bbar i ≥ ((Int.natAbs AB.det : ℚ) - 1) * rowMax i) :
    ∀ x : Sum B N → ℝ,
      pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x →
        ∀ i : B, 0 ≤ x (Sum.inl i) := by
  intro x hx i
  -- Strict optimality first removes the complete nonbasic contribution from the tableau row.
  have hnonbasicZero : ∀ j : N, x (Sum.inr j) = 0 :=
    hx.nonbasic_eq_zero_of_strict hstrictReducedCosts
  have hbasicEquation :
      x (Sum.inl i) = (bbar i : ℝ) -
        ∑ j : N, (abar i j : ℝ) * x (Sum.inr j) :=
    ((mem_rationalTableauCornerRelaxation_iff abar bbar x).1
      ((mem_pure_gomory_relaxation_feasible_region_iff abar bbar x).1 hx.feasible).1).1 i
  have hbasicValue : x (Sum.inl i) = (bbar i : ℝ) := by
    simpa [hnonbasicZero] using hbasicEquation
  -- A nonzero integral determinant makes `|det A_B| - 1` nonnegative.
  have hdetNatAbsPositive : 0 < Int.natAbs AB.det := Int.natAbs_pos.mpr hdet
  have hdetNatAbsOne : 1 ≤ Int.natAbs AB.det := hdetNatAbsPositive
  have hdetFactorNonnegative : (0 : ℚ) ≤ (Int.natAbs AB.det : ℚ) - 1 := by
    apply sub_nonneg.mpr
    exact_mod_cast hdetNatAbsOne
  -- Since zero is one of the row candidates, its greatest element is nonnegative.
  have hrowMaxNonnegative : 0 ≤ rowMax i := by
    exact (hrowMax i).2 (Set.mem_insert 0 (Set.range (abar i)))
  have hbbarNonnegative : 0 ≤ bbar i :=
    le_trans (mul_nonneg hdetFactorNonnegative hrowMaxNonnegative) (hbound i)
  have hbbarRealNonnegative : (0 : ℝ) ≤ (bbar i : ℝ) := by
    exact_mod_cast hbbarNonnegative
  -- Substitute the now-constant basic row and finish with the cast row bound.
  rw [hbasicValue]
  exact hbbarRealNonnegative

/-- Basis-level bookkeeping for Exercise 6.5: `Ā`, `b̄`, and `c̄_N` are the tableau and
reduced-cost data attached to the integer basis block `A_B`. The ambient linear-program data is
suppressed, but the source-required basis condition `det A_B ≠ 0` and the exported tableau-side
properties remain explicit. -/
class pure_gomory_basis_tableau_data
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ) : Prop where
  det_ne_zero : AB.det ≠ 0
  dual_feasible : ∀ j : N, 0 ≤ reducedCosts j
  det_clears_abar :
    ∀ i : B, ∀ j : N, ∃ z : ℤ, (Int.natAbs AB.det : ℚ) * abar i j = z
  det_clears_bbar :
    ∀ i : B, ∃ z : ℤ, (Int.natAbs AB.det : ℚ) * bbar i = z

/-- Helper for Exercise 6.5: once the tableau data `Ā`, `b̄`, and `c̄_N` are fixed together with
the determinant-clearing integrality consequences of the integer basis block `A_B`, the row bound
`b̄_i ≥ (D - 1) m_i`, where `m_i` is the maximum of `0` and the `i`th row entries of `Ā`, and
strict positivity of the reduced costs force every optimal pure Gomory solution to have
nonnegative basic coordinates. -/
theorem pure_gomory_basis_tableau_data.basic_coordinates_nonnegative_of_optimal_solution
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (reducedCosts : N → ℚ)
    (hbasis : pure_gomory_basis_tableau_data AB abar bbar reducedCosts)
    (rowMax : B → ℚ)
    (hrowMax :
      ∀ i : B,
        IsGreatest
          (Set.insert 0 (Set.range (abar i)))
          (rowMax i))
    (hstrictReducedCosts :
      ∀ j : N, 0 < reducedCosts j)
    (hbound :
      ∀ i : B,
        bbar i ≥ ((Int.natAbs AB.det : ℚ) - 1) * rowMax i) :
    ∀ x : Sum B N → ℝ,
      pure_gomory_relaxation_optimal_solution abar bbar reducedCosts x →
        ∀ i : B, 0 ≤ x (Sum.inl i) := by
  -- The basis package supplies the only field needed by the tableau-level row-bound theorem.
  exact pure_gomory_relaxation_optimal_solution.basic_coordinates_nonnegative_of_row_bound
    AB abar bbar reducedCosts hbasis.det_ne_zero rowMax hrowMax hstrictReducedCosts hbound

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_5.lean

Exercise 6.5. Consider a pure integer linear program
`max c x`, `A x = b`, `x_j ∈ ℤ≥0`, where the columns are partitioned as
`A = (A_B, A_N)` and `c = (c_B, c_N)`. Let `Ā = A_B⁻¹ A_N`,
`b̄ = A_B⁻¹ b`, and `c̄_N = c_B A_B⁻¹ A_N - c_N`, and assume the basis is dual feasible in the
sense that `c̄_N ≥ 0`. This source-facing repair also makes explicit the strict positivity
side condition on `c̄_N` needed to exclude zero reduced-cost tie optima. If
`m_i = max (0, max_{j ∈ N} Ā i j)` and
`b̄ i ≥ (|det A_B| - 1) m_i` for every basic index `i`, then every optimal solution of the
Gomory relaxation has nonnegative basic coordinates. -/
theorem ch6_sec6_5_exercise_6_5
    [Fintype B] [DecidableEq B]
    (AB : Matrix B B ℤ)
    (AN : Matrix B N ℤ)
    (b : B → ℤ)
    (cB : B → ℤ)
    (cN : N → ℤ)
    (abar : B → N → ℚ)
    (bbar : B → ℚ)
    (hdet : AB.det ≠ 0)
    (habar :
      abar =
        pure_gomory_basis_abar AB AN)
    (hbbar :
      bbar =
        pure_gomory_basis_bbar AB b)
    (hdualFeasible :
      ∀ j : N,
        0 ≤ pure_gomory_basis_reduced_costs AB AN cB cN j)
    (hstrictReducedCosts :
      ∀ j : N,
        0 < pure_gomory_basis_reduced_costs AB AN cB cN j)
    (rowMax : B → ℚ)
    (hrowMax :
      ∀ i : B,
        IsGreatest
          (Set.insert 0 (Set.range (abar i)))
          (rowMax i))
    (hbound :
      ∀ i : B,
        bbar i ≥ ((Int.natAbs AB.det : ℚ) - 1) * rowMax i) :
    ∀ x : Sum B N → ℝ,
      pure_gomory_relaxation_optimal_solution
          abar
          bbar
          (pure_gomory_basis_reduced_costs AB AN cB cN)
          x →
        ∀ i : B, 0 ≤ x (Sum.inl i) := by
  -- Route correction: strict reduced-cost positivity rules out the tied optima that invalidated
  -- the earlier nonnegative-cost formulation, so the tableau-level argument now applies directly.
  subst abar
  subst bbar
  have hstrictFromDual :
      ∀ j : N, 0 < pure_gomory_basis_reduced_costs AB AN cB cN j := by
    intro j
    exact lt_of_le_of_ne (hdualFeasible j)
      (Ne.symm (ne_of_gt (hstrictReducedCosts j)))
  exact pure_gomory_relaxation_optimal_solution.basic_coordinates_nonnegative_of_row_bound
    AB (pure_gomory_basis_abar AB AN) (pure_gomory_basis_bbar AB b)
      (pure_gomory_basis_reduced_costs AB AN cB cN) hdet rowMax hrowMax hstrictFromDual hbound

end Exercise65

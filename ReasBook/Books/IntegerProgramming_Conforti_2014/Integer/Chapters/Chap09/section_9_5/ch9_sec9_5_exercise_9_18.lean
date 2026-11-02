import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section Exercise918

variable {ι : Type*}

/-- The reduced-cost form of the objective in Exercise 9.18, where `N0` indexes the nonbasic
variables fixed at `0` and `Nu` indexes the nonbasic variables fixed at their upper bounds. -/
def exercise_9_18_reduced_cost_objective
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ) : ℝ :=
  zBar +
    Finset.sum N0 (fun j ↦ cBar j * (x j : ℝ)) +
    Finset.sum Nu (fun j ↦ cBar j * ((x j - u j : ℤ) : ℝ))

/-- The bounded integer feasible points `x` with `0 ≤ x j ≤ u j` for every variable. -/
def exercise_9_18_feasible
    (u : ι → ℤ)
    (x : ι → ℤ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ u j

/-- The attainable objective values of Exercise 9.18 on bounded integer feasible points. -/
def exercise_9_18_objective_values
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ) : Set ℝ :=
  {r | ∃ x : ι → ℤ,
      exercise_9_18_feasible u x ∧
        exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x = r}

/-- Membership in `exercise_9_18_objective_values N0 Nu u zBar cBar` means that a bounded integer
feasible point attains the value `r`. -/
theorem mem_exercise_9_18_objective_values_iff
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (r : ℝ) :
    r ∈ exercise_9_18_objective_values N0 Nu u zBar cBar ↔
      ∃ x : ι → ℤ,
        exercise_9_18_feasible u x ∧
          exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x = r :=
  Iff.rfl

/-- A known lower bound `zUnder` for the integer program of Exercise 9.18 is any real number that
lies below an attained objective value of a bounded integer feasible point. -/
def exercise_9_18_has_lower_bound
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar zUnder : ℝ)
    (cBar : ι → ℝ) : Prop :=
  ∃ r ∈ exercise_9_18_objective_values N0 Nu u zBar cBar, zUnder ≤ r

/-- `exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar` unfolds to the original witness form:
some bounded integer feasible point has objective value at least `zUnder`. -/
theorem exercise_9_18_has_lower_bound_iff
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar zUnder : ℝ)
    (cBar : ι → ℝ) :
    exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar ↔
      ∃ y : ι → ℤ,
        exercise_9_18_feasible u y ∧
          zUnder ≤ exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y := by
  constructor
  · rintro ⟨r, hr, hz⟩
    rcases (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar r).1 hr with
      ⟨y, hy, rfl⟩
    exact ⟨y, hy, hz⟩
  · rintro ⟨y, hy, hz⟩
    refine ⟨exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y, ?_, hz⟩
    exact (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar
      (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y)).2 ⟨y, hy, rfl⟩

/-- A bounded integer feasible point is optimal for Exercise 9.18 when its objective value is the
greatest value attained on the bounded integer feasible region. -/
def exercise_9_18_optimal_solution
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ) : Prop :=
  exercise_9_18_feasible u x ∧
    IsGreatest
      (exercise_9_18_objective_values N0 Nu u zBar cBar)
      (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x)

/-- `exercise_9_18_optimal_solution N0 Nu u zBar cBar x` records feasibility of `x` together
with maximality of its attained objective value. -/
theorem exercise_9_18_optimal_solution_iff
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ) :
    exercise_9_18_optimal_solution N0 Nu u zBar cBar x ↔
      exercise_9_18_feasible u x ∧
        IsGreatest
          (exercise_9_18_objective_values N0 Nu u zBar cBar)
          (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x) :=
  Iff.rfl

/-- The canonical `IsGreatest` formulation of optimality is equivalent to the source-facing
quantifier form used by the original statement pipeline. -/
theorem exercise_9_18_optimal_solution_iff_forall
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ) :
    exercise_9_18_optimal_solution N0 Nu u zBar cBar x ↔
      exercise_9_18_feasible u x ∧
        ∀ y : ι → ℤ,
          exercise_9_18_feasible u y →
            exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y ≤
              exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x := by
  constructor
  · rintro ⟨hx, hxGreatest⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact hxGreatest.2 <|
      (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar
        (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y)).2 ⟨y, hy, rfl⟩
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, ?_⟩
    refine ⟨?_, ?_⟩
    · exact (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar
        (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x)).2 ⟨x, hx, rfl⟩
    · intro r hr
      rcases (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar r).1 hr with
        ⟨y, hy, hyr⟩
      simpa [hyr] using hmax y hy

/-- An optimal solution of Exercise 9.18 is bounded integer feasible. -/
theorem exercise_9_18_optimal_solution.feasible
    {N0 Nu : Finset ι}
    {u : ι → ℤ}
    {zBar : ℝ}
    {cBar : ι → ℝ}
    {x : ι → ℤ}
    (hopt : exercise_9_18_optimal_solution N0 Nu u zBar cBar x) :
    exercise_9_18_feasible u x :=
  hopt.1

/-- The objective value of an optimal solution dominates the objective value of every bounded
integer feasible point. -/
theorem exercise_9_18_optimal_solution.objective_le
    {N0 Nu : Finset ι}
    {u : ι → ℤ}
    {zBar : ℝ}
    {cBar : ι → ℝ}
    {x y : ι → ℤ}
    (hopt : exercise_9_18_optimal_solution N0 Nu u zBar cBar x)
    (hy : exercise_9_18_feasible u y) :
    exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y ≤
      exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x :=
  hopt.2.2 <|
    (mem_exercise_9_18_objective_values_iff N0 Nu u zBar cBar
      (exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y)).2 ⟨y, hy, rfl⟩

/-- A lower bound in the sense of Exercise 9.18 is witnessed by a bounded integer feasible point
whose objective value is at least `zUnder`. -/
theorem exercise_9_18_has_lower_bound.exists_feasible
    {N0 Nu : Finset ι}
    {u : ι → ℤ}
    {zBar zUnder : ℝ}
    {cBar : ι → ℝ}
    (hLower : exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar) :
    ∃ y : ι → ℤ,
      exercise_9_18_feasible u y ∧
        zUnder ≤ exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar y :=
  (exercise_9_18_has_lower_bound_iff N0 Nu u zBar zUnder cBar).1 hLower

/-- Helper for Exercise 9.18: every `N0` reduced-cost summand is nonpositive at a feasible point,
because the reduced cost is nonpositive and the variable value is nonnegative. -/
lemma nonbasicAtZeroSummand_nonpos
    (N0 : Finset ι)
    (u : ι → ℤ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hfeas : exercise_9_18_feasible u x)
    {k : ι}
    (hk : k ∈ N0) :
    cBar k * (x k : ℝ) ≤ 0 := by
  -- Cast feasibility to `ℝ` so the summand sign follows from the reduced-cost sign.
  have hxk_nonneg : 0 ≤ (x k : ℝ) := by
    exact_mod_cast (hfeas k).1
  exact mul_nonpos_of_nonpos_of_nonneg (hN0 k hk) hxk_nonneg

/-- Helper for Exercise 9.18: every `Nu` reduced-cost summand is nonpositive at a feasible point,
because the reduced cost is nonnegative and the slack `x k - u k` is nonpositive. -/
lemma nonbasicAtUpperSummand_nonpos
    (Nu : Finset ι)
    (u : ι → ℤ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j)
    (hfeas : exercise_9_18_feasible u x)
    {k : ι}
    (hk : k ∈ Nu) :
    cBar k * (((x k - u k : ℤ) : ℝ)) ≤ 0 := by
  -- The slack is nonpositive because feasibility gives `x k ≤ u k`.
  have hxk_sub_nonpos : (((x k - u k : ℤ) : ℝ)) ≤ 0 := by
    exact_mod_cast sub_nonpos.mpr (hfeas k).2
  exact mul_nonpos_of_nonneg_of_nonpos (hNu k hk) hxk_sub_nonpos

/-- Helper for Exercise 9.18: isolating one `N0` summand shows that the reduced-cost objective is
bounded above by the contribution of that single nonbasic-at-zero variable. -/
lemma reducedCostObjective_le_zeroPivot
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j)
    (hfeas : exercise_9_18_feasible u x)
    {j : ι}
    (hj : j ∈ N0) :
    exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x ≤
      zBar + cBar j * (x j : ℝ) := by
  classical
  -- Every summand except the pivot is nonpositive, so removing them can only increase the bound.
  have hN0_rest :
      Finset.sum (N0.erase j) (fun k ↦ cBar k * (x k : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun k hk ↦ ?_
    exact nonbasicAtZeroSummand_nonpos N0 u cBar x hN0 hfeas (Finset.mem_of_mem_erase hk)
  have hNu_all :
      Finset.sum Nu (fun k ↦ cBar k * (((x k - u k : ℤ) : ℝ))) ≤ 0 := by
    refine Finset.sum_nonpos fun k hk ↦ ?_
    exact nonbasicAtUpperSummand_nonpos Nu u cBar x hNu hfeas hk
  -- Split the `N0` sum at `j` and discard the remaining nonpositive contributions.
  have hsplit :
      exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x =
        zBar + cBar j * (x j : ℝ) +
          Finset.sum (N0.erase j) (fun k ↦ cBar k * (x k : ℝ)) +
          Finset.sum Nu (fun k ↦ cBar k * (((x k - u k : ℤ) : ℝ))) := by
    rw [exercise_9_18_reduced_cost_objective, ← Finset.add_sum_erase N0
      (fun k ↦ cBar k * (x k : ℝ)) hj]
    ring
  rw [hsplit]
  linarith

/-- Helper for Exercise 9.18: isolating one `Nu` summand shows that the reduced-cost objective is
bounded above by the contribution of that single nonbasic-at-upper-bound variable. -/
lemma reducedCostObjective_le_upperPivot
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j)
    (hfeas : exercise_9_18_feasible u x)
    {j : ι}
    (hj : j ∈ Nu) :
    exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x ≤
      zBar + cBar j * (((x j - u j : ℤ) : ℝ)) := by
  classical
  -- Every summand except the pivot is nonpositive, so removing them can only increase the bound.
  have hN0_all :
      Finset.sum N0 (fun k ↦ cBar k * (x k : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun k hk ↦ ?_
    exact nonbasicAtZeroSummand_nonpos N0 u cBar x hN0 hfeas hk
  have hNu_rest :
      Finset.sum (Nu.erase j) (fun k ↦ cBar k * (((x k - u k : ℤ) : ℝ))) ≤ 0 := by
    refine Finset.sum_nonpos fun k hk ↦ ?_
    exact nonbasicAtUpperSummand_nonpos Nu u cBar x hNu hfeas (Finset.mem_of_mem_erase hk)
  -- Split the `Nu` sum at `j` and discard the remaining nonpositive contributions.
  have hsplit :
      exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x =
        zBar + Finset.sum N0 (fun k ↦ cBar k * (x k : ℝ)) +
          cBar j * (((x j - u j : ℤ) : ℝ)) +
          Finset.sum (Nu.erase j) (fun k ↦ cBar k * (((x k - u k : ℤ) : ℝ))) := by
    rw [exercise_9_18_reduced_cost_objective, ← Finset.add_sum_erase Nu
      (fun k ↦ cBar k * (((x k - u k : ℤ) : ℝ))) hj]
    ring
  rw [hsplit]
  linarith

/-- Helper for Exercise 9.18: in an optimal solution of the bounded pure integer program, every
nonbasic variable indexed by `N0` with nonzero reduced cost satisfies the displayed floor upper
bound. -/
theorem exercise_9_18_nonbasic_at_zero_variable_bound
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar zUnder : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hopt : exercise_9_18_optimal_solution N0 Nu u zBar cBar x)
    (hLower : exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar)
    (hdisj : Disjoint N0 Nu)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j)
    {j : ι}
    (hj : j ∈ N0)
    (hcj : cBar j ≠ 0) :
    x j ≤ Int.floor ((zBar - zUnder) / (-cBar j)) := by
  -- The source statement includes the disjoint nonbasic partition; keep that hypothesis in scope.
  have _ : Disjoint N0 Nu := hdisj
  -- Compare the optimal objective value with the lower-bound witness.
  have hfeas : exercise_9_18_feasible u x := exercise_9_18_optimal_solution.feasible hopt
  rcases exercise_9_18_has_lower_bound.exists_feasible hLower with ⟨y, hy, hyLower⟩
  have hzUnder_le_obj :
      zUnder ≤ exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x := by
    exact hyLower.trans (exercise_9_18_optimal_solution.objective_le hopt hy)
  -- Isolate the `j`-summand and use the reduced-cost sign to discard all others.
  have hobj_le_pivot :
      exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x ≤
        zBar + cBar j * (x j : ℝ) :=
    reducedCostObjective_le_zeroPivot N0 Nu u zBar cBar x hN0 hNu hfeas hj
  have hcj_neg : cBar j < 0 := lt_of_le_of_ne (hN0 j hj) hcj
  have hneg_pos : 0 < -cBar j := by
    linarith
  -- Rearrange the objective sandwich into a bound on the single variable.
  have hscaled : (-cBar j) * (x j : ℝ) ≤ zBar - zUnder := by
    linarith
  have hdiv : (x j : ℝ) ≤ (zBar - zUnder) / (-cBar j) := by
    exact (le_div_iff₀ hneg_pos).2 (by simpa [mul_comm] using hscaled)
  exact Int.le_floor.mpr hdiv

/-- Helper for Exercise 9.18: in an optimal solution of the bounded pure integer program, every
nonbasic variable indexed by `Nu` with nonzero reduced cost satisfies the displayed ceiling lower
bound. -/
lemma exercise_9_18_nonbasic_at_upper_bound_variable_bound
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar zUnder : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hopt : exercise_9_18_optimal_solution N0 Nu u zBar cBar x)
    (hLower : exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar)
    (hdisj : Disjoint N0 Nu)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j)
    {j : ι}
    (hj : j ∈ Nu)
    (hcj : cBar j ≠ 0) :
    u j - Int.ceil ((zBar - zUnder) / cBar j) ≤ x j := by
  -- The source statement includes the disjoint nonbasic partition; keep that hypothesis in scope.
  have _ : Disjoint N0 Nu := hdisj
  -- Compare the optimal objective value with the lower-bound witness.
  have hfeas : exercise_9_18_feasible u x := exercise_9_18_optimal_solution.feasible hopt
  rcases exercise_9_18_has_lower_bound.exists_feasible hLower with ⟨y, hy, hyLower⟩
  have hzUnder_le_obj :
      zUnder ≤ exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x := by
    exact hyLower.trans (exercise_9_18_optimal_solution.objective_le hopt hy)
  -- Isolate the `j`-summand and convert it into the nonnegative slack `u j - x j`.
  have hobj_le_pivot :
      exercise_9_18_reduced_cost_objective N0 Nu u zBar cBar x ≤
        zBar + cBar j * (((x j - u j : ℤ) : ℝ)) :=
    reducedCostObjective_le_upperPivot N0 Nu u zBar cBar x hN0 hNu hfeas hj
  have hcj_pos : 0 < cBar j := lt_of_le_of_ne (hNu j hj) (by simpa [eq_comm] using hcj)
  have hsub_int : (x j - u j : ℤ) = -((u j - x j : ℤ)) := by
    omega
  have hsub_real : (((x j - u j : ℤ) : ℝ)) = -(((u j - x j : ℤ) : ℝ)) := by
    rw [hsub_int, Int.cast_neg]
  have hscaled :
      cBar j * (((u j - x j : ℤ) : ℝ)) ≤ zBar - zUnder := by
    rw [hsub_real] at hobj_le_pivot
    linarith
  have hdiv : (((u j - x j : ℤ) : ℝ)) ≤ (zBar - zUnder) / cBar j := by
    exact (le_div_iff₀ hcj_pos).2 (by simpa [mul_comm] using hscaled)
  have hslack_le_ceil_real :
      (((u j - x j : ℤ) : ℝ)) ≤ Int.ceil ((zBar - zUnder) / cBar j) := by
    exact hdiv.trans (Int.le_ceil _)
  have hslack_le_ceil :
      (u j - x j : ℤ) ≤ Int.ceil ((zBar - zUnder) / cBar j) := by
    exact_mod_cast hslack_le_ceil_real
  -- Rearranging the slack inequality gives the stated lower bound on `x j`.
  omega

/-- Exercise 9.18. In any optimal solution of the bounded pure integer program, every nonbasic
variable indexed by `N0` with nonzero reduced cost satisfies the displayed floor upper bound, and
every nonbasic variable indexed by `Nu` with nonzero reduced cost satisfies the displayed ceiling
lower bound. -/
theorem exercise_9_18_variable_bounds
    (N0 Nu : Finset ι)
    (u : ι → ℤ)
    (zBar zUnder : ℝ)
    (cBar : ι → ℝ)
    (x : ι → ℤ)
    (hopt : exercise_9_18_optimal_solution N0 Nu u zBar cBar x)
    (hLower : exercise_9_18_has_lower_bound N0 Nu u zBar zUnder cBar)
    (hdisj : Disjoint N0 Nu)
    (hN0 : ∀ j ∈ N0, cBar j ≤ 0)
    (hNu : ∀ j ∈ Nu, 0 ≤ cBar j) :
    (∀ {j : ι}, j ∈ N0 → cBar j ≠ 0 →
      x j ≤ Int.floor ((zBar - zUnder) / (-cBar j))) ∧
      ∀ {j : ι}, j ∈ Nu → cBar j ≠ 0 →
        u j - Int.ceil ((zBar - zUnder) / cBar j) ≤ x j := by
  constructor
  · intro j hj hcj
    exact exercise_9_18_nonbasic_at_zero_variable_bound
      N0 Nu u zBar zUnder cBar x hopt hLower hdisj hN0 hNu hj hcj
  · intro j hj hcj
    exact exercise_9_18_nonbasic_at_upper_bound_variable_bound
      N0 Nu u zBar zUnder cBar x hopt hLower hdisj hN0 hNu hj hcj

end Exercise918

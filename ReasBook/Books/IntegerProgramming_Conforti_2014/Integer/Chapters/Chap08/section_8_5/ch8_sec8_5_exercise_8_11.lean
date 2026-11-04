/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Data.NNReal.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Algebra.InfiniteSum.Real
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_9

open scoped BigOperators

-- Semantic recall note: the Chapter 8 owner for subgradients is `IsSubgradientAtOn`; this file
-- reuses that owner at `Set.univ` and adds only the method-sequence and counterexample layer
-- specific to Exercise 8.11.

section Exercise811

variable {n : ℕ}

/-- One coordinatewise subgradient step with stepsize `α`. -/
def subgradient_step
    (x g : Fin n → ℝ)
    (α : ℝ) : Fin n → ℝ :=
  fun i ↦ x i - α * g i

/-- Evaluating a subgradient step at coordinate `i` gives the textbook update formula. -/
theorem subgradient_step_apply
    (x g : Fin n → ℝ)
    (α : ℝ)
    (i : Fin n) :
    subgradient_step x g α i = x i - α * g i :=
  rfl

/-- `IsSubgradientMethodSequence f α x g` means that `x` evolves by the subgradient method for
`f` with stepsizes `α` and chosen subgradients `g`. -/
def IsSubgradientMethodSequence
    (f : (Fin n → ℝ) → ℝ)
    (α : ℕ → ℝ)
    (x g : ℕ → Fin n → ℝ) : Prop :=
  ∀ t : ℕ,
    IsSubgradientAt f (x t) (g t) ∧
      x (t + 1) = subgradient_step (x t) (g t) (α t)

/-- Unfolding `IsSubgradientMethodSequence` gives the stagewise subgradient condition together with
the update rule. -/
theorem is_subgradient_method_sequence_iff
    (f : (Fin n → ℝ) → ℝ)
    (α : ℕ → ℝ)
    (x g : ℕ → Fin n → ℝ) :
    IsSubgradientMethodSequence f α x g ↔
      ∀ t : ℕ,
        IsSubgradientAt f (x t) (g t) ∧
          x (t + 1) = subgradient_step (x t) (g t) (α t) :=
  Iff.rfl

namespace IsSubgradientMethodSequence

/-- Each chosen direction in a subgradient method sequence is a subgradient at the current
iterate. -/
theorem isSubgradientAt
    {f : (Fin n → ℝ) → ℝ}
    {α : ℕ → ℝ}
    {x g : ℕ → Fin n → ℝ}
    (hmethod : IsSubgradientMethodSequence f α x g)
    (t : ℕ) :
    IsSubgradientAt f (x t) (g t) :=
  (hmethod t).1

/-- Each iterate after the initial point is obtained from the previous iterate by one
subgradient step. -/
theorem step_eq
    {f : (Fin n → ℝ) → ℝ}
    {α : ℕ → ℝ}
    {x g : ℕ → Fin n → ℝ}
    (hmethod : IsSubgradientMethodSequence f α x g)
    (t : ℕ) :
    x (t + 1) = subgradient_step (x t) (g t) (α t) :=
  (hmethod t).2

end IsSubgradientMethodSequence

/-- Helper for Exercise 8.11: one subgradient step is the old iterate plus the increment
`(-α) • g`. -/
lemma subgradientStep_eq_add_smul
    (x g : Fin n → ℝ)
    (α : ℝ) :
    subgradient_step x g α = x + (-α) • g := by
  -- Rewrite the coordinatewise textbook formula into vector-addition form.
  ext i
  simp [subgradient_step, sub_eq_add_neg]

/-- Helper for Exercise 8.11: iterating the update rule produces the initial point plus the sum of
all past subgradient increments. -/
lemma iterate_eq_initial_add_sumSubgradientIncrements
    (α : ℕ → ℝ)
    (x g : ℕ → Fin n → ℝ)
    (hstep : ∀ t : ℕ, x (t + 1) = subgradient_step (x t) (g t) (α t)) :
    ∀ t : ℕ, x t = x 0 + ∑ i ∈ Finset.range t, (-α i) • g i := by
  intro t
  induction t with
  | zero =>
      -- At time `0` there are no increments yet.
      simp
  | succ t ih =>
      -- One more step appends the next increment to the partial sum.
      calc
        x (t + 1) = subgradient_step (x t) (g t) (α t) := hstep t
        _ = x t + (-α t) • g t := subgradientStep_eq_add_smul (x t) (g t) (α t)
        _ = x 0 + ∑ i ∈ Finset.range (t + 1), (-α i) • g i := by
          rw [ih]
          rw [Finset.sum_range_succ]
          abel

/-- Exercise 8.11 (1). If the iterates satisfy the subgradient-style update with summable
stepsizes and the chosen directions are uniformly norm-bounded, then the iterates
converge to some point. -/
theorem subgradient_method_converges_of_summable_steps
    (α : ℕ → ℝ)
    (x g : ℕ → Fin n → ℝ)
    (S : NNReal)
    (hα_summable : Summable α)
    (hstep : ∀ t : ℕ, x (t + 1) = subgradient_step (x t) (g t) (α t))
    (hbounded : ∀ t : ℕ, norm (g t) ≤ (S : ℝ)) :
    ∃ x_limit : Fin n → ℝ, Filter.Tendsto x Filter.atTop (nhds x_limit) := by
  let u : ℕ → Fin n → ℝ := fun t ↦ (-α t) • g t
  have hu_bound : ∀ t : ℕ, ‖u t‖ ≤ ‖α t‖ * (S : ℝ) := by
    intro t
    -- Compare each increment norm with the summable scalar majorant `‖α t‖ * S`.
    calc
      ‖u t‖ = ‖(-α t) • g t‖ := rfl
      _ = ‖-α t‖ * ‖g t‖ := norm_smul _ _
      _ = ‖α t‖ * ‖g t‖ := by simp
      _ ≤ ‖α t‖ * (S : ℝ) := by
        exact mul_le_mul_of_nonneg_left (hbounded t) (norm_nonneg _)
  have hmajorant : Summable (fun t : ℕ ↦ ‖α t‖ * (S : ℝ)) := by
    -- Summability is preserved after multiplying the absolutely summable steps by `S`.
    simpa [mul_comm] using (hα_summable.norm.mul_left (S : ℝ))
  have hu_summable : Summable u :=
    Summable.of_norm_bounded hmajorant hu_bound
  have hu_norm_summable : Summable (fun t : ℕ ↦ ‖u t‖) := hu_summable.norm
  obtain ⟨u_limit, hu_tendsto⟩ :=
    NormedAddCommGroup.summable_imp_tendsto_of_complete u hu_norm_summable
  refine ⟨x 0 + u_limit, ?_⟩
  have hx_eq :
      x = fun t ↦ x 0 + ∑ i ∈ Finset.range t, u i := by
    -- The iteration is exactly the sequence of partial sums of the increments.
    funext t
    simpa [u] using iterate_eq_initial_add_sumSubgradientIncrements α x g hstep t
  have hpartial :
      Filter.Tendsto
        (fun t : ℕ ↦ x 0 + ∑ i ∈ Finset.range t, u i)
        Filter.atTop
        (nhds (x 0 + u_limit)) :=
    tendsto_const_nhds.add hu_tendsto
  have heventually :
      (fun t : ℕ ↦ x 0 + ∑ i ∈ Finset.range t, u i) =ᶠ[Filter.atTop] x := by
    exact Filter.Eventually.of_forall fun t ↦ by
      simpa using congrArg (fun f : ℕ → Fin n → ℝ ↦ f t) hx_eq.symm
  exact hpartial.congr' heventually

namespace IsSubgradientMethodSequence

/-- Exercise 8.11 (1), source-facing form. A subgradient method sequence with summable stepsizes
and uniformly norm-bounded subgradients converges. -/
theorem tendsto_of_summable_steps
    {f : (Fin n → ℝ) → ℝ}
    {α : ℕ → ℝ}
    {x g : ℕ → Fin n → ℝ}
    {S : NNReal}
    (hα_summable : Summable α)
    (hmethod : IsSubgradientMethodSequence f α x g)
    (hbounded : ∀ t : ℕ, norm (g t) ≤ (S : ℝ)) :
    ∃ x_limit : Fin n → ℝ, Filter.Tendsto x Filter.atTop (nhds x_limit) := by
  exact subgradient_method_converges_of_summable_steps α x g S hα_summable
    (fun t ↦ hmethod.step_eq t) hbounded

end IsSubgradientMethodSequence

/-- The convex function `x ↦ |x|` used for the explicit counterexample. -/
def exercise_8_11_counterexample_function
    (x : Fin 1 → ℝ) : ℝ :=
  |x 0|

/-- The summable nonnegative stepsizes `α_t = 2^{-(t+2)}` used in the counterexample. -/
noncomputable def exercise_8_11_counterexample_steps
    (t : ℕ) : ℝ :=
  ((2 : ℝ) ^ (t + 2))⁻¹

/-- The starting point `x₀ = 1` for the counterexample. -/
def exercise_8_11_counterexample_start : Fin 1 → ℝ :=
  fun _ ↦ 1

/-- The chosen subgradient is constantly equal to `1`, which is valid because all iterates stay
positive in the counterexample. -/
def exercise_8_11_counterexample_subgradient :
    ℕ → Fin 1 → ℝ :=
  fun _ _ ↦ 1

/-- The counterexample iterates are the successive partial-sum updates
`x_t = 1 - ∑ s < t, α_s`. -/
noncomputable def exercise_8_11_counterexample_iterates :
    ℕ → Fin 1 → ℝ :=
  fun t _ ↦ 1 - (Finset.range t).sum exercise_8_11_counterexample_steps

/-- The counterexample limit is the nonoptimal point `1/2`. -/
noncomputable def exercise_8_11_counterexample_limit : Fin 1 → ℝ :=
  fun _ ↦ (1 / 2 : ℝ)

/-- Helper for Exercise 8.11: the explicit partial sums of the geometric steps are
`1 / 2 + 2^(-(t+1))`. -/
lemma counterexampleIterates_eq_half_add_geometricTail
    (t : ℕ) :
    exercise_8_11_counterexample_iterates t =
      fun _ ↦ (1 / 2 : ℝ) + ((2 : ℝ) ^ (t + 1))⁻¹ := by
  induction t with
  | zero =>
      -- The initial iterate is `1 = 1/2 + 1/2`.
      ext i
      fin_cases i
      norm_num [exercise_8_11_counterexample_iterates]
  | succ t ih =>
      ext i
      fin_cases i
      have ih0 :
          exercise_8_11_counterexample_iterates t 0 =
            (1 / 2 : ℝ) + ((2 : ℝ) ^ (t + 1))⁻¹ := by
        simpa using congrArg (fun f : Fin 1 → ℝ ↦ f 0) ih
      have hdouble :
          ((2 : ℝ) ^ (t + 1))⁻¹ = 2 * ((2 : ℝ) ^ (t + 2))⁻¹ := by
        -- The next geometric tail is exactly half the previous one.
        have hpow :
            (2 : ℝ) ^ (t + 2) = (2 : ℝ) ^ (t + 1) * 2 := by
          rw [show t + 2 = (t + 1) + 1 by omega, pow_succ]
        rw [hpow]
        field_simp
      -- Expand one more partial sum and simplify the remaining geometric term.
      calc
        exercise_8_11_counterexample_iterates (t + 1) 0
            = exercise_8_11_counterexample_iterates t 0 -
                exercise_8_11_counterexample_steps t := by
              simp [exercise_8_11_counterexample_iterates, Finset.sum_range_succ]
              ring
        _ = ((1 / 2 : ℝ) + ((2 : ℝ) ^ (t + 1))⁻¹) -
              exercise_8_11_counterexample_steps t := by
              rw [ih0]
        _ = (1 / 2 : ℝ) + ((2 : ℝ) ^ (t + 2))⁻¹ := by
              rw [exercise_8_11_counterexample_steps, hdouble]
              ring

/-- Helper for Exercise 8.11: the constant vector `1` is a valid subgradient of `x ↦ |x|` at each
counterexample iterate because those iterates stay positive. -/
lemma counterexampleSubgradientAtIterate
    (t : ℕ) :
    IsSubgradientAt
      exercise_8_11_counterexample_function
      (exercise_8_11_counterexample_iterates t)
      (exercise_8_11_counterexample_subgradient t) := by
  refine isSubgradientAt_of_ineq ?_
  intro y
  have hiter :
      exercise_8_11_counterexample_iterates t 0 =
        (1 / 2 : ℝ) + ((2 : ℝ) ^ (t + 1))⁻¹ := by
    simpa using congrArg (fun f : Fin 1 → ℝ ↦ f 0)
      (counterexampleIterates_eq_half_add_geometricTail t)
  have hiter_nonneg : 0 ≤ exercise_8_11_counterexample_iterates t 0 := by
    have htail_nonneg : 0 ≤ ((2 : ℝ) ^ (t + 1))⁻¹ := by positivity
    linarith
  have hfx :
      exercise_8_11_counterexample_function (exercise_8_11_counterexample_iterates t) =
        exercise_8_11_counterexample_iterates t 0 := by
    -- Positivity removes the absolute value at the current iterate.
    simp [exercise_8_11_counterexample_function, abs_of_nonneg hiter_nonneg]
  have hsum :
      ∑ i, exercise_8_11_counterexample_subgradient t i *
        (y i - exercise_8_11_counterexample_iterates t i) =
          y 0 - exercise_8_11_counterexample_iterates t 0 := by
    -- In dimension one the affine term has only one coordinate.
    simp [exercise_8_11_counterexample_subgradient]
  -- The affine lower bound reduces to the scalar inequality `|y₀| ≥ y₀`.
  calc
    exercise_8_11_counterexample_function y = |y 0| := rfl
    _ ≥ y 0 := by exact le_abs_self (y 0)
    _ =
        exercise_8_11_counterexample_function (exercise_8_11_counterexample_iterates t) +
          ∑ i, exercise_8_11_counterexample_subgradient t i *
            (y i - exercise_8_11_counterexample_iterates t i) := by
          rw [hfx, hsum]
          ring

/-- Exercise 8.11 (2). The counterexample function `x ↦ |x|` is convex. -/
theorem exercise_8_11_counterexample_function_convex :
    ConvexOn ℝ Set.univ exercise_8_11_counterexample_function := by
  -- Realize `x ↦ |x 0|` as the norm composed with the coordinate projection.
  simpa [exercise_8_11_counterexample_function, Real.norm_eq_abs] using
    (convexOn_univ_norm.comp_linearMap (LinearMap.proj 0 : (Fin 1 → ℝ) →ₗ[ℝ] ℝ))

/-- Exercise 8.11 (3). The counterexample stepsizes `α_t = 2^{-(t+2)}` are nonnegative. -/
theorem exercise_8_11_counterexample_steps_nonneg
    (t : ℕ) :
    0 ≤ exercise_8_11_counterexample_steps t := by
  -- Reciprocal powers of the positive number `2` are nonnegative.
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (t + 2) := by positivity
  change 0 ≤ ((2 : ℝ) ^ (t + 2))⁻¹
  exact inv_nonneg.mpr hpow_nonneg

/-- Exercise 8.11 (4). The counterexample stepsizes `α_t = 2^{-(t+2)}` are summable. -/
theorem exercise_8_11_counterexample_steps_summable :
    Summable exercise_8_11_counterexample_steps := by
  -- This is a geometric series with ratio `1/2`, scaled by `1/4`.
  have hgeom : Summable (fun t : ℕ ↦ (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ t)) := by
    exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left (1 / 4 : ℝ)
  have hsteps :
      exercise_8_11_counterexample_steps = fun t : ℕ ↦ (1 / 4 : ℝ) * ((1 / 2 : ℝ) ^ t) := by
    funext t
    rw [exercise_8_11_counterexample_steps]
    rw [show ((1 / 2 : ℝ) ^ t) = ((2 : ℝ) ^ t)⁻¹ by simp [one_div, inv_pow]]
    rw [show t + 2 = t + 1 + 1 by omega, pow_succ, pow_succ]
    field_simp
    ring
  rw [hsteps]
  exact hgeom

/-- Exercise 8.11 (5). The counterexample iterates start at `x₀ = 1`. -/
theorem exercise_8_11_counterexample_iterates_zero :
    exercise_8_11_counterexample_iterates 0 = exercise_8_11_counterexample_start := by
  -- The empty partial sum leaves the starting point unchanged.
  ext i
  fin_cases i
  simp [exercise_8_11_counterexample_iterates, exercise_8_11_counterexample_start]

/-- Exercise 8.11 (6). The counterexample iterates are generated by the subgradient method for
`x ↦ |x|` with the chosen stepsizes and subgradients. -/
theorem exercise_8_11_counterexample_is_subgradient_method_sequence :
    IsSubgradientMethodSequence
      exercise_8_11_counterexample_function
      exercise_8_11_counterexample_steps
      exercise_8_11_counterexample_iterates
      exercise_8_11_counterexample_subgradient := by
  intro t
  constructor
  · -- The chosen constant direction is a valid subgradient at every iterate.
    exact counterexampleSubgradientAtIterate t
  · -- Expanding the next partial sum matches one subgradient step.
    ext i
    fin_cases i
    simp [exercise_8_11_counterexample_iterates, subgradient_step,
      exercise_8_11_counterexample_subgradient, Finset.sum_range_succ, sub_eq_add_neg,
      add_assoc, add_comm]

/-- Exercise 8.11 (7). The counterexample iterates converge to the limit point `1/2`. -/
theorem exercise_8_11_counterexample_iterates_tendsto_limit :
    Filter.Tendsto
      exercise_8_11_counterexample_iterates
      Filter.atTop
      (nhds exercise_8_11_counterexample_limit) := by
  refine tendsto_pi_nhds.2 ?_
  intro i
  fin_cases i
  have hpow :
      Filter.Tendsto
        (fun t : ℕ ↦ ((1 / 2 : ℝ) ^ t))
        Filter.atTop
        (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  have htail :
      Filter.Tendsto
        (fun t : ℕ ↦ ((1 / 2 : ℝ) ^ (t + 1)))
        Filter.atTop
        (nhds 0) :=
    hpow.comp (Filter.tendsto_add_atTop_nat 1)
  have hcoord :
      Filter.Tendsto
        (fun t : ℕ ↦ (1 / 2 : ℝ) + ((1 / 2 : ℝ) ^ (t + 1)))
        Filter.atTop
        (nhds ((1 / 2 : ℝ) + 0)) :=
    tendsto_const_nhds.add htail
  -- Rewrite the iterate and the limit into the same scalar closed form.
  simpa [exercise_8_11_counterexample_limit, counterexampleIterates_eq_half_add_geometricTail,
    one_div, inv_pow] using hcoord

/-- Exercise 8.11 (8). The counterexample limit `1/2` is not an optimal point of `x ↦ |x|`. -/
theorem exercise_8_11_counterexample_limit_not_optimal :
    ¬ IsMinOn
      exercise_8_11_counterexample_function
      Set.univ
      exercise_8_11_counterexample_limit := by
  intro hmin
  have hzero := isMinOn_iff.mp hmin (fun _ ↦ 0) (by simp)
  -- The origin has smaller objective value than the claimed limit `1/2`.
  simp [exercise_8_11_counterexample_function, exercise_8_11_counterexample_limit] at hzero
  norm_num at hzero

end Exercise811

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.Extr

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {ι : Type*} [Fintype ι]

/-
Domain sampling for Lemma 9.15 uses the existing optimization owner `IsMinOn` from mathlib and
the nearby project pattern of a concrete objective together with atomic minimizer/value lemmas, as
in `finite_intersection_orthogonal_projection_isMinOn` with its direct quadratic objective surface
and the canonical Chapter 8 argmin owner applied to
`polytope_quadratic_vertex_linear_objective`.

This item is `source-facing`: it introduces the fixed-iteration ratio objective and the constant
step family singled out by the textbook. The primitive data are the coefficients `α`, `β`, the
finite index family of steps, and the step family itself. The `core/canonical` owner for the
finite aggregation is therefore an arbitrary `Fintype`-indexed family `ι → ℝ`; the textbook
`m`-step presentation is the specialization `ι = Fin m`, not a second owner. Positivity of the
uniform family and its minimizing property are derived API, so they are stated as separate
theorems rather than bundled into one conjunction. -/

/-- The objective function in the fixed-iteration step-size optimization problem. -/
def fixed_iteration_objective (α β : ℝ) (t : ι → ℝ) : ℝ :=
  (α + β * ∑ k, (t k) ^ 2) / ∑ k, t k

/-- The constant step family `t_i = √(α / (β |ι|))` from Lemma 9.15. -/
def fixed_iteration_uniform_steps (ι : Type*) [Fintype ι] (α β : ℝ) : ι → ℝ :=
  fun _ ↦ Real.sqrt (α / (β * Fintype.card ι))

-- Proof sketch: `fixed_iteration_uniform_steps` is definitionally a constant function.
/-- The uniform family from Lemma 9.15 is the constant function with value
`√(α / (β |ι|))`. -/
theorem fixed_iteration_uniform_steps_eq_const (α β : ℝ) :
    fixed_iteration_uniform_steps ι α β = fun _ ↦ Real.sqrt (α / (β * Fintype.card ι)) := rfl

-- Proof sketch: unfold `fixed_iteration_uniform_steps`; every coordinate is definitionally the
-- same constant `√(α / (β |ι|))`.
/-- Evaluating `fixed_iteration_uniform_steps α β` at any index gives `√(α / (β |ι|))`. -/
@[simp] theorem fixed_iteration_uniform_steps_apply
    (α β : ℝ) (i : ι) :
    fixed_iteration_uniform_steps ι α β i = Real.sqrt (α / (β * Fintype.card ι)) := rfl

-- Proof sketch: use `hα`, `hβ`, and finiteness with `Nonempty ι` to show
-- `α / (β |ι|)` is positive and apply the positivity of `Real.sqrt`.
/-- The constant step family from Lemma 9.15 is positive coordinatewise when `α` and `β`
are positive. -/
theorem fixed_iteration_uniform_steps_pos
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ i : ι, 0 < fixed_iteration_uniform_steps ι α β i := by
  -- The square-root argument is positive because `α`, `β`, and `|ι|` are positive.
  have hn : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have harg : 0 < α / (β * (Fintype.card ι : ℝ)) := by
    exact div_pos hα (mul_pos hβ hn)
  intro i
  -- Each coordinate is the positive square root of that positive scalar.
  simpa [fixed_iteration_uniform_steps_apply] using Real.sqrt_pos_of_pos harg

/-- Helper for Lemma 9.15: the sum of a positive finite family is positive. -/
lemma sum_pos_of_pos
    [Nonempty ι] {t : ι → ℝ} (ht : ∀ i, 0 < t i) :
    0 < ∑ i, t i := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty ι›
  -- Compare the whole sum to a single positive summand.
  have hi0 : t i0 ≤ ∑ i, t i := by
    simpa using Finset.single_le_sum (fun i _ ↦ le_of_lt (ht i)) (by simp)
  exact lt_of_lt_of_le (ht i0) hi0

/-- Helper for Lemma 9.15: Cauchy-Schwarz reduces the ratio objective to a scalar lower model
in the total sum `∑ i, t i`. -/
lemma fixedIterationObjectiveGeReducedObjective
    [Nonempty ι] {α β : ℝ} (hβ : 0 < β) {t : ι → ℝ} (ht : ∀ i, 0 < t i) :
    let S := ∑ i, t i
    let n : ℝ := Fintype.card ι
    fixed_iteration_objective α β t ≥ α / S + (β / n) * S := by
  classical
  let S := ∑ i, t i
  let Q := ∑ i, (t i) ^ 2
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hS : 0 < S := by
    simpa [S] using sum_pos_of_pos (ι := ι) ht
  -- Cauchy-Schwarz gives `S^2 ≤ n * Q` for the constant-one comparison family.
  have hsq : S ^ 2 ≤ n * Q := by
    simpa [S, Q, n, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ t fun _ ↦ (1 : ℝ))
  -- Dividing the Cauchy bound by the positive denominators yields the reduced model.
  have hdiv : (β / n) * S ≤ β * Q / S := by
    have hqs : S / n ≤ Q / S := by
      field_simp [hS.ne', hn.ne']
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq
    have hβnonneg : 0 ≤ β := le_of_lt hβ
    have hmul := mul_le_mul_of_nonneg_left hqs hβnonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
  -- Rewrite the objective and insert the lower bound above.
  calc
    fixed_iteration_objective α β t
        = (α + β * Q) / S := by
            simp [fixed_iteration_objective, S, Q]
    _ = α / S + β * Q / S := by
          field_simp [hS.ne']
    _ ≥ α / S + (β / n) * S := by
          have hcomp : α / S + (β / n) * S ≤ α / S + β * Q / S := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hdiv (α / S)
          exact hcomp

/-- Helper for Lemma 9.15: the reduced scalar model is bounded below by the claimed optimal
value. -/
lemma fixedIterationReducedObjectiveGeOptimalValue
    [Nonempty ι] {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 < s) :
    let n : ℝ := Fintype.card ι
    α / s + (β / n) * s ≥ 2 * Real.sqrt (α * β / n) := by
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have ha : 0 ≤ α / s := by
    exact le_of_lt (div_pos hα hs)
  have hb : 0 ≤ (β / n) * s := by
    exact le_of_lt (mul_pos (div_pos hβ hn) hs)
  have harg_nonneg : 0 ≤ α * β / n := by
    exact le_of_lt (div_pos (mul_pos hα hβ) hn)
  -- The square-root term is an exact square root of the product of the two summands.
  have hsq :
      (Real.sqrt (α * β / n)) ^ 2 = (α / s) * ((β / n) * s) := by
    rw [Real.sq_sqrt harg_nonneg]
    field_simp [hs.ne', hn.ne']
  -- Apply the squared AM-GM inequality with that exact witness.
  simpa [n, add_comm, add_left_comm, add_assoc] using
    two_mul_le_add_of_sq_eq_mul ha hb hsq

/-- Helper for Lemma 9.15: evaluating the fixed-iteration objective on the uniform step family
gives the closed-form optimal value. -/
lemma fixedIterationUniformObjectiveEqOptimalValue
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    fixed_iteration_objective α β (fixed_iteration_uniform_steps ι α β) =
      2 * Real.sqrt (α * β / Fintype.card ι) := by
  let n : ℝ := Fintype.card ι
  let c := Real.sqrt (α / (β * n))
  have hn : 0 < n := by
    change 0 < (Fintype.card ι : ℝ)
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hc : 0 < c := by
    apply Real.sqrt_pos_of_pos
    exact div_pos hα (mul_pos hβ hn)
  have hc_sq : c ^ 2 = α / (β * n) := by
    simpa [c] using (Real.sq_sqrt (le_of_lt (div_pos hα (mul_pos hβ hn))))
  have hαeq : α = β * n * c ^ 2 := by
    rw [hc_sq]
    field_simp [hβ.ne', hn.ne']
  have hβc_sq : (β * c) ^ 2 = α * β / n := by
    calc
      (β * c) ^ 2 = β ^ 2 * c ^ 2 := by ring
      _ = β ^ 2 * (α / (β * n)) := by rw [hc_sq]
      _ = α * β / n := by
            field_simp [hβ.ne', hn.ne']
  have hβc : β * c = Real.sqrt (α * β / n) := by
    -- Identify `β * c` with the nonnegative square root of `α * β / n`.
    calc
      β * c = Real.sqrt ((β * c) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hβ) hc.le)]
      _ = Real.sqrt (α * β / n) := by rw [hβc_sq]
  -- Normalize the finite sums of the constant family and simplify with `c^2 = α / (β n)`.
  calc
    fixed_iteration_objective α β (fixed_iteration_uniform_steps ι α β)
        = (α + β * (n * c ^ 2)) / (n * c) := by
            unfold fixed_iteration_objective
            simp [c, n, pow_two]
    _ = (2 * β * n * c ^ 2) / (n * c) := by rw [hαeq]; ring
    _ = 2 * (β * c) := by
          field_simp [hn.ne', hc.ne']
    _ = 2 * Real.sqrt (α * β / n) := by rw [hβc]
    _ = 2 * Real.sqrt (α * β / Fintype.card ι) := by
          simp [n]

-- Proof sketch: use permutation symmetry to reduce to equal coordinates, then solve the
-- resulting one-variable minimization problem on the positive half-line.
/-- Lemma 9.15: for positive `α` and `β`, the ratio
`(α + β * ∑ i, t i ^ 2) / (∑ i, t i)` is minimized over positive step sizes by the constant
choice `t_i = √(α / (β |ι|))`. Specializing to `ι = Fin m` recovers the textbook `m`-step
statement. -/
theorem fixed_iteration_objective_minimized_by_uniform_steps
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsMinOn (fixed_iteration_objective α β)
      {t : ι → ℝ | ∀ i, 0 < t i}
      (fixed_iteration_uniform_steps ι α β) := by
  -- Route correction: use Cauchy-Schwarz and scalar AM-GM instead of a convexity formalization.
  refine isMinOn_iff.mpr ?_
  intro t ht
  -- First compare any feasible family with the reduced scalar model in `∑ i, t i`.
  have hlower :=
    fixedIterationObjectiveGeReducedObjective (ι := ι) (α := α) (β := β) hβ ht
  have hsum_pos : 0 < ∑ i, t i := sum_pos_of_pos (ι := ι) ht
  -- Then close the scalar model by AM-GM and identify the uniform family as the equality case.
  calc
    fixed_iteration_objective α β (fixed_iteration_uniform_steps ι α β)
        = 2 * Real.sqrt (α * β / Fintype.card ι) := by
            exact fixedIterationUniformObjectiveEqOptimalValue (ι := ι) hα hβ
    _ ≤ α / (∑ i, t i) + (β / (Fintype.card ι : ℝ)) * (∑ i, t i) := by
          simpa using
            fixedIterationReducedObjectiveGeOptimalValue (ι := ι) (α := α) (β := β)
              (s := ∑ i, t i) hα hβ hsum_pos
    _ ≤ fixed_iteration_objective α β t := by
          simpa using hlower

-- Proof sketch: evaluate the objective on the constant minimizer and simplify the resulting
-- finite sums to obtain the closed-form value.
/-- The uniform minimizer of `fixed_iteration_objective` attains the value
`2 * √(α * β / |ι|)`. -/
theorem fixed_iteration_objective_uniform_step_value
    [Nonempty ι] {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    fixed_iteration_objective α β (fixed_iteration_uniform_steps ι α β) =
      2 * Real.sqrt (α * β / Fintype.card ι) := by
  -- This is exactly the closed-form evaluation established in the helper lemma above.
  simpa using fixedIterationUniformObjectiveEqOptimalValue (ι := ι) hα hβ

end

/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw

public section

noncomputable section

open scoped ProbabilityTheory NNReal

namespace ProbabilityTheory

/-- Helper for Exercise 4.4: the square of the identity is integrable under `Po(ℝ, r)`. -/
lemma integrable_sq_id_mapCastPoissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun x : ℝ ↦ x ^ 2) Po(ℝ, r) := by
  let firstFactorial : ℕ → ℝ :=
    fun n ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) * (n : ℝ)
  let secondFactorial : ℕ → ℝ :=
    fun n ↦
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) *
        ((n : ℝ) * ((n : ℝ) - 1))
  have hfirstShift :
      (fun n : ℕ ↦ firstFactorial (n + 1)) =
        fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    dsimp [firstFactorial]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
    rw [Nat.cast_add, Nat.cast_one]
    have h0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h0, h1]
  have hsecondShift :
      (fun n : ℕ ↦ secondFactorial (n + 2)) =
        fun n : ℕ ↦
          (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    dsimp [secondFactorial]
    rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    have h0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h0, h1, h2]
    ring_nf
  have hs_first : Summable firstFactorial := by
    exact (summable_nat_add_iff 1 (f := firstFactorial)).1 <| by
      have hbase :
        Summable (fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        exact (Real.summable_pow_div_factorial (r : ℝ)).mul_left
          (Real.exp (-(r : ℝ)) * (r : ℝ))
      rwa [hfirstShift]
  have hs_second : Summable secondFactorial := by
    exact (summable_nat_add_iff 2 (f := secondFactorial)).1 <| by
      have hbase :
        Summable (fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2 * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        exact (Real.summable_pow_div_factorial (r : ℝ)).mul_left
          (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2)
      rwa [hsecondShift]
  -- Rewrite the square moment as the sum of the first two factorial moments.
  have h_nat : MeasureTheory.Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) Po(r) := by
    rw [integrable_poissonMeasure_iff]
    convert hs_second.add hs_first using 1
    funext n
    change
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) * ‖(n : ℝ) ^ 2‖ =
        secondFactorial n + firstFactorial n
    have hnorm : ‖((n : ℝ) ^ 2)‖ = (n : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [hnorm]
    dsimp [firstFactorial, secondFactorial]
    ring
  exact (MeasureTheory.integrable_map_measure (by fun_prop) (by fun_prop)).2 h_nat

/-- The identity function has expectation equal to the Poisson rate under `Po(ℝ, r)`. -/
theorem integral_id_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ∂Po(ℝ, r) = (r : ℝ) := by
  let firstFactorial : ℕ → ℝ :=
    fun n ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) * (n : ℝ)
  have hfirstShift :
      (fun n : ℕ ↦ firstFactorial (n + 1)) =
        fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    dsimp [firstFactorial]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
    rw [Nat.cast_add, Nat.cast_one]
    have h0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h0, h1]
  have hs_first : Summable firstFactorial := by
    exact (summable_nat_add_iff 1 (f := firstFactorial)).1 <| by
      have hbase :
        Summable (fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        exact (Real.summable_pow_div_factorial (r : ℝ)).mul_left
          (Real.exp (-(r : ℝ)) * (r : ℝ))
      rwa [hfirstShift]
  -- Shift the series once so that the factor `n` cancels against `(n + 1)!`.
  calc
    ∫ x, x ∂Po(ℝ, r) = ∫ n, (n : ℝ) ∂Po(r) := by
      simpa using
        (MeasureTheory.integral_map (μ := Po(r)) (φ := Nat.cast)
          (hφ := by fun_prop) (f := fun x : ℝ ↦ x) aestronglyMeasurable_id)
    _ = ∑' n, firstFactorial n := by
      rw [integral_poissonMeasure]
      simp [firstFactorial]
    _ = ∑ i ∈ Finset.range 1, firstFactorial i + ∑' i, firstFactorial (i + 1) := by
      symm
      exact Summable.sum_add_tsum_nat_add 1 hs_first
    _ = ∑' i, firstFactorial (i + 1) := by
      simp [firstFactorial]
    _ = ∑' n, Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
      rw [hfirstShift]
    _ = (Real.exp (-(r : ℝ)) * (r : ℝ)) * ∑' n, (r : ℝ) ^ n / (Nat.factorial n : ℝ) := by
      rw [tsum_mul_left]
    _ = (Real.exp (-(r : ℝ)) * (r : ℝ)) * NormedSpace.exp (r : ℝ) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).tsum_eq]
    _ = (Real.exp (-(r : ℝ)) * (r : ℝ)) * Real.exp (r : ℝ) := by
      rw [Real.exp_eq_exp_ℝ]
    _ = (r : ℝ) := by
      calc
        (Real.exp (-(r : ℝ)) * (r : ℝ)) * Real.exp (r : ℝ)
            = (r : ℝ) * (Real.exp (-(r : ℝ)) * Real.exp (r : ℝ)) := by ring
        _ = (r : ℝ) * Real.exp (-(r : ℝ) + r) := by rw [← Real.exp_add]
        _ = (r : ℝ) := by simp

/-- Helper for Exercise 4.4: the second moment of the identity under `Po(ℝ, r)` is `r^2 + r`. -/
lemma integral_sq_id_mapCastPoissonMeasure (r : ℝ≥0) :
    ∫ x, x ^ 2 ∂Po(ℝ, r) = (r : ℝ) ^ 2 + r := by
  let firstFactorial : ℕ → ℝ :=
    fun n ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) * (n : ℝ)
  let secondFactorial : ℕ → ℝ :=
    fun n ↦
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (Nat.factorial n : ℝ) *
        ((n : ℝ) * ((n : ℝ) - 1))
  have hsecondShift :
      (fun n : ℕ ↦ secondFactorial (n + 2)) =
        fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2 * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    funext n
    dsimp [secondFactorial]
    rw [pow_succ, pow_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    have h0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h0, h1, h2]
    ring_nf
  have hs_first : Summable firstFactorial := by
    exact (summable_nat_add_iff 1 (f := firstFactorial)).1 <| by
      have hbase :
        Summable (fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        exact (Real.summable_pow_div_factorial (r : ℝ)).mul_left
          (Real.exp (-(r : ℝ)) * (r : ℝ))
      have hfirstShift :
        (fun n : ℕ ↦ firstFactorial (n + 1)) =
          fun n : ℕ ↦
            (Real.exp (-(r : ℝ)) * (r : ℝ)) * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
        funext n
        dsimp [firstFactorial]
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
        rw [Nat.cast_add, Nat.cast_one]
        have h0 : (Nat.factorial n : ℝ) ≠ 0 := by positivity
        have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [h0, h1]
      rwa [hfirstShift]
  have hs_second : Summable secondFactorial := by
    exact (summable_nat_add_iff 2 (f := secondFactorial)).1 <| by
      have hbase :
        Summable (fun n : ℕ ↦
          Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2 * ((r : ℝ) ^ n / (Nat.factorial n : ℝ))) := by
        exact (Real.summable_pow_div_factorial (r : ℝ)).mul_left
          (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2)
      rwa [hsecondShift]
  have hsecond :
      ∑' n, secondFactorial n = (r : ℝ) ^ 2 := by
    calc
      ∑' n, secondFactorial n
          = ∑ i ∈ Finset.range 2, secondFactorial i + ∑' i, secondFactorial (i + 2) := by
              symm
              exact Summable.sum_add_tsum_nat_add 2 hs_second
      _ = ∑' i, secondFactorial (i + 2) := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
            simp [secondFactorial]
      _ = ∑' n, Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2 * ((r : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
            rw [hsecondShift]
      _ = (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * ∑' n, (r : ℝ) ^ n / (Nat.factorial n : ℝ) := by
            rw [tsum_mul_left]
      _ = (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * NormedSpace.exp (r : ℝ) := by
            rw [(NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).tsum_eq]
      _ = (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * Real.exp (r : ℝ) := by
            rw [Real.exp_eq_exp_ℝ]
      _ = (r : ℝ) ^ 2 := by
            calc
              (Real.exp (-(r : ℝ)) * (r : ℝ) ^ 2) * Real.exp (r : ℝ)
                  = (r : ℝ) ^ 2 * (Real.exp (-(r : ℝ)) * Real.exp (r : ℝ)) := by ring
              _ = (r : ℝ) ^ 2 * Real.exp (-(r : ℝ) + r) := by rw [← Real.exp_add]
              _ = (r : ℝ) ^ 2 := by simp
  have hfirst :
      ∑' n, firstFactorial n = (r : ℝ) := by
    calc
      ∑' n, firstFactorial n = ∫ n, (n : ℝ) ∂Po(r) := by
        rw [integral_poissonMeasure]
        simp [firstFactorial]
      _ = ∫ x, x ∂Po(ℝ, r) := by
        symm
        simpa using
          (MeasureTheory.integral_map (μ := Po(r)) (φ := Nat.cast)
            (hφ := by fun_prop) (f := fun x : ℝ ↦ x) aestronglyMeasurable_id)
      _ = (r : ℝ) := integral_id_map_cast_poissonMeasure r
  -- Express `x^2` as `x (x - 1) + x` and evaluate the two factorial moments.
  calc
    ∫ x, x ^ 2 ∂Po(ℝ, r) = ∫ n, (n : ℝ) ^ 2 ∂Po(r) := by
      simpa using
        (MeasureTheory.integral_map (μ := Po(r)) (φ := Nat.cast)
          (hφ := by fun_prop) (f := fun x : ℝ ↦ x ^ 2) (by fun_prop))
    _ = ∑' n, (secondFactorial n + firstFactorial n) := by
      rw [integral_poissonMeasure]
      congr with n
      dsimp [firstFactorial, secondFactorial]
      ring
    _ = ∑' n, secondFactorial n + ∑' n, firstFactorial n := by
      exact (hs_second.hasSum.add hs_first.hasSum).tsum_eq
    _ = (r : ℝ) ^ 2 + r := by rw [hsecond, hfirst]

/-- The identity function has variance equal to the Poisson rate under `Po(ℝ, r)`. -/
theorem variance_id_map_cast_poissonMeasure (r : ℝ≥0) :
    Var[id; Po(ℝ, r)] = (r : ℝ) := by
  have hmem : MeasureTheory.MemLp (fun x : ℝ ↦ x) 2 Po(ℝ, r) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_sq_id_mapCastPoissonMeasure r)
  have hsq : ∫ x : ℝ, ((fun y : ℝ ↦ y) ^ 2) x ∂Po(ℝ, r) = (r : ℝ) ^ 2 + r := by
    simpa using integral_sq_id_mapCastPoissonMeasure r
  rw [show Var[id; Po(ℝ, r)] = Var[fun x : ℝ ↦ x; Po(ℝ, r)] by rfl]
  rw [variance_eq_sub hmem, hsq, integral_id_map_cast_poissonMeasure]
  ring

end ProbabilityTheory

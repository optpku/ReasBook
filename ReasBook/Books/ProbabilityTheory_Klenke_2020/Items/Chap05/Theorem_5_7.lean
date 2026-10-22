/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

noncomputable section

/- Theorem 5.7 (1): The covariance map is symmetric on real random variables, hence in
particular on `ℒ²(μ)`. -/
recall covariance_comm

-- Proof sketch: rewrite `cov[X, X; μ]` as `Var[X; μ]` using `ProbabilityTheory.covariance_self`,
-- then apply `ProbabilityTheory.variance_nonneg`.
/-- Theorem 5.7 (2): Covariance is positive semidefinite on `ℒ²(μ)`, i.e.
`0 ≤ cov[X, X; μ]` for every square-integrable real random variable `X`. -/
theorem covariance_self_nonneg_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    0 ≤ cov[X, X; μ] := by
  rw [covariance_self hX.aemeasurable]
  exact variance_nonneg X μ

variable [IsProbabilityMeasure μ]

-- Proof sketch: replace `Y` by the almost-surely equal constant function in the covariance
-- integral, then use `ProbabilityTheory.covariance_const_right`.
/-- Theorem 5.7 (3): The covariance with a real random variable that is almost surely equal to a
constant `c` is zero. -/
theorem covariance_eq_zero_of_ae_eq_const_right {X Y : Ω → ℝ} {c : ℝ}
    (hY : Y =ᵐ[μ] fun _ ↦ c) :
    cov[X, Y; μ] = 0 := by
  have hμY : μ[Y] = c := by
    simpa using integral_congr_ae hY
  rw [ProbabilityTheory.covariance]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hY] with ω hω
  simp [hω, hμY]

-- Proof sketch: remove the additive constants with
-- `ProbabilityTheory.covariance_const_add_left/right`, expand the two finite sums with
-- `ProbabilityTheory.covariance_fun_sum_fun_sum`, and pull the scalar coefficients out with
-- `ProbabilityTheory.covariance_const_mul_left/right`.
/-- Theorem 5.7 (4): Equation `(5.1)`. The covariance of two affine finite linear combinations of
square-integrable real random variables is the corresponding double sum of pairwise covariances. -/
theorem covariance_affine_combination_eq_sum {m n : ℕ} {X : Fin m → Ω → ℝ} {Y : Fin n → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ j, MemLp (Y j) 2 μ)
    (α : Fin m → ℝ) (β : Fin n → ℝ) (d e : ℝ) :
    cov[fun ω ↦ d + ∑ i, α i * X i ω, fun ω ↦ e + ∑ j, β j * Y j ω; μ] =
      ∑ i, ∑ j, α i * β j * cov[X i, Y j; μ] := by
  let X' : Fin m → Ω → ℝ := fun i ω ↦ α i * X i ω
  let Y' : Fin n → Ω → ℝ := fun j ω ↦ β j * Y j ω
  have hX' : ∀ i, MemLp (X' i) 2 μ := fun i ↦ (hX i).const_mul (α i)
  have hY' : ∀ j, MemLp (Y' j) 2 μ := fun j ↦ (hY j).const_mul (β j)
  have hsumX_memLp : MemLp (fun ω ↦ ∑ i, X' i ω) 2 μ := by
    convert memLp_finset_sum' Finset.univ (fun i _ ↦ hX' i) using 1
    ext ω
    simp [X']
  have hsumY_memLp : MemLp (fun ω ↦ ∑ j, Y' j ω) 2 μ := by
    convert memLp_finset_sum' Finset.univ (fun j _ ↦ hY' j) using 1
    ext ω
    simp [Y']
  have hsumX : Integrable (fun ω ↦ ∑ i, X' i ω) μ := hsumX_memLp.integrable (by simp)
  have hsumY : Integrable (fun ω ↦ ∑ j, Y' j ω) μ := hsumY_memLp.integrable (by simp)
  rw [covariance_const_add_left hsumX d, covariance_const_add_right hsumY e,
    covariance_fun_sum_fun_sum hX' hY']
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show cov[X' i, Y' j; μ] = α i * β j * cov[X i, Y j; μ] by
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring]

/- Theorem 5.7 (5): In particular, for every real scalar `α`, the variance scales quadratically:
`Var[α • X; μ] = α^2 Var[X; μ]`. -/
recall variance_smul

-- Proof sketch: start from `ProbabilityTheory.variance_sum`, split the double covariance sum into
-- diagonal and off-diagonal terms, and rewrite the diagonal terms using
-- `ProbabilityTheory.covariance_self`.
/-- Theorem 5.7 (6): Equation `(5.2)` (Bienayme formula). For a finite family of square-integrable
real random variables, the variance of the sum is the sum of the variances plus the ordered
off-diagonal covariance sum. -/
theorem variance_sum_eq_sum_variance_add_sum_covariance_off_diagonal {m : ℕ}
    {X : Fin m → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[∑ i, X i; μ] =
      (∑ i, Var[X i; μ]) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, cov[X i, X j; μ] := by
  calc
    Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ] := variance_sum hX
    _ = ∑ i, (cov[X i, X i; μ] + ∑ j ∈ Finset.univ.erase i, cov[X i, X j; μ]) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hsplit :=
            Finset.sum_erase_add Finset.univ
              (fun j ↦ cov[X i, X j; μ]) (Finset.mem_univ i)
          rw [add_comm] at hsplit
          exact hsplit.symm
    _ = ∑ i, (Var[X i; μ] + ∑ j ∈ Finset.univ.erase i, cov[X i, X j; μ]) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [covariance_self (hX i).aemeasurable]
    _ = (∑ i, Var[X i; μ]) + ∑ i, ∑ j ∈ Finset.univ.erase i, cov[X i, X j; μ] := by
          rw [Finset.sum_add_distrib]

-- Proof sketch: combine the Bienayme formula of clause `(6)` with the hypothesis that every
-- off-diagonal covariance vanishes.
/-- Theorem 5.7 (7): For pairwise uncorrelated square-integrable real random variables, the
variance of the finite sum is the sum of the variances. -/
theorem variance_sum_eq_sum_variance_of_pairwise_uncorrelated {m : ℕ}
    {X : Fin m → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (h_uncorr : Pairwise fun i j ↦ cov[X i, X j; μ] = 0) :
    Var[∑ i, X i; μ] = ∑ i, Var[X i; μ] := by
  rw [variance_sum_eq_sum_variance_add_sum_covariance_off_diagonal hX]
  have hoffdiag : ∑ i, ∑ j ∈ Finset.univ.erase i, cov[X i, X j; μ] = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact h_uncorr (fun hij ↦ hji hij.symm)
  rw [hoffdiag, add_zero]

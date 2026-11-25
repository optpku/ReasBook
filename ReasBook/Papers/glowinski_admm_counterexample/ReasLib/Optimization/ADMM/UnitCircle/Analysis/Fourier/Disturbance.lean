/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Bounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace ADMM.UnitCircle.Fourier

noncomputable section

/-- Finite-coordinate Cauchy--Schwarz, expressed in the square-energy normalization. -/
theorem finite_norm_product_bound {ι : Type*} [Fintype ι]
    (e y : ι → TimeSequence) :
    (∑ i, ‖e i‖ * ‖y i‖) ≤
      Real.sqrt (∑ i, ‖e i‖ ^ 2) * Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  have he : (0 : ℝ) ≤ ∑ i, ‖e i‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hy : (0 : ℝ) ≤ ∑ i, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hs : (0 : ℝ) ≤ ∑ i, ‖e i‖ * ‖y i‖ :=
    Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hp := mul_nonneg (Real.sqrt_nonneg (∑ i, ‖e i‖ ^ 2))
    (Real.sqrt_nonneg (∑ i, ‖y i‖ ^ 2))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ ‖e i‖) (fun i ↦ ‖y i‖)
  have heq : (Real.sqrt (∑ i, ‖e i‖ ^ 2) * Real.sqrt (∑ i, ‖y i‖ ^ 2)) ^ 2 =
      (∑ i, ‖e i‖ ^ 2) * (∑ i, ‖y i‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt he, Real.sq_sqrt hy]
  nlinarith

/-- Each actual disturbance/lag product has the expected operator-norm bound. -/
theorem disturbance_coordinate_bound {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (e y : TimeSequence) :
    (inner ℂ e (lagOperator c α b y)).re ≤ lagUniformBound c α * ‖e‖ * ‖y‖ := by
  calc
    (inner ℂ e (lagOperator c α b y)).re ≤ ‖inner ℂ e (lagOperator c α b y)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖e‖ * ‖lagOperator c α b y‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (lagUniformBound c α * ‖y‖) :=
      mul_le_mul_of_nonneg_left (lagOperator_norm_le_uniform c α b y) (norm_nonneg e)
    _ = _ := by ring

/-- The complete finite-coordinate disturbance cross term for the actual lag operators.
The estimate includes both blocks and works also in dimension zero. -/
theorem disturbance_cross_bound {ℓ m : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (e y : Fin 2 × Fin m → TimeSequence) :
    (∑ i : Fin 2 × Fin m, (inner ℂ (e i) (lagOperator c α i.1 (y i))).re) ≤
      lagUniformBound c α * Real.sqrt (∑ i : Fin 2 × Fin m, ‖e i‖ ^ 2) *
        Real.sqrt (∑ i : Fin 2 × Fin m, ‖y i‖ ^ 2) := by
  calc
    _ ≤ ∑ i : Fin 2 × Fin m, lagUniformBound c α * ‖e i‖ * ‖y i‖ :=
      Finset.sum_le_sum (fun i _ ↦ disturbance_coordinate_bound c α i.1 (e i) (y i))
    _ = lagUniformBound c α * (∑ i : Fin 2 × Fin m, ‖e i‖ * ‖y i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ lagUniformBound c α *
        (Real.sqrt (∑ i : Fin 2 × Fin m, ‖e i‖ ^ 2) *
          Real.sqrt (∑ i : Fin 2 × Fin m, ‖y i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (finite_norm_product_bound e y) (lagUniformBound_pos c α).le
    _ = _ := by ring

/-- The same bound with the separate block and coordinate indexing used by the ADMM orbit. -/
theorem disturbance_cross_bound_curried {ℓ m : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (e y : Fin 2 → Fin m → TimeSequence) :
    (∑ b : Fin 2, ∑ a : Fin m, (inner ℂ (e b a) (lagOperator c α b (y b a))).re) ≤
      lagUniformBound c α * Real.sqrt (∑ b : Fin 2, ∑ a : Fin m, ‖e b a‖ ^ 2) *
        Real.sqrt (∑ b : Fin 2, ∑ a : Fin m, ‖y b a‖ ^ 2) := by
  simpa only [Fintype.sum_prod_type] using
    disturbance_cross_bound c α (fun i ↦ e i.1 i.2) (fun i ↦ y i.1 i.2)

end

end ADMM.UnitCircle.Fourier

/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.ParsevalSupply

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory

noncomputable section

/-- Bilateral time shifts are isometries, proved from the actual Fourier transform. -/
theorem delay_norm (j : ℤ) (x : TimeSequence) : ‖delay j x‖ = ‖x‖ := by
  have h : ‖delay j x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← transformed_normSq_integral, ← transformed_normSq_integral]
    apply integral_congr_ae
    filter_upwards [transform_delay_ae j x] with t ht
    rw [ht, Complex.normSq_mul, Complex.normSq_eq_norm_sq (fourier j t),
      fourier_apply, Circle.norm_coe]
    simp
  nlinarith [norm_nonneg (delay j x), norm_nonneg x]

theorem backwardDifference_norm_le (α : ℝ) (j : ℕ) (x : TimeSequence) :
    ‖backwardDifference α j x‖ ≤ (1 + |α| ^ j) * ‖x‖ := by
  calc
    ‖backwardDifference α j x‖ ≤ ‖x‖ + ‖((α : ℂ) ^ j) • delay (j : ℤ) x‖ :=
      norm_sub_le _ _
    _ = (1 + |α| ^ j) * ‖x‖ := by
      rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, delay_norm]
      ring

theorem forwardDifference_norm_le (α : ℝ) (j : ℕ) (x : TimeSequence) :
    ‖forwardDifference α j x‖ ≤ (|α| ^ (2 * j) + |α| ^ j) * ‖x‖ := by
  calc
    ‖forwardDifference α j x‖ ≤
        ‖((α : ℂ) ^ (2 * j)) • x‖ + ‖((α : ℂ) ^ j) • delay (-(j : ℤ)) x‖ :=
      norm_sub_le _ _
    _ = (|α| ^ (2 * j) + |α| ^ j) * ‖x‖ := by
      rw [norm_smul, norm_smul, norm_pow, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, delay_norm]
      ring

def lagTermBound {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2) (i : Fin ℓ) : ℝ :=
  c.backward b i * (1 + |α| ^ (i.val + 1)) +
    c.forward b i * (|α| ^ (2 * (i.val + 1)) + |α| ^ (i.val + 1))

def lagBound {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2) : ℝ :=
  c.omega + ∑ i, lagTermBound c α b i

theorem lagTermBound_nonneg {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (i : Fin ℓ) : 0 ≤ lagTermBound c α b i := by
  dsimp [lagTermBound]
  exact add_nonneg (mul_nonneg (c.backward_nonneg b i) (by positivity))
    (mul_nonneg (c.forward_nonneg b i) (by positivity))

theorem lagBound_pos {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2) :
    0 < lagBound c α b :=
  add_pos_of_pos_of_nonneg c.omega_pos
    (Finset.sum_nonneg (fun i _ ↦ lagTermBound_nonneg c α b i))

theorem lagTerm_norm_le {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (i : Fin ℓ) (x : TimeSequence) :
    ‖lagTerm c α b i x‖ ≤ lagTermBound c α b i * ‖x‖ := by
  calc
    ‖lagTerm c α b i x‖ ≤
      ‖(c.backward b i : ℂ) • backwardDifference α (i.val + 1) x‖ +
        ‖(c.forward b i : ℂ) • forwardDifference α (i.val + 1) x‖ := norm_add_le _ _
    _ = c.backward b i * ‖backwardDifference α (i.val + 1) x‖ +
        c.forward b i * ‖forwardDifference α (i.val + 1) x‖ := by
      rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (c.backward_nonneg b i),
        abs_of_nonneg (c.forward_nonneg b i)]
    _ ≤ c.backward b i * ((1 + |α| ^ (i.val + 1)) * ‖x‖) +
        c.forward b i * ((|α| ^ (2 * (i.val + 1)) + |α| ^ (i.val + 1)) * ‖x‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (backwardDifference_norm_le α _ x) (c.backward_nonneg b i))
        (mul_le_mul_of_nonneg_left (forwardDifference_norm_le α _ x) (c.forward_nonneg b i))
    _ = lagTermBound c α b i * ‖x‖ := by dsimp [lagTermBound]; ring

/-- A finite explicit operator bound for the exact two-sided discounted multiplier. -/
theorem lagOperator_norm_le {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (x : TimeSequence) :
    ‖lagOperator c α b x‖ ≤ lagBound c α b * ‖x‖ := by
  have hs : ‖∑ i, lagTerm c α b i x‖ ≤ (∑ i, lagTermBound c α b i) * ‖x‖ := by
    calc
      _ ≤ ∑ i, ‖lagTerm c α b i x‖ := norm_sum_le _ _
      _ ≤ ∑ i, lagTermBound c α b i * ‖x‖ :=
        Finset.sum_le_sum (fun i _ ↦ lagTerm_norm_le c α b i x)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    ‖lagOperator c α b x‖ ≤ ‖(c.omega : ℂ) • x‖ + ‖∑ i, lagTerm c α b i x‖ :=
      norm_add_le _ _
    _ ≤ c.omega * ‖x‖ + (∑ i, lagTermBound c α b i) * ‖x‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos c.omega_pos]
      exact add_le_add le_rfl hs
    _ = lagBound c α b * ‖x‖ := by dsimp [lagBound]; ring

/-- One positive constant controls the actual lag operator in both blocks. -/
def lagUniformBound {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) : ℝ :=
  max (lagBound c α 0) (lagBound c α 1)

theorem lagUniformBound_pos {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) :
    0 < lagUniformBound c α := (lagBound_pos c α 0).trans_le (le_max_left _ _)

theorem lagBound_le_uniform {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2) :
    lagBound c α b ≤ lagUniformBound c α := by
  fin_cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem lagOperator_norm_le_uniform {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (x : TimeSequence) :
    ‖lagOperator c α b x‖ ≤ lagUniformBound c α * ‖x‖ :=
  (lagOperator_norm_le c α b x).trans
    (mul_le_mul_of_nonneg_right (lagBound_le_uniform c α b) (norm_nonneg x))

end

end ADMM.UnitCircle.Fourier

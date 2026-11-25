/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.ParsevalSupply
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.DiscountedCoercivity

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory
open scoped ComplexOrder

noncomputable section

/-- The complete discounted state dissipation, including its difference term. -/
def stateEnergy (α : ℝ) (s : Fin 2 → TimeSequence) : ℝ :=
  ‖difference α (s 0)‖ ^ 2 + ‖difference α (s 1)‖ ^ 2 +
    (1 - α) * (‖s 0‖ ^ 2 + ‖s 1‖ ^ 2)

def energyIntegrand (α : ℝ) (s : Fin 2 → TimeSequence) (t : AddCircle (1 : ℝ)) : ℝ :=
  Complex.normSq (delaySymbol α (circlePoint t) * transform (s 0) t) +
    Complex.normSq (delaySymbol α (circlePoint t) * transform (s 1) t) +
      (1 - α) * (Complex.normSq (transform (s 0) t) + Complex.normSq (transform (s 1) t))

theorem energyIntegrand_integrable (α : ℝ) (s : Fin 2 → TimeSequence) :
    Integrable (energyIntegrand α s) AddCircle.haarAddCircle :=
  ((residual_integrand_integrable α (s 0)).add
    (residual_integrand_integrable α (s 1))).add
      (((transformed_normSq_integrable (s 0)).add
        (transformed_normSq_integrable (s 1))).const_mul (1 - α))

theorem energyIntegrand_integral (α : ℝ) (s : Fin 2 → TimeSequence) :
    (∫ t : AddCircle (1 : ℝ), energyIntegrand α s t ∂AddCircle.haarAddCircle) =
      stateEnergy α s := by
  unfold energyIntegrand stateEnergy
  rw [integral_add, integral_add, integral_const_mul, integral_add,
    residual_integrand_integral, residual_integrand_integral,
    transformed_normSq_integral, transformed_normSq_integral]
  · exact transformed_normSq_integrable (s 0)
  · exact transformed_normSq_integrable (s 1)
  · exact residual_integrand_integrable α (s 0)
  · exact residual_integrand_integrable α (s 1)
  · exact (residual_integrand_integrable α (s 0)).add
      (residual_integrand_integrable α (s 1))
  · exact ((transformed_normSq_integrable (s 0)).add
      (transformed_normSq_integrable (s 1))).const_mul (1 - α)

/-- The actual discounted symbol estimate gives dissipation for all bilateral L² states. -/
theorem supply_dissipation {ℓ : ℕ} (c : LagWeights ℓ) (α γ c₀ : ℝ)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (s : Fin 2 → TimeSequence) :
    timeSupply c α γ s + c.epsilon * ‖difference α (s 1)‖ ^ 2 +
      c₀ * stateEnergy α s ≤ 0 := by
  have hpoint (t : AddCircle (1 : ℝ)) :
      c₀ * energyIntegrand α s t ≤
        quadratic (supplySymbol c α γ (circlePoint t)) (frequencyState s t) := by
    have h := quadratic_lower_bound (hQ (circlePoint t) (circlePoint_norm t)) (frequencyState s t)
    convert h using 1
    dsimp [energyIntegrand, frequencyState]
    rw [Complex.normSq_mul, Complex.normSq_mul]
    ring
  have hi := integral_mono ((energyIntegrand_integrable α s).const_mul c₀)
    (supply_quadratic_integrable c α γ s) hpoint
  rw [integral_const_mul, energyIntegrand_integral] at hi
  rw [supply_pairing_parseval]
  linarith

/-- An elementary norm estimate for the two actual output rows. -/
theorem pointSignal_energy_le (α : ℝ) (s : Fin 2 → TimeSequence) :
    ‖pointSignal α s 0‖ ^ 2 + ‖pointSignal α s 1‖ ^ 2 ≤
      3 * ‖s 0‖ ^ 2 + 2 * ‖difference α (s 1)‖ ^ 2 := by
  have h := norm_add_le (s 0) (difference α (s 1))
  have hs : ‖s 0 + difference α (s 1)‖ ^ 2 ≤
      2 * (‖s 0‖ ^ 2 + ‖difference α (s 1)‖ ^ 2) := by
    nlinarith [norm_nonneg (s 0), norm_nonneg (difference α (s 1)),
      norm_nonneg (s 0 + difference α (s 1)),
      sq_nonneg (‖s 0‖ - ‖difference α (s 1)‖)]
  simp only [pointSignal, ite_true, Fin.isValue, one_ne_zero, ite_false]
  linarith

/-- The discounted output separation estimate used in the causal homotopy proof. -/
theorem discounted_separation {ℓ : ℕ} (c : LagWeights ℓ)
    {α γ c₀ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc₀ : 0 < c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (s : Fin 2 → TimeSequence) :
    timeSupply c α γ s ≤ -(c₀ * (1 - α) / 6) *
      (‖pointSignal α s 0‖ ^ 2 + ‖pointSignal α s 1‖ ^ 2) := by
  have hd := supply_dissipation c α γ c₀ hQ s
  have hout := pointSignal_energy_le α s
  have henergy : (1 - α) / 6 *
      (‖pointSignal α s 0‖ ^ 2 + ‖pointSignal α s 1‖ ^ 2) ≤ stateEnergy α s := by
    have hh : 0 ≤ (1 - α) / 6 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hout hh
    dsimp [stateEnergy]
    nlinarith [sq_nonneg ‖s 0‖, sq_nonneg ‖s 1‖,
      sq_nonneg ‖difference α (s 0)‖, sq_nonneg ‖difference α (s 1)‖,
      mul_nonneg (sub_nonneg.mpr hα1.le) (sq_nonneg ‖s 1‖),
      mul_nonneg hα0 (sq_nonneg ‖difference α (s 1)‖)]
  have hc := mul_le_mul_of_nonneg_left henergy hc₀.le
  have heps := mul_nonneg c.epsilon_pos.le (sq_nonneg ‖difference α (s 1)‖)
  nlinarith

end

end ADMM.UnitCircle.Fourier

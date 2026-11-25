/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Pairing
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.ZeroStateSignals

@[expose] public section

open scoped BigOperators ENNReal ComplexOrder

namespace ADMM.UnitCircle.Causal

/-- The actual causal feedback pairing is the sum of the actual Fourier
state supplies, one for each physical coordinate. -/
theorem pureSupply_eq_timeSupply {m ℓ : ℕ} (c : LagWeights ℓ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (γ : ℝ)
    (y : ℕ → BlockVector m) (hy : Memℓp y 2) :
    pairedSupply c α (feedbackOperator α γ y) y
      (feedbackOperator_memℓp hα0 hα1 γ y hy) hy =
      ∑ a : Fin m, Fourier.timeSupply c α γ (zeroStateSignals hα0 hα1 y hy a) := by
  unfold pairedSupply Fourier.timeSupply
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [zeroStateSignals_normal, zeroStateSignals_point]

/-- Parseval separation now holds for the very feedback operator used by
the causal nonlinear recursion, rather than an abstract state realization. -/
theorem pureSupply_separation {m ℓ : ℕ} (c : LagWeights ℓ)
    {α γ c₀ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc₀ : 0 < c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (y : ℕ → BlockVector m) (hy : Memℓp y 2) :
    pairedSupply c α (feedbackOperator α γ y) y
      (feedbackOperator_memℓp hα0 hα1 γ y hy) hy ≤
      -(c₀ * (1 - α) / 6) * coordinateEnergy y hy := by
  rw [pureSupply_eq_timeSupply c hα0 hα1 γ y hy]
  calc
    _ ≤ ∑ a : Fin m, -(c₀ * (1 - α) / 6) *
        (‖coordinateLp y hy 0 a‖ ^ 2 + ‖coordinateLp y hy 1 a‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [zeroStateSignals_point] using Fourier.discounted_separation c hα0 hα1 hc₀ hQ
        (zeroStateSignals hα0 hα1 y hy a)
    _ = _ := by
      simp only [coordinateEnergy, Fin.sum_univ_two, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum]

end ADMM.UnitCircle.Causal

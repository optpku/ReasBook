/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.StateSignals
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.WeightedNorms

@[expose] public section

open ADMM.ConvergenceProof
open scoped BigOperators ComplexOrder

namespace ADMM.UnitCircle.Initialized

open Supply Fourier

noncomputable section

/-- The actual real auxiliary supply agrees with the scalar Fourier-coordinate pairings. -/
theorem auxiliary_block_pairing {m ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (η w : ℕ → Fin m → ℝ) (hη : SquareSummable α η) (hw : SquareSummable α w) (b : Fin 2) :
    (∑' k, timeWeight α k * blockSupply c b (auxPoint η w b) (auxNormal γ η w b) k) =
      ∑ a : Fin m, (inner ℂ
        (normalSignal α γ (stateCoordinates α η w hη hw a) b)
        (lagOperator c α b (pointSignal α (stateCoordinates α η w hη hw a) b))).re := by
  have h := congrArg Complex.re (weighted_blockSupply_inner c b α
    (auxPoint η w b) (auxNormal γ η w b)
    (auxPoint_summable hη hw b) (auxNormal_summable hη hw γ b))
  simp only [Complex.ofReal_re, Complex.re_sum] at h
  simp_rw [complexLp_auxNormal α γ η w hη hw b,
    complexLp_auxPoint α η w hη hw b] at h
  exact h

theorem auxiliary_total_pairing {m ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (η w : ℕ → Fin m → ℝ) (hη : SquareSummable α η) (hw : SquareSummable α w) :
    (∑ b : Fin 2, ∑' k, timeWeight α k *
      blockSupply c b (auxPoint η w b) (auxNormal γ η w b) k) =
        ∑ a : Fin m, timeSupply c α γ (stateCoordinates α η w hη hw a) := by
  simp_rw [auxiliary_block_pairing c α γ η w hη hw]
  rw [Finset.sum_comm]
  rfl

/-- Scalar-coordinate residual norms sum to the genuine weighted real residual energy. -/
theorem auxiliary_residual_energy {m : ℕ} (α : ℝ) (w : ℕ → Fin m → ℝ)
    (hw : SquareSummable α w) :
    (∑ a : Fin m, ‖difference α (complexLp α w hw a)‖ ^ 2) =
      ∑' k, timeWeight α k * coordinateSquare (auxResidual w k) := by
  have h := complexLp_coordinate_energy α (w - zeroDelay w 1) (hw.sub (hw.zeroDelay 1))
  simp_rw [complexLp_difference α w hw] at h
  exact h

/-- The exact auxiliary zero-extension obeys the nonpositive frequency-domain
supply estimate. This has no initialization or convexity hypotheses. -/
theorem auxiliary_supply_nonpositive {m ℓ : ℕ} (c : LagWeights ℓ)
    {α γ c₀ : ℝ} (hα1 : α ≤ 1) (hc₀ : 0 ≤ c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (η w : ℕ → Fin m → ℝ) (hη : SquareSummable α η) (hw : SquareSummable α w) :
    (∑ b : Fin 2, ∑' k, timeWeight α k *
      blockSupply c b (auxPoint η w b) (auxNormal γ η w b) k) +
        c.epsilon * (∑' k, timeWeight α k * coordinateSquare (auxResidual w k)) ≤ 0 := by
  have hd (a : Fin m) : timeSupply c α γ (stateCoordinates α η w hη hw a) +
      c.epsilon * ‖difference α (complexLp α w hw a)‖ ^ 2 ≤ 0 := by
    have h := supply_dissipation c α γ c₀ hQ (stateCoordinates α η w hη hw a)
    have hE : 0 ≤ stateEnergy α (stateCoordinates α η w hη hw a) := by
      dsimp only [stateEnergy]
      exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_nonneg (sub_nonneg.mpr hα1) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hp := mul_nonneg hc₀ hE
    simp only [stateCoordinates, one_ne_zero, ite_false] at h
    linarith
  have hsum := Finset.sum_nonpos (fun a (_ : a ∈ Finset.univ) ↦ hd a)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, auxiliary_residual_energy] at hsum
  rw [auxiliary_total_pairing]
  exact hsum

end

end ADMM.UnitCircle.Initialized

/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.UniformBound

@[expose] public section

open ADMM.ConvergenceProof Filter
open scoped BigOperators Topology

namespace ADMM.UnitCircle.Initialized

open Supply

/-- Discounted state membership gives discounted actual residual membership,
with the arbitrary initial multiplier retained as a finite correction. -/
theorem weighted_actualResidual_summable {m : ℕ} {α : ℝ} (w : ℕ → Fin m → ℝ)
    (hw : SquareSummable α (fun k ↦ w (k + 1))) : SquareSummable α (actualResidual w) :=
  (auxResidual_summable hw).of_eq_after_zero
    (fun k hk ↦ (auxResidual_eq_actual_after_zero w k (by omega)).symm)

/-- The complete initialized frequency-domain argument removes the discount
without assuming summability of the actual undiscounted trajectory.
The discounted state membership is supplied by the causal homotopy theorem. -/
theorem residual_summable_of_discounted_state {m ℓ : ℕ} (c : LagWeights ℓ)
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (hbalance : BalancedMoments c) (hcircle : HasCoercivityBound c γ κ)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b) (actualNormal γ η w b k) (actualPoint η w b k))
    (hstate : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      SquareSummable α (fun k ↦ η (k + 1)) ∧
      SquareSummable α (fun k ↦ w (k + 1))) :
    Summable (fun k ↦ coordinateSquare (w (k + 1) - w k)) := by
  obtain ⟨c₀, δ, hc₀, hδ, hQ⟩ :=
    supplySymbol_discounted_coercivity c hγ hκ hbalance hcircle
  have hα0 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 0 < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 0 < α from lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  have hα1 : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), α < 1 := self_mem_nhdsWithin
  have hclose : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ), 1 - δ < α :=
    (show ∀ᶠ α : ℝ in 𝓝 (1 : ℝ), 1 - δ < α from lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith)).filter_mono
      nhdsWithin_le_nhds
  have hcorr := (eventually_discountCorrection_small c).filter_mono
    (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
  have hbound : ∀ᶠ α : ℝ in 𝓝[<] (1 : ℝ),
      Summable (fun k ↦ α ^ (2 * k) * (c.epsilon * coordinateSquare (actualResidual w k))) ∧
        (∑' k, α ^ (2 * k) * (c.epsilon * coordinateSquare (actualResidual w k))) ≤
          initializationError c γ η w := by
    filter_upwards [hstate, hα0, hα1, hclose, hcorr] with α hs ha0 ha1 hac hco
    have hr := weighted_actualResidual_summable w hs.2
    have ht := initialized_residual_bound c ha0.le ha1.le hc₀.le (hQ α hac ha1)
      η w φ hzero hgraph hs.1 hs.2 hco
    constructor
    · apply (hr.mul_left c.epsilon).congr
      intro k
      dsimp only [timeWeight]
      ring
    · calc
        _ = c.epsilon * (∑' k, timeWeight α k * coordinateSquare (actualResidual w k)) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro k
          dsimp only [timeWeight]
          ring
        _ ≤ _ := ht
  have hr := (remove_time_discount
    (fun k ↦ mul_nonneg c.epsilon_pos.le (coordinateSquare_nonneg (actualResidual w k))) hbound).1
  have hscaled := hr.mul_left c.epsilon⁻¹
  simpa only [actualResidual, ← mul_assoc, inv_mul_cancel₀ c.epsilon_pos.ne', one_mul] using hscaled

end ADMM.UnitCircle.Initialized

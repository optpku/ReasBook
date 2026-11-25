/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.InitialData
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.AuxiliaryBound

@[expose] public section

open ADMM.ConvergenceProof
open scoped BigOperators ComplexOrder

namespace ADMM.UnitCircle.Initialized

open Supply Fourier

noncomputable section

theorem summable_totalSupply {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (x g : Fin 2 → ℕ → Fin m → ℝ)
    (hx : ∀ b, SquareSummable α (x b)) (hg : ∀ b, SquareSummable α (g b)) :
    Summable (fun k ↦ timeWeight α k * (∑ b : Fin 2, blockSupply c b (x b) (g b) k)) := by
  apply (summable_sum (s := Finset.univ) (fun b _ ↦
    summable_weighted_blockSupply c b (hx b) (hg b))).congr
  intro k
  simp only [Finset.mul_sum]

theorem tsum_totalSupply {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (x g : Fin 2 → ℕ → Fin m → ℝ)
    (hx : ∀ b, SquareSummable α (x b)) (hg : ∀ b, SquareSummable α (g b)) :
    (∑' k, timeWeight α k * (∑ b : Fin 2, blockSupply c b (x b) (g b) k)) =
      ∑ b : Fin 2, ∑' k, timeWeight α k * blockSupply c b (x b) (g b) k := by
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun b _ ↦ summable_weighted_blockSupply c b (hx b) (hg b))

/-- The initialized uniform residual estimate in Appendix C.1. Its constant
is a fixed finite prefix correction and has no dependence on the discount. -/
theorem initialized_residual_bound {m ℓ : ℕ} (c : LagWeights ℓ)
    {α γ c₀ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hc₀ : 0 ≤ c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (η w : ℕ → Fin m → ℝ) (φ : Fin 2 → (Fin m → ℝ) → EReal)
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (φ b) (actualNormal γ η w b k) (actualPoint η w b k))
    (hη : SquareSummable α (fun k ↦ η (k + 1)))
    (hw : SquareSummable α (fun k ↦ w (k + 1)))
    (hcorrection : ∀ b, |discountCorrection c b α| ≤ c.omega / 2) :
    c.epsilon * (∑' k, timeWeight α k * coordinateSquare (actualResidual w k)) ≤
      initializationError c γ η w := by
  let η' := fun k ↦ η (k + 1)
  let w' := fun k ↦ w (k + 1)
  have hpx (b : Fin 2) : SquareSummable α (actualPoint η w b) :=
    (auxPoint_summable hη hw b).of_eq_after_zero
      (fun k hk ↦ (auxPoint_eq_actual_after_zero η w b k hk).symm)
  have hng (b : Fin 2) : SquareSummable α (actualNormal γ η w b) :=
    (auxNormal_summable hη hw γ b).of_eq_after_zero
      (fun k hk ↦ (auxNormal_eq_actual_after_zero γ η w b k hk).symm)
  have hactual := summable_totalSupply c α (actualPoint η w) (actualNormal γ η w) hpx hng
  have haux := summable_totalSupply c α (auxPoint η' w') (auxNormal γ η' w')
    (auxPoint_summable hη hw) (auxNormal_summable hη hw γ)
  have hresaux := auxResidual_summable hw
  have hres : SquareSummable α (actualResidual w) :=
    hresaux.of_eq_after_zero (fun k hk ↦
      (auxResidual_eq_actual_after_zero w k (by omega)).symm)
  have hactualpos : 0 ≤ ∑' k, timeWeight α k * actualSupply c γ η w k := by
    change 0 ≤ ∑' k, timeWeight α k *
      (∑ b : Fin 2, blockSupply c b (actualPoint η w b) (actualNormal γ η w b) k)
    rw [tsum_totalSupply c α _ _ hpx hng]
    apply Finset.sum_nonneg
    intro b _
    have hb := discounted_convex_supply c b (hzero b) (hgraph b) (hpx b) (hng b) (hcorrection b)
    exact hb.1.trans hb.2
  have hauxbound : (∑' k, timeWeight α k * auxSupply c γ η w k) +
      c.epsilon * (∑' k, timeWeight α k * coordinateSquare (auxResidual w' k)) ≤ 0 := by
    change (∑' k, timeWeight α k * (∑ b : Fin 2,
      blockSupply c b (auxPoint η' w' b) (auxNormal γ η' w' b) k)) + _ ≤ 0
    rw [tsum_totalSupply c α _ _ (auxPoint_summable hη hw) (auxNormal_summable hη hw γ)]
    exact auxiliary_supply_nonpositive c hα1 hc₀ hQ η' w' hη hw
  exact residual_bound_of_prefix_corrections hα0 hα1 hactual haux hres hresaux
    c.epsilon_pos.le hactualpos hauxbound (ℓ + 1)
    (auxSupply_eq_actual_after_prefix c γ η w)
    (fun k hk ↦ congrArg coordinateSquare (auxResidual_eq_actual_after_zero w k hk))

end

end ADMM.UnitCircle.Initialized

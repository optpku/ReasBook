/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.ResidualSummability

@[expose] public section

open ADMM.ConvergenceProof
open scoped BigOperators ComplexOrder

namespace ADMM.UnitCircle.Initialized

open Supply Fourier

noncomputable section

theorem actualPoint_squareSummable {m : ℕ} {α : ℝ} (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α (fun k ↦ η (k + 1)))
    (hw : SquareSummable α (fun k ↦ w (k + 1))) (b : Fin 2) :
    SquareSummable α (actualPoint η w b) :=
  (auxPoint_summable hη hw b).of_eq_after_zero
    (fun k hk ↦ (auxPoint_eq_actual_after_zero η w b k hk).symm)

theorem actualNormal_squareSummable {m : ℕ} {α : ℝ} (γ : ℝ) (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α (fun k ↦ η (k + 1)))
    (hw : SquareSummable α (fun k ↦ w (k + 1))) (b : Fin 2) :
    SquareSummable α (actualNormal γ η w b) :=
  (auxNormal_summable hη hw γ b).of_eq_after_zero
    (fun k hk ↦ (auxNormal_eq_actual_after_zero γ η w b k hk).symm)

/-- The full actual supply, rather than just its nonnegative part, survives
initialization with the same fixed finite error constant. -/
theorem initialized_supply_residual_bound {m ℓ : ℕ} (c : LagWeights ℓ)
    {α γ c₀ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hc₀ : 0 ≤ c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (η w : ℕ → Fin m → ℝ)
    (hη : SquareSummable α (fun k ↦ η (k + 1)))
    (hw : SquareSummable α (fun k ↦ w (k + 1))) :
    (∑' k, timeWeight α k * actualSupply c γ η w k) +
      c.epsilon * (∑' k, timeWeight α k * coordinateSquare (actualResidual w k)) ≤
        initializationError c γ η w := by
  let η' := fun k ↦ η (k + 1)
  let w' := fun k ↦ w (k + 1)
  have hs := summable_totalSupply c α (actualPoint η w) (actualNormal γ η w)
    (actualPoint_squareSummable η w hη hw) (actualNormal_squareSummable γ η w hη hw)
  have hbs := summable_totalSupply c α (auxPoint η' w') (auxNormal γ η' w')
    (auxPoint_summable hη hw) (auxNormal_summable hη hw γ)
  have hr := weighted_actualResidual_summable w hw
  have hbr := auxResidual_summable hw
  have haux : (∑' k, timeWeight α k * auxSupply c γ η w k) +
      c.epsilon * (∑' k, timeWeight α k * coordinateSquare (auxResidual w' k)) ≤ 0 := by
    change (∑' k, timeWeight α k * (∑ b : Fin 2,
      blockSupply c b (auxPoint η' w' b) (auxNormal γ η' w' b) k)) + _ ≤ 0
    rw [tsum_totalSupply c α _ _ (auxPoint_summable hη hw) (auxNormal_summable hη hw γ)]
    exact auxiliary_supply_nonpositive c hα1 hc₀ hQ η' w' hη hw
  have hS := weighted_totals_prefix_error_le hbs hs hα0 hα1 (ℓ + 1)
    (auxSupply_eq_actual_after_prefix c γ η w)
  have hR := weighted_totals_prefix_error_le hbr hr hα0 hα1 1
    (fun k hk ↦ congrArg coordinateSquare (auxResidual_eq_actual_after_zero w k hk))
  simp only [Finset.sum_range_one] at hR
  have hR' := mul_le_mul_of_nonneg_left (abs_le.mp hR).1 c.epsilon_pos.le
  have hS' := (abs_le.mp hS).1
  change _ ≤ (∑ k ∈ Finset.range (ℓ + 1), |auxSupply c γ η w k - actualSupply c γ η w k|) +
    c.epsilon * |coordinateSquare (auxResidual w' 0) - coordinateSquare (actualResidual w 0)|
  dsimp only [auxSupply, actualSupply, timeWeight, η', w'] at haux hS' hR' ⊢
  linarith

/-- The two nonnegative origin pairings relative to the chosen normalization. -/
def originMerit {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ) (b : Fin 2) (k : ℕ) : ℝ :=
  dotProduct (actualNormal γ η w b k) (actualPoint η w b k)

def totalMerit {m : ℕ} (γ : ℝ) (η w : ℕ → Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ b : Fin 2, originMerit γ η w b k

/-- The stronger discounted estimate retains the origin merits of the exact
initially chosen KKT normalization, as in the manuscript's proof. -/
theorem initialized_merit_bound {m ℓ : ℕ} (c : LagWeights ℓ)
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
    c.epsilon * (∑' k, timeWeight α k * coordinateSquare (actualResidual w k)) +
      (c.omega / 2) * (∑' k, timeWeight α k * totalMerit γ η w k) ≤
        initializationError c γ η w := by
  have hx := actualPoint_squareSummable η w hη hw
  have hg := actualNormal_squareSummable γ η w hη hw
  have hm (b : Fin 2) := summable_weighted_dot (hg b) (hx b)
  have hM : (∑' k, timeWeight α k * totalMerit γ η w k) =
      ∑ b : Fin 2, ∑' k, timeWeight α k * originMerit γ η w b k := by
    simp only [totalMerit, Finset.mul_sum]
    exact Summable.tsum_finsetSum (fun b _ ↦ hm b)
  have hS : (c.omega / 2) * (∑' k, timeWeight α k * totalMerit γ η w k) ≤
      ∑' k, timeWeight α k * actualSupply c γ η w k := by
    rw [hM, Finset.mul_sum]
    change _ ≤ ∑' k, timeWeight α k * (∑ b : Fin 2,
      blockSupply c b (actualPoint η w b) (actualNormal γ η w b) k)
    rw [tsum_totalSupply c α _ _ hx hg]
    exact Finset.sum_le_sum (fun b _ ↦
      (discounted_convex_supply c b (hzero b) (hgraph b) (hx b) (hg b) (hcorrection b)).2)
  have hb := initialized_supply_residual_bound c hα0 hα1 hc₀ hQ η w hη hw
  linarith

end

end ADMM.UnitCircle.Initialized

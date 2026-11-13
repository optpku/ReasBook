/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.PureSeparation
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.HomotopySupply
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.OrbitIdentification

@[expose] public section

open scoped ENNReal ComplexOrder

namespace ADMM.UnitCircle.Causal

/-- The supply depends on the actual sequences, independently of their
membership proofs. -/
theorem pairedSupply_congr_input {m ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (v w y : ℕ → BlockVector m) (hv : Memℓp v 2) (hw : Memℓp w 2) (hy : Memℓp y 2)
    (h : v = w) : pairedSupply c α v y hv hy = pairedSupply c α w y hw hy := by
  subst w
  rfl

set_option maxHeartbeats 2000000 in
/-- Combining the actual disturbance pairing with strict feedback separation
gives the a priori input estimate, with a constant independent of homotopy. -/
theorem feedback_apriori_norm_bound {m ℓ : ℕ} (c : LagWeights ℓ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (γ : ℝ)
    (e : lp (fun _ : ℕ ↦ BlockVector m) 2) (y : ℕ → BlockVector m) (hy : Memℓp y 2)
    {δ : ℝ} (hδ : 0 < δ)
    (hnonneg : 0 ≤ pairedSupply c α ((e : ℕ → BlockVector m) + feedbackOperator α γ y) y
      ((lp.memℓp e).add (feedbackOperator_memℓp hα0 hα1 γ y hy)) hy)
    (hsep : pairedSupply c α (feedbackOperator α γ y) y
      (feedbackOperator_memℓp hα0 hα1 γ y hy) hy ≤ -δ * coordinateEnergy y hy) :
    ‖e + (⟨feedbackOperator α γ y, feedbackOperator_memℓp hα0 hα1 γ y hy⟩ :
      lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤
      (1 + 2 * (1 + α + 4 * |γ| * (α / (1 - α))) *
        (Fourier.lagUniformBound c α / δ)) * ‖e‖ := by
  let L := 1 + α + 4 * |γ| * (α / (1 - α))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ Fourier.lagUniformBound c α / δ :=
    div_nonneg (Fourier.lagUniformBound_pos c α).le hδ.le
  have hout := output_energy_bound_of_supply c α (feedbackOperator α γ y) (e : ℕ → BlockVector m) y
    (feedbackOperator_memℓp hα0 hα1 γ y hy) (lp.memℓp e) hy hδ hnonneg hsep
  have hybound : ‖(⟨y, hy⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤
      (Fourier.lagUniformBound c α / δ) * (2 * ‖e‖) := by
    exact (coordinateEnergy_sqrt_bounds y hy).1.trans (hout.trans
      (mul_le_mul_of_nonneg_left (coordinateEnergy_sqrt_bounds (e : ℕ → BlockVector m) (lp.memℓp e)).2 hB))
  calc
    _ ≤ ‖e‖ + ‖(⟨feedbackOperator α γ y, feedbackOperator_memℓp hα0 hα1 γ y hy⟩ :
        lp (fun _ : ℕ ↦ BlockVector m) 2)‖ := norm_add_le _ _
    _ ≤ ‖e‖ + L * ‖(⟨y, hy⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ :=
      add_le_add le_rfl (feedbackOperator_norm_le hα0 hα1 γ y hy)
    _ ≤ ‖e‖ + L * ((Fourier.lagUniformBound c α / δ) * (2 * ‖e‖)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hybound hL)
    _ = _ := by dsimp [L]; ring

/-- A single explicit constant controls every square-summable homotopy
solution of the actual discounted reduced ADMM feedback. -/
theorem discountedInput_apriori {m ℓ : ℕ} (c : LagWeights ℓ)
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0)
    {α γ c₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hc₀ : 0 < c₀)
    (hQ : ∀ z : ℂ, ‖z‖ = 1 →
      (supplySymbol c α γ z -
        ((c₀ * (Complex.normSq (delaySymbol α z) + 1 - α) : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef)
    (hcorrection : ∀ b, |Supply.discountCorrection c b α| ≤ c.omega / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ∀ e : lp (fun _ : ℕ ↦ BlockVector m) 2,
      ∀ hv : Memℓp (discountedInput hφ α γ τ e) 2,
        ‖(⟨discountedInput hφ α γ τ e, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤ C * ‖e‖ := by
  let δ := c₀ * (1 - α) / 6
  have hδ : 0 < δ := div_pos (mul_pos hc₀ (sub_pos.mpr hα1)) (by norm_num)
  let C := 1 + 2 * (1 + α + 4 * |γ| * (α / (1 - α))) * (Fourier.lagUniformBound c α / δ)
  have hBpos := Fourier.lagUniformBound_pos c α
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro τ hτ e hv
  let v := discountedInput hφ α γ τ (e : ℕ → BlockVector m)
  let y := τ • discountedProx hφ α v
  have hy : Memℓp y 2 := (discountedProx_memℓp hφ hzero hα0 v hv).const_smul τ
  have hfeedback : v = (e : ℕ → BlockVector m) + feedbackOperator α γ y := by
    funext k
    have h := homotopyInput_equation (fun j b ↦ discountedProxBlock (hφ b) α j) α γ τ e k
    change v k = e k + τ • feedbackOperator α γ (discountedProx hφ α v) k at h
    have hsmul : feedbackOperator α γ y k =
        τ • feedbackOperator α γ (discountedProx hφ α v) k :=
      congrFun (feedbackOperator_smul α γ τ (discountedProx hφ α v)) k
    change v k = e k + feedbackOperator α γ y k
    rw [hsmul]
    exact h
  have hsign := homotopy_pairedSupply_nonneg c hφ hzero hα0 τ hτ.1 hτ.2 v hv hcorrection
  have hsign' : 0 ≤ pairedSupply c α ((e : ℕ → BlockVector m) + feedbackOperator α γ y) y
      ((lp.memℓp e).add (feedbackOperator_memℓp hα0.le hα1 γ y hy)) hy := by
    rw [← pairedSupply_congr_input c α v _ y hv _ hy hfeedback]
    exact hsign
  have hsep := pureSupply_separation c hα0.le hα1 hc₀ hQ y hy
  have hn := feedback_apriori_norm_bound c hα0.le hα1 γ e y hy hδ hsign' hsep
  have heq : (⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2) =
      e + (⟨feedbackOperator α γ y, feedbackOperator_memℓp hα0.le hα1 γ y hy⟩ :
        lp (fun _ : ℕ ↦ BlockVector m) 2) := by
    apply lp.ext
    funext k
    exact congrFun hfeedback k
  rw [heq]
  exact hn

end ADMM.UnitCircle.Causal

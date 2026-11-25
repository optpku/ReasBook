/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.LagOperator
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.SupplyAlgebra

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

set_option maxHeartbeats 2000000

/-- Every frequency-domain product used below is integrable by L² Cauchy--Schwarz. -/
theorem transformed_pair_integrable (x y : TimeSequence) :
    Integrable (fun t ↦ conj (transform x t) * transform y t) AddCircle.haarAddCircle := by
  simpa only [RCLike.inner_apply'] using L2.integrable_inner (𝕜 := ℂ) (transform x) (transform y)

theorem transformed_pair_integral (x y : TimeSequence) :
    inner ℂ x y = ∫ t : AddCircle (1 : ℝ),
      conj (transform x t) * transform y t ∂AddCircle.haarAddCircle := by
  rw [lp.inner_eq_tsum]
  simpa only [RCLike.inner_apply'] using transform_inner x y

theorem transformed_normSq_integrable (x : TimeSequence) :
    Integrable (fun t ↦ Complex.normSq (transform x t)) AddCircle.haarAddCircle := by
  have h := (transformed_pair_integrable x x).re
  simpa [Complex.mul_re, Complex.normSq_apply] using h

theorem transformed_normSq_integral (x : TimeSequence) :
    (∫ t : AddCircle (1 : ℝ), Complex.normSq (transform x t)
      ∂AddCircle.haarAddCircle) = ‖x‖ ^ 2 := by
  have h := congrArg Complex.re (transformed_pair_integral x x)
  change RCLike.re (inner ℂ x x) = RCLike.re (∫ t : AddCircle (1 : ℝ),
    conj (transform x t) * transform x t ∂AddCircle.haarAddCircle) at h
  rw [← integral_re (transformed_pair_integrable x x),
    ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  simpa [Complex.mul_re, Complex.normSq_apply] using h.symm

/-- The frequency-domain integrand of one actual lag pairing. -/
def blockIntegrand {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) (b : Fin 2) (t : AddCircle (1 : ℝ)) : ℂ :=
  conj (normalRow α γ (circlePoint t) b ⬝ᵥ frequencyState s t) *
    lagMultiplier c α (circlePoint t) b *
      (pointRow α (circlePoint t) b ⬝ᵥ frequencyState s t)

theorem blockIntegrand_ae {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) (b : Fin 2) :
    (fun t ↦ conj (transform (normalSignal α γ s b) t) *
      transform (lagOperator c α b (pointSignal α s b)) t) =ᵐ[AddCircle.haarAddCircle]
        blockIntegrand c α γ s b := by
  filter_upwards [transform_normalSignal_ae α γ s b,
    transform_lagOperator_ae c α b (pointSignal α s b),
    transform_pointSignal_ae α s b] with t hn hl hp
  rw [hn, hl, hp]
  dsimp [blockIntegrand]
  ring

theorem blockIntegrand_integrable {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) (b : Fin 2) :
    Integrable (blockIntegrand c α γ s b) AddCircle.haarAddCircle :=
  (transformed_pair_integrable (normalSignal α γ s b)
    (lagOperator c α b (pointSignal α s b))).congr (blockIntegrand_ae c α γ s b)

theorem block_pairing_parseval {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) (b : Fin 2) :
    (inner ℂ (normalSignal α γ s b) (lagOperator c α b (pointSignal α s b))).re =
      ∫ t : AddCircle (1 : ℝ), (blockIntegrand c α γ s b t).re
        ∂AddCircle.haarAddCircle := by
  rw [transformed_pair_integral]
  rw [integral_congr_ae (blockIntegrand_ae c α γ s b)]
  exact (integral_re (blockIntegrand_integrable c α γ s b)).symm

/-- The residual frequency integrand is an actual transformed difference. -/
theorem residual_integrand_ae (α : ℝ) (x : TimeSequence) :
    (fun t ↦ Complex.normSq (transform (difference α x) t)) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ Complex.normSq (delaySymbol α (circlePoint t) * transform x t)) := by
  filter_upwards [transform_difference_ae α x] with t ht
  rw [ht]

theorem residual_integrand_integrable (α : ℝ) (x : TimeSequence) :
    Integrable (fun t ↦ Complex.normSq (delaySymbol α (circlePoint t) * transform x t))
      AddCircle.haarAddCircle :=
  (transformed_normSq_integrable (difference α x)).congr (residual_integrand_ae α x)

theorem residual_integrand_integral (α : ℝ) (x : TimeSequence) :
    (∫ t : AddCircle (1 : ℝ),
      Complex.normSq (delaySymbol α (circlePoint t) * transform x t)
        ∂AddCircle.haarAddCircle) = ‖difference α x‖ ^ 2 := by
  rw [← integral_congr_ae (residual_integrand_ae α x), transformed_normSq_integral]

/-- The real total supply, without its residual correction, in bilateral L² coordinates. -/
def timeSupply {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ) (s : Fin 2 → TimeSequence) : ℝ :=
  ∑ b : Fin 2,
    (inner ℂ (normalSignal α γ s b) (lagOperator c α b (pointSignal α s b))).re

theorem supply_quadratic_integrable {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) :
    Integrable (fun t ↦ quadratic (supplySymbol c α γ (circlePoint t))
      (frequencyState s t)) AddCircle.haarAddCircle := by
  have hsum := integrable_finsetSum Finset.univ
    (fun b _ ↦ (blockIntegrand_integrable c α γ s b).re)
  have hr := (residual_integrand_integrable α (s 1)).const_mul c.epsilon
  apply (hsum.neg.sub hr).congr
  exact Filter.Eventually.of_forall fun t ↦ by
    simp only [Pi.sub_apply, Pi.neg_apply, RCLike.re_to_complex, supplySymbol_quadratic, blockIntegrand, frequencyState]

/-- Exact discounted Parseval identity for the manuscript's actual supply symbol.
Both directions of every lag and the residual-square correction are retained. -/
theorem supply_pairing_parseval {ℓ : ℕ} (c : LagWeights ℓ) (α γ : ℝ)
    (s : Fin 2 → TimeSequence) :
    timeSupply c α γ s =
      -(∫ t : AddCircle (1 : ℝ),
        quadratic (supplySymbol c α γ (circlePoint t)) (frequencyState s t)
          ∂AddCircle.haarAddCircle) - c.epsilon * ‖difference α (s 1)‖ ^ 2 := by
  have hi : (∫ t : AddCircle (1 : ℝ),
      quadratic (supplySymbol c α γ (circlePoint t)) (frequencyState s t)
        ∂AddCircle.haarAddCircle) =
      -timeSupply c α γ s - c.epsilon * ‖difference α (s 1)‖ ^ 2 := by
    simp only [supplySymbol_quadratic]
    rw [integral_sub, integral_neg, integral_finsetSum]
    · simp only [integral_const_mul, frequencyState, residual_integrand_integral]
      change -(∑ b : Fin 2, ∫ t : AddCircle (1 : ℝ), (blockIntegrand c α γ s b t).re
        ∂AddCircle.haarAddCircle) - c.epsilon * ‖difference α (s 1)‖ ^ 2 = _
      simp_rw [← block_pairing_parseval]
      rfl
    · exact fun b _ ↦ (blockIntegrand_integrable c α γ s b).re
    · exact (integrable_finsetSum Finset.univ
        (fun b _ ↦ (blockIntegrand_integrable c α γ s b).re)).neg
    · exact (residual_integrand_integrable α (s 1)).const_mul c.epsilon
  linarith

end

end ADMM.UnitCircle.Fourier

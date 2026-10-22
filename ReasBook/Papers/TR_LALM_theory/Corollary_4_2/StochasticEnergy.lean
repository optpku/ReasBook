/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.EnergyGeometry
public import TR_LALM_theory.Corollary_4_2.StochasticMoments

public section

open MeasureTheory
open scoped InnerProductSpace LALM

namespace LALM.Correction

variable {n m : ℕ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}

/-- Helper for Corollary 4.2: explicit-gradient model optimality gives the
exact change of the linearized augmented-Lagrangian core. -/
lemma linearizedAugmentedLagrangianChange_eq_of_minimizesStepModelWithGradient
    (g : EuclideanSpace ℝ (Fin n)) (rho beta : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (lambda : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n))
    (hp : IsMinOn (LALM.stepModelWithGradient c g rho beta x lambda) Set.univ p) :
    ⟪g, p⟫_ℝ + ⟪lambda, fderiv ℝ c x p⟫_ℝ +
        (rho / 2) * (‖c x + fderiv ℝ c x p‖ ^ 2 - ‖c x‖ ^ 2) =
      -beta * ‖p‖ ^ 2 - (rho / 2) * ‖fderiv ℝ c x p‖ ^ 2 := by
  -- Pair the explicit-gradient stationarity equation with the minimizing step.
  have hfirstOrder := stepModelWithGradientOptimality g rho beta x lambda p hp
  have hoptimal := congrArg (fun v ↦ ⟪v, p⟫_ℝ) hfirstOrder
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
    ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    inner_zero_left] at hoptimal
  rw [norm_add_sq_real]
  nlinarith

end LALM.Correction

namespace LALM.Correction.StochasticRun

universe u v

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

/-- Helper for Corollary 4.2: the corrected stochastic Lyapunov rank couples
the augmented Lagrangian to the preceding base-step square. -/
noncomputable def lyapunov
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) : ℝ :=
  ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) +
    (multiplierPrimalConstant h params.delta params.beta params.rho
      params.multiplierBound / params.rho) * ‖run.baseStep (k - 1) ω‖ ^ 2

/-- Helper for Corollary 4.2: the corrected stochastic Lyapunov rank exposes
its augmented-Lagrangian and preceding-base-step terms. -/
theorem lyapunov_def
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    run.lyapunov k ω =
      ℒ[f, c; params.rho](run.point k ω, run.multiplier k ω) +
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            ‖run.baseStep (k - 1) ω‖ ^ 2 := by
  -- Expose the two stable components without unfolding the corrected run.
  rfl

/-- Helper for Corollary 4.2: the true gradient is the estimated gradient
minus the corrected run's gradient error. -/
theorem gradient_eq_gradientEstimate_sub_gradientError
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (ω : Ω) :
    gradient f (run.point k ω) =
      run.gradientEstimate k ω - run.gradientError k ω := by
  -- Rearrange the defining estimator-error subtraction once for energy proofs.
  rw [run.gradientError_apply]
  module

/-- Helper for Corollary 4.2: explicit fixed-path admissibility and norm bounds
give one-step fixed-multiplier augmented-Lagrangian descent. -/
theorem augmentedLagrangianDescent_of_bounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω)
    (hadm : IsAdmissible h (run.point k omega) (run.baseStep k omega))
    (hstep : ‖run.baseStep k omega‖ ≤ params.delta)
    (hMultiplier : ∀ j ≤ k,
      ‖run.multiplier j omega‖ ≤ params.multiplierBound) :
    ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier k omega) ≤
      ℒ[f, c; params.rho](run.point k omega, run.multiplier k omega) -
        (params.beta / 2) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
  -- The supplied path bounds instantiate the run-independent transition geometry.
  have heffective := run.normEffectiveMultiplier_le k omega hMultiplier
  have hchange := augmentedLagrangianChangeAlongCorrectedStep_le h params
    (run.point k omega) (run.multiplier k omega) (run.baseStep k omega)
    hadm hstep heffective
  rw [← run.point_succ k omega] at hchange
  -- Rewrite estimated-gradient model optimality into the same linearized core.
  have hminimizes :
      IsMinOn (LALM.stepModelWithGradient c (run.gradientEstimate k omega)
        params.rho params.beta (run.point k omega) (run.multiplier k omega))
          Set.univ (run.baseStep k omega) := by
    simpa only [run.gradientEstimate_apply] using run.minimizes_baseStep k omega
  have hlinearized :=
    linearizedAugmentedLagrangianChange_eq_of_minimizesStepModelWithGradient
      (run.gradientEstimate k omega) params.rho params.beta
      (run.point k omega) (run.multiplier k omega) (run.baseStep k omega) hminimizes
  -- One Young estimate absorbs the sole stochastic gradient-error pairing.
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hquarterBeta : 0 < (params.beta : ℝ) / 4 := by positivity
  have hinverseQuarterBeta : ((params.beta : ℝ) / 4)⁻¹ = 4 / params.beta := by
    field_simp [hbeta.ne']
  have htwoProduct := two_mul_le_add_mul_sq
    (a := ‖run.baseStep k omega‖) (b := ‖run.gradientError k omega‖)
      hquarterBeta
  rw [hinverseQuarterBeta] at htwoProduct
  have hyoung :
      ‖run.baseStep k omega‖ * ‖run.gradientError k omega‖ ≤
        (params.beta / 8) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
    have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      ‖run.baseStep k omega‖ * ‖run.gradientError k omega‖ =
          (2 * ‖run.baseStep k omega‖ * ‖run.gradientError k omega‖) / 2 := by
        ring
      _ ≤ ((params.beta / 4) * ‖run.baseStep k omega‖ ^ 2 +
          (4 / params.beta) * ‖run.gradientError k omega‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right htwoProduct htwoNonneg
      _ = (params.beta / 8) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by ring
  have hinnerNorm := real_inner_le_norm
    (-run.gradientError k omega) (run.baseStep k omega)
  simp only [inner_neg_left, norm_neg] at hinnerNorm
  have hinner :
      -⟪run.gradientError k omega, run.baseStep k omega⟫_ℝ ≤
        (params.beta / 8) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
    have hyoungCommuted := by simpa only [mul_comm] using hyoung
    exact hinnerNorm.trans hyoungCommuted
  have hmodelTerm :
      modelConstant h params.delta params.rho params.multiplierBound *
          ‖run.baseStep k omega‖ ^ 2 ≤
        (3 * (params.beta : ℝ) / 8) * ‖run.baseStep k omega‖ ^ 2 :=
    mul_le_mul_of_nonneg_right params.modelConstant_le (sq_nonneg _)
  have hpenaltyNonneg :
      (0 : ℝ) ≤ (params.rho / 2) *
        ‖fderiv ℝ c (run.point k omega) (run.baseStep k omega)‖ ^ 2 := by
    positivity
  rw [run.gradient_eq_gradientEstimate_sub_gradientError k omega,
    inner_sub_left] at hchange
  have hchangeFinal :
      ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier k omega) -
          ℒ[f, c; params.rho](run.point k omega, run.multiplier k omega) ≤
        -(params.beta / 2) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
    nlinarith
  -- Move the previous augmented-Lagrangian value to the right-hand side.
  linarith

/-- Helper for Corollary 4.2: global prefix admissibility specializes the
fixed-path augmented-Lagrangian descent theorem. -/
theorem augmentedLagrangianDescent
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix N) (hk : k < N)
    (omega : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier k omega) ≤
      ℒ[f, c; params.rho](run.point k omega, run.multiplier k omega) -
        (params.beta / 2) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
  -- Project the active transition and the multiplier prefix at this sample path.
  have hnormBounds := run.admissiblePrefix_normBounds N h_admissible
  exact run.augmentedLagrangianDescent_of_bounds k omega
    ((run.isAdmissiblePrefix_iff N).1 h_admissible k hk omega)
    (hnormBounds.1 k hk omega)
    (fun j hj ↦ hnormBounds.2 j (hj.trans (Nat.le_of_lt hk)) omega)

end LALM.Correction.StochasticRun

end

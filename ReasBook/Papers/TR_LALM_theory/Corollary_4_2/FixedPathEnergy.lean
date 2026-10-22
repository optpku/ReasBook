/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StochasticEnergy
public import TR_LALM_theory.Corollary_4_2.StochasticMultiplier

public section

open MeasureTheory
open scoped BigOperators InnerProductSpace LALM NNReal

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

/-- Helper for Corollary 4.2: the corrected admissibility and norm invariant
for one stochastic sample path through a finite horizon. -/
structure BoundedAdmissiblePath
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (N : ℕ) (omega : Ω) : Prop where
  admissible : ∀ j < N, IsAdmissible h (run.point j omega) (run.baseStep j omega)
  baseStep_le : ∀ j < N, ‖run.baseStep j omega‖ ≤ params.delta
  multiplier_le : ∀ j ≤ N, ‖run.multiplier j omega‖ ≤ params.multiplierBound

namespace BoundedAdmissiblePath

/-- Helper for Corollary 4.2: a bounded admissible path controls each positive
squared multiplier increment by its adjacent steps and estimator errors. -/
lemma norm_multiplier_succ_sub_sq_le
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk : k < N) :
    ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 ≤
      multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound *
        (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
      LALM.multiplierErrorConstant h *
        (‖run.gradientError k omega‖ ^ 2 +
          ‖run.gradientError (k - 1) omega‖ ^ 2) := by
  -- Supply the two adjacent transitions to the fixed-path multiplier API.
  have hkPrevious : k - 1 < N := by omega
  have hkLeN : k ≤ N := by omega
  exact run.norm_multiplier_succ_sub_sq_le_of_bounds k hk_pos omega
    (bounds.admissible k hk) (bounds.admissible (k - 1) hkPrevious)
    (bounds.baseStep_le k hk) (bounds.baseStep_le (k - 1) hkPrevious)
    (bounds.multiplier_le k hkLeN)

/-- Helper for Corollary 4.2: a bounded admissible path gives one-step
fixed-multiplier augmented-Lagrangian descent. -/
lemma augmentedLagrangianDescent
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    {k : ℕ} (hk : k < N) :
    ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier k omega) ≤
      ℒ[f, c; params.rho](run.point k omega, run.multiplier k omega) -
        (params.beta / 2) * ‖run.baseStep k omega‖ ^ 2 +
          (2 / params.beta) * ‖run.gradientError k omega‖ ^ 2 := by
  -- Restrict the bundled multiplier bound to the active prefix.
  have hMultiplier : ∀ j ≤ k,
      ‖run.multiplier j omega‖ ≤ params.multiplierBound := by
    intro j hj
    exact bounds.multiplier_le j (hj.trans (Nat.le_of_lt hk))
  exact run.augmentedLagrangianDescent_of_bounds k omega
    (bounds.admissible k hk) (bounds.baseStep_le k hk) hMultiplier

/-- Helper for Corollary 4.2: a corrected stochastic multiplier update changes
the augmented Lagrangian by the penalty-scaled squared multiplier increment. -/
lemma augmentedLagrangian_multiplier_succ_eq
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (k : ℕ) (omega : Ω) :
    ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier (k + 1) omega) =
      ℒ[f, c; params.rho](run.point (k + 1) omega, run.multiplier k omega) +
        ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 /
          params.rho := by
  -- Substitute the exact multiplier update and cancel the positive penalty.
  have hupdate :
      run.multiplier (k + 1) omega = run.multiplier k omega +
        (params.rho : ℝ) • c (run.point (k + 1) omega) := by
    rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
  rw [augmentedLagrangian_def, augmentedLagrangian_def, hupdate,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos params.spec.1.2.2.1,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
  field_simp [params.spec.1.2.2.1.ne']
  ring

/-- Helper for Corollary 4.2: the corrected parameter inequality absorbs the
multiplier-primal coefficient after division by the penalty. -/
lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  -- Clear the two positive denominators in the stored parameter inequality.
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Corollary 4.2: every positive transition of a bounded
admissible path decreases the corrected Lyapunov rank up to adjacent errors. -/
lemma lyapunovDescent
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    {k : ℕ} (hk_pos : 1 ≤ k) (hk : k < N) :
    run.lyapunov (k + 1) omega ≤
      run.lyapunov k omega -
        (params.beta / 4) * ‖run.baseStep k omega‖ ^ 2 +
      lyapunovErrorConstant h params *
        (‖run.gradientError k omega‖ ^ 2 +
          ‖run.gradientError (k - 1) omega‖ ^ 2) := by
  -- Combine fixed-multiplier descent with the fixed-path multiplier estimate.
  have hlagrangian := bounds.augmentedLagrangianDescent hk
  have hmultiplier := bounds.norm_multiplier_succ_sub_sq_le hk_pos hk
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierDivided :=
    (div_le_div_iff_of_pos_right hrho).2 hmultiplier
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 /
          params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
          (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
        (LALM.multiplierErrorConstant h / params.rho) *
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2) := by
    calc
      ‖run.multiplier (k + 1) omega - run.multiplier k omega‖ ^ 2 /
          params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound *
                (‖run.baseStep k omega‖ ^ 2 +
                  ‖run.baseStep (k - 1) omega‖ ^ 2) +
            LALM.multiplierErrorConstant h *
              (‖run.gradientError k omega‖ ^ 2 +
                ‖run.gradientError (k - 1) omega‖ ^ 2)) / params.rho :=
        hmultiplierDivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
              params.multiplierBound / params.rho) *
            (‖run.baseStep k omega‖ ^ 2 + ‖run.baseStep (k - 1) omega‖ ^ 2) +
          (LALM.multiplierErrorConstant h / params.rho) *
            (‖run.gradientError k omega‖ ^ 2 +
              ‖run.gradientError (k - 1) omega‖ ^ 2) := by ring
  have hcoefficient :=
    multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have htwiceCoefficient :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound / params.rho) ≤ params.beta / 4 := by
    linarith
  have hcurrent :
      2 * (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep k omega‖ ^ 2 ≤
        (params.beta / 4) * ‖run.baseStep k omega‖ ^ 2 :=
    mul_le_mul_of_nonneg_right htwiceCoefficient (sq_nonneg _)
  have hpreviousErrorNonneg :
      (0 : ℝ) ≤ (2 / params.beta) *
        ‖run.gradientError (k - 1) omega‖ ^ 2 := by
    positivity
  -- Expose the two ranks only after both one-step estimates share one normal form.
  rw [run.lyapunov_def, run.lyapunov_def,
    augmentedLagrangian_multiplier_succ_eq run, Nat.add_sub_cancel,
    lyapunovErrorConstant_def]
  nlinarith

/-- Helper for Corollary 4.2: the terminal value of a positive-horizon bounded
admissible path lies above the uniform corrected Lyapunov lower bound. -/
lemma lyapunovLowerBound_le
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    (hN : 1 ≤ N) :
    lyapunovLowerBound h params ≤ run.lyapunov N omega := by
  -- The endpoint belongs to the region through the preceding admissible transition.
  have hPrevious : N - 1 < N := by omega
  have hx := nextPoint_mem_region h (run.point (N - 1) omega)
    (run.baseStep (N - 1) omega) (bounds.admissible (N - 1) hPrevious)
  rw [← run.point_succ (N - 1) omega, Nat.sub_add_cancel hN] at hx
  have hlower := augmentedLagrangian_lowerBound h params.rho
    (run.point N omega) (run.multiplier N omega) params.multiplierBound
    params.spec.1.2.2.1 hx (bounds.multiplier_le N (Nat.le_refl N))
    (NNReal.coe_nonneg params.multiplierBound)
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            ‖run.baseStep (N - 1) omega‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg params.spec.1.2.2.1.le)
      (sq_nonneg _)
  rw [lyapunovLowerBound_def, run.lyapunov_def]
  linarith

/-- Helper for Corollary 4.2: the first corrected Lyapunov value of a bounded
admissible path lies below the corrected initial potential. -/
lemma lyapunovOne_le_initialPotentialBound
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    (hN : 1 ≤ N) :
    run.lyapunov 1 omega ≤ initialPotentialBound h params := by
  have hzeroLt : 0 < N := by omega
  have hadm := bounds.admissible 0 hzeroLt
  have hstep := bounds.baseStep_le 0 hzeroLt
  have hmultiplierZero := bounds.multiplier_le 0 (Nat.zero_le N)
  have hmultiplierOne := bounds.multiplier_le 1 hN
  -- The two corrected legs give exactly the objective allowance in the potential.
  have hobjectiveChange := normObjectiveChangeAlongCorrectedStep_le h params
    (run.point 0 omega) (run.baseStep 0 omega) hadm hstep
  have hsignedObjective :
      f (run.point 1 omega) - f (run.point 0 omega) ≤
        ‖f (run.point 1 omega) - f (run.point 0 omega)‖ := by
    simpa only [Real.norm_eq_abs] using
      le_abs_self (f (run.point 1 omega) - f (run.point 0 omega))
  have hfactorNonneg :
      0 ≤ (h.gradientBound : ℝ) * displacementFactor h params.delta := by
    rw [displacementFactor_def, stepConstant_def]
    positivity
  have hgradientStep :
      h.gradientBound * displacementFactor h params.delta *
          ‖run.baseStep 0 omega‖ ≤
        h.gradientBound * displacementFactor h params.delta * params.delta :=
    mul_le_mul_of_nonneg_left hstep hfactorNonneg
  have hobjective :
      f (run.point 1 omega) ≤
        f x₀ + h.gradientBound * displacementFactor h params.delta *
          params.delta := by
    rw [← run.point_succ 0] at hobjectiveChange
    rw [run.point_zero] at hsignedObjective hobjectiveChange
    linarith
  -- The multiplier update controls the constraint part by the stored dual bound.
  have hresidualIdentity :
      (params.rho : ℝ) • c (run.point 1 omega) =
        run.multiplier 1 omega - run.multiplier 0 omega := by
    have hupdate :
        run.multiplier 1 omega = run.multiplier 0 omega +
          (params.rho : ℝ) • c (run.point 1 omega) := by
      rw [run.multiplier_succ, nextMultiplier_def, ← run.point_succ]
    rw [hupdate]
    module
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hscaledResidual :
      params.rho * ‖c (run.point 1 omega)‖ ≤ 2 * params.multiplierBound := by
    calc
      params.rho * ‖c (run.point 1 omega)‖ =
          ‖(params.rho : ℝ) • c (run.point 1 omega)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
      _ = ‖run.multiplier 1 omega - run.multiplier 0 omega‖ :=
        congrArg norm hresidualIdentity
      _ ≤ ‖run.multiplier 1 omega‖ + ‖run.multiplier 0 omega‖ := norm_sub_le _ _
      _ ≤ 2 * params.multiplierBound := by linarith
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound :=
    NNReal.coe_nonneg params.multiplierBound
  have hinnerBound :
      ⟪run.multiplier 1 omega, c (run.point 1 omega)⟫_ℝ ≤
        params.multiplierBound * ‖c (run.point 1 omega)‖ := by
    calc
      ⟪run.multiplier 1 omega, c (run.point 1 omega)⟫_ℝ ≤
          ‖run.multiplier 1 omega‖ * ‖c (run.point 1 omega)‖ :=
        real_inner_le_norm _ _
      _ ≤ params.multiplierBound * ‖c (run.point 1 omega)‖ :=
        mul_le_mul_of_nonneg_right hmultiplierOne (norm_nonneg _)
  have hinnerRho := mul_le_mul_of_nonneg_left hinnerBound hrho.le
  have hresidualBound := mul_le_mul_of_nonneg_left hscaledResidual hboundNonneg
  have hinnerScaled :
      params.rho * ⟪run.multiplier 1 omega, c (run.point 1 omega)⟫_ℝ ≤
        2 * params.multiplierBound ^ 2 := by
    nlinarith
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hscaledResidualSq :
      (params.rho * ‖c (run.point 1 omega)‖) ^ 2 ≤
        (2 * params.multiplierBound) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hrho.le (norm_nonneg _))
      (mul_nonneg htwoNonneg hboundNonneg)).2 hscaledResidual
  have hconstraintContribution :
      ⟪run.multiplier 1 omega, c (run.point 1 omega)⟫_ℝ +
          params.rho / 2 * ‖c (run.point 1 omega)‖ ^ 2 ≤
        4 * params.multiplierBound ^ 2 / params.rho := by
    apply (le_div_iff₀ hrho).2
    nlinarith
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hstepSq : ‖run.baseStep 0 omega‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstep
  have hcorrection :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.baseStep 0 omega‖ ^ 2 ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * params.delta ^ 2 :=
    mul_le_mul_of_nonneg_left hstepSq (div_nonneg hconstantNonneg hrho.le)
  -- Expose the rank and corrected potential only after all four terms are bounded.
  rw [run.lyapunov_def, augmentedLagrangian_def, initialPotentialBound_def]
  norm_num only [Nat.reduceSub]
  linarith

/-- Helper for Corollary 4.2: every positive-horizon bounded admissible path
has total base-step energy controlled by its initial allowance and error energy. -/
lemma sumBaseStepSq_le
    {run : StochasticRun h oracle P x₀ multiplier₀ params Q B b}
    {N : ℕ} {omega : Ω} (bounds : run.BoundedAdmissiblePath N omega)
    (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, ‖run.baseStep k omega‖ ^ 2 ≤
      initialStepBound h params + errorStepConstant h params *
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
  -- Sum the one-step descent inequality over all positive transition indices.
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N,
          (params.beta / 4) * ‖run.baseStep k omega‖ ^ 2) ≤
        ∑ k ∈ Finset.Ico 1 N,
          ((run.lyapunov k omega - run.lyapunov (k + 1) omega) +
            lyapunovErrorConstant h params *
              (‖run.gradientError k omega‖ ^ 2 +
                ‖run.gradientError (k - 1) omega‖ ^ 2)) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := bounds.lyapunovDescent hkBounds.1 hkBounds.2
    linarith
  have hendpointLeft : 1 + (N - 1) = N := by omega
  have hendpointRight : N - 1 + 1 = N := by omega
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (run.lyapunov k omega - run.lyapunov (k + 1) omega)) =
        run.lyapunov 1 omega - run.lyapunov N omega := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ run.lyapunov (k + 1) omega) (N - 1))
  -- Both adjacent error sums embed in the full prefix error sum.
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError k omega‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k omega‖)
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) omega‖ ^ 2) =
        ∑ j ∈ Finset.range (N - 1), ‖run.gradientError j omega‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (N - 1) ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 N, ‖run.gradientError (k - 1) omega‖ ^ 2) ≤
        ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k _ _ ↦ sq_nonneg ‖run.gradientError k omega‖)
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (‖run.gradientError k omega‖ ^ 2 +
            ‖run.gradientError (k - 1) omega‖ ^ 2)) ≤
        2 * ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  -- Replace the terminal rank by its lower bound and normalize the coefficient.
  have hlower := bounds.lyapunovLowerBound_le hN
  have herrorCoefficientNonneg : 0 ≤ lyapunovErrorConstant h params := by
    rw [lyapunovErrorConstant_def, LALM.multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  have henergy :
      (params.beta / 4) *
          (∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2) ≤
        run.lyapunov 1 omega - lyapunovLowerBound h params +
          2 * lyapunovErrorConstant h params *
            ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    nlinarith
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hscalingNonneg : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  have hsumIco :
      (∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2) ≤
        4 * (run.lyapunov 1 omega - lyapunovLowerBound h params) / params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by
    calc
      (∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2) =
          (4 / params.beta) *
            ((params.beta / 4) *
              ∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2) := by
        field_simp [hbeta.ne']
      _ ≤ (4 / params.beta) *
          (run.lyapunov 1 omega - lyapunovLowerBound h params +
            2 * lyapunovErrorConstant h params *
              ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2) :=
        mul_le_mul_of_nonneg_left henergy hscalingNonneg
      _ = 4 * (run.lyapunov 1 omega - lyapunovLowerBound h params) /
            params.beta +
          (8 * lyapunovErrorConstant h params / params.beta) *
            ∑ k ∈ Finset.range N, ‖run.gradientError k omega‖ ^ 2 := by ring
  have hupper := bounds.lyapunovOne_le_initialPotentialBound hN
  have hgap := sub_le_sub_right hupper (lyapunovLowerBound h params)
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hscalingNonneg
  have hgapScaledNormalized :
      4 * (run.lyapunov 1 omega - lyapunovLowerBound h params) / params.beta ≤
        4 * (initialPotentialBound h params - lyapunovLowerBound h params) /
          params.beta := by
    calc
      4 * (run.lyapunov 1 omega - lyapunovLowerBound h params) / params.beta =
          (4 / params.beta) *
            (run.lyapunov 1 omega - lyapunovLowerBound h params) := by ring
      _ ≤ (4 / params.beta) *
          (initialPotentialBound h params - lyapunovLowerBound h params) :=
        hgapScaled
      _ = 4 * (initialPotentialBound h params - lyapunovLowerBound h params) /
          params.beta := by ring
  -- Restore index zero and absorb its radius bound into the initial allowance.
  have hzeroLt : 0 < N := by omega
  have hstepZero := bounds.baseStep_le 0 hzeroLt
  have hstepZeroSq :
      ‖run.baseStep 0 omega‖ ^ 2 ≤ (params.delta : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (NNReal.coe_nonneg params.delta)).2 hstepZero
  have hdecomposition :
      (∑ k ∈ Finset.range N, ‖run.baseStep k omega‖ ^ 2) =
        ‖run.baseStep 0 omega‖ ^ 2 +
          ∑ k ∈ Finset.Ico 1 N, ‖run.baseStep k omega‖ ^ 2 := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    simp
  rw [hdecomposition, initialStepBound_def, errorStepConstant_def]
  linarith

end BoundedAdmissiblePath

end LALM.Correction.StochasticRun

end

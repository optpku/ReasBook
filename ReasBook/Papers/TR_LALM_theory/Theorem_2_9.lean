/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

import TR_LALM_theory.Lemma_2_7
import TR_LALM_theory.Lemma_2_8
public import TR_LALM_theory.Theorem_2_9.Lyapunov

public section

open scoped InnerProductSpace LALM NNReal

namespace LALM.Run

variable {n m : ℕ}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}

/-- Helper for Theorem 2.9: a multiplier update increases the augmented
Lagrangian by the squared multiplier increment divided by the penalty. -/
private lemma augmentedLagrangian_multiplier_succ_eq
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀) (k : ℕ) :
    ℒ[f, c; params.rho](run.point (k + 1), run.multiplier (k + 1)) =
      ℒ[f, c; params.rho](run.point (k + 1), run.multiplier k) +
        ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho := by
  -- Expand the multiplier-dependent term and replace the update by its residual.
  rw [augmentedLagrangian_def, augmentedLagrangian_def, run.multiplier_succ,
    inner_add_left, inner_smul_left, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos run.rho_pos, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial]
  -- Positivity of the penalty clears the sole denominator in the identity.
  field_simp [run.rho_pos.ne']
  ring

/-- Helper for Theorem 2.9: the admissible parameter inequality bounds the
multiplier-primal coefficient after division by the penalty. -/
private lemma multiplierPrimalConstant_div_rho_le_beta_div_eight
    (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀) :
    multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho ≤
      params.beta / 8 := by
  -- Clear the positive proximal denominator in Assumption 2.3.
  have hscaled :
      8 * multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound ≤ params.rho * params.beta :=
    (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.1).1
      params.multiplierPrimalConstant_le
  -- Clear the positive penalty denominator and normalize the scalar factors.
  apply (div_le_iff₀ params.toAdmissibleParameters.spec.1.2.2.1).2
  nlinarith

/-- Helper for Theorem 2.9: a bounded multiplier gives the standard uniform
lower bound for the augmented Lagrangian on the regularity region. -/
private lemma augmentedLagrangian_lowerBound_of_norm_multiplier_le
    (h : EqualityConstrained.Regularity f c) (rho : ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (B : ℝ)
    (hrho : 0 < rho) (hx : x ∈ h.region)
    (hmultiplier : ‖multiplier‖ ≤ B) (hB : 0 ≤ B) :
    h.objectiveLower - B ^ 2 / (2 * rho) ≤
      ℒ[f, c; rho](x, multiplier) := by
  -- Cauchy–Schwarz controls the possibly negative multiplier pairing.
  have hinner : -(‖multiplier‖ * ‖c x‖) ≤ ⟪multiplier, c x⟫_ℝ :=
    neg_le_of_abs_le (abs_real_inner_le_norm multiplier (c x))
  -- Young's inequality completes the square against the quadratic penalty.
  have hyoung :
      2 * ‖c x‖ * ‖multiplier‖ ≤
        rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2 :=
    two_mul_le_add_mul_sq hrho
  have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
  have hyoungDivided := div_le_div_of_nonneg_right hyoung htwoNonneg
  have hyoungHalf :
      ‖multiplier‖ * ‖c x‖ ≤
        rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
    calc
      ‖multiplier‖ * ‖c x‖ = (2 * ‖c x‖ * ‖multiplier‖) / 2 := by ring
      _ ≤ (rho * ‖c x‖ ^ 2 + rho⁻¹ * ‖multiplier‖ ^ 2) / 2 :=
        hyoungDivided
      _ = rho / 2 * ‖c x‖ ^ 2 + ‖multiplier‖ ^ 2 / (2 * rho) := by
        field_simp [hrho.ne']
  have hmultiplierSq : ‖multiplier‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg multiplier) hB).2 hmultiplier
  have htwoRhoPos : 0 < 2 * rho := by positivity
  have hdiv :
      ‖multiplier‖ ^ 2 / (2 * rho) ≤ B ^ 2 / (2 * rho) :=
    (div_le_div_iff_of_pos_right htwoRhoPos).2 hmultiplierSq
  -- Combine the objective lower bound with the completed-square estimate.
  rw [augmentedLagrangian_def]
  have hobjective := h.objectiveLower_le x hx
  linarith

/-- Theorem 2.9 (1): on an admissible prefix, each positive-index Lyapunov step
decreases by at least `(params.beta / 4) * ‖run.step k‖ ^ 2`. -/
theorem lyapunovDescent (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k < N) :
    run.lyapunov h params (k + 1) ≤
      run.lyapunov h params k - (params.beta / 4) * ‖run.step k‖ ^ 2 := by
  -- Lemmas 2.7 and 2.8 control the primal decrease and the multiplier-update cost.
  have hlagrangian := run.augmentedLagrangianDescent h params h_admissible hk
  have hmultiplier :=
    run.norm_multiplier_succ_sub_sq_le h params h_admissible hk_pos hk
  have hmultiplierDiv :
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
        (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) *
            (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by
    have hdivided := (div_le_div_iff_of_pos_right run.rho_pos).2 hmultiplier
    calc
      ‖run.multiplier (k + 1) - run.multiplier k‖ ^ 2 / params.rho ≤
          (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound *
              (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2)) / params.rho := hdivided
      _ = (multiplierPrimalConstant h params.delta params.beta params.rho
            params.multiplierBound / params.rho) *
              (‖run.step k‖ ^ 2 + ‖run.step (k - 1)‖ ^ 2) := by ring
  -- Assumption 2.3 makes each current-step correction cost at most `beta / 8`.
  have hcoefficient := multiplierPrimalConstant_div_rho_le_beta_div_eight h params
  have hcurrent :
      (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step k‖ ^ 2 ≤
        (params.beta / 8) * ‖run.step k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
  -- The preceding-step term cancels, leaving the claimed quarter-beta decrease.
  rw [run.lyapunov_def, run.lyapunov_def,
    augmentedLagrangian_multiplier_succ_eq h params run, Nat.add_sub_cancel]
  nlinarith

/-- Theorem 2.9 (2): every positive-index Lyapunov value in an admissible prefix
is at least the uniform Lyapunov lower bound. -/
theorem lyapunovLowerBound_le (h : EqualityConstrained.Regularity f c)
    (params : Parameters h x₀ multiplier₀)
    (run : Run f c params.rho params.beta x₀ multiplier₀)
    {N k : ℕ} (h_admissible : run.IsAdmissiblePrefix h N)
    (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    lyapunovLowerBound h params ≤ run.lyapunov h params k := by
  -- The right endpoint of the preceding admissible segment is `run.point k`.
  have hkPrevious : k - 1 < N := by omega
  have hsegment :=
    (run.isAdmissiblePrefix_iff h N).1 h_admissible (k - 1) hkPrevious
  have hx : run.point k ∈ h.region := by
    simpa only [Nat.sub_add_cancel hk_pos] using
      hsegment (right_mem_segment ℝ (run.point (k - 1)) (run.point ((k - 1) + 1)))
  have hmultiplier := run.norm_multiplier_le h params h_admissible hk
  -- Completion of squares supplies the lower bound for the augmented term.
  have hboundNonneg : (0 : ℝ) ≤ params.multiplierBound := by positivity
  have hlower := augmentedLagrangian_lowerBound_of_norm_multiplier_le h params.rho
    (run.point k) (run.multiplier k) params.multiplierBound run.rho_pos hx
    hmultiplier hboundNonneg
  have hconstantNonneg :
      0 ≤ multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [multiplierPrimalConstant_def]
    positivity
  have hcorrectionNonneg :
      0 ≤ (multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * ‖run.step (k - 1)‖ ^ 2 :=
    mul_nonneg (div_nonneg hconstantNonneg run.rho_pos.le) (sq_nonneg _)
  -- Adding the nonnegative Lyapunov correction preserves the uniform bound.
  rw [lyapunovLowerBound_def, run.lyapunov_def]
  linarith

end LALM.Run

end

/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.FeedbackOperator
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.InitialForcing

@[expose] public section

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Discounted outputs; index zero represents the first updated iterate. -/
noncomputable def discountedOutputs (α : ℝ) (q η : ℕ → E) (k : ℕ) : Fin 2 → E :=
  fun b ↦ if b = 0 then α ^ (k + 1) • q (k + 1) else α ^ (k + 1) • η (k + 1)

/-- The actual proximal inputs in the centered scaled reduced iteration. -/
noncomputable def initializedInputs (α γ : ℝ) (q η w : ℕ → E) (k : ℕ) : Fin 2 → E :=
  fun b ↦ if b = 0 then α ^ (k + 1) • (η k - γ • w k)
    else α ^ (k + 1) • (q (k + 1) + γ • w k)

/-- The zero-state resolvent differs from the discounted actual state by
exactly the geometrically discounted initial state. -/
theorem initialized_resolvent_identity (α : ℝ) (q η w : ℕ → E)
    (hrec : ∀ k, w (k + 1) = w k + q (k + 1) - η (k + 1)) (k : ℕ) :
    causalResolvent α (fun j ↦ discountedOutputs α q η j 0 -
      discountedOutputs α q η j 1) k = α ^ (k + 1) • (w k - w 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [causalResolvent_succ, ih, hrec]
      simp only [discountedOutputs, Fin.isValue, if_true, one_ne_zero, if_false]
      simp only [pow_succ, smul_add, smul_sub, smul_smul]
      module

/-- The one-step initial position is the only impulse created by the delay. -/
theorem initialized_delayed_position (α : ℝ) (η : ℕ → E) (k : ℕ) :
    (if k = 0 then α • η 0 else 0) +
      α • delay (fun j ↦ α ^ (j + 1) • η (j + 1)) k = α ^ (k + 1) • η k := by
  cases k with
  | zero => simp
  | succ k =>
      simp only [Nat.succ_ne_zero, if_false, delay_succ, zero_add, pow_succ, smul_smul]
      module

/-- Exact identification of the manuscript's initialized disturbance with
its causal zero-state feedback relation. -/
theorem initializedInputs_feedback (α γ : ℝ) (q η w : ℕ → E)
    (hrec : ∀ k, w (k + 1) = w k + q (k + 1) - η (k + 1)) :
    initializedInputs α γ q η w = initialForcing α γ (η 0) (w 0) +
      feedbackOperator α γ (discountedOutputs α q η) := by
  funext k b
  fin_cases b
  · change α ^ (k + 1) • (η k - γ • w k) = initialForcing α γ (η 0) (w 0) k 0 +
      feedbackOperator α γ (discountedOutputs α q η) k 0
    rw [initialForcing_first, feedbackOperator_first, initialized_resolvent_identity α q η w hrec]
    have hd := initialized_delayed_position α η k
    change (if k = 0 then α • η 0 else 0) +
      α • delay (fun j ↦ discountedOutputs α q η j 1) k = α ^ (k + 1) • η k at hd
    rw [show α ^ (k + 1) • (η k - γ • w k) =
      α ^ (k + 1) • η k + (-γ) • (α ^ (k + 1) • w k) by module]
    rw [← hd]
    module
  · change α ^ (k + 1) • (q (k + 1) + γ • w k) = initialForcing α γ (η 0) (w 0) k 1 +
      feedbackOperator α γ (discountedOutputs α q η) k 1
    rw [initialForcing_second, feedbackOperator_second,
      initialized_resolvent_identity α q η w hrec]
    simp only [discountedOutputs, Fin.isValue, if_true]
    module

/-- The reconstructed memory is precisely the actual discounted multiplier
state at every time; no bound on the state is used in this identity. -/
theorem reconstructedMemory_identity (α : ℝ) (q η w : ℕ → E)
    (hrec : ∀ k, w (k + 1) = w k + q (k + 1) - η (k + 1)) (k : ℕ) :
    discountedOutputs α q η k 0 - discountedOutputs α q η k 1 +
      causalResolvent α (fun j ↦ discountedOutputs α q η j 0 -
        discountedOutputs α q η j 1) k + geometricTail α (w 0) k =
      α ^ (k + 1) • w (k + 1) := by
  rw [initialized_resolvent_identity α q η w hrec, hrec]
  simp only [discountedOutputs, geometricTail, Fin.isValue, if_true, one_ne_zero, if_false]
  module

end ADMM.UnitCircle.Causal

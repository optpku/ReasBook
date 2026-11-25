/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.ZeroState
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.CoordinateNorms
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Separation

@[expose] public section

open scoped BigOperators ENNReal

namespace ADMM.UnitCircle.Causal

/-- The true bilateral delay restricts to the zero-initial one-sided delay. -/
theorem coordinateLp_delay_nat {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) (k : ℕ) :
    Fourier.delay 1 (coordinateLp v hv b a) (k : ℤ) =
      ((delay (fun j ↦ v j b) k) a : ℂ) := by
  rw [Fourier.delay_apply]
  cases k with
  | zero =>
      change coordinateLp v hv b a (-((0 : ℕ) + 1 : ℤ)) = 0
      exact coordinateLp_negSucc v hv b a 0
  | succ k =>
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega, coordinateLp_nat]
      rfl

theorem coordinateLp_delay_negSucc {m : ℕ} (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (b : Fin 2) (a : Fin m) (k : ℕ) :
    Fourier.delay 1 (coordinateLp v hv b a) (-(k + 1 : ℤ)) = 0 := by
  rw [Fourier.delay_apply, show -(k + 1 : ℤ) - 1 = -((k + 1 : ℕ) + 1 : ℤ) by omega]
  exact coordinateLp_negSucc v hv b a (k + 1)

theorem difference_apply (α : ℝ) (x : Fourier.TimeSequence) (k : ℤ) :
    Fourier.difference α x k = x k - (α : ℂ) * Fourier.delay 1 x k := rfl

theorem multiplierNormal_apply (α γ : ℝ) (x : Fourier.TimeSequence) (k : ℤ) :
    Fourier.multiplierNormal α γ x k = x k + (((γ - 1) * α : ℝ) : ℂ) *
      Fourier.delay 1 x k := rfl

theorem pointSignal_first_apply (α : ℝ) (s : Fin 2 → Fourier.TimeSequence) (k : ℤ) :
    Fourier.pointSignal α s 0 k = s 0 k + Fourier.difference α (s 1) k := rfl

theorem pointSignal_second_apply (α : ℝ) (s : Fin 2 → Fourier.TimeSequence) (k : ℤ) :
    Fourier.pointSignal α s 1 k = s 0 k := rfl

theorem normalSignal_first_apply (α γ : ℝ) (s : Fin 2 → Fourier.TimeSequence) (k : ℤ) :
    Fourier.normalSignal α γ s 0 k = -Fourier.difference α (s 0) k -
      Fourier.multiplierNormal α γ (s 1) k := rfl

theorem normalSignal_second_apply (α γ : ℝ) (s : Fin 2 → Fourier.TimeSequence) (k : ℤ) :
    Fourier.normalSignal α γ s 1 k = Fourier.multiplierNormal α γ (s 1) k := rfl

/-- The genuine Fourier state for the zero-state feedback realization. -/
noncomputable def zeroStateSignals {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (y : ℕ → BlockVector m) (hy : Memℓp y 2) (a : Fin m) : Fin 2 → Fourier.TimeSequence :=
  fun i ↦ coordinateLp (zeroState α y) (zeroState_memℓp hα0 hα1 y hy) i a

/-- The two symbol rows recover exactly the prescribed arbitrary `ℓ₂`
outputs of the actual causal realization. -/
theorem zeroStateSignals_point {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (y : ℕ → BlockVector m) (hy : Memℓp y 2) (a : Fin m) (b : Fin 2) :
    Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) b = coordinateLp y hy b a := by
  ext z
  cases z with
  | ofNat k =>
    fin_cases b
    · change Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) 0 (k : ℤ) =
        coordinateLp y hy 0 a (k : ℤ)
      rw [pointSignal_first_apply, difference_apply]
      simp only [zeroStateSignals, coordinateLp_nat, coordinateLp_delay_nat]
      have hv : y k 1 + (zeroStateMemory α y k -
          α • delay (zeroStateMemory α y) k) = y k 0 := by
        rw [zeroStateMemory_difference]
        module
      have hc := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ (x a : ℂ)) hv
      simpa [zeroState, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] using hc
    · change Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) 1 (k : ℤ) =
        coordinateLp y hy 1 a (k : ℤ)
      rw [pointSignal_second_apply]
      simp [zeroStateSignals, zeroState]
  | negSucc k =>
    change Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) b (-(k + 1 : ℤ)) =
      coordinateLp y hy b a (-(k + 1 : ℤ))
    fin_cases b
    · change Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) 0 (-(k + 1 : ℤ)) =
        coordinateLp y hy 0 a (-(k + 1 : ℤ))
      rw [pointSignal_first_apply, difference_apply]
      simp only [zeroStateSignals, coordinateLp_negSucc, coordinateLp_delay_negSucc,
        mul_zero, sub_zero, add_zero]
    · change Fourier.pointSignal α (zeroStateSignals hα0 hα1 y hy a) 1 (-(k + 1 : ℤ)) =
        coordinateLp y hy 1 a (-(k + 1 : ℤ))
      rw [pointSignal_second_apply]
      simp only [zeroStateSignals, coordinateLp_negSucc]

/-- The normal symbol rows recover `Gα y−y` exactly for the same state.
This attaches the strict separation inequality to the causal feedback used
in the homotopy proof. -/
theorem zeroStateSignals_normal {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (γ : ℝ) (y : ℕ → BlockVector m) (hy : Memℓp y 2) (a : Fin m) (b : Fin 2) :
    Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) b =
      coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) b a -
        coordinateLp y hy b a := by
  ext z
  change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) b z =
    coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) b a z -
      coordinateLp y hy b a z
  cases z with
  | ofNat k =>
    fin_cases b
    · change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) 0 (k : ℤ) =
        coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) 0 a (k : ℤ) -
          coordinateLp y hy 0 a (k : ℤ)
      rw [normalSignal_first_apply, difference_apply, multiplierNormal_apply]
      simp only [zeroStateSignals, coordinateLp_nat, coordinateLp_delay_nat]
      have hc := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ (x a : ℂ))
        (zeroStateMemory_normal_first α γ y k)
      simpa [zeroState, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.neg_apply, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg] using hc
    · change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) 1 (k : ℤ) =
        coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) 1 a (k : ℤ) -
          coordinateLp y hy 1 a (k : ℤ)
      rw [normalSignal_second_apply, multiplierNormal_apply]
      simp only [zeroStateSignals, coordinateLp_nat, coordinateLp_delay_nat]
      have hc := congrArg (fun x : EuclideanSpace ℝ (Fin m) ↦ (x a : ℂ))
        (zeroStateMemory_multiplier α γ y k)
      simpa [zeroState, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul] using hc
  | negSucc k =>
    change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) b (-(k + 1 : ℤ)) =
      coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) b a
        (-(k + 1 : ℤ)) - coordinateLp y hy b a (-(k + 1 : ℤ))
    fin_cases b
    · change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) 0 (-(k + 1 : ℤ)) =
        coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) 0 a
          (-(k + 1 : ℤ)) - coordinateLp y hy 0 a (-(k + 1 : ℤ))
      rw [normalSignal_first_apply, difference_apply, multiplierNormal_apply]
      simp only [zeroStateSignals, coordinateLp_negSucc, coordinateLp_delay_negSucc,
        mul_zero, sub_zero, add_zero, neg_zero]
    · change Fourier.normalSignal α γ (zeroStateSignals hα0 hα1 y hy a) 1 (-(k + 1 : ℤ)) =
        coordinateLp (feedbackOperator α γ y) (feedbackOperator_memℓp hα0 hα1 γ y hy) 1 a
          (-(k + 1 : ℤ)) - coordinateLp y hy 1 a (-(k + 1 : ℤ))
      rw [normalSignal_second_apply, multiplierNormal_apply]
      simp only [zeroStateSignals, coordinateLp_negSucc, coordinateLp_delay_negSucc,
        mul_zero, sub_zero, add_zero]

end ADMM.UnitCircle.Causal

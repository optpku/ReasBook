/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Truncation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section

open scoped BigOperators ENNReal

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E]

theorem truncate_norm_sq (T : ℕ) (v : ℕ → E) :
    ‖truncate T v‖ ^ 2 = ∑ k ∈ Finset.range T, ‖v k‖ ^ 2 := by
  have heq : truncate T v = ∑ k ∈ Finset.range T, lp.single 2 k (v k) := by
    apply Subtype.ext
    funext k
    simp only [truncate_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
    simp [Pi.single_apply, Finset.mem_range]
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) v (Finset.range T)
  rw [← heq] at h
  simpa using h

theorem truncate_norm_mono {T U : ℕ} (hTU : T ≤ U) (v : ℕ → E) :
    ‖truncate T v‖ ≤ ‖truncate U v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : k < T
  · simp [hk, lt_of_lt_of_le hk hTU]
  · simp [hk, norm_nonneg]

/-- One-sided delay, with an explicit zero before the first time index. -/
def delay (v : ℕ → E) : ℕ → E
  | 0 => 0
  | k + 1 => v k

@[simp] theorem delay_zero (v : ℕ → E) : delay v 0 = 0 := rfl
@[simp] theorem delay_succ (v : ℕ → E) (k : ℕ) : delay v (k + 1) = v k := rfl

theorem delay_prefix_norm_le (v : ℕ → E) (T : ℕ) :
    ‖truncate T (delay v)‖ ≤ ‖truncate T v‖ := by
  cases T with
  | zero =>
      have ht (w : ℕ → E) : truncate 0 w = 0 := by ext k; simp
      rw [ht, ht]
  | succ T =>
    have hsq : ‖truncate (T + 1) (delay v)‖ ^ 2 = ‖truncate T v‖ ^ 2 := by
      rw [truncate_norm_sq, truncate_norm_sq, Finset.sum_range_succ']
      simp
    have hnorm : ‖truncate (T + 1) (delay v)‖ = ‖truncate T v‖ := by
      nlinarith [norm_nonneg (truncate (T + 1) (delay v)), norm_nonneg (truncate T v)]
    rw [hnorm]
    exact truncate_norm_mono (Nat.le_succ T) v

section Scalar

variable [NormedSpace ℝ E]

/-- The strictly causal resolvent `α S (I-α S)⁻¹`, defined on arbitrary
sequences before square summability is known. -/
def causalResolvent (α : ℝ) (v : ℕ → E) : ℕ → E
  | 0 => 0
  | k + 1 => α • (v k + causalResolvent α v k)

@[simp] theorem causalResolvent_zero (α : ℝ) (v : ℕ → E) :
    causalResolvent α v 0 = 0 := rfl

@[simp] theorem causalResolvent_succ (α : ℝ) (v : ℕ → E) (k : ℕ) :
    causalResolvent α v (k + 1) = α • (v k + causalResolvent α v k) := rfl

theorem causalResolvent_eq_delay (α : ℝ) (v : ℕ → E) :
    causalResolvent α v = α • delay (v + causalResolvent α v) := by
  funext k
  cases k <;> simp

/-- The geometric resolvent bound holds on every finite prefix. Its proof
uses an absorbable delay estimate, so it needs no prior `ℓ₂` membership. -/
theorem causalResolvent_prefix_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (v : ℕ → E) (T : ℕ) :
    ‖truncate T (causalResolvent α v)‖ ≤ α / (1 - α) * ‖truncate T v‖ := by
  have h : ‖truncate T (causalResolvent α v)‖ ≤
      α * (‖truncate T v‖ + ‖truncate T (causalResolvent α v)‖) := by
    calc
      ‖truncate T (causalResolvent α v)‖ =
          α * ‖truncate T (delay (v + causalResolvent α v))‖ := by
        conv_lhs => rw [causalResolvent_eq_delay]
        rw [truncate_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0]
      _ ≤ α * ‖truncate T (v + causalResolvent α v)‖ :=
        mul_le_mul_of_nonneg_left (delay_prefix_norm_le _ _) hα0
      _ ≤ _ := by
        rw [truncate_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hα0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hα1)).mpr
  nlinarith

@[simp] theorem causalResolvent_smul (α a : ℝ) (v : ℕ → E) :
    causalResolvent α (a • v) = a • causalResolvent α v := by
  funext k
  induction k with
  | zero => simp
  | succ k ih => simp only [causalResolvent_succ, Pi.smul_apply, ih]; module

theorem causalResolvent_prefix_congr (α : ℝ) {v w : ℕ → E} (k : ℕ)
    (h : ∀ j < k, v j = w j) : causalResolvent α v k = causalResolvent α w k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [causalResolvent_succ, causalResolvent_succ, h k (Nat.lt_succ_self k),
        ih (fun j hj ↦ h j (Nat.lt_trans hj (Nat.lt_succ_self k)))]

end Scalar

end ADMM.UnitCircle.Causal

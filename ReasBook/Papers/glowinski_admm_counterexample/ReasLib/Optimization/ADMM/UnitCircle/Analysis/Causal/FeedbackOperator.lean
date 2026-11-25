/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.SequenceOperators
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped ENNReal

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E]

theorem truncate_norm_le_of_pointwise {E' : Type*} [NormedAddCommGroup E']
    (v : ℕ → E) (w : ℕ → E') (h : ∀ k, ‖v k‖ ≤ ‖w k‖) (T : ℕ) :
    ‖truncate T v‖ ≤ ‖truncate T w‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : k < T <;> simp [hk, h k]

theorem truncate_norm_norm (v : ℕ → E) (T : ℕ) :
    ‖truncate T (fun k ↦ ‖v k‖)‖ = ‖truncate T v‖ := by
  apply le_antisymm
  · exact truncate_norm_le_of_pointwise _ _ (fun k ↦ by simp) T
  · exact truncate_norm_le_of_pointwise _ _ (fun k ↦ by simp) T

/-- The temporal `ℓ₂` norm of a pair of blocks is at most the sum of the
blockwise temporal norms, for the product maximum norm used here. -/
theorem truncate_pair_norm_le (v : ℕ → Fin 2 → E) (T : ℕ) :
    ‖truncate T v‖ ≤ ‖truncate T (fun k ↦ v k 0)‖ +
      ‖truncate T (fun k ↦ v k 1)‖ := by
  let a : ℕ → ℝ := fun k ↦ ‖v k 0‖
  let b : ℕ → ℝ := fun k ↦ ‖v k 1‖
  calc
    ‖truncate T v‖ ≤ ‖truncate T (a + b)‖ := by
      apply truncate_norm_le_of_pointwise
      intro k
      change ‖v k‖ ≤ |‖v k 0‖ + ‖v k 1‖|
      rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro i
      fin_cases i
      · exact le_add_of_nonneg_right (norm_nonneg _)
      · exact le_add_of_nonneg_left (norm_nonneg _)
    _ ≤ ‖truncate T a‖ + ‖truncate T b‖ := by
      rw [truncate_add]
      exact norm_add_le _ _
    _ = _ := by rw [truncate_norm_norm, truncate_norm_norm]

variable [NormedSpace ℝ E]

/-- The actual zero-state feedback operator from the manuscript, written in
its causal resolvent form. Block zero is `F`, block one is `J`. -/
def feedbackOperator (α γ : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) : Fin 2 → E :=
  let K := causalResolvent α (fun j ↦ y j 0 - y j 1)
  fun b ↦ if b = 0 then α • delay (fun j ↦ y j 1) k + (-γ) • K k
    else y k 0 + γ • K k

@[simp] theorem feedbackOperator_first (α γ : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    feedbackOperator α γ y k 0 =
      α • delay (fun j ↦ y j 1) k + (-γ) • causalResolvent α (fun j ↦ y j 0 - y j 1) k := by
  simp [feedbackOperator]

@[simp] theorem feedbackOperator_second (α γ : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    feedbackOperator α γ y k 1 =
      y k 0 + γ • causalResolvent α (fun j ↦ y j 0 - y j 1) k := by
  simp [feedbackOperator]

/-- Scalar homogeneity is used to place the homotopy parameter in front of
`G D` while leaving the discounted proximal map itself fixed. -/
theorem feedbackOperator_smul (α γ a : ℝ) (y : ℕ → Fin 2 → E) :
    feedbackOperator α γ (a • y) = a • feedbackOperator α γ y := by
  have hdiff : (fun j ↦ (a • y) j 0 - (a • y) j 1) =
      a • (fun j ↦ y j 0 - y j 1) := by funext j; simp [smul_sub]
  have hdelay : delay (fun j ↦ (a • y) j 1) = a • delay (fun j ↦ y j 1) := by
    funext k
    cases k <;> simp
  have hK (k : ℕ) : causalResolvent α (fun j ↦ (a • y) j 0 - (a • y) j 1) k =
      a • causalResolvent α (fun j ↦ y j 0 - y j 1) k := by
    rw [hdiff, causalResolvent_smul]
    rfl
  funext k b
  fin_cases b
  · change feedbackOperator α γ (a • y) k 0 = a • feedbackOperator α γ y k 0
    rw [feedbackOperator_first, feedbackOperator_first, hK, hdelay]
    simp only [Pi.smul_apply]
    module
  · change feedbackOperator α γ (a • y) k 1 = a • feedbackOperator α γ y k 1
    rw [feedbackOperator_second, feedbackOperator_second, hK]
    simp only [Pi.smul_apply]
    module

/-- A finite-prefix bound for the actual linear feedback. The constant may
depend on the fixed discount; no prior `ℓ₂` membership is required. -/
theorem feedbackOperator_prefix_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (γ : ℝ) (y : ℕ → Fin 2 → E) (T : ℕ) :
    ‖truncate T (feedbackOperator α γ y)‖ ≤
      (1 + α + 4 * |γ| * (α / (1 - α))) * ‖truncate T y‖ := by
  let q := fun k ↦ y k 0
  let η := fun k ↦ y k 1
  let K := causalResolvent α (q - η)
  let A := α / (1 - α)
  have hA : 0 ≤ A := div_nonneg hα0 (sub_pos.mpr hα1).le
  have hq : ‖truncate T q‖ ≤ ‖truncate T y‖ :=
    truncate_norm_le_of_pointwise _ _ (fun k ↦ norm_le_pi_norm (y k) 0) T
  have hη : ‖truncate T η‖ ≤ ‖truncate T y‖ :=
    truncate_norm_le_of_pointwise _ _ (fun k ↦ norm_le_pi_norm (y k) 1) T
  have hdiff : ‖truncate T (q - η)‖ ≤ 2 * ‖truncate T y‖ := by
    have heq : truncate T (q - η) = truncate T q - truncate T η := by
      ext k
      by_cases hk : k < T <;> simp [hk]
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith)
  have hK : ‖truncate T K‖ ≤ 2 * A * ‖truncate T y‖ := by
    exact (causalResolvent_prefix_norm_le hα0 hα1 (q - η) T).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hdiff hA])
  have hF : ‖truncate T (fun k ↦ feedbackOperator α γ y k 0)‖ ≤
      α * ‖truncate T y‖ + |γ| * (2 * A * ‖truncate T y‖) := by
    have heq : (fun k ↦ feedbackOperator α γ y k 0) = α • delay η + (-γ) • K := rfl
    rw [heq, truncate_add, truncate_smul, truncate_smul]
    have h := norm_add_le (α • truncate T (delay η)) ((-γ) • truncate T K)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hα0, abs_neg] at h
    exact h.trans (add_le_add
      (mul_le_mul_of_nonneg_left ((delay_prefix_norm_le η T).trans hη) hα0)
      (mul_le_mul_of_nonneg_left hK (abs_nonneg γ)))
  have hJ : ‖truncate T (fun k ↦ feedbackOperator α γ y k 1)‖ ≤
      ‖truncate T y‖ + |γ| * (2 * A * ‖truncate T y‖) := by
    have heq : (fun k ↦ feedbackOperator α γ y k 1) = q + γ • K := rfl
    rw [heq, truncate_add, truncate_smul]
    have h := norm_add_le (truncate T q) (γ • truncate T K)
    rw [norm_smul, Real.norm_eq_abs] at h
    exact h.trans (add_le_add hq (mul_le_mul_of_nonneg_left hK (abs_nonneg γ)))
  have h := (truncate_pair_norm_le (feedbackOperator α γ y) T).trans
    (add_le_add hF hJ)
  convert! h using 1 <;> dsimp [A] <;> ring

end ADMM.UnitCircle.Causal

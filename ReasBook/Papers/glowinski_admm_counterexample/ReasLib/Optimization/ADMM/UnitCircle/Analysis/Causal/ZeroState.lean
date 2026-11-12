/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.DiscountedStability

@[expose] public section

open scoped ENNReal

namespace ADMM.UnitCircle.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero-state multiplier memory from the two output blocks. -/
def zeroStateMemory (α : ℝ) (y : ℕ → Fin 2 → E) : ℕ → E :=
  (fun k ↦ y k 0 - y k 1) + causalResolvent α (fun k ↦ y k 0 - y k 1)

theorem zeroStateMemory_delay (α : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    α • delay (zeroStateMemory α y) k =
      causalResolvent α (fun j ↦ y j 0 - y j 1) k := by
  cases k with
  | zero => simp
  | succ k => rfl

theorem zeroStateMemory_difference (α : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    zeroStateMemory α y k - α • delay (zeroStateMemory α y) k = y k 0 - y k 1 := by
  rw [zeroStateMemory_delay]
  change (y k 0 - y k 1) + _ - _ = _
  module

theorem zeroStateMemory_multiplier (α γ : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    zeroStateMemory α y k + ((γ - 1) * α) • delay (zeroStateMemory α y) k =
      feedbackOperator α γ y k 1 - y k 1 := by
  rw [mul_smul, zeroStateMemory_delay, feedbackOperator_second]
  change (y k 0 - y k 1) + _ + _ = _
  module

theorem zeroStateMemory_normal_first (α γ : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) :
    -(y k 1 - α • delay (fun j ↦ y j 1) k) -
      (zeroStateMemory α y k + ((γ - 1) * α) • delay (zeroStateMemory α y) k) =
      feedbackOperator α γ y k 0 - y k 0 := by
  rw [zeroStateMemory_multiplier, feedbackOperator_second, feedbackOperator_first]
  module

theorem zeroStateMemory_memℓp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (y : ℕ → Fin 2 → E) (hy : Memℓp y 2) : Memℓp (zeroStateMemory α y) 2 := by
  have hq : Memℓp (fun k ↦ y k 0) 2 := hy.mono' (fun k ↦ norm_le_pi_norm (y k) 0)
  have hη : Memℓp (fun k ↦ y k 1) 2 := hy.mono' (fun k ↦ norm_le_pi_norm (y k) 1)
  have hd : Memℓp (fun k ↦ y k 0 - y k 1) 2 := hq.sub hη
  exact hd.add (causalResolvent_memℓp hα0 hα1 _ hd)

theorem memℓp_pair (v : ℕ → Fin 2 → E)
    (h0 : Memℓp (fun k ↦ v k 0) 2) (h1 : Memℓp (fun k ↦ v k 1) 2) : Memℓp v 2 := by
  apply memℓp_of_truncate_norm_le
    (B := ‖(⟨fun k ↦ v k 0, h0⟩ : lp (fun _ : ℕ ↦ E) 2)‖ +
      ‖(⟨fun k ↦ v k 1, h1⟩ : lp (fun _ : ℕ ↦ E) 2)‖)
  intro T
  exact (truncate_pair_norm_le v T).trans (add_le_add
    (truncate_norm_le T (⟨fun k ↦ v k 0, h0⟩ : lp (fun _ : ℕ ↦ E) 2))
    (truncate_norm_le T (⟨fun k ↦ v k 1, h1⟩ : lp (fun _ : ℕ ↦ E) 2)))

/-- State order is `(eta,w)`, matching the supply symbol's two columns. -/
def zeroState (α : ℝ) (y : ℕ → Fin 2 → E) (k : ℕ) : Fin 2 → E :=
  fun i ↦ if i = 0 then y k 1 else zeroStateMemory α y k

theorem zeroState_memℓp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (y : ℕ → Fin 2 → E) (hy : Memℓp y 2) : Memℓp (zeroState α y) 2 := by
  apply memℓp_pair
  · simpa [zeroState] using
      hy.mono' (fun k ↦ norm_le_pi_norm (y k) 1)
  · simpa [zeroState] using
      zeroStateMemory_memℓp hα0 hα1 y hy

/-- The actual linear feedback preserves square summability with its
previously verified explicit finite-prefix constant. -/
theorem feedbackOperator_memℓp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (γ : ℝ) (y : ℕ → Fin 2 → E) (hy : Memℓp y 2) :
    Memℓp (feedbackOperator α γ y) 2 := by
  let L := 1 + α + 4 * |γ| * (α / (1 - α))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply memℓp_of_truncate_norm_le
    (B := L * ‖(⟨y, hy⟩ : lp (fun _ : ℕ ↦ Fin 2 → E) 2)‖)
  intro T
  exact (feedbackOperator_prefix_norm_le hα0 hα1 γ y T).trans
    (mul_le_mul_of_nonneg_left
      (truncate_norm_le T (⟨y, hy⟩ : lp (fun _ : ℕ ↦ Fin 2 → E) 2)) hL)

theorem feedbackOperator_norm_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (γ : ℝ) (y : ℕ → Fin 2 → E) (hy : Memℓp y 2) :
    ‖(⟨feedbackOperator α γ y, feedbackOperator_memℓp hα0 hα1 γ y hy⟩ :
      lp (fun _ : ℕ ↦ Fin 2 → E) 2)‖ ≤
      (1 + α + 4 * |γ| * (α / (1 - α))) *
        ‖(⟨y, hy⟩ : lp (fun _ : ℕ ↦ Fin 2 → E) 2)‖ := by
  apply norm_le_of_truncate_norm_le
  intro T
  have hL : 0 ≤ 1 + α + 4 * |γ| * (α / (1 - α)) := by positivity
  exact (feedbackOperator_prefix_norm_le hα0 hα1 γ y T).trans
    (mul_le_mul_of_nonneg_left
      (truncate_norm_le T (⟨y, hy⟩ : lp (fun _ : ℕ ↦ Fin 2 → E) 2)) hL)

end ADMM.UnitCircle.Causal
